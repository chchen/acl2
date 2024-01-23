;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg-change3")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")
(include-book "type-options")
(include-book "../utils/fresh-vars")
(include-book "ttmrg-triv3")
(include-book "make-test")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

(local (in-theory (e/d
  (ev-smtcp-of-fncall-args)
  (pseudo-termp pseudo-term-listp symbol-listp  ; Mark is impatient
   boolean-listp member-equal consp-of-pseudo-lambdap
   pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
   pseudo-termp-when-pseudo-term-syntax-p consp-of-is-conjunct? default-car
   (:type-prescription pseudo-lambdap)))))


; negate: simple version.  Might make more sophisticated later, such as
;   pushing the 'not to the leaves.
(define negate ((x pseudo-termp))
  :returns (not-x pseudo-termp)
  (b* ((x (pseudo-term-fix x))
       (nx (list 'not x))
       ((unless (consp x)) nx)
       ((if (equal (car x) 'not)) (cadr x))
       ((unless (equal (car x) 'if)) nx)
       ((if (and (equal (caddr x) ''t) (equal (caddr x) ''nil)))
	(negate (cadr x)))
       ((if (and (equal (caddr x) ''nil) (equal (caddr x) ''t)))
	(cadr x)))
    nx)
  ///
  (more-returns
    (not-x :name correctness-of-negate
      (iff (ev-smtcp not-x a)
	   (not (ev-smtcp (pseudo-term-fix x) a)))
      :hints(("Goal" :in-theory (enable negate))))))

; Yan's code for type-inference represents type judgements with pseudo-terms
; of the form: (if conj1 conj2 nil) where conj1 and conj2 are "conjuncts" that
; may be of this conjunction form as well.  Our "new" representation for typed
; terms used pseudo-term-set-p objects to represent conjunctions of pseudo-terms
; (i.e. for the path condition) and a judge-set-p objects for hype judgements
; for a term.  The functions pseudo-term-set-expr and judge-set-expr return
; produces if-then-else expressions from a pseudo-term-set or a judge-set
; respectively.  Here we provide functions that convert an if-then-else tree
; into a pseudo-term-set or a judge-set respectively.

(define judge-ev-lst ((lst judge-list-p) (term pseudo-termp) (a alistp))
  :returns (x true-listp)
  (if (consp lst)
    (cons (judge-ev (car lst) term a)
	  (judge-ev-lst (cdr lst) term a))
    nil)
  ///
  (more-returns
    (x :name judge-ev-list-when-consp
      (implies (consp lst)
	(equal x (cons (judge-ev (car lst) term a)
		       (judge-ev-lst (cdr lst) term a)))))
    (x :name judge-ev-list-of-atom
      (implies (not (consp lst)) (not x)))))

(define parse-conjunct-helper
    ((term pseudo-termp) (acc pseudo-term-listp))
  :returns (conjuncts pseudo-term-listp)
  :verify-guards nil
  (b* ((term (pseudo-term-fix term))
       (acc (pseudo-term-list-fix acc))
       ((if (equal term ''t)) acc)
       ((unless (and (consp term) (consp (cdr term)) (consp (cddr term))
		     (consp (cdddr term)) (not (cddddr term))
		     (equal (car term) 'if)
		     (equal (cadddr term) ''nil)))
	(cons term acc))
       (condx (cadr term))
       (thenx (caddr term)))
    (parse-conjunct-helper
     thenx
     (parse-conjunct-helper condx acc)))
  ///
  (verify-guards parse-conjunct-helper)

  (more-returns
    (conjuncts :name correctness-of-parse-conjunct-helper
      (equal (all-list<pseudo-term-ev> conjuncts a)
	     (and (ev-smtcp (pseudo-term-fix term) a)
		  (ev-and-list (pseudo-term-list-fix acc) a)))
      :hints(("Goal"
	:in-theory (e/d (parse-conjunct-helper pseudo-term-ev)
			(pseudo-term-list-equiv-implies-equal-ev-and-list-1)))))))

(define parse-conjunct ((term pseudo-termp))
  :returns pset
  (std::mergesort (parse-conjunct-helper term nil))
  ///
  (more-returns
    (pset :name pseudo-term-set-p-of-parse-conjunct
      (pseudo-term-set-p pset))

    (pset :name correctness-of-parse-conjunct
      (iff (all<pseudo-term-ev> pset a)
	   (ev-smtcp (pseudo-term-fix term) a)))))


(defines parse-judge
  :verify-guards nil
  :prepwork (
    (local (defrule lemma-quote
      (implies (and (pseudo-termp x) (equal (car x) 'quote))
	       (and (consp (cdr x)) (not (cddr x))))
      :in-theory (enable pseudo-termp))))
  :returns-hints(("Goal" :in-theory (enable judge-p judge-list-p)))

  (define parse-judge-term ((x pseudo-termp) (expr pseudo-termp))
    :returns (mv (erp booleanp) (new-term judge-p))
    :flag term
    (b* ((x (pseudo-term-fix x))
	 ((if (equal x expr)) (mv nil 'smt::x))
	 ((unless x) (mv nil x))
	 ((unless (consp x)) (mv t nil))
	 ((if (equal (car x) 'quote)) (mv nil x))
	 ((unless (symbolp (car x))) (mv t nil))
	 ((mv err-args arg-list) (parse-judge-args (cdr x) expr))
	 ((if err-args) (mv t nil)))
      (mv nil (cons (car x) arg-list))))

  (define parse-judge-args ((args pseudo-term-listp) (expr pseudo-termp))
    :returns (mv (erp booleanp) (new-args judge-list-p))
    :flag args
    (b* (((unless (consp args)) (mv nil nil))
	 ((cons hd tl) args)
	 ((mv err-hd new-hd) (parse-judge-term hd expr))
	 ((if err-hd) (mv t nil))
	 ((mv err-tl new-tl) (parse-judge-args tl expr))
	 ((if err-tl) (mv t nil)))
      (mv nil (cons new-hd new-tl))))
  ///
  (local (defrule guard-lemma
    (mv-let (erp new-args)
	    (parse-judge-args args expr)
	    (implies (not erp)
		     (equal (consp new-args) (consp args))))
    :in-theory (enable parse-judge-args)
    :induct (len args)))
  (verify-guards parse-judge-term)

  (local (encapsulate nil ; prepwork for correctness theorems
    (defrule parse-judge-args-when-atom
      (mv-let (erp new-args)
	      (parse-judge-args args expr)
	      (implies (not (consp args))
		       (and (not erp) (not new-args))))
      :in-theory (enable parse-judge-args))

    (defrule parse-judge-args-when-consp
      (b* (((mv erp new-args) (parse-judge-args args expr))
	   ((cons hd tl) args)
	   ((cons new-hd new-tl) new-args)
	   ((mv erp-hd na-hd) (parse-judge-term hd expr))
	   ((mv erp-tl na-tl) (parse-judge-args tl expr)))
	(implies (and (not erp) (consp args))
		 (and (not erp-hd)
		      (equal new-hd na-hd)
		      (not erp-tl)
		      (equal new-tl na-tl))))
      :in-theory (enable parse-judge-args)
      :induct (len args))

    (defrule consp-of-parse-judge-args
      (implies
	 (not (mv-nth 0 (parse-judge-args args expr)))
	 (equal (consp (mv-nth 1 (parse-judge-args args expr)))
		(consp args)))
      :in-theory (enable parse-judge-args)
      :induct (len args))

    (local (in-theory (enable parse-judge-term parse-judge-args judge-ev judge-ev-lst)))
    (defthm-parse-judge-flag
      (defthm correctness-lemma-term
	(mv-let (erp new-term)
		(parse-judge-term x expr)
		(implies (not erp)
			 (equal (judge-ev new-term expr a)
				(ev-smtcp (pseudo-term-fix x) a))))
	:flag term)

      (defthm correctness-lemma-args
	(mv-let (erp new-args)
		(parse-judge-args args expr)
		(implies (not erp)
			 (and (equal (judge-ev-lst new-args expr a)
				     (ev-smtcp-lst (pseudo-term-list-fix args) a))
			      (equal (ev-smtcp-lst new-args (cons (cons 'smt::x (ev-smtcp expr a)) nil))
				     (ev-smtcp-lst (pseudo-term-list-fix args) a)))))
	:flag args))
    (local (in-theory (disable parse-judge-term parse-judge-args judge-ev judge-ev-lst)))))

  (defrule correctness-of-parse-judge-term
    (mv-let (erp new-term)
	    (parse-judge-term x expr)
	    (implies (not erp)
		     (equal (judge-ev new-term expr a)
			    (ev-smtcp (pseudo-term-fix x) a)))))

  (defrule correctness-of-parse-judge-args
    (mv-let (erp new-args)
	    (parse-judge-args args expr)
	    (implies (not erp)
		     (iff (all-list<judge-ev> new-args expr a)
			  (all-list<pseudo-term-ev> args a))))
    :in-theory (enable all-list<judge-ev> all-list<pseudo-term-ev> pseudo-term-ev)
    :induct (pairlis$ args new-args)))

; an example -- change to use make-test
; (parse-judge-term
;   '(if (integerp (binary-+ x y))
;      (< '0 (binary-+ x y)))
;   '(binary-+ x y))

(define parse-judge-set((term pseudo-termp) (judge-pt pseudo-termp))
  :returns (jset judge-set-p)
  :guard-debug t
  (b* ((j-lst (parse-conjunct judge-pt))
       ((mv erp jx) (parse-judge-args j-lst term))
       ((if erp)
	(prog2$
	  (er hard? 'top-level
	      (concatenate 'string
			   "Badly formed judgements for term ~q0~%"
			   "  judgements ~q1~%")
	      term judge-pt jx)
	  '((smt::bad-judgement x)))))
    (std::mergesort jx))
  ///
  (more-returns
    (jset :name correctness-of-parse-judge-set
      (implies
	(not (equal jset '((bad-judgement x))))
	(iff (all<judge-ev> jset term a)
	     (ev-smtcp (pseudo-term-fix judge-pt) a))))))


(defines judge-flat-expr
  :returns-hints(("Goal" :in-theory (enable pseudo-termp)))
  :flag-local nil
  :verify-guards nil
  (define judge-flat-expr ((x judge-p) (expr pseudo-termp))
    :returns (x-flat pseudo-termp)
    :flag term
    (if (consp x)
	(if (equal (car x) 'quote)
	  (and (consp (cdr x)) (equal (cddr x) nil) x)
	  (and (symbolp (car x))
	       (cons (car x)
		     (judge-list-flat-expr (cdr x) expr))))
	(and (equal x 'x) (pseudo-term-fix expr))))

  (define judge-list-flat-expr ((lst judge-list-p) (expr pseudo-termp))
    :returns (lst-flat pseudo-term-listp)
    :flag list
    (if (consp lst)
	(cons (judge-flat-expr (car lst) expr)
	      (judge-list-flat-expr (cdr lst) expr))
	nil))
  ///
  (verify-guards judge-flat-expr
    :hints(("Goal" :in-theory (enable judge-p))))

  (local (in-theory (enable judge-flat-expr judge-list-flat-expr judge-p judge-ev judge-ev-lst)))
  (local (defrule lemma-1
    (implies (and (judge-list-p lst) (pseudo-termp expr))
      (equal (judge-ev-lst lst expr a)
	     (ev-smtcp-lst lst (list (cons 'x (ev-smtcp expr a))))))))

  (defthm-judge-flat-expr-flag
    (defthm correctness-of-judge-flat-expr
       (implies (and (judge-p x) (pseudo-termp expr))
		(equal (ev-smtcp (judge-flat-expr x expr) a)
		       (judge-ev x expr a)))
       :flag term)
    (defthm correctness-of-judge-list-flat-expr
       (implies (and (judge-list-p lst) (pseudo-termp expr))
		(equal (ev-smtcp-lst (judge-list-flat-expr lst expr) a)
		       (judge-ev-lst lst expr a)))
       :flag list)))

; propagate the path-cond down the expression tree
;   Most functions just pass forward their path-cond to their arguments.
;   (if cond then else) strengthens the path-cond of its then and else
;   with cond and (not cond) respectively.
;   BOZO: rather than constructing a new pseudo-term (list 'not cond) for
;   the else clause, I should at least check and cancel repeated if's.  I
;   believe Yan has code already that does this.  I'll make that change when
;   I have an example for testing it.
(define ttmrg-list-update-path-cond ((lst ttmrg-list-p) (parent ttmrg-p))
  :returns (new-lst ttmrg-list-p)
  (if (consp lst)
    (cons (ttmrg-add-path-cond-tterm (car lst) parent)
	  (ttmrg-list-update-path-cond (cdr lst) parent))
    nil)
  ///
  (defcong ttmrg-list-equiv ttmrg-list-equiv
	   (ttmrg-list-update-path-cond lst parent) 1
    :hints(("Goal" :induct (pairlis$ lst lst-equiv))))
  (defcong ttmrg->path-cond-equiv ttmrg-list-equiv
	   (ttmrg-list-update-path-cond lst parent) 2
    :hints(("Goal" :induct (len lst))))
  (more-returns
    (new-lst :name ttmrg-list->expr-list-equiv-of-ttmrg-list-update-path-cond
      (ttmrg-list->expr-list-equiv new-lst lst))

    (new-lst :name ttmrg-list-correct-p-of-ttmrg-list-update-path-cond
      (implies (ttmrg-list-correct-p lst a)
	       (ttmrg-list-correct-p new-lst a)))

    (new-lst :name args->path-cond-ev-of-ttmrg-list-update-path-cond
      (implies (and (ttmrg->path-cond-ev parent a)
		    (args->path-cond-ev lst a))
	       (args->path-cond-ev new-lst a)))))

(define ttmrg-update-path-cond-children ((tterm ttmrg-p))
  :returns (new-tt ttmrg-p)
  (case (ttmrg->kind tterm)
    (:var (ttmrg-fix tterm))
    (:quote (ttmrg-fix tterm))
    (:if
      (b* ((condx (ttmrg->condx tterm))
	   (thenx (ttmrg->thenx tterm))
	   (elsex (ttmrg->elsex tterm))
	   (cond-expr  (ttmrg->expr condx)))
	(change-ttmrg
	  tterm
	  :guts
	  (change-ttmrg-guts-if
	    (ttmrg->guts tterm)
	    :condx (ttmrg-add-path-cond-tterm condx tterm)
	    :thenx (ttmrg-add-path-cond-set
		     (ttmrg-add-path-cond-tterm thenx tterm)
		     (parse-conjunct cond-expr))
	    :elsex (ttmrg-add-path-cond-set
		     (ttmrg-add-path-cond-tterm elsex tterm)
		     (parse-conjunct (negate cond-expr)))))))
    (:fncall
      (b* ((new-args (ttmrg-list-update-path-cond (ttmrg->args tterm) tterm))
	   (new-guts (make-ttmrg-guts-fncall
		       :f (ttmrg->f tterm)
		       :args new-args)))
	(make-ttmrg :path-cond (ttmrg->path-cond tterm)
		    :judgements (ttmrg->judgements tterm)
		    :guts new-guts))))
  ///
  (defcong ttmrg-equiv ttmrg-equiv (ttmrg-update-path-cond-children tterm) 1)
  (more-returns
    (new-tt :name ttmrg->path-cond-of-ttmrg-update-path-cond-children
      (ttmrg->path-cond-equiv new-tt tterm))

    (new-tt :name ttmrg->judgements-of-ttmrg-update-path-cond-children
      (ttmrg->judgements-equiv new-tt tterm))

    (new-tt :name ttmrg->kind-of-ttmrg-update-path-cond-children
      (ttmrg->kind-equiv new-tt tterm))))

(local (defrule ttmrg-equiv-of-var-or-quote
  (implies
    (or (equal (ttmrg->kind tterm) :var)
	(equal (ttmrg->kind tterm) :quote))
    (ttmrg-equiv (ttmrg-update-path-cond-children tterm)
		 tterm))
  :in-theory (enable ttmrg-update-path-cond-children)))

(local (defrule lemma-if-details
  (let* ((condx (ttmrg->condx tterm))
	 (thenx (ttmrg->thenx tterm))
	 (elsex (ttmrg->elsex tterm))
	 (cond-expr  (ttmrg->expr condx))
	 (new-tt (ttmrg-update-path-cond-children tterm))
         (new-condx (ttmrg-add-path-cond-tterm condx tterm))
	 (new-thenx (ttmrg-add-path-cond-set
		      (ttmrg-add-path-cond-tterm thenx tterm)
		      (parse-conjunct cond-expr)))
	 (new-elsex (ttmrg-add-path-cond-set
		      (ttmrg-add-path-cond-tterm elsex tterm)
		      (parse-conjunct (negate cond-expr)))))
    (implies (equal (ttmrg->kind tterm) :if)
	     (and (ttmrg-equiv (ttmrg->condx new-tt) new-condx)
		  (ttmrg-equiv (ttmrg->thenx new-tt) new-thenx)
		  (ttmrg-equiv (ttmrg->elsex new-tt) new-elsex))))
  :in-theory (enable ttmrg-update-path-cond-children)))

(local (defrule lemma-fncall-details
  (implies (equal (ttmrg->kind tterm) :fncall)
    (let* ((new-tt (ttmrg-update-path-cond-children tterm))
	   (args (ttmrg->args tterm))
	   (new-args (ttmrg->args new-tt)))
      (ttmrg-list-equiv new-args (ttmrg-list-update-path-cond args tterm))))
  :in-theory (enable ttmrg-update-path-cond-children)))

(local (defrule ttmrg->judgements-and-expr-of-ttmrg-update-path-cond-children
  (let ((new-tt (ttmrg-update-path-cond-children tterm)))
    (ttmrg->judgements-and-expr-equiv new-tt tterm))
  :in-theory (enable ttmrg->judgements-and-expr-equiv)
  :prep-lemmas (
    (defrule lemma-fncall-f
      (let ((new-tt (ttmrg-update-path-cond-children tterm)))
	(implies (equal (ttmrg->kind tterm) :fncall)
		 (ttmrg->f-equiv new-tt tterm)))
      :in-theory (enable ttmrg-update-path-cond-children
			 ttmrg->f ttmrg->f-equiv))
    (defrule lemma-equal
      (let ((new-tt (ttmrg-update-path-cond-children tterm)))
	(equal (ttmrg->expr new-tt) (ttmrg->expr tterm)))
      :use((:instance
	     ttmrg->expr (tterm (ttmrg-update-path-cond-children tterm)))
	   (:instance ttmrg->expr))))))

(defrule ttmrg->expr-of-ttmrg-update-path-cond-children
  (let ((new-tt (ttmrg-update-path-cond-children tterm)))
    (ttmrg->expr-equiv new-tt tterm)))

(defrule ttmrg-correct-p-of-ttmrg-update-path-cond-children
  (let ((new-tt (ttmrg-update-path-cond-children tterm)))
    (implies (ttmrg-correct-p tterm a)
	     (ttmrg-correct-p new-tt a)))
  :expand ((ttmrg-correct-p (ttmrg-update-path-cond-children tterm) a)))

(define ttmrg-upcc-ignore-options-and-state
    ((tterm ttmrg-p) (opts acl2::any-p) (state state-p))
  :ignore-ok t
  (ttmrg-update-path-cond-children tterm))

(in-theory (enable ttmrg-upcc-ignore-options-and-state))
(ttmrg-propagate path-cond :pre ttmrg-upcc-ignore-options-and-state)
(in-theory (disable ttmrg-upcc-ignore-options-and-state))


;;-------------------------------------------------------
;; judgements of ground terms


(defrule judge-p-when-call-fn-sym-p
  (implies (fn-sym-p fn)
	   (judge-p (list fn 'x)))
  :in-theory (enable fn-sym-p judge-p))

(defines ev-smtcp-of-ground-term
  (define ev-smtcp-induct (term)
    :flag term
    (if (and (consp term) (not (equal (car term) 'quote)))
      (ev-smtcp-lst-induct (cdr term))
      1))
  (define ev-smtcp-lst-induct (lst)
    :flag list
    (if (consp lst)
      (+ (ev-smtcp-induct (car lst))
	 (ev-smtcp-lst-induct (cdr lst)))
      0))
  ///
  (local (defrule foobar-of-union-equal
     (implies (and (true-listp lst1) (true-listp lst2))
	      (iff (union-equal lst1 lst2)
		   (or lst1 lst2)))))

  (local (defrule simple-term-vars-lst-when-consp
    (implies (consp lst)
	     (iff (acl2::simple-term-vars-lst lst)
		  (or (acl2::simple-term-vars (car lst))
		      (acl2::simple-term-vars-lst (cdr lst)))))
    :in-theory (enable acl2::simple-term-vars-lst)))

  (local (defrule pseudo-term-crock
    (IMPLIES (AND (syntaxp (eq a1 'a1))
		  (PSEUDO-TERMP TERM)
		  (CONSP TERM)
		  (NOT (EQUAL (CAR TERM) 'QUOTE))
		  (EQUAL (EV-SMTCP-LST (CDR TERM) A1)
			 (EV-SMTCP-LST (CDR TERM) A2))
		  (NOT (ACL2::SIMPLE-TERM-VARS-LST (CDR TERM))))
	     (EQUAL (EV-SMTCP TERM A1)
		    (EV-SMTCP TERM A2)))
    :expand (pseudo-termp term)))

  (defthm-ev-smtcp-of-ground-term-flag
    (defthmd ev-smtcp-of-ground-term
      (implies (and (pseudo-termp term)
		    (not (acl2::simple-term-vars term)))
	       (equal (ev-smtcp term a1) (ev-smtcp term a2)))
      :flag term)
    (defthmd ev-smtcp-lst-of-ground-term
      (implies (and (pseudo-term-listp lst)
		    (not (acl2::simple-term-vars-lst lst)))
	       (equal (ev-smtcp-lst lst a1) (ev-smtcp-lst lst a2)))
      :flag list)
    :hints(("Goal" :in-theory (enable acl2::simple-term-vars pseudo-termp pseudo-term-listp)))))

(define judge-set-of-ground-term-help
    ((v acl2::any-p) (recognizers fn-sym-list-p)
     (state state-p))
  :returns (j judge-set-p)
  :measure (len recognizers)
  :verify-guards nil
  (b* ((recognizers (fn-sym-list-fix recognizers))
       ((unless (consp recognizers)) nil)
       ((cons recognizer tl) recognizers)
       (recognizer (fn-sym-fix recognizer))
       (j-tl (judge-set-of-ground-term-help v tl state))
       ((unless (acl2::logicp recognizer (w state))) j-tl)
       ((mv magic-err magic-val)
	(acl2::magic-ev-fncall recognizer (list v) state t nil)))
    (if (and (not magic-err) magic-val)
      (set::insert (list recognizer 'x) j-tl)
      j-tl))
  ///
  (verify-guards judge-set-of-ground-term-help)

  (defcong fn-sym-list-equiv equal
	     (judge-set-of-ground-term-help v recognizers state) 2
    :hints(("Goal" :in-theory '(judge-set-of-ground-term-help
				fn-sym-list-equiv))))

  (defrule correctness-of-judge-set-of-ground-term-help
    (let ((j (judge-set-of-ground-term-help v recognizers state)))
      (implies (ev-smtcp-meta-extract-global-facts)
	       (all<judge-ev> j (list 'quote v) a)))
    :in-theory (disable judge-set-of-ground-term-help)
    :use((:instance lemma-1 (recognizers (fn-sym-list-fix recognizers))))
    :prep-lemmas (
      (acl2::defruled lemma-1
	(let ((j (judge-set-of-ground-term-help v recognizers state)))
	  (implies (and (ev-smtcp-meta-extract-global-facts)
			(fn-sym-list-p recognizers))
		   (all<judge-ev> j (list 'quote v) a)))
	:in-theory (enable judge-ev fn-sym-p)))))

(acl2::defruled all<judge-ev>-when-expr-equal
  (implies (equal (ev-smtcp expr1 a1) (ev-smtcp expr2 a2))
	   (equal (all<judge-ev> j expr1 a1) (all<judge-ev> j expr2 a2)))
  :in-theory (enable all<judge-ev> judge-ev))

(define judge-set-of-ground-term ((tterm ttmrg-p)
				  (recognizers fn-sym-list-p)
				  (state state-p))
  :returns (j judge-set-p)
  ; Perhaps, we should report an error if magic-ev fails.  But, it will
  ; fail if a type-recognizer of tterm.term has non-executable functions.
  ; For now, we will silently ignore failures of magic-ev.
  (let ((expr (ttmrg->expr tterm)))
    (and (not (acl2::simple-term-vars expr))
	 (logic-fnsp expr (w state))
	 (mv-let (magic-err magic-val)
	         (acl2::magic-ev expr nil state t nil)
		 (and (not magic-err)
		      (judge-set-of-ground-term-help magic-val recognizers state)))))
  ///
  (defrule correctness-of-judge-set-of-ground-term
    (let ((j (judge-set-of-ground-term tterm recognizers state)))
      (implies (ev-smtcp-meta-extract-global-facts)
	       (all<judge-ev> j (ttmrg->expr tterm) a)))
    :in-theory (disable all-strategy<judge-ev> w
			correctness-of-judge-set-of-ground-term-help)
    :use((:instance correctness-of-judge-set-of-ground-term-help
		      (v (mv-nth 1 (acl2::magic-ev (ttmrg->expr tterm) nil state t nil))))
	 (:instance all<judge-ev>-when-expr-equal
		      (j (judge-set-of-ground-term-help (ev-smtcp (ttmrg->expr tterm) nil)
							recognizers state))
		      (expr1 (ttmrg->expr tterm)) (a1 a)
		      (expr2 (list 'quote (ev-smtcp (ttmrg->expr tterm) nil))) (a2 a))
	 (:instance lemma-2 (x (ttmrg->expr tterm)) (a0 a) (a1 nil) (a2 a))
	 )
    :prep-lemmas (
      (acl2::defruled lemma-2
        (implies (and (pseudo-termp x)
		      (not (acl2::simple-term-vars x)))
		 (equal (ev-smtcp x a0)
			(ev-smtcp (list 'quote (ev-smtcp x a1)) a2)))
	:use((:instance ev-smtcp-of-ground-term (term x) (a1 a0) (a2 a1)))))))


;; ------------------------------------------------------------------
;;    Judgements of variables

(define judge-set-of-variable
    ((tterm ttmrg-p) (options type-options-p) (state state-p))
  :returns (j judge-set-p)
  (b* ((options (type-options-fix options))
       (supertype (type-options->supertype options))
       (expr (ttmrg->expr tterm))
       (path-cond (ttmrg->path-cond-expr tterm))
       (x (look-up-path-cond expr path-cond supertype))
       (y (extend-judgements x path-cond options state))
       (j (parse-judge-set expr y)))
    (if (equal j '((bad-judgement x))) nil j))
  ///
  (acl2::defruled correctness-of-judge-set-of-variable
    (let ((j (judge-set-of-variable tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (alistp a)
		    (ttmrg->path-cond-ev tterm a))
	       (all<judge-ev> j (ttmrg->expr tterm) a)))
      :in-theory (enable judge-set-of-variable)))


;; ------------------------------------------------------------------
;;    Judgements of if-expressions

(defrule judge-ev-of-if ; move to ttmrg.lisp
  (equal (judge-ev j (list 'if condx thenx elsex) a)
	 (if (ev-smtcp condx a)
	   (judge-ev j thenx a)
	   (judge-ev j elsex a)))
  :in-theory (enable judge-ev))

(define judge-set-of-if ((tterm ttmrg-p))
  :returns (j judge-set-p)
  :guard (equal (ttmrg->kind tterm) :if)
  (and (mbt (and (ttmrg-p tterm) (equal (ttmrg->kind tterm) :if)))
       (set::intersect
	 (ttmrg->judgements (ttmrg->thenx tterm))
	 (ttmrg->judgements (ttmrg->elsex tterm))))
  ///
  (more-returns
    (j :name correctness-of-judge-set-of-if
      (implies (and (equal (ttmrg->kind tterm) :if)
		    (ttmrg-correct-p tterm a)
		    (ttmrg->path-cond-ev tterm a))
	       (all<judge-ev> j (ttmrg->expr tterm) a))
      :hints(("Goal"
	:expand (ttmrg->expr tterm)
	:use((:instance ttmrg->judgements-ev (tterm (ttmrg->thenx tterm)))
	     (:instance ttmrg->judgements-ev (tterm (ttmrg->elsex tterm)))))))))

;; ------------------------------------------------------------------
;;    Judgements of function calls (other than 'if)

; args->judgements-expr reconstructs the pseudo-term (i.e. Yan's version)
;   of the judgements of the arguments to a function call.
;   We prove ev-smtcp-of-args->judgements-expr to show that
;     (and (ttmrg-correct-p tterm)         ; tterm is a correct ttmrg object
;          (ttmrg->path-cond-ev tterm a))  ; the path-cond for term holds in a
;   then the expression that we return holds in a, i.e.:
;     (ev-smtcp (args->judgements-expr args) a)

(define args->judgements-expr ((args ttmrg-list-p))
  :returns (judge-expr pseudo-termp)
  (if (consp args)
    (and-expr
      (and-list-expr (judge-list-flat-expr (ttmrg->judgements (car args))
					   (ttmrg->expr (car args))))
      (args->judgements-expr (cdr args)))
    ''t)
  ///
  (defrule ev-smtcp-of-args->judgements-expr
    (implies (and (ttmrg-list-correct-p args a)
		  (args->path-cond-ev args a))
	     (ev-smtcp (args->judgements-expr args) a))
    :in-theory (enable args->judgements-expr args->path-cond-ev ev-and)
    :prep-lemmas (
      (defrule lemma-1
	(implies
	  (and (judge-list-p j) (pseudo-termp expr))
	  (equal
	    (and-list (judge-ev-lst j expr a))
	    (all-list<judge-ev> j expr a)))
	:rule-classes (
	  (:rewrite :corollary (implies (and (judge-set-p j) (pseudo-termp expr))
					(equal (and-list (judge-ev-lst j expr a))
					       (all<judge-ev> j expr a))))))

      (defrule lemma-2
	(implies
	  (pseudo-term-listp lst)
	  (equal (all-list<pseudo-term-ev> lst a)
		 (and-list (ev-smtcp-lst lst a))))
	  :in-theory (enable and-list pseudo-term-ev))

      (defrule lemma-3
	(let ((j (ttmrg->judgements tterm))
	      (expr (ttmrg->expr tterm)))
	  (equal (ev-smtcp (and-list-expr (judge-list-flat-expr j expr)) a)
		 (ttmrg->judgements-ev tterm a)))
	:expand ((ttmrg->judgements-ev tterm a))))))


(define judge-set-of-fncall ((tterm ttmrg-p)
			     (options type-options-p)
			     (state state-p))
  :returns (j judge-set-p)
  :guard (equal (ttmrg->kind tterm) :fncall)
  (b* (((unless (mbt (and (ttmrg-p tterm) (equal (ttmrg->kind tterm) :fncall))))
	nil)
       (path-cond (ttmrg->path-cond-expr tterm))
       (expr (ttmrg->expr tterm))
       (f (ttmrg->f tterm))
       (actuals (ttmrg->args tterm))
       (actuals-expr (ttmrg-list->expr-list actuals))
       (actuals-judgements-top (args->judgements-expr actuals))
       (functions (type-options->functions options))
       (conspair (assoc-equal f functions))
       ((unless conspair)
	(er hard? "no returns theorem found for ~x0~%" f))
       (rj (returns-judgement
	     f actuals-expr actuals-judgements-top (cdr conspair)
	     path-cond ''t state))
       (xj (extend-judgements rj path-cond options state))
       (j (parse-judge-set expr xj)))
  (and (not (equal j '((bad-judgement x)))) j))
  ///
  (more-returns
    (j :name correctness-of-judge-set-of-fncall
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm a)
		    (alistp a)
		    (equal (ttmrg->kind tterm) :fncall)
		    (ttmrg->path-cond-ev tterm a))
	       (all<judge-ev> j (ttmrg->expr tterm) a))
	:hints(("Goal"
	  :in-theory (e/d (judge-set-of-fncall)
		     (all-strategy<judge-ev>)))))))

;; ------------------------------------------------------------------
;;    Combine the four cases above to get the judgements of a term

(define judgements-of-term ((tterm ttmrg-p)
			    (options type-options-p)
			    (state state-p))
  :returns (new-tt ttmrg-p)
  (let* ((recognizers (type-options->type-recognizers options))
	 (j (case (ttmrg->kind tterm)
	      (:quote  (judge-set-of-ground-term tterm recognizers state))
	      (:var    (judge-set-of-variable tterm options state))
	      (:if     (judge-set-of-if tterm))
	      (:fncall (judge-set-of-fncall tterm options state)))))
    (ttmrg-add-judge-set tterm j))
  ///

  (defrule ttmrg->path-cond-of-judgements-of-term
    (let ((new-tt (judgements-of-term tterm options state)))
      (ttmrg->path-cond-equiv new-tt tterm)))

  (defrule ttmrg->expr-of-judgements-of-term
    (let ((new-tt (judgements-of-term tterm options state)))
      (ttmrg->expr-equiv new-tt tterm)))

  (local (in-theory (disable correctness-of-judge-set-of-if
                             correctness-of-judge-set-of-fncall)))
  (defrule ttmrg-correct-p-of-judgements-of-term
    (let ((new-tt (judgements-of-term tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm a)
		    (alistp a))
	       (and (ttmrg-correct-p new-tt a)
		    (ttmrg->path-cond-equiv new-tt tterm)
		    (ttmrg->guts-equiv new-tt tterm))))
    :use((:instance correctness-of-judge-set-of-variable)
         (:instance correctness-of-judge-set-of-if)
         (:instance correctness-of-judge-set-of-fncall))))


;; -------------------------------------------------------

(in-theory (enable ttmrg-upcc-ignore-options-and-state))
(ttmrg-propagate ti-bottom-up
		 :pre  ttmrg-upcc-ignore-options-and-state
		 :post judgements-of-term
		 :opt-guard type-options-p)
(in-theory (disable ttmrg-upcc-ignore-options-and-state))


; ttmrg-clause: produce an ACL2 clause corresponding to tterm
; This version constructs an expression with 'implies' and 'if' where the
; if-expression is a "translated" and.  We might want to just create the
; clause directly:
; (list ,(not (ttmrg-p (quote ,tterm)))
;       ,(not ,(ttmrg-correct-expr tterm))
;       ,(ttmrg->expr tterm))
; But I'm leaving it in the current form for now to be close to Yan's
; representation.  The big difference between ttmrg-clause and what Yan
; does is that I'm including tterm in the goal so the next clause processor
; can recover it.
(define ttmrg-clause ((tterm ttmrg-p))
  :returns (cl pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
  `(implies
     (if (ttmrg-p (quote ,tterm))
       ,(ttmrg-correct-expr tterm)
       ''nil)
     ,(ttmrg->expr tterm)))


(define type-judge-bottomup-cp ((cl pseudo-term-listp)
                                (smtlink-hint t)
                                state)
  (b* (((unless (pseudo-term-listp cl)) (value (list nil)))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list nil)))
       (goal (disjoin cl))
       ((unless (pseudo-term-syntax-p goal)) (value (list nil)))
       ((type-options h) (construct-type-options smtlink-hint goal))
       (new-tt (ttmrg-propagate-ti-bottom-up-term
		(make-ttmrg-trivial goal) h state))
       (next-cp (cdr (assoc-equal 'type-judge-bottomup *SMT-architecture*)))
       ((if (null next-cp)) (value (list nil)))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (new-cl (ttmrg-clause new-tt))
       (hinted-goal `((hint-please ',the-hint) ,new-cl))
       (- (cw "type-judge-bottomup-cp: ~q0" hinted-goal)))
    (value (list hinted-goal))))


(defrule correctness-of-type-judge-bottomup-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-bottomup-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand (type-judge-bottomup-cp cl hints state)
  :in-theory (enable ttmrg-clause)
  :rule-classes :clause-processor)


; (ttmrg-parse-clause cl) -> (mv fail tterm)
;   cl should be the pseudo-termp returned by (disjoin clause) where clause
;     is a list of disjuncts, where each disjunct satisfies termp.
;   If cl has the form of a clause constructed by (ttmrg-clause tterm),
;     ttmrg-parse-clause returns (mv nil tterm).
;     In this case, we ensure (see ttmrg-parse-clause-when-good-cl) that
;       for any context, a, either (ttmrg-correct-p tterm a) holds or cl
;       is vacously satisified, e.g. a type-hypotheses of cl is violated
;       in context a.  We also ensure that (ttmrg->expr tterm) implies
;       cl in any context a.
;   Otherwise cl does not have the form of a clause constructed by
;     (ttmrg-clause tterm), and (ttmrg-parse-clause cl) reutrns (mv fail tterm)
;     where fail is not nil, and tterm satisfies ttmrg-p (to make guard and
;     returns theorems happy.  The current implementation returns t for
;     fail in this case.
;     TODO: write smt:fail((info acl2::any-p)) -> nil.  Then, we can
;     return clauses that will fail, but the info argument will give
;     potentially useful feedback to the user.

(define ttmrg-parse-clause ((cl pseudo-termp))
  :returns (mv (fail booleanp) (tterm ttmrg-p))
  (b* (((unless (pseudo-termp cl)) (mv t (make-ttmrg)))
       (tterm (case-match cl
		      (('implies ('if ('ttmrg-p tterm) & &) &) tterm)
		      (& nil)))
       ((unless (and (ttmrg-p tterm)
		     (equal (ttmrg-clause tterm) cl)))
	(mv t (make-ttmrg))))
    (mv nil tterm))
  ///
  (defrule ttmrg-parse-clause-correct
    (mv-let
      (fail tterm)
      (ttmrg-parse-clause cl)
      (implies (not fail)
	       (and (ttmrg-correct-p tterm a)
		    (implies (ev-smtcp (ttmrg->expr tterm) a)
			     (ev-smtcp cl a)))))
    :in-theory (enable ttmrg-parse-clause ttmrg-clause)))
