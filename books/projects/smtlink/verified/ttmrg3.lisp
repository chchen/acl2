;; Copyright (C) 2015, University of British Columbia)
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;; This book introduces the ttmrg, ttmrg-guts, and ttmrg-list types.
;; These types provide annotations to terms for type-inference and other
;; reasoning about terms in Smtlink.  The name ttmrg is a placeholder.
;; It should by typed-term (or similar), but only when the integration
;; into the Smtlink code is complete (because there already is a typed-term
;; data structure in the existing code).

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/osets/quantify" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/basics")
(include-book "evaluator")

(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; time to certify (M1 Macbook Pro):
;  without disabling any runes below: 136s
;  disabling the runes following 7.7s
(local (in-theory (disable pseudo-termp ;; Mark is impatient
  symbol-listp pseudo-term-listp-of-cdr-of-pseudo-termp set::sfix-when-empty
  acl2::pseudo-lambdap-of-car-when-pseudo-termp set::insert-identity
  pseudo-term-listp-of-symbol-listp acl2::pseudo-termp-list-cdr set::in-tail
  acl2::true-listp-of-car-when-true-list-listp integerp-when-maybe-integerp
  true-list-listp acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  acl2::symbol-listp-when-not-consp consp-of-cdr-of-pseudo-lambdap
  member-equal acl2::pseudo-termp-car set::nonempty-means-set set::union-in
  acl2::pseudo-termp-cadr-from-pseudo-term-listp maybe-integerp-when-integerp
  acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp set::insert-when-empty
  acl2::integerp-of-car-when-integer-listp integer-listp rational-listp
  acl2::rationalp-of-car-when-rational-listp default-cdr
  acl2::pseudo-lambdap-when-member-equal-of-pseudo-lambda-listp
  acl2::integer-listp-of-cdr-when-integer-listp)))

(define consp-equiv (x y) ; perhaps this should move to ../utils/basics.lisp
  :returns (ok booleanp)
  (equal (consp x) (consp y))
  ///
  (more-returns
    (ok :name consp-equiv-when-equal
      (implies (equal (consp x) (consp y)) ok)))
  (defequiv consp-equiv)
  (defcong consp-equiv equal (consp x) 1))

(defrefinement pseudo-term-list-equiv consp-equiv
  :hints(("Goal"
    :in-theory (enable pseudo-term-list-fix)
    :induct (pairlis$ x y))))

(defsection simple-ev/expr
  (define ev-and ((x pseudo-termp) (y pseudo-termp) (a alistp))
    :returns (x^y acl2::any-p)
    (and ;(mbt (and (pseudo-termp x) (pseudo-termp y)))
	 (ev-smtcp (pseudo-term-fix x) a)
	 (ev-smtcp (pseudo-term-fix y) a))
    ///
    (defcong pseudo-term-equiv equal (ev-and x y a) 1)
    (defcong pseudo-term-equiv equal (ev-and x y a) 2))

  (define and-expr ((x pseudo-termp) (y pseudo-termp))
    :returns (x^y pseudo-termp)
    (list 'if (pseudo-term-fix x) (pseudo-term-fix y) 'nil)
    ///
    (more-returns
      (x^y :name ev-smtcp-of-and-expr
	(equal (ev-smtcp x^y a)
	       (and (ev-smtcp (pseudo-term-fix x) a)
		    (ev-smtcp (pseudo-term-fix y) a))))
      (x^y :name and--expr/ev
         (equal (ev-smtcp x^y a) (ev-and x y a))
	 :hints(("Goal" :in-theory (enable ev-and)))))
    (defcong pseudo-term-equiv equal (and-expr x y) 1)
    (defcong pseudo-term-equiv equal (and-expr x y) 2))

  (define and-list ((lst true-listp))
    :returns (x booleanp)
    (if (consp lst)
      (and (car lst) (and-list (cdr lst)))
      t)
    ///
    (more-returns
      (x :name and-list-when-consp
	(implies (consp lst)
		 (equal x (and (car lst) (and-list (cdr lst))))))))

  (define ev-and-list ((lst pseudo-term-listp) (a alistp))
    :returns (x booleanp)
    (if (consp lst)
      (and (ev-smtcp (pseudo-term-fix (car lst)) a)
	   (ev-and-list (cdr lst) a))
      t)
    ///
    (more-returns
      (x :name ev-and-list-when-consp
	 (implies
	   (consp lst)
	   (equal x
		  (and (ev-smtcp (pseudo-term-fix (car lst)) a)
		       (ev-and-list (cdr lst) a)))))
      (x :name ev-and-list-of-atom
	(implies (not (consp lst)) x)))

    (defcong pseudo-term-list-equiv equal (ev-and-list lst a) 1
      :hints(("Goal" :induct (pairlis$ lst lst-equiv)))))

  (define and-list-expr ((lst pseudo-term-listp))
    :returns (x pseudo-termp)
    (if (consp lst)
      (list 'if (pseudo-term-fix (car lst))
	    (and-list-expr (cdr lst)) ''nil)
      ''t)
    ///
    (more-returns
      (x :name ev-smtcp-of-and-list-expr
	 (implies (pseudo-term-listp lst)
		  (equal (ev-smtcp x a)
			 (and-list (ev-smtcp-lst lst a)))))
      (x :name and-list--expr/ev
	(equal (ev-smtcp x a) (ev-and-list lst a))
	:hints(("Goal" :in-theory (enable ev-and-list)))))
    (defcong pseudo-term-list-equiv equal (and-list-expr lst) 1
      :hints(("Goal" :induct (pairlis$ lst lst-equiv)))))

  (define implies-expr ((x pseudo-termp) (y pseudo-termp))
    :returns (x=>y pseudo-termp)
    (and (pseudo-termp x) (pseudo-termp y) `(if ,x (if ,y 't 'nil) 't))
    ///
    (more-returns
      (x=>y :name ev-smtcp-of-implies-expr
        (implies (and (pseudo-termp x) (pseudo-termp y) (alistp a))
           (equal (ev-smtcp x=>y a)
		  (implies (ev-smtcp x a) (ev-smtcp y a))))))))

(defsection judge ; type judgements
  (defines judge
    :flag-local nil
    (define judge-p ((x acl2::any-p))
      :returns (ok booleanp)
      :flag term
      (if (consp x)
	(if (equal (car x) 'quote)
	  (and (consp (cdr x)) (equal (cddr x) nil))
	  (and (symbolp (car x)) (judge-list-p (cdr x))))
	(and (symbolp x)
	     (or (equal x 'x) (not x)))))
    (define judge-list-p ((lst acl2::any-p))
      :returns (ok booleanp)
      :flag list
      (if (consp lst)
	(and (judge-p (car lst)) (judge-list-p (cdr lst)))
	(not lst)))
    ///
    (define judge-fix ((j judge-p))
      :returns (j-fix judge-p)
      (mbe :logic (and (judge-p j) j) :exec j)
      ///
      (more-returns
	(j-fix :name judge-fix-when-judge-p
	  (implies (judge-p j) (equal j-fix j)))
	(j-fix :name idempotence-of-judge-fix
	       (equal (judge-fix j-fix) j-fix))))

    (deffixtype judge
      :pred judge-p
      :equiv judge-equiv
      :fix judge-fix
      :define t
      :forward t
      :topic judge)

    (deflist judge-list
      :pred judge-list-p
      :elt-type judge-p
      :fix judge-list-fix
      :true-listp t)

    (defthm-judge-flag
      (defthm pseudo-termp-when-judge-p
	(implies (judge-p x) (pseudo-termp x))
	:rule-classes ((:rewrite) (:forward-chaining))
	:flag term)
      (defthm pseudo-term-listp-when-judge-list-p
	(implies (judge-list-p lst) (pseudo-term-listp lst))
	:rule-classes ((:rewrite) (:forward-chaining))
	:flag list)
      :hints(("Goal" :in-theory (enable judge-p judge-list-p
					pseudo-termp pseudo-term-listp))))

    (define judge-ev ((j judge-p) (term pseudo-termp) (a alistp))
      :returns (x acl2::any-p)
      (ev-smtcp `((lambda (x) ,(pseudo-term-fix j)) ,term) a))

    (define judge-alist-equiv ((x symbol-alistp) (y symbol-alistp))
      :returns (ok booleanp)
      (equal (assoc-equal 'smt::x x) (assoc-equal 'smt::x y))
      ///
      (defequiv judge-alist-equiv))

    (local (in-theory (enable judge-alist-equiv ev-smtcp-of-fncall-args)))
    (defthm-judge-flag
      (defthm judge-ev-when-judge-alist-equiv
	(implies (and (judge-p x) (judge-alist-equiv a0 a1))
		 (equal (ev-smtcp x a0) (ev-smtcp x a1)))
	:flag term)
      (defthm judge-ev-lst-when-judge-alist-equiv
	(implies (and (judge-list-p lst) (judge-alist-equiv a0 a1))
		 (equal (ev-smtcp-lst lst a0) (ev-smtcp-lst lst a1)))
	:flag list)))


  (fty::defset judge-set
    :elt-type judge-p
    :elementp-of-nil t)

  (defrule acl2-count-of-judge-set-fix
    (<= (acl2-count (judge-set-fix x)) (acl2-count x))
    :rule-classes (:linear :rewrite)
    :in-theory (enable judge-set-fix))

  (defrule judge-set-p-implies-judge-list-p
    (implies (judge-set-p j)
	     (judge-list-p j))
    :rule-classes ((:rewrite) (:forward-chaining))
    :in-theory (enable judge-set-p judge-list-p))

  (defrule judge-set-p-when-judge-list-p-and-setp
    (implies (and (std::setp s) (judge-list-p s))
	     (judge-set-p s))
	:in-theory (enable judge-set-p std::setp))

  (set::quantify-predicate (judge-ev judge term a)
    :set-guard  ((judge-set-p ?set))
    :list-guard ((judge-list-p ?list))
    :arg-guard ((pseudo-termp term) (alistp a))
    :in-package-of judge-ev)

  (define judge-set-expr ((J judge-set-p))
    :returns (x pseudo-termp)
    :verify-guards nil
    (if (set::empty J)
      ''t
      (and-expr (pseudo-term-fix (set::head J))
		(judge-set-expr (set::tail J))))
    ///
    (verify-guards judge-set-expr)
    (defrule judge-set--ev/expr  
      (equal (ev-smtcp `((lambda (x) ,(judge-set-expr J)) ,term) a)
	     (all<judge-ev> j term a))
      :in-theory (enable judge-set-expr all<judge-ev> judge-ev ev-and))))


(defsection pseudo-term-set ; added for path-conditions, may find broader uses in Smtlink
  (fty::defset pseudo-term-set
    :elt-type pseudo-termp
    :elementp-of-nil t)

  (defrule acl2-count-of-pseudo-term-set-fix
    (<= (acl2-count (pseudo-term-set-fix x)) (acl2-count x))
    :rule-classes (:linear :rewrite)
    :in-theory (enable pseudo-term-set-fix))

  (defrule pseudo-term-list-p-when-pseudo-term-set-p
    (implies (pseudo-term-set-p x) (pseudo-term-listp x))
    :rule-classes ((:rewrite) (:forward-chaining))
    :in-theory (enable pseudo-term-set-p pseudo-term-listp))

  (defrule pseudo-term-set-p-when-pseudo-term-listp-and-setp
    (implies (and (std::setp s) (pseudo-term-listp s))
	     (pseudo-term-set-p s))
	:in-theory (enable pseudo-term-set-p std::setp))

  (define pseudo-term-ev ((term pseudo-termp) (a alistp))
    :returns (x acl2::any-p)
    (ev-smtcp (pseudo-term-fix term) a))

  (set::quantify-predicate (pseudo-term-ev term a)
      :set-guard  ((pseudo-term-set-p ?set))
      :list-guard ((pseudo-term-listp ?list))
      :arg-guard ((alistp a))
      :in-package-of pseudo-term-ev)

  (defrule ev-and-list-equals-all-list<pseudo-term-ev>
    (implies (pseudo-term-listp x)
	     (equal (ev-and-list x a)
		    (all-list<pseudo-term-ev> x a)))
    :in-theory (enable ev-and-list all-list<pseudo-term-ev> pseudo-term-ev))


  (define pseudo-term-set-expr ((cl pseudo-term-set-p))
    :returns (x pseudo-termp)
    :verify-guards nil
    (if (set::empty cl)
      ''t
      (and-expr (set::head cl)
		(pseudo-term-set-expr (set::tail cl))))
    ///
    (verify-guards pseudo-term-set-expr)
    (defrule pseudo-term-set--ev/expr  
       (equal (ev-smtcp (pseudo-term-set-expr cl) a)
	      (all<pseudo-term-ev> cl a))
      :in-theory (enable pseudo-term-set-expr pseudo-term-ev all<pseudo-term-ev> ev-and))))

(defsection ttmrg
  (set-well-founded-relation l<)
  (fty::deftypes ttmrg
    (defprod ttmrg
      :measure (list (acl2-count x) 2)
      ((path-cond pseudo-term-set-p :default nil)
       (judgements judge-set-p :default nil)
       (guts ttmrg-guts :default (ttmrg-guts-var nil))))

    ; (for now) ttmrg-guts doesn't support lambda-expressions
    ; We assume that the clause has already been through expand-cp.
    (deftagsum ttmrg-guts
      :measure (list (acl2-count x) 1)
      (:var ((name symbolp)))
      (:quote ((val acl2::any-p)))
      (:if ((condx ttmrg-p)
	    (thenx ttmrg-p)
	    (elsex ttmrg-p)))
      (:fncall ((f symbolp :reqfix (if (not (equal f 'quote)) f 'bad-quote))
	        (args ttmrg-list-p))
	       :require (not (equal f 'quote))))

    (deflist ttmrg-list
      :elt-type ttmrg-p
      :true-listp t
      :measure (list (acl2-count x) 0)))

  (set-well-founded-relation o<)

  (defrefinement ttmrg-list-equiv consp-equiv
     :rule-classes (:refinement :forward-chaining)
     :hints(("Goal"
       :in-theory (enable ttmrg-list-equiv consp-equiv)
       :expand ((ttmrg-list-fix x)
		(ttmrg-list-fix y)))))

  ; We want ttmrg objects to be abstracted behind their accessor functions.
  ; To support this, we'll define per-field equivalence relations.
  (defmacro ttmrg->field-equiv (field-name)
    (let* ((access-fn (symcat 'ttmrg-> field-name))
	   (equiv-fn (symcat access-fn '-equiv))
	   (equal-implies-equiv (symcat equiv-fn '-when-equal- access-fn)))
      `(define ,equiv-fn ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
	 :returns (ok booleanp)
         (equal (,access-fn tterm1) (,access-fn tterm2))
         ///
         (defequiv ,equiv-fn)
	 (defcong ,equiv-fn equal (,access-fn tterm) 1)
	 (defrefinement ttmrg-equiv ,equiv-fn)
	 (defrule ,equal-implies-equiv
           (implies (equal (,access-fn tterm1) (,access-fn tterm2))
		    (,equiv-fn tterm1 tterm2))))))

  (ttmrg->field-equiv path-cond)
  (ttmrg->field-equiv judgements)
  (ttmrg->field-equiv guts)

  ; short-cuts to access fields of ttmrg->guts
  (define ttmrg->kind ((tterm ttmrg-p))
    :returns (kind keywordp :hints(("Goal" :in-theory (enable ttmrg-guts-kind))))
    (ttmrg-guts-kind (ttmrg->guts tterm))
    ///
    (ttmrg->field-equiv kind)
    (defrefinement ttmrg->guts-equiv ttmrg->kind-equiv)
    (defrule ttmrg->kind-of-ttmrg
      (equal (ttmrg->kind (ttmrg path-cond judgments guts))
	     (ttmrg-guts-kind guts)))
    (more-returns ttmrg->kind
      (kind :name ttmrg->kind-possibilities
        (or (equal kind :var) (equal kind :quote) (equal kind :if) (equal kind :fncall))
	:rule-classes ((:rewrite) (:forward-chaining :trigger-terms ((ttmrg->kind tterm))))
	:hints(("Goal" :expand ((ttmrg->kind tterm)))))))

  (defmacro guts-shortcut (kind field-name field-type field-equiv)
    (let* ((access-fn (symcat 'ttmrg-> field-name))
	   (guts-access-fn (symcat 'ttmrg-guts- kind '-> field-name))
	   (equiv-fn (symcat access-fn '-equiv))
	   (equal-implies-equiv (symcat equiv-fn '-when-equal- access-fn))
	   (access-of-constructor (symcat access-fn '-of-ttmrg)))
      `(define ,access-fn ((tterm ttmrg-p))
	 :returns (,field-name ,field-type)
	 :guard (equal (ttmrg->kind tterm) ,kind)
	 :guard-hints(("Goal" :in-theory (enable ttmrg->kind)))
	 (,guts-access-fn (ttmrg->guts tterm))
	 ///
	 (defcong ttmrg->guts-equiv equal (,access-fn tterm) 1
	   :hints(("Goal" :in-theory (enable ttmrg->guts-equiv ,access-fn))))
	 (define ,equiv-fn ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
	   :returns (ok booleanp)
	   :guard (and (equal (ttmrg->kind tterm1) ,kind)
		       (equal (ttmrg->kind tterm2) ,kind))
	   :guard-hints(("Goal" :in-theory (enable ttmrg->kind)))
	   (,field-equiv (,access-fn tterm1) (,access-fn tterm2))
	   ///
	   (defequiv ,equiv-fn)
	   (defcong ,equiv-fn ,field-equiv (,access-fn tterm) 1)
	   (defrefinement ttmrg->guts-equiv ,equiv-fn)
	   (defrule ,equal-implies-equiv
	     (implies (equal (,access-fn tterm1) (,access-fn tterm2))
		      (,equiv-fn tterm1 tterm2)))
	   (defrule ,access-of-constructor
             (,field-equiv (,access-fn (ttmrg path-cond judgements guts))
			   (,guts-access-fn guts)))))))

  (guts-shortcut :var name symbolp equal)
  (guts-shortcut :quote val acl2::any-p equal)
  (guts-shortcut :if condx ttmrg-p ttmrg-equiv)
  (guts-shortcut :if thenx ttmrg-p ttmrg-equiv)
  (guts-shortcut :if elsex ttmrg-p ttmrg-equiv)
  (guts-shortcut :fncall f symbolp equal)
  (more-returns ttmrg->f
    (f :name ttmrg->f-not-equal-quote
       (not (equal f 'quote))
       :hints(("Goal" :in-theory (enable ttmrg->f)))))
  (guts-shortcut :fncall args ttmrg-list-p ttmrg-list-equiv)

  ; reconstruct the pseudo-termp from a ttmrg-p, and likewise for ttmrg-list-p
  (defines ttmrg->expr
    :hints(("Goal"
      :in-theory (enable ttmrg->kind ttmrg->args
			 ttmrg->condx ttmrg->thenx ttmrg->elsex)))
    :returns-hints(("Goal" :in-theory (enable pseudo-termp)))
    (define ttmrg->expr ((tterm ttmrg-p))
      :returns (expr pseudo-termp)
      :flag term
      :measure (ttmrg-count tterm)
      (case (ttmrg->kind tterm)
	(:var    (ttmrg->name tterm))
	(:quote  (kwote (ttmrg->val tterm)))
	(:if     `(if ,(ttmrg->expr (ttmrg->condx tterm))
		    ,(ttmrg->expr (ttmrg->thenx tterm))
		    ,(ttmrg->expr (ttmrg->elsex tterm))))
	(:fncall (list* (ttmrg->f tterm)
			(ttmrg-list->expr-list (ttmrg->args tterm))))))

    (define ttmrg-list->expr-list ((lst ttmrg-list-p))
      :flag list
      :returns (expr-lst pseudo-term-listp)
      :measure (ttmrg-list-count lst)
      (if (consp lst)
	(cons (ttmrg->expr (car lst))
	      (ttmrg-list->expr-list (cdr lst)))
	nil))
    ///
    (more-returns ttmrg-list->expr-list
      (expr-lst :name ttmrg-list->expr-list-when-consp
        (implies (consp lst)
		 (equal expr-lst
		        (cons (ttmrg->expr (car lst))
			      (ttmrg-list->expr-list (cdr lst)))))
	:hints(("Goal" :expand ((ttmrg-list->expr-list lst)))))

      (expr-lst :name ttmrg-list->expr-list-when-atom
        (implies (not (consp lst)) (not expr-lst))
	:hints(("Goal" :expand ((ttmrg-list->expr-list lst))))))

    (defrule ttmrg-list->expr-list-of-cons
      (equal (ttmrg-list->expr-list (cons tterm lst))
	     (cons (ttmrg->expr tterm) (ttmrg-list->expr-list lst)))))

    
    (define ttmrg->expr-equiv ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
      :returns (ok booleanp)
      (equal (ttmrg->expr tterm1) (ttmrg->expr tterm2))
      ///
      (defequiv ttmrg->expr-equiv)
      (defrefinement ttmrg->guts-equiv ttmrg->expr-equiv
        :hints(("Goal"
	  :in-theory (disable ttmrg->guts-equiv)
	  :expand ((ttmrg->expr x) (ttmrg->expr y)))))
      (defcong ttmrg->expr-equiv equal (ttmrg->expr tterm) 1)
      (defrule ttmrg->expr-equiv-when-equal
        (implies (equal (ttmrg->expr tterm1) (ttmrg->expr tterm2))
		 (ttmrg->expr-equiv tterm1 tterm2))))

    (define ttmrg-list->expr-list-equiv ((lst1 ttmrg-list-p) (lst2 ttmrg-list-p))
      :returns (ok booleanp)
      (equal (ttmrg-list->expr-list lst1) (ttmrg-list->expr-list lst2))
      ///
      (defequiv ttmrg-list->expr-list-equiv)
      (defrefinement ttmrg-list-equiv ttmrg-list->expr-list-equiv
	:hints(("Goal"
	  :in-theory (enable ttmrg-list->expr-list ttmrg-list-fix)
	  :induct (pairlis$ x y))))
      (defcong ttmrg-list->expr-list-equiv equal (ttmrg-list->expr-list lst) 1)

      (defrule ttmrg-list->expr-equiv-when-equal
        (implies (equal (ttmrg-list->expr-list lst1)
			(ttmrg-list->expr-list lst2))
		 (ttmrg-list->expr-list-equiv lst1 lst2)))

      (defrule ttmrg-list->expr-list-equiv-of-cons
	(equal (ttmrg-list->expr-list-equiv (cons tterm1 lst1)
					    (cons tterm2 lst2))
	       (and (ttmrg->expr-equiv tterm1 tterm2)
		    (ttmrg-list->expr-list-equiv lst1 lst2)))
	:in-theory (enable ttmrg-list->expr-list-equiv))

      (defrule ttmrg-list->expr-list-equiv-when-atom
	(iff (ttmrg-list->expr-list-equiv nil lst)
	     (not (consp lst)))
	:in-theory (enable ttmrg-list->expr-list)))

  (define ttmrg->expr-count ((tterm ttmrg-p))
    :returns (d natp)
    (acl2-count (ttmrg->expr tterm))
    ///

      (more-returns ttmrg->expr-count
	(d :name ttmrg->condx-decreases-ttmrg->expr-count
	   (implies (equal (ttmrg->kind tterm) :if)
		    (<  (ttmrg->expr-count (ttmrg->condx tterm)) d))
	   :hints(("Goal" :expand ((ttmrg->expr tterm))))
	   :rule-classes (:rewrite :linear))

	(d :name ttmrg->thenx-decreases-ttmrg->expr-count
	   (implies (equal (ttmrg->kind tterm) :if)
		    (< (ttmrg->expr-count (ttmrg->thenx tterm)) d))
	   :hints(("Goal" :expand ((ttmrg->expr tterm))))
	   :rule-classes (:rewrite :linear))

	(d :name ttmrg->elsex-decreases-ttmrg->expr-count
	   (implies (equal (ttmrg->kind tterm) :if)
		    (< (ttmrg->expr-count (ttmrg->elsex tterm)) d))
	   :hints(("Goal" :expand ((ttmrg->expr tterm))))
	   :rule-classes (:rewrite :linear))))

  (define ttmrg-list->expr-list-count ((lst ttmrg-list-p))
    :returns (d natp)
    (acl2-count (ttmrg-list->expr-list lst))
    ///
    (more-returns ttmrg-list->expr-list-count
      (d :name car-decreases-ttmrg-list->expr-list-count
	 (implies (consp lst)
		  (< (ttmrg->expr-count (car lst)) d))
	 :hints(("Goal"
	   :expand ((ttmrg-list->expr-list lst)
		    (ttmrg->expr-count (car lst)))))
	 :rule-classes (:rewrite :linear))

      (d :name cdr-decreases-ttmrg-list->expr-list-count
	 (implies (consp lst)
		  (< (ttmrg-list->expr-list-count (cdr lst)) d))
	 :hints(("Goal"
	   :expand ((ttmrg-list->expr-list lst))))
	 :rule-classes (:rewrite :linear))

      (d :name ttmrg-list->expr-list-count-when-consp
	(implies (consp lst)
		 (equal d
			(+ (ttmrg->expr-count (car lst))
			   (ttmrg-list->expr-list-count (cdr lst))
			   1)))
       :hints(("Goal" :in-theory (enable ttmrg->expr-count))))

      (d :name ttmrg-list->expr-list-count-when-atom
	(implies (not (consp lst)) (equal d 0))
	:hints(("Goal" :expand (
	  (ttmrg-list->expr-list-count lst)
	  (ttmrg-list->expr-list lst))))))

    (more-returns ttmrg->expr-count
      (d :name ttmrg->args-decreases-ttmrg->expr-count
	 (implies (equal (ttmrg->kind tterm) :fncall)
		  (< (ttmrg-list->expr-list-count (ttmrg->args tterm)) d))
	 :hints(("Goal"
	   :in-theory (enable ttmrg->expr)
	   :expand ((ttmrg->expr-count tterm))))
	 :rule-classes (:rewrite :linear))))

  (define ttmrg->expr-count-equiv ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
    :returns (ok booleanp)
    (equal (ttmrg->expr-count tterm1) (ttmrg->expr-count tterm2))
    ///
    (defequiv ttmrg->expr-count-equiv)
    (defcong ttmrg->expr-count-equiv equal (ttmrg->expr-count tterm) 1
      :rule-classes (:congruence :rewrite))
    (defrefinement ttmrg->expr-equiv ttmrg->expr-count-equiv
      :hints(("Goal" :in-theory (enable ttmrg->expr-count)))))

  (define ttmrg-list->expr-list-count-equiv ((lst1 ttmrg-list-p)
					     (lst2 ttmrg-list-p))
    :returns (ok booleanp)
    (equal (ttmrg-list->expr-list-count lst1)
	   (ttmrg-list->expr-list-count lst2))
    ///
    (defequiv ttmrg-list->expr-list-count-equiv)
    (defcong ttmrg-list->expr-list-count-equiv equal
	     (ttmrg-list->expr-list-count lst) 1
      :rule-classes (:congruence :rewrite))
    (defrefinement ttmrg-list->expr-list-equiv ttmrg-list->expr-list-count-equiv
      :hints(("Goal" :in-theory (enable ttmrg-list->expr-list-count)))))

  (define ttmrg->path-cond-ev ((tterm ttmrg-p) (a alistp))
    :returns (x booleanp)
    (all<pseudo-term-ev> (ttmrg->path-cond tterm) a)
    ///
    (defcong ttmrg->path-cond-equiv equal (ttmrg->path-cond-ev tterm a) 1))

  (define ttmrg->path-cond-expr ((tterm ttmrg-p))
    :returns (x pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
    (pseudo-term-set-expr (ttmrg->path-cond tterm))
    ///
    (more-returns
      (x :name ttmrg->path-cond--expr/ev
	(equal (ev-smtcp x a) (ttmrg->path-cond-ev tterm a))
        :hints(("Goal" :in-theory (enable ttmrg->path-cond-ev))))))

  (define ttmrg-list->path-cond-equiv ((lst1 ttmrg-list-p) (lst2 ttmrg-list-p))
    :returns (ok booleanp)
    (if (consp lst1)
      (and (consp lst2)
	   (ttmrg->path-cond-equiv (car lst1) (car lst2))
	   (ttmrg-list->path-cond-equiv (cdr lst1) (cdr lst2)))
      (not (consp lst2)))
    ///
    (local (defrule reflexivity
      (ttmrg-list->path-cond-equiv x x)))
    (local (defrule commutativity
      (equal (ttmrg-list->path-cond-equiv x y)
	     (ttmrg-list->path-cond-equiv y x))))
    (defrule ttmrg-list->path-cond-equiv-when-consp
      (implies (consp lst1)
	       (equal (ttmrg-list->path-cond-equiv lst1 lst2)
		      (and (consp lst2)
			   (ttmrg->path-cond-equiv (car lst1) (car lst2))
			   (ttmrg-list->path-cond-equiv (cdr lst1) (cdr lst2))))))
    (defrule ttmrg-list->path-cond-equiv-when-atom
      (implies (not (consp lst1))
	       (equal (ttmrg-list->path-cond-equiv lst1 lst2)
		      (not (consp lst2)))))
    (defequiv ttmrg-list->path-cond-equiv)
    (defrefinement ttmrg-list-equiv ttmrg-list->path-cond-equiv)
    (defrefinement ttmrg-list->path-cond-equiv consp-equiv))

  (define ttmrg->judgements-and-expr-equiv ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
    :returns (ok booleanp)
    (and (ttmrg->judgements-equiv tterm1 tterm2)
	 (ttmrg->expr-equiv tterm1 tterm2))
    ///
    (defrule ttmrg->judgements-and-expr-equiv-when-judgements-and-expr-equal
      (implies (and (ttmrg->judgements-equiv tterm1 tterm2)
		    (ttmrg->expr-equiv tterm1 tterm2))
	       (ttmrg->judgements-and-expr-equiv tterm1 tterm2)))
    (defequiv ttmrg->judgements-and-expr-equiv)
    (defrefinement ttmrg->judgements-and-expr-equiv ttmrg->judgements-equiv)
    (defrefinement ttmrg->judgements-and-expr-equiv ttmrg->expr-equiv)
    (defrefinement ttmrg-equiv ttmrg->judgements-and-expr-equiv))

  (define ttmrg->judgements-ev ((tterm ttmrg-p) (a alistp))
    :returns (x booleanp)
    (all<judge-ev> (ttmrg->judgements tterm) (ttmrg->expr tterm) a)
    ///
    (defcong ttmrg->judgements-and-expr-equiv equal (ttmrg->judgements-ev tterm a) 1))

  (define ttmrg->judgements-expr ((tterm ttmrg-p))
    :returns (x pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
    (and
      `((lambda (x) ,(judge-set-expr (ttmrg->judgements tterm)))
	,(ttmrg->expr tterm)))
    ///
    (more-returns
      (x :name ttmrg->judgements--expr/ev
	(equal (ev-smtcp x a) (ttmrg->judgements-ev tterm a))
        :hints(("Goal" :in-theory (enable ttmrg->judgements-ev)))))))


(defsection ttmrg-correct
  (define args->path-cond-ev ((args ttmrg-list-p) (a alistp))
    :returns (ok booleanp)
    (if (consp args)
      (and (ttmrg->path-cond-ev (car args) a)
           (args->path-cond-ev (cdr args) a))
      t)
    ///
    (more-returns
      (ok :name args->path-cond-ev-when-consp
        (implies (consp args)
		 (equal ok (and (ttmrg->path-cond-ev (car args) a)
				(args->path-cond-ev (cdr args) a)))))
      (ok :name args->path-cond-ev-when-atom
        (implies (not (consp args)) ok)))

    (defcong ttmrg-list->path-cond-equiv equal (args->path-cond-ev args a) 1
      :hints(("Goal"
	:in-theory (enable args->path-cond-ev ttmrg-list->path-cond-equiv)
	:induct (pairlis$ args args-equiv)))))

  (define args->path-cond-expr ((args ttmrg-list-p))
    :returns (expr pseudo-termp)
    (if (consp args)
      (and-expr
	(ttmrg->path-cond-expr (car args))
	(args->path-cond-expr (cdr args)))
      ''t)
    ///
    (more-returns
      (expr :name args->path-cond--expr/ev
	(equal (ev-smtcp expr a)
	       (args->path-cond-ev args a))
	:hints(("Goal" :in-theory (enable args->path-cond-ev ev-and))))))

  (defines ttmrg-correct
    (define ttmrg-correct-p ((tterm ttmrg-p) (a alistp))
      :returns (ok booleanp)
      :flag term
      :measure (ttmrg->expr-count tterm)
      (b* ((path-eval (ttmrg->path-cond-ev tterm a))
	   (judge-eval (ttmrg->judgements-ev tterm a))
	   ((unless (implies path-eval judge-eval)) nil)
	   ((if (equal (ttmrg->kind tterm) :if))
	    (and (ttmrg-correct-p (ttmrg->condx tterm) a)
		 (ttmrg-correct-p (ttmrg->thenx tterm) a)
		 (ttmrg-correct-p (ttmrg->elsex tterm) a)
		 (implies
		   path-eval
		   (and (ttmrg->path-cond-ev (ttmrg->condx tterm) a)
			(if (ev-smtcp (ttmrg->expr (ttmrg->condx tterm)) a)
			  (ttmrg->path-cond-ev (ttmrg->thenx tterm) a)
			  (ttmrg->path-cond-ev (ttmrg->elsex tterm) a))))))
	   ((if (equal (ttmrg->kind tterm) :fncall))
	    (and (ttmrg-list-correct-p (ttmrg->args tterm) a)
		 (implies path-eval
			  (args->path-cond-ev (ttmrg->args tterm) a)))))
      t))

    (define ttmrg-list-correct-p ((lst ttmrg-list-p) (a alistp))
      :returns (ok booleanp)
      :flag list
      :measure (ttmrg-list->expr-list-count lst)
      (if (consp lst)
	(and (ttmrg-correct-p (car lst) a)
	     (ttmrg-list-correct-p (cdr lst) a))
	t))
    ///
    (more-returns ttmrg-correct-p
      (ok :name path-cond-implies-judgements-when-ttmrg-correct-p
	(implies
	  ok
	  (implies (ttmrg->path-cond-ev tterm a)
		   (ttmrg->judgements-ev tterm a))))
      (ok :name ttmrg-correct-p-when-if
	(implies (and ok (equal (ttmrg->kind tterm) :if))
		 (and (ttmrg-correct-p (ttmrg->condx tterm) a)
		      (ttmrg-correct-p (ttmrg->thenx tterm) a)
		      (ttmrg-correct-p (ttmrg->elsex tterm) a)))
	:hints(("Goal" :expand (ttmrg-correct-p tterm a))))
      (ok :name ttmrg-correct-p-when-if-condx
	(implies (and ok (equal (ttmrg->kind tterm) :if)
			 (ttmrg->path-cond-ev tterm a))
		 (ttmrg->path-cond-ev (ttmrg->condx tterm) a))
	:hints(("Goal" :expand (ttmrg-correct-p tterm a))))
      (ok :name ttmrg-correct-p-when-if-thenx
	(implies (and ok (equal (ttmrg->kind tterm) :if)
			 (ttmrg->path-cond-ev tterm a)
			 (ev-smtcp (ttmrg->expr (ttmrg->condx tterm)) a))
		 (ttmrg->path-cond-ev (ttmrg->thenx tterm) a))
	:hints(("Goal" :expand (ttmrg-correct-p tterm a))))
      (ok :name ttmrg-correct-p-when-if-elsex
	(implies (and ok (equal (ttmrg->kind tterm) :if)
			 (ttmrg->path-cond-ev tterm a)
			 (not (ev-smtcp (ttmrg->expr (ttmrg->condx tterm)) a)))
		 (ttmrg->path-cond-ev (ttmrg->elsex tterm) a))
	:hints(("Goal" :expand (ttmrg-correct-p tterm a))))
      (ok :name ttmrg-correct-p-when-fncall
	(implies (and ok (equal (ttmrg->kind tterm) :fncall))
		 (and (ttmrg-list-correct-p (ttmrg->args tterm) a)
		      (implies (ttmrg->path-cond-ev tterm a)
			       (args->path-cond-ev (ttmrg->args tterm) a))))
	:hints(("Goal" :expand (ttmrg-correct-p tterm a))))) 

    (more-returns ttmrg-list-correct-p
      (ok :name ttmrg-list-correct-p-when-consp
	(implies (consp lst)
		 (equal ok
			(and (ttmrg-correct-p (car lst) a)
			     (ttmrg-list-correct-p (cdr lst) a))))
	:hints(("Goal" :expand (ttmrg-list-correct-p lst a))))
      (ok :name ttmrg-list-correct-p-when-atom
	(implies (not (consp lst)) ok)
	:hints(("Goal" :expand ((ttmrg-list-correct-p lst a)))))))

    ; the (defines use-me-for-induction ...) below shows that ttmrg-correct-p
    ; and ttmrg-list-correct-p are preserved under ttmrg-equiv and
    ; ttmrg-list-equiv respectively.  We make the defines local to avoid
    ; cluttering the logical world when we're done.
    (local (defines use-me-for-induction
      (define induct-term ((tterm1 ttmrg-p) (tterm2 ttmrg-p))
	:flag term
	:measure (ttmrg->expr-count tterm1)
	(and
	  (equal (ttmrg->kind tterm1) (ttmrg->kind tterm2))
	  (case (ttmrg->kind tterm1) 
	    (:if (list (induct-term (ttmrg->condx tterm1) (ttmrg->condx tterm2))
		       (induct-term (ttmrg->thenx tterm1) (ttmrg->thenx tterm2))
		       (induct-term (ttmrg->elsex tterm1) (ttmrg->elsex tterm2))))
	    (:fncall (induct-args (ttmrg->args tterm1) (ttmrg->args tterm2)))
	    (otherwise t))))

      (define induct-args ((lst1 ttmrg-list-p) (lst2 ttmrg-list-p))
	:flag args
	:measure (ttmrg-list->expr-list-count lst1)
	(if (and (consp lst1) (consp lst2))
	  (list (consp lst2)
		(induct-term (car lst1) (car lst2))
		(induct-args (cdr lst1) (cdr lst2)))
	  t))
      ///

      (defthm-use-me-for-induction-flag
	(defthm congruence-lemma-term
	  (implies (ttmrg-equiv tterm1 tterm2)
		   (equal (ttmrg-correct-p tterm1 a)
			  (ttmrg-correct-p tterm2 a)))
	  :flag term
	  :rule-classes :congruence)
	(defthm congruence-lemma-args
	  (implies (ttmrg-list-equiv lst1 lst2)
		   (equal (ttmrg-list-correct-p lst1 a)
			  (ttmrg-list-correct-p lst2 a)))
	  :flag args
	  :rule-classes :congruence)
	:hints(("Goal" :in-theory (enable ttmrg-correct-p ttmrg-list-correct-p))))))

    ; "export" the two congruences from use-me-for-induction
    (defcong ttmrg-equiv equal (ttmrg-correct-p tterm a) 1)
    (defcong ttmrg-list-equiv equal (ttmrg-list-correct-p lst a) 1)


  ; ttmrg-correct-expr: the expr counterpart of ttmrg-correct-p
  ;   A "learned from experience" note about functions for traversing ttmrg objects.
  ;   Initially, I wrote function cliques with a function for ttmrg, a function
  ;   for ttmrg-guts, and a function for ttmrg-list to match the deftypes.
  ;   ttmrg-correct-p (defined later in this book) makes checks that the path-conditions
  ;   of actual-parameters are implied by the path-condition for the function call
  ;   (possibly strengthened by the if-condition or its negation).  The path-cond
  ;   field is shared for all forms of ttexpr-guts, and thus in part of the ttmrg
  ;   product.  This means verifying the ttmrg-guts requires knowing the path-cond
  ;   field from the parent ttmrg object.  If the path-cond is passed as a parameter
  ;   to a function for handling the ttmrg-guts, then I need an inducton hypothesis
  ;   for the ttmrg-guts function that says how the value it returns maintains the
  ;   right properties with respect to its path-cond parameter.  This is painful.
  ;     My solution is to use two functions: one for ttmrg-term and one for ttmrg-list.
  ;   The ttmrg-guts function is just absorbed into ttmrg-term.  This is easy enough.
  ;   However, this means that the measure-decreasing expressions are often buried
  ;   in the body of the function.  Thus, we often need
  ;     :ruler-extenders :all
  ;   ttmrg-correct-expr is an example of this.
  (defines ttmrg-correct-expr
    :verify-guards nil
    :ruler-extenders :all
    (define ttmrg-correct-expr ((tterm ttmrg-p))
      :returns (expr pseudo-termp)
      :flag term
      :measure (ttmrg->expr-count tterm)
      (b* (;((unless (mbt (ttmrg-p tterm))) nil)
	   (path  (ttmrg->path-cond-expr  tterm))
	   (judge (ttmrg->judgements-expr tterm))
	   (guts-expr
	     (case (ttmrg->kind tterm)
	       (:var ''t)
	       (:quote ''t)
	       (:if
		 (and-list-expr (list
		   (ttmrg-correct-expr (ttmrg->condx tterm))
		   (ttmrg-correct-expr (ttmrg->thenx tterm))
		   (ttmrg-correct-expr (ttmrg->elsex tterm))
		   (implies-expr
		     path
		     (and-expr
		       (ttmrg->path-cond-expr (ttmrg->condx tterm))
		       (list 'if (ttmrg->expr (ttmrg->condx tterm))
			  (ttmrg->path-cond-expr (ttmrg->thenx tterm))
			  (ttmrg->path-cond-expr (ttmrg->elsex tterm))))))))
	       (:fncall
		 (and-expr
		   (ttmrg-list-correct-expr (ttmrg->args tterm))
		   (implies-expr
		     path
		     (args->path-cond-expr (ttmrg->args tterm))))))))
        (and-expr (implies-expr path judge) guts-expr)))

    (define ttmrg-list-correct-expr ((lst ttmrg-list-p))
      :returns (expr pseudo-termp)
      :flag list
      :measure (ttmrg-list->expr-list-count lst)
      (if (consp lst)
	(and-expr (ttmrg-correct-expr (car lst))
	     (ttmrg-list-correct-expr (cdr lst)))
	''t ;(kwote (equal lst nil))
	))
    ///
    (verify-guards ttmrg-correct-expr)

    (defthm-ttmrg-correct-expr-flag
      (defthm ttmrg-correct-p-equals-ev-of-expr
	(equal (ev-smtcp (ttmrg-correct-expr tterm) a)
	       (ttmrg-correct-p tterm a))
	:flag term)

      (defthm ttmrg-correct-list-p-equals-ev-of-expr
	(equal (ev-smtcp (ttmrg-list-correct-expr lst) a)
	       (ttmrg-list-correct-p lst a))
	:flag list)
      :hints(("Goal"
	:in-theory (enable ttmrg-correct-p ttmrg-list-correct-p
			   ev-and pseudo-term-ev implies-expr))))))
