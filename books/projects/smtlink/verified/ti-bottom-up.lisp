;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg-change")
(include-book "typed-term-fns")
(include-book "judgement-fns")
(include-book "returns-judgement")
(include-book "type-options")
(include-book "../utils/fresh-vars")
(include-book "ttmrg-triv")
(include-book "make-test")

(set-state-ok t)
(set-induction-depth-limit 1)

; Mark is impatient
(local (in-theory (disable pseudo-termp pseudo-term-listp symbol-listp
  boolean-listp member-equal consp-of-pseudo-lambdap
  pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
  pseudo-termp-when-pseudo-term-syntax-p ev-smtcp-of-type-hyp-call
  (:type-prescription pseudo-lambdap) member-equal)))


(define update-path-cond-args-help
    ((ttargs ttmrg-list-p) (new-path-cond conj-p))
  :returns (new-args ttmrg-list-p)
  (if (consp ttargs)
    (cons (strengthen-ttmrg->path-cond (car ttargs) new-path-cond)
	  (update-path-cond-args-help (cdr ttargs) new-path-cond))
    nil)
  ///
  (more-returns
    (new-args :name ttmrg-args-simple-count-of-update-path-cond-args-help
      (equal (ttmrg-args-simple-count new-args)
	     (ttmrg-args-simple-count ttargs))
      :hints(("Goal"
	:in-theory (enable update-path-cond-args-help
			   ttmrg-args-simple-count))))))

(define update-path-cond-term-help ((tterm ttmrg-p))
  :returns (new-args ttmrg-list-p)
  (b* (((ttmrg tterm) tterm)
       ((unless (and (consp tterm.term)
		     (not (equal (car tterm.term) 'quote))))
	(ttmrg->args tterm))
       ((unless (and (equal (car tterm.term) 'if)
		     (consp (cddr (ttmrg->args tterm)))
		     (not (cdddr (ttmrg->args tterm)))))
	(update-path-cond-args-help tterm.args tterm.path-cond)))
    (list (strengthen-ttmrg->path-cond (car tterm.args) tterm.path-cond)
	  (strengthen-ttmrg->path-cond (cadr tterm.args)
	    (conj-cons2 (ttmrg->term (car tterm.args)) tterm.path-cond))
	  (strengthen-ttmrg->path-cond (caddr tterm.args)
	    (conj-cons2 `(not ,(ttmrg->term (car tterm.args)))
			tterm.path-cond))))
  ///
  (more-returns
    (new-args :name ttmrg-args-simple-count-of-update-path-cond-term-help
      (equal (ttmrg-args-simple-count new-args)
	     (ttmrg-args-simple-count (ttmrg->args tterm)))
      :hints(("Goal"
	:in-theory (enable update-path-cond-term-help
			   ttmrg-args-simple-count))))))

(defines update-path-cond
  (define update-path-cond-term ((tterm ttmrg-p))
    :flag term
    :returns (new-tt ttmrg-p)
    :measure (ttmrg-simple-count tterm)
    :verify-guards nil
    (let ((new-args (update-path-cond-term-help tterm)))
      (change-ttmrg->args
	(change-ttmrg->args tterm new-args)
	(update-path-cond-args new-args))))

  (define update-path-cond-args ((ttargs ttmrg-list-p))
    :flag args
    :returns (new-args ttmrg-list-p)
    :measure (ttmrg-args-simple-count ttargs)
    (if (consp ttargs)
      (cons (update-path-cond-term (car ttargs))
	    (update-path-cond-args (cdr ttargs)))
      nil))
  ///
  (verify-guards update-path-cond-term)

  (defrule ttmrg-args-only-changed->args-of-update-path-cond-args
    (ttmrg-args-only-changed->args
      (update-path-cond-args ttargs) ttargs)
    :in-theory (enable ttmrg-args-only-changed->args)
    :prep-lemmas (
      (defrule lemma-*1/3
	(equal (consp (update-path-cond-args ttargs))
	       (consp ttargs))
	:use((:instance update-path-cond-args)))
      (defrule change-ttmrg->args-ttmrg-args-only-changed->args
	(and (equal (ttmrg->term (change-ttmrg->args tterm new-ttargs))
		    (ttmrg->term tterm))
	     (equal (ttmrg->path-cond (change-ttmrg->args tterm new-ttargs))
		    (ttmrg->path-cond tterm)))
	:use((:instance change-ttmrg->args)))
      (defrule lemma-*1/2
	(implies (consp ttargs)
	  (and (equal (ttmrg->term (car (update-path-cond-args ttargs)))
		      (ttmrg->term (car ttargs)))
	       (equal (ttmrg->path-cond (car (update-path-cond-args ttargs)))
		      (ttmrg->path-cond (car ttargs)))))
	  :use((:instance update-path-cond-args)
	       (:instance update-path-cond-term (tterm (car ttargs)))))))

  (local (encapsulate nil
    (defrule ttmrg-args->stronger-path-cond-of-update-path-cond-term-help
      (implies (alistp env)
	(ttmrg-args->stronger-path-cond
	  (ttmrg->args tterm)
	  (update-path-cond-term-help tterm)
	  env))
      :in-theory (enable update-path-cond-term-help
			 ttmrg-args->stronger-path-cond)
      :prep-lemmas (
	(defrule lemma-args
	  (implies (and (alistp env) (pseudo-termp new-path-cond))
	    (ttmrg-args->stronger-path-cond
	      ttargs
	      (update-path-cond-args-help ttargs new-path-cond)
	      env))
	  :in-theory (enable ttmrg-args->stronger-path-cond
			     update-path-cond-args-help
			     strengthen-ttmrg->path-cond))))

    (defrule ttmrg-args-correct-path-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (alistp env)
	     (ev-smtcp (ttmrg->path-cond tterm) env)
	     (consp (ttmrg->term tterm))
	     (not (equal (car (ttmrg->term tterm)) 'quote)))
	(let ((new-ttargs (update-path-cond-term-help tterm)))
	  (if (equal (car (ttmrg->term tterm)) 'if)
	    (and (ev-smtcp (ttmrg->path-cond (car new-ttargs)) env)
		 (if (ev-smtcp (ttmrg->term (car new-ttargs)) env)
		   (ev-smtcp (ttmrg->path-cond (cadr new-ttargs)) env)
		   (ev-smtcp (ttmrg->path-cond (caddr new-ttargs)) env)))
	    (ttmrg-args-correct-path new-ttargs env))))
      :expand ((update-path-cond-term-help tterm)
	       (ttmrg-correct-p tterm))
      :use((:instance ttmrg-correct-sk-necc))
      :prep-lemmas (
	(defrule lemma-args
	  (implies (and (alistp env)
			(conj-p path-cond)
			(ttmrg-args-correct-path ttargs env)
			(ev-smtcp path-cond env))
		   (ttmrg-args-correct-path
		     (update-path-cond-args-help ttargs path-cond)
		     env))
	  :in-theory (enable update-path-cond-args-help
			     ttmrg-args-correct-path))))

    (defrule ttmrg-correct-p-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(ttmrg-correct-p
	  (change-ttmrg->args tterm
			      (update-path-cond-term-help tterm))))
      :use((:functional-instance
	      ttmrg-correct-p-of-change-ttmrg-args--strengthen-path-cond
	(constrain-ttmrg->args-path-cond
	  (lambda (tterm state) (update-path-cond-term-help tterm))))))

    (defrule lemma-0
	(equal (ttmrg->args (change-ttmrg->args tterm new-ttargs))
	       (ttmrg-list-fix new-ttargs))
	:expand (change-ttmrg->args tterm new-ttargs))

    (defrule ttmrg-args-correct-p-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(ttmrg-args-correct-p (update-path-cond-term-help tterm)))
      :in-theory (disable ttmrg-args-correct-p-when-ttmrg-correct-p)
      :use ((:instance ttmrg-args-correct-p-when-ttmrg-correct-p
		       (tterm (change-ttmrg->args
				tterm
				(update-path-cond-term-help tterm))))))

    (defrule ttmrg->args-of-update-path-cond-term-help
      (implies
	(and (ttmrg-correct-p tterm)
	     (ev-smtcp-meta-extract-global-facts))
	(equal (ttmrg->args
		 (change-ttmrg->args tterm (update-path-cond-term-help tterm)))
	       (update-path-cond-term-help tterm))))

    (defrule lemma-correct-p-1
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (ttmrg-args-correct-p
	       (update-path-cond-args (ttmrg->args tterm))))
	(let ((new-tt
	       (change-ttmrg->args
		 tterm
		 (update-path-cond-args (ttmrg->args tterm)))))
	  (and (ttmrg-correct-p new-tt)
	       (equal (ttmrg->term new-tt) (ttmrg->term tterm)))))
      :use((:functional-instance
	ttmrg-correct-p-of-constrain-ttmrg->args-args
	(constrain-ttmrg->args-args
	  (lambda (tterm state)
	     (update-path-cond-args (ttmrg->args tterm)))))))

    (defrule lemma-correct-p-2
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (ttmrg-args-correct-p
	       (update-path-cond-args (update-path-cond-term-help tterm))))
	(let* ((new-args (update-path-cond-term-help tterm))
	       (new-tt
	        (change-ttmrg->args
		  (change-ttmrg->args tterm new-args)
		  (update-path-cond-args new-args))))
	  (and (ttmrg-correct-p new-tt)
	       (equal (ttmrg->term new-tt) (ttmrg->term tterm)))))
      :rule-classes ((:rewrite :match-free :all))
      :in-theory (disable lemma-correct-p-1)
      :use((:instance lemma-correct-p-1
			(tterm (change-ttmrg->args
				 tterm
				 (update-path-cond-term-help tterm))))))))

   (defthm-update-path-cond-flag
     (defthm ttmrg-correct-p-of-update-path-cond-term
       (implies 
	 (and (ev-smtcp-meta-extract-global-facts)
	      (ttmrg-correct-p tterm))
	 (let ((new-tt (update-path-cond-term tterm)))
	   (and (ttmrg-correct-p new-tt)
		(equal (ttmrg->term new-tt) (ttmrg->term tterm)))))
       :flag term)
     (defthm ttmrg-args-correct-p-of-update-path-cond-args
       (implies (and (ev-smtcp-meta-extract-global-facts)
		     (ttmrg-args-correct-p ttargs))
		(ttmrg-args-correct-p (update-path-cond-args ttargs)))
       :flag args)
     :hints(("Goal"
       :in-theory (enable ttmrg-args-correct-p)))))


(defsection move-this-stuff-to-../utils/pseudo-term
  (defines term-q
    :flag-local nil
    (define term-q ((term acl2::any-p))
      :returns (ok booleanp)
      :flag term
      (if (and (consp term)
	             (not (equal (car term) 'quote))
	             (true-listp term))
	        (args-q (cdr term))
	      t))

    (define args-q ((args acl2::any-p))
      :returns (ok booleanp)
      :flag args
      (if (consp args)
	        (and (term-q (car args))
	             (args-q (cdr args)))
	      (null args))))

  ;; Need to show that pseudo-termp implies term-q and pseudo-term-listp
  ;; implies args-q.  This helps because defthm-term-q-flag theorems tend to
  ;; have hypotheses involving pseudo-termp and pseudo-term-listp, and showing
  ;; these implications allows those hypotheses to discharge goals generated
  ;; from term-q and args-q.
  (defthm-term-q-flag
    (defthm pseudo-termp--implies--term-q
      (implies (pseudo-termp term) (term-q term))
      :hints('(:expand ((term-q term))))
      :flag term)

    (defthm pseudo-term-listp--implies--args-q
      (implies (pseudo-term-listp args) (args-q args))
      :hints('(:expand ((args-q args))))
      :flag args)))


;;-------------------------------------------------------
;; judgements of ground terms

(encapsulate nil
  (local (defrule lemma-*1/5
    (implies (consp x) (union-equal x y))))

  (defthm-term-q-flag ev-smtcp-of-ground-term
    (defthmd ev-smtcp-of-ground-term
      (implies (and (pseudo-termp term)
		    (null (acl2::simple-term-vars term))
		    (alistp a1) (alistp a2) (not (equal a1 a2)))
	       (equal (ev-smtcp term a1) (ev-smtcp term a2)))
      :flag term)

    (defthmd ev-smtcp-of-ground-args
      (implies (and (pseudo-term-listp args)
		    (null (acl2::simple-term-vars-lst args))
		    (alistp a1) (alistp a2) (not (equal a1 a2)))
	       (equal (ev-smtcp-lst args a1) (ev-smtcp-lst args a2)))
      :flag args)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp
				      acl2::simple-term-vars acl2::simple-term-vars-lst
				      ev-smtcp-of-fncall-args)))))

(define fn-sym-p ((fn acl2::any-p))
  :returns (ok booleanp)
  (and (symbolp fn)
       (not (equal fn 'quote))
       (not (equal fn 'if))))

(easy-fix fn-sym nil)
(deflist fn-sym-list
  :elt-type fn-sym-p
  :pred fn-sym-list-p
  :true-listp t)

(local (in-theory (enable fn-sym-fix acl2::simple-term-vars)))
(more-returns fn-sym-fix
  (fix-x :name simple-vars-of-call-of-fn-sym-fix
     (equal (acl2::simple-term-vars (cons fix-x args))
	    (acl2::simple-term-vars-lst args))))
(local (in-theory (disable fn-sym-fix acl2::simple-term-vars)))

(local (in-theory (disable 
  DEFAULT-CAR CONSP-OF-IS-CONJUNCT?  DEFAULT-CDR ACL2::PSEUDO-TERMP-OPENER
  ASSOC-EQUAL NIL-OF-ASSOC-EQUAL-OF-PSEUDO-TERM-ALISTP
  PSEUDO-TERM-ALISTP-WHEN-NOT-CONSP PAIRLIS$ IMPLIES-OF-TYPE-PREDICATE-OF-TERM
  PSEUDO-TERMP-WHEN-PSEUDO-CONJ-P IMPLIES-OF-IS-CONJUNCT?  CAR-IS-IF-WHEN-CONJ-CONSP)))

(define judgements-of-ground-term-helper
    ((c pseudo-termp) (recognizers fn-sym-list-p)
     (env symbol-alistp) (state state-p))
  :measure (len recognizers)
  :returns (j conj-p)
  (b* ((recognizers (fn-sym-list-fix recognizers))
       ((unless (consp recognizers)) ''t)
       ((cons hd tl) recognizers)
       (hd (fn-sym-fix hd))
       ((unless (acl2::logicp hd (w state))) ''t)
       ((unless (mbt (pseudo-termp c))) ''t)
       ((unless (logic-fnsp c (w state))) ''t)
       ((unless (null (acl2::simple-term-vars c))) ''t)
       ; BOZO-mrg: should move the evaluaiton of c to judgements-of-ground-term
       ;   (and kwote the result for use here).  Then, we'll only evaluate c once.
       (pred (list hd c))
       ((mv magic-err magic-val) (acl2::magic-ev pred env state t nil))
       (j-tl (judgements-of-ground-term-helper c tl env state)))
    (if (and (not magic-err) magic-val)
      (conj-cons pred j-tl)
      j-tl))
  ///
  (local (in-theory (e/d (acl2::simple-term-vars acl2::simple-term-vars-lst) (alistp w))))
  (defrule judgements-of-ground-term-is-ground-term
    (not (acl2::simple-term-vars (judgements-of-ground-term-helper c recognizers env state)))
    :prep-lemmas (
      (defrule lemma-*1
	(let ((fn (car recognizers))
	      (j-cdr (judgements-of-ground-term-helper c (cdr recognizers) env state)))
	  (implies
	    (and
	      (fn-sym-list-p recognizers)
	      (pseudo-termp c)
	      (not (acl2::simple-term-vars c))
	      (not (acl2::simple-term-vars j-cdr)))
	    (not (acl2::simple-term-vars (conj-cons (list fn c) j-cdr)))))
	:in-theory (disable simple-term-vars-of-conj-cons)
	:use((:instance simple-term-vars-of-conj-cons
			  (hd (list (fn-sym-fix (car recognizers)) c))
			  (tl (judgements-of-ground-term-helper
				c (cdr recognizers) env state)))))))

  (defrule correctness-of-judgements-of-ground-term-helper
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp env)
		  (alistp env2))
	     (ev-smtcp (judgements-of-ground-term-helper c recognizers env state) env2))
    :prep-lemmas (
      (defrule correctness-lemma-1
	  (implies (and (ev-smtcp-meta-extract-global-facts)
			(alistp env))
		   (ev-smtcp (judgements-of-ground-term-helper c recognizers env state) env))
	  :prep-lemmas (
	    (defrule lemma-*1
	      (let ((fn (car recognizers)))
		(implies (and (fn-sym-list-p recognizers)
			      (pseudo-termp c)
			      (alistp env)
			      (acl2::logicp fn (w state))
			      (not (acl2::simple-term-vars c))
			      (logic-fnsp c (w state))
			      (not (mv-nth 0 (acl2::magic-ev (list fn c) env state t nil)))
			      (mv-nth 1 (acl2::magic-ev (list fn c) env state t nil))
			      (ev-smtcp-meta-extract-global-facts))
			 (ev-smtcp (list fn c) env)))
	      :do-not-induct t
	      :in-theory (disable acl2::magic-ev ev-smtcp-meta-extract-magic-ev)
	      :use((:instance ev-smtcp-meta-extract-magic-ev
			        (acl2::x (list (fn-sym-fix (car recognizers)) c))
				(acl2::st state)
				(acl2::hard-errp t)
				(acl2::aokp nil)
				(acl2::alist env)))))
	  ; unless we disable w, lemma-*1/1 won't match "Subgoal *1/1".
	  ; Or, we could expand out w in the statement of lemma-*1/1, but that would be painful.
	  :in-theory (disable w)))
    :hints(("Goal"
      :use((:instance ev-smtcp-of-ground-term
		      (term (judgements-of-ground-term-helper c recognizers env state))
		      (a1 env)
		      (a2 env2)))))))

(make-test ; a simple example
  (equal (judgements-of-ground-term-helper
	   '(unary-- '3)
	   '(booleanp integerp natp rationalp true-listp)
	   nil
	   state)
	 '(if (integerp (unary-- '3))
	    (if (rationalp (unary-- '3))
	      't
	      'nil)
	    'nil))
  :output (:fail (:all . :warn)))

(def-strengthen-correct-ttmrg->top-judgement judgements-of-ground-term
    ((tterm ttmrg-syntax-p)
     (recognizers fn-sym-list-p)
     (state state-p))
  (judgements-of-ground-term-helper (ttmrg->term tterm) recognizers nil state))


;; ------------------------------------------------------------------
;;    Judgements of variables

(define judgements-of-variable-helper
    ((tterm ttmrg-syntax-p) (options type-options-p) (state state-p))
  :returns (judge conj-p)
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       (options (type-options-fix options))
       (supertype (type-options->supertype options)))
    (term-to-conj
      (extend-judgements
	(look-up-path-cond tterm.term tterm.path-cond supertype)
	tterm.path-cond options state)))
  ///
  (more-returns judgements-of-variable-helper
    (judge :name correctness-of-judgements-of-variable-helper
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	       (ev-smtcp judge env))
      :hints(("Goal"
	:in-theory (enable judgements-of-variable-helper))))))

(def-strengthen-correct-ttmrg->top-judgement judgements-of-variable
    ((tterm ttmrg-syntax-p)
     (options type-options-p)
     (state state-p))
  (judgements-of-variable-helper (ttmrg-fix tterm) options state))


(define judgements-of-if ((tterm ttmrg-syntax-p))
  :returns (new-tt ttmrg-p)
  :guard (and (consp (ttmrg->term tterm))
	      (equal (car (ttmrg->term tterm)) 'if))
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       ((unless (mbt (and (consp tterm.term) (equal (car tterm.term) 'if))))
	tterm)
       (thenj (ttmrg->top-judgement (cadr tterm.args)))
       (elsej (ttmrg->top-judgement (caddr tterm.args))))
    (strengthen-ttmrg->top-judgement tterm (conj-common thenj elsej)))
  ///
 (defrule ttmrg-correct-p-of-judgements-of-if
   (let ((new-tt (judgements-of-if tterm)))
     (implies (and (ev-smtcp-meta-extract-global-facts)
		   (ttmrg-correct-p tterm))
	      (and (ttmrg-correct-p new-tt)
		   (equal (ttmrg->term new-tt) (ttmrg->term tterm)))))
   :expand (judgements-of-if tterm)
   :use((:functional-instance correctness-of-strengthen-ttmrg->top-judgement
	   (constrain-ttmrg->top-judgement
	    (lambda (tterm state)
	      (if (and (ttmrg-correct-p tterm)
		       (equal (car (ttmrg->term tterm)) 'if))
		(conj-common
		  (ttmrg->top-judgement (cadr (ttmrg->args tterm)))
		  (ttmrg->top-judgement (caddr (ttmrg->args tterm))))
		''t)))))
   :prep-lemmas (
     (defrule path-cond-implies-judgements
       (implies (and (ttmrg-correct-p tterm)
		     (alistp env)
		     (equal (car (ttmrg->term tterm)) 'if)
		     (ev-smtcp (ttmrg->path-cond tterm) env))
		(ev-smtcp (conj-common
			    (ttmrg->top-judgement (cadr (ttmrg->args tterm)))
			    (ttmrg->top-judgement (caddr (ttmrg->args tterm))))
			  env))
       :use((:instance ttmrg->path-cond-of-ifargs-when-ttmrg-correct-sk))
       :prep-lemmas (
	 (in-theory (enable ttmrg-correct-sk-thms))
	 (defrule lemma-then
	   (implies
	     (and (ttmrg-correct-p tterm)
		  (alistp env)
		  (equal (car (ttmrg->term tterm)) 'if))
	     (and
	       (implies
		 (ev-smtcp (ttmrg->path-cond (cadr (ttmrg->args tterm))) env)
		 (ev-smtcp (ttmrg->top-judgement (cadr (ttmrg->args tterm))) env))
	       (implies
		 (ev-smtcp (ttmrg->path-cond (caddr (ttmrg->args tterm))) env)
		 (ev-smtcp (ttmrg->top-judgement (caddr (ttmrg->args tterm))) env))))
	   :use((:instance member-when-ttmrg-args-correct-p
			     (ttargs (ttmrg->args tterm))
			     (ttarg (cadr (ttmrg->args tterm))))
		(:instance member-when-ttmrg-args-correct-p
			     (ttargs (ttmrg->args tterm))
			     (ttarg (caddr (ttmrg->args tterm))))
		(:instance ttmrg-syntax-p)))))))
   (more-returns
    (new-tt :name judgements-of-if--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt))
    (new-tt :name ttmrg-syntax-p-of-judgements-of-if
      (implies (ttmrg-syntax-p tterm)
	       (ttmrg-syntax-p new-tt)))))


(define judgements-of-fncall-help ((tterm ttmrg-syntax-p)
				   (options type-options-p)
				   (state state-p))
  :returns (new-judge conj-p)
  :guard (and (consp (ttmrg->term tterm))
	      (not (equal (car (ttmrg->term tterm)) 'quote))
	      (not (equal (car (ttmrg->term tterm)) 'if)))
  :guard-hints(("Goal" :use((:instance ttmrg-syntax-p))))
  (b* (((ttmrg tterm) (ttmrg-fix tterm))
       ((unless (mbt (and (consp tterm.term)
			  (not (equal (car tterm.term) 'quote))
			  (not (equal (car tterm.term) 'if)))))
	''t)
       ((cons fn actuals) tterm.term)
       (actuals-judgements-top (ttmrg->args-judgements tterm))
       (functions (type-options->functions options))
       (conspair (assoc-equal fn functions))
       ((unless conspair)
	(prog2$ (cw "no returns theorem found for ~x0~%" fn) ''t)))
    (term-to-conj
      (extend-judgements
	(returns-judgement
	  fn actuals actuals-judgements-top (cdr conspair)
	  tterm.path-cond ''t state)
	tterm.path-cond options state))))

(defrule ev-smtcp-of-ttmrg->args-judgements
  (implies
    (and (ttmrg-correct-p tterm)
	 (alistp env)
	 (ev-smtcp (ttmrg->path-cond tterm) env)
	 (consp (ttmrg->term tterm))
	 (not (equal (car (ttmrg->term tterm)) 'quote))
	 (not (equal (car (ttmrg->term tterm)) 'if)))
    (ev-smtcp (ttmrg->args-judgements tterm) env))
  :do-not-induct t
  :in-theory (enable ttmrg-correct-p ttmrg->args-judgements)
  :use((:instance ttmrg-correct-sk-necc))
  :prep-lemmas (
    (defrule lemma-1
      (implies (and (ttmrg-correct-p tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	  (ev-smtcp (ttmrg->top-judgement tterm) env))
      :use((:instance ttmrg->top-judgement-when-ttmrg-correct-sk)))
    (defrule lemma-2
      (implies
	(and (alistp env)
	     (ttmrg-args-correct-p ttargs)
	     (ttmrg-args-correct-path ttargs env))
	(ev-smtcp (ttmrg->args-judgements-help ttargs) env))
      :in-theory (enable ttmrg-args-correct-p
			 ttmrg-args-correct-path
			 ttmrg->args-judgements-help))))

(defrule syntax-p-lemma
  (implies
    (ttmrg-syntax-p tterm)
    (let ((term (ttmrg->term tterm)))
      (or (symbolp term)
	  (and (consp term) (symbolp (car term))))))
  :rule-classes (:forward-chaining :rewrite)
  :use((:instance ttmrg-syntax-p)
       (:instance pseudo-termp (x (ttmrg->term tterm)))))

(define judgements-of-fncall ((tterm ttmrg-syntax-p)
			      (options type-options-p)
			      (state state-p))
  :returns (new-tt ttmrg-p)
  :guard (and (consp (ttmrg->term tterm))
	      (not (equal (car (ttmrg->term tterm)) 'quote))
	      (not (equal (car (ttmrg->term tterm)) 'if)))
  :verify-guards nil
  (strengthen-ttmrg->top-judgement tterm
    (judgements-of-fncall-help tterm options state))
  ///
  (local (defrule correctness-of-judgements-of-fncall-help
    (let ((new-judge (judgements-of-fncall-help tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm)
		    (alistp env)
		    (ev-smtcp (ttmrg->path-cond tterm) env))
	       (ev-smtcp new-judge env)))
      :in-theory (disable alistp correctness-of-returns-judgement
			  )
      :use((:instance judgements-of-fncall-help)
	   (:instance correctness-of-returns-judgement
		      (term (ttmrg->term tterm))
		      (a env)
		      (fn (car (ttmrg->term tterm)))
		      (actuals (cdr (ttmrg->term tterm)))
		      (actuals-judgements (ttmrg->args-judgements tterm))
		      (path-cond (ttmrg->path-cond tterm))
		      (respec-lst (cdr (assoc-equal (car (ttmrg->term tterm))
						    (type-options->functions options))))
		      (acc ''t)))))

  (verify-guards judgements-of-fncall
    :hints(("Goal" :use((:instance ttmrg-syntax-p)))))

  (defrule ttmrg-correct-p-of-judgements-of-fncall
    (let ((new-tt (judgements-of-fncall tterm options state)))
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (and (ttmrg-correct-p new-tt)
		    (equal (ttmrg->term new-tt) (ttmrg->term tterm)))))
    :expand (judgements-of-fncall tterm options state)
    :use((:functional-instance correctness-of-strengthen-ttmrg->top-judgement
	    (constrain-ttmrg->top-judgement
	     (lambda (tterm state)
	       (if (ttmrg-correct-p tterm)
		 (judgements-of-fncall-help tterm options state)
		 ''t)))))
    :prep-lemmas (
      (defrule lemma-1
	(implies (and (ttmrg-correct-p tterm)
		      (consp (ttmrg->term tterm))
		      (not (equal (car (ttmrg->term tterm)) 'quote))
		      (not (equal (car (ttmrg->term tterm)) 'if))
		      (alistp env)
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (and (ttmrg-args-correct-p (ttmrg->args tterm))
		      (ttmrg-args-correct-path (ttmrg->args tterm) env)))
	:in-theory (e/d (ttmrg-correct-p ttmrg-correct-sk) (alistp))
	:use((:instance ttmrg-correct-sk-necc))
	:rule-classes ((:rewrite :match-free :all)))
      (defrule lemma-2
	(implies (and (alistp env)
		      (ttmrg-correct-p tterm)
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (ev-smtcp (ttmrg->top-judgement tterm) env))
	:in-theory (e/d (ttmrg-correct-p ttmrg-correct-sk) (alistp))
	:use((:instance ttmrg-correct-sk-necc)))
      (defrule lemma-3
	(implies (and (alistp env)
		      (ttmrg-args-correct-p ttargs)
		      (ttmrg-args-correct-path ttargs env))
		 (ev-smtcp (ttmrg->args-judgements-help ttargs) env))
	:in-theory (enable ttmrg-args-correct-p
			   ttmrg-args-correct-path
			   ttmrg->args-judgements-help))
      (defrule lemma-4
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp env)
		      (ttmrg-correct-p tterm)
		      (ev-smtcp (ttmrg->path-cond tterm) env))
		 (ev-smtcp (judgements-of-fncall-help tterm options state)
			   env))
	:in-theory (disable alistp correctness-of-judgements-of-fncall-help)
	:use((:instance correctness-of-judgements-of-fncall-help)
	     (:instance ttmrg->args-judgements)))))
  (more-returns
    (new-tt :name judgements-of-fncall--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt))
    (new-tt :name ttmrg-syntax-p-of-judgements-of-fncall
      (implies (ttmrg-syntax-p tterm)
	       (ttmrg-syntax-p new-tt)))))

(define judgements-of-term-help ((tterm ttmrg-syntax-p)
			         (options type-options-p)
			         (state state-p))
  :returns (new-tt ttmrg-p)
  (let ((term (ttmrg->term tterm)))
    (cond
      ((and (consp term) (equal (car term) 'quote))
       (judgements-of-ground-term
	 tterm (type-options->type-recognizers options) state))
      ((symbolp term)
       (judgements-of-variable tterm options state))
      ((equal (car term) 'if)
       (judgements-of-if tterm))
      (t (judgements-of-fncall tterm options state))))
  ///
  (more-returns
    (new-tt :name ttmrg-correct-p-of-judgements-of-term-help
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p new-tt)))
    (new-tt :name judgements-of-term-help--unchanged-fields
      (ttmrg-only-changed->top-judgement tterm new-tt))
    (new-tt :name ttmrg-syntax-p-of-judgements-of-term-help
      (implies (ttmrg-syntax-p tterm)
	       (ttmrg-syntax-p new-tt)))))

(defines judgements-of-term
  :verify-guards nil
  :flag-local nil

  (define judgements-of-term ((tterm ttmrg-syntax-p)
			      (options type-options-p)
			      (state state-p))
    :returns (new-tt ttmrg-p)
    :measure (ttmrg-simple-count tterm)
    :flag term
    (let* ((term (ttmrg->term tterm))
	   (args (ttmrg->args tterm))
	   (ttx (if (or (not (consp term))
		    (and (consp term) (equal (car term) 'quote)))
		  tterm
		  (change-ttmrg->args tterm
		    (judgements-of-args args options state)))))
      (judgements-of-term-help ttx options state)))

  (define judgements-of-args ((ttargs ttmrg-args-syntax-p)
			      (options type-options-p)
			      (state state-p))
    :returns (new-args ttmrg-list-p)
    :measure (ttmrg-args-simple-count ttargs)
    :flag args
    (if (consp ttargs)
      (cons (judgements-of-term (car ttargs) options state)
	    (judgements-of-args (cdr ttargs) options state))
      nil))
  ///
  (defthm-judgements-of-term-flag
    (defthm unchanged-of-judgements-of-term
      (let ((new-tt (judgements-of-term tterm options state)))
	(implies
	  (ttmrg-p tterm)
	  (and (equal (ttmrg->term new-tt) (ttmrg->term tterm))
	       (equal (ttmrg->path-cond new-tt) (ttmrg->path-cond tterm)))))
      :flag term)

    (defthm unchanged-of-judgements-of-args
      (let ((new-args (judgements-of-args ttargs options state)))
	(implies (ttmrg-list-p ttargs)
		 (ttmrg-args-only-changed->args new-args ttargs)))
      :flag args)
    :hints(("Goal"
      :in-theory (enable ttmrg-args-only-changed->args))))

  (local (defrule ttmrg-correct-p--new-args
    (let ((new-args (judgements-of-args (ttmrg->args tterm)
					options state)))
      (implies
	(and (ev-smtcp-meta-extract-global-facts)
	     (ttmrg-correct-p tterm)
	     (ttmrg-args-correct-p new-args))
	(ttmrg-correct-p
	  (change-ttmrg->args tterm new-args))))
    :use((:functional-instance ttmrg-correct-p-of-constrain-ttmrg->args-args
	    (constrain-ttmrg->args-args
	      (lambda (tterm state)
		(judgements-of-args (ttmrg->args tterm) options state)))))))

  (defthm-judgements-of-term-flag
    (defthm ttmrg-correct-p-of-judgements-of-term
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-correct-p tterm))
	       (ttmrg-correct-p (judgements-of-term tterm options state)))
      :flag term)

    (defthm ttmrg-args-correct-p-of-judgements-of-args
      (implies (and (ev-smtcp-meta-extract-global-facts)
		    (ttmrg-args-correct-p ttargs))
	       (ttmrg-args-correct-p (judgements-of-args ttargs options state)))
      :flag args)
    :hints(("Goal" :in-theory (enable ttmrg-args-correct-p))))

  (defrule match-len-of-judgements-of-args
    (match-len (judgements-of-args ttargs options state)
	       ttargs)
    :in-theory (enable match-len)
    :prep-lemmas (
      (defrule lemma-1
	(equal (consp (judgements-of-args ttargs options state))
	       (consp ttargs))
	:use((:instance judgements-of-args)))))

  (local (defrule lemma-syntax
    (implies (ttmrg-syntax-p tterm)
	     (ttmrg-args-syntax-p (ttmrg->args tterm)))
    :in-theory (enable ttmrg-syntax-p ttmrg-args-syntax-p)))

  (defthm-judgements-of-term-flag
      (defthm ttmrg-syntax-p-of-judgements-of-term
	(implies (ttmrg-syntax-p tterm)
		 (ttmrg-syntax-p (judgements-of-term tterm options state)))
	:flag term)

      (defthm ttmrg-args-syntax-p-of-judgements-of-args
	(implies (ttmrg-args-syntax-p ttargs)
		 (ttmrg-args-syntax-p (judgements-of-args ttargs options state)))
	:flag args)
      :hints(("Goal" :in-theory (enable ttmrg-args-syntax-p))))

  (defrule car-when-ttmrg-args-syntax-p
    (implies (and (ttmrg-args-syntax-p ttargs) ttargs)
	     (ttmrg-syntax-p (car ttargs)))
    :in-theory (enable ttmrg-args-syntax-p))
  
  (verify-guards judgements-of-term
    :guard-debug t
    :hints(("Goal"
	    :use((:instance ttmrg-syntax-p)
		 (:instance pseudo-termp (x (ttmrg->term tterm))))))))

;; -------------------------------------------------------


(define type-judge-bottomup-cp ((cl pseudo-term-listp)
                                (smtlink-hint t)
                                state)
  (b* (((unless (pseudo-term-listp cl)) (value nil))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list cl)))
       (goal (disjoin cl))
       ((unless (pseudo-term-syntax-p goal)) (value (list cl)))
       ((type-options h) (construct-type-options smtlink-hint goal))
       (judges (judgements-of-term (make-ttmrg-trivial goal)
				   h state))
       ((unless (mbt (ttmrg-correct-p judges))) (value (list cl)))
       (new-cl `(implies (ttmrg-correct-p ,(kwote judges) ,goal)))
       (next-cp (cdr (assoc-equal 'type-judge-bottomup *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-cl))
       (- (cw "type-judge-bottomup-cp: ~q0" hinted-goal)))
    (value (list hinted-goal))))

(defthm correctness-of-type-judge-bottomup-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-bottomup-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
	   :expand (type-judge-bottomup-cp cl hints state)
           :in-theory (disable alistp
			       ttmrg-correct-p-of-make-ttmrg-trivial
			       ttmrg-correct-p-of-judgements-of-term)
	   :use((:instance ttmrg-correct-p-of-make-ttmrg-trivial (term (disjoin cl)))
		(:instance ttmrg-correct-p-of-judgements-of-term
			     (tterm (make-ttmrg-trivial (disjoin cl)))
			     (options (construct-type-options hints (disjoin cl)))))))
  :rule-classes :clause-processor)
