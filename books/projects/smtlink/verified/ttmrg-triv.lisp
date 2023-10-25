;; Copyright (C) 2022, University of British Columbia)
;; Initial version by Mark Greenstreet.
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")

; This book has three main exports:
;   Function that make correct ttmrg and ttmrg-args values from pseudo-termp
;       and pseudo-term-listp objects respectively.  The functions we export
;       are
;     make-ttmrg-trivial and make-ttmrg-args-trivial.
;   Theorems that show that these functions produce values satisfying
;       ttmrg-correct-p and ttmrg-args-correct-p.  These theorems are
;     ttmrg-correct-p-of-make-ttmrg-trivial and
;     ttmrg-args-correct-p-of-mke-ttmrg-args-trivial.
;   Theorems that show that if a term satisfies pseudo-term-syntax-p, then
;       (equal (ttmrg->term (make-ttmrg-trivial term)) term)
;     and likewise for make-ttmrg-args-trivial.  These theorems are
;       make-ttmrg-trivial-when-pseudo-term-syntax-p and
;       make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p and

(include-book "ttmrg-correct2")

(set-induction-depth-limit 1)
(set-warnings-as-errors t '("Use") state)

; Mark is impatient
(local (in-theory (disable
  pseudo-termp pseudo-term-listp
  acl2::pseudo-termp-opener
  acl2::pseudo-termp-of-car-when-pseudo-term-listp
  acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  pseudo-term-listp-of-cdr-of-pseudo-termp
  acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  pseudo-termp-when-conj-p
  lambda-of-pseudo-lambdap
  symbol-listp symbol-alistp alistp true-listp boolean-listp
  acl2::symbolp-of-car-when-symbol-listp
  acl2::symbol-listp-of-cdr-when-symbol-listp
  pseudo-term-listp-of-symbol-listp
  default-car member-equal conj-p-when-conj-consp
  acl2-count)))

(local (defrule lemma-for-make-ttmrg-trivial-measure
  (implies (consp (pseudo-term-syntax-fix term))
	   (< (acl2-count (cdr (pseudo-term-syntax-fix term)))
	      (acl2-count term)))
  :expand ((pseudo-term-syntax-fix term))
  :in-theory (disable acl2-count-of-pseudo-term-list-syntax-fix)
  :use((:instance acl2-count-of-pseudo-term-list-syntax-fix (args (cdr term))))))

(defines make-ttmrg-trivial
  :flag-local nil
  :verify-guards nil
  (define make-ttmrg-trivial ((term pseudo-term-syntax-p))
    :returns (tterm ttmrg-p)
    :flag term
    (b* ((term (pseudo-term-syntax-fix term))
	 (tterm (make-ttmrg :term term
			    :path-cond ''t
			    :args nil
			    :top-judgement ''t))
	 ((if (or (atom term) (equal (car term) 'quote))) tterm)
	 ((cons fn args) term)
	 (ttargs (make-ttmrg-args-trivial args))
	 (args-triv (ttmrg-list->terms ttargs))
	 )
      (change-ttmrg tterm :term (cons fn args-triv) :args ttargs)))

  (define make-ttmrg-args-trivial ((args pseudo-term-list-syntax-p))
    :returns (ttargs ttmrg-list-p)
    :flag args
    (b* (((unless (consp args)) nil)
	 ((cons hd tl) args))
       (cons (make-ttmrg-trivial hd)
	     (make-ttmrg-args-trivial tl))))
  ///
  (verify-guards make-ttmrg-trivial
    :hints(("Goal" :in-theory (enable pseudo-term-syntax-p
				      pseudo-term-list-syntax-p))))

  ; Show that if term satisfies pseudo-term-syntax-p, then
  ;   (equal (ttmrg->term (make-ttmrg-trivial term)) term)
  ; We need a few lemmas for the induction cases, hence the encapsulation.
  (local (defrule lemma-term
    (implies (and (pseudo-term-syntax-p term)
		  (or (not (consp term))
		      (equal (car term) 'quote)
		      (equal (ttmrg-list->terms (make-ttmrg-args-trivial (cdr term)))
			     (cdr term))))
	     (equal (ttmrg->term (make-ttmrg-trivial term)) term))
    :expand ((pseudo-term-syntax-p term)
	     (make-ttmrg-trivial term))))

  (local (defrule lemma-args
    (equal (ttmrg-list->terms
		(make-ttmrg-args-trivial (cons term args)))
	   (cons (ttmrg->term (make-ttmrg-trivial term))
		 (ttmrg-list->terms (make-ttmrg-args-trivial args))))
    :in-theory (enable ttmrg-list->terms)
    :expand ((make-ttmrg-args-trivial (cons term args)))))

  (defthm-make-ttmrg-trivial-flag
    (defthm make-ttmrg-trivial-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term)
	       (equal (ttmrg->term (make-ttmrg-trivial term)) term))
      :flag term)

    (defthm make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p args)
	       (equal (ttmrg-list->terms (make-ttmrg-args-trivial args)) args))
      :flag args)

    :hints(("Goal"
      :in-theory (e/d (pseudo-term-syntax-p pseudo-term-list-syntax-p)
		      (make-ttmrg-trivial make-ttmrg-args-trivial))))))


; I don't want to clutter the namespace of any book that includes this book.
; The theorems in the following encapsulation are lemmas used in the proof
; that (ttmrg-correct-e (make-ttmrg-trivial term)) and likewise for
; make-ttmrg-args-trivial.
(local (encapsulate nil
  (local (in-theory (enable
    make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms
    ttmrg-list->judgements ttmrg-args-correct-values ttmrg-args-correct-path)))

  (defrule match-len-of-make-ttmrg-args-trivial
    (match-len (make-ttmrg-args-trivial args) args)
    :in-theory (enable match-len)
    :induct (len args))

  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-syntax-p-of-make-ttmrg-trivial
      (implies (pseudo-term-syntax-p term)
               (ttmrg-syntax-p (make-ttmrg-trivial term)))
      :flag term)

    (defthm ttmrg-args-syntax-p-of-make-ttmrg-args-trivial
      (implies (pseudo-term-list-syntax-p args)
	       (ttmrg-args-syntax-p (make-ttmrg-args-trivial args)))
      :flag args)
    :hints(("Goal"
      :in-theory (enable ttmrg-syntax-p ttmrg-args-syntax-p
			 pseudo-term-syntax-p pseudo-term-list-syntax-p))))

  (defrule make-ttmrg-trivial->path-cond
    (equal (ttmrg->path-cond (make-ttmrg-trivial term)) ''t)
    :expand (make-ttmrg-trivial term))

  (defrule ttmrg-args-correct-path-of-make-ttmrg-trivial->args
    (ttmrg-args-correct-path
      (ttmrg->args (make-ttmrg-trivial term)) env)
    :expand ((make-ttmrg-trivial term)
	     (ttmrg-args-correct-path nil env))
    :prep-lemmas (
      (defrule make-ttmrg-args-trivial-correct-path
	(ttmrg-args-correct-path
	  (make-ttmrg-args-trivial args) env)
	:induct (len args))))

  (defrule make-ttmrg-trivial->top-judgement
    (equal (ttmrg->top-judgement (make-ttmrg-trivial term)) ''t)
    :expand (make-ttmrg-trivial term))

  (defrule ttmrg->path-cond-of-if-args
    (implies (pseudo-term-syntax-p term)
      (and (equal (ttmrg->path-cond (car (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	   (equal (ttmrg->path-cond (cadr (ttmrg->args (make-ttmrg-trivial term)))) ''t)
	   (equal (ttmrg->path-cond (caddr (ttmrg->args (make-ttmrg-trivial term)))) ''t)))
    :expand ((make-ttmrg-trivial term)
	     (make-ttmrg-args-trivial (cdr term))
	     (make-ttmrg-args-trivial (cddr term))
	     (make-ttmrg-args-trivial (cdddr term))))

  (local (defrule ttmrg-args-correct-e-of-make-ttmrg-trivial->args
    (implies
      (and (pseudo-term-syntax-p term) (alistp env)
	   (ttmrg-args-correct-e (make-ttmrg-args-trivial (cdr term)) env))
      (ttmrg-args-correct-e (ttmrg->args (make-ttmrg-trivial term)) env))
    :in-theory (enable make-ttmrg-trivial ttmrg-args-correct-e)))

  (local (defrule pseudo-term-list-syntax-p-of-args-when-pseudo-term-syntax-p
    (implies (and (pseudo-term-syntax-p term)
		  (consp term)
		  (not (equal (car term) 'quote)))
	     (pseudo-term-list-syntax-p (cdr term)))
    :expand ((pseudo-term-syntax-p term))))

  (local (defrule make-ttmrg-trivial-correct-values
      (implies
	(and (pseudo-term-syntax-p term)
	     (consp term)
	     (not (equal (car term) 'quote)))
	(ttmrg-args-correct-values
	  (ttmrg->args (make-ttmrg-trivial term))
	  (cdr term)
	  env))
      :expand ((make-ttmrg-trivial term))
      :in-theory (disable make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p)
      :use((:instance make-ttmrg-args-trivial-when-pseudo-term-list-syntax-p
	     (args (cdr term)))
	   (:instance make-ttmrg-args-trivial-correct-values
	     (args (cdr term))))
      :prep-lemmas (
	(acl2::defruled make-ttmrg-args-trivial-correct-values
	  (ttmrg-args-correct-values
	    (make-ttmrg-args-trivial args)
	    (ttmrg-list->terms (make-ttmrg-args-trivial args)) env)
	  :induct (len args)))))

  (local (in-theory (e/d
    (ttmrg-correct-e ttmrg-args-correct-e)
    ( make-ttmrg-trivial make-ttmrg-args-trivial ttmrg-list->terms
      ttmrg-list->judgements ttmrg-args-correct-values ttmrg-args-correct-path))))

  (defthm-make-ttmrg-trivial-flag
    (defthm ttmrg-correct-e-of-make-ttmrg-trivial-lemma
      (implies
	(and (pseudo-term-syntax-p term) (alistp env))
	(ttmrg-correct-e (make-ttmrg-trivial term) env))
      :flag term)

    (defthm ttmrg-args-correct-e-of-make-ttmrg-args-trivial-lemma
      (implies
	(and (pseudo-term-list-syntax-p args) (alistp env))
	(ttmrg-args-correct-e (make-ttmrg-args-trivial args) env))
      :flag args)
    :hints(("Goal"
      :in-theory (enable ttmrg-correct-e ttmrg-args-correct-e
			 make-ttmrg-args-trivial pseudo-term-list-syntax-p))))

    (acl2::defruled make-ttmrg-trivial-of-pseudo-term-syntax-fix
      (equal (make-ttmrg-trivial (pseudo-term-syntax-fix term))
	     (make-ttmrg-trivial term))
      :expand ((make-ttmrg-trivial term)
	       (make-ttmrg-trivial (pseudo-term-syntax-fix term))))

    (acl2::defruled make-ttmrg-args-trivial-of-pseudo-term-list-syntax-fix
	(equal (make-ttmrg-args-trivial (pseudo-term-list-syntax-fix args))
	       (make-ttmrg-args-trivial args))
	:in-theory (enable make-ttmrg-args-trivial pseudo-term-list-syntax-fix
			   make-ttmrg-trivial-of-pseudo-term-syntax-fix)
	:induct (len args))))


(defrule ttmrg-correct-e-of-make-ttmrg-trivial
  (ttmrg-correct-e (make-ttmrg-trivial term) env)
  :in-theory (disable ttmrg-correct-e-of-make-ttmrg-trivial-lemma
		      ttmrg-correct-e-of-fix-env)
  :use((:instance make-ttmrg-trivial-of-pseudo-term-syntax-fix)
       (:instance ttmrg-correct-e-of-make-ttmrg-trivial-lemma
		    (term (pseudo-term-syntax-fix term))
		    (env (acl2::alist-fix env))
		    )
       (:instance ttmrg-correct-e-of-fix-env
		    (tterm (make-ttmrg-trivial term)))))

(defrule ttmrg-args-correct-e-of-make-ttmrg-args-trivial
  (ttmrg-args-correct-e (make-ttmrg-args-trivial args) env)
  :in-theory (disable ttmrg-args-correct-e-of-fix-env)
  :use((:instance make-ttmrg-args-trivial-of-pseudo-term-list-syntax-fix)
       (:instance ttmrg-args-correct-e-of-fix-env
		    (ttargs (make-ttmrg-args-trivial args)))))

(define ttmrg-triv-cp ((cl pseudo-term-listp)
			(smtlink-hint t)
			state)
  (b* (((unless (pseudo-term-listp cl)) (value nil))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list cl)))
       (goal (disjoin cl))
       ((unless (pseudo-term-syntax-p goal)) (value (list cl)))
       (new-cl (implies-ev (ttmrg-correct-ev (make-ttmrg-trivial goal)) goal))
       (- (cw "ttmrg-triv-cp: new-cl = ~q0~%" new-cl)))
    (value (list (list new-cl)))))

(defrule correctness-of-ttmrg-triv-cp
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (ttmrg-triv-cp cl hints state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :expand (ttmrg-triv-cp cl hints state)
  :in-theory (disable alistp ttmrg-correct-e-of-make-ttmrg-trivial
		      ttmrg-correct-evx)
  :use((:instance ttmrg-correct-e-of-make-ttmrg-trivial
		    (term (disjoin cl)) (env a))
       (:instance ttmrg-correct-evx
		    (tterm (make-ttmrg-trivial (disjoin cl))) (env a))
		  )
  :rule-classes :clause-processor)
