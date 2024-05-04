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

(include-book "ttmrg3")

(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; Time to certify on a M1 Pro Macbook
;   If we don't disable useless rules:                22.75s
;   If we disable all useless rules:                   2.66s
;   Disable until :frame one-tenth of worst offender:  3.04s -- this is what I do below
;   Disable top 10 useless runes:                      3.30s
(local (in-theory (disable
  acl2::true-listp-of-car-when-true-list-listp
  true-list-listp true-listp symbol-listp default-car default-cdr
  acl2::true-list-listp-of-cdr-when-true-list-listp
  acl2::pseudo-lambdap-of-car-when-pseudo-termp
  pseudo-lambdap-of-fn-call-of-pseudo-termp consp-of-cdr-of-pseudo-lambdap
  pseudo-term-listp-of-cdr-of-pseudo-termp consp-of-pseudo-lambdap
  acl2::symbolp-of-car-when-symbol-listp lambda-of-pseudo-lambdap
  acl2::symbol-listp-when-not-consp pseudo-term-listp-of-symbol-listp
  acl2::pseudo-termp-when-member-equal-of-pseudo-term-listp
  acl2::symbol-listp-of-cdr-when-symbol-listp member-equal
  acl2::pseudo-termp-cadr-from-pseudo-term-listp
  acl2::pseudo-termp-car all-tail<judge-ev> acl2::subsetp-car-member)))


(defines make-ttmrg-trivial
  :verify-guards nil
  :ruler-extenders :all

  (define make-ttmrg-trivial ((term pseudo-termp))
    :returns (tterm ttmrg-p)
    :flag term
    (make-ttmrg
      :path-cond nil
      :judgements nil
      :smt-judgements nil
      :guts
	(b* (((if (symbolp term))
	      (make-ttmrg-guts-var :name term))
	     ((unless (mbt (consp term))) (make-ttmrg-guts-var :name 'bad-term))
	     ((cons fn args) term)
	     ((if (equal fn 'quote))
	      (make-ttmrg-guts-quote :val (cadr term)))
	     ((if (equal fn 'if))
	      (make-ttmrg-guts-if
		:condx (make-ttmrg-trivial (car args))
		:thenx (make-ttmrg-trivial (cadr args))
		:elsex (make-ttmrg-trivial (caddr args))))
	     ((if (symbolp fn))
	      (make-ttmrg-guts-fncall :f fn :args (make-ttmrg-list-trivial args))))
	    (make-ttmrg-guts-var :name 'bad-term))))

  (define make-ttmrg-list-trivial ((lst pseudo-term-listp))
    :returns (ttlst ttmrg-list-p)
    :flag list
    (if (consp lst)
       (cons (make-ttmrg-trivial (car lst))
	     (make-ttmrg-list-trivial (cdr lst)))
       nil))
  ///
  (verify-guards make-ttmrg-trivial
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp))))

  (encapsulate nil
    (local (defrule args->path-cond-ev-of-make-ttmrg-list-trivial
      (args->path-cond-ev (make-ttmrg-list-trivial lst) a)
      :induct (len lst)
      :in-theory (enable args->path-cond-ev make-ttmrg-list-trivial)
      :prep-lemmas (
	(defrule ttmrg->path-cond-ev-of-make-ttmrg-trivial
	  (ttmrg->path-cond-ev (make-ttmrg-trivial term) a)
	  :in-theory (enable ttmrg->path-cond-ev)
	  :expand ((make-ttmrg-trivial term))))))

    (local (defrule ttmrg->path-cond-ev-of-make-ttmrg-trivial
      (ttmrg->path-cond-ev (make-ttmrg-trivial term) a)
      :in-theory (enable ttmrg->path-cond-ev)
      :expand (make-ttmrg-trivial term)))

    (local (acl2::defruled ttmrg->judgements-evs-of-make-ttmrg-trivial
             (and
               (ttmrg->judgements-ev (make-ttmrg-trivial term) a)
               (ttmrg->smt-judgements-ev (make-ttmrg-trivial term) a))
             :in-theory (enable ttmrg->judgements-ev ttmrg->smt-judgements-ev)
             :expand (make-ttmrg-trivial term)))

    (defthm-make-ttmrg-trivial-flag
      (defthm ttmrg-correct-p-of-make-ttmrg-trivial
	(ttmrg-correct-p (make-ttmrg-trivial term) a)
	:flag term)

      (defthm ttmrg-list-correct-p-of-make-ttmrg-trivial
	(ttmrg-list-correct-p (make-ttmrg-list-trivial lst) a)
	:flag list)
      :hints(
        ("Goal" :in-theory (enable ttmrg-correct-p ttmrg-list-correct-p
				   make-ttmrg-trivial))
	; a computed hint because all of the subgoals for make-ttmrg-trivial
	; need an instantiation of ttmrg->judgements-ev-of-make-ttmrg-trivial.
	(and (member-equal '(not (acl2::flag-is 'term)) clause)
	     '(:use ((:instance ttmrg->judgements-evs-of-make-ttmrg-trivial))))))))


(defines pseudo-term-syntax
  (define pseudo-term-syntax-p ((term pseudo-termp))
    :returns (ok booleanp)
    :flag term
    (b* (((if (not (consp term))) (symbolp term))
	 ((cons fn args) term)
	 ((if (equal fn 'quote))
	  (and (consp args) (not (cdr args))))
	 ((if (equal fn 'if))
	  (and
	    (consp args)        (pseudo-term-syntax-p (car args))
	    (consp (cdr args))  (pseudo-term-syntax-p (cadr args))
	    (consp (cddr args)) (pseudo-term-syntax-p (caddr args))
	    (not (cdddr args))))
	 ((if (symbolp fn)) (pseudo-term-list-syntax-p args)))
      nil))

  (define pseudo-term-list-syntax-p ((lst pseudo-term-listp))
    :returns (ok booleanp)
    :flag list
    (if (consp lst)
      (and (pseudo-term-syntax-p (car lst))
	   (pseudo-term-list-syntax-p (cdr lst)))
      (not lst)))
  ///
  (defthm-pseudo-term-syntax-flag
    (defthm pseudo-termp-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term) (pseudo-termp term))
      :rule-classes :type-prescription
      :flag term)
    (defthm pseudo-term-listp-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p lst) (pseudo-term-listp lst))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp))))

  (defthm-pseudo-term-syntax-flag
    (defthm make-ttmrg-trivial-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term)
	       (equal (ttmrg->expr (make-ttmrg-trivial term)) term))
      :flag term)

    (defthm make-ttmrg-list-trivial-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p lst)
	       (equal (ttmrg-list->expr-list (make-ttmrg-list-trivial lst)) lst))
      :flag list)

    :hints(("Goal"
      :in-theory (enable pseudo-term-syntax-p pseudo-term-list-syntax-p
			 make-ttmrg-trivial make-ttmrg-list-trivial
			 ttmrg->expr ttmrg-list->expr-list)))))
