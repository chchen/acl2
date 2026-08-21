;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a clause processor that extracts typing
;; information from unconditional, monomorphically-typed typed terms.

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "basics")
(include-book "hint-interface")
(include-book "smt-judgement")
(include-book "ttmrg3")
(include-book "ttmrg-clause")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

;; Extracts :var guts from a typed term, returning an alist of (sym
;; . judgement) pairs
(defsection SMT-tterm-type-extract
  :parents (verified)

  (define tterm->smt-judgement-symbol ((tterm ttmrg-p))
    :returns (rv symbolp)
    (b* ((tterm (ttmrg-fix tterm))
         (smt-j (ttmrg->smt-judgements tterm))
         ((unless (and (equal (len smt-j) 1)
                       (equal (len (car smt-j)) 2)))
          'acl2::any-p$inline))
      (symbol-fix (caar smt-j)))
    ///
    (fty::deffixequiv tterm->smt-judgement-symbol))

  (std::defprojection tterms->smt-judgement-symbols ((x ttmrg-list-p))
    :returns (rv symbol-listp)
    (tterm->smt-judgement-symbol x)
    ///
    (fty::deffixequiv tterms->smt-judgement-symbols))

  (defines tterm->fn-judgements
    :verify-guards nil
    :well-founded-relation l<

    (define tterm-if->fn-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 2 0)
      :guard (equal (ttmrg->kind tterm) :if)
      :returns (rv fn-judgement-list-p)
      :flag if
      (b* ((tterm (ttmrg-fix tterm))
           ((unless (mbt (equal (ttmrg->kind tterm) :if))) nil)
           (condx-judgements (tterm->fn-judgements (ttmrg->condx tterm)))
           (thenx-judgements (tterm->fn-judgements (ttmrg->thenx tterm)))
           (elsex-judgements (tterm->fn-judgements (ttmrg->elsex tterm))))
        (append condx-judgements
                thenx-judgements
                elsex-judgements)))

    (define tterm-list->fn-judgements ((tterms ttmrg-list-p))
      :measure (list (ttmrg-list->expr-list-count tterms) 1 0)
      :returns (rv fn-judgement-list-p)
      :flag list
      (b* ((tterms (ttmrg-list-fix tterms)))
        (if (consp tterms)
            (append (tterm->fn-judgements (car tterms))
                    (tterm-list->fn-judgements (cdr tterms)))
          nil)))

    (define tterm-fncall->fn-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 2 0)
      :guard (equal (ttmrg->kind tterm) :fncall)
      :returns (rv fn-judgement-list-p)
      :flag fncall
      (b* ((tterm (ttmrg-fix tterm))
           ((unless (mbt (equal (ttmrg->kind tterm) :fncall))) nil)
           (name (ttmrg->f tterm))
           (smt-j (ttmrg->smt-judgements tterm))
           ((unless (and (equal (len smt-j) 1)
                         (equal (len (car smt-j)) 2)))
            nil)
           (range (symbol-fix (caar smt-j)))
           (args (ttmrg->args tterm))
           (domain (tterms->smt-judgement-symbols args)))
        (cons (fn-judgement name domain range)
              (tterm-list->fn-judgements args))))

    (define tterm->fn-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 3 0)
      :returns (rv fn-judgement-list-p)
      :flag term
      (b* ((tterm (ttmrg-fix tterm)))
        (case (ttmrg->kind tterm)
          (:quote nil)
          (:var nil)
          (:if (tterm-if->fn-judgements tterm))
          (:fncall (tterm-fncall->fn-judgements tterm))))
      ///
      (verify-guards tterm->fn-judgements)
      (fty::deffixequiv-mutual tterm->fn-judgements)))

  (define tterm-var->var-judgements ((tterm ttmrg-p))
    :guard (equal (ttmrg->kind tterm) :var)
    :returns (rv var-judgement-list-p)
    (b* ((tterm (ttmrg-fix tterm))
         ((unless (mbt (equal (ttmrg->kind tterm) :var))) nil)
         (smt-j (ttmrg->smt-judgements tterm))
         ((unless (and (equal (len smt-j) 1)
                       (equal (len (car smt-j)) 2)))
          nil)
         (name (ttmrg->name tterm))
         (recognizer (caar smt-j)))
      (list (var-judgement (symbol-fix name)
                           (symbol-fix recognizer))))
    ///
    (fty::deffixequiv tterm-var->var-judgements))

  (defines tterm->var-judgements
    :verify-guards nil
    :well-founded-relation l<

    (define tterm-if->var-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 2 0)
      :guard (equal (ttmrg->kind tterm) :if)
      :returns (rv var-judgement-list-p)
      :flag if
      (b* ((tterm (ttmrg-fix tterm))
           ((unless (mbt (equal (ttmrg->kind tterm) :if))) nil)
           (condx-judgements (tterm->var-judgements (ttmrg->condx tterm)))
           (thenx-judgements (tterm->var-judgements (ttmrg->thenx tterm)))
           (elsex-judgements (tterm->var-judgements (ttmrg->elsex tterm))))
        (append condx-judgements
                thenx-judgements
                elsex-judgements)))

    (define tterms->var-judgements ((tterms ttmrg-list-p))
      :measure (list (ttmrg-list->expr-list-count tterms) 1 0)
      :returns (rv var-judgement-list-p)
      :flag list
      (b* ((tterms (ttmrg-list-fix tterms)))
        (if (consp tterms)
            (append (tterm->var-judgements (car tterms))
                    (tterms->var-judgements (cdr tterms)))
          nil)))

    (define tterm-fncall->var-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 2 0)
      :guard (equal (ttmrg->kind tterm) :fncall)
      :returns (rv var-judgement-list-p)
      :flag fncall
      (b* ((tterm (ttmrg-fix tterm))
           ((unless (mbt (equal (ttmrg->kind tterm) :fncall))) nil))
        (tterms->var-judgements (ttmrg->args tterm))))

    (define tterm->var-judgements ((tterm ttmrg-p))
      :measure (list (ttmrg->expr-count tterm) 3 0)
      :returns (rv var-judgement-list-p)
      :flag term
      (b* ((tterm (ttmrg-fix tterm)))
        (case (ttmrg->kind tterm)
          (:quote nil)
          (:var (tterm-var->var-judgements tterm))
          (:if (tterm-if->var-judgements tterm))
          (:fncall (tterm-fncall->var-judgements tterm))))
      ///
      (verify-guards tterm->var-judgements)
      (fty::deffixequiv-mutual tterm->var-judgements))
    )
 )

(define tterm->smt-judgement ((tterm ttmrg-p))
  :returns (rv smt-judgement-p)
  (b* ((tterm (ttmrg-fix tterm)))
    (smt-judgement (std::mergesort (tterm->var-judgements tterm))
                   (std::mergesort (tterm->fn-judgements tterm))))
  ///
  (fty::deffixequiv tterm->smt-judgement))

(defsection tterm-type-extract-cp

  (define tterm-type-extract-cp ((cl pseudo-term-listp)
                                 (hint t)
                                 state)
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (smtlink-hint-p hint)) (mv t nil state))
         (goal (disjoin cl))
         ((mv fail tterm) (ttmrg-parse-clause goal))
         ((if fail) (mv t nil state))
         ;; Goal for next clause processor
         (expr (ttmrg->expr tterm))
         (next-condition (smt-judgement-clause (tterm->smt-judgement tterm)
                                               expr))
         (next-cp (cdr (assoc-equal 'tterm-type-extract
                                    *SMT-architecture*)))
         ((if (null next-cp)) (mv t nil state))
         (next-hint
           `(:clause-processor (,next-cp clause ',hint state)))
         (next-goal `((hint-please ',next-hint) ,next-condition))
         ;; Side condition
         (side-goal (list (implies-expr next-condition expr))))
                    (value (list next-goal
                                 side-goal))))

  (defrule correctness-of-tterm-type-extract-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev-smtcp
                    (conjoin-clauses
                      (acl2::clauses-result
                        (tterm-type-extract-cp cl hint state)))
                    a))
             (ev-smtcp (disjoin cl) a))
    :do-not-induct t
    :expand (tterm-type-extract-cp cl hint state)
    :in-theory (e/d (ev-and) (ev-smtcp-of-disjoin))
    :rule-classes :clause-processor)
  )
