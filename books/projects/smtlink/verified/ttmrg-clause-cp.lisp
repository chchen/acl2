;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet and Chris Chen (2 Feb 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "basics")
(include-book "ttmrg-clause")
(include-book "ttmrg-triv3")
(include-book "type-options")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))


(local (in-theory (e/d
  ()
  (pseudo-termp pseudo-term-listp symbol-listp  ; Mark is impatient
   boolean-listp member-equal consp-of-pseudo-lambdap
   pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
   default-car
   (:type-prescription pseudo-lambdap)))))


;; Define correctness properties for ttmrg-clause processors
(encapsulate
    (((tterm-trans-fn * * state) => *)
     ((env-trans-fn *) => *)
     ((current-cp-fn) => *))

  (local (defun tterm-trans-fn (tterm opts state)
           (declare (ignore opts state))
           (ttmrg-fix tterm)))

  (local (defun env-trans-fn (a)
           a))

  (local (defun current-cp-fn ()
           'process-hint))

  (defthm symbolp-of-current-cp-fn
    (symbolp (current-cp-fn)))

  (defthm ttmrg-p-of-tterm-trans-fn
    (ttmrg-p (tterm-trans-fn tterm opts state)))

  (defthm tterm-trans-fn-preserves-expr-eval-backwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (ev-smtcp (ttmrg->expr (tterm-trans-fn tterm opts state))
                            (env-trans-fn a)))
             (ev-smtcp (ttmrg->expr tterm) a)))

  (defthm tterm-trans-fn-preserves-correct-p-forwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (ttmrg-correct-p tterm a))
             (ttmrg-correct-p (tterm-trans-fn tterm opts state)
                              (env-trans-fn a)))))


(define tterm-trans-fn-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       ((unless (pseudo-term-syntax-p goal)) (mv t nil state))
       ((mv fail tterm) (ttmrg-parse-clause goal))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal (current-cp-fn) *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (type-opt (construct-type-options hint goal))
       (new-tt (tterm-trans-fn tterm type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (ttmrg-clause new-tt))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-tterm-trans-fn-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (tterm-trans-fn-cp cl hint state)))
                  (env-trans-fn a)))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand (tterm-trans-fn-cp cl hint state)
  :in-theory (disable ev-smtcp-of-disjoin)
  :rule-classes :clause-processor)
