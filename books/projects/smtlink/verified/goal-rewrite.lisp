;; Copyright (C) 2015, University of British Columbia
;; Written by Chris Chen (March 2025)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/osets/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "ttmrg-clause-cp")
(include-book "typed-term-fns")
(include-book "returns-judgement")
(include-book "judgement-fns")
(include-book "ti-bottom-up3")

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
   default-car
   (:type-prescription pseudo-lambdap)))))


(define type-judge-top-down-cp ((cl pseudo-term-listp)
                                (hint t)
                                state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       ((mv fail tterm) (ttmrg-parse-clause goal))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal 'type-judge-top-down *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (type-opt (construct-type-options hint goal))
       (new-tt (refine-ttmrg-wrapper tterm type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (ttmrg-clause new-tt))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-type-judge-top-down-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (type-judge-top-down-cp cl hint state)))
                  a))
           (ev-smtcp (disjoin cl) a))
  :do-not-induct t
  :expand ((type-judge-top-down-cp cl hint state))
  :use ((:functional-instance
          correctness-of-tterm-trans-fn-cp
          (tterm-trans-fn refine-ttmrg-wrapper)
          (env-trans-fn (lambda (x) x))
          (current-cp-fn (lambda () 'type-judge-top-down))
          (tterm-trans-fn-cp type-judge-top-down-cp)))
  :in-theory (disable ev-smtcp-of-disjoin)
  :rule-classes :clause-processor)
