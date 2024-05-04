;; Copyright (C) 2022, University of British Columbia)
;; Initial version by Mark Greenstreet.
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")

(include-book "basics")
(include-book "ttmrg-triv3")
(include-book "ttmrg-clause")

(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

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


(define ttmrg-triv-cp ((cl pseudo-term-listp)
		       (hint t)
		       state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       ((unless (pseudo-term-syntax-p goal)) (mv t nil state))
       (next-cp (cdr (assoc-equal 'ttmrg-triv *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (new-tt (make-ttmrg-trivial goal))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (ttmrg-clause new-tt))
       (- (cw "ttmrg-triv-cp: new-cl = ~q0~%" new-cl))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-ttmrg-triv-cp
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (ttmrg-triv-cp cl hint state)))
                  a))
           (ev-smtcp (disjoin cl) a))
  :expand (ttmrg-triv-cp cl hint state)
  :rule-classes :clause-processor)
