;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet and Chris Chen (2 Feb 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "basics")
(include-book "ttmrg3")
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
  (b* ((tterm (ttmrg-fix tterm)))
    `(implies
       (if (acl2::any-p$inline (quote ,tterm))
           ,(ttmrg-correct-expr tterm)
         ''nil)
       ,(ttmrg->expr tterm)))
  ///
  (defrule eval-ttmrg-clause-if-eval-ttmrg-expr
    (implies (ev-smtcp (ttmrg->expr tterm) a)
             (ev-smtcp (ttmrg-clause tterm) a))))


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
		      (('implies ('if ('acl2::any-p$inline ('quote tterm)) & &) &) tterm)
		      (& nil)))
       ((unless (and (ttmrg-p tterm)
		     (equal (ttmrg-clause tterm) cl)))
	(mv t (make-ttmrg))))
    (mv nil tterm))
  ///
  (defrule ttmrg-parse-clause-of-ttmrg-clause
    (implies (ttmrg-p tterm)
             (mv-let
                 (fail parsed-tterm)
                 (ttmrg-parse-clause (ttmrg-clause tterm))
               (and (not fail)
                    (equal parsed-tterm tterm))))
    :expand ((ttmrg-clause tterm))
    :in-theory (enable pseudo-termp))

  (defrule ttmrg-parse-clause-pass
    (mv-let
        (fail tterm)
        (ttmrg-parse-clause cl)
      (implies (and (not fail)
                    (ev-smtcp (ttmrg->expr tterm) a))
               (ev-smtcp cl a)))
    :in-theory (disable eval-ttmrg-clause-if-eval-ttmrg-expr)
    :use (:instance eval-ttmrg-clause-if-eval-ttmrg-expr
                    (tterm (mv-nth 1 (ttmrg-parse-clause cl))))))


;; Lift evaluation of ttmrg-clauses to evaluation of their components
(encapsulate ()
  (local
    (acl2::defruled ttmrg-clause-of-ttmrg-parse-clause
      (mv-let (fail parsed-tterm)
              (ttmrg-parse-clause cl)
        (implies (not fail)
                 (equal (ttmrg-clause parsed-tterm)
                        cl)))
      :expand ((ttmrg-parse-clause cl))))

  (local
    (acl2::defruled ev-smtcp-ttmrg-clause-equivalent
      (mv-let (fail tterm)
              (ttmrg-parse-clause cl)
        (implies (not fail)
                 (equal (ev-smtcp cl a)
                        (ev-smtcp (ttmrg-clause tterm) a))))
      :in-theory (enable ttmrg-clause-of-ttmrg-parse-clause)))

  (defrule ev-smtcp-ttmrg-clause
    (mv-let (fail tterm)
            (ttmrg-parse-clause cl)
      (implies (not fail)
               (equal (ev-smtcp cl a)
                      (implies (ttmrg-correct-p tterm a)
                               (ev-smtcp (ttmrg->expr tterm) a)))))
    :in-theory (e/d (ttmrg-clause
                     ev-smtcp-ttmrg-clause-equivalent)
                    (ttmrg-parse-clause-of-ttmrg-clause))))


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
                  (ev-smtcp (ttmrg->expr (tterm-trans-fn tterm opts state))
                            (env-trans-fn a)))
             (ev-smtcp (ttmrg->expr tterm) a)))

  (defthm tterm-trans-fn-preserves-correct-p-forwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (ttmrg-correct-p tterm a))
             (ttmrg-correct-p (tterm-trans-fn tterm opts state)
                              (env-trans-fn a)))))


(define tterm-trans-fn-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       (goal (disjoin cl))
       (type-opts (construct-type-options hint goal))
       ((mv fail tterm) (ttmrg-parse-clause goal))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal (current-cp-fn) *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (new-tt (tterm-trans-fn tterm type-opts state))
       ((if (equal new-tt
                   (make-ttmrg-trivial nil)))
        (mv t nil state))
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
