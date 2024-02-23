;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet and Chris Chen (2 Feb 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "ttmrg3")

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
       (if (ttmrg-p (quote ,tterm))
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
		      (('implies ('if ('ttmrg-p ('quote tterm)) & &) &) tterm)
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
