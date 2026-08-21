;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a computed hints and clause processors that
;; apply rewrite$ to smtlink typed terms.

(in-package "SMT")
(include-book "hints/hint-wrapper" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "basics")
(include-book "hint-interface")
(include-book "ttmrg-clause")

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

(defsection SMT-term-rewrite
  :parents (verified)

  (program)

  (define rewrite$-helper-fn (term hyps theory fuel state)
    (b* (((if (zp fuel))
          (prog2$ (cw "rewrite$-helper reached limit of ~x0 applications"
                      (rewrite-stack-limit (w state)))
                  (mv t nil state)))
         ((mv rewrite-fail result state)
          (acl2::rewrite$ term
                          :hyps hyps
                          :in-theory theory))
         ((if rewrite-fail)
          (prog2$ (cw "rewrite$-helper failed for ~x0 ~x1"
                      term hyps)
                  (mv t nil state)))
         ((list new-term & &) result)
         ((if (equal term new-term)) (value new-term)))
      (prog2$ (cw "rewrite$-helper recurse with fuel ~x0"
                  (1- fuel))
              (rewrite$-helper-fn new-term hyps theory (1- fuel) state))))

  (define rewrite$-helper (term hyps theory state)
    (b* ((fuel (acl2::rewrite-stack-limit (w state)))
         ((unless (and (pseudo-termp term)
                       (pseudo-term-listp hyps)
                       (pseudo-termp theory)
                       (state-p state)
                       (natp fuel)))
          (mv t nil state)))
      (rewrite$-helper-fn term hyps theory fuel state)))

  (define SMT-term-rewrite-hint (cl kwd-alist state)
    :guard-debug t
    :parents (SMT-computed-hints)
    :short "@('SMT::SMT-term-rewrite-hint') WRITE SOMETHING."
    (b* (((unless (and (pseudo-term-listp cl)
                       (consp kwd-alist)
                       (consp (cdr kwd-alist))
                       (consp (cadr kwd-alist))
                       (= (len (cadr kwd-alist))
                          4)
                       (state-p state)))
          (prog2$ (cw "SMT-term-rewrite-hint: preconditions not met")
                  (value nil)))
         ((list* cp-kwd (list next-cp & q-smt-hint &) kwd-alist-tail) kwd-alist)
         ((unless (equal cp-kwd :clause-processor))
          (prog2$ (cw "SMT-term-rewrite-hint: missing clause processor in kwd-alist: ~x0"
                      kwd-alist)
                  (value nil)))
         ((unless (and (quotep q-smt-hint)
                       (smtlink-hint-p (unquote q-smt-hint))))
          (prog2$ (cw "not quoted smtlink-hint-p: ~x0" q-smt-hint)
                  (value nil)))
         (smt-hint (unquote q-smt-hint))
         (translation-theory (smtlink-hint->translation-theory smt-hint))
         (goal (disjoin cl))
         ((mv fail tterm) (ttmrg-parse-clause goal))
         ((if fail) (prog2$ (cw "not a ttmrg-clause: ~x0" tterm)
                            (value nil)))
         (expr (ttmrg->expr tterm))
         (correct-smt-exprs (list (ttmrg-correct-smt-expr tterm)))
         ((mv fail new-expr state)
          (rewrite$-helper expr
                           correct-smt-exprs
                           translation-theory
                           state))
         ((if fail) (value nil)))
      (prog2$ (cw "SMT-term-rewrite-hint orig: ~x0 new: ~x1"
                  expr
                  new-expr)
              (value `(:computed-hint-replacement ((SMT-computed-hint clause))
                       :clause-processor (,next-cp clause ',(cons smt-hint new-expr) state)
                       ,@kwd-alist-tail)))))

  (logic)


  ;; Clause processors
  ;; If rewritten term = original ttmrg->expr, continue as if 'term-rewrite
  ;; Reinjects rewritten term as if it came from 'process-hint
  ;; Discharge equality side condition with hint from translation-theory
  (define term-rewrite-cp ((cl pseudo-term-listp)
                           (hint t)
                           state)
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (consp hint)) (mv t nil state))
         ((cons smt-hint new-expr) hint)
         ((unless (smtlink-hint-p smt-hint)) (mv t nil state))
         ((unless (pseudo-termp new-expr)) (mv t nil state))
         (goal (disjoin cl))
         ((mv fail tterm) (ttmrg-parse-clause goal))
         ((if fail) (mv t nil state))
         (orig-expr (ttmrg->expr tterm))
         (orig-correct-expr (ttmrg-correct-expr tterm)))
      (if (equal orig-expr new-expr)
          (prog2$ (cw "term-rewrite-cp: rewrite$ did not change term")
                  (b* ((next-cp (cdr (assoc-equal 'term-rewrite
                                                  *SMT-architecture*)))
                       ((if (null next-cp)) (mv t nil state))
                       (the-hint
                         `(:clause-processor (,next-cp clause ',smt-hint state)))
                       (new-cl (ttmrg-clause tterm))
                       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
                    (value (list hinted-goal))))
        (prog2$ (cw "term-rewrite-cp: feeding new term back into pipeline")
                (b* ((next-cp (cdr (assoc-equal 'process-hint
                                                *SMT-architecture*)))
                     ((if (null next-cp)) (mv t nil state))
                     (the-hint
                         `(:clause-processor (,next-cp clause ',smt-hint state)))
                     (hinted-goal `((hint-please ',the-hint) ,new-expr))
                     ;; Side condition
                     (side-condition (implies-expr orig-correct-expr
                                                   (equal-expr
                                                     orig-expr
                                                     new-expr)))
                     (side-hint `(acl2::hint-wrapper
                                   '(:in-theory
                                     ,(smtlink-hint->translation-theory smt-hint))))
                     (hinted-goal2 `((not ,side-hint)
                                     ,side-condition)))
                  (value (list hinted-goal
                               hinted-goal2)))))))

  (defrule correctness-of-term-rewrite-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev-smtcp
                    (conjoin-clauses
                      (acl2::clauses-result
                        (term-rewrite-cp cl hint state)))
                    a))
             (ev-smtcp (disjoin cl) a))
    :do-not-induct t
    :expand (term-rewrite-cp cl hint state)
    :in-theory (disable ev-smtcp-of-disjoin)
    :rule-classes :clause-processor)

  )
