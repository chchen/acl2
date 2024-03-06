;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
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

(include-book "ttmrg-change3")
(include-book "ttmrg-clause")
(include-book "typed-term-fns")
(include-book "returns-judgement")
(include-book "judgement-fns")
(include-book "ti-bottom-up3")

(set-state-ok t)
(set-bogus-mutual-recursion-ok t)


(defval *top-down-priority*
  '((rationalp smt::x)
    (integerp smt::x)
    (booleanp smt::x)
    (symbolp smt::x)))


;; (defcong judge-set-equiv equal (set::in element set) 2)

(defrule set-membership-fix-elimination
	 (implies (set::in e (judge-set-fix (double-rewrite s)))
		  (set::in e s))
         :in-theory (enable judge-set-fix
                            set::in))

(defrule set-subset-fix-elimination
	 (implies (set::subset e (judge-set-fix (double-rewrite s)))
		  (set::subset e s))
         :in-theory (enable judge-set-fix
                            set::subset))


(defrule set-intersection-fix-elimination
	 (implies (set::intersect (judge-set-fix (double-rewrite a))
				  (judge-set-fix (double-rewrite b)))
		  (set::intersect a b))
	 :in-theory (enable judge-set-fix
                            set::intersect))


(define refine-judgement-helper ((recognizers pseudo-term-listp)
                                 (judgements judge-set-p))
  :measure (acl2-count recognizers)
  :returns (rv judge-set-p)
  (b* ((judgements (judge-set-fix judgements))
       (recognizers (pseudo-term-list-fix recognizers))
       ((if (set::empty judgements)) nil)
       ((unless (consp recognizers)) nil)
       ((cons head tail) recognizers))
    (if (set::in head judgements)
        (set::insert head nil)
      (refine-judgement-helper tail judgements)))
  ///
  (fty::deffixequiv refine-judgement-helper)
  (more-returns
   (rv :name refine-judgement-helper-subset-judgements
       (implies (equal (judge-set-fix judgements) j-fix)
       (set::subset rv j-fix)))))


(define refine-judgement ((judgements judge-set-p)
                          (top judge-set-p))
  :returns (rv judge-set-p)
  (b* ((judgements (judge-set-fix judgements))
       (recognizers (pseudo-term-list-fix *top-down-priority*))
       (top (judge-set-fix top))
       (permissible (set::intersect judgements top)))
    (refine-judgement-helper recognizers permissible))
  ///
  (fty::deffixequiv refine-judgement)
  (more-returns
   (rv :name refine-judgement-subset-intersect-judgements-top
       (implies (and (equal (judge-set-fix judgements) j-fix)
                     (equal (judge-set-fix top) t-fix))
                (set::subset rv (set::intersect j-fix t-fix))))))


(define parse-judge-sets ((exprs pseudo-term-listp)
                          (judgements pseudo-term-listp))
  :returns (rv judge-set-list-p)
  (b* ((exprs (pseudo-term-list-fix exprs))
       (judgements (pseudo-term-list-fix judgements))
       ((unless (consp exprs)) nil)
       ((unless (consp judgements)) nil))
    (cons (parse-judge-set (car exprs) (car judgements))
          (parse-judge-sets (cdr exprs) (cdr judgements)))))


;; A theorem that shows a evaluation relation would be nice here?
(define refine-terminal ((tterm ttmrg-p)
                         (top judge-set-p))
  :guard (or (equal (ttmrg->kind tterm) :quote)
             (equal (ttmrg->kind tterm) :var))
  :returns (rv ttmrg-p)
  (b* ((tterm (ttmrg-fix tterm))
       (top (judge-set-fix top))
       ((unless (mbt (or (equal (ttmrg->kind tterm) :quote)
                         (equal (ttmrg->kind tterm) :var))))
        (make-ttmrg-trivial nil))
       (judgements (ttmrg->judgements tterm))
       (new-judgement (refine-judgement judgements top)))
    (ttmrg-add-smt-judge-set tterm new-judgement)))


(define ttmrg-smt-judgement-expr ((tterm ttmrg-p))
  :returns (rv pseudo-termp)
  (b* ((tterm (ttmrg-fix tterm)))
    (and-list-expr
      (judge-list-flat-expr (ttmrg->smt-judgements tterm)
                            (ttmrg->expr tterm)))))


(defines refine-ttmrg
  :ignore-ok t
  :verify-guards nil
  :well-founded-relation l<

  (define refine-if ((tterm ttmrg-p)
                     (top judge-set-p)
                     (options type-options-p)
                     state)
    :measure (list (ttmrg->expr-count tterm) 2 0)
    :guard (equal (ttmrg->kind tterm)
                  :if)
    :returns (rv ttmrg-p)
    (b* ((tterm (ttmrg-fix tterm))
         (top (judge-set-fix top))
         ((unless (mbt (equal (ttmrg->kind tterm) :if)))
          (make-ttmrg-trivial nil))
         (judgements (ttmrg->judgements tterm))
         (permissible (refine-judgement judgements top))
         (bool (set::insert (judge-fix '(booleanp smt::x)) '()))
         (new-condx (refine-ttmrg (ttmrg->condx tterm)
                                  bool
                                  options
                                  state))
         (new-thenx (refine-ttmrg (ttmrg->thenx tterm)
                                  permissible
                                  options
                                  state))
         (new-elsex (refine-ttmrg (ttmrg->elsex tterm)
                                  permissible
                                  options
                                  state))
         (new-guts (make-ttmrg-guts-if :condx new-condx
                                       :thenx new-thenx
                                       :elsex new-elsex)))
      (ttmrg-add-smt-judge-set (ttmrg-change-guts tterm new-guts)
                               permissible)))

  (define zip-refine ((tterms ttmrg-list-p)
                      (tops judge-set-list-p)
                      (options type-options-p)
                      state)
    :measure (list (ttmrg-list->expr-list-count tterms) 1 0)
    :returns (rv ttmrg-list-p)
    (b* ((tterms (ttmrg-list-fix tterms))
         (tops (judge-set-list-fix tops))
         ((unless (consp tterms)) nil)
         ((unless (consp tops)) nil))
      (cons (refine-ttmrg (car tterms) (car tops) options state)
            (zip-refine (cdr tterms) (cdr tops) options state))))

  (define refine-fn ((tterm ttmrg-p)
                     (top judge-set-p)
                     (options type-options-p)
                     state)
    :measure (list (ttmrg->expr-count tterm) 2 0)
    :guard (equal (ttmrg->kind tterm)
                  :fncall)
    :returns (rv ttmrg-p)
    (b* ((tterm (ttmrg-fix tterm))
         (top (judge-set-fix top))
         ((unless (mbt (equal (ttmrg->kind tterm) :fncall)))
          (make-ttmrg-trivial nil))
         (judgements (ttmrg->judgements tterm))
         (permissible (refine-judgement judgements top))
         (tterm-new (ttmrg-add-smt-judge-set tterm permissible))
         ;; We construct a original-style `term substituted for variable'
         ;; judgement because of the way choose-returns works
         (top-judgement-expr (ttmrg-smt-judgement-expr tterm-new))
         (path-cond-expr (ttmrg->path-cond-expr tterm-new))
         (f (ttmrg->f tterm-new))
         (args (ttmrg->args tterm-new))
         (args-expr (ttmrg-list->expr-list args))
         (args-judgement-exprs (args->judgements-expr args))
         (functions (type-options->functions options))
         (conspair (assoc-equal f functions))
         ((unless conspair) (make-ttmrg-trivial nil))
         (permissible-args (choose-returns top-judgement-expr
                                           f
                                           args-expr
                                           args-judgement-exprs
                                           path-cond-expr
                                           (cdr conspair)
                                           options
                                           state))
         (permissible-judge-sets (parse-judge-sets args-expr                                                   permissible-args))
         (new-args (zip-refine args permissible-judge-sets options
                               state))
         (new-guts (make-ttmrg-guts-fncall :f f :args new-args)))
      (ttmrg-add-smt-judge-set (ttmrg-change-guts tterm new-guts)
                               permissible)))

  (define refine-ttmrg ((tterm ttmrg-p)
                        (top judge-set-p)
                        (options type-options-p)
                        state)
    :measure (list (ttmrg->expr-count tterm) 3 0)
    :returns (rv ttmrg-p)
    (b* (((unless (mbt (ttmrg-p tterm)))
          (make-ttmrg-trivial nil))
         (tterm (ttmrg-fix tterm))
         (top (judge-set-fix top)))
      (case (ttmrg->kind tterm)
        (:quote (refine-terminal tterm top))
        (:var (refine-terminal tterm top))
        (:if (refine-if tterm top options state))
        (:fncall (refine-fn tterm top options state)))))
  ///
  (verify-guards refine-ttmrg))


(define type-judge-topdown-cp ((cl pseudo-term-listp)
                               (smtlink-hint t)
                               state)
  (b* (((unless (pseudo-term-listp cl)) (value (list nil)))
       ((unless (smtlink-hint-p smtlink-hint)) (value (list nil)))
       (goal (disjoin cl))
       ((type-options type-opt) (construct-type-options smtlink-hint goal))
       ((mv fail tterm) (ttmrg-parse-clause goal))
       ((if fail) (value (list nil)))
       (next-cp (cdr (assoc-equal 'type-judge-topdown *SMT-architecture*)))
       ((if (null next-cp)) (value (list nil)))
       (bool (set::insert (judge-fix '(booleanp smt::x)) '()))
       (new-tt (refine-ttmrg tterm bool type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (new-cl (ttmrg-clause new-tt))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (value (list hinted-goal))))


;; (defrule correctness-of-type-judge-topdown-cp
;;   (implies (and (ev-smtcp-meta-extract-global-facts)
;;                 (pseudo-term-listp cl)
;;                 (alistp a)
;;                 (ev-smtcp
;;                  (conjoin-clauses
;;                   (acl2::clauses-result
;;                    (type-judge-topdown-cp cl hints state)))
;;                  a))
;;            (ev-smtcp (disjoin cl) a))
;;   :do-not-induct t
;;   :expand (type-judge-topdown-cp cl hints state)
;;   :in-theory (enable ttmrg-clause)
;;   :rule-classes :clause-processor)
