;; Copyright (C) 2021, University of British Columbia
;; Written by Mark Greenstreet (December 15th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

; ttmrg-change.lisp
;   Functions that preserve ttmrg-correct-p when updating one or more
;   fields of a ttmrg-p term.

(include-book "ttmrg3")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; Disabling the 30 top "useless" made no significant change in the time for
; certification.  I won't clutter this book with a paean to my impatience.


(define ttmrg-add-judge-set ((tterm ttmrg-p) (new-judges judge-set-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg (ttmrg-fix tterm)
		:judgements (set::union (judge-set-fix new-judges)
					(ttmrg->judgements tterm)))
  ///
  (more-returns
    (new-tt :name ttmrg->path-cond-of-ttmrg-add-judge-set
      (ttmrg->path-cond-equiv new-tt tterm))

    (new-tt :name ttmrg->judgements-of-ttmrg-add-judge-set
      (equal (ttmrg->judgements new-tt)
	     (set::union (judge-set-fix new-judges)
			 (ttmrg->judgements tterm))))

    (new-tt :name ttmrg->guts-equiv-of-ttmrg-add-judge-set
      (ttmrg->guts-equiv new-tt tterm)))

  (local (in-theory (disable ttmrg-add-judge-set)))

  (defrule ttmrg->judgements-ev-of-ttmrg-add-judge-set
    (equal (ttmrg->judgements-ev (ttmrg-add-judge-set tterm new-judges) a)
	   (and (all<judge-ev> (judge-set-fix new-judges) (ttmrg->expr tterm) a)
		(ttmrg->judgements-ev tterm a)))
    :in-theory (enable ttmrg->judgements-ev))
  
  (defrule ttmrg-correct-p-of-ttmrg-add-judge-set
    (implies (and (ttmrg-correct-p tterm a)
		  (implies (ttmrg->path-cond-ev tterm a)
			   (all<judge-ev> (judge-set-fix new-judges)
					  (ttmrg->expr tterm)
					  a)))
	     (ttmrg-correct-p (ttmrg-add-judge-set tterm new-judges) a))
      :expand ((ttmrg-correct-p (ttmrg-add-judge-set tterm new-judges) a))))

(define ttmrg-add-judge ((tterm ttmrg-p) (new-judge judge-p))
  :returns (new-tt ttmrg-p)
  (ttmrg-add-judge-set tterm (set::insert (judge-fix new-judge) nil))
  ///
  (more-returns
    (new-tt :name ttmrg->path-cond-of-ttmrg-add-judge
      (ttmrg->path-cond-equiv new-tt tterm))

    (new-tt :name ttmrg->judgements-of-ttmrg-add-judge
      (equal (ttmrg->judgements new-tt)
	     (set::insert (judge-fix new-judge)
			 (ttmrg->judgements tterm))))

    (new-tt :name ttmrg->guts-equiv-of-ttmrg-add-judge
      (ttmrg->guts-equiv new-tt tterm))

    (new-tt :name ttmrg->judgements-ev-of-ttmrg-add-judge
      (equal (ttmrg->judgements-ev new-tt a)
	     (and (judge-ev (judge-fix new-judge) (ttmrg->expr tterm) a)
		  (ttmrg->judgements-ev tterm a))))
  
    (new-tt :name ttmrg-correct-p-of-ttmrg-add-judge
      (implies (and (ttmrg-correct-p tterm a)
		    (implies (ttmrg->path-cond-ev tterm a)
			     (judge-ev (judge-fix new-judge)
				       (ttmrg->expr tterm)
				       a)))
	       (ttmrg-correct-p new-tt a)))))


(define ttmrg-add-path-cond-set ((tterm ttmrg-p) (new-pcs pseudo-term-set-p))
  :returns (new-tt ttmrg-p)
  (change-ttmrg (ttmrg-fix tterm)
		:path-cond (set::union (pseudo-term-set-fix new-pcs)
				       (ttmrg->path-cond tterm)))
  ///
  (defcong ttmrg-equiv ttmrg-equiv (ttmrg-add-path-cond-set tterm new-pcs) 1)
  (defcong pseudo-term-set-equiv ttmrg-equiv (ttmrg-add-path-cond-set tterm new-pcs) 2)

  (more-returns
    (new-tt :name ttmrg->path-cond-of-ttmrg-add-path-cond-set
      (equal (ttmrg->path-cond new-tt)
	     (set::union (pseudo-term-set-fix new-pcs)
			(ttmrg->path-cond tterm))))

    (new-tt :name ttmrg->judgements-equiv-of-ttmrg-add-path-cond-set
      (ttmrg->judgements-equiv new-tt tterm))

    (new-tt :name ttmrg->guts-equiv-of-ttmrg-add-path-cond-set
      (ttmrg->guts-equiv new-tt tterm)))

    (local (in-theory (disable ttmrg-add-path-cond-set)))

    (defrule ttmrg->judgements-and-expr-equiv-of-ttmrg-add-path-cond-set
      (ttmrg->judgements-and-expr-equiv
	(ttmrg-add-path-cond-set tterm new-pcs)
	tterm)
      :in-theory (enable ttmrg->judgements-and-expr-equiv))

    (defrule ttmrg->path-cond-ev-of-ttmrg-add-path-cond-set
      (equal (ttmrg->path-cond-ev (ttmrg-add-path-cond-set tterm new-pcs) a)
	     (and (ttmrg->path-cond-ev tterm a)
		  (all<pseudo-term-ev> (pseudo-term-set-fix new-pcs) a)))
      :in-theory (enable ttmrg->path-cond-ev))

    (defrule ttmrg-correct-p-of-ttmrg-add-path-cond-set
      (implies (ttmrg-correct-p tterm a)
	       (ttmrg-correct-p (ttmrg-add-path-cond-set tterm new-pcs) a))
      :expand ((ttmrg-correct-p (ttmrg-add-path-cond-set tterm new-pcs) a))))

(define ttmrg-add-path-cond-tterm ((tterm ttmrg-p) (parent ttmrg-p))
  :returns (new-tt ttmrg-p)
  (ttmrg-add-path-cond-set tterm (ttmrg->path-cond parent))
  ///
  (defcong ttmrg-equiv ttmrg-equiv (ttmrg-add-path-cond-tterm tterm parent) 1)
  (defcong ttmrg->path-cond-equiv ttmrg-equiv (ttmrg-add-path-cond-tterm tterm parent) 2)
  (more-returns
    (new-tt :name ttmrg->guts-equiv-of-ttmrg-add-path-cond-term
      (ttmrg->guts-equiv new-tt tterm))

    (new-tt :name ttmrg-correct-p-of-ttmrg-add-path-cond-tterm
      (implies (ttmrg-correct-p tterm a)
	       (ttmrg-correct-p new-tt a)))

    (new-tt :name ttmrg->path-cond-ev-of-ttmrg-add-path-cond-tterm
      (equal (ttmrg->path-cond-ev new-tt a)
	     (and (ttmrg->path-cond-ev tterm a)
		  (ttmrg->path-cond-ev parent a)))
      :hints(("Goal" :expand (ttmrg->path-cond-ev parent a))))))

(define ttmrg-add-path-cond ((tterm ttmrg-p) (new-pc pseudo-termp))
  :returns (new-tt ttmrg-p)
  (ttmrg-add-path-cond-set tterm (set::insert (pseudo-term-fix new-pc) nil))
  ///
  (defcong ttmrg-equiv ttmrg-equiv (ttmrg-add-path-cond tterm new-pcs) 1)
  (defcong pseudo-term-equiv ttmrg-equiv (ttmrg-add-path-cond tterm new-pcs) 2)
  (more-returns
    (new-tt :name ttmrg->guts-equiv-of-ttmrg-add-path-cond
      (ttmrg->guts-equiv new-tt tterm))

    (new-tt :name ttmrg-correct-p-of-ttmrg-add-path-cond
      (implies (ttmrg-correct-p tterm a)
	       (ttmrg-correct-p new-tt a)))

    (new-tt :name ttmrg->path-cond-ev-of-ttmrg-add-path-cond
      (equal (ttmrg->path-cond-ev new-tt a)
	     (and (ev-smtcp (pseudo-term-fix new-pc) a)
		  (ttmrg->path-cond-ev tterm a)))
      :hints(("Goal" :in-theory (enable pseudo-term-ev))))))



; the functions above allow us to update the path-cond or judgements or a
; single ttmrg-p object.  ttmrg-p objects for trees corresponding to the syntax
; of the expression that they are annotating.  The
;     (ttmrg-propagate name :pre fn-pre :post fn-post)
; macro below introduces
;     ttmrg-propagate-<$name$>-term
; (and several other functions) that performs a depth-first traversal the tree
; updating each node with fn-pre (default: ttmrg-fix) before traversing the
; descendants and ; updating with fn-post (default: ttmrg-fix) after traversing
; the descendants.  Functions fn-pre and fn-post must ensure:
;   (ttmrg-p (fn-pxx tterm))
;   (ttmrg->path-cond-equiv (fn-pxx tterm) tterm)
;   (ttmrg->expr-equiv (fn-pxx tterm) tterm)
;   (implies (ttmrg-correct-p tterm a) (ttmrg-correct-p (fn-pxx tterm) a))
; The function ttmrg-propagate-<$name$>-term then makes the same guarantees.

(define ttmrg-update-term-default ((tterm ttmrg-p) (opts acl2::any-p) state)
  (declare (ignore opts state))
  :returns (new-tt ttmrg-p)
  (ttmrg-fix tterm)
  ///
  (more-returns
    (new-tt :name ttmrg->path-cond-of-ttmrg-update-term-default
      (ttmrg->path-cond-equiv new-tt tterm))

    (new-tt :name ttmrg->expr-of-ttmrg-update-term-default
      (ttmrg->expr-equiv new-tt tterm))

    (new-tt :name ttmrg-correct-p-of-ttmrg-update-term-default
      (implies (ttmrg-correct-p tterm a)
	       (ttmrg-correct-p new-tt a)))))

(encapsulate
  (((ttmrg-update-term-pre * * state) => *)
   ((ttmrg-update-term-post * * state) => *))

  (local (defun ttmrg-update-term-pre (tterm opts state)
	   (ttmrg-update-term-default tterm opts state)))

  (defthm ttmrg-p-of-ttmrg-update-term-pre
    (ttmrg-p (ttmrg-update-term-pre tterm opts state)))

  (defthm ttmrg->path-cond-of-ttmrg-update-term-pre
    (ttmrg->path-cond-equiv (ttmrg-update-term-pre tterm opts state) tterm))

  (defthm ttmrg->expr-of-ttmrg-update-term-pre
    (ttmrg->expr-equiv (ttmrg-update-term-pre tterm opts state) tterm))

  (defthm ttmrg-correct-p-of-ttmrg-update-term-pre
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp a) ; BOZO
		  (ttmrg-correct-p tterm a))
	     (ttmrg-correct-p (ttmrg-update-term-pre tterm opts state) a)))

  ; Yuck -- a cut-and-paste to create the -post version.  If this gets
  ; used in yet another way, I should probably write a macro.
  (local (defun ttmrg-update-term-post (tterm opts state)
	   (ttmrg-update-term-default tterm opts state)))

  (defthm ttmrg-p-of-ttmrg-update-term-post
    (ttmrg-p (ttmrg-update-term-post tterm opts state)))

  (defthm ttmrg->path-cond-of-ttmrg-update-term-post
    (ttmrg->path-cond-equiv (ttmrg-update-term-post tterm opts state) tterm))

  (defthm ttmrg->expr-of-ttmrg-update-term-post
    (ttmrg->expr-equiv (ttmrg-update-term-post tterm opts state) tterm))

  (defthm ttmrg-correct-p-of-ttmrg-update-term-post
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp a) ; BOZO
		  (ttmrg-correct-p tterm a))
	     (ttmrg-correct-p (ttmrg-update-term-post tterm opts state) a))))

(defrule ttmrg-update-term-pre-preserves-ttmrg->expr-count
  (equal (ttmrg->expr-count (ttmrg-update-term-pre tterm opts state))
	 (ttmrg->expr-count tterm)))

(defrule ttmrg-update-term-post-preserves-ttmrg->expr-count
  (equal (ttmrg->expr-count (ttmrg-update-term-post tterm opts state))
	 (ttmrg->expr-count tterm)))

(defun ttmrg-propagate-defines-fn (name fn-pre fn-post opt-guard more-events)
  (b* ((defines-name (symcat 'ttmrg-propagate- name))
       (fn-term (symcat defines-name '-term))
       (fn-guts (symcat defines-name '-guts))
       (fn-term-if (symcat defines-name '-if))
       (fn-term-fncall (symcat defines-name '-fncall))
       (fn-args (symcat defines-name '-args))
       (more-formals `((opts ,opt-guard) (state state-p)))
       (more-actuals '(opts state)))
    `(defines ,defines-name
       :verify-guards nil
       :well-founded-relation l<
       (define ,fn-term ((tterm ttmrg-p) ,@more-formals)
	 :flag term
	 :returns (new-tt ttmrg-p)
	 :measure (list (ttmrg->expr-count tterm) 3)
	 (,fn-post (,fn-guts (,fn-pre tterm ,@more-actuals)
				,@more-actuals)
		 ,@more-actuals))

       (define ,fn-guts ((tterm ttmrg-p) ,@more-formals)
	 :flag guts
	 :returns (new-tt ttmrg-p)
	 :measure (list (ttmrg->expr-count tterm) 2)
	 (case (ttmrg->kind tterm)
	   (:var (ttmrg-fix tterm))
	   (:quote (ttmrg-fix tterm))
	   (:if (,fn-term-if tterm ,@more-actuals))
	   (:fncall (,fn-term-fncall tterm ,@more-actuals))))

       (define ,fn-term-if ((tterm ttmrg-p) ,@more-formals)
	 :flag if
	 :returns (new-tt ttmrg-p)
	 :measure (list (ttmrg->expr-count tterm) 1)
	 (if (equal (ttmrg->kind tterm) :if)
	   (ttmrg
	     (ttmrg->path-cond tterm)
	     (ttmrg->judgements tterm)
	     (ttmrg-guts-if
	       (,fn-term (ttmrg->condx tterm) ,@more-actuals)
	       (,fn-term (ttmrg->thenx tterm) ,@more-actuals)
	       (,fn-term (ttmrg->elsex tterm) ,@more-actuals)))
	   (ttmrg-fix tterm)))

       (define ,fn-term-fncall ((tterm ttmrg-p) ,@more-formals)
	 :flag fncall
	 :returns (new-tt ttmrg-p)
	 :measure (list (ttmrg->expr-count tterm) 1)
	 (if (equal (ttmrg->kind tterm) :fncall)
	   (ttmrg
	     (ttmrg->path-cond tterm)
	     (ttmrg->judgements tterm)
	     (ttmrg-guts-fncall
	       (ttmrg->f tterm)
	       (,fn-args (ttmrg->args tterm) ,@more-actuals)))
	   (ttmrg-fix tterm)))

       (define ,fn-args ((args ttmrg-list-p) ,@more-formals)
	 :flag args
	 :returns (new-args ttmrg-list-p)
	 :measure (list (ttmrg-list->expr-list-count args) 0)
	 (if (consp args)
	   (cons (,fn-term (car args) ,@more-actuals)
		 (,fn-args (cdr args) ,@more-actuals))
	   nil))
       ///
       (verify-guards ,fn-term)
       ,@more-events)))

; an example:
; (ttmrg-propagate-defines-fn 'foo 'foo-pre 'foo-post 'rationalp nil)

(defmacro ttmrg-propagate-defines
  (name
   &key (pre 'ttmrg-update-term-default)
        (post 'ttmrg-update-term-default)
	(opt-guard 'acl2::any-p)
        (more-events 'nil))
  (ttmrg-propagate-defines-fn name pre post opt-guard more-events))

(ttmrg-propagate-defines generic
			 :pre ttmrg-update-term-pre
			 :post ttmrg-update-term-post
			 :more-events (
  (local (defrule ttmrg-propagate-generic-args-when-consp
    (implies (consp args)
	     (equal (ttmrg-propagate-generic-args args opts state)
		    (cons (ttmrg-propagate-generic-term (car args) opts state)
			  (ttmrg-propagate-generic-args (cdr args) opts state))))))

  (local (defrule ttmrg-propagate-generic-args-of-atom
    (implies (not (consp args))
	     (not (ttmrg-propagate-generic-args args opts state)))
    :expand ((ttmrg-propagate-generic-args args opts state))))

  (local (defrule lemma-fncall-judgements
    (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
      (implies (and (equal (ttmrg->kind tterm) :fncall)
		    (acl2::any-p opts) (state-p state))
	(ttmrg->judgements-equiv new-tt tterm)))
    :expand (ttmrg-propagate-generic-fncall tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-fncall-expr
    (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state))
	  (new-args (ttmrg-propagate-generic-args (ttmrg->args tterm) opts state)))
      (implies
	(ttmrg-list->expr-list-equiv new-args (ttmrg->args tterm))
	(ttmrg->expr-equiv new-tt tterm)))
    :in-theory (enable ttmrg->expr ttmrg->f)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-fncall-trivial
    (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
      (implies (not (equal (ttmrg->kind tterm) :fncall))
	       (equal new-tt (ttmrg-fix tterm))))))

  (local (defrule lemma-if-judgements 
    (let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
      (implies (and (equal (ttmrg->kind tterm) :if)
		    (acl2::any-p opts) (state-p state))
	(ttmrg->judgements-equiv new-tt tterm)))
    :expand (ttmrg-propagate-generic-if tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-if-expr
    (let ((new-tt (ttmrg-propagate-generic-if tterm opts state))
          (new-condx (ttmrg-propagate-generic-term (ttmrg->condx tterm) opts state))
	  (new-thenx (ttmrg-propagate-generic-term (ttmrg->thenx tterm) opts state))
	  (new-elsex (ttmrg-propagate-generic-term (ttmrg->elsex tterm) opts state)))
      (implies
	(and (equal (ttmrg->kind tterm) :if)
	     (ttmrg->expr-equiv new-condx (ttmrg->condx tterm))
	     (ttmrg->expr-equiv new-thenx (ttmrg->thenx tterm))
	     (ttmrg->expr-equiv new-elsex (ttmrg->elsex tterm)))
	(ttmrg->judgements-and-expr-equiv new-tt tterm)))
    :in-theory (enable ttmrg->expr )))

  (local (defrule lemma-if-trivial
    (let ((new-tt (ttmrg-propagate-generic-if tterm opts st)))
      (implies (not (equal (ttmrg->kind tterm) :if))
	       (equal new-tt (ttmrg-fix tterm))))))

  (defthm-ttmrg-propagate-generic-flag
    (defthm ttmrg->expr-of-ttmrg-propagate-generic-term
      (let ((new-tt (ttmrg-propagate-generic-term tterm opts state)))
	(ttmrg->expr-equiv new-tt tterm))
      :flag term)
    
    (defthm ttmrg->expr-of-ttmrg-propagate-generic-guts
      (let ((new-tt (ttmrg-propagate-generic-guts tterm opts state)))
	(ttmrg->expr-equiv new-tt tterm))
      :flag guts)
    
    (defthm ttmrg->expr-of-ttmrg-propagate-generic-if
      (let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
	(ttmrg->expr-equiv new-tt tterm))
      :flag if)
    
    (defthm ttmrg->expr-of-ttmrg-propagate-generic-fncall
      (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
	(ttmrg->expr-equiv new-tt tterm))
      :flag fncall)
    
    (defthm ttmrg-list->expr-list-of-ttmrg-propagate-generic-args
      (let ((new-args (ttmrg-propagate-generic-args args opts state)))
	(ttmrg-list->expr-list-equiv new-args args))
      :flag args)

    :hints(("Goal"
      :in-theory (enable ttmrg-propagate-generic-term
			 ttmrg-propagate-generic-guts))))
  
  (local (defrule ttmrg->path-cond-of-ttmrg-propagate-generic-fncall
    (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
      (ttmrg->path-cond-equiv new-tt tterm))
    :expand (ttmrg-propagate-generic-fncall tterm opts state)))
  
  (local (defrule ttmrg->path-cond-of-ttmrg-propagate-generic-if
    (let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
      (ttmrg->path-cond-equiv new-tt tterm))
    :expand (ttmrg-propagate-generic-if tterm opts state)))
  
  (local (defrule ttmrg->path-cond-of-ttmrg-propagate-generic-guts
    (let ((new-tt (ttmrg-propagate-generic-guts tterm opts state)))
      (ttmrg->path-cond-equiv new-tt tterm))
    :expand (ttmrg-propagate-generic-guts tterm opts state)))
  
  (defrule ttmrg->path-cond-of-ttmrg-propagate-generic-term
    (let ((new-tt (ttmrg-propagate-generic-term tterm opts state)))
      (ttmrg->path-cond-equiv new-tt tterm))
    :expand (ttmrg-propagate-generic-term tterm opts state))

  (defrule ttmrg-list->path-cond-of-ttmrg-propagate-generic-args
    (let ((new-args (ttmrg-propagate-generic-args args opts state)))
      (ttmrg-list->path-cond-equiv new-args args))
    :in-theory (enable ttmrg-list->path-cond-equiv)
    :induct (len args))

  (local (defrule lemma-fncall-correct
    (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state))
	  (new-args (ttmrg-propagate-generic-args (ttmrg->args tterm) opts state)))
      (implies (and (equal (ttmrg->kind tterm) :fncall)
		    (ttmrg-correct-p tterm a)
		    (ttmrg-list-correct-p new-args a))
	       (ttmrg-correct-p new-tt a)))
    :in-theory (disable ttmrg-propagate-generic-fncall)
    :expand ((ttmrg-correct-p (ttmrg-propagate-generic-fncall tterm opts state) a))
    :prep-lemmas (
      (defrule lemma-1
	(let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state))
	      (new-args (ttmrg-propagate-generic-args (ttmrg->args tterm) opts state)))
	  (implies (equal (ttmrg->kind tterm) :fncall)
		   (and (ttmrg-list-equiv (ttmrg->args new-tt) new-args)
			(equal (ttmrg->kind new-tt) :fncall))))
	:expand ((ttmrg-propagate-generic-fncall tterm opts state)))
      (defrule lemma-2
	(let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
	  (ttmrg->judgements-equiv new-tt tterm))
	:expand ((ttmrg-propagate-generic-fncall tterm opts state)))
      (defrule lemma-3
	(let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
	  (ttmrg->judgements-and-expr-equiv new-tt tterm))
	:in-theory (enable ttmrg->judgements-and-expr-equiv)
;	:expand ((ttmrg->judgements-and-expr-equiv
;		   (ttmrg-propagate-generic-fncall tterm opts state) tterm))
	:cases ((equal (ttmrg->kind tterm) :fncall))))))

  (local (defrule lemma-if-correct
    (let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
      (implies (and (equal (ttmrg->kind tterm) :if)
		    (ttmrg-correct-p tterm a)
		    (ttmrg-correct-p (ttmrg-propagate-generic-term (ttmrg->condx tterm) opts state) a)
		    (ttmrg-correct-p (ttmrg-propagate-generic-term (ttmrg->thenx tterm) opts state) a)
		    (ttmrg-correct-p (ttmrg-propagate-generic-term (ttmrg->elsex tterm) opts state) a))
	       (ttmrg-correct-p new-tt a)))
    :in-theory (disable ttmrg-propagate-generic-if)
    :expand ((ttmrg-correct-p (ttmrg-propagate-generic-if tterm opts state) a))
    :prep-lemmas (
      (defrule lemma-1
	(let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
	  (implies (equal (ttmrg->kind tterm) :if)
		   (and (equal (ttmrg->kind new-tt) :if)
			(ttmrg-equiv (ttmrg->condx new-tt)
				     (ttmrg-propagate-generic-term (ttmrg->condx tterm) opts state))
			(ttmrg-equiv (ttmrg->thenx new-tt)
				     (ttmrg-propagate-generic-term (ttmrg->thenx tterm) opts state))
			(ttmrg-equiv (ttmrg->elsex new-tt)
				     (ttmrg-propagate-generic-term (ttmrg->elsex tterm) opts state)))))
	:expand ((ttmrg-propagate-generic-if tterm opts state))))))

  (defthm-ttmrg-propagate-generic-flag
    (defthm ttmrg-correct-p-of-ttmrg-propagate-generic-term
      (let ((new-tt (ttmrg-propagate-generic-term tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (ttmrg-correct-p tterm a))
		 (ttmrg-correct-p new-tt a)))
      :flag term)
    
    (defthm ttmrg-correct-p-of-ttmrg-propagate-generic-guts
      (let ((new-tt (ttmrg-propagate-generic-guts tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (ttmrg-correct-p tterm a))
	  (ttmrg-correct-p new-tt a)))
      :flag guts)
    
    (defthm ttmrg-correct-p-of-ttmrg-propagate-generic-if
      (let ((new-tt (ttmrg-propagate-generic-if tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (ttmrg-correct-p tterm a))
	  (ttmrg-correct-p new-tt a)))
      :flag if)
    
    (defthm ttmrg-correct-p-of-ttmrg-propagate-generic-fncall
      (let ((new-tt (ttmrg-propagate-generic-fncall tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (ttmrg-correct-p tterm a))
	  (ttmrg-correct-p new-tt a)))
      :flag fncall)
    
    (defthm ttmrg-list-correct-p-of-ttmrg-propagate-generic-args
      (let ((new-args (ttmrg-propagate-generic-args args opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (ttmrg-list-correct-p args a))
		 (ttmrg-list-correct-p new-args a)))
      :flag args)
    :hints(("Goal"
      :in-theory (disable ttmrg-propagate-generic-fncall ttmrg-propagate-generic-if))))))

(defun ttmrg-propagate-fn (name fn-pre fn-post opt-guard)
  (ttmrg-propagate-defines-fn name fn-pre fn-post opt-guard
    (b* ((defines-name (symcat 'ttmrg-propagate- name))
	 (fn-term (symcat defines-name '-term))
	 (fn-guts (symcat defines-name '-guts))
	 (fn-term-if (symcat defines-name '-if))
	 (fn-term-fncall (symcat defines-name '-fncall))
	 (fn-args (symcat defines-name '-args))
	 (lemma-pre-type (symcat defines-name '-lemma-pre-type))
	 (lemma-pre-expr (symcat defines-name '-lemma-pre-expr))
	 (lemma-pre-path (symcat defines-name '-lemma-path-pre-cond))
	 (lemma-pre-correct (symcat defines-name '-lemma-pre-correct))
	 (lemma-post-type (symcat defines-name '-lemma-post-type))
	 (lemma-post-expr (symcat defines-name '-lemma-post-expr))
	 (lemma-post-path (symcat defines-name '-lemma-post-path-cond))
	 (lemma-post-correct (symcat defines-name '-lemma-post-correct))
	 (thm-expr (symcat 'ttmrg->expr-of- fn-term))
	 (thm-path-cond (symcat 'ttmrg->path-cond-of- fn-term))
	 (thm-correct (symcat 'ttmrg-correct-p-of- fn-term))
	 (more-actuals '(opts state))
	 (fi-bindings `((ttmrg-update-term-pre ,fn-pre)
			(ttmrg-update-term-post ,fn-post)
			(ttmrg-propagate-generic-term ,fn-term)
			(ttmrg-propagate-generic-guts ,fn-guts)
			(ttmrg-propagate-generic-if ,fn-term-if)
			(ttmrg-propagate-generic-fncall ,fn-term-fncall)
			(ttmrg-propagate-generic-args ,fn-args))))
      `((local (defrule ,lemma-pre-type
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (ttmrg-p new-tt))))
        (local (defrule ,lemma-pre-expr
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (ttmrg->expr-equiv new-tt tterm))))
        (local (defrule ,lemma-pre-path
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (ttmrg->path-cond-equiv new-tt tterm))))
        (local (defrule ,lemma-pre-correct
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
			  (ttmrg-correct-p tterm a))
		     (ttmrg-correct-p new-tt a)))))
        (local (defrule ,lemma-post-type
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (ttmrg-p new-tt))))
        (local (defrule ,lemma-post-expr
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (ttmrg->expr-equiv new-tt tterm))))
        (local (defrule ,lemma-post-path
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (ttmrg->path-cond-equiv new-tt tterm))))
        (local (defrule ,lemma-post-correct
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
			  (ttmrg-correct-p tterm a))
		     (ttmrg-correct-p new-tt a)))))
	(defrule ,thm-expr
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (ttmrg->expr-equiv new-tt tterm))
	  :use((:functional-instance ttmrg->expr-of-ttmrg-propagate-generic-term
		  ,@fi-bindings))
	  :in-theory '(
	    (:congruence ttmrg-equiv-implies-equal-ttmrg-correct-p-1)
	    (:definition ,fn-term)
	    (:definition ,fn-guts)
	    (:definition ,fn-term-if)
	    (:definition ,fn-term-fncall)
	    (:definition ,fn-args)
	    (:equivalence ttmrg->expr-equiv-is-an-equivalence)
	    (:equivalence ttmrg->path-cond-equiv-is-an-equivalence)
	    (:forward-chaining ttmrg->kind-possibilities)
	    (:rewrite ,lemma-pre-type)
	    (:rewrite ,lemma-pre-expr)
	    (:rewrite ,lemma-pre-path)
	    (:rewrite ,lemma-pre-correct)
	    (:rewrite ,lemma-post-type)
	    (:rewrite ,lemma-post-expr)
	    (:rewrite ,lemma-post-path)
	    (:rewrite ,lemma-post-correct)
	    (:rewrite ttmrg-p-of-ttmrg-update-path-cond-children)
	    (:type-prescription ttmrg-correct-p)))

	(defrule ,thm-path-cond
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (ttmrg->path-cond-equiv new-tt tterm))
	  :use((:functional-instance ttmrg->path-cond-of-ttmrg-propagate-generic-term
		  ,@fi-bindings)))

	(defrule ,thm-correct
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
		          (ttmrg-correct-p tterm a))
		     (ttmrg-correct-p new-tt a)))
	  :use((:functional-instance ttmrg-correct-p-of-ttmrg-propagate-generic-term
		  ,@fi-bindings)))))))

(defmacro ttmrg-propagate (name &key (pre 'ttmrg-update-term-default)
				     (post 'ttmrg-update-term-default)
				     (opt-guard 'acl2::any-p))
  (ttmrg-propagate-fn name pre post opt-guard))
