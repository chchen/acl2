;; define an alist that maps natural numbers to symbols, and then introduce
;; the theorems Smtlink needs to translate such alists to Z3 arrays.
;;
;; https://www.sandraboynton.com/sboynton/Amazing%20Cows%20interview.html

(in-package "SMT")
(include-book "std/util/top" :dir :system)
(include-book "alist")

(local (encapsulate nil
  (define kp (x)
    :returns (ok booleanp)
    (natp x))

  (define vp (x)
    :returns (ok booleanp)
    (symbolp x))

  (define kvp (x)
    (and (consp x)
	 (kp (car x))
	 (vp (cdr x))))

  (define mkvp (x) (implies x (kvp x)))

  (define kvap (x)
    (if x
	(and (consp x)
	     (kvp (car x))
	     (kvap (cdr x)))
	t))

  (acl2::define-sk ar-kv-p (ar)
    :returns (ok)
    (forall (k)
      (and (ua-p ar)
	   (mkvp (ua-select k ar)))))
  (define ar-kv-init ()
    (ua-init nil)
    ///
    (in-theory (disable (:e ar-kv-init))))

  (define ar-kv-store ((k kp) (kv mkvp) (ar ar-kv-p))
    :verify-guards nil
    (if (and (kp k) (mkvp kv) (ar-kv-p ar))
	(ua-store k kv ar)
	(ar-kv-init)))

  (define ar-kv-from-al ((al kvap))
    :verify-guards nil
    (if (and (consp al) (kvp (car al)))
      (ar-kv-store (caar al) (car al) (ar-kv-from-al (cdr al)))
      (ar-kv-init)))

  (define ar-kv-select ((k kp) (ar ar-kv-p))
    (if (ar-kv-p ar)
	(ua-select k ar)
	nil))

  (acl2::define-sk ar-kv-equiv (al ar)
    :returns (ok)
    :verify-guards nil
    (forall (k)
	    (and (kvap al)
		 (ar-kv-p ar)
		 (equal (assoc-equal k al) (ar-kv-select k ar)))))


  ;; Rather than writing the long functional instantiation hint for each of the
  ;; theorems below, I'll wrap it up with a macro.
  (defmacro fi-thm (name claim ar-thm &optional theory)
    `(defthm ,name ,claim :hints(("Goal"
       :in-theory ,theory
       :use((:functional-instance ,ar-thm
				  ;; instantiate the generic functions
				  (ar-key-p kp)
				  (ar-val-p vp)
				  ;; instantiate the other relevant functions
				  (ar-key-val-consp kvp)
				  (ar-maybe-key-val-consp mkvp)
				  (ar-key-val-alist-p kvap)
				  (ar-p ar-kv-p)
				  (ar-p-witness ar-kv-p-witness)
				  (ar-init ar-kv-init)
				  (ar-store ar-kv-store)
				  (ar-from-al ar-kv-from-al)
				  (ar-select ar-kv-select)
				  (ar-equiv ar-kv-equiv)
				  (ar-equiv-witness ar-kv-equiv-witness)))))))


  ;; return type theorems
  ;;   In addition to providing returns theorems used by Smtlink, proving
  ;;   these theorems by functional instantiation has the salubrious effect
  ;;   of establishing the constraints for funcitional instantation one
  ;;   function at a time.  This seems to avoid having ACL2 generate a big,
  ;;   complicated constraint that it then is unable to discharge.

  (fi-thm booleanp-of-kvp
    (booleanp (kvp x))
    booleanp-of-ar-key-val-consp '(kvp booleanp-of-kp booleanp-of-vp))

  (fi-thm booleanp-of-mkvp
    (booleanp (mkvp x))
    booleanp-of-ar-maybe-key-val-consp '(mkvp (:t kvp)))

  (fi-thm booleanp-of-kvap
    (booleanp (kvap x))
    booleanp-of-ar-key-val-alist-p '(kvap))

  (encapsulate nil
    ;; booleanp-of-ar-kv-p can be prove using functional instantiation of
    ;;   booleanp-of-ar-p in the theory '(ar-kv-p ar-kv-p-necc).  So, why
    ;;   am I proving it by introducing three lemmas and using those?
    ;;   My reason is that the proof for boolean-p-of-ar-kv-equiv (below)
    ;;   fails with the corresponding hint.  I believe that's because the
    ;;   functional constraints require showing that the bodies of
    ;;   ar-kv-equiv and ar-kv-equiv-witness are what one would expect.
    ;;   Sadly, the rewrite rule for ar-kv-equiv-necc has a hypothesis of
    ;;     (ar-kv-equiv al ar)
    ;;   The corresponding term in the proof goal gets re-written by the
    ;;   rule (:d ar-kv-equiv), and then the rule for ar-kv-equiv-necc fails
    ;;   to match.  At least that's what I think is happening.
    ;;     I fixed the problem by using proof-builder to identify a sufficient
    ;;   set of lemmas, prove those, and then prove the main theorem.  I'm
    ;;   using the same approach here because I'm concerned that even though
    ;;   the more succinct proof just using theory '(ar-kv-p ar-kv-p-necc)
    ;;   succeeds, it may be sensitive to the order in which rewrites are
    ;;   performed.  The current proof seems likely to be more robust.
    ;;
    ;; Here's how I got the lemmas.  I gave the commands:
    ;;   ACL2 !> (verify (booleanp (ar-kv-equiv al ar)))
    ;;   ->: (use (:functional-instance booleanp-of-ar-equiv ...))
    ;;   ->: :s  ;; main.1 is trivial to discharge
    ;;   ->: :split  ;; produces 7 goals corresponding to the functional constraints.
    ;;   ->: print-all-goals
    ;; I stated a lemma for each of the goals printed above.  The lemma
    ;; main.4 is the contrapositive of main.1, and unused in the final proof;
    ;  so I don't state a lemma for it here.
    (local (defthm fi-ar-kv-p-1
      (implies (ar-kv-p ar) (ua-p ar))
      :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

    (local (defthm fi-ar-kv-p-2
      (implies (ar-kv-p ar) (mkvp (ua-select k ar)))
      :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

    (local (defthm fi-ar-kv-p-3
      (implies (ua-p ar)
	       (equal (ar-kv-p ar)
		      (mkvp (ua-select (ar-kv-p-witness ar) ar))))
      :hints(("Goal" :in-theory '(ar-kv-p)))))

   (fi-thm booleanp-of-ar-kv-p
     (booleanp (ar-kv-p ar))
     booleanp-of-ar-p '(fi-ar-kv-p-1 fi-ar-kv-p-2 fi-ar-kv-p-3)))

  (fi-thm ar-kv-p-of-ar-kv-init
    (ar-kv-p (ar-kv-init))
    ar-p-of-ar-init '(ar-kv-init))

  (fi-thm ar-kv-p-of-ar-kv-store
    (ar-kv-p (ar-kv-store k kv ar))
    ar-p-of-ar-store '(ar-kv-store))

  (verify-guards ar-kv-store)

  (fi-thm ar-kv-p-of-ar-kv-from-al
    (ar-kv-p (ar-kv-from-al al))
    ar-p-of-ar-from-al '(ar-kv-from-al))

  (verify-guards ar-kv-from-al
    :hints(("Goal"
      :in-theory '(ar-kv-p-of-ar-kv-from-al kvap mkvp kvp))))

  (fi-thm mkvp-of-ar-kv-select
    (mkvp (ar-kv-select k ar))
    ar-maybe-key-val-consp-of-ar-select '(ar-kv-select))

  ;; init select and store behave like they should for arrays
  (fi-thm ar-kv-select-of-ar-kv-init
    (equal (ar-kv-select k (ar-kv-init)) nil)
    ar-select-of-ar-init)

  (fi-thm ar-kv-select-of-ar-kv-store
    (implies (and (ar-kv-p ar) (kp k0) (mkvp kv0))
	     (equal (ar-kv-select k1 (ar-kv-store k0 kv0 ar))
		    (if (equal k1 k0)
		      kv0
		      (ar-kv-select k1 ar))))
    ar-select-of-ar-store)


  ;; translation of alist operations to operations on arrays
  (encapsulate nil
    ;; See the comments with the proof of booleanp-of-ar-kv-p to see
    ;;   how I came up with these lemmas and why.
    (local (defthm fi-ar-kv-equiv-1
      (implies (ar-kv-equiv al ar)
	       (kvap al))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-2
      (implies (ar-kv-equiv al ar)
	       (equal (assoc-equal k al) (ar-kv-select k ar)))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-3
      (implies (ar-kv-equiv al ar)
	       (ar-kv-p ar))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-5
      (implies (and (kvap al)
		    (ar-kv-p ar)
		    (equal (assoc-equal (ar-kv-equiv-witness al ar) al)
			   (ar-kv-select (ar-kv-equiv-witness al ar) ar)))
	       (equal (ar-kv-equiv al ar) t))
      :hints(("Goal" :in-theory '(ar-kv-equiv)))))

    (fi-thm booleanp-of-ar-kv-equiv
      (booleanp (ar-kv-equiv al ar))
      booleanp-of-ar-equiv
      '(fi-ar-kv-equiv-1 fi-ar-kv-equiv-2 fi-ar-kv-equiv-3 fi-ar-kv-equiv-5)))

  (fi-thm ar-kv-translation-of-nil
    (ar-kv-equiv nil (ar-kv-init))
    ar-translation-of-nil)

  (fi-thm ar-kv-translation-of-acons
    (implies (and (ar-kv-equiv al ar)
		  (kp k)
		  (vp v))
	     (ar-kv-equiv (cons (cons k v) al) (ar-kv-store k (cons k v) ar)))
    ar-translation-of-acons)

  (fi-thm ar-kv-translation-of-alist
    (implies (kvap al) (ar-kv-equiv al (ar-kv-from-al al)))
    ar-translation-of-alist)

  (fi-thm ar-kv-translation-of-assoc-equal
    (implies (ar-kv-equiv al ar)
	     (equal (assoc-equal k al) (ar-kv-select k ar)))
    ar-translation-of-assoc-equal)

  (fi-thm ar-kv-top-down-translation-of-assoc-equal
          (implies (kvap al)
                   (equal (assoc-equal k al)
                          (ar-kv-select k
                                        (ar-kv-from-al al))))
          ar-top-down-translation-of-assoc-equal)

  (fi-thm ar-kv-top-down-translation-of-acons
          (implies (and (kp k)
                        (vp v))
                   (equal (ar-kv-from-al (cons (cons k v) al))
                          (ar-kv-store k (cons k v) (ar-kv-from-al al))))
          ar-top-down-translation-of-acons)

  (fi-thm ar-kv-top-down-translation-of-nil
          (equal (ar-kv-from-al nil)
                 (ar-kv-init))
          ar-top-down-translation-of-nil)
  ))


;; Having established the main results using kp and vp, I'll now restate
;; them with natp and symbolp to produce the theorems needed by Smtlink.

(local (defthm natp-equals-kp
  (equal (natp x) (kp x))
  :hints(("Goal" :in-theory '(kp natp)))))

(local (defthm symbolp-equals-vp
  (equal (symbolp x) (vp x))
  :hints(("Goal" :in-theory '(vp symbolp)))))

(define nat-sym-consp (x)
  (and (consp x)
       (natp (car x))
       (symbolp (cdr x))))

(local (defthm nat-sym-consp-equals-kvp
  (equal (nat-sym-consp x) (kvp x))
  :hints(("Goal"
    :in-theory '(natp-equals-kp symbolp-equals-vp)
    :expand((nat-sym-consp x) (kvp x))))))

(local (defthm booleanp-of-nat-sym-consp
  (booleanp (nat-sym-consp x))
  :hints(("Goal"
    :in-theory '(nat-sym-consp-equals-kvp booleanp-of-kvp)))))

(define maybe-nat-sym-consp (x)
  (implies x (nat-sym-consp x)))

(local (defthm maybe-nat-sym-consp-equals-mkvp
  (equal (maybe-nat-sym-consp x) (mkvp x))
  :hints(("Goal"
    :in-theory '(maybe-nat-sym-consp mkvp nat-sym-consp-equals-kvp)))))

(local (defthm booleanp-of-maybe-nat-sym-consp
  (booleanp (maybe-nat-sym-consp x))
  :hints(("Goal"
    :in-theory '(maybe-nat-sym-consp-equals-mkvp booleanp-of-mkvp)))))

(define nat-sym-alist-p (x)
  (or (not x)
      (and (consp x)
	   (consp (car x))
	   (natp (caar x))
	   (symbolp (cdar x))
	   (nat-sym-alist-p (cdr x)))))

(local (defthm nat-sym-alist-p-equals-kvap
  (equal (nat-sym-alist-p x) (kvap x))
  :hints(("Goal"
    :in-theory (enable nat-sym-alist-p kvap kvp)))))

(encapsulate
  (((nat-sym-array-p *) => *)
   ((nat-sym-array-init) => *)
   ((nat-sym-array-store * * *) => *)
   ((nat-sym-array-from-al *) => *)
   ((nat-sym-array-select * *) => *)
   ((nat-sym-array-equiv * *) => *))

  (local (defun nat-sym-array-p (ar) (ar-kv-p ar)))
  (local (defun nat-sym-array-init () (ar-kv-init)))
  (local (defun nat-sym-array-store (k kv ar) (ar-kv-store k kv ar)))
  (local (defun nat-sym-array-from-al (al) (ar-kv-from-al al)))
  (local (defun nat-sym-array-select (k ar) (ar-kv-select k ar)))
  (local (defun nat-sym-array-equiv (al ar) (ar-kv-equiv al ar)))

  ;; return type constraints
  (defthmd booleanp-of-nat-sym-array-p
    (booleanp (nat-sym-array-p ar))
    :hints(("Goal"
      :in-theory '(nat-sym-array-p)
      :use((:instance booleanp-of-ar-kv-p (ar ar))))))

  (defthmd nat-sym-array-p-of-nat-sym-array-init
    (nat-sym-array-p (nat-sym-array-init))
    :hints(("Goal"
      :in-theory '(nat-sym-array-init nat-sym-array-p ar-kv-p-of-ar-kv-init))))

  (defthmd nat-sym-array-p-of-nat-sym-array-store
    (nat-sym-array-p (nat-sym-array-store k kv ar))
    :hints(("Goal"
      :in-theory '(nat-sym-array-store nat-sym-array-p ar-kv-p-of-ar-kv-store))))

  (defthmd nat-sym-array-p-of-nat-sym-array-from-al
    (nat-sym-array-p (nat-sym-array-from-al al))
    :hints(("Goal"
      :in-theory '(nat-sym-array-from-al nat-sym-array-p ar-kv-p-of-ar-kv-from-al))))

  (defthmd maybe-nat-sym-cons-of-nat-sym-array-select
    (maybe-nat-sym-consp (nat-sym-array-select k ar))
    :hints(("Goal"
      :in-theory '(nat-sym-array-select maybe-nat-sym-consp-equals-mkvp mkvp-of-ar-kv-select))))

  (defthmd booleanp-of-nat-sym-array-equiv
    (booleanp (nat-sym-array-equiv al ar))
    :hints(("Goal"
      :in-theory '(nat-sym-array-equiv booleanp-of-ar-kv-equiv))))

  ;; array operation constraints
  (defthmd nat-sym-array-select-of-nat-sym-array-init
    (equal (nat-sym-array-select k (nat-sym-array-init)) nil)
    :hints(("Goal"
      :in-theory '(nat-sym-array-select nat-sym-array-init natp-equals-kp)
      :use((:instance ar-kv-select-of-ar-kv-init)))))

  (defthmd nat-sym-array-select-of-nat-sym-array-store
    (implies (and (nat-sym-array-p ar) (natp k0) (maybe-nat-sym-consp kv0))
	     (equal (nat-sym-array-select k1 (nat-sym-array-store k0 kv0 ar))
		    (if (equal k1 k0)
			kv0
			(nat-sym-array-select k1 ar))))
    :hints(("Goal"
      :in-theory '(nat-sym-array-select nat-sym-array-store nat-sym-array-p
		   natp-equals-kp maybe-nat-sym-consp-equals-mkvp)
      :use((:instance ar-kv-select-of-ar-kv-store)))))

  ;; translating alist values and operations to array versions
  (defthmd nat-sym-translation-of-nil
    (nat-sym-array-equiv nil (nat-sym-array-init))
    :hints(("Goal"
      :in-theory '(nat-sym-array-equiv nat-sym-array-init
                   ar-kv-translation-of-nil))))

  (defthmd nat-sym-translation-of-alist
    (implies (nat-sym-alist-p al)
	     (nat-sym-array-equiv al (nat-sym-array-from-al al)))
    :hints(("Goal" :in-theory '(
      nat-sym-alist-p-equals-kvap nat-sym-array-equiv nat-sym-array-from-al
      ar-kv-translation-of-alist))))

  (defthmd nat-sym-translation-of-acons
    (implies (and (nat-sym-array-equiv al ar)
		  (natp k)
		  (symbolp v))
	     (nat-sym-array-equiv (cons (cons k v) al)
				  (nat-sym-array-store k (cons k v) ar)))
    :hints(("Goal" :in-theory '(
      natp-equals-kp symbolp-equals-vp nat-sym-alist-p-equals-kvap
      nat-sym-array-p nat-sym-array-equiv nat-sym-array-store
      ar-kv-translation-of-acons))))

  (defthmd nat-sym-translation-of-assoc-equal
    (implies (nat-sym-array-equiv al ar)
	     (equal (assoc-equal k al) (nat-sym-array-select k ar)))
    :hints(("Goal" :in-theory '(
      nat-sym-consp-equals-kvp nat-sym-alist-p-equals-kvap natp-equals-kp
      nat-sym-array-p nat-sym-array-equiv nat-sym-array-select
                                ar-kv-translation-of-assoc-equal))))

  (defthmd nat-sym-top-down-translation-of-assoc-equal
    (implies (nat-sym-alist-p al)
             (equal (assoc-equal k al)
                    (nat-sym-array-select k
                                          (nat-sym-array-from-al
                                            al))))
    :hints (("Goal"
              :in-theory '(natp-equals-kp
                           symbolp-equals-vp
                           nat-sym-alist-p-equals-kvap
                           nat-sym-array-select
                           nat-sym-array-from-al
                           ar-kv-top-down-translation-of-assoc-equal))))

  (defthmd nat-sym-top-down-translation-of-acons
    (implies (and (natp k)
                  (symbolp v))
             (equal (nat-sym-array-from-al (cons (cons k v) al))
                    (nat-sym-array-store k
                                         (cons k v)
                                         (nat-sym-array-from-al al))))
    :hints (("Goal"
              :in-theory '(natp-equals-kp
                           symbolp-equals-vp
                           nat-sym-array-from-al
                           nat-sym-array-store
                           ar-kv-top-down-translation-of-acons))))

  (defthmd nat-sym-top-down-translation-of-nil
    (equal (nat-sym-array-from-al nil)
           (nat-sym-array-init))
    :hints (("Goal"
              :in-theory '(nat-sym-array-from-al
                           nat-sym-array-init
                           ar-kv-top-down-translation-of-nil)))))
