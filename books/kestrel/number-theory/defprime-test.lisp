; A small test of defprime
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "defprime")
(include-book "std/testing/must-be-redundant" :dir :system)

(defprime my97-prime ;; name to use for the prime
  97 ;; numeric value of the prime
  ;; Pratt certificate:
  (5 (2 3)
     (5 1)
     (() ()))
  )

;; Stuff generated by defprime:
(acl2::must-be-redundant

 ;; the constant:
 (defconst *my97-prime* 97)

 ;; the 0-ary function:
 (defund my97-prime () (declare (xargs :guard t)) *my97-prime*)

 (defmacro eviscerate-my97-prime ()
   `(table acl2::evisc-table 97 "#.*MY97-PRIME*"))

 (defmacro uneviscerate-my97-prime ()
   `(table acl2::evisc-table 97 nil))

 ;; causes 97 to be printed as #.*my97-prime*:
 (eviscerate-my97-prime)

 ;; the pratt certificate:
 (defconst *my97-prime-pratt-cert*
   '(5 (2 3) (5 1) (nil nil)))

 ;; proof of primality:
 (defthm primep-of-my97-prime-constant
   (rtl::primep *my97-prime*))

 ;; lift primality proof to the 0-ary function:
 (defthm primep-of-my97-prime
   (rtl::primep (my97-prime)))

 ;; strong linear rule about the 0-ary function:
 (defthm my97-prime-linear
   (= (my97-prime) *my97-prime*)
   :rule-classes :linear))