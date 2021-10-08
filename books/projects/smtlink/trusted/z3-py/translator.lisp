;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "pretty-printer")

; Matt K. addition: definition from before November 2022 of pseudo-termp, to
; fix a proof failure occurring after changing that definition.
(local
 #!acl2
 (defthm pseudo-termp-def
     (equal (pseudo-termp x)
            (cond ((atom x) (symbolp x))
                  ((eq (car x) 'quote)
                   (and (consp (cdr x))
                        (null (cdr (cdr x)))))
                  ((not (true-listp x)) nil)
                  ((not (pseudo-term-listp (cdr x))) nil)
                  (t (or (symbolp (car x))

; For most function applications we do not check that the number of
; arguments matches the number of formals.  However, for lambda
; applications we do make that check.  The reason is that the
; constraint on an evaluator dealing with lambda applications must use
; pairlis$ to pair the formals with the actuals and pairlis$ insists on
; the checks below.

                         (and (true-listp (car x))
                              (equal (length (car x)) 3)
                              (eq (car (car x)) 'lambda)
                              (symbol-listp (cadr (car x)))
                              (pseudo-termp (caddr (car x)))
                              (equal (length (cadr (car x)))
                                     (length (cdr x))))))))
   :rule-classes ((:definition :controller-alist ((pseudo-termp t))))))

;; (defsection SMT-translator
;;   :parents (z3-py)
;;   :short "SMT-translator does the LISP to Python translation."

(define SMT-translation ((term pseudo-termp)
                         (smtlink-hint smtlink-hint-p)
                         state)
  ;; :returns (mv (py-term paragraphp)
  ;;              (smt-precond pseudo-termp)
  ;;              (uninterpreted-precond pseudo-term-list-listp))
  :mode :program
  :ignore-ok t
  (b* ((term (pseudo-term-fix term))
       (- (cw "SMT-translation: ~q0" term))
       (smtlink-hint (smtlink-hint-fix smtlink-hint)))
    (mv nil nil)))
;;  )
