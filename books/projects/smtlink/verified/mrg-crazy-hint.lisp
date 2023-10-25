;; Copyright (C) 2023, University of British Columbia
;; Written by Mark Greenstreet (May 26th 2023)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

;; ToDo: Store a list of cp's that should end with a by-nil hint
(define by-nil-hint ((cp symbolp))
  :returns (by-nil booleanp)
  (b* ((r (equal cp 'type-judge-bottomup))
       (- (cw "Clause processor ~p0: r = ~p1~%" cp r)))
      r))
