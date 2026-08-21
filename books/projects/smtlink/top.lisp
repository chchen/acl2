;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "config")

;; verified
(include-book "verified/computed-hints")
(include-book "verified/process")
(include-book "verified/add-hypo-cp")
(include-book "verified/expand-cp")
(include-book "verified/reorder-hypotheses")
(include-book "verified/term-rewrite")
;; (include-book "verified/type-inference-bottomup")
;; (include-book "verified/type-inference-topdown")
(include-book "verified/ttmrg-triv-cp")
(include-book "verified/ti-bottom-up3")
(include-book "verified/ti-top-down")
;; (include-book "verified/term-replacement")
(include-book "verified/term-rewrite")
(include-book "verified/tterm-type-extract")
(include-book "verified/hint-generation")
;; (include-book "verified/type-extract")
;;(include-book "verified/alist/alist-macro")
;;(include-book "verified/alist/define-nonexist")

;; trusted
;; (include-book "trusted/prove")
;; (include-book "trusted/run")
;; (include-book "trusted/trusted-cp")
;; (include-book "trusted/write")
(include-book "trusted/smt-lib")

;; trusted/z3-py
;; (include-book "trusted/z3-py/header")
;; (include-book "trusted/z3-py/names")
;; (include-book "trusted/z3-py/translate")
