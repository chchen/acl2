; Top file for terms-light library
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-quotep")
(include-book "trivial-formals")
(include-book "non-trivial-formals")
(include-book "non-trivial-formals-and-args")
(include-book "bound-vars-in-term")
(include-book "let-vars-in-term")
(include-book "free-vars-in-term")
(include-book "sublis-var-simple")
(include-book "sublis-var-simple-proofs")
(include-book "subst-var-alt")
(include-book "subst-var-alt-proofs")
(include-book "sublis-var-and-magic-eval")
(include-book "expr-calls-fn")
(include-book "unary-lambdap")
(include-book "wrap-pattern-around-term")
(include-book "lambda-free-termp")
(include-book "lambdas-closed-in-termp")
(include-book "all-lambdas-serialized-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "expand-lambdas-in-term")
(include-book "expand-lambdas-in-term-proof")
(include-book "add-param-to-calls-in-term")
(include-book "rename-vars-in-term")
(include-book "count-ifs-in-term")
(include-book "count-ifs-in-then-and-else-branches")
(include-book "combine-ifs-in-then-and-else-branches")
(include-book "restore-mv-in-branches")
(include-book "logic-termp")
(include-book "negate-term")
(include-book "negate-term-proof")
(include-book "negate-terms")
(include-book "drop-clearly-implied-conjuncts")
(include-book "term-is-conjunctionp")
(include-book "clearly-implies-for-disjunctionp")
(include-book "make-if-term")
(include-book "make-if-term-proof")
(include-book "strengthen-conjuncts")
(include-book "reconstruct-lets-in-term")
(include-book "serialize-lambdas-in-term")
(include-book "serialize-lambdas-in-term-proofs")
(include-book "let-bind-formals-in-calls")
(include-book "restore-mv-lets-in-term")
(include-book "substitute-unnecessary-lambda-vars")
(include-book "make-lambda-term-simple")
(include-book "make-lambda-terms-simple")
(include-book "make-lambda-application-simple")
(include-book "make-lambda-application-simple-proof")
(include-book "function-call-subterms")
(include-book "replace-term-with-term")
(include-book "count-occurrences-in-term")
(include-book "no-nils-in-termp")
(include-book "all-fnnames1")
(include-book "get-conjuncts")
(include-book "get-hyps-and-conc")
(include-book "replace-corresponding-arg")
