(APPLY-FOR-DEFEVALUATOR)
(NOT-EVAL)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(NOT-EVAL-OF-FNCALL-ARGS)
(NOT-EVAL-OF-VARIABLE)
(NOT-EVAL-OF-QUOTE)
(NOT-EVAL-OF-LAMBDA)
(NOT-EVAL-LIST-OF-ATOM)
(NOT-EVAL-LIST-OF-CONS)
(NOT-EVAL-OF-NONSYMBOL-ATOM)
(NOT-EVAL-OF-BAD-FNCALL)
(NOT-EVAL-OF-NOT-CALL)
(NOT-EVAL-OF-LAMBDA-BETTER
 (19 13 (:REWRITE NOT-EVAL-OF-NOT-CALL))
 (10 10 (:REWRITE NOT-EVAL-OF-QUOTE))
 (8 8 (:REWRITE NOT-EVAL-LIST-OF-CONS))
 (8 8 (:REWRITE NOT-EVAL-LIST-OF-ATOM))
 )
(NOT-EVAL-LIST-OF-APPEND
 (256 128 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (128 128 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (128 128 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (13 10 (:REWRITE DEFAULT-CAR))
 (12 9 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE NOT-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE NOT-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE NOT-EVAL-OF-QUOTE))
 (2 2 (:REWRITE NOT-EVAL-OF-NOT-CALL))
 )
(LEN-OF-NOT-EVAL-LIST
 (14 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE NOT-EVAL-OF-LAMBDA-BETTER))
 (1 1 (:REWRITE NOT-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE NOT-EVAL-OF-QUOTE))
 (1 1 (:REWRITE NOT-EVAL-OF-NOT-CALL))
 )
(NOT-EVAL-LIST-OF-TRUE-LIST_FIX
 (7 6 (:REWRITE DEFAULT-CAR))
 (6 5 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE NOT-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE NOT-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE NOT-EVAL-OF-QUOTE))
 (2 2 (:REWRITE NOT-EVAL-OF-NOT-CALL))
 )
(NOT-EVAL-OF-FNCALL-ARGS-BACK)
