(EVMAC-PROCESS-INPUT-HINTS
 (10 1 (:DEFINITION STRIP-CARS))
 (9 6 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 )
(EVMAC-INPUT-HINTS-P-OF-EVMAC-PROCESS-INPUT-HINTS.HINTS$
 (50 5 (:DEFINITION STRIP-CARS))
 (30 2 (:DEFINITION KEYWORD-VALUE-LISTP))
 (27 2 (:DEFINITION TRUE-LISTP))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (24 1 (:REWRITE EVMAC-INPUT-HINTS-P-WHEN-TRUE-LISTP))
 (22 12 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (17 17 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (13 13 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION KEYWORD-VALUE-LIST-TO-ALIST))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 1 (:REWRITE EVMAC-INPUT-HINTS-P-WHEN-KEYWORD-TRUELIST-ALISTP))
 (6 6 (:REWRITE RETURN-TYPE-OF-ENSURE-LIST-HAS-NO-DUPLICATES.ERP))
 (6 2 (:DEFINITION KEYWORDP))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE TRUE-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP))
 (4 4 (:REWRITE KEYWORDP-OF-CAR-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP))
 (4 4 (:REWRITE SET::IN-SET))
 (3 1 (:REWRITE KEYWORD-TRUELIST-ALISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION KEYWORD-TRUELIST-ALISTP))
 (2 2 (:REWRITE KEYWORD-TRUELIST-ALISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(EVMAC-PROCESS-INPUT-PRINT)
(EVMAC-INPUT-PRINT-P-OF-EVMAC-PROCESS-INPUT-PRINT.PRINT$)
(EVMAC-PROCESS-INPUT-SHOW-ONLY)
(BOOLEANP-OF-EVMAC-PROCESS-INPUT-SHOW-ONLY.SHOW-ONLY$)
