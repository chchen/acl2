(INTERPRETED-FUNCTION-INFOP)
(ALL-INTERPRETED-FUNCTION-INFOP)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-CONS)
(USE-ALL-INTERPRETED-FUNCTION-INFOP-FOR-CAR)
(USE-ALL-INTERPRETED-FUNCTION-INFOP-FOR-CAR-OF-LAST)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-APPEND)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-UNION-EQUAL)
(ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP)
(ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-REVAPPEND)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-CDR)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-NTHCDR)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-FIRSTN)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-REMOVE1-EQUAL)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-REMOVE-EQUAL)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-LAST)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-TAKE)
(ALL-INTERPRETED-FUNCTION-INFOP-WHEN-PERM)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-TRUE-LIST-FIX)
(PERM-IMPLIES-EQUAL-ALL-INTERPRETED-FUNCTION-INFOP-1)
(USE-ALL-INTERPRETED-FUNCTION-INFOP)
(USE-ALL-INTERPRETED-FUNCTION-INFOP-2)
(ALL-INTERPRETED-FUNCTION-INFOP-OF-ADD-TO-SET-EQUAL)
(INTERPRETED-FUNCTION-ALISTP)
(INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-ALISTP)
(INTERPRETED-FUNCTION-ALISTP-FORWARD-TO-SYMBOL-ALISTP)
(INTERPRETED-FUNCTION-ALISTP-OF-ACONS
     (190 2 (:DEFINITION PSEUDO-TERMP))
     (58 50 (:REWRITE DEFAULT-CDR))
     (54 10 (:DEFINITION LEN))
     (54 6 (:DEFINITION LENGTH))
     (48 24
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (46 46
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (44 4 (:DEFINITION SYMBOL-LISTP))
     (42 42 (:REWRITE DEFAULT-CAR))
     (42 2 (:DEFINITION SYMBOL-ALISTP))
     (32 16
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (24 4 (:DEFINITION STRIP-CDRS))
     (22 3
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (20 10 (:REWRITE DEFAULT-+-2))
     (16 8
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (16 6 (:DEFINITION TRUE-LISTP))
     (12 6
         (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (12 2 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (10 10 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (10 10 (:REWRITE DEFAULT-+-1))
     (6 3
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 2
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (4 2
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (2 2
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (2 2 (:TYPE-PRESCRIPTION MEMBERP))
     (2 2
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (2 2
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (2 2 (:REWRITE DEFAULT-COERCE-2))
     (2 2 (:REWRITE DEFAULT-COERCE-1)))
(INTERPRETED-FUNCTION-INFOP-OF-CDR-OF-ASSOC-EQUAL
     (212 106
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (131 131
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (67 43 (:REWRITE DEFAULT-CAR))
     (48 11
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (44 22
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (42 22 (:REWRITE DEFAULT-CDR))
     (36 36 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (22 11
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (19 9
         (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (10 10 (:TYPE-PRESCRIPTION MEMBERP))
     (9 9
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (6 3
        (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP)))
(INTERPRETED-FUNCTION-INFOP-OF-LOOKUP-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (29 1
         (:DEFINITION ALL-INTERPRETED-FUNCTION-INFOP))
     (22 2 (:DEFINITION ASSOC-EQUAL))
     (21 1 (:DEFINITION SYMBOL-ALISTP))
     (20 4
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (19 13 (:REWRITE DEFAULT-CDR))
     (18 3 (:DEFINITION STRIP-CDRS))
     (17 13 (:REWRITE DEFAULT-CAR))
     (15 15
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (12 6
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (12 6
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (6 6 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (6 3
        (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (6 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-FOR-CAR))
     (6 1 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (6 1
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-OF-CDR))
     (5 4
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (2 1
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP)))
(TRUE-LISTP-OF-CADR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (95 1 (:DEFINITION PSEUDO-TERMP))
     (44 36 (:REWRITE DEFAULT-CDR))
     (44 36 (:REWRITE DEFAULT-CAR))
     (40 40
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (40 20
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (30 15
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (27 5 (:DEFINITION LEN))
     (27 3 (:DEFINITION LENGTH))
     (24 4 (:DEFINITION STRIP-CDRS))
     (22 2 (:DEFINITION SYMBOL-LISTP))
     (21 1 (:DEFINITION SYMBOL-ALISTP))
     (20 2
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (12 4 (:DEFINITION TRUE-LISTP))
     (10 5 (:REWRITE DEFAULT-+-2))
     (8 8 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (8 4
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (6 3
        (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (6 1 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (5 5 (:REWRITE DEFAULT-+-1))
     (4 2
        (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (4 2
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (3 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (2 2 (:TYPE-PRESCRIPTION MEMBERP))
     (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (2 2
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (2 1
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (1 1
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (1 1 (:REWRITE DEFAULT-COERCE-2))
     (1 1 (:REWRITE DEFAULT-COERCE-1)))
(SYMBOL-LISTP-OF-CADR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (14 10 (:REWRITE DEFAULT-CDR))
     (14 10 (:REWRITE DEFAULT-CAR))
     (12 12
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (12 6
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (12 2 (:DEFINITION STRIP-CDRS))
     (10 5
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (10 1
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (5 1 (:DEFINITION LEN))
     (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (3 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (2 2 (:TYPE-PRESCRIPTION MEMBERP))
     (2 1
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (2 1
        (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (2 1 (:REWRITE DEFAULT-+-2))
     (2 1
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (2 1 (:DEFINITION TRUE-LISTP))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(PSEUDO-TERMP-OF-CADDR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (53 39 (:REWRITE DEFAULT-CAR))
     (48 24
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (45 41 (:REWRITE DEFAULT-CDR))
     (39 39
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (28 14
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (22 2 (:DEFINITION SYMBOL-LISTP))
     (14 7 (:REWRITE DEFAULT-+-2))
     (12 2 (:DEFINITION STRIP-CDRS))
     (10 1
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 3
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (4 4 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (3 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (2 2 (:TYPE-PRESCRIPTION MEMBERP))
     (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (2 2
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (2 1
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (2 1
        (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (2 1
        (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (1 1 (:REWRITE DEFAULT-COERCE-2))
     (1 1 (:REWRITE DEFAULT-COERCE-1)))
(ADD-TO-INTERPRETED-FUNCTION-ALIST
     (249 3 (:DEFINITION PSEUDO-TERMP))
     (81 9 (:DEFINITION LENGTH))
     (66 12 (:DEFINITION LEN))
     (58 58 (:REWRITE DEFAULT-CDR))
     (54 54 (:REWRITE DEFAULT-CAR))
     (41 41
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (36 4 (:DEFINITION SYMBOL-LISTP))
     (32 16
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (32 16
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (27 27 (:TYPE-PRESCRIPTION LEN))
     (24 12 (:REWRITE DEFAULT-+-2))
     (21 1 (:DEFINITION SYMBOL-ALISTP))
     (20 10
         (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
     (18 6 (:DEFINITION TRUE-LISTP))
     (18 1 (:DEFINITION PLIST-WORLDP))
     (12 12 (:REWRITE DEFAULT-+-1))
     (10 10
         (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
     (10 5
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (9 3
        (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
     (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (6 3
        (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (6 3
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (6 1 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (3 3
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (3 3
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (3 3
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (3 3
        (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
     (3 3
        (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
     (3 3 (:REWRITE DEFAULT-COERCE-2))
     (3 3 (:REWRITE DEFAULT-COERCE-1)))
(INTERPRETED-FUNCTION-ALISTP-OF-ADD-TO-INTERPRETED-FUNCTION-ALIST
     (166 2 (:DEFINITION PSEUDO-TERMP))
     (54 6 (:DEFINITION LENGTH))
     (38 38 (:REWRITE DEFAULT-CDR))
     (31 31 (:REWRITE DEFAULT-CAR))
     (19 19 (:TYPE-PRESCRIPTION LEN))
     (18 18
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (18 9 (:REWRITE DEFAULT-+-2))
     (16 8
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (12 6
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (12 4 (:DEFINITION TRUE-LISTP))
     (10 10
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
     (10 10
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
     (9 9 (:REWRITE DEFAULT-+-1))
     (6 2
        (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 2
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (4 2
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (2 2
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (2 2 (:REWRITE DEFAULT-COERCE-2))
     (2 2 (:REWRITE DEFAULT-COERCE-1))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP)))
(ADD-FNS-TO-INTERPRETED-FUNCTION-ALIST
     (166 2 (:DEFINITION PSEUDO-TERMP))
     (117 117 (:REWRITE DEFAULT-CAR))
     (88 88
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (76 38
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (71 71 (:REWRITE DEFAULT-CDR))
     (54 6 (:DEFINITION LENGTH))
     (48 24
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (44 22
         (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (44 8 (:DEFINITION LEN))
     (18 18 (:TYPE-PRESCRIPTION LEN))
     (16 8 (:REWRITE DEFAULT-+-2))
     (12 4 (:DEFINITION TRUE-LISTP))
     (9 9
        (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
     (9 9
        (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
     (8 8 (:REWRITE DEFAULT-+-1))
     (6 6
        (:TYPE-PRESCRIPTION ADD-TO-INTERPRETED-FUNCTION-ALIST))
     (6 2
        (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
     (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 2
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (2 2
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (2 2 (:TYPE-PRESCRIPTION ACONS))
     (2 2
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (2 2
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (2 2 (:REWRITE DEFAULT-COERCE-2))
     (2 2 (:REWRITE DEFAULT-COERCE-1)))
(INTERPRETED-FUNCTION-ALISTP-OF-ADD-FNS-TO-INTERPRETED-FUNCTION-ALIST
     (332 4 (:DEFINITION PSEUDO-TERMP))
     (108 12 (:DEFINITION LENGTH))
     (88 88 (:REWRITE DEFAULT-CAR))
     (76 76 (:REWRITE DEFAULT-CDR))
     (37 37 (:TYPE-PRESCRIPTION LEN))
     (36 36
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (34 17 (:REWRITE DEFAULT-+-2))
     (32 16
         (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (24 12
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (24 8 (:DEFINITION TRUE-LISTP))
     (17 17 (:REWRITE DEFAULT-+-1))
     (16 16
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
     (16 16
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
     (12 4
         (:REWRITE PSEUDO-TERMP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TERM-ALISTP))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (8 4
        (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (8 4
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (4 4
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (4 4
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (4 4
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (1 1
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP)))
(MAKE-INTERPRETED-FUNCTION-ALIST)
(INTERPRETED-FUNCTION-ALISTP-OF-MAKE-INTERPRETED-FUNCTION-ALIST)
(CONSP-OF-CDR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (490 245
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (380 4 (:DEFINITION PSEUDO-TERMP))
     (308 308
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (156 142 (:REWRITE DEFAULT-CAR))
     (119 111 (:REWRITE DEFAULT-CDR))
     (108 20 (:DEFINITION LEN))
     (108 12 (:DEFINITION LENGTH))
     (88 8 (:DEFINITION SYMBOL-LISTP))
     (82 41
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (67 8 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (48 11
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (44 22
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (40 20 (:REWRITE DEFAULT-+-2))
     (38 19
         (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (36 36 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (22 11
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (20 20 (:REWRITE DEFAULT-+-1))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (8 8
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (8 4
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (6 3
        (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (4 4
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (4 4
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1)))
(CDDR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (510 255
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (380 4 (:DEFINITION PSEUDO-TERMP))
     (329 329
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (177 157 (:REWRITE DEFAULT-CAR))
     (141 129 (:REWRITE DEFAULT-CDR))
     (108 12 (:DEFINITION LENGTH))
     (94 47
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (88 8 (:DEFINITION SYMBOL-LISTP))
     (73 9 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (58 12
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (46 23
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (44 22
         (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (40 40 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (40 20 (:REWRITE DEFAULT-+-2))
     (24 12
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (20 20 (:REWRITE DEFAULT-+-1))
     (10 5
         (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (8 8
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (8 4
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (4 4
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (4 4
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1)))
(CONSP-OF-CDDR-OF-ASSOC-EQUAL-WHEN-INTERPRETED-FUNCTION-ALISTP
     (510 255
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (380 4 (:DEFINITION PSEUDO-TERMP))
     (329 329
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (180 160 (:REWRITE DEFAULT-CAR))
     (145 133 (:REWRITE DEFAULT-CDR))
     (108 12 (:DEFINITION LENGTH))
     (94 47
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (88 8 (:DEFINITION SYMBOL-LISTP))
     (73 9 (:REWRITE SYMBOL-ALISTP-OF-CDR))
     (58 12
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (46 23
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (44 22
         (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (40 40 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (40 20 (:REWRITE DEFAULT-+-2))
     (24 12
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (20 20 (:REWRITE DEFAULT-+-1))
     (10 5
         (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (8 8
        (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (8 4
        (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (4 4
        (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (4 4
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (4 4
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1)))
(CONSP-OF-CAR-WHEN-INTERPRETED-FUNCTION-ALISTP
     (2 1
        (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (1 1
        (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (1 1 (:REWRITE DEFAULT-CAR)))
(INTERPRETED-FUNCTION-COMPLETEP-AUX
     (447 339 (:REWRITE DEFAULT-CDR))
     (284 282 (:REWRITE DEFAULT-CAR))
     (269 269
          (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
     (212 106
          (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (188 94
          (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
     (170 24
          (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP))
     (138 69
          (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (86 43 (:REWRITE DEFAULT-+-2))
     (78 78 (:TYPE-PRESCRIPTION STRIP-CDRS))
     (70 35
         (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
     (48 24
         (:REWRITE ALL-INTERPRETED-FUNCTION-INFOP-WHEN-NOT-CONSP-CHEAP))
     (43 43 (:REWRITE DEFAULT-+-1))
     (35 5 (:DEFINITION SUBSETP-EQUAL))
     (18 6 (:DEFINITION MEMBER-EQUAL))
     (14 14
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (14 7
         (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP))
     (11 11
         (:REWRITE PSEUDO-TERMP-OF-LAMBDA-BODY-CHEAP))
     (9 9
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP-2))
     (9 9
        (:REWRITE USE-ALL-INTERPRETED-FUNCTION-INFOP))
     (9 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
     (7 7
        (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (7 7 (:REWRITE DEFAULT-COERCE-2))
     (7 7 (:REWRITE DEFAULT-COERCE-1))
     (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL)))
(INTERPRETED-FUNCTION-COMPLETEP
     (142 88 (:REWRITE DEFAULT-CAR))
     (98 70 (:REWRITE DEFAULT-CDR))
     (78 13 (:DEFINITION STRIP-CARS))
     (26 13
         (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
     (13 13
         (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP)))