(ALL-<=
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(ALL-<=-OF-CONS)
(USE-ALL-<=-FOR-CAR)
(USE-ALL-<=-FOR-CAR-OF-LAST)
(ALL-<=-OF-APPEND)
(ALL-<=-OF-UNION-EQUAL)
(ALL-<=-WHEN-NOT-CONSP)
(ALL-<=-WHEN-NOT-CONSP-CHEAP)
(ALL-<=-OF-REVAPPEND)
(ALL-<=-OF-CDR)
(ALL-<=-OF-NTHCDR)
(ALL-<=-OF-FIRSTN)
(ALL-<=-OF-REMOVE1-EQUAL)
(ALL-<=-OF-REMOVE-EQUAL)
(ALL-<=-OF-LAST)
(ALL-<=-OF-TAKE)
(ALL-<=-WHEN-PERM)
(ALL-<=-OF-TRUE-LIST-FIX)
(PERM-IMPLIES-EQUAL-ALL-<=-1)
(USE-ALL-<=)
(USE-ALL-<=-2)
(ALL-<=-OF-ADD-TO-SET-EQUAL)
(ALL-<=-MONOTONE
 (35 19 (:REWRITE DEFAULT-<-2))
 (35 19 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (29 25 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 (26 20 (:REWRITE USE-ALL-<=))
 (25 25 (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
 (24 4 (:REWRITE ALL-<=-OF-CDR))
 (20 20 (:REWRITE USE-ALL-<=-2))
 (17 17 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 )
(<=-OF-NTH-WHEN-ALL-<=
 (41 23 (:REWRITE USE-ALL-<=))
 (23 23 (:REWRITE USE-ALL-<=-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (18 18 (:TYPE-PRESCRIPTION MEMBERP))
 (18 16 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 (17 17 (:REWRITE ALL-<=-MONOTONE))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 2 (:REWRITE ALL-<=-OF-CDR))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(<=-OF-NTH-WHEN-ALL-<=-FREE
 (99 12 (:REWRITE USE-ALL-<=-FOR-CAR))
 (34 27 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE USE-ALL-<=-2))
 (28 28 (:REWRITE USE-ALL-<=))
 (25 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 18 (:REWRITE ALL-<=-MONOTONE))
 (18 16 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 2 (:REWRITE ALL-<=-OF-CDR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(NOT-ALL-<=-WHEN-<-AND-MEMBER-EQUAL
 (15 5 (:REWRITE USE-ALL-<=))
 (10 10 (:TYPE-PRESCRIPTION MEMBERP))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE USE-ALL-<=-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE ALL-<=-MONOTONE))
 (2 2 (:REWRITE ALL-<=-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 )
(ALL-<=-OF-REVAPPEND-STRONG
 (5654 534 (:REWRITE ALL-<=-WHEN-NOT-CONSP))
 (2664 72 (:DEFINITION BUTLAST))
 (2372 154 (:DEFINITION TAKE))
 (2246 2246 (:TYPE-PRESCRIPTION LEN))
 (1342 254 (:DEFINITION LEN))
 (1199 502 (:REWRITE DEFAULT-<-2))
 (1140 154 (:REWRITE ZP-OPEN))
 (1099 1099 (:REWRITE DEFAULT-CDR))
 (1096 770 (:REWRITE DEFAULT-+-2))
 (966 504 (:REWRITE USE-ALL-<=))
 (908 130 (:REWRITE ALL-<=-OF-CDR))
 (770 770 (:REWRITE DEFAULT-+-1))
 (688 502 (:REWRITE DEFAULT-<-1))
 (633 162 (:REWRITE CONSP-OF-REVAPPEND))
 (622 622 (:TYPE-PRESCRIPTION LAST))
 (531 531 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (525 375 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (504 504 (:REWRITE USE-ALL-<=-2))
 (502 430 (:REWRITE DEFAULT-CAR))
 (462 462 (:TYPE-PRESCRIPTION MEMBERP))
 (426 118 (:REWRITE FOLD-CONSTS-IN-+))
 (407 407 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (342 72 (:REWRITE COMMUTATIVITY-OF-+))
 (306 90 (:DEFINITION LAST))
 (238 10 (:DEFINITION BINARY-APPEND))
 (103 14 (:REWRITE USE-ALL-<=-FOR-CAR-OF-LAST))
 (91 14 (:REWRITE ALL-<=-OF-LAST))
 (72 18 (:REWRITE REVAPPEND-IFF))
 (70 34 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (68 12 (:REWRITE APPEND-TO-NIL))
 (54 18 (:REWRITE UNICITY-OF-0))
 (40 8 (:DEFINITION TRUE-LISTP))
 (36 18 (:DEFINITION FIX))
 (34 34 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (10 6 (:REWRITE PERM-OF-APPEND-WHEN-NOT-CONSP))
 )
