(BV-ARRAYP-LIST)
(2D-BV-ARRAYP)
(LEN-OF-NTH-WHEN-BV-ARRAYP-LIST
     (102 6 (:DEFINITION TRUE-LISTP))
     (96 6
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (41 41 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (41 41 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (36 20 (:REWRITE DEFAULT-<-2))
     (21 15 (:REWRITE DEFAULT-CAR))
     (20 20 (:REWRITE DEFAULT-<-1))
     (20 14 (:REWRITE DEFAULT-CDR))
     (19 19
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (19 19
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (12 12 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (12 12 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (6 6
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (5 5 (:REWRITE ZP-OPEN))
     (5 5
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (5 5
        (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN)))
(LEN-OF-NTH-WHEN-2D-BV-ARRAYP
     (9 1 (:DEFINITION NTH))
     (5 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (5 1 (:DEFINITION TRUE-LISTP))
     (4 2 (:REWRITE DEFAULT-CDR))
     (3 3
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(TRUE-LISTP-OF-NTH-WHEN-BV-ARRAYP-LIST
     (144 9 (:DEFINITION TRUE-LISTP))
     (96 6
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (40 23 (:REWRITE DEFAULT-<-2))
     (36 36 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (36 36 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (23 23 (:REWRITE DEFAULT-<-1))
     (21 16 (:REWRITE DEFAULT-CDR))
     (21 15 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (18 18
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (18 18
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (15 15 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 6
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (6 6
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (5 5 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (3 3
        (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (3 3
        (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
     (1 1
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (1 1
        (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN)))
(TRUE-LISTP-OF-NTH-WHEN-2D-BV-ARRAYP
     (9 1 (:DEFINITION NTH))
     (5 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (5 1 (:DEFINITION TRUE-LISTP))
     (4 2 (:REWRITE DEFAULT-CDR))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(LEN-WHEN-2D-BV-ARRAYP)
(TRUE-LISTP-WHEN-2D-BV-ARRAYP)
(BV-ARRAYP-OF-NTH
     (307 15
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (133 7 (:DEFINITION TRUE-LISTP))
     (85 23 (:REWRITE DEFAULT-CAR))
     (81 81 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (81 20 (:REWRITE DEFAULT-CDR))
     (73 73 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (73 73 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (54 33 (:REWRITE DEFAULT-<-2))
     (33 33 (:REWRITE DEFAULT-<-1))
     (23 15
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (21 21 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (17 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
     (15 15
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (15 15
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (15 1 (:LINEAR LEN-OF-CDR-LINEAR))
     (14 14 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (10 10 (:REWRITE ZP-OPEN))
     (7 7
        (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (6 6
        (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (2 2
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (2 2
        (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
     (1 1
        (:REWRITE TRUE-LISTP-OF-NTH-WHEN-2D-BV-ARRAYP)))
(ALL-UNSIGNED-BYTE-P-OF-NTH2
     (48 2 (:DEFINITION NTH))
     (43 7 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (34 1
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (14 2 (:REWRITE DEFAULT-CDR))
     (14 2 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (7 7 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (1 1
        (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (1 1
        (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
     (1 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (1 1
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(ALL-UNSIGNED-BYTE-P-OF-NTH3
     (30 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (24 1 (:DEFINITION NTH))
     (16 1 (:DEFINITION TRUE-LISTP))
     (14 2 (:REWRITE DEFAULT-CDR))
     (7 1 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (6 6 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(UNSIGNED-BYTE-P-OF-ARRAY-ELEM-2D
     (33 2 (:DEFINITION NTH))
     (21 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (9 2 (:REWRITE DEFAULT-CDR))
     (9 2 (:REWRITE DEFAULT-CAR))
     (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (6 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1)))
(NATP-OF-ARRAY-ELEM-2D (10 7 (:REWRITE DEFAULT-<-2))
                       (7 7 (:REWRITE DEFAULT-<-1))
                       (3 3
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
                       (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P)))
(BV-ARRAYP-LIST-OF-CONS
     (152 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (89 5 (:DEFINITION TRUE-LISTP))
     (76 5
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (24 12 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (17 17 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (12 12
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (10 10
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 6
        (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (6 6
        (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 5
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (5 5
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER)))
(2D-BV-ARRAYP-OF-CONS
     (144 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (56 4
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (24 12 (:REWRITE DEFAULT-<-2))
     (23 23 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (23 23 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (22 22 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (18 18 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (18 18
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (12 12
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (12 6 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (4 4
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BV-ARRAYP-LIST-OF-APPEND
     (1379 100 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (692 35
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (513 27 (:DEFINITION TRUE-LISTP))
     (203 104 (:REWRITE DEFAULT-<-2))
     (168 141 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (142 142 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (141 141 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (132 99
          (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (104 104 (:REWRITE DEFAULT-<-1))
     (100 100
          (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (100 100
          (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (100 100 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (94 94 (:REWRITE DEFAULT-CAR))
     (72 36
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (66 66 (:REWRITE DEFAULT-CDR))
     (54 54 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (54 54
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (51 35
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (36 36 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (35 35
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (12 4 (:DEFINITION NATP))
     (9 1 (:REWRITE LEN-OF-CDR))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN)))
(BV-ARRAYP-LIST-OF-REVERSE
     (2273 16 (:DEFINITION BINARY-APPEND))
     (1882 105 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (693 33 (:REWRITE TAKE-DOES-NOTHING))
     (660 30 (:DEFINITION NTH))
     (655 7 (:REWRITE NTH-OF-TAKE-GEN2))
     (558 558 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (519 22
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (406 383 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (360 360 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (348 88 (:REWRITE DEFAULT-CAR))
     (325 16 (:DEFINITION TRUE-LISTP))
     (324 10 (:REWRITE CDR-OF-TAKE))
     (293 247 (:REWRITE DEFAULT-+-2))
     (277 206 (:REWRITE DEFAULT-<-2))
     (247 247 (:REWRITE DEFAULT-+-1))
     (228 47 (:REWRITE ZP-OPEN))
     (218 23 (:REWRITE LEN-OF-REVERSE-LIST))
     (210 206 (:REWRITE DEFAULT-<-1))
     (198 7 (:REWRITE TAKE-OF-TAKE-WHEN-<=))
     (172 17 (:REWRITE CONSP-OF-TAKE))
     (127 61
          (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (124 74 (:REWRITE DEFAULT-CDR))
     (97 97 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (92 21 (:REWRITE LEN-OF-TAKE))
     (71 21 (:DEFINITION NFIX))
     (39 39
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (39 39
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (35 9 (:DEFINITION NATP))
     (32 32 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (32 32
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (30 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (27 27
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (25 7 (:REWRITE BV-ARRAYP-OF-NTH))
     (23 23
         (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
     (22 22 (:REWRITE EQUAL-OF-LEN-AND-0))
     (22 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (21 21
         (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (21 21
         (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (21 21
         (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (21 21
         (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
     (20 10 (:REWRITE CAR-OF-TAKE-STRONG))
     (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (14 14
         (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
     (7 7
        (:REWRITE TRUE-LISTP-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (7 7
        (:REWRITE TRUE-LISTP-OF-NTH-WHEN-2D-BV-ARRAYP))
     (7 7
        (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTH3))
     (7 7
        (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTH2))
     (2 2 (:TYPE-PRESCRIPTION NATP)))
(BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS
     (12 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (5 5 (:TYPE-PRESCRIPTION LEN))
     (2 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (1 1 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(BV-ARRAYP-OF-COLS-TO-ROW
     (866 63 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (503 17
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (360 17 (:DEFINITION NTH))
     (149 149 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (124 79 (:REWRITE DEFAULT-<-2))
     (106 106 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (103 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
     (90 3 (:DEFINITION MEMBER-EQUAL))
     (79 79 (:REWRITE DEFAULT-<-1))
     (57 57 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (57 45 (:REWRITE DEFAULT-CDR))
     (48 47 (:REWRITE DEFAULT-+-2))
     (48 42 (:REWRITE DEFAULT-CAR))
     (47 47 (:REWRITE DEFAULT-+-1))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (21 17
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (17 17 (:REWRITE ZP-OPEN))
     (17 17
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (16 1 (:DEFINITION TRUE-LISTP))
     (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (13 13
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (10 10
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (1 1 (:TYPE-PRESCRIPTION NATP)))
(BV-ARRAYP-LIST-OF-COLS-TO-ROW-AUX
     (196 14 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (85 5 (:DEFINITION TRUE-LISTP))
     (66 14
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (61 61 (:TYPE-PRESCRIPTION LEN))
     (37 29 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (29 29 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (29 29 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (26 21 (:REWRITE DEFAULT-<-2))
     (24 21 (:REWRITE DEFAULT-<-1))
     (21 21
         (:TYPE-PRESCRIPTION COLS-TO-ARRAY-AUX))
     (16 8 (:REWRITE LEN-OF-COLS-TO-ARRAY-AUX))
     (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (10 10
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1)))
(BV-ARRAYP-LIST-OF-COLS-TO-ARRAY
     (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (17 1 (:DEFINITION TRUE-LISTP))
     (13 1
         (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (9 9 (:TYPE-PRESCRIPTION LEN))
     (6 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (4 4 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER)))
(2D-BV-ARRAYP-OF-COLS-TO-ARRAY
     (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (17 1 (:DEFINITION TRUE-LISTP))
     (13 1
         (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (6 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (6 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (5 5 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (4 4 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (3 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (2 2 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER)))
(BV-ARRAYP-LIST-OF-REPEAT
     (308 22
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (192 160 (:REWRITE DEFAULT-<-2))
     (170 10 (:DEFINITION TRUE-LISTP))
     (160 160 (:REWRITE DEFAULT-<-1))
     (106 79 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (79 79 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (62 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (52 52 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (47 47 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (34 34
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (30 10 (:DEFINITION NATP))
     (25 25 (:REWRITE DEFAULT-+-2))
     (25 25 (:REWRITE DEFAULT-+-1))
     (22 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (20 20 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (10 10 (:TYPE-PRESCRIPTION NATP))
     (10 10 (:REWRITE DEFAULT-CDR)))
(BV-ARRAYP-LIST-OF-TAKE
     (2001 180 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (1526 61 (:REWRITE TAKE-DOES-NOTHING))
     (432 432 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (341 19
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (340 225 (:REWRITE DEFAULT-<-2))
     (323 17 (:DEFINITION TRUE-LISTP))
     (320 320 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (243 155 (:REWRITE DEFAULT-+-2))
     (236 225 (:REWRITE DEFAULT-<-1))
     (170 170 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (163 78
          (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (155 155 (:REWRITE DEFAULT-+-1))
     (55 55
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (55 55
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (38 38
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (34 34 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (34 34
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (30 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (24 24
         (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
     (22 22
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (6 2 (:DEFINITION NATP))
     (2 2 (:TYPE-PRESCRIPTION NATP)))
(BV-ARRAYP-LIST-OF-NTHCDR
     (1011 82 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (276 10
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (237 7 (:DEFINITION NTH))
     (217 25 (:REWRITE DEFAULT-CDR))
     (214 8 (:REWRITE LEN-OF-NTHCDR))
     (182 9 (:DEFINITION TRUE-LISTP))
     (152 152 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (132 93 (:REWRITE DEFAULT-<-2))
     (118 118 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (118 118 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (95 93 (:REWRITE DEFAULT-<-1))
     (94 48
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (85 63 (:REWRITE DEFAULT-+-2))
     (82 21 (:REWRITE DEFAULT-CAR))
     (63 63 (:REWRITE DEFAULT-+-1))
     (52 52 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (36 4 (:REWRITE COMMUTATIVITY-2-OF-+))
     (33 11 (:REWRITE COMMUTATIVITY-OF-+))
     (28 4
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (21 12 (:REWRITE ZP-OPEN))
     (21 9
         (:REWRITE LEN-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (20 20
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (20 20
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (18 18 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (18 18
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (17 3
         (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTH2))
     (15 5 (:DEFINITION NATP))
     (14 10
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (13 11 (:REWRITE FOLD-CONSTS-IN-+))
     (12 4 (:DEFINITION POSP))
     (11 3
         (:REWRITE TRUE-LISTP-OF-NTH-WHEN-BV-ARRAYP-LIST))
     (10 10
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (9 9 (:TYPE-PRESCRIPTION NATP))
     (9 9 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (9 9
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (9 9
        (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (9 9
        (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 6
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (6 6
        (:REWRITE CONSP-NTH-FROM-ITEMS-HAVE-LEN))
     (4 4 (:TYPE-PRESCRIPTION POSP))
     (3 3
        (:REWRITE TRUE-LISTP-OF-NTH-WHEN-2D-BV-ARRAYP))
     (3 3
        (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTH3))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(BV-ARRAYP-LIST-OF-SUBRANGE
     (44 2 (:REWRITE TAKE-DOES-NOTHING))
     (15 11 (:REWRITE DEFAULT-<-1))
     (12 11 (:REWRITE DEFAULT-<-2))
     (11 9 (:REWRITE DEFAULT-+-2))
     (11 9 (:REWRITE DEFAULT-+-1))
     (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (7 1
        (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (6 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (5 5 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 1 (:DEFINITION POSP))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(2D-BV-ARRAYP-OF-SUBRANGE
     (25 2 (:REWRITE TAKE-DOES-NOTHING))
     (15 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (11 11 (:REWRITE DEFAULT-+-2))
     (11 11 (:REWRITE DEFAULT-+-1))
     (9 9 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (6 1 (:DEFINITION TRUE-LISTP))
     (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (3 1 (:DEFINITION POSP))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (2 1 (:REWRITE DEFAULT-CDR))
     (2 1
        (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(BV-ARRAYP-OF-GET-COLUMN
     (866 63 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (503 17
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (360 17 (:DEFINITION NTH))
     (149 149 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (124 79 (:REWRITE DEFAULT-<-2))
     (106 106 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (103 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
     (90 3 (:DEFINITION MEMBER-EQUAL))
     (79 79 (:REWRITE DEFAULT-<-1))
     (57 57 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (57 45 (:REWRITE DEFAULT-CDR))
     (48 47 (:REWRITE DEFAULT-+-2))
     (48 42 (:REWRITE DEFAULT-CAR))
     (47 47 (:REWRITE DEFAULT-+-1))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (22 22
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (21 17
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (17 17 (:REWRITE ZP-OPEN))
     (17 17
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (16 1 (:DEFINITION TRUE-LISTP))
     (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (13 13
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (10 10
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
     (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (1 1 (:TYPE-PRESCRIPTION NATP)))
(2D-BV-ARRAYP-OF-GET-COLUMNS (25 5 (:DEFINITION TRUE-LISTP))
                             (15 15 (:REWRITE CONSP-WHEN-LEN-GREATER))
                             (10 10 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
                             (10 10
                                 (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
                             (9 9 (:REWRITE DEFAULT-<-2))
                             (9 9 (:REWRITE DEFAULT-<-1))
                             (8 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                             (7 7 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
                             (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
                             (5 5 (:REWRITE DEFAULT-CDR))
                             (5 5 (:REWRITE DEFAULT-+-2))
                             (5 5 (:REWRITE DEFAULT-+-1)))
(2D-BV-ARRAYP-OF-GET-COLUMNS-SPECIAL-CASE (5 5 (:REWRITE DEFAULT-+-2))
                                          (5 5 (:REWRITE DEFAULT-+-1))
                                          (1 1 (:REWRITE DEFAULT-<-2))
                                          (1 1 (:REWRITE DEFAULT-<-1)))
(BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP)
(2D-ARRAY-HEIGHT-WHEN-2D-BV-ARRAYP
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(2D-ARRAY-WIDTH-WHEN-2D-BV-ARRAYP
     (68 13 (:DEFINITION TRUE-LISTP))
     (49 49 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (49 49 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (49 49 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (30 19 (:REWRITE DEFAULT-<-2))
     (28 20 (:REWRITE DEFAULT-CDR))
     (26 26 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (26 26
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (22 19 (:REWRITE DEFAULT-<-1))
     (22 14
         (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (21 13 (:REWRITE DEFAULT-CAR))
     (19 19
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (19 19
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (14 14
         (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
     (14 7 (:DEFINITION NTH))
     (7 7
        (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
     (7 7
        (:REWRITE LEN-OF-NTH-WHEN-2D-BV-ARRAYP))
     (7 7
        (:REWRITE LEN-NTH-FROM-ITEMS-HAVE-LEN))
     (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ALL-UNSIGNED-BYTE-P-OF-GET-COLUMN
     (1242 92 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (686 20
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (471 23 (:DEFINITION NTH))
     (270 29 (:REWRITE LEN-OF-CDR))
     (180 110 (:REWRITE DEFAULT-<-2))
     (173 173 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (158 144 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (135 14 (:REWRITE LEN-OF-GET-COLUMN))
     (129 129 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (110 110 (:REWRITE DEFAULT-<-1))
     (109 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
     (96 3 (:DEFINITION MEMBER-EQUAL))
     (83 83 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (74 72 (:REWRITE DEFAULT-CDR))
     (57 53 (:REWRITE DEFAULT-+-2))
     (55 54 (:REWRITE DEFAULT-CAR))
     (53 53 (:REWRITE DEFAULT-+-1))
     (28 28
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (28 28
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (25 25 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (25 25
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (25 21
         (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (23 23 (:REWRITE ZP-OPEN))
     (21 21
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (19 19
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (18 18
         (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
     (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (12 12
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (7 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
     (3 3 (:REWRITE EQUAL-OF-LEN-AND-0))
     (1 1 (:TYPE-PRESCRIPTION NATP)))
(TRUE-LIST-LISTP-WHEN-BV-ARRAYP-LIST
     (363 26 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (85 5
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (53 26
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (48 24 (:REWRITE DEFAULT-<-2))
     (41 41 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (39 39 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (39 39 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (24 24 (:REWRITE DEFAULT-<-1))
     (24 24 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (24 2 (:REWRITE LEN-OF-CDR))
     (20 20 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (20 20
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (16 16
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (16 16
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (16 16 (:REWRITE DEFAULT-CAR))
     (13 13 (:REWRITE DEFAULT-CDR))
     (8 8
        (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
     (5 5
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (5 5
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN)))
(ITEMS-HAVE-LEN-WHEN-BV-ARRAYP-LIST
     (692 47 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (205 11 (:DEFINITION TRUE-LISTP))
     (174 19 (:REWRITE LEN-OF-CDR))
     (136 8
          (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (111 111 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (92 92 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (88 88 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (82 37
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (71 40 (:REWRITE DEFAULT-<-2))
     (43 43 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (40 40 (:REWRITE DEFAULT-<-1))
     (37 37
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (33 33
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (28 28 (:REWRITE DEFAULT-CAR))
     (26 26 (:REWRITE DEFAULT-CDR))
     (23 19 (:REWRITE DEFAULT-+-2))
     (22 22 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (22 22
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (22 6 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
     (19 19 (:REWRITE DEFAULT-+-1))
     (16 16
         (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (14 14
         (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
     (9 3 (:REWRITE FOLD-CONSTS-IN-+))
     (8 8
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (8 8
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
     (3 3
        (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN)))
(2D-ARRAYP-WHEN-2D-BV-ARRAYP
     (355 20 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (154 6
          (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
     (93 8 (:REWRITE LEN-OF-CDR))
     (69 4
         (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
     (47 47 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
     (47 18
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (39 39 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (39 39 (:REWRITE LEN-WHEN-BV-ARRAYP))
     (37 18 (:REWRITE DEFAULT-<-2))
     (31 2
         (:REWRITE ITEMS-HAVE-LEN-WHEN-NOT-CONSP))
     (19 19 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (18 18 (:REWRITE DEFAULT-<-1))
     (16 8 (:REWRITE DEFAULT-+-2))
     (15 15 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
     (14 14
         (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
     (14 14
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
     (14 14
         (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
     (12 12 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE DEFAULT-+-1))
     (7 7 (:REWRITE EQUAL-OF-LEN-AND-0))
     (7 7
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (6 6
        (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
     (5 1 (:REWRITE ITEMS-HAVE-LEN-OF-CDR))
     (4 4
        (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
     (4 4
        (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
     (4 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN)))
(2D-BV-ARRAYP-OF-NTHCDR (154 14 (:REWRITE CONSP-FROM-LEN-CHEAP))
                        (112 7 (:DEFINITION TRUE-LISTP))
                        (91 7
                            (:REWRITE BV-ARRAYP-LIST-WHEN-LST-IS-NOT-A-CONS))
                        (52 35 (:REWRITE DEFAULT-<-2))
                        (51 35 (:REWRITE DEFAULT-<-1))
                        (40 26 (:REWRITE DEFAULT-+-1))
                        (38 26 (:REWRITE DEFAULT-+-2))
                        (36 36 (:REWRITE LEN-WHEN-2D-BV-ARRAYP))
                        (35 35 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                        (35 35 (:REWRITE LEN-WHEN-BV-ARRAYP))
                        (14 14 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
                        (14 14
                            (:REWRITE TRUE-LISTP-WHEN-2D-BV-ARRAYP))
                        (14 14 (:REWRITE CONSP-WHEN-LEN-GREATER))
                        (8 8
                           (:REWRITE BV-ARRAYP-LIST-WHEN-2D-BV-ARRAYP))
                        (7 7 (:REWRITE DEFAULT-CDR))
                        (7 7
                           (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                        (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                        (5 5
                           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                        (3 1 (:DEFINITION POSP))
                        (1 1 (:TYPE-PRESCRIPTION POSP))
                        (1 1
                           (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                        (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN)))