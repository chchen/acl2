(F)
(UBDDP-OF-F)
(TEST-Q-AND-MACRO-BASIC)
(TEST-Q-AND-MACRO-LAZY-2 (1496 13 (:DEFINITION Q-ITE-FN))
                         (982 13 (:DEFINITION QCONS$INLINE))
                         (295 84 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                         (210 39 (:DEFINITION HONS-EQUAL))
                         (184 184 (:TYPE-PRESCRIPTION BOOLEANP))
                         (150 27 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                         (114 84
                              (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                         (95 84
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                         (66 51 (:REWRITE |(q-ite non-nil y z)|))
                         (66 10
                             (:REWRITE |(qs-subset x (q-and x y))|))
                         (40 40 (:DEFINITION HONS))
                         (27 27 (:REWRITE DEFAULT-CDR))
                         (27 27 (:REWRITE DEFAULT-CAR))
                         (26 13 (:DEFINITION QCDR$INLINE))
                         (26 13 (:DEFINITION QCAR$INLINE))
                         (23 23 (:REWRITE QS-SUBSET-OF-Q-ITE-LEFT))
                         (14 2
                             (:REWRITE |(qs-subset y (q-and x y))|))
                         (12 12 (:REWRITE |(qs-subset x t)|))
                         (12 12 (:REWRITE |(q-ite t x y)|))
                         (11 1
                             (:REWRITE |(qs-subset y (q-ite x y nil))|))
                         (7 7
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                         (5 5
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                         (4 1 (:DEFINITION Q-NOT))
                         (2 2 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                         (2 2
                            (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                         (2 2
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-AND-MACRO-LAZY-3 (414 150 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                         (224 48
                              (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 4))
                         (216 18
                              (:REWRITE |(qs-subset x (q-and x y))|))
                         (192 192 (:TYPE-PRESCRIPTION BOOLEANP))
                         (150 150
                              (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                         (150 150
                              (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                         (48 48
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                         (44 6
                             (:REWRITE |(qs-subset y (q-and x y))|))
                         (30 30
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                         (18 18 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                         (18 18
                             (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                         (18 18
                             (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-OR-MACRO-BASIC)
(TEST-Q-OR-MACRO-LAZY-2 (1707 14 (:DEFINITION Q-ITE-FN))
                        (1024 14 (:DEFINITION QCONS$INLINE))
                        (347 84 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                        (281 42 (:DEFINITION HONS-EQUAL))
                        (194 194 (:TYPE-PRESCRIPTION BOOLEANP))
                        (181 30 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                        (136 84
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                        (84 84
                            (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                        (60 57 (:REWRITE |(q-ite non-nil y z)|))
                        (54 54 (:DEFINITION HONS))
                        (49 8 (:REWRITE |(qs-subset (q-or x y) x)|))
                        (48 12 (:DEFINITION Q-NOT))
                        (40 40 (:REWRITE DEFAULT-CDR))
                        (40 40 (:REWRITE DEFAULT-CAR))
                        (28 14 (:DEFINITION QCDR$INLINE))
                        (28 14 (:DEFINITION QCAR$INLINE))
                        (12 12 (:REWRITE |(q-ite t x y)|))
                        (7 1 (:REWRITE |(qs-subset (q-or x y) y)|))
                        (4 4
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (4 4
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 2))
                        (4 4
                           (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (1 1 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                        (1 1
                           (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                        (1 1
                           (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-OR-MACRO-LAZY-3 (403 103 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                        (156 156 (:TYPE-PRESCRIPTION BOOLEANP))
                        (103 103
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                        (103 103
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                        (61 61
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                        (49 49
                            (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                        (25 25 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                        (25 25
                            (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                        (25 25
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-IMPLIES-MACRO-LAZY-2
     (1617 16 (:DEFINITION QCONS$INLINE))
     (573 152 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
     (480 152
          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
     (286 286 (:TYPE-PRESCRIPTION BOOLEANP))
     (246 19
          (:REWRITE |(qs-subset (q-ite x nil y) nil)|))
     (193 152
          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
     (150 26 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (95 77 (:REWRITE |(q-ite non-nil y z)|))
     (58 58 (:DEFINITION HONS))
     (42 42 (:REWRITE DEFAULT-CDR))
     (42 42 (:REWRITE DEFAULT-CAR))
     (40 10 (:DEFINITION Q-NOT))
     (32 16 (:DEFINITION QCDR$INLINE))
     (32 16 (:DEFINITION QCAR$INLINE))
     (24 24 (:REWRITE |(q-ite t x y)|))
     (12 12
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
     (10 10
         (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
     (9 1
        (:REWRITE |(qs-subset y (q-ite x y nil))|))
     (4 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
     (4 4
        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
     (4 4
        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-OR-C2-MACRO-LAZY-2 (1617 16 (:DEFINITION QCONS$INLINE))
                           (573 152 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                           (480 152
                                (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                           (286 286 (:TYPE-PRESCRIPTION BOOLEANP))
                           (246 19
                                (:REWRITE |(qs-subset (q-ite x nil y) nil)|))
                           (193 152
                                (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                           (150 26 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                           (95 77 (:REWRITE |(q-ite non-nil y z)|))
                           (58 58 (:DEFINITION HONS))
                           (42 42 (:REWRITE DEFAULT-CDR))
                           (42 42 (:REWRITE DEFAULT-CAR))
                           (40 10 (:DEFINITION Q-NOT))
                           (32 16 (:DEFINITION QCDR$INLINE))
                           (32 16 (:DEFINITION QCAR$INLINE))
                           (24 24 (:REWRITE |(q-ite t x y)|))
                           (12 12
                               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                           (10 10
                               (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                           (9 1
                              (:REWRITE |(qs-subset y (q-ite x y nil))|))
                           (4 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                           (4 4
                              (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                           (4 4
                              (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-AND-C1-MACRO-LAZY-2 (2112 13 (:DEFINITION Q-ITE-FN))
                            (1333 13 (:DEFINITION QCONS$INLINE))
                            (566 125 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                            (319 39 (:DEFINITION HONS-EQUAL))
                            (252 252 (:TYPE-PRESCRIPTION BOOLEANP))
                            (165 125
                                 (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                            (143 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                            (134 57 (:REWRITE |(q-ite non-nil y z)|))
                            (129 125
                                 (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                            (73 17 (:DEFINITION Q-NOT))
                            (57 43 (:REWRITE DEFAULT-CDR))
                            (57 43 (:REWRITE DEFAULT-CAR))
                            (56 56 (:DEFINITION HONS))
                            (30 30 (:REWRITE QS-SUBSET-OF-Q-ITE-LEFT))
                            (30 30 (:REWRITE CONSP-OF-Q-NOT))
                            (26 13 (:DEFINITION QCDR$INLINE))
                            (26 13 (:DEFINITION QCAR$INLINE))
                            (18 18 (:REWRITE |(qs-subset x t)|))
                            (18 18 (:REWRITE |(q-ite t x y)|))
                            (12 12
                                (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                            (11 11
                                (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                            (5 5 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                            (5 5
                               (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                            (5 5
                               (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-AND-C2-MACRO-LAZY-2 (1877 13 (:DEFINITION Q-ITE-FN))
                            (1217 13 (:DEFINITION QCONS$INLINE))
                            (487 125 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                            (274 39 (:DEFINITION HONS-EQUAL))
                            (236 236 (:TYPE-PRESCRIPTION BOOLEANP))
                            (165 125
                                 (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                            (143 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                            (129 125
                                 (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                            (72 57 (:REWRITE |(q-ite non-nil y z)|))
                            (51 51 (:DEFINITION HONS))
                            (48 12 (:DEFINITION Q-NOT))
                            (38 38 (:REWRITE DEFAULT-CDR))
                            (38 38 (:REWRITE DEFAULT-CAR))
                            (30 30 (:REWRITE QS-SUBSET-OF-Q-ITE-LEFT))
                            (26 13 (:DEFINITION QCDR$INLINE))
                            (26 13 (:DEFINITION QCAR$INLINE))
                            (18 18 (:REWRITE |(qs-subset x t)|))
                            (18 18 (:REWRITE |(q-ite t x y)|))
                            (12 12
                                (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                            (10 10
                                (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                            (4 4 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                            (4 4
                               (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                            (4 4
                               (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-IFF-MACRO-LAZY-2 (183 62 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                         (70 70 (:TYPE-PRESCRIPTION BOOLEANP))
                         (62 62
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                         (62 62
                             (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                         (26 26
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                         (19 19
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                         (7 7 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                         (7 7
                            (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                         (7 7
                            (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-IFF-MACRO-LAZY-3 (930 388 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                         (388 388
                              (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                         (388 388
                              (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                         (326 326 (:TYPE-PRESCRIPTION BOOLEANP))
                         (120 120
                              (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                         (90 90
                             (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                         (36 36 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                         (36 36
                             (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                         (36 36
                             (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP)))
(TEST-Q-XOR-MACRO-2 (4334 42 (:DEFINITION QCONS$INLINE))
                    (2292 457
                          (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 2))
                    (1789 457 (:REWRITE QS-SUBSET-WHEN-BOOLEANS))
                    (1192 3
                          (:REWRITE |(q-ite (q-ite a b c) x y)|))
                    (815 815 (:TYPE-PRESCRIPTION BOOLEANP))
                    (650 457
                         (:REWRITE TRANSITIVITY-OF-QS-SUBSET . 1))
                    (609 40
                         (:REWRITE |(qs-subset (q-ite x nil y) nil)|))
                    (462 66 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                    (292 226 (:REWRITE |(q-ite non-nil y z)|))
                    (228 57 (:DEFINITION Q-NOT))
                    (183 183 (:DEFINITION HONS))
                    (142 142 (:REWRITE DEFAULT-CDR))
                    (142 142 (:REWRITE DEFAULT-CAR))
                    (94 43 (:DEFINITION QCDR$INLINE))
                    (94 43 (:DEFINITION QCAR$INLINE))
                    (62 62 (:REWRITE |(q-ite t x y)|))
                    (50 3
                        (:REWRITE |(qs-subset (q-ite x nil y) x)|))
                    (45 2
                        (:REWRITE |(qs-subset y (q-ite x y nil))|))
                    (31 31
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 3))
                    (27 27
                        (:REWRITE EVAL-BDD-WHEN-QS-SUBSET . 1))
                    (21 1
                        (:REWRITE |(qs-subset x (q-ite x y nil))|))
                    (14 14
                        (:REWRITE EVAL-BDD-WHEN-NON-CONSP-VALUES))
                    (11 11 (:REWRITE EVAL-BDD-WHEN-NOT-CONSP))
                    (11 11
                        (:REWRITE EVAL-BDD-OF-NON-CONSP-CHEAP))
                    (3 3 (:REWRITE |(q-ite nil x y)|))
                    (1 1
                       (:REWRITE |(qs-subset (q-ite x y nil) y)|))
                    (1 1
                       (:REWRITE |(qs-subset (q-ite x y nil) x)|)))
(TEST-Q-XOR-MACRO-3 (32 32 (:TYPE-PRESCRIPTION Q-BINARY-XOR)))