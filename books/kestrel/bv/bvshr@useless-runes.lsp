(BVSHR)
(INTEGERP-OF-BVSHR)
(NATP-OF-BVSHR)
(BVSHR-OF-0-ARG1)
(BVSHR-OF-0-ARG2)
(BVSHR-OF-0-ARG3
     (108 4 (:DEFINITION EXPT))
     (36 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
     (32 8 (:REWRITE COMMUTATIVITY-OF-+))
     (26 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
     (24 8 (:REWRITE DEFAULT-*-2))
     (20 10 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (20 4 (:DEFINITION NATP))
     (18 18 (:REWRITE DEFAULT-+-2))
     (18 18 (:REWRITE DEFAULT-+-1))
     (16 6
         (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
     (16 6 (:REWRITE BVCHOP-IDENTITY))
     (15 13 (:REWRITE DEFAULT-<-2))
     (14 14 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (14 6
         (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
     (14 6
         (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
     (13 13 (:REWRITE DEFAULT-<-1))
     (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (10 10 (:TYPE-PRESCRIPTION NATP))
     (10 4 (:REWRITE ZIP-OPEN))
     (8 8 (:REWRITE DEFAULT-*-1))
     (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
     (8 6
        (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
     (8 4 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 6
        (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
     (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
     (2 2
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE)))
(UNSIGNED-BYTE-P-OF-BVSHR
     (4 2 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
     (3 1 (:REWRITE SLICE-TOO-HIGH-IS-0))
     (3 1 (:REWRITE SLICE-OUT-OF-ORDER))
     (2 2 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
     (1 1 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
     (1 1 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
     (1 1 (:REWRITE SLICE-TOO-HIGH-LEMMA))
     (1 1
        (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
     (1 1 (:REWRITE SLICE-SUBST-IN-CONSTANT))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(BVCHOP-OF-BVSHR (30 15 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
                 (28 28 (:REWRITE DEFAULT-+-2))
                 (28 28 (:REWRITE DEFAULT-+-1))
                 (27 27 (:REWRITE DEFAULT-<-2))
                 (27 27 (:REWRITE DEFAULT-<-1))
                 (27 9
                     (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
                 (27 9 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
                 (27 9 (:REWRITE SLICE-TOO-HIGH-IS-0))
                 (27 9 (:REWRITE SLICE-OUT-OF-ORDER))
                 (22 1 (:DEFINITION EXPT))
                 (19 19 (:TYPE-PRESCRIPTION POWER-OF-2P))
                 (9 9
                    (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
                 (9 9 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
                 (9 9 (:REWRITE SLICE-TOO-HIGH-LEMMA))
                 (9 9
                    (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
                 (9 9 (:REWRITE SLICE-SUBST-IN-CONSTANT))
                 (8 4 (:REWRITE NATP-WHEN-POWER-OF-2P))
                 (6 2 (:REWRITE DEFAULT-*-2))
                 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
                 (2 2 (:REWRITE DEFAULT-*-1))
                 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
                 (1 1 (:REWRITE ZIP-OPEN))
                 (1 1 (:LINEAR SLICE-UPPER-BOUND-LINEAR)))
(BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT)