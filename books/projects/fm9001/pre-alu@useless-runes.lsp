(FM9001::DECODE-MODE)
(FM9001::F$DECODE-MODE)
(FM9001::DECODE-MODE-OKP)
(FM9001::DECODE-MODE&)
(FM9001::DECODE-MODE$VALUE (29 8 (:REWRITE FM9001::F-GATES=B-GATES))
                           (25 25 (:REWRITE DEFAULT-CAR))
                           (19 19 (:REWRITE DEFAULT-CDR))
                           (15 3 (:DEFINITION FM9001::DELETE-TO-EQ))
                           (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
                           (12 4
                               (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
                           (9 9 (:TYPE-PRESCRIPTION FM9001::F-NOR3))
                           (8 8
                              (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
                           (3 1
                              (:REWRITE FM9001::ASSOC-EQ-VALUE-CONS-2)))
(FM9001::F$DECODE-MODE=DECODE-MODE)
(FM9001::DECODE-MODE$VALUE-ZERO)
(FM9001::DECODE-PROP)
(FM9001::F$DECODE-PROP)
(FM9001::DECODE-PROP-OKP)
(FM9001::DECODE-PROP&)
(FM9001::DECODE-PROP$VALUE (1342 1126 (:REWRITE FM9001::F-GATES=B-GATES))
                           (141 141 (:REWRITE DEFAULT-CAR))
                           (130 26 (:DEFINITION FM9001::DELETE-TO-EQ))
                           (117 117 (:REWRITE DEFAULT-CDR))
                           (108 108 (:TYPE-PRESCRIPTION BOOLEANP))
                           (12 4
                               (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
                           (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
                           (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
                           (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND))
                           (8 8
                              (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP)))
(FM9001::F$DECODE-PROP=DECODE-PROP)
(FM9001::DECODE-PROP$VALUE-ZERO)
(FM9001::DECODE-GEN)
(FM9001::F$DECODE-GEN)
(FM9001::DECODE-GEN-OKP)
(FM9001::DECODE-GEN&)
(FM9001::DECODE-GEN$VALUE (1984 1768 (:REWRITE FM9001::F-GATES=B-GATES))
                          (160 160 (:REWRITE DEFAULT-CAR))
                          (145 29 (:DEFINITION FM9001::DELETE-TO-EQ))
                          (136 136 (:REWRITE DEFAULT-CDR))
                          (108 108 (:TYPE-PRESCRIPTION BOOLEANP))
                          (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
                          (12 4
                              (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
                          (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
                          (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND))
                          (8 8
                             (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP)))
(FM9001::F$DECODE-GEN=DECODE-GEN)
(FM9001::DECODE-GEN$VALUE-ZERO)
(FM9001::F$MPG)
(FM9001::MPG)
(FM9001::F$MPG=MPG (4124 294 (:REWRITE FM9001::BVP-CVZBV))
                   (3605 111
                         (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
                   (3180 54 (:DEFINITION TRUE-LISTP))
                   (1927 1831 (:REWRITE DEFAULT-CDR))
                   (475 419 (:REWRITE DEFAULT-CAR))
                   (448 48 (:DEFINITION BINARY-APPEND))
                   (280 96 (:REWRITE APPEND-WHEN-NOT-CONSP)))
(FM9001::LEN-F$MPG (529 325 (:REWRITE FM9001::F-GATES=B-GATES))
                   (526 526 (:REWRITE DEFAULT-CDR))
                   (159 159 (:REWRITE DEFAULT-CAR))
                   (104 104 (:TYPE-PRESCRIPTION BOOLEANP))
                   (66 66 (:TYPE-PRESCRIPTION FM9001::F-NOT))
                   (23 1 (:REWRITE FM9001::F$MPG=MPG))
                   (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
                   (16 1 (:REWRITE FM9001::BVP-CVZBV))
                   (12 12 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
                   (12 12 (:TYPE-PRESCRIPTION FM9001::F-NAND))
                   (12 6 (:REWRITE DEFAULT-+-2))
                   (11 7
                       (:REWRITE FM9001::F$DECODE-MODE=DECODE-MODE))
                   (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
                   (9 1 (:DEFINITION TRUE-LISTP))
                   (8 4
                      (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
                   (8 2 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
                   (6 6 (:REWRITE DEFAULT-+-1))
                   (4 4 (:TYPE-PRESCRIPTION FM9001::BVP))
                   (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                   (3 1
                      (:REWRITE FM9001::F$DECODE-PROP=DECODE-PROP))
                   (3 1
                      (:REWRITE FM9001::F$DECODE-GEN=DECODE-GEN))
                   (2 2
                      (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS)))
(FM9001::BVP-MPG (104 2 (:DEFINITION BINARY-APPEND))
                 (95 95 (:TYPE-PRESCRIPTION FM9001::B-NOT))
                 (68 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
                 (34 2 (:REWRITE FM9001::BVP-CVZBV))
                 (34 1 (:REWRITE FM9001::BVP-APPEND))
                 (33 17 (:REWRITE DEFAULT-CDR))
                 (30 30 (:TYPE-PRESCRIPTION FM9001::B-NOR))
                 (24 8 (:REWRITE DEFAULT-CAR))
                 (19 19 (:TYPE-PRESCRIPTION FM9001::B-NAND3))
                 (19 2
                     (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                 (8 8 (:TYPE-PRESCRIPTION FM9001::B-AND))
                 (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(FM9001::LEN-MPG (116 2 (:DEFINITION BINARY-APPEND))
                 (100 100 (:TYPE-PRESCRIPTION FM9001::B-NOT))
                 (68 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
                 (52 20 (:REWRITE DEFAULT-CDR))
                 (29 29 (:TYPE-PRESCRIPTION FM9001::B-NOR))
                 (24 8 (:REWRITE DEFAULT-CAR))
                 (24 4
                     (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                 (20 20 (:TYPE-PRESCRIPTION FM9001::B-NAND3))
                 (18 2
                     (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                 (14 7 (:REWRITE DEFAULT-+-2))
                 (11 11 (:TYPE-PRESCRIPTION FM9001::B-AND))
                 (10 7 (:REWRITE DEFAULT-+-1))
                 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                 (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
                 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                 (2 2
                    (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS)))
(FM9001::MPG-IF-OP-CODE)
(FM9001::MPG-ZERO)
(FM9001::MPG-OKP)
(FM9001::MPG&)
(FM9001::MPG$VALUE (794 473 (:REWRITE FM9001::F-GATES=B-GATES))
                   (727 727 (:REWRITE DEFAULT-CDR))
                   (263 263 (:REWRITE DEFAULT-CAR))
                   (162 162 (:TYPE-PRESCRIPTION BOOLEANP))
                   (99 99 (:TYPE-PRESCRIPTION FM9001::F-NOT))
                   (35 7 (:DEFINITION FM9001::DELETE-TO-EQ))
                   (27 27 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
                   (23 1 (:REWRITE FM9001::F$MPG=MPG))
                   (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND4))
                   (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND))
                   (16 1 (:REWRITE FM9001::BVP-CVZBV))
                   (12 4
                       (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
                   (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
                   (9 9 (:TYPE-PRESCRIPTION FM9001::F-NOR3))
                   (9 1 (:DEFINITION TRUE-LISTP))
                   (8 8
                      (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
                   (8 4
                      (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
                   (8 2 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
                   (6 2
                      (:REWRITE FM9001::F$DECODE-PROP=DECODE-PROP))
                   (6 2
                      (:REWRITE FM9001::F$DECODE-MODE=DECODE-MODE))
                   (6 2
                      (:REWRITE FM9001::F$DECODE-GEN=DECODE-GEN))
                   (4 4 (:TYPE-PRESCRIPTION FM9001::BVP)))
(FM9001::MPG$VALUE-ZERO)
(FM9001::CARRY-IN-HELP)
(FM9001::F$CARRY-IN-HELP)
(FM9001::F$CARRY-IN-HELP=CARRY-IN-HELP
     (106410 8268 (:REWRITE FM9001::BVP-CVZBV))
     (93478 2820
            (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (84406 1382 (:DEFINITION TRUE-LISTP))
     (32013 32013 (:REWRITE DEFAULT-CDR))
     (5717 5717 (:REWRITE DEFAULT-CAR))
     (1571 323 (:REWRITE FM9001::F-GATES=B-GATES))
     (417 417 (:TYPE-PRESCRIPTION FM9001::F-NOT))
     (270 270
          (:TYPE-PRESCRIPTION FM9001::F-NAND3))
     (3 3 (:TYPE-PRESCRIPTION FM9001::F-NAND)))
(FM9001::CARRY-IN-HELP-OKP)
(FM9001::CARRY-IN-HELP-ZERO (4 4 (:REWRITE DEFAULT-CDR))
                            (1 1 (:REWRITE DEFAULT-CAR)))
(FM9001::CARRY-IN-HELP-IF-OP-CODE)
(FM9001::CARRY-IN-HELP&)
(FM9001::CARRY-IN-HELP$VALUE
     (1253 1253 (:REWRITE DEFAULT-CDR))
     (600 440 (:REWRITE FM9001::F-GATES=B-GATES))
     (514 514 (:REWRITE DEFAULT-CAR))
     (201 161
          (:REWRITE FM9001::F-BUF-OF-NOT-BOOLEANP))
     (201 161 (:REWRITE FM9001::F-BUF-OF-3VP))
     (128 128 (:TYPE-PRESCRIPTION BOOLEANP))
     (75 15 (:DEFINITION FM9001::DELETE-TO-EQ))
     (40 40 (:TYPE-PRESCRIPTION FM9001::3VP))
     (27 27 (:TYPE-PRESCRIPTION FM9001::F-NOT))
     (23 1
         (:REWRITE FM9001::F$CARRY-IN-HELP=CARRY-IN-HELP))
     (18 18 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
     (18 18 (:TYPE-PRESCRIPTION FM9001::F-BUF))
     (16 1 (:REWRITE FM9001::BVP-CVZBV))
     (12 4
         (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
     (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (9 9 (:TYPE-PRESCRIPTION FM9001::F-NAND))
     (9 1 (:DEFINITION TRUE-LISTP))
     (8 8
        (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
     (8 4
        (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
     (8 2 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION FM9001::BVP)))
(FM9001::CARRY-IN-HELP$VALUE-ZERO
     (39 7 (:REWRITE FM9001::F-GATES=B-GATES))
     (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
     (12 12 (:TYPE-PRESCRIPTION FM9001::F-NOT))
     (10 1
         (:REWRITE FM9001::F$CARRY-IN-HELP=CARRY-IN-HELP))
     (6 6 (:TYPE-PRESCRIPTION FM9001::F-NAND3))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2
        (:TYPE-PRESCRIPTION FM9001::BVP-CVZBV))
     (3 1 (:REWRITE FM9001::BVP-CVZBV))
     (2 2 (:TYPE-PRESCRIPTION FM9001::BVP))
     (1 1 (:REWRITE DEFAULT-CAR)))