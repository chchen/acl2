(PFIELD::BITXOR-CONSTRAINT-INTRO
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (18 18
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (6 6 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (4 4
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (2 2
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-ALT
     (41 22
         (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (22 22
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (22 22
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (16 16 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (14 11
         (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (7 7
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (7 4
        (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (5 4
        (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (5 1 (:DEFINITION NATP))
     (4 4 (:REWRITE PFIELD::ADD-COMMUTATIVE))
     (3 3
        (:REWRITE PFIELD::NEG-OF-MUL-WHEN-CONSTANT))
     (2 2 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (2 1 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (2 1 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (2 1 (:REWRITE PFIELD::ADD-BOUND))
     (1 1
        (:TYPE-PRESCRIPTION PFIELD::NATP-OF-NEG))
     (1 1 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
     (1 1
        (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (1 1
        (:REWRITE EQUAL-OF-CONSTANT-AND-BITXOR-OF-CONSTANT))
     (1 1
        (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1
        (:REWRITE BITXOR-WHEN-Y-IS-NOT-AN-INTEGER))
     (1 1
        (:REWRITE BITXOR-WHEN-X-IS-NOT-AN-INTEGER))
     (1 1
        (:REWRITE BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG2))
     (1 1
        (:REWRITE BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG1))
     (1 1 (:REWRITE BITXOR-SUBST-ARG2))
     (1 1 (:REWRITE BITXOR-SUBST-ARG1))
     (1 1
        (:REWRITE PFIELD::ADD-OF-MUL-AND-MUL-COMBINE-CONSTANTS))
     (1 1 (:REWRITE PFIELD::ADD-COMMUTATIVE-2))
     (1 1
        (:REWRITE PFIELD::ADD-COMBINE-CONSTANTS)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-B
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (18 18
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (6 6 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (4 4
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (2 2
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-B-ALT
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (18 18
         (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (18 18
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (6 6 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (4 4
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (2 2
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-2
     (28 14 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (23 7 (:DEFINITION NATP))
     (21 21 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (21 21
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (21 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (14 7 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (13 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (13 10 (:REWRITE DEFAULT-<-1))
     (12 1 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
     (10 10 (:REWRITE DEFAULT-<-2))
     (9 3
        (:REWRITE PFIELD::ADD-OF-NEG-SAME-ARG2-GEN))
     (8 8 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (7 7 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (3 3
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-2-ALT
     (28 14 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (23 7 (:DEFINITION NATP))
     (21 21 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (21 21
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (21 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (14 7 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (13 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (13 10 (:REWRITE DEFAULT-<-1))
     (12 1 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
     (10 10 (:REWRITE DEFAULT-<-2))
     (9 3
        (:REWRITE PFIELD::ADD-OF-NEG-SAME-ARG2-GEN))
     (8 8 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (7 7 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (3 3
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-2B
     (28 14 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (23 7 (:DEFINITION NATP))
     (21 21 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (21 21
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (21 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (14 7 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (13 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (13 10 (:REWRITE DEFAULT-<-1))
     (12 1 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
     (10 10 (:REWRITE DEFAULT-<-2))
     (9 3
        (:REWRITE PFIELD::ADD-OF-NEG-SAME-ARG2-GEN))
     (8 8 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (7 7 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (3 3
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::BITXOR-CONSTRAINT-INTRO-2B-ALT
     (28 14 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (23 7 (:DEFINITION NATP))
     (21 21 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (21 21
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (21 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (14 7 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (13 13
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (13 10 (:REWRITE DEFAULT-<-1))
     (12 1 (:REWRITE PFIELD::EQUAL-OF-NEG-SOLVE))
     (10 10 (:REWRITE DEFAULT-<-2))
     (9 3
        (:REWRITE PFIELD::ADD-OF-NEG-SAME-ARG2-GEN))
     (8 8 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (7 7 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1))
     (3 3
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1)))
(PFIELD::XOR-IDIOM-1
     (20 12
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (20 4 (:DEFINITION NATP))
     (18 18 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (16 14 (:REWRITE DEFAULT-<-1))
     (14 14
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (14 14 (:REWRITE DEFAULT-<-2))
     (12 12
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (8 8 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (8 4 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (8 4 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (5 5
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (4 4
        (:REWRITE PFIELD::NEG-WHEN-CONSTANT-ARG1)))
(PFIELD::XOR-IDIOM-2
     (37 37 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (28 17
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
     (25 23 (:REWRITE DEFAULT-<-1))
     (23 23 (:REWRITE DEFAULT-<-2))
     (20 4 (:DEFINITION NATP))
     (17 17
         (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
     (14 14
         (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (11 11
         (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (9 9
        (:REWRITE PFIELD::NEG-WHEN-NOT-INTEGERP-CHEAP))
     (8 8 (:TYPE-PRESCRIPTION POWER-OF-2P))
     (8 4 (:REWRITE NATP-WHEN-POWER-OF-2P))
     (8 4 (:REWRITE INTEGERP-WHEN-POWER-OF-2P))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (1 1 (:REWRITE PFIELD::MUL-COMMUTATIVE-2))
     (1 1
        (:REWRITE PFIELD::MUL-COMBINE-CONSTANTS))
     (1 1
        (:REWRITE EQUAL-OF-CONSTANT-AND-BITXOR-OF-CONSTANT))
     (1 1
        (:REWRITE PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS))
     (1 1
        (:REWRITE BITXOR-WHEN-Y-IS-NOT-AN-INTEGER))
     (1 1
        (:REWRITE BITXOR-WHEN-X-IS-NOT-AN-INTEGER))
     (1 1
        (:REWRITE BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG2))
     (1 1
        (:REWRITE BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG1))
     (1 1 (:REWRITE BITXOR-SUBST-ARG2))
     (1 1 (:REWRITE BITXOR-SUBST-ARG1)))
(PFIELD::XOR-IDIOM-3
     (12 12 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (6 6
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (4 4
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(PFIELD::XOR-IDIOM-3-ALT
     (12 12 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (6 6
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (4 4
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(PFIELD::XOR-IDIOM-4
     (12 12 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (6 6
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (4 4
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(PFIELD::XOR-IDIOM-4-ALT
     (12 12 (:REWRITE PFIELD::MUL-BECOMES-NEG))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE))
     (6 6
        (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
     (6 6
        (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
     (4 4
        (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))