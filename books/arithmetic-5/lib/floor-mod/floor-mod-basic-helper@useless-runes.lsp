(NIQ-BOUNDS
     (674 674
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (674 674
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (674 674
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (674 674
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (160 84 (:REWRITE DEFAULT-LESS-THAN-1))
     (156 81
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (151 80 (:REWRITE SIMPLIFY-SUMS-<))
     (117 59 (:REWRITE DEFAULT-PLUS-2))
     (100 84 (:REWRITE DEFAULT-LESS-THAN-2))
     (84 84
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (84 84
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (81 81 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (81 81
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (81 81 (:REWRITE INTEGERP-<-CONSTANT))
     (81 81 (:REWRITE CONSTANT-<-INTEGERP))
     (81 81
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (81 81
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (81 81
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (81 81
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (81 81 (:REWRITE |(< c (- x))|))
     (81 81
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (81 81
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (81 81
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (81 81
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (81 81 (:REWRITE |(< (/ x) (/ y))|))
     (81 81 (:REWRITE |(< (- x) c)|))
     (81 81 (:REWRITE |(< (- x) (- y))|))
     (80 59 (:REWRITE DEFAULT-PLUS-1))
     (42 42
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE |(< (* x y) 0)|))
     (33 33 (:REWRITE |(< (/ x) 0)|))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (30 30 (:REWRITE DEFAULT-TIMES-2))
     (30 30 (:REWRITE DEFAULT-TIMES-1))
     (26 26 (:REWRITE REDUCE-INTEGERP-+))
     (26 26 (:REWRITE INTEGERP-MINUS-X))
     (26 26 (:META META-INTEGERP-CORRECT))
     (20 20
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (18 18 (:REWRITE DEFAULT-DIVIDE))
     (15 15 (:REWRITE DEFAULT-MINUS))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< 0 (/ x))|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:REWRITE |arith (* c (* d x))|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< y (+ (- c) x))|))
     (7 7 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |arith (- (* c x))|))
     (4 4 (:REWRITE |arith (* (- x) y)|))
     (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|)))
(INTEGERP-MOD
     (241 2
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (58 2 (:DEFINITION NFIX))
     (50 15 (:REWRITE DEFAULT-PLUS-2))
     (41 13 (:REWRITE DEFAULT-MINUS))
     (35 15 (:REWRITE DEFAULT-TIMES-1))
     (31 31 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (26 15 (:REWRITE DEFAULT-PLUS-1))
     (24 15 (:REWRITE DEFAULT-TIMES-2))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (21 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (16 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (16 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (15 5 (:REWRITE SIMPLIFY-SUMS-<))
     (15 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 2 (:DEFINITION IFIX))
     (11 6 (:REWRITE |(< (- x) (- y))|))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 1 (:REWRITE DEFAULT-MOD-RATIO))
     (10 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (5 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (3 3 (:REWRITE DEFAULT-DIVIDE))
     (3 3 (:REWRITE |(- (* c x))|))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(RATIONALP-MOD
     (241 2
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (64 6 (:REWRITE REDUCE-RATIONALP-*))
     (58 2 (:DEFINITION NFIX))
     (52 17 (:REWRITE DEFAULT-PLUS-2))
     (48 6 (:REWRITE RATIONALP-X))
     (41 21 (:REWRITE DEFAULT-TIMES-1))
     (41 13 (:REWRITE DEFAULT-MINUS))
     (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (31 31 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (31 31
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (30 21 (:REWRITE DEFAULT-TIMES-2))
     (28 17 (:REWRITE DEFAULT-PLUS-1))
     (21 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (16 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (16 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (16 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (15 5 (:REWRITE SIMPLIFY-SUMS-<))
     (15 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 2 (:DEFINITION IFIX))
     (11 6 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8 (:REWRITE DEFAULT-DIVIDE))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (5 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:DEFINITION RFIX))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE |(- (* c x))|))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2 (:REWRITE ACL2-NUMBERP-X))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE |(+ c (+ d x))|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(FLOOR-MOD-ELIM (233 17 (:REWRITE REDUCE-RATIONALP-*))
                (136 21 (:REWRITE RATIONALP-X))
                (120 8 (:REWRITE |(equal (if a b c) x)|))
                (96 8 (:DEFINITION RFIX))
                (47 7 (:REWRITE ACL2-NUMBERP-X))
                (36 4 (:REWRITE RATIONALP-/))
                (35 18 (:REWRITE DEFAULT-PLUS-2))
                (35 18 (:REWRITE DEFAULT-PLUS-1))
                (32 15 (:REWRITE DEFAULT-TIMES-2))
                (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                (21 21 (:REWRITE REDUCE-INTEGERP-+))
                (21 21 (:REWRITE INTEGERP-MINUS-X))
                (21 21 (:META META-INTEGERP-CORRECT))
                (19 19 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                (19 19 (:TYPE-PRESCRIPTION INTEGERP-MOD))
                (17 17 (:REWRITE REDUCE-RATIONALP-+))
                (17 17 (:REWRITE RATIONALP-MINUS-X))
                (17 17 (:META META-RATIONALP-CORRECT))
                (9 9
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (8 8
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (8 8
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (8 8
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (8 8
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (8 8
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (8 8
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (8 8 (:REWRITE |(equal c (/ x))|))
                (8 8 (:REWRITE |(equal c (- x))|))
                (8 8 (:REWRITE |(equal (/ x) c)|))
                (8 8 (:REWRITE |(equal (/ x) (/ y))|))
                (8 8 (:REWRITE |(equal (- x) c)|))
                (8 8 (:REWRITE |(equal (- x) (- y))|))
                (7 7
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
                (7 7 (:REWRITE DEFAULT-DIVIDE))
                (4 4 (:REWRITE INTEGERP-/))
                (4 4 (:REWRITE |(not (equal x (/ y)))|))
                (4 4 (:REWRITE |(equal x (/ y))|))
                (3 3 (:REWRITE DEFAULT-FLOOR-1))
                (2 2 (:REWRITE DEFAULT-MOD-1))
                (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                (2 1 (:REWRITE DEFAULT-MINUS))
                (1 1
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (1 1 (:REWRITE |(- (* c x))|)))
(LINEAR-FLOOR-BOUNDS-1
     (1431 12
           (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (348 12 (:DEFINITION NFIX))
     (346 346 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (220 28 (:REWRITE ACL2-NUMBERP-X))
     (191 191
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (191 191
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (191 191
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (191 191
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (183 36 (:REWRITE RATIONALP-X))
     (174 42
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (164 81 (:REWRITE DEFAULT-PLUS-2))
     (158 81 (:REWRITE DEFAULT-PLUS-1))
     (146 52 (:REWRITE DEFAULT-LESS-THAN-2))
     (141 33 (:REWRITE REDUCE-RATIONALP-*))
     (124 52 (:REWRITE DEFAULT-LESS-THAN-1))
     (100 60 (:REWRITE DEFAULT-TIMES-2))
     (79 44 (:REWRITE |(< (- x) (- y))|))
     (72 12 (:DEFINITION IFIX))
     (60 4 (:REWRITE |(equal (if a b c) x)|))
     (50 50 (:REWRITE REDUCE-INTEGERP-+))
     (50 50 (:REWRITE INTEGERP-MINUS-X))
     (50 50 (:META META-INTEGERP-CORRECT))
     (48 4 (:DEFINITION RFIX))
     (44 44 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (44 44
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (44 44
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (44 44
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (44 44 (:REWRITE INTEGERP-<-CONSTANT))
     (44 44 (:REWRITE CONSTANT-<-INTEGERP))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< c (- x))|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (44 44
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (44 44 (:REWRITE |(< (/ x) (/ y))|))
     (44 44 (:REWRITE |(< (- x) c)|))
     (37 37
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (33 33 (:REWRITE REDUCE-RATIONALP-+))
     (33 33 (:REWRITE RATIONALP-MINUS-X))
     (33 33 (:META META-RATIONALP-CORRECT))
     (33 21 (:REWRITE DEFAULT-MINUS))
     (27 27
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (27 27
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (27 3 (:REWRITE RATIONALP-/))
     (16 16 (:REWRITE |(< (/ x) 0)|))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (16 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 2
        (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                 . 4))
     (8 2
        (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION-LINEAR
                 . 2))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE |(- (* c x))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (3 3 (:REWRITE INTEGERP-/))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(+ c (+ d x))|)))
(LINEAR-FLOOR-BOUNDS-2
     (110 14 (:REWRITE ACL2-NUMBERP-X))
     (50 50 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (50 50
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (50 50
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (50 50
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (50 50
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (48 12 (:REWRITE RATIONALP-X))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18 18 (:REWRITE DEFAULT-TIMES-2))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE REDUCE-RATIONALP-+))
     (12 12 (:REWRITE REDUCE-RATIONALP-*))
     (12 12 (:REWRITE RATIONALP-MINUS-X))
     (12 12 (:META META-RATIONALP-CORRECT))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(LINEAR-FLOOR-BOUNDS-3
     (600 5
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (145 5 (:DEFINITION NFIX))
     (102 102 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (72 8 (:REWRITE ACL2-NUMBERP-X))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (61 26 (:REWRITE DEFAULT-PLUS-2))
     (57 26 (:REWRITE DEFAULT-PLUS-1))
     (50 16 (:REWRITE DEFAULT-LESS-THAN-1))
     (42 14
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 13 (:REWRITE SIMPLIFY-SUMS-<))
     (36 9 (:REWRITE RATIONALP-X))
     (34 19 (:REWRITE DEFAULT-TIMES-2))
     (30 5 (:DEFINITION IFIX))
     (26 15 (:REWRITE |(< (- x) (- y))|))
     (17 16 (:REWRITE DEFAULT-LESS-THAN-2))
     (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (15 15
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15 (:REWRITE INTEGERP-<-CONSTANT))
     (15 15 (:REWRITE CONSTANT-<-INTEGERP))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 15 (:REWRITE |(< (- x) c)|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 8 (:REWRITE DEFAULT-MINUS))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9 (:META META-RATIONALP-CORRECT))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (7 7
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE |(- (* c x))|)))
(HACK0 (77 77 (:REWRITE DEFAULT-TIMES-2))
       (77 77 (:REWRITE DEFAULT-TIMES-1))
       (72 18 (:REWRITE RATIONALP-X))
       (68 68
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (22 22 (:REWRITE DEFAULT-COMPLEX-2))
       (22 22 (:REWRITE DEFAULT-COMPLEX-1))
       (18 18 (:REWRITE REDUCE-RATIONALP-+))
       (18 18 (:REWRITE REDUCE-RATIONALP-*))
       (18 18 (:REWRITE REDUCE-INTEGERP-+))
       (18 18 (:REWRITE RATIONALP-MINUS-X))
       (18 18 (:REWRITE INTEGERP-MINUS-X))
       (18 18
           (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (18 18 (:META META-RATIONALP-CORRECT))
       (18 18 (:META META-INTEGERP-CORRECT))
       (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (16 16
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (16 16
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (16 16
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (16 16
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (16 16
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
       (16 16 (:REWRITE NORMALIZE-ADDENDS))
       (16 16
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (16 16 (:REWRITE DEFAULT-PLUS-2))
       (16 16 (:REWRITE DEFAULT-PLUS-1))
       (16 16 (:REWRITE |(equal c (/ x))|))
       (16 16 (:REWRITE |(equal c (- x))|))
       (16 16 (:REWRITE |(equal (/ x) c)|))
       (16 16 (:REWRITE |(equal (/ x) (/ y))|))
       (16 16 (:REWRITE |(equal (- x) c)|))
       (16 16 (:REWRITE |(equal (- x) (- y))|))
       (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
       (9 9 (:REWRITE |(* c (* d x))|))
       (4 4 (:REWRITE ARITH-NORMALIZE-ADDENDS))
       (2 2 (:REWRITE |arith (* c (* d x))|)))
(HACK1 (12 3 (:REWRITE RATIONALP-X))
       (3 3 (:REWRITE REDUCE-RATIONALP-+))
       (3 3 (:REWRITE REDUCE-RATIONALP-*))
       (3 3 (:REWRITE REDUCE-INTEGERP-+))
       (3 3 (:REWRITE RATIONALP-MINUS-X))
       (3 3 (:REWRITE INTEGERP-MINUS-X))
       (3 3 (:META META-RATIONALP-CORRECT))
       (3 3 (:META META-INTEGERP-CORRECT))
       (1 1
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (1 1
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (1 1
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (1 1
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (1 1
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (1 1
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (1 1 (:REWRITE DEFAULT-COMPLEX-2))
       (1 1 (:REWRITE DEFAULT-COMPLEX-1))
       (1 1 (:REWRITE |(equal c (/ x))|))
       (1 1 (:REWRITE |(equal c (- x))|))
       (1 1 (:REWRITE |(equal (/ x) c)|))
       (1 1 (:REWRITE |(equal (/ x) (/ y))|))
       (1 1 (:REWRITE |(equal (- x) c)|))
       (1 1 (:REWRITE |(equal (- x) (- y))|)))
(HACK2 (96 24 (:REWRITE RATIONALP-X))
       (81 9 (:REWRITE ACL2-NUMBERP-X))
       (30 30 (:REWRITE DEFAULT-TIMES-2))
       (30 30 (:REWRITE DEFAULT-TIMES-1))
       (26 26
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (24 24 (:REWRITE REDUCE-RATIONALP-+))
       (24 24 (:REWRITE REDUCE-RATIONALP-*))
       (24 24 (:REWRITE REDUCE-INTEGERP-+))
       (24 24 (:REWRITE RATIONALP-MINUS-X))
       (24 24 (:REWRITE INTEGERP-MINUS-X))
       (24 24 (:META META-RATIONALP-CORRECT))
       (24 24 (:META META-INTEGERP-CORRECT))
       (11 11 (:REWRITE DEFAULT-REALPART))
       (11 11 (:REWRITE DEFAULT-IMAGPART))
       (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (10 10
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (10 10
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (10 10
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (10 10
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (10 10
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (10 10 (:REWRITE |(equal c (/ x))|))
       (10 10 (:REWRITE |(equal c (- x))|))
       (10 10 (:REWRITE |(equal (/ x) c)|))
       (10 10 (:REWRITE |(equal (/ x) (/ y))|))
       (10 10 (:REWRITE |(equal (- x) c)|))
       (10 10 (:REWRITE |(equal (- x) (- y))|))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (6 6 (:REWRITE DEFAULT-COMPLEX-2))
       (6 6 (:REWRITE DEFAULT-COMPLEX-1)))
(HACK3)
(FOO-1 (320 50 (:REWRITE REDUCE-RATIONALP-*))
       (200 50 (:REWRITE RATIONALP-X))
       (125 101 (:REWRITE DEFAULT-TIMES-2))
       (101 101 (:REWRITE DEFAULT-TIMES-1))
       (87 31 (:REWRITE |(equal (/ x) c)|))
       (67 67
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-2))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-1))
       (61 61 (:REWRITE INTEGERP-<-CONSTANT))
       (61 61 (:REWRITE CONSTANT-<-INTEGERP))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< c (- x))|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< (/ x) (/ y))|))
       (61 61 (:REWRITE |(< (- x) c)|))
       (61 61 (:REWRITE |(< (- x) (- y))|))
       (60 12 (:DEFINITION RFIX))
       (55 55
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (50 50 (:REWRITE REDUCE-RATIONALP-+))
       (50 50 (:REWRITE REDUCE-INTEGERP-+))
       (50 50 (:REWRITE RATIONALP-MINUS-X))
       (50 50 (:REWRITE INTEGERP-MINUS-X))
       (50 50 (:META META-RATIONALP-CORRECT))
       (50 50 (:META META-INTEGERP-CORRECT))
       (50 27
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (49 49 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (43 43 (:REWRITE SIMPLIFY-SUMS-<))
       (43 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (33 33 (:REWRITE |(< 0 (* x y))|))
       (31 31
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (31 31
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (31 31 (:REWRITE |(equal c (/ x))|))
       (31 31 (:REWRITE |(equal (/ x) (/ y))|))
       (31 31 (:REWRITE |(equal (- x) (- y))|))
       (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (27 27
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (27 27
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (27 27 (:REWRITE |(equal c (- x))|))
       (27 27 (:REWRITE |(equal (- x) c)|))
       (27 27 (:REWRITE |(< 0 (/ x))|))
       (26 26
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (21 21 (:REWRITE DEFAULT-REALPART))
       (8 8 (:REWRITE DEFAULT-IMAGPART))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (6 6 (:REWRITE |(equal (if a b c) x)|))
       (6 6
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
       (6 6
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (6 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
       (4 4 (:REWRITE DEFAULT-DIVIDE))
       (4 4
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |(not (equal x (/ y)))|))
       (4 4 (:REWRITE |(equal x (/ y))|))
       (4 4 (:REWRITE |(/ (/ x))|))
       (2 2 (:REWRITE |arith (* c (* d x))|))
       (1 1 (:REWRITE |arith (- (* c x))|))
       (1 1 (:REWRITE |arith (* (- x) y)|)))
(FOO-2 (475 70 (:REWRITE REDUCE-RATIONALP-*))
       (282 234 (:REWRITE DEFAULT-TIMES-2))
       (280 70 (:REWRITE RATIONALP-X))
       (255 12
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (234 234 (:REWRITE DEFAULT-TIMES-1))
       (164 164 (:REWRITE DEFAULT-LESS-THAN-2))
       (164 164 (:REWRITE DEFAULT-LESS-THAN-1))
       (125 125
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (125 125
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (125 125
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (122 122
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
       (122 122 (:REWRITE INTEGERP-<-CONSTANT))
       (122 122 (:REWRITE CONSTANT-<-INTEGERP))
       (122 122
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (122 122
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (122 122
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (122 122
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (122 122 (:REWRITE |(< c (- x))|))
       (122 122
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (122 122
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (122 122
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (122 122
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (122 122 (:REWRITE |(< (/ x) (/ y))|))
       (122 122 (:REWRITE |(< (- x) c)|))
       (122 122 (:REWRITE |(< (- x) (- y))|))
       (120 12
            (:REWRITE |(<= (/ x) y) with (< x 0)|))
       (120 12
            (:REWRITE |(< x (/ y)) with (< y 0)|))
       (107 107
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (107 107
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (107 107 (:REWRITE |(equal c (/ x))|))
       (107 107 (:REWRITE |(equal (/ x) (/ y))|))
       (107 107 (:REWRITE |(equal (- x) (- y))|))
       (104 104 (:REWRITE SIMPLIFY-SUMS-<))
       (104 104
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (93 93 (:REWRITE |(equal c (- x))|))
       (93 93 (:REWRITE |(equal (- x) c)|))
       (90 18 (:DEFINITION RFIX))
       (88 88 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (88 88
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (85 85
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (84 84
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (71 17 (:REWRITE FOO-1))
       (70 70 (:REWRITE REDUCE-RATIONALP-+))
       (70 70 (:REWRITE REDUCE-INTEGERP-+))
       (70 70 (:REWRITE RATIONALP-MINUS-X))
       (70 70 (:REWRITE INTEGERP-MINUS-X))
       (70 70 (:META META-RATIONALP-CORRECT))
       (70 70 (:META META-INTEGERP-CORRECT))
       (46 46 (:REWRITE |(< 0 (* x y))|))
       (43 43
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (43 43
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (43 43 (:REWRITE |(< 0 (/ x))|))
       (36 36 (:REWRITE DEFAULT-REALPART))
       (32 32
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (32 32
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (32 32 (:REWRITE |(< (/ x) 0)|))
       (32 32 (:REWRITE |(< (* x y) 0)|))
       (18 18 (:REWRITE DEFAULT-IMAGPART))
       (14 14 (:REWRITE DEFAULT-DIVIDE))
       (14 14 (:REWRITE |(not (equal x (/ y)))|))
       (14 14 (:REWRITE |(equal x (/ y))|))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |arith (* c (* d x))|))
       (2 2 (:REWRITE |arith (- (* c x))|))
       (2 2 (:REWRITE |arith (* (- x) y)|))
       (2 2
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(FOO-3 (368 53 (:REWRITE REDUCE-RATIONALP-*))
       (212 53 (:REWRITE RATIONALP-X))
       (126 102 (:REWRITE DEFAULT-TIMES-2))
       (102 102 (:REWRITE DEFAULT-TIMES-1))
       (90 34 (:REWRITE |(equal (/ x) c)|))
       (70 14 (:DEFINITION RFIX))
       (67 67
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-2))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-1))
       (61 61 (:REWRITE INTEGERP-<-CONSTANT))
       (61 61 (:REWRITE CONSTANT-<-INTEGERP))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< c (- x))|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< (/ x) (/ y))|))
       (61 61 (:REWRITE |(< (- x) c)|))
       (61 61 (:REWRITE |(< (- x) (- y))|))
       (56 56
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (53 53 (:REWRITE REDUCE-RATIONALP-+))
       (53 53 (:REWRITE REDUCE-INTEGERP-+))
       (53 53 (:REWRITE RATIONALP-MINUS-X))
       (53 53 (:REWRITE INTEGERP-MINUS-X))
       (53 53 (:META META-RATIONALP-CORRECT))
       (53 53 (:META META-INTEGERP-CORRECT))
       (53 30
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (49 49 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (43 43 (:REWRITE SIMPLIFY-SUMS-<))
       (43 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (34 34
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (34 34
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (34 34 (:REWRITE |(equal c (/ x))|))
       (34 34 (:REWRITE |(equal (/ x) (/ y))|))
       (34 34 (:REWRITE |(equal (- x) (- y))|))
       (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (30 30
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (30 30
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (30 30 (:REWRITE |(equal c (- x))|))
       (30 30 (:REWRITE |(equal (- x) c)|))
       (29 29
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (27 27 (:REWRITE |(< (/ x) 0)|))
       (27 27 (:REWRITE |(< (* x y) 0)|))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (21 21 (:REWRITE DEFAULT-REALPART))
       (12 12 (:REWRITE FOO-2))
       (12 12 (:REWRITE FOO-1))
       (8 8 (:REWRITE DEFAULT-IMAGPART))
       (7 7 (:REWRITE |(equal (if a b c) x)|))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (6 6 (:REWRITE |(< 0 (* x y))|))
       (4 4 (:REWRITE DEFAULT-DIVIDE))
       (4 4
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |(not (equal x (/ y)))|))
       (4 4 (:REWRITE |(equal x (/ y))|))
       (4 4 (:REWRITE |(/ (/ x))|))
       (2 2 (:REWRITE |arith (* c (* d x))|))
       (1 1 (:REWRITE |arith (- (* c x))|))
       (1 1 (:REWRITE |arith (* (- x) y)|)))
(FOO-4 (475 70 (:REWRITE REDUCE-RATIONALP-*))
       (280 70 (:REWRITE RATIONALP-X))
       (272 224 (:REWRITE DEFAULT-TIMES-2))
       (252 9 (:REWRITE |(< x (/ y)) with (< y 0)|))
       (224 224 (:REWRITE DEFAULT-TIMES-1))
       (168 168 (:REWRITE DEFAULT-LESS-THAN-2))
       (168 168 (:REWRITE DEFAULT-LESS-THAN-1))
       (129 129
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (129 129
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (129 129
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (126 126
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
       (126 126 (:REWRITE INTEGERP-<-CONSTANT))
       (126 126 (:REWRITE CONSTANT-<-INTEGERP))
       (126 126
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (126 126
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (126 126
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (126 126
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (126 126 (:REWRITE |(< c (- x))|))
       (126 126
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (126 126
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (126 126
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (126 126
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (126 126 (:REWRITE |(< (/ x) (/ y))|))
       (126 126 (:REWRITE |(< (- x) c)|))
       (126 126 (:REWRITE |(< (- x) (- y))|))
       (117 9
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (117 9 (:REWRITE |(< x (/ y)) with (< 0 y)|))
       (108 108 (:REWRITE SIMPLIFY-SUMS-<))
       (108 108
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (107 107
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (107 107
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (107 107 (:REWRITE |(equal c (/ x))|))
       (107 107 (:REWRITE |(equal (/ x) (/ y))|))
       (107 107 (:REWRITE |(equal (- x) (- y))|))
       (93 93 (:REWRITE |(equal c (- x))|))
       (93 93 (:REWRITE |(equal (- x) c)|))
       (90 18 (:DEFINITION RFIX))
       (88 88 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (88 88
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (85 85
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (84 84
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (71 17 (:REWRITE FOO-3))
       (71 17 (:REWRITE FOO-2))
       (71 17 (:REWRITE FOO-1))
       (70 70 (:REWRITE REDUCE-RATIONALP-+))
       (70 70 (:REWRITE REDUCE-INTEGERP-+))
       (70 70 (:REWRITE RATIONALP-MINUS-X))
       (70 70 (:REWRITE INTEGERP-MINUS-X))
       (70 70 (:META META-RATIONALP-CORRECT))
       (70 70 (:META META-INTEGERP-CORRECT))
       (47 47 (:REWRITE |(< 0 (* x y))|))
       (44 44
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (44 44
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (44 44 (:REWRITE |(< 0 (/ x))|))
       (36 36 (:REWRITE DEFAULT-REALPART))
       (35 35
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (35 35
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (35 35 (:REWRITE |(< (/ x) 0)|))
       (35 35 (:REWRITE |(< (* x y) 0)|))
       (18 18 (:REWRITE DEFAULT-IMAGPART))
       (14 14 (:REWRITE DEFAULT-DIVIDE))
       (14 14 (:REWRITE |(not (equal x (/ y)))|))
       (14 14 (:REWRITE |(equal x (/ y))|))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |arith (* c (* d x))|))
       (2 2 (:REWRITE |arith (- (* c x))|))
       (2 2 (:REWRITE |arith (* (- x) y)|))
       (2 2
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(MOD-BOUNDS-1
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (192 24 (:REWRITE ACL2-NUMBERP-X))
     (184 36 (:REWRITE RATIONALP-X))
     (144 24 (:REWRITE DEFAULT-FLOOR-RATIO))
     (124 32 (:REWRITE REDUCE-RATIONALP-*))
     (89 82 (:REWRITE DEFAULT-TIMES-2))
     (65 65
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (60 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (60 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (59 59 (:REWRITE DEFAULT-DIVIDE))
     (53 36 (:REWRITE DEFAULT-PLUS-2))
     (48 4 (:DEFINITION RFIX))
     (46 36 (:REWRITE DEFAULT-PLUS-1))
     (44 44 (:REWRITE REDUCE-INTEGERP-+))
     (44 44 (:REWRITE INTEGERP-MINUS-X))
     (44 44 (:META META-INTEGERP-CORRECT))
     (40 36 (:REWRITE DEFAULT-LESS-THAN-1))
     (36 4 (:REWRITE RATIONALP-/))
     (34 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 32 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (32 32 (:REWRITE REDUCE-RATIONALP-+))
     (32 32 (:REWRITE RATIONALP-MINUS-X))
     (32 32 (:META META-RATIONALP-CORRECT))
     (30 19 (:REWRITE SIMPLIFY-SUMS-<))
     (30 4 (:REWRITE |(equal (if a b c) x)|))
     (30 2 (:REWRITE HACK3))
     (28 28
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (28 26 (:REWRITE |(< (- x) (- y))|))
     (27 26 (:REWRITE |(< (- x) c)|))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE DEFAULT-FLOOR-2))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< c (- x))|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< (/ x) (/ y))|))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (17 17
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 2 (:REWRITE DEFAULT-MOD-RATIO))
     (10 10 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE |(< 0 (* x y))|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< x (+ c/d y))|))
     (5 5 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE INTEGERP-/))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 2 (:REWRITE DEFAULT-MINUS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(- (* c x))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(MOD-BOUNDS-2
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (221 221
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (192 24 (:REWRITE ACL2-NUMBERP-X))
     (184 36 (:REWRITE RATIONALP-X))
     (144 24 (:REWRITE DEFAULT-FLOOR-RATIO))
     (124 32 (:REWRITE REDUCE-RATIONALP-*))
     (89 82 (:REWRITE DEFAULT-TIMES-2))
     (65 65
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (60 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (60 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (59 59
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (59 59 (:REWRITE DEFAULT-DIVIDE))
     (57 39 (:REWRITE DEFAULT-LESS-THAN-2))
     (53 36 (:REWRITE DEFAULT-PLUS-2))
     (48 4 (:DEFINITION RFIX))
     (46 36 (:REWRITE DEFAULT-PLUS-1))
     (44 44 (:REWRITE REDUCE-INTEGERP-+))
     (44 44 (:REWRITE INTEGERP-MINUS-X))
     (44 44 (:META META-INTEGERP-CORRECT))
     (36 4 (:REWRITE RATIONALP-/))
     (34 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (32 32 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (32 32 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (32 32 (:REWRITE REDUCE-RATIONALP-+))
     (32 32 (:REWRITE RATIONALP-MINUS-X))
     (32 32 (:META META-RATIONALP-CORRECT))
     (30 19 (:REWRITE SIMPLIFY-SUMS-<))
     (30 4 (:REWRITE |(equal (if a b c) x)|))
     (30 2 (:REWRITE HACK3))
     (28 28
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (27 26 (:REWRITE |(< c (- x))|))
     (26 26 (:REWRITE INTEGERP-<-CONSTANT))
     (26 26 (:REWRITE DEFAULT-FLOOR-2))
     (26 26 (:REWRITE CONSTANT-<-INTEGERP))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (26 26
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (26 26 (:REWRITE |(< (/ x) (/ y))|))
     (26 26 (:REWRITE |(< (- x) c)|))
     (26 26 (:REWRITE |(< (- x) (- y))|))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (17 17
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 2 (:REWRITE DEFAULT-MOD-RATIO))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE INTEGERP-/))
     (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 2 (:REWRITE DEFAULT-MINUS))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(- (* c x))|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(HACK0 (77 77 (:REWRITE DEFAULT-TIMES-2))
       (77 77 (:REWRITE DEFAULT-TIMES-1))
       (72 18 (:REWRITE RATIONALP-X))
       (68 68
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (22 22 (:REWRITE DEFAULT-COMPLEX-2))
       (22 22 (:REWRITE DEFAULT-COMPLEX-1))
       (18 18 (:REWRITE REDUCE-RATIONALP-+))
       (18 18 (:REWRITE REDUCE-RATIONALP-*))
       (18 18 (:REWRITE REDUCE-INTEGERP-+))
       (18 18 (:REWRITE RATIONALP-MINUS-X))
       (18 18 (:REWRITE INTEGERP-MINUS-X))
       (18 18
           (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (18 18 (:META META-RATIONALP-CORRECT))
       (18 18 (:META META-INTEGERP-CORRECT))
       (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (16 16
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (16 16
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (16 16
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (16 16
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (16 16
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
       (16 16 (:REWRITE NORMALIZE-ADDENDS))
       (16 16
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (16 16 (:REWRITE DEFAULT-PLUS-2))
       (16 16 (:REWRITE DEFAULT-PLUS-1))
       (16 16 (:REWRITE |(equal c (/ x))|))
       (16 16 (:REWRITE |(equal c (- x))|))
       (16 16 (:REWRITE |(equal (/ x) c)|))
       (16 16 (:REWRITE |(equal (/ x) (/ y))|))
       (16 16 (:REWRITE |(equal (- x) c)|))
       (16 16 (:REWRITE |(equal (- x) (- y))|))
       (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
       (9 9 (:REWRITE |(* c (* d x))|))
       (4 4 (:REWRITE ARITH-NORMALIZE-ADDENDS))
       (2 2 (:REWRITE |arith (* c (* d x))|)))
(HACK1 (12 3 (:REWRITE RATIONALP-X))
       (3 3 (:REWRITE REDUCE-RATIONALP-+))
       (3 3 (:REWRITE REDUCE-RATIONALP-*))
       (3 3 (:REWRITE REDUCE-INTEGERP-+))
       (3 3 (:REWRITE RATIONALP-MINUS-X))
       (3 3 (:REWRITE INTEGERP-MINUS-X))
       (3 3 (:META META-RATIONALP-CORRECT))
       (3 3 (:META META-INTEGERP-CORRECT))
       (1 1
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (1 1
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (1 1
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (1 1
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (1 1
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (1 1
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (1 1 (:REWRITE DEFAULT-COMPLEX-2))
       (1 1 (:REWRITE DEFAULT-COMPLEX-1))
       (1 1 (:REWRITE |(equal c (/ x))|))
       (1 1 (:REWRITE |(equal c (- x))|))
       (1 1 (:REWRITE |(equal (/ x) c)|))
       (1 1 (:REWRITE |(equal (/ x) (/ y))|))
       (1 1 (:REWRITE |(equal (- x) c)|))
       (1 1 (:REWRITE |(equal (- x) (- y))|)))
(HACK2 (96 24 (:REWRITE RATIONALP-X))
       (81 9 (:REWRITE ACL2-NUMBERP-X))
       (30 30 (:REWRITE DEFAULT-TIMES-2))
       (30 30 (:REWRITE DEFAULT-TIMES-1))
       (26 26
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (24 24 (:REWRITE REDUCE-RATIONALP-+))
       (24 24 (:REWRITE REDUCE-RATIONALP-*))
       (24 24 (:REWRITE REDUCE-INTEGERP-+))
       (24 24 (:REWRITE RATIONALP-MINUS-X))
       (24 24 (:REWRITE INTEGERP-MINUS-X))
       (24 24 (:META META-RATIONALP-CORRECT))
       (24 24 (:META META-INTEGERP-CORRECT))
       (11 11 (:REWRITE DEFAULT-REALPART))
       (11 11 (:REWRITE DEFAULT-IMAGPART))
       (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (10 10
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (10 10
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (10 10
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (10 10
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (10 10
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (10 10 (:REWRITE |(equal c (/ x))|))
       (10 10 (:REWRITE |(equal c (- x))|))
       (10 10 (:REWRITE |(equal (/ x) c)|))
       (10 10 (:REWRITE |(equal (/ x) (/ y))|))
       (10 10 (:REWRITE |(equal (- x) c)|))
       (10 10 (:REWRITE |(equal (- x) (- y))|))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (6 6 (:REWRITE DEFAULT-COMPLEX-2))
       (6 6 (:REWRITE DEFAULT-COMPLEX-1)))
(HACK3)
(FOO-1 (320 50 (:REWRITE REDUCE-RATIONALP-*))
       (200 50 (:REWRITE RATIONALP-X))
       (125 101 (:REWRITE DEFAULT-TIMES-2))
       (101 101 (:REWRITE DEFAULT-TIMES-1))
       (87 31 (:REWRITE |(equal (/ x) c)|))
       (67 67
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-2))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-1))
       (61 61 (:REWRITE INTEGERP-<-CONSTANT))
       (61 61 (:REWRITE CONSTANT-<-INTEGERP))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< c (- x))|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< (/ x) (/ y))|))
       (61 61 (:REWRITE |(< (- x) c)|))
       (61 61 (:REWRITE |(< (- x) (- y))|))
       (60 12 (:DEFINITION RFIX))
       (55 55
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (50 50 (:REWRITE REDUCE-RATIONALP-+))
       (50 50 (:REWRITE REDUCE-INTEGERP-+))
       (50 50 (:REWRITE RATIONALP-MINUS-X))
       (50 50 (:REWRITE INTEGERP-MINUS-X))
       (50 50 (:META META-RATIONALP-CORRECT))
       (50 50 (:META META-INTEGERP-CORRECT))
       (50 27
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (49 49 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (43 43 (:REWRITE SIMPLIFY-SUMS-<))
       (43 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (33 33 (:REWRITE |(< 0 (* x y))|))
       (31 31
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (31 31
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (31 31 (:REWRITE |(equal c (/ x))|))
       (31 31 (:REWRITE |(equal (/ x) (/ y))|))
       (31 31 (:REWRITE |(equal (- x) (- y))|))
       (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (27 27
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (27 27
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (27 27 (:REWRITE |(equal c (- x))|))
       (27 27 (:REWRITE |(equal (- x) c)|))
       (27 27 (:REWRITE |(< 0 (/ x))|))
       (26 26
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (21 21 (:REWRITE DEFAULT-REALPART))
       (8 8 (:REWRITE DEFAULT-IMAGPART))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (6 6 (:REWRITE |(equal (if a b c) x)|))
       (6 6
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
       (6 6
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (6 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
       (4 4 (:REWRITE DEFAULT-DIVIDE))
       (4 4
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |(not (equal x (/ y)))|))
       (4 4 (:REWRITE |(equal x (/ y))|))
       (4 4 (:REWRITE |(/ (/ x))|))
       (2 2 (:REWRITE |arith (* c (* d x))|))
       (1 1 (:REWRITE |arith (- (* c x))|))
       (1 1 (:REWRITE |arith (* (- x) y)|)))
(FOO-2 (520 79 (:REWRITE REDUCE-RATIONALP-*))
       (423 18 (:REWRITE FOO-1))
       (316 79 (:REWRITE RATIONALP-X))
       (309 12
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (294 254 (:REWRITE DEFAULT-TIMES-2))
       (254 254 (:REWRITE DEFAULT-TIMES-1))
       (191 191 (:REWRITE DEFAULT-LESS-THAN-2))
       (191 191 (:REWRITE DEFAULT-LESS-THAN-1))
       (146 146
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (146 146
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (146 146
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (145 145
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
       (145 145 (:REWRITE INTEGERP-<-CONSTANT))
       (145 145 (:REWRITE CONSTANT-<-INTEGERP))
       (145 145
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (145 145
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (145 145
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (145 145
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (145 145 (:REWRITE |(< c (- x))|))
       (145 145
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (145 145
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (145 145
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (145 145
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (145 145 (:REWRITE |(< (/ x) (/ y))|))
       (145 145 (:REWRITE |(< (- x) c)|))
       (145 145 (:REWRITE |(< (- x) (- y))|))
       (125 125
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (125 125
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (125 125 (:REWRITE |(equal c (/ x))|))
       (125 125 (:REWRITE |(equal (/ x) (/ y))|))
       (125 125 (:REWRITE |(equal (- x) (- y))|))
       (121 121 (:REWRITE SIMPLIFY-SUMS-<))
       (121 121
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (120 12
            (:REWRITE |(<= (/ x) y) with (< x 0)|))
       (120 12
            (:REWRITE |(< x (/ y)) with (< y 0)|))
       (108 12 (:REWRITE ACL2-NUMBERP-X))
       (107 107
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (107 107 (:REWRITE |(equal c (- x))|))
       (107 107 (:REWRITE |(equal (- x) c)|))
       (105 105 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (105 105
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (102 102
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (90 18 (:DEFINITION RFIX))
       (88 88
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (79 79 (:REWRITE REDUCE-RATIONALP-+))
       (79 79 (:REWRITE REDUCE-INTEGERP-+))
       (79 79 (:REWRITE RATIONALP-MINUS-X))
       (79 79 (:REWRITE INTEGERP-MINUS-X))
       (79 79 (:META META-RATIONALP-CORRECT))
       (79 79 (:META META-INTEGERP-CORRECT))
       (49 49 (:REWRITE |(< 0 (* x y))|))
       (48 48
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (48 48
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (48 48 (:REWRITE |(< 0 (/ x))|))
       (47 47 (:REWRITE |(< (/ x) 0)|))
       (47 47 (:REWRITE |(< (* x y) 0)|))
       (41 41
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (41 41
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (38 38 (:REWRITE DEFAULT-REALPART))
       (18 18 (:REWRITE DEFAULT-IMAGPART))
       (18 18 (:REWRITE DEFAULT-DIVIDE))
       (18 18 (:REWRITE |(not (equal x (/ y)))|))
       (18 18 (:REWRITE |(equal x (/ y))|))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |arith (* c (* d x))|))
       (2 2 (:REWRITE |arith (- (* c x))|))
       (2 2 (:REWRITE |arith (* (- x) y)|))
       (2 2
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(FOO-3 (368 53 (:REWRITE REDUCE-RATIONALP-*))
       (212 53 (:REWRITE RATIONALP-X))
       (126 102 (:REWRITE DEFAULT-TIMES-2))
       (102 102 (:REWRITE DEFAULT-TIMES-1))
       (90 34 (:REWRITE |(equal (/ x) c)|))
       (70 14 (:DEFINITION RFIX))
       (67 67
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (67 67
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-2))
       (67 67 (:REWRITE DEFAULT-LESS-THAN-1))
       (61 61 (:REWRITE INTEGERP-<-CONSTANT))
       (61 61 (:REWRITE CONSTANT-<-INTEGERP))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< c (- x))|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (61 61
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (61 61 (:REWRITE |(< (/ x) (/ y))|))
       (61 61 (:REWRITE |(< (- x) c)|))
       (61 61 (:REWRITE |(< (- x) (- y))|))
       (56 56
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (53 53 (:REWRITE REDUCE-RATIONALP-+))
       (53 53 (:REWRITE REDUCE-INTEGERP-+))
       (53 53 (:REWRITE RATIONALP-MINUS-X))
       (53 53 (:REWRITE INTEGERP-MINUS-X))
       (53 53 (:META META-RATIONALP-CORRECT))
       (53 53 (:META META-INTEGERP-CORRECT))
       (53 30
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (49 49 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (43 43 (:REWRITE SIMPLIFY-SUMS-<))
       (43 43 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (34 34
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (34 34
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (34 34 (:REWRITE |(equal c (/ x))|))
       (34 34 (:REWRITE |(equal (/ x) (/ y))|))
       (34 34 (:REWRITE |(equal (- x) (- y))|))
       (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (30 30
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (30 30
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (30 30 (:REWRITE |(equal c (- x))|))
       (30 30 (:REWRITE |(equal (- x) c)|))
       (29 29
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (27 27 (:REWRITE |(< (/ x) 0)|))
       (27 27 (:REWRITE |(< (* x y) 0)|))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (21 21
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (21 21 (:REWRITE DEFAULT-REALPART))
       (12 12 (:REWRITE FOO-2))
       (12 12 (:REWRITE FOO-1))
       (8 8 (:REWRITE DEFAULT-IMAGPART))
       (7 7 (:REWRITE |(equal (if a b c) x)|))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (6 6 (:REWRITE |(< 0 (* x y))|))
       (4 4 (:REWRITE DEFAULT-DIVIDE))
       (4 4
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |(not (equal x (/ y)))|))
       (4 4 (:REWRITE |(equal x (/ y))|))
       (4 4 (:REWRITE |(/ (/ x))|))
       (2 2 (:REWRITE |arith (* c (* d x))|))
       (1 1 (:REWRITE |arith (- (* c x))|))
       (1 1 (:REWRITE |arith (* (- x) y)|)))
(FOO-4 (522 18 (:REWRITE FOO-2))
       (520 79 (:REWRITE REDUCE-RATIONALP-*))
       (423 18 (:REWRITE FOO-3))
       (316 79 (:REWRITE RATIONALP-X))
       (308 11
            (:REWRITE |(< x (/ y)) with (< y 0)|))
       (280 240 (:REWRITE DEFAULT-TIMES-2))
       (240 240 (:REWRITE DEFAULT-TIMES-1))
       (211 211 (:REWRITE DEFAULT-LESS-THAN-2))
       (211 211 (:REWRITE DEFAULT-LESS-THAN-1))
       (166 166
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (166 166
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (166 166
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (165 165
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
       (165 165 (:REWRITE INTEGERP-<-CONSTANT))
       (165 165 (:REWRITE CONSTANT-<-INTEGERP))
       (165 165
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (165 165
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (165 165
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (165 165
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (165 165 (:REWRITE |(< c (- x))|))
       (165 165
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (165 165
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (165 165
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (165 165
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (165 165 (:REWRITE |(< (/ x) (/ y))|))
       (165 165 (:REWRITE |(< (- x) c)|))
       (165 165 (:REWRITE |(< (- x) (- y))|))
       (141 141 (:REWRITE SIMPLIFY-SUMS-<))
       (141 141
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (125 125
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (125 125
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (125 125 (:REWRITE |(equal c (/ x))|))
       (125 125 (:REWRITE |(equal (/ x) (/ y))|))
       (125 125 (:REWRITE |(equal (- x) (- y))|))
       (119 11
            (:REWRITE |(<= (/ x) y) with (< 0 x)|))
       (119 11
            (:REWRITE |(< x (/ y)) with (< 0 y)|))
       (108 12 (:REWRITE ACL2-NUMBERP-X))
       (107 107
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (107 107 (:REWRITE |(equal c (- x))|))
       (107 107 (:REWRITE |(equal (- x) c)|))
       (105 105 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (105 105
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (102 102
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (90 18 (:DEFINITION RFIX))
       (88 88
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (79 79 (:REWRITE REDUCE-RATIONALP-+))
       (79 79 (:REWRITE REDUCE-INTEGERP-+))
       (79 79 (:REWRITE RATIONALP-MINUS-X))
       (79 79 (:REWRITE INTEGERP-MINUS-X))
       (79 79 (:META META-RATIONALP-CORRECT))
       (79 79 (:META META-INTEGERP-CORRECT))
       (72 18 (:REWRITE FOO-1))
       (60 60 (:REWRITE |(< 0 (* x y))|))
       (59 59 (:REWRITE |(< 0 (/ x))|))
       (56 56
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (56 56
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (56 56 (:REWRITE |(< (/ x) 0)|))
       (56 56 (:REWRITE |(< (* x y) 0)|))
       (53 53
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (53 53
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (38 38 (:REWRITE DEFAULT-REALPART))
       (18 18 (:REWRITE DEFAULT-IMAGPART))
       (18 18 (:REWRITE DEFAULT-DIVIDE))
       (18 18 (:REWRITE |(not (equal x (/ y)))|))
       (18 18 (:REWRITE |(equal x (/ y))|))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
       (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
       (8 8
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (4 4 (:REWRITE |arith (* c (* d x))|))
       (2 2 (:REWRITE |arith (- (* c x))|))
       (2 2 (:REWRITE |arith (* (- x) y)|))
       (2 2
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(FLOOR-RULE-1
     (138 18 (:REWRITE ACL2-NUMBERP-X))
     (92 20 (:REWRITE RATIONALP-X))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (34 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (34 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (25 25 (:REWRITE DEFAULT-TIMES-2))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-INTEGERP-CORRECT))
     (24 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (20 20 (:REWRITE REDUCE-RATIONALP-+))
     (20 20 (:REWRITE REDUCE-RATIONALP-*))
     (20 20 (:REWRITE RATIONALP-MINUS-X))
     (20 20 (:META META-RATIONALP-CORRECT))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
     (9 1
        (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
     (9 1
        (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
     (9 1
        (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS)))
(BAR-1 (204 48 (:REWRITE RATIONALP-X))
       (174 22 (:REWRITE ACL2-NUMBERP-X))
       (123 123
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
       (123 123
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
       (123 123
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
       (123 123
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
       (63 7
           (:REWRITE |(<= 1 (* x (/ y))) with (< y 0)|))
       (63 7
           (:REWRITE |(<= 1 (* x (/ y))) with (< 0 y)|))
       (63 7
           (:REWRITE |(< (* x (/ y)) 1) with (< y 0)|))
       (63 7
           (:REWRITE |(< (* x (/ y)) 1) with (< 0 y)|))
       (62 62 (:REWRITE DEFAULT-TIMES-2))
       (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
       (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
       (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
       (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
       (51 51 (:REWRITE REDUCE-INTEGERP-+))
       (51 51 (:REWRITE INTEGERP-MINUS-X))
       (51 51 (:META META-INTEGERP-CORRECT))
       (48 48 (:REWRITE REDUCE-RATIONALP-+))
       (48 48 (:REWRITE REDUCE-RATIONALP-*))
       (48 48 (:REWRITE RATIONALP-MINUS-X))
       (48 48 (:META META-RATIONALP-CORRECT))
       (48 27
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (27 27
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (27 27
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (27 27
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (27 27 (:REWRITE INTEGERP-<-CONSTANT))
       (27 27 (:REWRITE CONSTANT-<-INTEGERP))
       (27 27
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (27 27
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (27 27
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (27 27
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (27 27 (:REWRITE |(< c (- x))|))
       (27 27
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (27 27
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (27 27
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (27 27 (:REWRITE |(< (/ x) (/ y))|))
       (27 27 (:REWRITE |(< (- x) c)|))
       (27 27 (:REWRITE |(< (- x) (- y))|))
       (18 18
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
       (17 17 (:REWRITE SIMPLIFY-SUMS-<))
       (17 17
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
       (17 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (17 17
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (7 7 (:REWRITE |(< (/ x) 0)|))
       (7 7 (:REWRITE |(< (* x y) 0)|))
       (6 6 (:REWRITE |(< 0 (/ x))|))
       (6 6 (:REWRITE |(< 0 (* x y))|))
       (4 4
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (4 4
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (4 4
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (4 4
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (4 4
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (4 4
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (4 4
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (4 4
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (4 4
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (4 4
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (4 4 (:REWRITE |(equal c (/ x))|))
       (4 4 (:REWRITE |(equal c (- x))|))
       (4 4 (:REWRITE |(equal (/ x) c)|))
       (4 4 (:REWRITE |(equal (/ x) (/ y))|))
       (4 4 (:REWRITE |(equal (- x) c)|))
       (4 4 (:REWRITE |(equal (- x) (- y))|)))
(FLOOR-RULE-2
     (60 6 (:REWRITE REDUCE-RATIONALP-*))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (46 8 (:REWRITE RATIONALP-X))
     (34 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (34 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (30 2 (:REWRITE |(equal (if a b c) x)|))
     (24 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (24 2 (:DEFINITION RFIX))
     (18 2 (:REWRITE RATIONALP-/))
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (15 1 (:REWRITE HACK3))
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (13 13 (:REWRITE DEFAULT-TIMES-2))
     (13 13 (:REWRITE DEFAULT-TIMES-1))
     (13 13 (:REWRITE DEFAULT-DIVIDE))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP-/))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|)))
(BAR-2 (236 48 (:REWRITE RATIONALP-X))
       (228 40 (:REWRITE REDUCE-RATIONALP-*))
       (191 191
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
       (191 191
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
       (191 191
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
       (191 191
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
       (172 20 (:REWRITE ACL2-NUMBERP-X))
       (96 8 (:DEFINITION RFIX))
       (72 8 (:REWRITE RATIONALP-/))
       (60 4 (:REWRITE HACK3))
       (48 48 (:REWRITE REDUCE-INTEGERP-+))
       (48 48 (:REWRITE INTEGERP-MINUS-X))
       (48 48 (:META META-INTEGERP-CORRECT))
       (40 40 (:REWRITE REDUCE-RATIONALP-+))
       (40 40 (:REWRITE RATIONALP-MINUS-X))
       (40 40 (:META META-RATIONALP-CORRECT))
       (35 35
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (35 35
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (35 35
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
       (35 35 (:REWRITE INTEGERP-<-CONSTANT))
       (35 35 (:REWRITE CONSTANT-<-INTEGERP))
       (35 35
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (35 35
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
       (35 35
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
       (35 35
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
       (35 35 (:REWRITE |(< c (- x))|))
       (35 35
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
       (35 35
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
       (35 35
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
       (35 35
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
       (35 35 (:REWRITE |(< (/ x) (/ y))|))
       (35 35 (:REWRITE |(< (- x) c)|))
       (35 35 (:REWRITE |(< (- x) (- y))|))
       (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
       (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
       (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
       (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
       (24 24 (:REWRITE SIMPLIFY-SUMS-<))
       (24 24
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
       (24 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (22 22 (:REWRITE DEFAULT-TIMES-2))
       (18 18 (:REWRITE |(< (/ x) 0)|))
       (18 18 (:REWRITE |(< (* x y) 0)|))
       (17 17 (:REWRITE |(< 0 (/ x))|))
       (17 17 (:REWRITE |(< 0 (* x y))|))
       (14 14
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
       (14 14
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
       (13 13
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (13 13
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (11 11
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (11 11
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (11 11
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (11 11
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (11 11 (:REWRITE |(equal c (/ x))|))
       (11 11 (:REWRITE |(equal c (- x))|))
       (11 11 (:REWRITE |(equal (/ x) c)|))
       (11 11 (:REWRITE |(equal (/ x) (/ y))|))
       (11 11 (:REWRITE |(equal (- x) c)|))
       (11 11 (:REWRITE |(equal (- x) (- y))|))
       (10 10
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
       (10 10
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (10 10
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (8 8 (:REWRITE INTEGERP-/))
       (3 3
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
       (2 2 (:REWRITE |(not (equal x (/ y)))|))
       (2 2 (:REWRITE |(equal x (/ y))|)))
(FLOOR-POSITIVE
     (958 118 (:REWRITE ACL2-NUMBERP-X))
     (642 159 (:REWRITE RATIONALP-X))
     (460 58
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (186 186
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (163 163 (:REWRITE REDUCE-INTEGERP-+))
     (163 163 (:REWRITE INTEGERP-MINUS-X))
     (163 163 (:META META-INTEGERP-CORRECT))
     (159 159 (:REWRITE REDUCE-RATIONALP-+))
     (159 159 (:REWRITE REDUCE-RATIONALP-*))
     (159 159 (:REWRITE RATIONALP-MINUS-X))
     (159 159 (:META META-RATIONALP-CORRECT))
     (115 3 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (115 3 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (93 93 (:REWRITE DEFAULT-TIMES-2))
     (90 15 (:REWRITE DEFAULT-FLOOR-RATIO))
     (58 58 (:REWRITE SIMPLIFY-SUMS-<))
     (58 58
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (58 58 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (58 58
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (58 58
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (58 58
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (58 58
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (58 58
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (58 58 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (58 58 (:REWRITE INTEGERP-<-CONSTANT))
     (58 58 (:REWRITE CONSTANT-<-INTEGERP))
     (58 58
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (58 58
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (58 58
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (58 58
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (58 58 (:REWRITE |(< c (- x))|))
     (58 58
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (58 58
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (58 58
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (58 58
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (58 58 (:REWRITE |(< (/ x) (/ y))|))
     (58 58 (:REWRITE |(< (- x) c)|))
     (58 58 (:REWRITE |(< (- x) (- y))|))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (41 41
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (20 20 (:REWRITE |(< 0 (/ x))|))
     (20 20 (:REWRITE |(< 0 (* x y))|))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< (/ x) 0)|))
     (15 15 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:REWRITE DEFAULT-PLUS-2))
     (10 10 (:REWRITE DEFAULT-PLUS-1))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(FLOOR-NEGATIVE
     (848 104 (:REWRITE ACL2-NUMBERP-X))
     (529 130 (:REWRITE RATIONALP-X))
     (351 239
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (312 35
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (311 239
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (311 239
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (262 262
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (262 262
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (262 262
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (262 262
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (137 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (135 135 (:REWRITE REDUCE-INTEGERP-+))
     (135 135 (:REWRITE INTEGERP-MINUS-X))
     (135 135 (:META META-INTEGERP-CORRECT))
     (130 130 (:REWRITE REDUCE-RATIONALP-+))
     (130 130 (:REWRITE REDUCE-RATIONALP-*))
     (130 130 (:REWRITE RATIONALP-MINUS-X))
     (130 130 (:META META-RATIONALP-CORRECT))
     (93 93 (:REWRITE DEFAULT-TIMES-2))
     (90 15 (:REWRITE DEFAULT-FLOOR-RATIO))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (41 41
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (35 35 (:REWRITE SIMPLIFY-SUMS-<))
     (35 35
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (35 35 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (35 35
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (35 35
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 35
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (35 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 35 (:REWRITE INTEGERP-<-CONSTANT))
     (35 35 (:REWRITE CONSTANT-<-INTEGERP))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< c (- x))|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< (/ x) (/ y))|))
     (35 35 (:REWRITE |(< (- x) c)|))
     (35 35 (:REWRITE |(< (- x) (- y))|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (18 18 (:REWRITE |(< 0 (/ x))|))
     (18 18 (:REWRITE |(< 0 (* x y))|))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (17 17 (:REWRITE |(< (/ x) 0)|))
     (17 17 (:REWRITE |(< (* x y) 0)|))
     (12 12 (:REWRITE DEFAULT-PLUS-2))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS)))
(FLOOR-ZERO
     (4609 593 (:REWRITE ACL2-NUMBERP-X))
     (3832 902 (:REWRITE RATIONALP-X))
     (3436 3436
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3436 3436
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (3436 3436
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2284 792
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2284 792
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2007 846 (:REWRITE REDUCE-RATIONALP-*))
     (1744 228
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (1041 32 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (947 947 (:REWRITE DEFAULT-TIMES-2))
     (936 936 (:REWRITE REDUCE-INTEGERP-+))
     (936 936 (:REWRITE INTEGERP-MINUS-X))
     (936 936 (:META META-INTEGERP-CORRECT))
     (846 846 (:REWRITE REDUCE-RATIONALP-+))
     (846 846 (:REWRITE RATIONALP-MINUS-X))
     (846 846 (:META META-RATIONALP-CORRECT))
     (612 58 (:DEFINITION RFIX))
     (504 56 (:REWRITE RATIONALP-/))
     (468 78 (:REWRITE DEFAULT-FLOOR-RATIO))
     (391 41 (:REWRITE HACK3))
     (356 228
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (340 340
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (313 313
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (300 300 (:REWRITE DEFAULT-PLUS-2))
     (300 300 (:REWRITE DEFAULT-PLUS-1))
     (244 244
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (244 244
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (244 244
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (244 244 (:REWRITE INTEGERP-<-CONSTANT))
     (244 244 (:REWRITE CONSTANT-<-INTEGERP))
     (244 244
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (244 244
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (244 244
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (244 244
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (244 244 (:REWRITE |(< c (- x))|))
     (244 244
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (244 244
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (244 244
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (244 244
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (244 244 (:REWRITE |(< (/ x) (/ y))|))
     (244 244 (:REWRITE |(< (- x) c)|))
     (244 244 (:REWRITE |(< (- x) (- y))|))
     (244 228
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (244 228
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (228 228 (:REWRITE SIMPLIFY-SUMS-<))
     (228 67
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (228 67
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (95 95 (:REWRITE |(< (/ x) 0)|))
     (95 95 (:REWRITE |(< (* x y) 0)|))
     (90 90 (:REWRITE |(< 0 (/ x))|))
     (90 90 (:REWRITE |(< 0 (* x y))|))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (86 86
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (86 86
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (71 71
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (71 71
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (71 71
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (71 71 (:REWRITE |(equal c (/ x))|))
     (71 71 (:REWRITE |(equal c (- x))|))
     (71 71 (:REWRITE |(equal (/ x) c)|))
     (71 71 (:REWRITE |(equal (/ x) (/ y))|))
     (71 71 (:REWRITE |(equal (- x) c)|))
     (71 71 (:REWRITE |(equal (- x) (- y))|))
     (67 67
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (67 67 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (56 56 (:REWRITE INTEGERP-/))
     (25 25
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (25 25 (:REWRITE NORMALIZE-ADDENDS))
     (16 16
         (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (8 8 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD))
     (4 4 (:REWRITE |(equal (* x y) 0)|))
     (4 4
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (4 4
        (:REWRITE |(< 0 (* x (/ y))) rationalp (* x (/ y))|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4
        (:REWRITE |(< (* x (/ y)) 0) rationalp (* x (/ y))|))
     (1 1 (:REWRITE FLOOR-POSITIVE . 4))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 4))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 2)))