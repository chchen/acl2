(INTEGERP-1/2-X-REQUIRES-INTEGERP-X
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE DEFAULT-IMAGPART))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(EVENP-IS-LOGBITP (8 7 (:REWRITE DEFAULT-*-2))
                  (8 7 (:REWRITE DEFAULT-*-1))
                  (5 5
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                  (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
                  (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(EXPT-FALLBACK (32 8 (:DEFINITION O-FIRST-EXPT))
               (22 22 (:REWRITE DEFAULT-CAR))
               (20 5 (:DEFINITION O-FIRST-COEFF))
               (16 14 (:REWRITE DEFAULT-<-2))
               (16 14 (:REWRITE DEFAULT-<-1))
               (9 9 (:REWRITE DEFAULT-CDR))
               (8 4 (:DEFINITION O-RST))
               (6 6
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (5 5 (:REWRITE DEFAULT-+-2))
               (5 5 (:REWRITE DEFAULT-+-1))
               (4 4 (:TYPE-PRESCRIPTION ABS))
               (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
               (4 1 (:DEFINITION NATP))
               (3 1 (:DEFINITION POSP))
               (2 2 (:REWRITE ZIP-OPEN)))
(EXPT-FALLBACK-IS-EXPT (40 12 (:REWRITE DEFAULT-*-2))
                       (24 8 (:REWRITE COMMUTATIVITY-OF-+))
                       (19 19
                           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (18 6 (:REWRITE DEFAULT-UNARY-/))
                       (16 16 (:REWRITE DEFAULT-+-2))
                       (16 16 (:REWRITE DEFAULT-+-1))
                       (16 12 (:REWRITE DEFAULT-*-1))
                       (10 10 (:REWRITE DEFAULT-<-2))
                       (10 10 (:REWRITE DEFAULT-<-1))
                       (8 8 (:REWRITE ZIP-OPEN)))
(OPTIMIZE-EXPT-2-FOR-GL
     (118 3 (:DEFINITION EXPT))
     (43 43
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (36 7 (:REWRITE DEFAULT-*-2))
     (23 23
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (20 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
     (15 5 (:REWRITE COMMUTATIVITY-OF-+))
     (12 7 (:REWRITE DEFAULT-*-1))
     (12 2 (:REWRITE DEFAULT-UNARY-/))
     (10 10 (:REWRITE DEFAULT-+-2))
     (10 10 (:REWRITE DEFAULT-+-1))
     (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (8 8
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE DEFAULT-NUMERATOR))
     (4 2 (:DEFINITION NOT))
     (3 3 (:REWRITE ZIP-OPEN))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
     (1 1 (:REWRITE NATP-RW)))
(ASH-OF-NEGATIVE-1 (524 18 (:REWRITE FLOOR-ZERO . 3))
                   (359 18 (:REWRITE CANCEL-FLOOR-+))
                   (286 18 (:REWRITE FLOOR-ZERO . 4))
                   (223 223
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (223 223
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (223 223
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (200 8 (:LINEAR FLOOR-BOUNDS-3))
                   (200 8 (:LINEAR FLOOR-BOUNDS-2))
                   (165 9 (:REWRITE FLOOR-X-1))
                   (160 160
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (160 160
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (160 160
                        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (106 106 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                   (106 106 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                   (106 106
                        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                   (83 23 (:REWRITE SIMPLIFY-SUMS-<))
                   (83 23
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (83 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (68 60 (:REWRITE DEFAULT-*-2))
                   (63 23 (:REWRITE DEFAULT-<-1))
                   (60 60
                       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (60 60 (:REWRITE DEFAULT-*-1))
                   (58 18 (:REWRITE FLOOR-ZERO . 2))
                   (58 18 (:REWRITE FLOOR-MINUS-WEAK))
                   (58 18 (:REWRITE FLOOR-MINUS-2))
                   (58 18 (:REWRITE FLOOR-COMPLETION))
                   (58 18 (:REWRITE FLOOR-CANCEL-*-WEAK))
                   (44 44 (:REWRITE REDUCE-INTEGERP-+))
                   (44 44 (:REWRITE INTEGERP-MINUS-X))
                   (44 44 (:META META-INTEGERP-CORRECT))
                   (43 43 (:REWRITE |(integerp (* c x))|))
                   (43 23 (:REWRITE DEFAULT-<-2))
                   (42 8 (:REWRITE DEFAULT-+-2))
                   (29 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (29 1
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (29 1
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (23 23
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (23 23 (:REWRITE |(< (- x) (- y))|))
                   (9 9
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (8 8
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (8 8 (:REWRITE NORMALIZE-ADDENDS))
                   (8 8 (:REWRITE DEFAULT-+-1))
                   (5 5
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (5 5 (:REWRITE |(< 0 (- x))|))
                   (4 4
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (4 4 (:REWRITE |(< 0 (* x y))|))
                   (4 4 (:REWRITE |(< (- x) 0)|))
                   (4 4 (:REWRITE |(< (* x y) 0)|))
                   (1 1 (:REWRITE |(equal (- x) (- y))|)))
(NONNEGATIVE-INTEGER-QUOTIENT-OF-2
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (211 211
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (146 146 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (146 146
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (146 146
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (146 146
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (145 145 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (145 145
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (145 145
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (130 130
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (123 13 (:REWRITE FLOOR-ZERO . 4))
     (84 50 (:REWRITE DEFAULT-+-2))
     (84 4 (:LINEAR FLOOR-BOUNDS-3))
     (84 4 (:LINEAR FLOOR-BOUNDS-2))
     (74 74
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (74 74 (:REWRITE DEFAULT-*-2))
     (74 74 (:REWRITE DEFAULT-*-1))
     (63 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (51 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (50 50
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (50 50
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (50 50 (:REWRITE DEFAULT-+-1))
     (45 45 (:REWRITE |(< (- x) (- y))|))
     (38 38 (:REWRITE DEFAULT-<-2))
     (38 38 (:REWRITE DEFAULT-<-1))
     (29 29 (:REWRITE REDUCE-INTEGERP-+))
     (29 29 (:REWRITE INTEGERP-MINUS-X))
     (29 29 (:META META-INTEGERP-CORRECT))
     (21 21 (:REWRITE |(integerp (* c x))|))
     (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (15 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (13 13 (:REWRITE FLOOR-MINUS-WEAK))
     (13 13 (:REWRITE FLOOR-MINUS-2))
     (13 13 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (13 2 (:REWRITE |(equal (+ c x) d)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (12 12 (:REWRITE FLOOR-ZERO . 2))
     (12 12 (:REWRITE FLOOR-COMPLETION))
     (12 12 (:REWRITE |(< 0 (- x))|))
     (11 11 (:REWRITE |(equal (- x) (- y))|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 8 (:REWRITE |(< (- x) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (4 4 (:REWRITE DEFAULT-UNARY-/))
     (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (3 3 (:REWRITE |(equal (- x) 0)|))
     (3 3 (:REWRITE |(< d (+ c x))|)))
(LOGCOUNT-OF-NATURAL (88 2 (:REWRITE FLOOR-ZERO . 3))
                     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (44 2 (:REWRITE CANCEL-FLOOR-+))
                     (34 2 (:REWRITE FLOOR-X-1))
                     (30 6 (:REWRITE SIMPLIFY-SUMS-<))
                     (30 6
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                     (30 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                     (30 6 (:REWRITE DEFAULT-<-1))
                     (27 1 (:LINEAR FLOOR-BOUNDS-3))
                     (27 1 (:LINEAR FLOOR-BOUNDS-2))
                     (18 18 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                     (18 18 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                     (18 18
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                     (18 2 (:REWRITE FLOOR-ZERO . 4))
                     (10 2 (:REWRITE FLOOR-ZERO . 2))
                     (10 2 (:REWRITE FLOOR-MINUS-WEAK))
                     (10 2 (:REWRITE FLOOR-MINUS-2))
                     (10 2 (:REWRITE FLOOR-COMPLETION))
                     (10 2 (:REWRITE FLOOR-CANCEL-*-WEAK))
                     (8 8
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                     (8 8
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (8 8 (:REWRITE DEFAULT-*-2))
                     (8 8 (:REWRITE DEFAULT-*-1))
                     (6 6
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                     (6 6 (:REWRITE REDUCE-INTEGERP-+))
                     (6 6 (:REWRITE INTEGERP-MINUS-X))
                     (6 6 (:REWRITE DEFAULT-<-2))
                     (6 6 (:REWRITE |(integerp (* c x))|))
                     (6 6 (:REWRITE |(< (- x) (- y))|))
                     (6 6 (:META META-INTEGERP-CORRECT))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (2 2
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                     (2 2 (:REWRITE |(< (- x) 0)|))
                     (1 1 (:REWRITE ZP-OPEN))
                     (1 1
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                     (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
                     (1 1 (:REWRITE FLOOR-NEGATIVE . 2))
                     (1 1 (:REWRITE |(< 0 (- x))|)))
(LOGCOUNT-OF-NATURAL-CORRECT
     (64 2 (:REWRITE FLOOR-FLOOR-INTEGER-ALT))
     (55 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (45 6 (:REWRITE FLOOR-ZERO . 3))
     (42 1 (:REWRITE ZP-OPEN))
     (39 29 (:REWRITE DEFAULT-*-2))
     (36 4 (:REWRITE |(* (* x y) z)|))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (29 29 (:REWRITE DEFAULT-*-1))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (18 1 (:REWRITE FLOOR-POSITIVE . 1))
     (16 4 (:REWRITE |(* c (* d x))|))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 12
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (11 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (11 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (11 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (8 4 (:REWRITE DEFAULT-+-2))
     (7 7
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE FLOOR-ZERO . 4))
     (6 6 (:REWRITE FLOOR-ZERO . 2))
     (6 6 (:REWRITE FLOOR-MINUS-WEAK))
     (6 6 (:REWRITE FLOOR-MINUS-2))
     (6 6 (:REWRITE FLOOR-COMPLETION))
     (6 6 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (6 6 (:REWRITE |(integerp (* c x))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 1 (:REWRITE |(- (* c x))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE |(< (- x) 0)|))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE ZIP-OPEN))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 1 (:REWRITE |(+ (* c x) (* d x))|))
     (1 1 (:REWRITE FLOOR-POSITIVE . 3))
     (1 1 (:REWRITE FLOOR-POSITIVE . 2))
     (1 1 (:REWRITE |(* 0 x)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(LOGCOUNT-FOR-GL)
(CROCK (1 1
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
       (1 1 (:REWRITE SIMPLIFY-SUMS-<))
       (1 1
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
       (1 1
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
       (1 1
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
       (1 1 (:REWRITE REDUCE-INTEGERP-+))
       (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
       (1 1
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
       (1 1 (:REWRITE NORMALIZE-ADDENDS))
       (1 1 (:REWRITE INTEGERP-MINUS-X))
       (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
       (1 1 (:REWRITE DEFAULT-<-2))
       (1 1 (:REWRITE DEFAULT-<-1))
       (1 1 (:REWRITE DEFAULT-+-2))
       (1 1 (:REWRITE DEFAULT-+-1))
       (1 1 (:REWRITE |(< (- x) 0)|))
       (1 1 (:REWRITE |(< (- x) (- y))|))
       (1 1 (:META META-INTEGERP-CORRECT)))
(LOGCOUNT-FOR-GL-CORRECT
     (615 10
          (:REWRITE NONNEGATIVE-INTEGER-QUOTIENT-OF-2))
     (317 8 (:REWRITE FLOOR-MINUS-WEAK))
     (271 13 (:REWRITE CANCEL-FLOOR-+))
     (267 6
          (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (254 5 (:DEFINITION EVENP))
     (183 6 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (156 36 (:REWRITE |(* (- x) y)|))
     (114 6 (:REWRITE |(* (+ x y) z)|))
     (111 24 (:REWRITE |(- (* c x))|))
     (107 14 (:REWRITE INTEGERP-MINUS-X))
     (104 26 (:REWRITE |(* y x)|))
     (93 28 (:REWRITE DEFAULT-+-2))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (58 22 (:REWRITE DEFAULT-UNARY-MINUS))
     (54 6 (:REWRITE |(< (+ c x) d)|))
     (52 5 (:REWRITE FLOOR-ZERO . 3))
     (50 50
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (50 50 (:REWRITE DEFAULT-*-2))
     (50 50 (:REWRITE DEFAULT-*-1))
     (43 33 (:REWRITE NORMALIZE-ADDENDS))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28 (:REWRITE DEFAULT-+-1))
     (26 26 (:META META-INTEGERP-CORRECT))
     (24 6 (:REWRITE |(* c (* d x))|))
     (22 7 (:REWRITE ZIP-OPEN))
     (19 19
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (18 3 (:REWRITE |(- (+ x y))|))
     (17 17
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (15 3 (:REWRITE |(equal (+ c x) d)|))
     (15 3 (:REWRITE |(+ (+ x y) z)|))
     (14 14 (:REWRITE |(integerp (* c x))|))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 13 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE DEFAULT-<-1))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 6 (:REWRITE |(* -1 x)|))
     (10 5 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (8 8 (:REWRITE FLOOR-MINUS-2))
     (8 8 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (8 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 5
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE |(- (- x))|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE FLOOR-ZERO . 4))
     (5 5 (:REWRITE FLOOR-ZERO . 2))
     (5 5 (:REWRITE FLOOR-COMPLETION))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE |(< (- x) 0)|))
     (5 5 (:REWRITE |(+ x (- x))|))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (3 3
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3 3 (:TYPE-PRESCRIPTION FLOOR))
     (2 2 (:REWRITE |(+ 0 x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1 1 (:REWRITE |(equal (- x) 0)|)))
(NONNEGATIVE-INTEGER-QUOTIENT-FOR-GL
     (554 84 (:REWRITE DEFAULT-UNARY-/))
     (485 24 (:REWRITE FLOOR-ZERO . 3))
     (387 24 (:REWRITE FLOOR-ZERO . 4))
     (336 32 (:REWRITE |(* x (if a b c))|))
     (334 9 (:LINEAR FLOOR-BOUNDS-3))
     (334 9 (:LINEAR FLOOR-BOUNDS-2))
     (304 93 (:REWRITE |(* (if a b c) x)|))
     (299 299
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (299 299
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (299 299
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (213 213
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (206 206 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (206 206
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (206 206
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (206 206
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (205 205
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (205 205
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (194 24 (:REWRITE FLOOR-ZERO . 2))
     (192 192
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (179 157 (:REWRITE DEFAULT-<-2))
     (176 95
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (174 174 (:REWRITE |(< (- x) (- y))|))
     (171 157 (:REWRITE DEFAULT-<-1))
     (164 94 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (160 32 (:REWRITE |(/ (if a b c))|))
     (149 67 (:REWRITE DEFAULT-+-2))
     (137 113 (:REWRITE DEFAULT-*-1))
     (133 113 (:REWRITE DEFAULT-*-2))
     (124 116 (:REWRITE INTEGERP-MINUS-X))
     (116 116 (:META META-INTEGERP-CORRECT))
     (113 113
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (95 95 (:REWRITE |(equal (- x) (- y))|))
     (86 86
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (86 86 (:REWRITE |(equal (- x) 0)|))
     (84 84
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (78 78 (:REWRITE |(< (- x) 0)|))
     (73 73
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (67 67
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (67 67 (:REWRITE DEFAULT-+-1))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (53 53 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (46 24 (:REWRITE FLOOR-MINUS-WEAK))
     (46 24 (:REWRITE FLOOR-MINUS-2))
     (46 24 (:REWRITE FLOOR-COMPLETION))
     (46 24 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (45 45 (:REWRITE |(< 0 (- x))|))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (32 2 (:REWRITE |(+ x (if a b c))|))
     (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
     (28 28 (:REWRITE |(integerp (* c x))|))
     (18 3 (:REWRITE |(* y (* x z))|))
     (17 17 (:REWRITE |(* c (* d x))|))
     (13 2 (:REWRITE |(equal (+ c x) d)|))
     (11 11 (:REWRITE |(< (+ c x) d)|))
     (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (3 3
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (3 3 (:REWRITE |(< d (+ c x))|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(- (if a b c))|))
     (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
     (1 1 (:REWRITE |(< (+ c x) (+ d y))|))
     (1 1 (:REWRITE |(< (+ c x y) d)|)))
(LOGCAR-FOR-GL (64 2
                   (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
               (50 5 (:REWRITE BFIX-WHEN-NOT-1))
               (28 28 (:TYPE-PRESCRIPTION BITP))
               (28 10 (:REWRITE BITOPS::LOGCAR-OF-BIT))
               (28 2
                   (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
               (20 4 (:LINEAR BITOPS::LOGCAR-BOUND))
               (15 15
                   (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
               (15 5 (:REWRITE BITOPS::LOGCDR-OF-BIT))
               (14 2 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
               (10 10
                   (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
               (10 5
                   (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
               (10 5 (:REWRITE BFIX-WHEN-NOT-BITP))
               (10 5 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
               (10 5 (:REWRITE BFIX-WHEN-BIT->BOOL))
               (10 2
                   (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
               (8 2 (:REWRITE NEGP-WHEN-LESS-THAN-0))
               (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
               (6 4 (:REWRITE DEFAULT-<-1))
               (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
               (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
               (4 4 (:REWRITE DEFAULT-<-2))
               (4 2 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
               (2 2 (:TYPE-PRESCRIPTION NEGP))
               (2 2
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (2 2 (:REWRITE NEGP-WHEN-INTEGERP))
               (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
               (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(LOGCDR-FOR-GL (26 13
                   (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
               (15 15
                   (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
               (13 13 (:TYPE-PRESCRIPTION NATP))
               (4 2 (:REWRITE BITOPS::LOGCDR-OF-BIT))
               (4 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
               (2 2 (:TYPE-PRESCRIPTION BITP)))
(LOGCONS-FOR-GL (66 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
                (62 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
                (54 3 (:LINEAR BITOPS::BFIX-BOUND))
                (53 8 (:REWRITE BFIX-WHEN-NOT-1))
                (52 4 (:REWRITE BITOPS::ASH-<-0))
                (52 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
                (32 17 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                (31 31
                    (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
                (30 30 (:TYPE-PRESCRIPTION BITP))
                (28 28 (:TYPE-PRESCRIPTION NATP))
                (28 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
                (26 13
                    (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
                (26 13
                    (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
                (26 13
                    (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
                (19 8 (:REWRITE BFIX-WHEN-NOT-BITP))
                (16 16
                    (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                (16 8 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                (16 8 (:REWRITE BFIX-WHEN-BIT->BOOL))
                (16 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
                (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
                (13 13 (:TYPE-PRESCRIPTION POSP))
                (13 5 (:REWRITE BFIX-BITP))
                (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
                (8 6 (:REWRITE DEFAULT-<-1))
                (6 6 (:REWRITE DEFAULT-<-2))
                (5 1 (:LINEAR BITOPS::LOGCAR-BOUND))
                (4 4 (:REWRITE NEGP-WHEN-INTEGERP))
                (4 2
                   (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                (4 1 (:REWRITE BFIX-EQUAL-1))
                (3 1 (:DEFINITION BIT->BOOL$INLINE))
                (1 1
                   (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT)))
(ENSURE-NEGATIVE (10 5
                     (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
                 (5 5 (:TYPE-PRESCRIPTION NATP))
                 (5 5
                    (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP)))
(ENSURE-NEGATIVE-WHEN-NEGATIVE (4 1 (:REWRITE NEGP-WHEN-LESS-THAN-0))
                               (2 2 (:REWRITE DEFAULT-<-2))
                               (2 2 (:REWRITE DEFAULT-<-1))
                               (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
                               (1 1 (:REWRITE NEGP-WHEN-INTEGERP)))
(LOGTAIL-FOR-GL (64 2 (:REWRITE LOGTAIL-IDENTITY))
                (58 2 (:DEFINITION UNSIGNED-BYTE-P))
                (56 28
                    (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
                (53 2 (:DEFINITION INTEGER-RANGE-P))
                (28 28 (:TYPE-PRESCRIPTION NATP))
                (14 8 (:REWRITE DEFAULT-<-2))
                (11 2 (:LINEAR EXPT->-1))
                (10 10
                    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
                (10 10
                    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
                (10 10
                    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
                (8 8 (:REWRITE DEFAULT-<-1))
                (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
                (8 2 (:REWRITE ZP-WHEN-GT-0))
                (4 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                (4 4
                   (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
                (2 2 (:REWRITE ZP-WHEN-INTEGERP))
                (2 2 (:REWRITE ZP-OPEN))
                (2 2
                   (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT)))
(LOGHEAD-FOR-GL)