(NEXT-TOTAL (1 1 (:TYPE-PRESCRIPTION NEXT-TOTAL)))
(PRE-TOTAL)
(EXTERNAL-TOTAL)
(POST-TOTAL)
(INV-TOTAL)
(M)
(PRE-TOTAL-IMPLIES-INV-TOTAL)
(INV-TOTAL-IS-INVARIANT)
(INV-TOTAL-AND-EXTERNAL-TOTAL-IMPLIES-POST-TOTAL)
(INV-TOTAL-IMPLIES-NOT-EXTERNAL-TOTAL)
(M-IS-AN-ORDINAL)
(INTERNAL-STEPS-DECREASE-M)
(RUN-TOTAL (17 9 (:REWRITE DEFAULT-+-2))
           (12 9 (:REWRITE DEFAULT-+-1))
           (8 2 (:REWRITE COMMUTATIVITY-OF-+))
           (8 1 (:DEFINITION LENGTH))
           (7 6 (:REWRITE DEFAULT-<-1))
           (6 6 (:REWRITE DEFAULT-<-2))
           (5 1 (:DEFINITION LEN))
           (2 2 (:REWRITE FOLD-CONSTS-IN-+))
           (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
           (2 2 (:REWRITE DEFAULT-CDR))
           (1 1 (:TYPE-PRESCRIPTION LEN))
           (1 1 (:REWRITE ZP-OPEN))
           (1 1 (:REWRITE DEFAULT-REALPART))
           (1 1 (:REWRITE DEFAULT-NUMERATOR))
           (1 1 (:REWRITE DEFAULT-IMAGPART))
           (1 1 (:REWRITE DEFAULT-DENOMINATOR))
           (1 1 (:REWRITE DEFAULT-COERCE-2))
           (1 1 (:REWRITE DEFAULT-COERCE-1))
           (1 1 (:REWRITE DEFAULT-CAR)))
(CLOCK-TOTAL--FN-AUX (4 2
                        (:REWRITE INV-TOTAL-IMPLIES-NOT-EXTERNAL-TOTAL))
                     (2 2
                        (:REWRITE PRE-TOTAL-IMPLIES-INV-TOTAL))
                     (2 1 (:REWRITE INV-TOTAL-IS-INVARIANT)))
(CLOCK-TOTAL--FN)
(INV-TOTAL-RUN-TOTAL-1 (76 4 (:REWRITE ZP-OPEN))
                       (19 19
                           (:REWRITE PRE-TOTAL-IMPLIES-INV-TOTAL))
                       (10 7 (:REWRITE DEFAULT-+-2))
                       (8 4 (:REWRITE SIMPLIFY-SUMS-<))
                       (8 4
                          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                       (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                       (8 4 (:REWRITE DEFAULT-<-2))
                       (7 7
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (7 7 (:REWRITE NORMALIZE-ADDENDS))
                       (7 7 (:REWRITE DEFAULT-+-1))
                       (4 4
                          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                       (4 4
                          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                       (4 4
                          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                       (4 4 (:REWRITE DEFAULT-<-1))
                       (4 4 (:REWRITE |(< 0 (- x))|))
                       (4 4 (:REWRITE |(< (- x) (- y))|)))
(INV-TOTAL-RUN-TOTAL-2 (76 4 (:REWRITE ZP-OPEN))
                       (19 19
                           (:REWRITE PRE-TOTAL-IMPLIES-INV-TOTAL))
                       (10 7 (:REWRITE DEFAULT-+-2))
                       (8 4 (:REWRITE SIMPLIFY-SUMS-<))
                       (8 4
                          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                       (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                       (8 4 (:REWRITE DEFAULT-<-2))
                       (7 7
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (7 7 (:REWRITE NORMALIZE-ADDENDS))
                       (7 7 (:REWRITE DEFAULT-+-1))
                       (6 4 (:REWRITE INV-TOTAL-RUN-TOTAL-1))
                       (4 4
                          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                       (4 4
                          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                       (4 4
                          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                       (4 4 (:REWRITE DEFAULT-<-1))
                       (4 4 (:REWRITE |(< 0 (- x))|))
                       (4 4 (:REWRITE |(< (- x) (- y))|)))
(NEXT-TOTAL-RUN-TOTAL-IS-RUN-TOTAL-1
     (8 8 (:REWRITE ZP-OPEN))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE |(equal (- x) (- y))|)))
(CLOCK-TOTAL--FN-IS-NATP)
(STANDARD-THEOREM-ABOUT-CLOCK-TOTAL-S-1
     (27 1 (:DEFINITION RUN-TOTAL))
     (19 1 (:REWRITE ZP-OPEN))
     (12 1 (:DEFINITION CLOCK-TOTAL--FN-AUX))
     (5 3 (:REWRITE DEFAULT-+-2))
     (5 2
        (:REWRITE INV-TOTAL-IMPLIES-NOT-EXTERNAL-TOTAL))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE INV-TOTAL-IS-INVARIANT))
     (2 1 (:REWRITE SIMPLIFY-SUMS-<))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-<-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(STANDARD-THEOREM-ABOUT-CLOCK-TOTAL-S-2
     (27 1 (:DEFINITION RUN-TOTAL))
     (19 1 (:REWRITE ZP-OPEN))
     (12 1 (:DEFINITION CLOCK-TOTAL--FN-AUX))
     (5 3 (:REWRITE DEFAULT-+-2))
     (5 2
        (:REWRITE INV-TOTAL-IMPLIES-NOT-EXTERNAL-TOTAL))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE INV-TOTAL-IS-INVARIANT))
     (2 1 (:REWRITE SIMPLIFY-SUMS-<))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-<-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(CLOCK-TOTAL--FN-IS-MINIMUM
     (28 28
         (:REWRITE PRE-TOTAL-IMPLIES-INV-TOTAL))
     (28 14
         (:REWRITE INV-TOTAL-IMPLIES-NOT-EXTERNAL-TOTAL))
     (20 16
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (19 11
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (19 11 (:REWRITE DEFAULT-+-2))
     (18 16
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (17 10 (:REWRITE SIMPLIFY-SUMS-<))
     (17 10 (:REWRITE DEFAULT-<-1))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE DEFAULT-+-1))
     (11 11 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (3 3 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< d (+ c x))|)))
(STANDARD-THEOREM-ABOUT-CLOCK-TOTAL-S-3
     (41 24 (:REWRITE DEFAULT-+-2))
     (27 10 (:REWRITE |(< d (+ c x))|))
     (25 13 (:REWRITE ZP-OPEN))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24 (:REWRITE NORMALIZE-ADDENDS))
     (24 24 (:REWRITE DEFAULT-+-1))
     (19 11 (:REWRITE DEFAULT-<-2))
     (17 13
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (16 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (15 13
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (14 11 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12 (:REWRITE |(< (- x) (- y))|))
     (11 11 (:REWRITE DEFAULT-<-1))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
     (2 2 (:REWRITE |(< (+ c x) d)|))
     (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
     (1 1 (:REWRITE |(+ 0 x)|)))