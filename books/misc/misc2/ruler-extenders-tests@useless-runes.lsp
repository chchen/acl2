(FIB)
(FIB (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(FIB1 (3 3 (:REWRITE DEFAULT-<-2))
      (3 3 (:REWRITE DEFAULT-<-1))
      (2 2 (:REWRITE DEFAULT-+-2))
      (2 2 (:REWRITE DEFAULT-+-1))
      (1 1 (:REWRITE ZP-OPEN))
      (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(FIB2 (7 7 (:REWRITE DEFAULT-<-2))
      (7 7 (:REWRITE DEFAULT-<-1))
      (2 2 (:REWRITE ZP-OPEN))
      (2 2 (:REWRITE DEFAULT-+-2))
      (2 2 (:REWRITE DEFAULT-+-1)))
(FOOP)
(OUR-TEST)
(APP)
(H)
(BAR (294 133 (:REWRITE DEFAULT-+-2))
     (185 133 (:REWRITE DEFAULT-+-1))
     (104 26 (:REWRITE COMMUTATIVITY-OF-+))
     (104 26 (:DEFINITION INTEGER-ABS))
     (104 13 (:DEFINITION LENGTH))
     (65 13 (:DEFINITION LEN))
     (44 32 (:REWRITE DEFAULT-<-2))
     (36 32 (:REWRITE DEFAULT-<-1))
     (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
     (20 20 (:REWRITE DEFAULT-CAR))
     (13 13 (:TYPE-PRESCRIPTION LEN))
     (13 13 (:REWRITE DEFAULT-REALPART))
     (13 13 (:REWRITE DEFAULT-NUMERATOR))
     (13 13 (:REWRITE DEFAULT-IMAGPART))
     (13 13 (:REWRITE DEFAULT-DENOMINATOR))
     (13 13 (:REWRITE DEFAULT-COERCE-2))
     (13 13 (:REWRITE DEFAULT-COERCE-1)))
(F)
(F)
(F)
(F1)
(F-IS-F1 (19 13 (:REWRITE DEFAULT-CDR))
         (12 6 (:REWRITE DEFAULT-CAR)))
(FACT)
(FACT)
(F2 (5 5 (:REWRITE DEFAULT-<-2))
    (5 5 (:REWRITE DEFAULT-<-1))
    (5 4 (:REWRITE DEFAULT-+-2))
    (4 4 (:REWRITE DEFAULT-+-1))
    (1 1
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
    (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(F3)
(F4 (484 222 (:REWRITE DEFAULT-+-2))
    (309 222 (:REWRITE DEFAULT-+-1))
    (176 44 (:REWRITE COMMUTATIVITY-OF-+))
    (176 44 (:DEFINITION INTEGER-ABS))
    (176 22 (:DEFINITION LENGTH))
    (110 22 (:DEFINITION LEN))
    (75 55 (:REWRITE DEFAULT-<-2))
    (63 55 (:REWRITE DEFAULT-<-1))
    (44 44 (:REWRITE DEFAULT-UNARY-MINUS))
    (34 34 (:REWRITE DEFAULT-CAR))
    (22 22 (:TYPE-PRESCRIPTION LEN))
    (22 22 (:REWRITE DEFAULT-REALPART))
    (22 22 (:REWRITE DEFAULT-NUMERATOR))
    (22 22 (:REWRITE DEFAULT-IMAGPART))
    (22 22 (:REWRITE DEFAULT-DENOMINATOR))
    (22 22 (:REWRITE DEFAULT-COERCE-2))
    (22 22 (:REWRITE DEFAULT-COERCE-1)))