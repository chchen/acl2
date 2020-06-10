(X86ISA::ELF-READ-MEM-NULL-TERM
     (66 33
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (16 2 (:REWRITE NFIX-WHEN-NOT-NATP))
     (15 3 (:DEFINITION LEN))
     (14 11 (:REWRITE DEFAULT-+-2))
     (14 1 (:DEFINITION NTHCDR))
     (11 11 (:REWRITE DEFAULT-+-1))
     (11 3 (:REWRITE NATP-WHEN-INTEGERP))
     (8 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 1 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 1 (:REWRITE ZP-WHEN-INTEGERP))
     (3 1 (:REWRITE ZP-WHEN-GT-0))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(X86ISA::ELF-READ-STRING-NULL-TERM)
(X86ISA::READ-SEGMENT-HEADERS-64
     (107 1 (:DEFINITION X86ISA::BYTE-LISTP))
     (104 1 (:DEFINITION X86ISA::N08P$INLINE))
     (73 2
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
     (70 1
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
     (42 2 (:DEFINITION UNSIGNED-BYTE-P))
     (40 2 (:DEFINITION INTEGER-RANGE-P))
     (30 4
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (22 2 (:DEFINITION INTEGER-LISTP))
     (14 14 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (9 9 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
     (6 2
        (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 4
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 1 (:REWRITE ZP-WHEN-GT-0))
     (3 1 (:DEFINITION TRUE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
     (2 2 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
     (1 1 (:REWRITE ZP-WHEN-INTEGERP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(X86ISA::READ-SEGMENT-HEADERS-32
     (107 1 (:DEFINITION X86ISA::BYTE-LISTP))
     (104 1 (:DEFINITION X86ISA::N08P$INLINE))
     (73 2
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
     (70 1
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
     (42 2 (:DEFINITION UNSIGNED-BYTE-P))
     (40 2 (:DEFINITION INTEGER-RANGE-P))
     (30 4
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (22 2 (:DEFINITION INTEGER-LISTP))
     (14 14 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (9 9 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
     (6 2
        (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
     (5 5 (:REWRITE DEFAULT-<-2))
     (5 5 (:REWRITE DEFAULT-<-1))
     (4 4
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 1 (:REWRITE ZP-WHEN-GT-0))
     (3 1 (:DEFINITION TRUE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
     (2 2 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
     (1 1 (:REWRITE ZP-WHEN-INTEGERP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(X86ISA::READ-SECTION-HEADERS
     (107 1 (:DEFINITION X86ISA::BYTE-LISTP))
     (104 1 (:DEFINITION X86ISA::N08P$INLINE))
     (73 2
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
     (70 1
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
     (42 2 (:DEFINITION UNSIGNED-BYTE-P))
     (40 2 (:DEFINITION INTEGER-RANGE-P))
     (30 4
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (22 2 (:DEFINITION INTEGER-LISTP))
     (14 14 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (9 9 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 2 (:REWRITE ZP-WHEN-GT-0))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
     (6 2
        (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
     (6 2
        (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
     (4 4
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 1 (:DEFINITION TRUE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
     (2 2 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
     (2 2 (:REWRITE ZP-WHEN-INTEGERP))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
     (2 1
        (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
     (1 1
        (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP)))
(X86ISA::READ-ELF-HEADER)
(X86ISA::READ-SECTION-NAMES)
(X86ISA::SET-STOBJ-FIELDS
     (280 140
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (140 140 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (8 8
        (:TYPE-PRESCRIPTION X86ISA::BYTE-LISTP-OF-STRING-TO-BYTES)))
(X86ISA::ELF-FILE-READ (12 6
                           (:TYPE-PRESCRIPTION X86ISA::NATP-COMBINE-BYTES))
                       (6 6
                          (:TYPE-PRESCRIPTION X86ISA::BYTE-LISTP)))
(X86ISA::ELF-LOAD-TEXT-SECTION
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::NTH-OF-NAT-LISTP-WITHIN-BOUNDS))
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (60606 60606 (:TYPE-PRESCRIPTION NAT-LISTP))
  (15368 136
         (:LINEAR X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (12159 318
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
  (11682 159
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
  (5506 636
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (4050 318 (:DEFINITION INTEGER-LISTP))
  (2226 2226 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (1460 730
        (:TYPE-PRESCRIPTION X86ISA::X86$CP-IMPLIES-NATP-NEXT-ADDR))
  (1431 1431
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
  (954 318
       (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
  (812 803 (:REWRITE DEFAULT-<-1))
  (803 803 (:REWRITE DEFAULT-<-2))
  (738 738 (:TYPE-PRESCRIPTION X86ISA::X86$CP))
  (713 713 (:REWRITE DEFAULT-CDR))
  (636 636
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (636 318
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (478 478 (:REWRITE DEFAULT-CAR))
  (477 477
       (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
  (35 7 (:DEFINITION LEN))
  (27 14 (:REWRITE DEFAULT-+-2))
  (15 14 (:REWRITE DEFAULT-+-1))
  (12 4
      (:REWRITE X86ISA::MEM-ARRAY-NEXT-ADDR-IS-EXPECTED-MEM-ARRAY-NEXT-ADDR))
  (4 4
     (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
  (3 1 (:REWRITE NATP-WHEN-GTE-0))
  (3 1 (:DEFINITION TRUE-LISTP))
  (2 2
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
  (1 1 (:REWRITE NATP-WHEN-INTEGERP))
  (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(X86ISA::ELF-LOAD-DATA-SECTION
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::NTH-OF-NAT-LISTP-WITHIN-BOUNDS))
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (60606 60606 (:TYPE-PRESCRIPTION NAT-LISTP))
  (15368 136
         (:LINEAR X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (12159 318
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
  (11682 159
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
  (5506 636
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (4050 318 (:DEFINITION INTEGER-LISTP))
  (2226 2226 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (1460 730
        (:TYPE-PRESCRIPTION X86ISA::X86$CP-IMPLIES-NATP-NEXT-ADDR))
  (1431 1431
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
  (954 318
       (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
  (812 803 (:REWRITE DEFAULT-<-1))
  (803 803 (:REWRITE DEFAULT-<-2))
  (738 738 (:TYPE-PRESCRIPTION X86ISA::X86$CP))
  (713 713 (:REWRITE DEFAULT-CDR))
  (636 636
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (636 318
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (478 478 (:REWRITE DEFAULT-CAR))
  (477 477
       (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
  (35 7 (:DEFINITION LEN))
  (31 18 (:REWRITE DEFAULT-+-2))
  (23 18 (:REWRITE DEFAULT-+-1))
  (12 4
      (:REWRITE X86ISA::MEM-ARRAY-NEXT-ADDR-IS-EXPECTED-MEM-ARRAY-NEXT-ADDR))
  (4 4
     (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
  (3 1 (:REWRITE NATP-WHEN-GTE-0))
  (3 1 (:DEFINITION TRUE-LISTP))
  (2 2
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
  (1 1 (:REWRITE NATP-WHEN-INTEGERP))
  (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(X86ISA::ELF-LOAD-BSS-SECTION
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::NTH-OF-NAT-LISTP-WITHIN-BOUNDS))
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (60606 60606 (:TYPE-PRESCRIPTION NAT-LISTP))
  (15368 136
         (:LINEAR X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (12159 318
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
  (11682 159
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
  (5506 636
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (4050 318 (:DEFINITION INTEGER-LISTP))
  (2226 2226 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (1460 730
        (:TYPE-PRESCRIPTION X86ISA::X86$CP-IMPLIES-NATP-NEXT-ADDR))
  (1431 1431
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
  (954 318
       (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
  (812 803 (:REWRITE DEFAULT-<-1))
  (803 803 (:REWRITE DEFAULT-<-2))
  (738 738 (:TYPE-PRESCRIPTION X86ISA::X86$CP))
  (713 713 (:REWRITE DEFAULT-CDR))
  (636 636
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (636 318
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (478 478 (:REWRITE DEFAULT-CAR))
  (477 477
       (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
  (35 7 (:DEFINITION LEN))
  (31 18 (:REWRITE DEFAULT-+-2))
  (23 18 (:REWRITE DEFAULT-+-1))
  (12 4
      (:REWRITE X86ISA::MEM-ARRAY-NEXT-ADDR-IS-EXPECTED-MEM-ARRAY-NEXT-ADDR))
  (4 4
     (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
  (3 1 (:REWRITE NATP-WHEN-GTE-0))
  (3 1 (:DEFINITION TRUE-LISTP))
  (2 2
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
  (1 1 (:REWRITE NATP-WHEN-INTEGERP))
  (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(X86ISA::ELF-LOAD-RODATA-SECTION
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::NTH-OF-NAT-LISTP-WITHIN-BOUNDS))
  (121212 60606
          (:TYPE-PRESCRIPTION X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (60606 60606 (:TYPE-PRESCRIPTION NAT-LISTP))
  (15368 136
         (:LINEAR X86ISA::N08P-ELEMENT-OF-BYTE-LISTP))
  (12159 318
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
  (11682 159
         (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
  (5506 636
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (4050 318 (:DEFINITION INTEGER-LISTP))
  (2226 2226 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (1460 730
        (:TYPE-PRESCRIPTION X86ISA::X86$CP-IMPLIES-NATP-NEXT-ADDR))
  (1431 1431
        (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
  (954 318
       (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
  (954 318
       (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
  (812 803 (:REWRITE DEFAULT-<-1))
  (803 803 (:REWRITE DEFAULT-<-2))
  (740 740 (:TYPE-PRESCRIPTION X86ISA::X86$CP))
  (713 713 (:REWRITE DEFAULT-CDR))
  (636 636
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (636 318
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (478 478 (:REWRITE DEFAULT-CAR))
  (477 477
       (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
  (318 318
       (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
  (318 159
       (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
  (159 159
       (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
  (35 7 (:DEFINITION LEN))
  (31 18 (:REWRITE DEFAULT-+-2))
  (23 18 (:REWRITE DEFAULT-+-1))
  (15 5
      (:REWRITE X86ISA::MEM-ARRAY-NEXT-ADDR-IS-EXPECTED-MEM-ARRAY-NEXT-ADDR))
  (4 4
     (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
  (3 1 (:REWRITE NATP-WHEN-GTE-0))
  (3 1 (:DEFINITION TRUE-LISTP))
  (2 2
     (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
  (1 1 (:REWRITE NATP-WHEN-INTEGERP))
  (1 1 (:REWRITE FOLD-CONSTS-IN-+)))