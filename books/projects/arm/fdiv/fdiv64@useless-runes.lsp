(RTL::RMODENEAR)
(RTL::RMODEUP)
(RTL::RMODEDN)
(RTL::RMODEZERO)
(RTL::IDC)
(RTL::IXC)
(RTL::UFC)
(RTL::OFC)
(RTL::DZC)
(RTL::IOC)
(RTL::ANALYZE)
(RTL::CLZ53-LOOP-0 (10 9 (:REWRITE DEFAULT-+-2))
                   (10 9 (:REWRITE DEFAULT-+-1))
                   (5 5 (:REWRITE DEFAULT-<-2))
                   (5 5 (:REWRITE DEFAULT-<-1))
                   (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
                   (3 3
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::CLZ53-LOOP-1 (5 5 (:REWRITE DEFAULT-<-2))
                   (5 5 (:REWRITE DEFAULT-<-1))
                   (5 5 (:REWRITE DEFAULT-+-2))
                   (5 5 (:REWRITE DEFAULT-+-1))
                   (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
                   (1 1
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(RTL::CLZ53-LOOP-2 (5 5 (:REWRITE DEFAULT-<-2))
                   (5 5 (:REWRITE DEFAULT-<-1))
                   (5 5 (:REWRITE DEFAULT-+-2))
                   (5 5 (:REWRITE DEFAULT-+-1))
                   (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
                   (1 1
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(RTL::CLZ53)
(RTL::COMPUTEQ)
(RTL::RSHFT64)
(RTL::ROUNDER (5 5 (:TYPE-PRESCRIPTION RTL::SI)))
(RTL::FINAL (15 15 (:TYPE-PRESCRIPTION RTL::SI)))
(RTL::SPECIALCASE)
(RTL::NORMALIZE (7 7 (:TYPE-PRESCRIPTION RTL::SI)))
(RTL::PRESCALE (2 2 (:TYPE-PRESCRIPTION RTL::SI)))
(RTL::NEXTDIGIT)
(RTL::NEXTREM)
(RTL::NEXTQUOT)
(RTL::ITER1)
(RTL::ITER2)
(RTL::ITER3)
(RTL::FDIV64-LOOP-0 (10 9 (:REWRITE DEFAULT-+-2))
                    (10 9 (:REWRITE DEFAULT-+-1))
                    (5 5 (:REWRITE DEFAULT-<-2))
                    (5 5 (:REWRITE DEFAULT-<-1))
                    (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
                    (3 3
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(RTL::FDIV64)