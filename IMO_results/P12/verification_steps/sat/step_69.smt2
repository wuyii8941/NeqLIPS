(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* -2654208 (pow a 8)) (* -2654208 (pow b 8)) (* -2654208 (pow c 8)) (* -15925248 (pow a 4) (pow b 4)) (* -15925248 (pow a 4) (pow c 4)) (* -15925248 (pow b 4) (pow c 4)) (* -10616832 (pow a 2) (pow b 6)) (* -10616832 (pow a 2) (pow c 6)) (* -10616832 (pow a 6) (pow b 2)) (* -10616832 (pow a 6) (pow c 2)) (* -10616832 (pow b 2) (pow c 6)) (* -10616832 (pow b 6) (pow c 2)) (* (pow a 2) (pow b 2) (+ (* 16777216 (pow a 4)) (* 16777216 (pow b 4)) (* -33554432 (pow a 2) (pow b 2)))) (* (pow b 2) (pow c 2) (+ (* 16777216 (pow b 4)) (* 16777216 (pow c 4)) (* -33554432 (pow b 2) (pow c 2)))) (* -31850496 (pow a 2) (pow b 2) (pow c 4)) (* -31850496 (pow a 2) (pow b 4) (pow c 2)) (* -31850496 (pow a 4) (pow b 2) (pow c 2)) (* 16777216 (pow a 2) (pow c 2) (pow (+ 1 (pow a 4) (* -2 (pow a 2) (pow c 2))) -1) (pow (+ (pow a 4) (pow c 2) (* -2 (pow a 2) (pow c 2))) 2)) (* -33554432 a b (pow c 2) (+ (pow a 2) (* -1 (pow c 2))) (+ (pow b 2) (* -1 (pow c 2)))) (* -33554432 b c (pow a 2) (+ (pow a 2) (* -1 (pow b 2))) (+ (pow a 2) (* -1 (pow c 2)))) (* 33554432 a c (pow b 2) (+ (pow a 2) (* -1 (pow b 2))) (+ (pow b 2) (* -1 (pow c 2))))) 0)))
(check-sat)
(get-model)
(exit)