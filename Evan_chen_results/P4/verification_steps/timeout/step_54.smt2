(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (pow (* (+ 2 (pow a 6)) (+ (* (pow b 2) (pow c 2)) (* (pow a 2) (pow b 2) (pow c 6)) (* (pow a 2) (pow b 6) (pow c 2)))) (/ 1 2)) (* -1 (pow a 5)) (* -1 (pow b 5)) (* -1 (pow c 5))) 0)))
(check-sat)
(get-model)
(exit)