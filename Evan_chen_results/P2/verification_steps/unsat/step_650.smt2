(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (pow (+ (* 2 (pow a 2) (pow b 4) (pow c 2)) (* 2 (pow a 4) (pow b 2) (pow c 2))) (/ 1 2)) (* -1 (pow a 4)) (* -1 (pow b 4)) (* -1 (pow c 4)) (* a b (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)