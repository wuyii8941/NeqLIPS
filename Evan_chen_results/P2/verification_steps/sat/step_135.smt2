(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (* -1 (pow a 4)) (* -1 (pow b 4)) (* -1 (pow c 4)) (* (pow a 2) (+ (/ 2 3) (* (/ 1 3) (pow b 3) (pow c 3)))) (* a b (pow c 2)) (* a c (pow b 2))) 0)))
(check-sat)
(get-model)
(exit)