(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (pow (* a b c) (/ 2 3)) (* -1 (pow a 2)) (* -2 (pow b 2)) (* -2 (pow c 2)) (* 2 (pow (+ (* 2 (pow a (/ 2 3)) (pow b (/ 2 3)) (pow c (/ 8 3))) (* 2 (pow a (/ 2 3)) (pow b (/ 8 3)) (pow c (/ 2 3)))) (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)