(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (pow (* a b c) (/ 2 3)) (* (pow (pow a 2) (pow (+ 1 (* 2 (pow b 2)) (* 2 (pow c 2))) -1)) (+ -1 (* -2 (pow b 2)) (* -2 (pow c 2)))) (* 2 b (pow (* a b c) (pow 3 -1))) (* 2 c (pow (* a b c) (pow 3 -1)))) 0)))
(check-sat)
(get-model)
(exit)