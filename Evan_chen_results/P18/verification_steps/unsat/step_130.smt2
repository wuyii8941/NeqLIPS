(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (not (<= (+ (* -1 (pow a 3)) (* -1 (pow b 3)) (* -1 (pow c 3)) (* a (pow (+ (pow b 4) (pow c 4) (* 2 (pow b 2) (pow c 2))) (/ 1 2))) (* b (pow a 2)) (* b (pow c 2)) (* c (pow a 2)) (* c (pow b 2)) (* -3 a b c)) 0)))
(check-sat)
(get-model)
(exit)