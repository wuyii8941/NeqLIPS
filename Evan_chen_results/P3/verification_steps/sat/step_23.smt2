(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 2) (* (pow (* a b c) (/ 4 3)) (+ (* -1 (pow (+ (* a (pow b 3)) (* c (pow b 3))) -1)) (* -1 (pow (+ (* a (pow c 3)) (* b (pow c 3))) -1)) (* -1 (pow (+ (* c (pow a 3)) (* (/ 1 2) b (+ 1 (pow a 6)))) -1))))) 0)))
(check-sat)
(get-model)
(exit)