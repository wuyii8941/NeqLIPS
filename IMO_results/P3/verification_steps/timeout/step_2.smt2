(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 2) (* -1 (pow b (/ -5 3)) (pow (* a c) (/ 4 3)) (pow (+ a c) -1)) (* -1 (pow c (/ -5 3)) (pow (* a b) (/ 4 3)) (pow (+ a b) -1)) (* -2 (pow (* a b c) (/ 4 3)) (pow (+ 1 (pow a 6)) -1) (pow (+ b c) -1))) 0)))
(check-sat)
(get-model)
(exit)