(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (* (+ 1 (pow b 10)) (+ (* (pow a 4) (pow c 4)) (* (pow a 4) (pow b 4) (pow c 10)))) (/ 1 2)) (* -1 a (pow b 8)) (* -1 b (pow c 8)) (* -1 c (pow a 8)) (* (pow a 5) (pow b 2) (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)