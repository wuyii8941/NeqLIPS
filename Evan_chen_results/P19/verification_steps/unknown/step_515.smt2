(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -9 (pow a 4)) (* -9 (pow b 4)) (* -9 (pow c 4)) (* (pow (* (pow b (* a (pow c 2))) (pow (* a b) (* b c)) (pow (* c (pow a 2)) b)) (pow (+ b (* a (pow c 2)) (* b c)) -1)) (+ (* -1 b) (* -1 a (pow c 2)) (* -1 b c))) (* -20 (pow a 2) (pow b 2)) (* -20 (pow a 2) (pow c 2)) (* -20 (pow b 2) (pow c 2)) (* 15 a (pow b 3)) (* 15 a (pow c 3)) (* 15 b (pow a 3)) (* 15 b (pow c 3)) (* 15 c (pow a 3)) (* 15 c (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)