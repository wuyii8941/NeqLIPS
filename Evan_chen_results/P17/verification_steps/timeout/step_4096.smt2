(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 540 c) (* 409600 (pow b 3)) (* 573440 (pow a 2) (pow b 3))) -1) (pow (+ (* 540 c (pow (+ (* 2 a) (* 2 b)) 2)) (* 409600 c (pow b 3)) (* 573440 (pow a 2) (pow b 3))) 2)) (* -3112960 a (pow c 4)) (* -3112960 b (pow a 4)) (* -3028480 c (pow b 4)) (* -622592 a (pow b 4)) (* -622592 b (pow c 4)) (* -573440 (pow a 2) (pow c 3)) (* -573440 (pow a 3) (pow b 2)) (* -538112 c (pow a 4)) (* 573440 (pow b 2) (pow c 3)) (* 1556480 (pow a 3) (pow c 2)) (* 2752512 a b (pow c 3)) (* 3090432 a c (pow b 3)) (* 3090432 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)