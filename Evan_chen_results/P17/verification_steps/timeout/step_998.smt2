(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 143360 (pow c 3)) (* 102400 (pow b 3) (pow c 2)) (* 143360 (pow a 2) (pow b 3)) (* 389120 (pow a 3) (pow c 2)) (* 34560 c (pow a 2) (pow b 2))) -1) (pow (+ (* 102400 (pow b 3) (pow c 2)) (* 143360 b (pow c 3)) (* 143360 (pow a 2) (pow b 3)) (* 389120 (pow a 3) (pow c 2)) (* 34560 c (pow a 2) (pow b 2))) 2)) (* -778240 a (pow c 4)) (* -778240 b (pow a 4)) (* -757120 c (pow b 4)) (* -155648 a (pow b 4)) (* -155648 b (pow c 4)) (* -143360 (pow a 2) (pow c 3)) (* -143360 (pow a 3) (pow b 2)) (* -134528 c (pow a 4)) (* 688128 a b (pow c 3)) (* 772608 a c (pow b 3)) (* 772608 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)