(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 3888 c) (* 30720 (pow b 3) (pow c 2)) (* 114688 a b (pow c 3)) (* 142624 a c (pow b 3)) (* 142624 b c (pow a 3))) -1) (pow (+ (* 243 c (pow (+ (* 2 a) (* 2 b)) 2)) (* 30720 (pow b 3) (pow c 2)) (* 114688 a b (pow c 3)) (* 142624 a c (pow b 3)) (* 142624 b c (pow a 3))) 2)) (* -141312 a (pow c 4)) (* -141312 b (pow a 4)) (* -134328 c (pow b 4)) (* -47104 a (pow b 4)) (* -47104 b (pow c 4)) (* -43008 (pow a 2) (pow c 3)) (* -43008 (pow a 3) (pow b 2)) (* -40120 c (pow a 4)) (* 43008 (pow a 2) (pow b 3)) (* 43008 (pow b 2) (pow c 3)) (* 116736 (pow a 3) (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)