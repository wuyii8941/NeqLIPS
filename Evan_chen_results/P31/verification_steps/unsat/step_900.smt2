(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -141312 a (pow c 4)) (* -141312 b (pow a 4)) (* -134976 c (pow b 4)) (* -47104 a (pow b 4)) (* -47104 b (pow c 4)) (* -43008 (pow a 2) (pow c 3)) (* -43008 (pow a 3) (pow b 2)) (* -40768 c (pow a 4)) (* 30720 (pow b 3) (pow c 2)) (* 43008 (pow a 2) (pow b 3)) (* 43008 (pow b 2) (pow c 3)) (* 116736 (pow a 3) (pow c 2)) (* 10368 c (pow a 2) (pow (+ (/ 1 2) (* (/ 1 2) b)) 4)) (* 114688 a b (pow c 3)) (* 140032 a c (pow b 3)) (* 140032 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)