(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 7864320 (pow b 3)) (* 3888 c (pow (+ (* 2 a) (* 2 b)) 4))) -1) (pow (+ (* 3888 c (pow (+ (* 2 a) (* 2 b)) 4)) (* 7864320 c (pow b 3))) 2)) (* -36175872 a (pow c 4)) (* -36175872 b (pow a 4)) (* -34387968 c (pow b 4)) (* -12058624 a (pow b 4)) (* -12058624 b (pow c 4)) (* -11010048 (pow a 2) (pow c 3)) (* -11010048 (pow a 3) (pow b 2)) (* -10270720 c (pow a 4)) (* 11010048 (pow a 2) (pow b 3)) (* 11010048 (pow b 2) (pow c 3)) (* 29884416 (pow a 3) (pow c 2)) (* 29360128 a b (pow c 3)) (* 36511744 a c (pow b 3)) (* 36511744 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)