(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 324 c) (* 245760 (pow b 3))) -1) (pow (+ (* 324 c (pow (+ (* 2 a) (* 2 b)) 2)) (* 245760 c (pow b 3))) 2)) (* -1130496 a (pow c 4)) (* -1130496 b (pow a 4)) (* -1079808 c (pow b 4)) (* -376832 a (pow b 4)) (* -376832 b (pow c 4)) (* -344064 (pow a 2) (pow c 3)) (* -344064 (pow a 3) (pow b 2)) (* -326144 c (pow a 4)) (* 344064 (pow a 2) (pow b 3)) (* 344064 (pow b 2) (pow c 3)) (* 933888 (pow a 3) (pow c 2)) (* 917504 a b (pow c 3)) (* 1120256 a c (pow b 3)) (* 1120256 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)