(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1104 a (pow c 4)) (* -1104 b (pow a 4)) (* -1068 c (pow b 4)) (* -368 a (pow b 4)) (* -368 b (pow c 4)) (* -336 (pow a 2) (pow c 3)) (* -336 (pow a 3) (pow b 2)) (* -332 c (pow a 4)) (* 240 (pow b 3) (pow c 2)) (* 336 (pow a 2) (pow b 3)) (* 336 (pow b 2) (pow c 3)) (* 912 (pow a 3) (pow c 2)) (* 896 a b (pow c 3)) (* 1040 a c (pow b 3)) (* 1040 b c (pow a 3)) (* (/ 27 4) c (pow (+ (* 2 a) (* 2 b)) 2) (+ 1 (* (/ 1 256) (pow (+ (* 2 a) (* 2 b)) 4))))) 0)))
(check-sat)
(get-model)
(exit)