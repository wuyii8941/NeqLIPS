(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 60 (pow b 3)) (* 9 c (pow (+ a b) 4)) (* 84 (pow a 2) (pow b 3)) (* 84 (pow b 2) (pow c 3))) -1) (pow (+ (* 9 c (pow (+ a b) 4)) (* 60 c (pow b 3)) (* 84 (pow a 2) (pow b 3)) (* 84 (pow b 2) (pow c 3))) 2)) (* -276 a (pow c 4)) (* -276 b (pow a 4)) (* -276 c (pow b 4)) (* -92 a (pow b 4)) (* -92 b (pow c 4)) (* -92 c (pow a 4)) (* -84 (pow a 2) (pow c 3)) (* -84 (pow a 3) (pow b 2)) (* 228 (pow a 3) (pow c 2)) (* 224 a b (pow c 3)) (* 224 a c (pow b 3)) (* 224 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)