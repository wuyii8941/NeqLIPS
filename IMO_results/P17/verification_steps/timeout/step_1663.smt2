(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1 (pow (+ (* 16816 c) (* 17920 (pow a 3) (pow b 2))) -1) (pow (+ (* 16816 c (pow a 2)) (* 17920 (pow a 3) (pow b 2))) 2)) (* -97280 a (pow c 4)) (* -97280 b (pow a 4)) (* -94640 c (pow b 4)) (* -19456 a (pow b 4)) (* -19456 b (pow c 4)) (* -17920 (pow a 2) (pow c 3)) (* 270 c (pow (+ a b) 4)) (* 12800 (pow b 3) (pow c 2)) (* 17920 (pow a 2) (pow b 3)) (* 17920 (pow b 2) (pow c 3)) (* 48640 (pow a 3) (pow c 2)) (* 86016 a b (pow c 3)) (* 96576 a c (pow b 3)) (* 96576 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)