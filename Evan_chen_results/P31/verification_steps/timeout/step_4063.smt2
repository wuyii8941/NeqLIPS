(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (+ (* 248832 c) (* 31457280 (pow b 3))) -1) (pow (+ (* 248832 c (pow (+ a b) 2)) (* 31457280 c (pow b 3))) 2)) (* -144703488 a (pow c 4)) (* -144703488 b (pow a 4)) (* -137551872 c (pow b 4)) (* -48234496 a (pow b 4)) (* -48234496 b (pow c 4)) (* -44040192 (pow a 2) (pow c 3)) (* -44040192 (pow a 3) (pow b 2)) (* -41082880 c (pow a 4)) (* 44040192 (pow a 2) (pow b 3)) (* 44040192 (pow b 2) (pow c 3)) (* 119537664 (pow a 3) (pow c 2)) (* 117440512 a b (pow c 3)) (* 146046976 a c (pow b 3)) (* 146046976 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)