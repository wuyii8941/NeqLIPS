(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (pow a 512) (* (pow (+ (* 641920 c) (* 688128 (pow b 2))) -1) (+ (* 4032 (pow b 2)) (* 5015 c)))) (+ (* -688128 (pow b 2)) (* -641920 c))) (* -2260992 a (pow c 4)) (* -2260992 b (pow a 4)) (* -2149248 c (pow b 4)) (* -753664 a (pow b 4)) (* -753664 b (pow c 4)) (* -688128 (pow a 2) (pow c 3)) (* 491520 (pow b 3) (pow c 2)) (* 688128 (pow a 2) (pow b 3)) (* 688128 (pow b 2) (pow c 3)) (* 1867776 (pow a 3) (pow c 2)) (* 62208 c (pow a 2) (pow b 2)) (* 1835008 a b (pow c 3)) (* 2281984 a c (pow b 3)) (* 2281984 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)