(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (pow (* (pow a (* 1304576 c (pow a 2))) (pow b (* 688128 b (pow a 3)))) (pow (+ (* 652288 c (pow a 2)) (* 688128 b (pow a 3))) -1)) (+ (* -688128 b (pow a 3)) (* -652288 c (pow a 2)))) (* -2260992 a (pow c 4)) (* -2260992 b (pow a 4)) (* -2159616 c (pow b 4)) (* -753664 a (pow b 4)) (* -753664 b (pow c 4)) (* -688128 (pow a 2) (pow c 3)) (* 10368 c (pow (+ a b) 4)) (* 491520 (pow b 3) (pow c 2)) (* 688128 (pow a 2) (pow b 3)) (* 688128 (pow b 2) (pow c 3)) (* 1867776 (pow a 3) (pow c 2)) (* 1835008 a b (pow c 3)) (* 2240512 a c (pow b 3)) (* 2240512 b c (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)