(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 1664928 (pow a 4)) (* 1664928 (pow b 4)) (* (pow (* (pow a (* 173529344 (pow a 3))) (pow b (* 226220288 (pow b 3)))) (pow (+ (* 173529344 (pow a 3)) (* 226220288 (pow b 3))) -1)) (+ (* -226220288 (pow b 3)) (* -173529344 (pow a 3)))) (* -452984832 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -226492416 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 9989568 (pow a 2) (pow b 2)) (* 253770368 b (pow a 3)) (* 812137088 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)