(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 17343 (pow a 4)) (* 17343 (pow b 4)) (* (pow (* (pow a (* 834120 a)) (pow b (* 1065672 b))) (pow (+ (* 278040 a) (* 355224 b)) -1)) (+ (* -355224 b) (* -278040 a))) (* -663552 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -331776 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 104058 (pow a 2) (pow b 2)) (* 335964 b (pow a 3)) (* 1153884 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)