(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (/ -2867 8) (pow b 4)) (* (/ -2035 8) (pow a 4)) (* (pow (+ (* (/ 351 4) (pow a 2)) (* 432 (pow a (/ 5 3)) (pow b (/ 7 3))) (* (/ 1597 2) a (pow b 3))) -1) (pow (+ (* 432 (pow a (/ 5 3)) (pow b (/ 7 3))) (* (/ 351 4) b (pow a 2)) (* (/ 1597 2) a (pow b 3))) 2)) (* -576 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -288 (pow a (/ 10 3)) (pow b (/ 2 3))) (* (/ 317 2) b (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)