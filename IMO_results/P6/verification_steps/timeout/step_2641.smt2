(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -11367168 (pow b 4)) (* -8897280 (pow a 4)) (* (pow (+ (* 554976 (pow a 2)) (* 554976 (pow b 4)) (* 3329856 (pow b 2))) -1) (pow (+ (* 554976 (pow a 3)) (* 554976 (pow b 4)) (* 3329856 a (pow b 2))) 2)) (* -21233664 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -10616832 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 10750848 b (pow a 3)) (* 36924288 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)