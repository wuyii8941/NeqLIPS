(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -14416256 (pow b 4)) (* -11123072 (pow a 4)) (* (pow (+ 277488 (* 277488 (pow b 4)) (* 1664928 (pow a 2) (pow b 2))) -1) (pow (+ (* 277488 (pow a 2)) (* 277488 (pow b 4)) (* 1664928 (pow a 2) (pow b 2))) 2)) (* -28311552 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -14155776 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 15444416 b (pow a 3)) (* 50342336 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)