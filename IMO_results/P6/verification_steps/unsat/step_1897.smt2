(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -11367168 (pow b 4)) (* -8897280 (pow a 4)) (* 554976 (pow (+ a b) 4)) (* -21233664 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -10616832 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 80819521373810618007552 (pow a 3) (pow b 3) (pow (+ (* 8530944 b) (* 34704384 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)