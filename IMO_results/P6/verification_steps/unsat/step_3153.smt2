(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -112627 (pow b 4)) (* -86899 (pow a 4)) (* (pow (+ (* (/ 17343 32) (pow (+ (* 2 a) (* 2 b)) 4)) (* 111988 b (pow a 3)) (* 384628 a (pow b 3))) 2) (pow (+ (* 34686 (pow (+ (* (/ 1 2) a) (* (/ 1 2) b)) 2) (pow (+ (* 2 a) (* 2 b)) 2)) (* 111988 b (pow a 3)) (* 384628 a (pow b 3))) -1)) (* -221184 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -110592 (pow a (/ 10 3)) (pow b (/ 2 3)))) 0)))
(check-sat)
(get-model)
(exit)