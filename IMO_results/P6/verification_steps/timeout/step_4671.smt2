(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -901016 (pow b 4)) (* -695192 (pow a 4)) (* (pow (+ (* 277488 (pow (+ (* (/ 1 2) a) (* (/ 1 2) b)) 2)) (* 3077024 a (pow b 3))) -1) (pow (+ (* 277488 (pow (+ (* (/ 1 2) a) (* (/ 1 2) b)) 3)) (* 3077024 a (pow b 3))) 2)) (* -1769472 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -884736 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 895904 b (pow a 3))) 0)))
(check-sat)
(get-model)
(exit)