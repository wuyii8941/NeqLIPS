(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (/ -4510 3) (pow b 4)) (* (/ -2902 3) (pow a 4)) (* -4608 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -2304 (pow a (/ 10 3)) (pow b (/ 2 3))) (* (/ 5554 3) b (pow a 3)) (* (/ 22594 3) a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)