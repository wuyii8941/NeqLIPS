(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* (/ -14801 6) (pow b 4)) (* (/ -11585 6) (pow a 4)) (* -4608 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -2304 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 1927 (pow a 2) (pow b 2)) (* (/ 22301939177792 27) (pow a 3) (pow b 3) (pow (+ (* (/ 5554 3) b) (* (/ 22594 3) a)) -2))) 0)))
(check-sat)
(get-model)
(exit)