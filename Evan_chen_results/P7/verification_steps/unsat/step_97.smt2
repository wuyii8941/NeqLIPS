(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (* (/ 1 2) (pow (* a b c) (/ 2 3))) (* (/ -1 2) (pow a 2)) (* (/ -1 2) (pow b 2)) (* (/ -1 2) (pow c 2)) (* (pow (+ 4 (* (/ 2 3) a b c)) (/ 14 3)) (pow (+ (* 2 (pow 3 -1)) 4) (/ -14 3)))) 0)))
(check-sat)
(get-model)
(exit)