(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (/ 2 3) (* -1 (pow c 2)) (* (/ -1 2) (pow a 2)) (* (/ -1 2) (pow b 2)) (* c (pow (* a b c) (pow 3 -1))) (* (/ 1 3) (pow a 2) (pow b 2) (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)