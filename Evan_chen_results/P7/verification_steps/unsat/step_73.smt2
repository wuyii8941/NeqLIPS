(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (/ 1 2) (* (/ 1 2) (pow (* a b c) (/ 4 3))) (* -1 (pow c 2)) (* (/ -1 2) (pow a 2)) (* (/ -1 2) (pow b 2)) (* c (pow (* a b c) (pow 3 -1)))) 0)))
(check-sat)
(get-model)
(exit)