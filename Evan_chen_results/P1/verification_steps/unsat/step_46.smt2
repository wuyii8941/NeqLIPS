(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (pow (* (+ (pow b 2) (pow c 2)) (+ (* 4 (pow a 2)) (* 4 (pow c 2)))) (/ 1 2)) (* -1 (pow a 2)) (* -1 (pow b 2)) (* -2 (pow c 2))) 0)))
(check-sat)
(get-model)
(exit)