(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (not (<= (+ (pow (* (+ (pow b 4) (* 2 (pow a 4))) (+ (pow b 4) (* 2 (pow c 4)))) (/ 1 2)) (* -1 (pow a 4)) (* -1 (pow b 4)) (* -1 (pow c 4))) 0)))
(check-sat)
(get-model)
(exit)