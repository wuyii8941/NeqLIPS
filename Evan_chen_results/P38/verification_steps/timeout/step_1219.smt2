(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 212992 (* -98304 (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2))) (* 5 (pow (+ a b c) 8)) (* -98305 (pow 2 (/ 3 19661)) (pow (* 3 (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2)) (pow (+ (pow b 2) (pow c 2) (* b c)) 49152)) (pow 98305 -1)))) 0)))
(check-sat)
(get-model)
(exit)