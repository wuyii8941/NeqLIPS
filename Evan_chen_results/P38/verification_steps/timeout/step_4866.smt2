(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 12 (* -26 (pow 24 (pow 13 -1)) (pow (* (pow (+ (pow a 2) (pow b 2) (* a b)) (/ 1 2)) (pow (+ (pow a 2) (pow c 2) (* a c)) (/ 1 2)) (pow (+ (pow b 2) (pow c 2) (* b c)) 12)) (pow 26 -1))) (* 2 (+ 1 (pow (+ a b c) 2)) (+ a b c))) 0)))
(check-sat)
(get-model)
(exit)