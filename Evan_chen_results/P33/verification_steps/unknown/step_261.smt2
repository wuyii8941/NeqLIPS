(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 2 (* -2 (pow (+ a (* b c)) (/ 1 2))) (* -2 (pow (+ b (* a c)) (/ 1 2))) (* 2 (pow (* b c) (/ 1 2))) (* 2 (pow (+ (* 2 a b) (* 2 a c)) (pow 2 -1))) (* -1 (pow 2 (/ 1 2)) (pow c (/ 1 2))) (* -1 (pow 2 (/ 1 2)) (pow (* a b) (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)