(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 1 (pow (* b c) (/ 1 2)) (* (/ 1 2) a) (* (/ 1 2) c) (* -1 (pow (+ a (* b c)) (/ 1 2))) (* -1 (pow (+ b (* a c)) (/ 1 2))) (* -1 (pow (+ c (* a b)) (/ 1 2))) (* (/ 1 8) (+ 1 b) (+ 1 (* 4 a)))) 0)))
(check-sat)
(get-model)
(exit)