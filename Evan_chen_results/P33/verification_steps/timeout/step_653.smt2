(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 1 (pow (* a c) (/ 1 2)) (* -1 (pow (+ a (* b c)) (/ 1 2))) (* -1 (pow (+ b (* a c)) (/ 1 2))) (* -1 (pow (+ c (* a b)) (/ 1 2))) (* (/ 1 8) (+ 1 b) (+ 1 (* 4 c))) (* (pow (+ 5 (* 24 a)) 2) (pow (+ 672 (* 256 a)) -1) (+ 1 b))) 0)))
(check-sat)
(get-model)
(exit)