(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -64 (pow (+ a (* b c)) (/ 1 2))) (* -64 (pow (+ b (* a c)) (/ 1 2))) (* -64 (pow (+ c (* a b)) (/ 1 2))) (* (pow (+ 88 (* 32 a) (* 32 c) (* 32 (pow b 2)) (* 32 a (pow 2 (/ 1 2)))) -1) (pow (+ 88 (* 32 a) (* 32 c) (* 32 (pow b 3)) (* 32 a (pow 2 (/ 1 2)))) 2)) (* 32 c (pow 2 (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)