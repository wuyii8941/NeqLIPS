(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 1 3) (* -1 (pow a (/ -8 3)) (pow (* b c) (/ 7 3)) (pow (+ b (* 2 c)) -2)) (* -1 (pow c (/ -8 3)) (pow (* a b) (/ 7 3)) (pow (+ a (* 2 b)) -2)) (* -2 (pow (* a b c) (/ 7 3)) (pow (+ 1 (pow b 10)) -1) (pow (+ c (* 2 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)) -2))) 0)))
(check-sat)
(get-model)
(exit)