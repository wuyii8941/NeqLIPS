(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ a b c d) 4))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (not (<= (+ (/ 2 3) (* -1 d (pow (+ a (* 2 b) (* 3 c)) -1)) (* -2 (pow (* c (+ (* a (pow (+ b (* 2 c) (* 3 d)) -1)) (* b (pow (+ c (* 2 d) (* 3 a)) -1)))) (/ 1 2)) (pow (+ d (* 2 a) (* 3 b)) (/ -1 2)))) 0)))
(check-sat)
(get-model)
(exit)