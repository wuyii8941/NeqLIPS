(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (+ a b c d) 1))
(assert (>= (+ a (* -1 b)) 0))
(assert (>= (+ b (* -1 c)) 0))
(assert (>= (+ c (* -1 d)) 0))
(assert (> d 0))
(assert (not (<= (+ -1 (* (/ 1 2) (pow a a) (+ (pow (pow d 2) d) (* (pow (pow b 2) b) (pow (pow c 2) c))) (+ a (* 2 b) (* 3 c) (* 4 d)))) 0)))
(check-sat)
(get-model)
(exit)