(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (+ (* 2 a) (* 2 b) (* 3 c)) -1) (pow (+ (* 2 a) (* 2 c) (* 3 b)) -1) (pow (+ (* 2 b) (* 2 c) (* 3 a)) -1) (* -1 (pow (+ (/ 3 2) c (* (/ 3 2) (pow (+ a b) 2))) -1)) (* -1 (pow (+ b (* 3 a) (* 3 c)) -1)) (* -1 (pow (+ (/ 1 2) (* (/ 1 2) (pow a 2)) (* 3 b) (* 3 c)) -1))) 0)))
(check-sat)
(get-model)
(exit)