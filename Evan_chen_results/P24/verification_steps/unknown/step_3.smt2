(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (+ (* 2 a) (* 2 b) (* 3 c)) -1) (pow (+ (* 2 a) (* 2 c) (* 3 b)) -1) (pow (+ (* 2 b) (* 2 c) (* 3 a)) -1) (* -2 (pow (+ c (* 6 (pow a (/ 1 2)) (pow b (/ 1 2)))) (/ -1 2)) (pow (+ (pow (+ a (* 6 (pow b (/ 1 2)) (pow c (/ 1 2)))) -1) (pow (+ b (* 6 (pow a (/ 1 2)) (pow c (/ 1 2)))) -1)) (/ 1 2)))) 0)))
(check-sat)
(get-model)
(exit)