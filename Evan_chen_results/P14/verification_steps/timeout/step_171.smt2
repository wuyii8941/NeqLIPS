(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 1 3) (* -1 (pow (+ (* (pow b (/ -8 3)) (pow c (/ 7 3)) (pow (+ c (* 2 a)) -2)) (* 2 (pow a (/ -1 6)) (pow c (/ -1 6)) (pow (+ a (* 2 b)) -1) (pow (+ b (* 2 c)) -1))) (/ -4 3)) (pow (+ (* a (pow b (/ -8 3)) (pow c (/ 7 3)) (pow (+ c (* 2 a)) -2)) (* 2 b (pow a (/ -1 6)) (pow c (/ -1 6)) (pow (+ a (* 2 b)) -1) (pow (+ b (* 2 c)) -1))) (/ 7 3)))) 0)))
(check-sat)
(get-model)
(exit)