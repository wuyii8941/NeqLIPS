(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 1 3) (* (pow (* (pow (* (pow a (/ -8 3)) (pow c (/ 7 3)) (pow (+ b (* 2 c)) -2)) (pow b (* 7 (pow 3 -1)))) (pow (* (pow a (/ 7 3)) (pow b (/ -8 3)) (pow (+ c (* 2 a)) -2)) (pow c (* 7 (pow 3 -1)))) (pow (* (pow a (/ 7 3)) (pow c (/ -8 3)) (pow (+ a (* 2 b)) -2)) (pow b (* 7 (pow 3 -1))))) (pow (+ (pow c (* 7 (pow 3 -1))) (* 2 (pow b (/ 7 3)))) -1)) (+ (* -1 (pow c (/ 7 3))) (* -2 (pow b (/ 7 3)))))) 0)))
(check-sat)
(get-model)
(exit)