(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (pow (* (+ 1 (pow c (* 8 (pow 3 -1)))) (+ (* (pow a (/ 2 3)) (pow b (/ 8 3))) (* (pow a (/ 10 3)) (pow b (/ 8 3))))) (/ 1 2)) (pow (* (+ 1 (pow c (* 10 (pow 3 -1)))) (+ (pow a (* 8 (pow 3 -1))) (* (pow b (/ 10 3)) (pow c (/ 8 3))))) (/ 1 2)) (pow (* (+ (pow a (* 8 (pow 3 -1))) (* (pow a (/ 8 3)) (pow b (/ 2 3)))) (+ (pow c (* 8 (pow 3 -1))) (* (pow b (/ 8 3)) (pow c (/ 2 3))))) (/ 1 2)) (* -1 a (pow c 2)) (* -1 b (pow a 2)) (* -1 c (pow b 2)) (* -3 a b c)) 0)))
(check-sat)
(get-model)
(exit)