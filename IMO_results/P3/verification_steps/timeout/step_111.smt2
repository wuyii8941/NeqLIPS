(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 2) (* -1 (pow (+ (* (pow a (/ 4 3)) (pow (+ (* a (pow c (/ 5 3))) (* b (pow c (/ 5 3)))) -1)) (* (pow b (/ 4 3)) (pow (+ (* b (pow a (/ 5 3))) (* c (pow a (/ 5 3)))) -1)) (* (pow c (/ 4 3)) (pow (+ (* a (pow b (/ 5 3))) (* c (pow b (/ 5 3)))) -1))) (/ -1 3)) (pow (+ (* a (pow c (/ 4 3)) (pow (+ (* a (pow b (/ 5 3))) (* c (pow b (/ 5 3)))) -1)) (* b (pow a (/ 4 3)) (pow (+ (* a (pow c (/ 5 3))) (* b (pow c (/ 5 3)))) -1)) (* c (pow b (/ 4 3)) (pow (+ (* b (pow a (/ 5 3))) (* c (pow a (/ 5 3)))) -1))) (/ 4 3)))) 0)))
(check-sat)
(get-model)
(exit)