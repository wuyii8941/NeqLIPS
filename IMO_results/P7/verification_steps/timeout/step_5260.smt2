(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 205 (pow b 3)) (* 224 (pow c 3)) (* -1458 a (pow c 2)) (* -1458 b (pow a 2)) (* -1158 c (pow b 2)) (* 729 (pow a (/ 4 3)) (pow b (/ 5 3))) (* 1458 (pow a (/ 5 3)) (pow (* b c) (/ 2 3))) (* 1458 (pow a (pow 3 -1)) (pow (* b c) (/ 4 3))) (* 1458 (pow b (pow 3 -1)) (pow (* a c) (/ 4 3))) (* 1458 (pow c (/ 5 3)) (pow (* a b) (/ 2 3))) (* 1458 (pow c (pow 3 -1)) (pow (* a b) (/ 4 3))) (* -4374 a b c)) 0)))
(check-sat)
(get-model)
(exit)