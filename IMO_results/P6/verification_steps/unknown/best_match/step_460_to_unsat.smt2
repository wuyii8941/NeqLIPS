(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 1404 (pow a 4)) (* 1404 (pow b 4)) (* -1 (pow (+ (* 25824 (pow a 2)) (* 35808 (pow b 2))) -1) (pow (+ (* 25824 (pow a 3)) (* 35808 (pow b 3))) 2)) (* -55296 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -27648 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 8424 (pow a 2) (pow b 2)) (* 15216 b (pow a 3)) (* 41472 (pow a (/ 5 3)) (pow b (/ 7 3))) (* 76656 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)