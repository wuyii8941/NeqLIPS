(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -34404 (pow b 4)) (* -24420 (pow a 4)) (* -82944 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 8424 (pow a 2) (pow b 2)) (* 15216 b (pow a 3)) (* 41472 (pow a (/ 5 3)) (pow b (/ 7 3))) (* 76656 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)