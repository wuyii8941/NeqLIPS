(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -2867 (pow b 4)) (* -2035 (pow a 4)) (* -6912 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 702 (pow a 2) (pow b 2)) (* 1268 b (pow a 3)) (* 3456 (pow a (/ 5 3)) (pow b (/ 7 3))) (* 6388 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)