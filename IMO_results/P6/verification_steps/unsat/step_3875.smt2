(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -10604076 (pow b 4)) (* -8134188 (pow a 4)) (* -31850496 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 1248696 (pow a 2) (pow b 2)) (* 11583312 b (pow a 3)) (* 37756752 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)