(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -904881152 (pow b 4)) (* -694117376 (pow a 4)) (* -2717908992 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 106555392 (pow a 2) (pow b 2)) (* 988442624 b (pow a 3)) (* 3221909504 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)