(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -112277680 (pow b 4)) (* -85932208 (pow a 4)) (* -339738624 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 4994784 (pow a 2) (pow b 2)) (* 126885184 b (pow a 3)) (* 406068544 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)