(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (= (* a b c d) 1))
(assert (>= a 0))
(assert (>= b 0))
(assert (>= c 0))
(assert (>= d 0))
(assert (not (<= (+ (/ 23 12) c (* (/ 1 2) (pow a 2)) (* (/ 1 3) (pow d 3)) (* (/ 1 4) (pow b 4)) (* -1 a (pow d 4)) (* -1 b (pow a 4)) (* -1 c (pow b 4)) (* -1 d (pow c 4))) 0)))
(check-sat)
(get-model)
(exit)