(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 4) (* (pow (pow b 3) (* (pow (+ 1 a) -1) (pow (+ 1 c) -1) (pow (+ (* (pow (+ 1 a) -1) (pow (+ 1 c) -1)) (* (pow a 3) (pow (+ 1 b) -1) (pow (+ 1 c) -1)) (* (pow c 3) (pow (+ 1 a) -1) (pow (+ 1 b) -1))) -1))) (+ (* -1 (pow (+ 1 a) -1) (pow (+ 1 c) -1)) (* -1 (pow a 3) (pow (+ 1 b) -1) (pow (+ 1 c) -1)) (* -1 (pow c 3) (pow (+ 1 a) -1) (pow (+ 1 b) -1))))) 0)))
(check-sat)
(get-model)
(exit)