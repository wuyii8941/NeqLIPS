(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 2) (* -1 (pow a -1) (pow b 2) (pow c 2) (pow (+ b c) -1)) (* -1 (pow (* (pow b (* (pow c -1) (pow (+ a b) -1))) (pow c (* (pow b -1) (pow (+ a c) -1)))) (* a (pow (+ (* a (pow b -1) (pow (+ a c) -1)) (* a (pow c -1) (pow (+ a b) -1))) -1))) (pow (+ (* (pow b -1) (pow (+ a c) -1)) (* (pow c -1) (pow (+ a b) -1))) -1) (+ (* a (pow b -1) (pow (+ a c) -1)) (* a (pow c -1) (pow (+ a b) -1))) (+ (* a b (pow c -1) (pow (+ a b) -1)) (* a c (pow b -1) (pow (+ a c) -1))))) 0)))
(check-sat)
(get-model)
(exit)