(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1 (pow a 4)) (* -1 (pow b 4)) (* -1 (pow c 4)) (* a (pow (+ c (* b (pow c 2)) (* a b c)) -1) (pow (+ (* b c) (* b (pow c 2)) (* a b c)) 2))) 0)))
(check-sat)
(get-model)
(exit)