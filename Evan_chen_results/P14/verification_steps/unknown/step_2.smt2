(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) (+ (pow a -1) (pow b -1) (pow c -1))))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 432 (* -48 (pow (* b c) (pow (+ 2 a) -1)) (+ 2 a) (+ a b c))) 0)))
(check-sat)
(get-model)
(exit)