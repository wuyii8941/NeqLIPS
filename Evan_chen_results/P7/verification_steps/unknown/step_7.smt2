(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (not (<= (+ (* a (pow (* a b c) (pow 3 -1))) (* b (pow (* a b c) (pow 3 -1))) (* c (pow (* a b c) (pow 3 -1))) (* (pow c (* c (pow (+ c (pow a 2) (pow b 2)) -1))) (+ (* -1 c) (* -1 (pow a 2)) (* -1 (pow b 2))))) 0)))
(check-sat)
(get-model)
(exit)