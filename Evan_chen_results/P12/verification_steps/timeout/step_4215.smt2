(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= (+ (pow a 2) (pow b 2) (pow c 2) (* a b) (* a c) (* b c)) 2))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ 6 (* -2 (pow (+ a b) -2)) (* -2 (pow (+ a c) -2)) (* -2 (pow (+ b c) -2)) (* -16 b c (pow (+ 10219556568130249792144084639737131127606612289527132208011744222787529204190600021912300083260777342570992572936925682985057359817573479329685 (* 5 (pow (+ b c) 4))) -1)) (* -2 a b (pow (+ a b) -2)) (* -2 a c (pow (+ a c) -2))) 0)))
(check-sat)
(get-model)
(exit)