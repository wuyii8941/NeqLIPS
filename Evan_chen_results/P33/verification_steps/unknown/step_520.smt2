(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 5 4) (pow (* a c) (/ 1 2)) (* -1 (pow (+ a (* b c)) (/ 1 2))) (* -1 (pow (+ b (* a c)) (/ 1 2))) (* -1 (pow (+ c (* a b)) (/ 1 2))) (* (pow a (/ 1 2)) (+ (/ 2 3) (* (/ 1 3) (pow b (/ 3 2))))) (* (/ 1 4) c (pow (+ 1 b) 2))) 0)))
(check-sat)
(get-model)
(exit)