(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 5) (* (pow (* (pow (+ (pow b 2) (pow (+ a c) 2)) (* -1 (pow (+ a c (* -1 b)) 2))) (pow (+ (pow c 2) (pow (+ a b) 2)) (* -1 (pow (+ a b (* -1 c)) 2)))) (pow (+ (pow (+ a b (* -1 c)) 2) (pow (+ a c (* -1 b)) 2) (* (pow (+ (pow a 2) (pow (+ b c) 2)) -1) (pow (+ b c (* -1 a)) 2))) -1)) (+ (* -1 (pow (+ a b (* -1 c)) 2)) (* -1 (pow (+ a c (* -1 b)) 2)) (* -1 (pow (+ (pow a 2) (pow (+ b c) 2)) -1) (pow (+ b c (* -1 a)) 2))))) 0)))
(check-sat)
(get-model)
(exit)