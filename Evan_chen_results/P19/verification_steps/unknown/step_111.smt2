(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (+ a b c) 3))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (/ 3 5) (* (pow (* (pow (* (pow (+ (pow a 2) (pow b 2) (pow c 2) (* 2 a b)) -1) (+ a b (* -1 c))) (+ a b (* -1 c))) (pow (+ a c (* -1 b)) 2) (pow (+ (pow a 2) (pow b 2) (pow c 2) (* 2 a c)) -1) (pow (+ (pow a 2) (pow b 2) (pow c 2) (* 2 b c)) (* -1 (pow (+ b c (* -1 a)) 2)))) (pow (+ 1 a b (pow (+ b c (* -1 a)) 2) (* -1 c)) -1)) (+ -1 c (* -1 a) (* -1 b) (* -1 (pow (+ b c (* -1 a)) 2))))) 0)))
(check-sat)
(get-model)
(exit)