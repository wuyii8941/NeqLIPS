(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -28277536 (pow b 4)) (* -21691168 (pow a 4)) (* (/ 52029 4) (pow (+ (* 2 a) (* 2 b)) 4)) (* -56623104 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -28311552 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 2277746155448727517528064 (pow a 3) (pow b 3) (pow (+ (* 30888832 b) (* 100684672 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)