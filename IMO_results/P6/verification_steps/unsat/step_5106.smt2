(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -7025938432 (pow b 4)) (* -5339828224 (pow a 4)) (* -14495514624 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -7247757312 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 8120651776 b (pow a 3)) (* 25988386816 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)