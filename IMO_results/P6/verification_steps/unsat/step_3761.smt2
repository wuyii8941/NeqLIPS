(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 1109952 (pow (+ a b) 4)) (* (/ -1 1066125598639005607395328) (pow (+ (* 44492288 a) (* 57665024 b)) 4)) (* -113246208 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -56623104 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 57337856 b (pow a 3)) (* 196929536 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)