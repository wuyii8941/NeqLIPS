(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -56555072 (pow b 4)) (* -43382336 (pow a 4)) (* (/ 52029 2) (pow (+ (* 2 a) (* 2 b)) 4)) (* -113246208 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -56623104 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 18221969243589820140224512 (pow a 3) (pow b 3) (pow (+ (* 61777664 b) (* 201369344 a)) -2))) 0)))
(check-sat)
(get-model)
(exit)