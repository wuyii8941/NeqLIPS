(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* 13319424 (pow a 4)) (* 13319424 (pow b 4)) (* (pow (* (pow a (* 1601722368 a)) (pow b (* 2075940864 b))) (pow (+ (* 533907456 a) (* 691980288 b)) -1)) (+ (* -691980288 b) (* -533907456 a))) (* -1358954496 (pow a (pow 3 -1)) (pow b (/ 11 3))) (* -679477248 (pow a (/ 10 3)) (pow b (/ 2 3))) (* 79916544 (pow a 2) (pow b 2)) (* 741331968 b (pow a 3)) (* 2416432128 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)