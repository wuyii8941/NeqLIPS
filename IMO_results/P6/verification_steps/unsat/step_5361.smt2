(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (= (* a b c) 1))
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (not (<= (+ (* -1796442880 (pow b 4)) (* -1374915328 (pow a 4)) (* -5435817984 (pow a (/ 4 3)) (pow b (/ 8 3))) (* 79916544 (pow a 2) (pow b 2)) (* 2030162944 b (pow a 3)) (* 6497096704 a (pow b 3))) 0)))
(check-sat)
(get-model)
(exit)