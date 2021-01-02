(set-logic LIA)


(synth-fun rec ((x Int) (y Int) (z Int)) Int
    ((end Int (x
                 y
                 z
            (* end end)
		    (+ end end)
		    (- end end)
            (ite StartBool end end)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (>=  end end)))))
		       
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (rec x1 x2 x3) (* (+ x1 x2) (- x2 x3))))
(constraint (>= (rec x1 x2 x3) (- (* x1 x2) (+ (* x1 x3) (* x2 x3)))))
(constraint (= (rec x1 0 x3) (* x1 (- 0 x3))))
(constraint (=> (<= 0 (* x1 x3)) (= (rec x1 x2 x3) (* (+ x1 x2) (- x2 x3)))))
(constraint (=> (= (rec x1 x2 x3) (* (+ x3 x2) (- x1 x3))) (<= 0 (* x2 x2))))
(constraint (= (rec x2 x3 x1) (* (+ x2 x3) (- x3 x1))))
(constraint (>= (rec x2 x3 x1) (- (* x2 x3) (+ (* x2 x1) (* x3 x1)))))
(constraint (= (rec x2 0 x1) (* x2 (- 0 x1))))
(constraint (=> (<= 0 (* x2 x1)) (= (rec x2 x3 x1) (* (+ x2 x3) (- x3 x1)))))
(constraint (=> (= (rec x2 x3 x1) (* (+ x1 x3) (- x2 x1))) (<= 0 (* x3 x3))))

(check-synth)
