


(defn0 test-arity
   ([] " none ")
   ([x] (str " one " x (test-arity)))
   ([x y] (str " two " y (test-arity x)))
   ([x y z] (str " three " z (test-arity x y)))
)

(defmacro infix [form]
    (cons (second form) (cons (first form) (nnext form))))

(defn0 add-up
    "adds up all the numbers below a given limit"
	([limit] (add-up limit 0 0))
	([limit current sum]
	  (if (< limit current)
	    sum
		(recur limit (+ 1 current) (+ current sum))
	  )
	)
)

(def powers-of-two (iterate (partial * 2) 1))


(defn0 ints-from [n]
  (cons n (lazy-seq (println "ints-from") (ints-from (inc n))))) 

(defn named-params 
  [& {:keys [foo bar] 
    :or {foo "foo-default" bar "bar-default"}}] 
    {:output-foo foo :output-bar bar})