;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.


;pure laziness to leave these here ...
(def splice-unquote)
(def finally)

(def newline (fn* newline [] (print "\r\n")))
(def println 
  (fn* println [& args] (do (display args) (print " ") (newline))))


;during bootstrap we don't have destructuring let, loop or fn
(def
 ^{:macro true
   :added "1.0"}
 loop1 (fn* loop1 [& decl] (cons 'loop* decl)))  

 (def
 ^{:macro true
   :added "1.0"}
 fn0 (fn* fn0 [& decl] 
         (with-meta (cons 'fn* decl) 
                    (meta &form))))

(def
 ^{:doc "Same as (first (first x))"
   :arglists '([x]) }
 ffirst (fn0 ffirst [x] (first (first x))))

(def
 ^{:doc "Same as (next(first x))"
   :arglists '([x]) }
 nfirst (fn0 nfirst [x] (next (first x))))

(def
 ^{:doc "Same as (first (next x))"
   :arglists '([x]) }
 fnext (fn0 fnext [x] (first (next x))))

(def
 ^{:doc "Same as (next (next x))"
   :arglists '([x]) }
 nnext (fn0 nnext [x] (next (next x))))

(def 
 ^{:arglists '([coll])
   :doc "Return the last item in coll" 
  }
 last (fn0 last [s]
        (if (next s)
          (recur (next s))
          (first s))))

;(def second  (fn0 second [xs] (nth xs 1)))
(def second (fn0 second [xs] (first (next xs))))
      
(def 
 ^{:arglists '([coll])
   :doc "Return a seq of all but the last item in coll, in linear time"
  }
 butlast (fn0 butlast [s]
           (loop1 [ret [] s s]
             (if (next s)
               (recur (conj ret (first s)) (next s))
               (seq ret)))))  


;will redefine later
(def
 ^{:macro true
   :added "1.0"}
 fn (fn* fn [& decl] 
         (with-meta (cons 'fn* decl) 
                    (meta &form))))
(def 

 ^{:doc "Same as (def name (fn0 [params* ] exprs*)) or (def
    name (fn0 ([params* ] exprs*)+)) with any doc-string or attrs added
    to the var metadata. prepost-map defines a map with optional keys
    :pre and :post that contain collections of pre or post conditions."
   :arglists '([name doc-string? attr-map? [params*] prepost-map? body]
                [name doc-string? attr-map? ([params*] prepost-map? body)+ attr-map?])
   :macro true
   :added "1.0"}
 defn0 (fn0 defn0 [name & fdecl]
        (if (symbol? name)
          nil
          (throw (System.ArgumentException. "First argument to defn0 must be a symbol")))   ;;; IllegalArgumentException
        (let* [m (if (string? (first fdecl))
                  {:doc (first fdecl)}
                  {})
              fdecl (if (string? (first fdecl))
                      (next fdecl)
                      fdecl)
              m (if (map? (first fdecl))
                  (conj m (first fdecl))
                  m)
              fdecl (if (map? (first fdecl))
                      (next fdecl)
                      fdecl)
              fdecl (if (vector? (first fdecl))
                      (list fdecl)
                      fdecl)
              m (if (map? (last fdecl))
                  (conj m (last fdecl))
                  m)
              fdecl (if (map? (last fdecl))
                      (butlast fdecl)
                      fdecl)
              m (conj (if (meta name) (meta name) {}) m)]
          (list 'def (with-meta name m)
                (cons `fn0 fdecl) ))))

(defn0 inc [n] (+ n 1))

(defn0 dec [n] (- n 1))


(defn0 pos? [n] (< 0 n))

(defn0 neg? [n] (> 0 n))

(defn0 false?
  "Returns true if x is the value false, false otherwise."
  {:tag Boolean
   :added "1.0"}
  [x] (Inc.Util/identical x false))

(defn0 true?
  "Returns true if x is the value true, false otherwise."
  {:tag Boolean
   :added "1.0"}
  [x] (Inc.Util/identical x true))


(defn0 not
  "Returns true if x is logical false, false otherwise."
  {:tag Boolean
   :added "1.0"}
  [x] (if x false true))

(defn0 <= [a b] (not (> a b)))
(defn0 >= [a b] (not (< a b)))

(defn0 ref-set [r x] (alter r (fn0 [_] x)))

(defn0
 ^{:arglists '([map key val] [map key val & kvs])
   :doc "assoc[iate]. When applied to a map, returns a new map of the
    same (hashed/sorted) type, that contains the mapping of key(s) to
    val(s). When applied to a vector, returns a new vector that
    contains val at index. Note - index must be <= (count vector)."
   }
 assoc
   ([map key val] (assoc* map key val))
   ([map key val & kvs]
    (let* [ret (assoc map key val)]
      (if kvs
        (if (next kvs)
          (recur ret (first kvs) (second kvs) (nnext kvs))
          (throw (System.ArgumentException.                                                                ;;; IllegalArgumentException
                  "assoc expects even number of arguments after map/vector, found odd number")))
        ret)))
	)

(def

 ^{:doc "Like defn0, but the resulting function name is declared as a
  macro and will be used as a macro by the compiler when it is
  called."
   :arglists '([name doc-string? attr-map? [params*] body]
                [name doc-string? attr-map? ([params*] body)+ attr-map?])
   :added "1.0"}
  defmacro (fn0 [name & args]
             (let* [prefix (loop1 [p (list name) args args]
                            (let* [f (first args)]
                              (if (string? f)
                                (recur (cons f p) (next args))
                                (if (map? f)
                                  (recur (cons f p) (next args))
                                  p))))
                   fdecl (loop1 [fd args]
                           (if (string? (first fd))
                             (recur (next fd))
                             (if (map? (first fd))
                               (recur (next fd))
                               fd)))
                   fdecl (if (vector? (first fdecl))
                           (list fdecl)
                           fdecl)
                   add-args (fn0 [acc ds]
                              (if (nil? ds)
                                acc
                                (let* [d (first ds)]
                                  (if (map? d)
                                    (conj acc d)
                                    (recur (conj acc d) (next ds))))))
                   fdecl (seq (add-args [] fdecl))
                   decl (loop1 [p prefix d fdecl]
                          (if p
                            (recur (next p) (cons (first p) d))
                            d))
                          ]
               (list 'do
                     (cons `defn0 decl)
                     (list 'set-macro name)
                     (list 'var name)))))

(set-macro defmacro)
        
(defmacro comment [& body] )



(defmacro locking
  "Executes exprs in an implicit do, while holding the monitor of x.
  Will release the monitor of x in all circumstances."
  {:added "1.0"}
  [x & body]
  `(let* [lockee# ~x]
     (try
      (monitor-enter lockee#)
      ~@body
      (finally
       (monitor-exit lockee#)))))

(defmacro and
  "Evaluates exprs one at a time, from left to right. If a form
  returns logical false (nil or false), and returns that value and
  doesn't evaluate any of the other expressions, otherwise it returns
  the value of the last expr. (and) returns true."
  {:added "1.0"}
  ([] true)
  ([x] x)
  ([x & next]
  `(let* [and# ~x]
      (if and# (and ~@next) and#))))


(defmacro or
  "Evaluates exprs one at a time, from left to right. If a form
  returns a logical true value, or returns that value and doesn't
  evaluate any of the other expressions, otherwise it returns the
  value of the last expression. (or) returns nil."
  {:added "1.0"}
  ([] nil)
  ([x] x)
  ([x & next]
      `(let* [or# ~x]
         (if or# or# (or ~@next)))))

;(defn0 >= [a b] (or (> a b) (= a b)))
;(defn0 <= [a b] (or (< a b) (= a b)))



(defn0 xor [a b] (and (or a b) (not (and a b))))
(defmacro commute [r f & xs] `(alter ~r ~f ~@xs))


(defmacro ..
  "form => fieldName-symbol or (instanceMethodName-symbol args*)

  Expands into a member access (.) of the first member on the first
  argument, followed by the next member on the result, etc. For
  instance:

  (.. System (getProperties) (get \"os.name\"))

  expands to:

  (. (. System (getProperties)) (get \"os.name\"))

  but is easier to write, read, and understand."
  {:added "1.0"}
  ([x form] `(. ~x ~form))
  ([x form & more] `(.. (. ~x ~form) ~@more)))

;(defmacro list [& xs] `(map eval (quote ~xs)))


(defmacro ->
  "Threads the expr through the forms. Inserts x as the
  second item in the first form, making a list of it if it is not a
  list already. If there are more forms, inserts the first form as the
  second item in second form, etc."
  {:added "1.0"}
  ([x] x)
  ([x form] (if (seq? form)
              ;(with-meta `(~(first form) ~x ~@(next form)) (meta form))
              `(~(first form) ~x ~@(next form)) 
              (list form x)))
  ([x form & more] `(-> (-> ~x ~form) ~@more)))

(defmacro ->>
  "Threads the expr through the forms. Inserts x as the
  last item in the first form, making a list of it if it is not a
  list already. If there are more forms, inserts the first form as the
  last item in second form, etc."
  {:added "1.1"}
  ([x form] (if (seq? form)
              (with-meta `(~(first form) ~@(next form)  ~x) (meta form))
              (list form x)))
  ([x form & more] `(->> (->> ~x ~form) ~@more)))



(defmacro when
  "Evaluates test. If logical true, evaluates body in an implicit do."
  {:added "1.0"}
  [test & body]    
  (list 'if test (cons 'do body) nil)
    )
    
(defmacro when-not
  "Evaluates test. If logical false, evaluates body in an implicit do."
  {:added "1.0"}
  [test & body]
    (list 'if test nil (cons 'do body))
)

(defn0 spread
  {:private true}
  [arglist]
  (cond
   (nil? arglist) nil
   (nil? (next arglist)) (seq (first arglist))
   :else (cons (first arglist) (spread (next arglist)))))

(defn0 list*
  "Creates a new list containing the items prepended to the rest, the
  last of which will be treated as a sequence."
  ([args] (seq args))
  ([a args] (cons a args))
  ([a b args] (cons a (cons b args)))
  ([a b c args] (cons a (cons b (cons c args))))
  ([a b c d & more]
     (cons a (cons b (cons c (cons d (spread more)))))))

(defn0 map
  "Returns a lazy sequence consisting of the result of applying f to the
  set of first items of each coll, followed by applying f to the set
  of second items in each coll, until any one of the colls is
  exhausted.  Any remaining items in other colls are ignored. Function
  f should accept number-of-colls arguments."
  {:added "1.0"
   :static true}
  ([f coll]
   (lazy-seq
    (when-let [s (seq coll)]
        (cons (f (first s)) (map f (rest s))))))
  ([f c1 c2]
   (lazy-seq
    (let* [s1 (seq c1) s2 (seq c2)]
      (when (and s1 s2)
        (cons (f (first s1) (first s2))
              (map f (rest s1) (rest s2)))))))
  ([f c1 c2 c3]
   (lazy-seq
    (let* [s1 (seq c1) s2 (seq c2) s3 (seq c3)]
      (when (and  s1 s2 s3)
        (cons (f (first s1) (first s2) (first s3))
              (map f (rest s1) (rest s2) (rest s3)))))))
  ([f c1 c2 c3 & colls]
   (let* [step (fn0 step [cs]
                 (lazy-seq
                  (let* [ss (map seq cs)]
                    (when (every? identity ss)
                      (cons (map first ss) (step (map rest ss)))))))]
     (map #(apply f %) (step (conj colls c3 c2 c1))))))

(defmacro ^{:private true} assert-args 
  [& pairs]
  `(do (when-not ~(first pairs)
         (throw (System.ArgumentException.                            ;;;IllegalArgumentException.
                  (str (first ~'&form) " requires " ~(second pairs) " in " ~'*ns* ))))
     ~(let* [more (nnext pairs)]
        (when more
          (list* `assert-args more))))
)


(defn0 vary-meta
 "Returns an object of the same type and value as obj, with
  (apply f (meta obj) args) as its metadata."
 [obj f & args]
  (with-meta obj (apply f (meta obj) args)))


(defmacro if-not
  "Evaluates test. If logical false, evaluates and returns then expr, 
  otherwise else expr, if supplied, else nil."  
  ([test then] `(if-not ~test ~then nil))
  ([test then else]
   `(if (not ~test) ~then ~else)))

(defn0 not=
  "Same as (not (= obj1 obj2))"
  {:tag Boolean
   :added "1.0"
   :static true}
  ([x] false)
  ([x y] (not (= x y)))
  ([x y & more]
   (not (apply = x y more))))  



(defmacro if-let
  "bindings => binding-form test

  If test is true, evaluates then with binding-form bound to the value of 
  test, if not, yields else"
  {:added "1.0"}
  ([bindings then]
   `(if-let ~bindings ~then nil))
  ([bindings then else & oldform]
   (assert-args
     (vector? bindings) "a vector for its binding"
     (nil? oldform) "1 or 2 forms after binding vector"
     (== 2 (count bindings)) "exactly 2 forms in binding vector"
   )
   (let* [form (bindings 0) tst (bindings 1)]
     `(let* [temp# ~tst]
        (if temp#
          (let* [~form temp#]
            ~then)
          ~else)))
  )
)

(defmacro when-let
  "bindings => binding-form test

  When test is true, evaluates body with binding-form bound to the value of test"
  {:added "1.0"}
  [bindings & body]
  (assert-args
     (vector? bindings) "a vector for its binding"
     (== 2 (count bindings)) "exactly 2 forms in binding vector") 
   (let* [form (bindings 0) tst (bindings 1)]
    `(let* [temp# ~tst]
       (when temp#
         (let* [~form temp#]
           ~@body)))))

(defn0 range 
  "Returns a lazy seq of nums from start (inclusive) to end
  (exclusive), by step, where start defaults to 0 and step to 1, and end
  to infinity."
  ([] (range 0 System.Int64/MaxValue 1))
  ([end] (range 0 end 1))
  ([start end] (range start end 1))
  ([start end step]
   (lazy-seq
    (let* [comp (if (pos? step) < >)]
      (if (comp start end)
          (cons start (range (+ start step) end step)))))))


(defn0 take
  "Returns a lazy sequence of the first n items in coll, or all items if
  there are fewer than n."
  [n coll]
   (lazy-seq
   (when (pos? n) 
     (when-let [s (seq coll)]
      (cons (first s) (take (dec n) (rest s))))))
	  )

(defn0 filter
  "Returns a lazy sequence of the items in coll for which
  (pairs item) returns true. pred must be free of side-effects."
  [pred coll]
  (let* [step (fn0 [p c]
                 (when-let [s (seq c)]
                   (if (p (first s))
                     (cons (first s) (filter p (rest s)))
                     (recur p (rest s)))))]
    (lazy-seq (step pred coll))))

(defn0 dorun
  "When lazy sequences are produced via functions that have side
  effects, any effects other than those needed to produce the first
  element in the seq do not occur until the seq is consumed. dorun can
  be used to force any effects. Walks through the successive nexts of
  the seq, does not retain the head and returns nil."
  {:added "1.0"
   :static true}
  ([coll]
   (when (seq coll)
    ; (println "dorun : " (first coll))
     (recur (next coll))))
  ([n coll]
   (when (and (seq coll) (pos? n))
     (recur (dec n) (next coll)))))

(defn0 doall
  "When lazy sequences are produced via functions that have side
  effects, any effects other than those needed to produce the first
  element in the seq do not occur until the seq is consumed. doall can
  be used to force any effects. Walks through the successive nexts of
  the seq, retains the head and returns it, thus causing the entire
  seq to reside in memory at one time."
  {:added "1.0"
   :static true}
  ([coll]
   (dorun coll)
   coll)
  ([n coll]
   (dorun n coll)
   coll))

(defn0 nthnext
  "Returns the nth next of coll, (seq coll) when n is 0."
  {:added "1.0"
   :static true}
  [coll n]
    (loop1 [n n xs (seq coll)]
      (if (and xs (pos? n))
        (recur (dec n) (next xs))
        xs)))

(defn0 nthrest
  "Returns the nth rest of coll, coll when n is 0."
  {:added "1.3"
   :static true}
  [coll n]
    (loop1 [n n xs coll]
      (if (and (pos? n) (seq xs))
        (recur (dec n) (rest xs))
        xs)))

(defn0 partition
  "Returns a lazy sequence of lists of n items each, at offsets step
  apart. If step is not supplied, defaults to n, i.e. the partitions
  do not overlap. If a pad collection is supplied, use its elements as
  necessary to complete last partition upto n items. In case there are
  not enough padding elements, return a partition with less than n items."
  {:added "1.0"
   :static true}
  ([n coll]
     (partition n n coll))
  ([n step coll]
     (lazy-seq
       (when-let [s (seq coll)]
         (let* [p (doall (take n s))]
           (when (= n (count p))
             (cons p (partition n step (nthrest s step))))))))
  ([n step pad coll]
     (lazy-seq
       (when-let [s (seq coll)]
         (let* [p (doall (take n s))]
           (if (= n (count p))
             (cons p (partition n step pad (nthrest s step)))
             (list (take n (concat p pad)))))))))

(defn0 reduce1
       ([f coll]
             (let* [s (seq coll)]
               (if s
                 (reduce1 f (first s) (next s))
                 (f))))
       ([f val coll]
          (let* [s (seq coll)]
            (if s
                (recur f (f val (first s)) (next s))
              val))))
              
; fold function (f) over seq (xs) while accumulating (a)
(defn0 fold [f a xs]
  (let* [x (first xs)]
    (if (not x) 
    a
      (fold f (f x a) (rest xs)))
    ))

; (define reverse (fn0 [xs] (fold cons '() xs)))
(defn0 reverse [xs] (fold cons [] xs)) 


(defmacro while
  "Repeatedly executes body while test expression is true. Presumes
  some side-effect will cause test to become false/nil. Returns nil"
  {:added "1.0"}
  [test & body]
  `(loop1 []
     (when ~test
       ~@body
       (recur))))

(defn0 push-thread-bindings
  "WARNING: This is a low-level function. Prefer high-level macros like
  binding where ever possible.

  Takes a map of Var/value pairs. Binds each Var to the associated value for
  the current thread. Each call *MUST* be accompanied by a matching call to
  pop-thread-bindings wrapped in a try-finally!
  
      (push-thread-bindings bindings)
      (try
        ...
        (finally
          (pop-thread-bindings)))"
  {:added "1.1"
   :static true}
  [bindings]
  (inc.Util/pushThreadBindings bindings))

(defn0 pop-thread-bindings
  "Pop one set of bindings pushed with push-binding before. It is an error to
  pop bindings without pushing before."
  {:added "1.1"
   :static true}
  []
  (inc.Util/popThreadBindings))

(defn0 get-thread-bindings
  "Get a map with the Var/value pairs which is currently in effect for the
  current thread."
  {:added "1.1"
   :static true}
  []
  (inc.Util/getThreadBindings))

(defn0 with-bindings*
  "Takes a map of Var/value pairs. Installs for the given Vars the associated
  values as thread-local bindings. Then calls f with the supplied arguments.
  Pops the installed bindings after f returned. Returns whatever f returns."
  {:added "1.1"
   :static true}
  [binding-map f & args]
  (push-thread-bindings binding-map)
  (try
    (apply f args)
    (finally
      (pop-thread-bindings))))

(defmacro with-bindings
  "Takes a map of Var/value pairs. Installs for the given Vars the associated
  values as thread-local bindings. The executes body. Pops the installed
  bindings after body was evaluated. Returns the value of body."
  {:added "1.1"}
  [binding-map & body]
  `(with-bindings* ~binding-map (fn0 [] ~@body)))

(defn0 bound-fn*
  "Returns a function, which will install the same bindings in effect as in
  the thread at the time bound-fn* was called and then call f with any given
  arguments. This may be used to define a helper function which runs on a
  different thread, but needs the same bindings in place."
  {:added "1.1"
   :static true}
  [f]
  (let* [bindings (get-thread-bindings)]
    (fn0 [& args]
      (apply with-bindings* bindings f args))))

(defmacro bound-fn
  "Returns a function defined by the given fntail, which will install the
  same bindings in effect as in the thread at the time bound-fn was called.
  This may be used to define a helper function which runs on a different
  thread, but needs the same bindings in place."
  {:added "1.1"}
  [& fntail]
  `(bound-fn* (fn0 ~@fntail)))



(def sum (fn0 [xs] (fold + 0 xs)))

(def odd? (fn0 [x] (= 1 (% x 2))))
(def even? (fn0 [x] (= 0 (% x 2))))

;(defn0 require [e] (if e e (amb)))

(defn0 cdr [x] (rest x))
(defn0 car [x] (first x))

(defn0 member? [item lst]
     (if lst
         (if (= item (car lst))
             true
             (member? item (cdr lst)))
         false))

(defn0 distinct? [lst]
    (if lst
         (if (member? (car lst) (cdr lst))
             false
             (distinct? (cdr lst)))
         true))

(defn0 exclude [items lst]
     (if lst
         (if (member? (car lst) items)
             (exclude items (cdr lst))
             (cons (car lst) (exclude items (cdr lst))))
         ()))

(defn0 not=
  "Same as (not (= obj1 obj2))"
  {:tag Boolean
   :added "1.0"
   :static true}
  ([x] false)
  ([x y] (not (= x y)))
  ([x y & more]
   (not (apply = x y more))))  

(defn0 comp
  "Takes a set of functions and returns a fn that is the composition
  of those fns.  The returned fn takes a variable number of args,
  applies the rightmost of fns to the args, the next
  fn (right-to-left) to the result, etc."
  {:added "1.0"
   :static true}
  ([] identity)
  ([f] f)
  ([f g] 
     (fn0 
       ([] (f (g)))
       ([x] (f (g x)))
       ([x y] (f (g x y)))
       ([x y z] (f (g x y z)))
       ([x y z & args] (f (apply g x y z args)))))
  ([f g h] 
     (fn0 
       ([] (f (g (h))))
       ([x] (f (g (h x))))
       ([x y] (f (g (h x y))))
       ([x y z] (f (g (h x y z))))
       ([x y z & args] (f (g (apply h x y z args))))))
  ([f1 f2 f3 & fs]
    (let* [fs (reverse (list* f1 f2 f3 fs))]
      (fn0 [& args]
        (loop1 [ret (apply (first fs) args) fs (next fs)]
          (if fs
            (recur ((first fs) ret) (next fs))
            ret))))))


(defn0 concat
  "Returns a lazy seq representing the concatenation of the elements in the supplied colls."
  {:added "1.0"
   :static true}
  ([] (lazy-seq nil))
  ([x] (lazy-seq x))
  ([x y]
    (lazy-seq
      (let*  [s (seq x)]
        (if s
            (cons (first s) (concat (rest s) y))
          y))))
  ([x y & zs]
     (let*  [cat (fn0 cat [xys zs]
                 (lazy-seq
                   (let*  [xys (seq xys)]
                     (if xys
                         (cons (first xys) (cat (rest xys) zs))
                       (when zs
                         (cat (first zs) (next zs)))))))]
       (cat (concat x y) zs))))

;;;;;;;;;;;;;;;;;;; sequence fns  ;;;;;;;;;;;;;;;;;;;;;;;
(defn0 sequence
  "Coerces coll to a (possibly empty) sequence, if it is not already
  one. Will not force a lazy seq. (sequence nil) yields ()"  
  {:added "1.0"
   :static true}
  [coll]
   (if (seq? coll) coll
    (or (seq coll) ())))

(defn0 every?
  "Returns true if (pred x) is logical true for every x in coll, else
  false."
  {:tag Boolean
   :added "1.0"
   :static true}
  [pred coll]
  (cond
   (nil? (seq coll)) true
   (pred (first coll)) (recur pred (next coll))
   :else false))

(def
 ^{:tag Boolean
   :doc "Returns false if (pred x) is logical true for every x in
  coll, else true."
   :arglists '([pred coll])
   :added "1.0"}
 not-every? (comp not every?))


(defn0 some
  "Returns the first logical true value of (pred x) for any x in coll,
  else nil.  One common idiom is to use a set as pred, for example
  this will return :fred if :fred is in the sequence, otherwise nil:
  (some #{:fred} coll)"
  {:added "1.0"
   :static true}
  [pred coll]
    (when (seq coll)
      (or (pred (first coll)) (recur pred (next coll)))))

(def
 ^{:tag Boolean
    :doc "Returns false if (pred x) is logical true for any x in coll,
  else true."
    :arglists '([pred coll])
   :added "1.0"}
 not-any? (comp not some))

(defn0 max
  "Returns the greatest of the nums."
  ([x] x)
  ([x y] (if (< x y) y x))
  ([x y & more]
   (reduce1 max (max x y) more)))

(defn0 min
  "Returns the least of the nums."
  ([x] x)
  ([x y] (if (> x y) y x))
  ([x y & more]
   (reduce1 min (min x y) more)))

(defmacro dotimes
  "bindings => name n

  Repeatedly executes body (presumably for side-effects) with name
  bound to integers from 0 through n-1."
  {:added "1.0"}
  [bindings & body]
  (let*  [i (first bindings)
        n (second bindings)]
    `(let*  [n# ~n]
       (loop1 [~i 0]
         (when (< ~i n#)
           ~@body
           (recur (inc ~i)))))))
           
(defn0 mapcat
  "Returns the result of applying concat to the result of applying map
  to f and colls.  Thus function f should return a collection."
  [f & colls]
    (apply concat (apply map f colls)))
 
(defn0 complement
  "Takes a fn f and returns a fn that takes the same arguments as f,
  has the same effects, if any, and returns the opposite truth value."
  [f] 
  (fn0 
    ([] (not (f)))
    ([x] (not (f x)))
    ([x y] (not (f x y)))
    ([x y & zs] (not (apply f x y zs)))))

(defn0 constantly
  "Returns a function that takes any number of arguments and returns x."
  [x] (fn0 [& args] x))



(defn0 remove
  "Returns a lazy sequence of the items in coll for which
  (pred item) returns false. pred must be free of side-effects."
  [pred coll]
  (filter (complement pred) coll))


(defn0 take-while
  "Returns a lazy sequence of successive items from coll while
  (pred item) returns true. pred must be free of side-effects."
  [pred coll]
  (lazy-seq
   (when-let [s (seq coll)]
       (when (pred (first s))
         (cons (first s) (take-while pred (rest s)))))))

(defn0 drop
  "Returns a lazy sequence of all but the first n items in coll."
  [n coll]
  (let*  [step (fn0 [n coll]
               (let*  [s (seq coll)]
                 (if (and (pos? n) s)
                   (recur (dec n) (rest s)) 
                   s)))]
    (lazy-seq (step n coll))))

(defn0 drop-last
  "Return a lazy sequence of all but the last n (default 1) items in coll"
  ([s] (drop-last 1 s))
  ([n s] (map (fn0 [x _] x) s (drop n s))))

(defn0 take-last
  "Returns a seq of the last n items in coll.  Depending on the type
  of coll may be no better than linear time.  For vectors, see also subvec."
  {:added "1.1"
   :static true}
  [n coll]
  (loop1 [s (seq coll), lead (seq (drop n coll))]
    (if lead
      (recur (next s) (next lead))
      s)))

(defn0 drop-while
  "Returns a lazy sequence of the items in coll starting from the first
  item for which (pred item) returns logical false."
  {:added "1.0"
   :static true}
  [pred coll]
  (let*  [step (fn0 [pred coll]
               (let*  [s (seq coll)]
                 (if (and s (pred (first s)))
                   (recur pred (rest s))
                   s)))]
    (lazy-seq (step pred coll))))
    
(defn0 cycle
  "Returns a lazy (infinite!) sequence of repetitions of the items in   coll."
  {:added "1.0"
   :static true}
  [coll] (lazy-seq 
          (when-let [s (seq coll)] 
              (concat s (cycle s)))))
              
(defn0 split-at
  "Returns a vector of [(take n coll) (drop n coll)]"
 [n coll]
    [(take n coll) (drop n coll)])

(defn0 split-with
  "Returns a vector of [(take-while pred coll) (drop-while pred coll)]"
  [pred coll]
    [(take-while pred coll) (drop-while pred coll)])

(defn0 repeat
  "Returns a lazy (infinite! or length n if supplied) sequence of xs."
  ([x] (lazy-seq (cons x (repeat x))))
  ([n x] (take n (repeat x))))
  
(defn0 iterate
  "Returns a lazy sequence of x, (f x), (f (f x)) etc. f must be free of side-effects"
  [f x] (lazy-seq (cons x (iterate f (f x)))))



(defmacro ns
  "Sets *ns* to the namespace named by name (unevaluated), creating it
  if needed.  references can be zero or more of: (:refer-inc ...)
  (:require ...) (:use ...) (:import ...) (:load ...)
  with the syntax of refer-inc/require/use/import/load
  respectively, except the arguments are unevaluated and need not be
  quoted. If :refer-inc is not used, a
  default (refer 'inc) is used.  Use of ns is preferred to
  individual calls to in-ns/require/use/import:

  (ns foo.bar
    (:refer-inc :exclude [ancestors printf])
    (:require (inc.contrib sql combinatorics))
    (:use (my.lib this that))
    (:import (Inc.Util Date Timer Random)
              (java.sql Connection Statement)))"
  {:arglists '([name docstring? attr-map? references*])
   :added "1.0"}

  [name & references]
  (let* [process-reference (fn0 [[kname & args]]
                               `(~(symbol "inc.core" (inc.core/name kname))
                               ~@(map #(list 'quote %) args)))
        docstring  (when (string? (first references)) (first references))
        references (if docstring (next references) references)
        name (if docstring
               (vary-meta name assoc :doc docstring)
               name)
        metadata   (when (map? (first references)) (first references))
        references (if metadata (next references) references)
        name (if metadata
               (vary-meta name merge metadata)
               name)
        ]
    `(do
       (in-ns '~name)      
        ~@(when (and (not= name 'inc.core) (not-any? #(= :refer-inc (first %)) references))
            `((inc.core/refer '~'inc.core)))
         ~@(map process-reference references))
        (if (.Equals '~name 'inc.core)           
          nil
          (do (dosync (commute @#'*loaded-libs* conj '~name)) nil))))

(defn0 dissoc
  "dissoc[iate]. Returns a new map of the same (hashed/sorted) type,
  that does not contain a mapping for key(s)."
  {:added "1.0"
   :static true}
  ([map] map)
  ([map key]
   (dissoc1 map key))
  ([map key & ks]
   (let* [ret (dissoc map key)]
     (if ks
       (recur ret (first ks) (next ks))
       ret))))

;redefine let and loop  with destructuring
(defn0 destructure [bindings]
  (let* [bents (partition 2 bindings)
        pb (fn0 pb [bvec b v]
               (let*  [pvec
                     (fn0 [bvec b val]
                       (let*  [gvec (gensym "vec__")]
                         (loop1 [ret (-> bvec (conj gvec) (conj val))
                                n 0
                                bs b
                                seen-rest? false]
                           (if (seq bs)
                             (let*  [firstb (first bs)]
                               (cond
                                (= firstb '&)  (recur (pb ret (second bs) (list `nthnext gvec n))
                                                     n
                                                     (nnext bs)
                                                     true)
                                (= firstb :as) (pb ret (second bs) gvec)
                                :else (if seen-rest?
                                        (throw (new System.Exception "Unsupported binding form, only :as can follow & parameter"))
                                        (recur (pb ret firstb  (list `nth gvec n nil))
                                               (inc n)
                                               (next bs)
                                               seen-rest?))))
                             ret))))
                     pmap
                     (fn0 [bvec b v]
                       (let*  [gmap (gensym "map__")
                               gmapseq (with-meta gmap {:tag 'ISeq})
                               defaults (:or b)]
                         (loop1 [ret (-> bvec (conj gmap) (conj v)
                                        (conj gmap) (conj `(if (seq? ~gmap) (make-map (seq ~gmapseq)) ~gmap))
                                        ((fn0 [ret]
                                           (if (:as b)
                                             (conj ret (:as b) gmap)
                                             ret))))
                                bes (reduce1
                                     (fn0 [bes entry]
                                       (reduce1 #(assoc %1 %2 ((val entry) %2))
                                               (dissoc bes (key entry))
                                               ((key entry) bes)))
                                     (dissoc b :as :or)
                                     {:keys #(keyword (str %)), :syms #(list `quote %), :strs str})]
                           (if (seq bes)
                             (let*  [bb (key (first bes))
                                   bk (val (first bes))
                                   has-default (contains? defaults bb)]
                               (recur (pb ret bb (if has-default
                                                   (list `get gmap bk (defaults bb))
                                                   (list `get gmap bk)))
                                      (next bes)))
                             ret))))]
                 (cond
                  (symbol? b) (-> bvec (conj b) (conj v))
                  (vector? b) (pvec bvec b v)
                  (map? b) (pmap bvec b v)
                  :else (throw (new System.Exception (str "Unsupported binding form: " b))))))
        process-entry (fn0 [bvec b] (pb bvec (first b) (second b)))]
    (if (every? symbol? (map first bents))
      bindings
      (reduce1 process-entry [] bents))))

(defmacro let
  "binding => binding-form init-expr

  Evaluates the exprs in a lexical context in which the symbols in
 the binding-forms are bound to their respective init-exprs or parts
  therein."
  [bindings & body]
  (assert-args
     (vector? bindings) "a vector for its binding"
     (even? (count bindings)) (str "an even number of forms in binding vector " (count bindings)))
 `(let* ~(destructure bindings) ~@body))

(defn0 ^{:private true}
  maybe-destructured
  [params body]
  (if (every? symbol? params)
    (cons params body)
    (loop* [params params
           new-params []
           lets []]
      (if params
        (if (symbol? (first params))
          (recur (next params) (conj new-params (first params)) lets)
          (let* [gparam (gensym "p__")]
            (recur (next params) (conj new-params gparam)
                   (-> lets (conj (first params)) (conj gparam)))))
        `(~new-params
          (let ~lets
            ~@body))))))

;redefine fn with destructuring and pre/post conditions
(defmacro fn
  "params => positional-params* , or positional-params* & next-param
  positional-param => binding-form
  next-param => binding-form
  name => symbol

  Defines a function"
  {:added "1.0", :special-form true,
   :forms '[(fn name? [params* ] exprs*) (fn name? ([params* ] exprs*)+)]}
  [& sigs]
    (let [name (if (symbol? (first sigs)) (first sigs) nil)
          sigs (if name (next sigs) sigs)
          sigs (if (vector? (first sigs)) 
                 (list sigs) 
                 (if (seq? (first sigs))
                   sigs
                   ;; Assume single arity syntax
                   (throw (System.ArgumentException.                                 ;;; IllegalArgumentException
                            (if (seq sigs)
                              (str "Parameter declaration " 
                                   (first sigs)
                                   " should be a vector")
                              (str "Parameter declaration missing"))))))
          psig (fn* [sig]
                 ;; Ensure correct type before destructuring sig
                 (when (not (seq? sig))
                   (throw (System.ArgumentException.                                ;;; IllegalArgumentException
                            (str "Invalid signature " sig
                                 " should be a list"))))
                 (let [[params & body] sig
                       _ (when (not (vector? params))
                           (throw (System.ArgumentException.                        ;;; IllegalArgumentException
                                    (if (seq? (first sigs))
                                      (str "Parameter declaration " params
                                           " should be a vector")
                                      (str "Invalid signature " sig
                                           " should be a list")))))
                       conds (when (and (next body) (map? (first body))) 
                                           (first body))
                       body (if conds (next body) body)
                       conds (or conds (meta params))
                       pre (:pre conds)
                       post (:post conds)                       
                       body (if post
                              `((let [~'% ~(if (< 1 (count body)) 
                                            `(do ~@body) 
                                            (first body))]
                                 ~@(map (fn* [c] `(assert ~c)) post)
                                 ~'%))
                              body)
                       body (if pre
                              (concat (map (fn* [c] `(assert ~c)) pre) 
                                      body)
                              body)]
                   (maybe-destructured params body)))
          new-sigs (map psig sigs)]
      (with-meta
        (if name
          (lambda name new-sigs)
          (lambda new-sigs))
        (meta &form))
      ))

(defn0 take-nth
  "Returns a lazy seq of every nth item in coll."
  {:added "1.0"
   :static true}
  [n coll]
    (lazy-seq
     (when-let [s (seq coll)]
       (cons (first s) (take-nth n (drop n s))))))

(defn0 interleave
  "Returns a lazy seq of the first item in each coll, then the second etc."
  {:added "1.0"
   :static true}
  ([c1 c2]
     (lazy-seq
      (let* [s1 (seq c1) s2 (seq c2)]
        (when (and s1 s2)
          (cons (first s1) (cons (first s2) 
                                 (interleave (rest s1) (rest s2))))))))
  ([c1 c2 & colls] 
     (lazy-seq 
      (let* [ss (map seq (conj colls c2 c1))]
        (when (every? identity ss)
          (concat (map first ss) (apply tinterleave (map rest ss))))))))

(defn0 vector
  "Creates a new vector containing the args."
  {:added "1.0"
   :static true}
  ([] [])
  ([a] [a])
  ([a b] [a b])
  ([a b c] [a b c])
  ([a b c d] [a b c d])
  ([a b c d & args]
     (vec (cons a (cons b (cons c (cons d args)))))))



(defmacro loop
  "Evaluates the exprs in a lexical context in which the symbols in
  the binding-forms are bound to their respective init-exprs or parts
  therein. Acts as a recur target."
  {:added "1.0", :special-form true, :forms '[(loop1 [bindings*] exprs*)]}
  [bindings & body]
    (assert-args
      (vector? bindings) "a vector for its binding"
      (even? (count bindings)) "an even number of forms in binding vector")
    (let [db (destructure bindings)]
      (if (= db bindings)
        `(loop* ~bindings ~@body)
        (let [vs (take-nth 2 (drop 1 bindings))
              bs (take-nth 2 bindings)
              gs (map (fn [b] (if (symbol? b) b (gensym))) bs)
              bfs (reduce1 (fn [ret [b v g]]
                            (if (symbol? b)
                              (conj ret g v)
                              (conj ret g v b g)))
                          [] (map vector bs vs gs)) 
              ]
          `(let ~bfs
             (loop* ~(vec (interleave gs gs))
               (let ~(vec (interleave bs gs))
                 ~@body)))))))

(defn0 re-groups
  "returns a vector of the groups of the given match, the first element
  being the entire match."
  [m]                                        
    (vec (seq (. m Groups))))

(defn0 re-next
  "Returns the next match, if any, of given match"
  ([m]                                      
   (when (. m Success)
     (let* [nxt (. m NextMatch)])
         (when (. nxt Success) nxt))
  ([re s]                       
   (let* [m (re-match re s)]
     (when (. m Success) m)))))

(defn0 re-seq
  "Returns a lazy sequence of successive matches of pattern in string,
   each such match processed with re-groups."
  [re s]                          
  (let* [step (fn* step [m]
               (when (. m Success)
                 (cons (re-groups m) (lazy-seq (step (. m NextMatch))))))]
        (step (re-match re s))))

(defn0 re-matches
  "Returns the first match, if any, of string to pattern"
  [re s]
    (let* [m (re-match re s)]
      (when (. m Success)
        (re-groups m))))

(defmacro when-first
  "bindings => x xs

  Roughly the same as (when (seq xs) (let [x (first xs)] body)) but xs is evaluated only once"
  {:added "1.0"}
  [bindings & body]
  (assert-args
     (vector? bindings) "a vector for its binding"
     (= 2 (count bindings)) "exactly 2 forms in binding vector")
  (let [[x xs] bindings]
    `(when-let [xs# (seq ~xs)]
       (let [~x (first xs#)]
           ~@body))))

(def 

 ^{:doc "Same as (def name (fn0 [params* ] exprs*)) or (def
    name (fn0 ([params* ] exprs*)+)) with any doc-string or attrs added
    to the var metadata. prepost-map defines a map with optional keys
    :pre and :post that contain collections of pre or post conditions."
   :arglists '([name doc-string? attr-map? [params*] prepost-map? body]
                [name doc-string? attr-map? ([params*] prepost-map? body)+ attr-map?])
   :macro true
   :added "1.0"}
 defn (fn defn [name & fdecl]
        (if (symbol? name)
          nil
          (throw (System.ArgumentException. "First argument to defn0 must be a symbol")))   ;;; IllegalArgumentException
        (let* [m (if (string? (first fdecl))
                  {:doc (first fdecl)}
                  {})
              fdecl (if (string? (first fdecl))
                      (next fdecl)
                      fdecl)
              m (if (map? (first fdecl))
                  (conj m (first fdecl))
                  m)
              fdecl (if (map? (first fdecl))
                      (next fdecl)
                      fdecl)
              fdecl (if (vector? (first fdecl))
                      (list fdecl)
                      fdecl)
              m (if (map? (last fdecl))
                  (conj m (last fdecl))
                  m)
              fdecl (if (map? (last fdecl))
                      (butlast fdecl)
                      fdecl)
              m (conj (if (meta name) (meta name) {}) m)]
          (list 'def (with-meta name m)
                (cons `fn fdecl) ))))
(defmacro lazy-cat
  "Expands to code which yields a lazy sequence of the concatenation
  of the supplied colls.  Each coll expr is not evaluated until it is
  needed.
  
  (lazy-cat xs ys zs) === (concat (lazy-seq xs) (lazy-seq ys) (lazy-seq zs))" 
  {:added "1.0"}
  [& colls]
  `(concat ~@(map #(list `lazy-seq %) colls)))

(defmacro for
  "List comprehension. Takes a vector of one or more
   binding-form/collection-expr pairs, each followed by zero or more
   modifiers, and yields a lazy sequence of evaluations of expr.
   Collections are iterated in a nested fashion, rightmost fastest,
   and nested coll-exprs can refer to bindings created in prior
   binding-forms.  Supported modifiers are: :let [binding-form expr ...],
   :while test, :when test.

  (take 100 (for [x (range 100000000) y (range 1000000) :while (< y x)] [x y]))"
  {:added "1.0"}
  [seq-exprs body-expr]
  (assert-args
    (vector? seq-exprs) "a vector for its binding"
    (even? (count seq-exprs)) "an even number of forms in binding vector")
  (let* [to-groups (fn [seq-exprs]
                      (reduce1 (fn [groups [k v]]
                                  (if (keyword? k)
                                     (conj (pop groups) (conj (peek groups) [k v])) 
                                     (conj groups [k v])))
                                [] (partition 2 seq-exprs)))
         err (fn [& msg] (throw (ArgumentException. ^String (apply str msg))))  ;;; IllegalArgumentException
         emit-bind (fn emit-bind [[[bind expr & mod-pairs]
                                & [[_ next-expr] :as next-groups]]]
      (let [giter (gensym "iter__")
           gxs (gensym "s__")
           do-mod (fn do-mod [[[k v :as pair] & etc]]
          (cond
            (= k :let) `(let ~v ~(do-mod etc))
            (= k :while) `(when ~v ~(do-mod etc))
            (= k :when) `(if ~v
                             ~(do-mod etc)
                             (recur (rest ~gxs)))
            (keyword? k) (err "Invalid 'for' keyword " k)
            next-groups
            `(let [iterys# ~(emit-bind next-groups)
                   fs# (seq (iterys# ~next-expr))]
              (if fs#
                (concat fs# (~giter (rest ~gxs)))
                (recur (rest ~gxs))))
            :else `(cons ~body-expr
                         (~giter (rest ~gxs)))))]
          (if next-groups
                        #_"not the inner-most loop"
                        `(fn ~giter [~gxs]
                           (lazy-seq
                             (loop [~gxs ~gxs]
                               (when-first [~bind ~gxs]
                                 ~(do-mod mod-pairs)))))
                        #_"inner-most loop"
                        (let [gi (gensym "i__")
                              gb (gensym "b__")
                              do-cmod (fn do-cmod [[[k v :as pair] & etc]]
                                        (cond
                                          (= k :let) `(let ~v ~(do-cmod etc))
                                          (= k :while) `(when ~v ~(do-cmod etc))
                                          (= k :when) `(if ~v
                                                         ~(do-cmod etc)
                                                         (recur
                                                           (inc ~gi)))
                                          (keyword? k)
                                            (err "Invalid 'for' keyword " k)
                                          :else
                                            `(do (chunk-append ~gb ~body-expr)  ;; never seems to be hit ?? (chunk-append doesn't exist)
                                                 (recur (inc ~gi)))))]
                          `(fn ~giter [~gxs]
                             (lazy-seq
                               (loop [~gxs ~gxs]
                                 (when-let [~gxs (seq ~gxs)]
                                     (let [~bind (first ~gxs)]
                                       ~(do-mod mod-pairs))))))))))
        ]
    `(let [iter# ~(emit-bind (to-groups seq-exprs))]
      (iter# ~(second seq-exprs)))))


