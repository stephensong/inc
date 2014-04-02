module Test

(*
 * Copyright (c) 2014, Gary Stephenson
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution. 
 * 3. Neither the name of the author nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission. 
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 *)



open System.Text
open IncTypes
open Inc
open System
open Utils


let callFn nm args =
    let fn = lst(sym(nm) :: args )
    eval id [] fn

let prn (v : IncValue) = 
    print v

let prep env =
    List.ofSeq >> parse "__REPL__" >> List.head >> (eval id env) >> prn


let rep env =
    let eval' e =
        try eval id env e
        with ex ->  Dummy("Exception : " + ex.Message) |> e2v
    List.ofSeq >> parse "__REPL__" >> List.head >> eval' >> prn



let test ftest =

    load ftest

    let case source expected =
        try
            let output = rep [] source

            if output <> expected then
                printfn "TEST FAILED: %s [Expected: %s, Actual: %s]" source expected output
        with ex -> printfn "TEST CRASHED: %s [%s]" ex.Message source

    let rcase source expected =
        try
            let output = rep [] source

            let r = System.Text.RegularExpressions.Regex(expected)

            if not( r.IsMatch(output) ) then
                printfn "TEST FAILED: %s [Expected: %s, Actual: %s]" source expected output
        with ex -> printfn "TEST CRASHED: %s [%s]" ex.Message source

    let crash source expected =
        try
            prep [] source |> ignore
            printfn "CRASH TEST FAILED TO THROW :  %s" source 
        with ex ->
            if ex.Message <> expected then
                printfn "CRASH TEST FAILED: %s [Expected: %s, Actual: %s]" source expected ex.Message

    let nocrash source =
        try
            prep [] source |> ignore
        with ex ->
            printfn "NOCRASH TEST FAILED: %s ; error : %s" source ex.Message

    let strt = DateTime.Now

    case "(true? true)" "true"
    case "(true? false)" "false"
    case "(true? 0)" "false"
    case "(true? nil)" "false"
    case "(false? true)" "false"
    case "(false? false)" "true"
    case "(false? 0)" "false"
    case "(false? nil)" "false"
    case "(when true (+ 1 2 3))" "6"
    case "(when false (+ 1 2 3))" "nil"
    case "(list 1 2 3)" "(1 2 3)"
    rcase "(new System.DateTime 1955 7 25)" @"#inst ""1955-07-24T1.:00:00Z"""   
    rcase "(new System.DateTime 1955 7 25)" @"#inst ""1955-07-24T1.:00:00Z"""   
    case "#inst \"1955-07-24T14:00:00Z\""  @"#inst ""1955-07-24T14:00:00Z"""   
    case "(re-pattern \" [a-zA-z] \")" "#\"[a-zA-z]\""
    case "#\" [a-zA-z] \"" "#\"[a-zA-z]\""
    case "(even? 2)" "true" 
    case "(even? 3)" "false" 
    case "(macroexpand '(-> bvec (conj gvec) (conj val)))" "(conj (-> bvec (conj gvec)) val)"
    case "([1 3 5 7 9] 2)" "5"  // vectors are functions too!!
    case "(nth [1 2 4] 1)" "2"  //  0 - based indexing
    case "(nth [1 2 4] 2)" "4"  //  0 - based indexing
    case "(second [1 2 4])" "2"  //  0 - based indexing
    case "(map first ['(6 1) '(7 2)])" "(6 7)"
    case "(map first ['(a 1) '(b 2)])" "(a b)"
    case "(range 4  10 3 )" "(4 7)"
    case "(take 2 [1 2 3])" "(1 2)"
    case "(take 5 [1 2 3])" "(1 2 3)"
    case "(take 5 (range 10))" "(0 1 2 3 4)"
    case "(dorun (take 5 (range 10)))" "nil"
    case "(doall (take 5 (range 10)))" "(0 1 2 3 4)"
    case "(range 10)" "(0 1 2 3 4 5 6 7 8 9)"


    case "(let* [a 0 b 0] (map first ['(a 1) '(b 2)]))" "(a b)"
    case "(let* [a 0 b 0] (every? symbol? (map first ['(a 1) '(b 2)])))" "true"
    case "(let* [g 1 h 2] (symbol? 'g))" "true"

    case "(let* [square (fn0 [x] (* x x))] (square 4))" "16" // lambda
    case "(let* [lrfact (fn0 [x] (if (<= x 1) 1 (* x  (recur (- x 1)) )))] (lrfact 4))" "24"  // recur in lambda
    case "(defn0 rfact[x] (if (<= x 1) 1 (* x  (recur (- x 1))  )))" "#'user/rfact"  
    case "(rfact 4)" "24"  
    case "(defn0 fact[x] (if (<= x 1) 1 (* x  (fact (- x 1))  )))" "#'user/fact"  
    case "(fact 4)" "24"  
    case "(new System.DateTime 1955 7 25 0 0 0 (System.DateTimeKind/Utc))" "#inst \"1955-07-25T00:00:00Z\""
    case "(System.DateTime. 1955 7 25)" "#inst \"1955-07-24T14:00:00Z\""
    case "#inst \"1955-07-24T14:00:00Z\"" "#inst \"1955-07-24T14:00:00Z\""
    case "#inst \"1955-07-25\"" "#inst \"1955-07-25T00:00:00Z\""
    case "(.ToUpper \"select * from\")" "\"SELECT * FROM\""
    case "(and)" "true" 
    case "(and true 0)" "0" 
    case "(and true false)" "false" 
    case "\"hello\"" "\"hello\"" // strings
    case "\\\"" "\\\"" // return char
    case "\\b" "\\b" // return char
    case "\\f" "\\f" // return char
    case "\\n" "\\n" // return char
    case "\\newline" "\\n" // return char
    case "\\r" "\\r" // return char
    case "\\t" "\\t" // return char
    case "\\tab" "\\t" // return char
    case "\\\\" "\\\\" // return char
    case "1" "1" // numbers
    case "+1" "1" // explicit positive numbers
    case "-1" "-1" // negative numbers
    case "(*)" "1" // multiplication
    case "(* 2)" "2" // multiplication
    case "(* 2 3)" "6" // multiplication
    case "(* 2 3 4)" "24" // multiplication
    case "(/)" "1" // division ???
    case "(/ 2)" "2" // division
    case "(/ 9 2)" "9/2" // rational division
    case "(/ 12 2 3)" "2" // rational division
    case "(%)" "1" // modulus
    case "(% 2)" "2" // modulus
    case "(% 9 2)" "1" // modulus
    case "(% 8 2)" "0" // modulus
    case "(% 26 7 3)" "2" // modulus
    case "(+)" "0" // strange addition case
    case "(+ 10)" "10" // explicit positive
    case "+10" "10" // explicit positive
    case "(+ 10 2)" "12" // addition
    case "(+ 10 2 3)" "15" // addition
    case "(+ 10 2M 3)" "15M" // addition
    case "(+ 10 2.5 3)" "15.5M" // addition
    case "(+ 10 2.5f 3)" "15.5f" // addition
    case "(-)" "0" // strange subtraction case
    case "(- 10)" "-10" // negation
    case "-10" "-10" // negation
    case "(- 10 2)" "8" // subtraction
    case "(- 10 2 3)" "5" // subtraction
    case "(- 1 1)" "0"
    case "(let* [n 1] (dec n))" "0"
    case "(let* [n 0] (dec n))" "-1"
    case "(pos? 0)" "false"
    case "(neg? 0)" "false"
    case "(let* [n 0] (pos? (dec n)))" "false"
    case "(let* [n 0] (neg? (dec n)))" "true"
    case "(= 6 (/ 12 2))" "true"  // numeric equality
    case "(= 4.5 (/ 9 2))" "true"  // numeric equality
    case "(if (* 0 1) 10 20)" "10" // if
    case "(if (= 0 1) 10 20)" "20" // if
    case "(if (= 1 1) 10 20)" "10" // if
    case "(if (* 1 1) 10 bomb)" "10" // if (special form)
    case "(* 1234567890987654321N 1234567890987654321)" "1524157877457704723228166437789971041N" // bigint math
    case "(let* [x 2] x)" "2" // simple let
    case "(let* [a 00 b 10 c 20] (if (= a 0) b c))" "10" // conditional eval
    case "(let* [square (fn0 [x] (* x x))] square)" "Special" // print lambda
    case "(let* [times3 (let* [n 3] (fn0 [x] (* n x)))] (times3 4))" "12" // closure
    case "(let* [times3 (let* [makemultiplier (fn0 [n] (fn0 [x] (* n x)))] (makemultiplier 3))] (times3 5))" "15" // higher order functions
    //case "(every? symbol? (map first [(a 1) (b 2)]))" "true"
    case "(let* [a 1 b 2] (let* [a b b a] b))" "2" // let* binds sequentially
    case "(let* [a 5] (let* [b (* a 2)] (let* [c (- b 3)] c)))" "7" // poor-man's sequential expressions
    case "(let* [a 5 b (* a 2) c (- b 3)] c)" "7" // let* sequential expressions
    case "[1 2 3]" "[1 2 3]" // vector
    case "(first '(1 2 3))" "1" 
    case "(rest '(1 2 3))" "(2 3)" 
    case "(first [1 2 3])" "1" 
    case "(rest [1 2 3])" "(2 3)" 
    case "(cat '(1 2) '(a b))" "(1 2 a b)" // cat
    case "(cat '(1 2) '())" "(1 2)" // cat
    case "(cat '() '(1 2))" "(1 2)" // cat
    case "(cons 1 [2 3])" "(1 2 3)" // cons
    case "(cons 3 '())" "(3)" // cons x3
    case "(cons 1 (cons 2 (cons 3 '())))" "(1 2 3)" // cons x3
    case "(let* [a 1 b 2 c 3] [a b c])" "[1 2 3]" // vector
    case "(let* [a [1 2 3]] (first a))" "1" // car
    case "(let* [a [1 2 3]] (rest a))" "(2 3)" // cdr
    case "(quote (* 2 3))" "(* 2 3)" // quote primitive
    case "'(* 2 3)" "(* 2 3)" // quote primitive with sugar
    case "(eval '(* 2 3))" "6" // eval quoted expression
    case "(= '(1 2 3) [1 2 3])" "true"
    case "(quote (* 2 (- 5 2)))" "(* 2 (- 5 2))" // quote nested
    case "(syntax-quote (* 2 (unquote (- 5 2))))" "(* 2 3)" // syntax-quote nested unquote
    case "`(* 2 ~(- 5 2))" "(* 2 3)" // syntax-quote nested unquote with sugar
    case "(quote (quote 1 2 3))" "(quote 1 2 3)" // quote special form
    case "(let* [x 'rain y 'spain z 'plain] `(the ~x in ~y falls mainly on the ~z))"
         "(user/the rain user/in spain user/falls user/mainly user/on user/the plain)" // syntax-quote/unquote
    case "(do (def a 1) (do (set! a 2)) a)" "2" // do and assign
    //case "(let* [a 5 dummy (set! a 10)] a)" "10" // re-assign after let
    case "(do (def fac (fn0 [x] (if (> x 0) (* x (fac (- x 1))) 1))) (fac 7))" "5040" // define recursive
    case "(do (def square (fn0 [x] (* x x))) (square 4))" "16" // global def
    case "(let* [x 4] (do (def y 8) (* x y)))" "32" // local def
    case "(and false false)" "false" 
    case "(and true false)" "false" // or (false)
    case "(and true false)" "false" // or (false)
    case "(and true true)" "true" // or (true)
    case "(or false false)" "false" // or (false)
    case "(or true false)" "true" // or (true)
    case "(or false true)" "true" // or (true)
    case "(or true true)" "true" // or (true)
    case "(not false)" "true" // or (true)
    case "(not true)" "false" // or (false)
    case "(xor false false)" "false" // xor (false)
    case "(xor true false)" "true" // xor (true)
    case "(xor false true)" "true" // xor (true)
    case "(xor true true)" "false" // xor (false)
    case "(let* [square (fn0 [x] (* x x))] (map square '(1 2 3)))" "(1 4 9)" // mapping
    case "(let* [square (fn0 [x] (* x x))] (map square [1 2 3 4 5 6 7 8 9]))" "(1 4 9 16 25 36 49 64 81)" // mapping
    case "(let* [square (fn0 [x] (* x x))] (map square '(9)))" "(81)" // mapping single
    case "(let* [square (fn0 [x] (* x x))] (map square []))" "()" // mapping empty
    case "(let* [square (fn0 [x] (* x x))] (map square '()))" "()" 
    case "(fold * 1 '(2 3 4 5))" "120" // fold
    case "(fold * 1 [2 3 4 5])" "120" // fold
    case "(reverse [1 2 3])" "(3 2 1)" // reverse
    case ":mykeyword" ":mykeyword"
    case "{ :mykeyword 1 :another 2  }" "{:another 2 :mykeyword 1}"
    case "(first [1 2 3])" "1"
    case "(first { :mykeyword 1 :another 2  } )" "[:another 2]"
    case "({ :mykeyword 1 :another 2 } :another )" "2"  // maps are functions
    case "({ \"mykey\" 1 \"another\" 2 } \"mykey\" )" "1"  // maps are functions
    case "(:another { :mykeyword 1 :another 2 } )" "2"  // keywords are functions too
    case "(conj [1 2 3] 4 5)" "[1 2 3 4 5]"
    case "(conj [1 2 3] :a)" "[1 2 3 :a]"
    case "(conj '(1 2 3) :a)" "(:a 1 2 3)"
    case "(conj {2 1, 6 5} [4 3])" "{2 1 4 3 6 5}"
    case "(conj #{1 3 4} 2)" "#{1 2 3 4}"
    case "(count [1 2 3 4 5])" "5"
    case "(let* [testprms (fn0 [& prms] prms)] (testprms 1 2))" "(1 2)"
    case "(let* [countprms (fn0 [& prms] (count prms))] (countprms 1 2 3 4))" "4"
    case "(test-arity :first :second :third)" "\" three :third two :second one :first none \""
    case "(macroexpand-1 '(infix (2 + 3)))" "(+ 2 3)"
    case "(def current-track (ref \"Mars Bringer of War\"))" "#'user/current-track"
    crash "(ref-set current-track \"Venus Bringer of Peace\")" "No transaction running"
    case "(try (/ 1 0) (catch System.Exception e \"holy crap Batman\"))" "\"holy crap Batman\""
    case "(try (/ 1 0) (catch System.Exception e (. e Message)))" "\"Attempted to divide by zero.\""
    case "(macroexpand '(.. System (getProperties) (get \"os.name\")))" "(. (. System (getProperties)) (get \"os.name\"))"
    case "(if-let [a :anything] a (throw \"not evaluated\"))" ":anything"  // else (throw) not evaluated
    case "(if-let [a nil]  (throw \"not evaluated\") \"no\")" "\"no\""  // then (throw) not evaluated
    case "(when-let [a 1] a)" "1"  
    case "(when-let [a false] a)" "nil" 
    case "(str \"i\" \s \- \"cool\")" "\"is-cool\""
    case "`(this ~(symbol (str \"i\" \"s\" \- \"cool\")))" "(user/this is-cool)"   // syntax quote resolves symbols
    case "`[:a ~(+ 1 1) '~'c]" "[:a 2 (quote c)]"
    case "(eval `(list 1 `(2 ~~(- 9 6)) 4))" "(1 (2 3) 4)"
    case "(seq '())" "nil"
    case "(seq '(1))" "(1)"
    case "(seq \"\")" "nil"
    case "(seq \"abc\")" "(\\a \\b \\c)"
    case "(rest nil)" "()"
    case "(int \\a)" "97"
    case "(map int \"Hello, world!\")" "(72 101 108 108 111 44 32 119 111 114 108 100 33)"
    case "(assoc {:k1 1 :k2 2 :k3 3} :k2 4)" "{:k1 1 :k2 4 :k3 3}"
    case "(if nil (throw \"not evaluated\") \"ok\")" "\"ok\""
    case "(if '(list) \"ok\")" "\"ok\""
    case "(assoc {:k1 1 :k2 2 :k3 3} :k2 4 :k3 5)" "{:k1 1 :k2 4 :k3 5}"
    rcase "(macroexpand '#(%))" @"\(fn\* \[p1.*] \(p1.*\)\)"
    rcase "(macroexpand '#(-> %))" @"\(fn\* \[p1.*] \(-> p1.*\)\)"
    case "(contains? [1 2 4 5] 3)" "true"
    case "(contains? (range 10) 10)" "false"
    case "(contains? {:k1 1 :k2 2 :k3 3} :k2)" "true"
    case "(contains? {:k1 1 :k2 2 :k3 3} 3)" "false"
    case "(concat [1 2 3] '(4 5 6))" "(1 2 3 4 5 6)"
    case "(max 12 3 15 7 9)" "15"
    case "(min 12 3 15 7 9)" "3"
    case "(filter #(= % 20) (range 100))" "(20)"
    case "(filter #(= % 20) (map inc (range 100)))" "(20)"
    case "(remove #(> % 5) (range 10))" "(0 1 2 3 4 5)"
    case "(drop-last (range 6))" "(0 1 2 3 4)"
    case "(drop-last 2 (range 6))" "(0 1 2 3)"
    case "(take-while #(< % 5) (range 10))" "(0 1 2 3 4)"
    case "(take 7 (cycle (range 3)))" "(0 1 2 0 1 2 0)" 
    case "(take 5 (iterate inc 5))" "(5 6 7 8 9)"
    case "((partial * 2) 3)" "6"
    case "((partial * 2) 3 4)" "24"
    case "(let* [testprms (fn0 [& prms] prms)] (apply testprms [1 2]))" "(1 2)"
    case "(apply (partial * 2) [3])" "6"
    case "(apply (partial * 2) [3 4])" "24"
    case "(take 10 (iterate (partial * 2) 1))" "(1 2 4 8 16 32 64 128 256 512)"
    case "(take 10 powers-of-two)" "(1 2 4 8 16 32 64 128 256 512)"
    case "(nth (range 105678567878567856785678) 5)" "5"
    case "(let*  [gs [1 2 3]] (interleave gs gs))" "(1 1 2 2 3 3)"
    case "(drop 3 [1 2 3 4 5])" "(4 5)"
    case "(split-at 5 (range 10))" "[(0 1 2 3 4) (5 6 7 8 9)]"
    case "(dosync (ref-set current-track \"Venus Bringer of Peace\"))" "\"Venus Bringer of Peace\""
    case "(dosync (alter current-track (fn0 [cur] (str cur \" Galore\"))))" "\"Venus Bringer of Peace Galore\""
    case "(dosync (commute current-track (fn0 [cur] (str cur \" Galore\"))))" "\"Venus Bringer of Peace Galore Galore\""
    case "(let* [gs (take 3 (iterate (fn0 [_] (gensym \"test_\")) (gensym \"test_\")))] (= (str gs) (str gs)))" "true"
    case "(partition 2 [1 2 3 4 5 6 7])" "((1 2) (3 4) (5 6))"
    case "(partition 2  3 [1 2 3 4 5 6 7])" "((1 2) (4 5))"
    case "(partition 4 3 [9 10] [1 2 3 4 5 6 7 8])" "((1 2 3 4) (4 5 6 7) (7 8 9 10))"
    case "(let [[g h i] [1 2 3]] (/ g h))" "1/2"
    case "(let [[x y & more] [1 2 3 4 5 6]] (str x y more))" "\"12(3 4 5 6)\""
    case "(let [[x & more :as full-list] [1 2 3]] (str x \" \" more \" \" full-list))" "\"1 (2 3) [1 2 3]\""
    case "(let [{the-x :x the-y :y} {:x 5 :y 7}] (str \"x: \" the-x \" y: \" the-y))" "\"x: 5 y: 7\""
    case "(let [[[a b] [c d]] [[1 2][3 4]] ] (str a d b c))" "\"1423\""
    case "(let [{name :name [hole1 hole2] :scores} {:name \"Jim\" :scores [3 5 4 5]}] 
                (str \"name: \" name \" hole1: \" hole1 \" hole2: \" hole2))" "\"name: Jim hole1: 3 hole2: 5\""
    case "(let [funscore (fn [{name :name [hole1 hole2] :scores}] 
                          (str \"name: \" name \" hole1: \" hole1 \" hole2: \" hole2))] (funscore {:name \"Jim\" :scores [3 5 4 5]}))" 
                          "\"name: Jim hole1: 3 hole2: 5\""
    case "(let [x [1 2 3]] (let [[a b c] x [d] x] (list a b c d)))" "(1 2 3 1)"
    case "(let [x [1 2 3] gs (map (fn [i] (gensym \"test_\")) x)] (= (str gs) (str gs)))" "true"
    case "(let [x [1 2 3]] (loop [[a b c] x [d] x] (list a b c d)))" "(1 2 3 1)"
 
    case "(re-matches #\"quick\" \"The quick brown fox jumps over the lazy dog\")" "[\"quick\"]"  
    case "(re-matches #\"(f(oo bar))\" \"foo bar\")"  "[\"foo bar\" \"foo bar\" \"oo bar\"]"
    case "(re-seq #\"\w*(\w)\" \"one-two/three\")" "([\"one\" \"e\"] [\"two\" \"o\"] [\"three\" \"e\"])"
    
    case "(named-params :bar \"override-bar\")" "{:output-bar \"override-bar\" :output-foo \"foo-default\"}"

    // the following test takes about 5 seconds!!!! wtf??  No idea why ...
    case "(for [x (range 3), y (range 3), z (range 3) :when (or (< x y z) (> x y z))] [x y z])" "([0 1 2] [2 1 0])"

    // the following will only succeed if tailcalls are optimized 
    nocrash "(rfact 10000)"    // test recur - and bigintegers i guess
    nocrash "(let* [lrfact (fn [x] (if (<= x 1) 1 (* x  (recur (- x 1)) )))] (lrfact 10000))" 

    let secs = (DateTime.Now - strt).TotalSeconds
    printfn "Test suite completed in %f seconds" secs
    ()
