﻿module Builtins

open Inc
open IncTypes
open Utils
open ImmutableCollections

let init() =
    let _builtins =
        [
        ".", Special(InterOp)
        "*", Function(Multiply)
        "/", Function(Divide)
        "%", Function(Modulus)
        "+", Function(Add)
        "-", Function(Subtract)
        "=", Function(Equal)
        "==", Function(Equal)   // needs review 
        "!=", Function(NotEqual)
        ">", Function(Greater)
        "<", Function(Less)
        "add-watch", Special(AddWatch)
        "alter", Special(Alter)
        "agent", Special(DefAgent)        
        "apply", Special(ApplyTo)
        "assoc*", Function(Assoc)
        "atom", Function(DefAtom)        
        "binding", Special(Binding)
        "cat", Function(Cat)
        "char?", Function(IsChar)
        "cond", Special(Cond)
        "conj", Function(Conjoin)
        "cons", Function(Cons)
        "contains?", Function(IncContains)
        "count", Function(Count)
        "debug", Special(Debug)
        "def", Special(Define)
        "deref", Function(Deref)
        "delay", Special(MakeDelay)
        "display", Function(Display)
        "dissoc1", Function(Dissoc)
        "do", Special(Begin)
        "dosync", Special(DoSync)
        "eval", Special(Eval)
        "first", Function(IncFirst)
        "find", Function(Find)
        "find-ns", Function(FindNS)
        "fn*", Special(FnStar)
        "force", Function(Force)
        "gensym", Function(GenSym)
        "get", Function(Get)
        "if", Special(If)
        "int", Function(CoerceToInt)
        "in-ns", Function(ChangeNS)
        "key", Function(Key)
        "keys", Function(Keys)
        "keyword", Function(MakeKeyword)
        "keyword?", Function(IsKeyword)
        "lambda", Special(Lambda)
        "lazy-seq", Special(LazySeq)
        "let*", Special(LetStar)
        "list", Special(MakeList)
        "load", Function(Load)
        "loop*", Special(Loop)
        "make-map", Function(MakeMap)
        "map?", Function(IsMap)
        "meta", Function(Meta)
        "monitor-enter", Function(MonitorEnter)
        "monitor-exit", Function(MonitorExit)
        "new", Special(New)
        "next", Function(IncNext)
        "nil?", Function(IsNil)
        "ns-unmap", Function(UnDef)
        "nth", Function(Nth)
        "partial", Special(Partial)
        "peek", Function(Peek)
        "pop", Function(Pop)
        "print", Function(Print)
        "quote", Special(Quote)
        "re-pattern", Function(RePattern)
        "re-match", Function(ReMatcher)
        "recur", Special(Recur)
        "ref", Function(DefRef)
        "rest", Function(IncRest)
        "reverse", Function(Reverse)
        "send", Special(Send)
        "send-off", Special(Send)
        "seq",  Function(IncSeq)
        "seq?", Function(IsSeq)
        "seqable?", Function(IsSeqable)
        "set-macro", Special(SetMacro)
        "set-validator", Function(SetValidator)
        "set!", Special(Assign)
        "str", Function(Str)
        "string?", Function(IsString)
        "symbol", Function(MakeSymbol)
        "symbol?", Function(IsSymbol)
        "syntax-quote", Special(SyntaxQuote)
        "throw", Special(Throw)
        "try", Special(Try)
        "unquote", Special(UnQuote)
        "val", Function(Val)
        "vals", Function(Vals)
        "var", Special(GetVar)
        "vec", Function(MakeVector)
        "vector?", Function(IsVector)
        "with-meta", Function(WithMeta)

        ]

    for nm,e in _builtins do
        let m = IncMap.ofPairs(
                    [ (kwd("name"), sym(nm)); 
                    (kwd("ns"), NS(Globals.CoreNS) |> e2v); 
                    (kwd("file"), str("__builtin__")); 
                    (kwd("doc"), str(""))])
        let v = IncValue.OfExpr(e,m)
        Globals.CoreNS.Intern(nm,v,Some(m)) |> ignore


