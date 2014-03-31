(*
 * Copyright (c) 2014, Gary Stephenson
 * portions copyright 2010 Ashley Nathan Feniello
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

module Inc

open System
open System.Text
open System.Text.RegularExpressions
open System.Xml
open System.Numerics
open System.Threading
open System.IO
open System.Collections.Generic
open System.Collections.Concurrent
open System.Linq
open ImmutableCollections
open System.Reflection
open Utils
open Numeric
open Stm
open agent
open tokens
open IncTypes

let Globals = new GlobalEnvironment()

let parse fname source =
    let e2vp posn e =
        let pos,line,col = posn
        let m = new IncMap([kwd("file"),str(fname)
                            kwd("pos"),incInt pos
                            kwd("line"),incInt line
                            kwd("col"),incInt col
                           ])
        IncValue.OfExpr(e,m)

    let map posn t =
        match t.tok with
        | Token.Number(s) -> Number(Numeric.Parse(s)) |> e2vp posn
        | Token.String(s) -> IncExpr.String(s) |> e2vp posn
        | Token.Symbol(s) -> 
            match s with
            | "true" -> incTrue
            | "false" -> incFalse
            | "nil" -> incNil
            | _ -> IncExpr.Symbol(String.Intern(s)) |> e2vp posn
        | Token.Keyword(s) -> IncExpr.Keyword(String.Intern(s)) |> e2vp posn
        | Token.Char(c) -> IncExpr.Character((int c)) |> e2vp posn
        | _ -> failwith "Syntax error."

    let tagEl(v : IncValue,tag) =
        match tag with 
        | Some(e) ->
            match e with
            | String("__implicit_function__") ->
                match v.value with
                | ExprList(l) ->
                    let syms = Dictionary<int,IncValue>()
                    let maxi = ref 0
                    let getsym i =
                       if i > !maxi then maxi := i
                       if not (syms.ContainsKey(i)) then
                           syms.[i] <- Globals.GenSym("p"+i.ToString())
                       syms.[i]
                    let rec _scan vs acc =
                        match vs with
                        | h :: t ->
                            match h.value with 
                            | Symbol(s) when s.StartsWith("%") ->
                                if s = "%" then _scan t (getsym(1) :: acc)
                                else 
                                    let i = System.Int32.Parse(s.Substring(1))
                                    _scan t (getsym(i) :: acc)
                            | ExprList(l) ->
                                let vs = _scan l []
                                _scan t ( (lst vs) :: acc)
                            | _ -> _scan t (h :: acc)
                        | [] -> List.rev acc
                    let tl = _scan l []
                    let prms = [for i in 1 .. !maxi -> getsym(i)  ]
                    let rslt = lst([sym("fn*"); vect prms; lst(tl)])   
                    rslt.SetMacro()
                    rslt
                | _ -> failwith "Invalid implicit function"
            | String("inst") ->
                match v.value with
                | String(cdt) ->
                    let x = IncExpr.DateTime(XmlConvert.ToDateTime(cdt,XmlDateTimeSerializationMode.Utc))
                    IncValue.OfExprM(x,v.metaMap)
                | _ -> failwith "Syntax error"
            | ExprDict(m) ->
                for k,mv in m do
                    v.SetMetaValue(k,mv)
                v
            | _ -> failwith "Syntax error"
        | None -> v 

    let rec addprs acc prs =
        match prs with
        | k :: v :: et -> addprs ((k,v) :: acc) et
        | [] -> List.rev acc
        | _ -> failwith "Malformed pairs for mapping."
          
    let applyQuoting fs =   // el bizarro - needs review :)
        let rec _app acc forms =
            let _app2 s t =
                match _app [] t with
                | h :: t -> 
                    let rslt =  (List.rev acc) @ (lst([s; h]) :: t) 
                    rslt
                | [] -> failwith "nothing to quote"

            match forms with
            | {value=Symbol("quote_")} :: t -> _app2 (sym "quote") t 
            | {value=Symbol("syntax-quote_")} :: t ->  _app2 (sym "syntax-quote") t 
            | {value=Symbol("unquote_")} :: t ->  _app2 (sym "unquote") t 
            | {value=Symbol("splice-unquote_")} :: t ->  _app2 (sym "splice-unquote") t 
            | h :: t -> _app (h :: acc) t
            | [] -> List.rev acc
        _app [] fs
 
    let rec xlist posn t acc tag =
        let e, t' = parse' [] None t
        parse' (tagEl(ExprList(applyQuoting(e)) |> e2vp posn ,tag) :: acc) None t'
    and xvect posn t acc tag =
        let e, t' = parse' [] None t
        parse' (tagEl(ExprVector(Vec.create(applyQuoting(e))) |> e2vp posn,tag) :: acc) None t'
    and xdict posn t acc tag =
        let e, t' = parse' [] None t
        let prs = addprs [] (applyQuoting(e))
        parse' (tagEl(ExprDict(prs) |> e2vp posn,tag) :: acc) None t'
    and xset posn t acc tag =
        let e, t' = parse' [] None t
        parse' (tagEl(ExprSet(applyQuoting(e)) |> e2vp posn,tag) :: acc) None t'
    and parse' acc tag (toks : TokenPos list) = 
        let posn = match toks with
                   | h :: t -> (h.startpos,h.startline,h.startcol) 
                   | [] -> (-1,-1,-1)
        match toks with
        | {tok=Open} :: t -> xlist posn t acc tag
        | {tok=Close} :: t -> (List.rev acc), t
        | {tok=OpenVector} :: t -> xvect posn t acc tag
        | {tok=CloseVector} :: t -> (List.rev acc), t
        | {tok=OpenDict} :: t -> xdict posn t acc tag
        | {tok=CloseDict} :: t -> (List.rev acc), t
        | {tok=OpenSet} :: t -> xset posn t acc tag
        | {tok=Quote} :: t ->  parse' (sym("quote_") :: acc) tag t
        | {tok=Unquote} :: t ->  parse' (sym("unquote_") :: acc) tag t
        | {tok=SyntaxQuote} :: t ->  parse' (sym("syntax-quote_") :: acc) tag t
        | {tok=SpliceUnquote} :: t ->  parse' (sym("splice-unquote_") :: acc) tag t
        | {tok=TagTok("^")} :: {tok=OpenDict} :: t -> // metadata map
            let m,t' = parse' [] None t
            let prs = addprs [] (applyQuoting(m))
            let meta = Some(ExprDict(prs))
            parse' acc meta t'
        | {tok=TagTok("^")} :: {tok=Token.Keyword(s)} :: t -> // metadata tag string
            let meta = Some(ExprDict([Keyword("tag") |> e2v,String(s) |> e2v]))
            parse' acc meta t
        | {tok=TagTok("__ignore__")} :: h :: t -> 
            parse' acc tag t
        | {tok=TagTok(s)} :: t -> parse' acc (Some(String(s))) t
        | h :: t -> parse' (tagEl((map posn h),tag) :: acc) None t
        | [] -> applyQuoting(List.rev acc), []
    let toks = (tokenize source)
    let result, _ = parse' [] None toks
    result

let malformed n (v : IncValue) = sprintf "Malformed '%s': %s" n (v.ToString()) |> failwith

let Str cont args = 
    let rec _str acc l =
        match l with
        | [] -> String.Concat( List.rev acc) 
        | h :: t ->
            match h.value with 
            | Character(i) -> _str ((char i).ToString() :: acc) t  
            | String(s) -> _str (s :: acc) t  
            | _ -> _str ( (h.ToPrint()) :: acc) t
    String(_str [] args) |> e2v |> cont


let math ident unary op name (cont : Continuation) args =
    let ident = Int(ident)
    let unary = Int(unary)
    let ns = [for x in args do
                    match x.value with 
                    | Number(n) -> yield n
                    | EvaldSeq(s) -> yield! [for t in s do 
                                                match t.value with
                                                | Number(n) -> yield n
                                                | _ -> malformed name (vect args) 
                                            ]
                    | _ -> malformed name (vect args) ]
    match ns with
    | [h] -> Number(unary * h)
    | h :: t ->
        Number(List.fold op h t) 
    | [] -> Number(ident)
    |> e2v |> cont

let Add cont args = math 0 1 (+) "addition"  cont args
let Subtract cont args = math 0 -1 (-) "subtraction" cont args 
let Multiply cont args = math 1 1 (*) "multiplication" cont args
let Divide cont args = math 1 1 (/) "division" cont args 
let Modulus cont args = math 1 1 (%) "modulus" cont args 


let rec Compare pred name cont vs = 
    match vs with 
    | [{value=Number(a)}; {value=Number(b)}] -> (if pred a b then incTrue else incFalse) |> cont
    | a :: b :: t -> 
        if (Compare pred name id [a ; b]).value.IsTrue then Compare pred name cont (b :: t)
        else incFalse |> cont
    | _ -> malformed name (vect vs) 

let Greater cont = Compare (>) "greater" cont
let Less cont = Compare (<) "less" cont

let Equal c vs = 
    let es = [for v in vs -> v.value]
    let cont e = e |> e2v |> c 
    
    match es with 
    | [a; b] -> 
       if (a.IsSeqable() && b.IsSeqable()) then
           let sa = a.ToSeq()
           let sb = b.ToSeq()
           let cmp = Seq.compareWith (fun x y -> (compare x y)) sa sb
           Boolean( cmp = 0 )
       else Boolean( a = b ) 
       |> cont
    | m -> malformed "Equal" (vect vs)

let NotEqual c vs = 
    let es = [for v in vs -> v.value]
    let cont e = e |> e2v |> c 
    match es with 
    | [a; b] -> Boolean( a <> b ) |> cont
    | _ -> malformed "Equal" (vect vs)

let extend env (bindings : (IncValue * IncValue) seq) = 
    let dic = Frame.Empty()
    for k,v in bindings do 
        dic.SetItem(k, v)
    dic :: env

let ChangeNS cont args =
    match args with 
    | [{value=Symbol(s)}] -> 
        match Globals.FindNS(s) with
        | Some(ns) -> Globals.DefaultNS <- ns
        | None ->  let ns = Namespace(s)
                   Globals.LoadNS(ns)
                   Globals.DefaultNS <- ns
        Dummy("in-ns") |> e2v |> cont
    | _ -> malformed "in-ns" (vect args)

let Find cont args =
    match args with
    | [coll; k] -> 
        match coll.value with
        | ExprDict(l) -> 
            match l |> List.tryFind (fun (k2,v) -> k = k2 ) with
            | Some(_,v) -> MapEntry(KeyValuePair(k,v)) |> e2v 
            | None -> incNil 
        | EvaldDict(m) ->
            if m.ContainsKey(k) then MapEntry(KeyValuePair(k,m.[k])) |> e2v 
            else incNil 
        | _ -> malformed "find" (vect args)
        |> cont
    | _ -> malformed "find" (vect args)

let FindNS cont args =
    match args with
    | [{value=Symbol(s)}] -> 
        match Globals.FindNS(s) with
        | Some(ns) -> NS(ns) |> e2v |> cont
        | None ->  incNil |> cont
    | _ -> malformed "find-ns" (vect args)

let rec UnDef cont  = function
    | [{value=NS(ns)}; {value=Symbol(s)}] -> 
        ns.UnIntern(s)
        Dummy("ns-unmap "+(ns.Name)+"/"+s) |> e2v |> cont
    | [{value=Symbol(ns)}; {value=Symbol(s)}] -> 
        match Globals.FindNS(ns) with
        | Some(ns) -> ns.UnIntern(s)
        | None ->  failwith ("Unable to find namespace : "+ns)
        Dummy("ns-unmap "+ns+"/"+s) |> e2v |> cont
    | vs -> malformed "in-ns" (vect vs)

and print (v : IncValue) : string = 
    match v.value with
    | Dummy(s) -> s
    | _ -> v.ToPrint()

and zipargs env asmacro parameters args =
    let rec _zip ps rs rslt = 
        match ps, rs with
        | (p :: pt, r :: rt ) ->  
            match p.value with
            | Symbol(s) ->
                if s = "&" then
                    match pt with
                    | [p] -> 
                        let mutable rest = r :: rt
                        if not asmacro then rest <- rest |> List.map (fun v -> eval id env v)  
                        let v = match rest with
                                | [] | [{value=Nil}] -> incNil 
                                | _ -> lst(rest) 
                        (p, v) :: rslt
                    | _ -> failwith "Invalid parameter list"
                else _zip pt rt ( (p,(if asmacro then r else (eval id env r)) ) :: rslt )
            | _ -> failwith "Invalid parameter list"
        | [], [] -> rslt
        | [{value=Symbol("&")}; {value=Symbol(s)} as p], [] -> (p, incNil) :: rslt
        | _, _ -> failwith "Invalid parameter list"
    let l = List.rev (_zip parameters args [])
    l

and If cont env form args = 
    match args with
    | condition :: vs -> 
        let v = eval id  env condition
        match vs with
        | [t; f] -> if v.IsTrue then eval cont env t
                                else eval cont env f
        | [t] -> if v.IsTrue then eval cont env t
                             else eval cont env incNil
        | _ ->  malformed "if" (vect args)
    | _ -> malformed "if" (vect args)

and LetStar cont env form args =
    match args with
    | {value=ExprVector(bindings)} :: body ->
        let rec foldbind env' args' = 
            match args' with
            | {value=Symbol(s)} as sm :: e :: t -> 
                if s.Contains("/") then failwith ("can't let qualified name : " + s)
                let x = eval id env' e
                let env'' = extend env' [sm, x]
                foldbind env'' t
            | [] ->
                match body with
                | [v] -> eval cont env' v
                | _ -> Begin cont env' form body
            | _ -> malformed "let*" (vect args')
        foldbind env (Seq.toList (bindings.toSeq()))
    | _ -> malformed "let" (vect args)

and Loop cont env form vs = 
    match vs with
    | [{value=ExprVector(bindings)}; body] ->
        let rec syms prms acc = 
            match prms with
            | k :: v :: t -> syms t (k :: acc)
            | [] -> vect (List.rev acc)
            | _ ->  malformed "loop" (vect vs)
        let ps = syms (bindings.toList()) []
        let f = Frame.RecurFrame(ps, body)
        LetStar cont (f :: env) form vs
    | {value=ExprVector(bindings)} as v :: body ->
       let body = lst(sym("do") :: body)
       Loop cont env form [v ; body]
    | _ -> malformed "loop" (vect vs)

and Lambda cont env form args =
    match args with
    | [nm; l] ->
        let nm = eval id env nm
        let s = eval id env l
        let vs = Seq.toList (s.ToSeq())
        FnStar cont env form (nm :: vs)
    | [l] ->
        let s = eval id env l
        let vs = Seq.toList (s.ToSeq())
        FnStar cont env form vs
    | _ -> malformed "lambda" (vect args)

and FnStar cont (env : Environment) form args =
    let mutable nm = ""
    let mutable doc = ""
    let mutable meta = IncMap.Empty
    let mutable rem = []
    let mutable forms = []


    let vs =
        match args with
        | {value=Symbol(s)} as sym :: t -> 
            nm <- s
            match sym.metaMap with
            | Some(m) -> meta <- m
            | None -> ()
            t
        | _ -> args

    match vs with
    | {value=String(docstr)} :: {value=ExprDict(attribs)} :: body ->
       doc <- docstr
       for k,v in attribs do meta <- meta.Add(k, v)
       rem <- body
    | {value=ExprDict(attribs)} :: body ->
       for k,v in attribs do meta <- meta.Add(k, v)
       rem <- body
    | {value=String(docstr)} :: body ->
       doc <- docstr
       rem <- body
    |  body ->
       rem <- body

    let nm_ = nm

    let dic = new Dictionary<IncValue,IncValue>()
    let rf = new Frame(dic,None) 
    let env =
        if nm = "" then env
        else
            dic.[sym(nm)] <- incUnbound
            rf :: env 

    let rec checkRecur canRecur (frms : IncValue list) =
        match frms with
        | h :: t ->
            match h.value with
            | ExprList(l) ->
                let _canRecur = match t with
                                | [] -> canRecur
                                | _ -> false
                match l with
                | [{value=Symbol("if")}; cond; t; f] ->
                    checkRecur canRecur [t] 
                    checkRecur canRecur [f] 
                | {value=Symbol("cond")} :: t ->
                    let rec chk vs =
                        match vs with
                        | tst :: xpr :: t -> 
                            checkRecur canRecur [xpr] 
                            chk t
                        | _ -> ()
                    chk t
                | {value=Symbol("recur")} :: _ ->
                    if not _canRecur then failwith "recur not in tail position"
                | {value=Symbol("loop")} :: t ->
                    checkRecur true t 
                | _ ->
                    checkRecur _canRecur l 
            | _ -> ()
            checkRecur canRecur t 
        | [] -> ()

    let vs = rem
    rem <- [for v in vs ->
                   match v.value with
                   | EvaldExpr(ev) -> ev.Value
                   | EvaldSeq(s) -> lst(Seq.toList s)
                   | _ -> v]

    match rem with
    | [{value=ExprVector(prms)}; body] ->
       forms <- [prms,body]
       checkRecur true [body] 
    | [{value=ExprVector(prms)}] ->
       forms <- [prms,incNil]
    | {value=ExprVector(prms)} :: body ->
       let body = lst(sym("do") :: body)
       forms <- [prms,body]
       checkRecur true [body] 
    | l ->
        for v in l do
            match v.value with
            | ExprList(t) ->
                match t with
                | [{value=ExprVector(prms)}; body] -> 
                    // check arity doesn't already exist
                    checkRecur true [body] 
                    forms <- (prms,body) :: forms
                | {value=ExprVector(prms)} :: body ->
                    let body = lst(sym("do") :: body)
                    forms <- (prms,body) :: forms
                    checkRecur true [body] 
                | _ -> malformed "fn*" (vect vs) 
            | Nil -> () 
            | _ -> malformed "fn*" (vect vs) 

    meta <- meta.Add(kwd("name"), str(nm)) 
    meta <- meta.Add(kwd("ns"), NS(Globals.DefaultNS) |> e2v)
    meta <- meta.Add(kwd("macro"), incFalse);
    if doc <> "" then meta <- meta.Add(kwd("doc"), str(doc))

    let frms =  forms |> List.rev 

    let closure cont' env' macro (args' : IncValue list) =
        let ismacro,form = match macro with
                           | None -> false,incNil
                           | Some(f) -> true,f 
        let matchlen ps a =
            match ps |> List.tryFindIndex (fun p -> match p.value with Symbol("&") -> true | _ -> false ) with
            | Some(i) -> i <= a
            | None -> ps.Length = a

        let prms,body = frms |> List.find (fun (ps,_) -> matchlen (ps.toList()) args'.Length )
        let binds = zipargs env' ismacro (prms.toList()) args' 

        if ismacro then
            let env'' = env' @ env 
            let envrf = extend env'' [sym("&form"),form]
            let env''' = binds |> extend envrf

            eval id env''' body
        else
            let dic = new Dictionary<IncValue,IncValue>()
            for k,v in binds do dic.[k] <- v
            let rf = new Frame(dic,Some(vect(prms.toSeq()),body)) 
            eval cont' (rf :: env) body

    let def = IncValue.OfExprM(Special(closure),Some(meta)) 
    if nm <> "" then dic.[sym(nm)] <- def
    def |> cont

and Cat cont args = 
    match args with 
    | [{value=ExprList(a)}; {value=ExprList(b)}] -> ExprList(a @ b) |> e2v |> cont 
    | _ -> malformed "cat" (vect args)

and IncSeq cont (args : IncValue list) =
    match args with
    | [v] -> 
       let s = v.ToSeq()
       if Seq.isEmpty s then incNil else evseq s 
       |> cont
    | _ -> malformed "seq" (vect args)

and IncFirst cont args =
    match args with
    | [x] ->
        let v = IncSeq id [x]
        match v.value with
        | EvaldSeq(s) -> let v = Seq.head s 
                         v |> cont
        | IncCons(cns) -> cns.head |> cont
        | Nil -> incNil |> cont
        | _ -> failwith "not a seq"
    | _ -> malformed "first" (vect args)

and IncRest cont args =
    match args with
    | [x] ->
        let v = (IncSeq id [x]).value
        match v with
        | EvaldSeq(s) -> 
            let s' = Seq.skip 1 s
            evseq s' |> cont
        | IncCons(cns) -> 
            match cns.tail.value with 
            | Nil | Unbound ->  incEmptySeq |> cont
            | _ -> cns.tail |> cont
        | Nil ->  incEmptySeq |> cont
        | _ -> failwith "not a seq"
    | _ -> malformed "rest" (vect args)

and IncNext cont args =
    match args with
    | [x] ->
        let v = IncSeq id [x]
        match v.value with
        | EvaldSeq(s) -> 
            let s' =  Seq.skip 1 s
            if Seq.isEmpty s' then incNil 
            else evseq s' 
            |> cont
        | IncCons(cns) -> cns.tail |> cont
        | Nil ->  incNil |> cont
        | _ -> failwith "not a seq"
    | _ -> malformed "next" (vect args)

and Nth (cont : Continuation) args =
    match args with
    | {value=EvaldExpr(x)} :: t -> Nth cont (x.Value :: t)
    | [x; {value=Number(_)} as n] -> Nth cont [x; n; incUnbound]
    | [x; {value=Number(n)}; dflt] ->
        let deflt() = 
            match dflt.value with
            | Unbound -> failwith "input sequence has insufficient elements"
            | _ -> dflt |> cont
        let n = n.ToInt()
        let mutable s = x
        for i = 0 to n - 1 do
           s <- IncNext id [s] 
        IncFirst cont [s] 
    | _ -> malformed "nth" (vect args)

and Reverse cont (args : IncValue list) =
    match args with
    | [x] ->
        let s = x.ToSeq()
        evseq (s.Reverse()) |> cont
    | _ -> malformed "reverse" (vect args)

and LazySeq cont env form args =
    match args with
    | [{value=EvaldExpr(x)}] -> LazySeq cont env form [x.Value]
    | [x] ->
        let lz = {fn = None; s = incNil}
        let f = fun _ -> 
            lz.fn <- None
            let t = eval id env x
            lz.s <- t
        lz.fn <- Some(f)
        IncLazy(lz) |> e2v |> cont            
    | h :: t -> 
        let v = lst(sym("do") :: h :: t)
        v.metaMap <- h.metaMap
        LazySeq cont env form [v]
    | _ -> malformed "lazy-seq" (vect args)

and Cons (cont : Continuation) (args : IncValue list) =
    match args with 
    | [h; {value=EvaldExpr(x)}] -> Cons cont [h; x.Value] 
    | [{value=Nil}; t] -> failwith "fuck me"
    | [{value=Symbol(s)} as symb; {value=ExprList(l)}] -> lst(symb :: l) |> cont
    | [{value=Symbol(s)} as symb; {value=EvaldSeq(sq)}] -> lst(symb :: (Seq.toList sq)) |> cont
    | [h; {value=IncLazy(_)} as t] ->
        IncCons({head = h; tail = t}) |> e2v |> cont
    | [h; t] -> 
        evseq (seq {yield h; yield! t.ToSeq()}) |> cont
    | _ -> malformed "cons" (vect args)

and IncContains cont args =
    match args with 
    | [{value=EvaldExpr(x)}; t] -> IncContains cont [x.Value; t] 
    | [h; {value=EvaldExpr(x)}] -> IncContains cont [h; x.Value] 
    | [h; t] -> 
        let rslt() =
            match h.value with
            | ExprVector(v) ->
                match t.value with
                | Number(n) -> let i = n.ToInt()
                               i >= 0 && i < v.Length
                | _ -> malformed "contains?" (vect args)
            | ExprSet(l) -> l.Contains(t)
            | EvaldSet(s) -> s.Contains(t)
            | EvaldSeq(s) -> s.Contains(t)
            | ExprDict(l) -> l |> List.exists (fun (k,v) -> k = t)
            | EvaldDict(m) -> m.ContainsKey(t)
            | ExprList(l) -> l |> List.exists (fun x -> x = t)
            | IncCons(c) ->
                if c.head = t then true
                else
                    let s = c.tail.ToSeq() 
                    t.In(s)
            | _ -> false  //malformed "contains" (vect args)
        (if rslt() then incTrue else incFalse) |> cont
    | _ -> malformed "contains?" (vect args)

and Count cont args =
    match args with
    | [{value=EvaldExpr(x)}] -> Count cont [x.Value]
    | [x] ->
        let s = x.value.Unlazy() 
        let l = List.length s 
        Number(Int(l)) |> e2v |> cont
    | _ -> malformed "count" (vect args)

and Assoc cont args =
    match args with
    | [tgt; key; value] ->
        match tgt.value with
        | EvaldExpr(v) -> Assoc cont [tgt; key; v.Value]
        | ExprDict(l) ->
            let tl = [for tk,v in l do if tk <> key then yield tk,v]
            ExprDict((key,value) :: tl) |> e2v |> cont
        | EvaldDict(m) ->
            EvaldDict(m.Add(key,value)) |> e2v |> cont
        | ExprVector(v) ->
            match key.value with 
            | Number(n) ->
                ExprVector(v.assocN(n.ToInt(),value)) |> e2v |> cont
            | _ -> failwith "Invalid index for vector"
        | _ -> malformed "assoc" (vect args)
    | _ -> malformed "assoc" (vect args)

and Conjoin cont args =
    match args with
    | h :: t ->
        let h = match h.value with
                | EvaldExpr(h') -> h'.Value
                | _ -> h
        match h.value with
        | ExprVector(v) -> 
            let mutable vt = v
            for x in t do vt <- vt.cons(x)
            vec(vt) |> cont
        | ExprList(tl) -> 
            let mutable vt = tl
            for x in t do vt <- x :: vt
            lst(vt) |> cont
        | ExprDict(prs) -> 
            let rec app acc t =
                match t with
                | {value=ExprVector(v)} :: t' ->
                    if v.Length <> 2 then failwith "invalid args to conj for map"
                    app ( (v.[0],v.[1]) :: acc) t'
                | [] -> ExprDict(acc) |> e2v |> cont
                | _ -> failwith "invalid args to conj for map"
            app prs t
        | EvaldDict(m) ->  
            let rec app (acc : IncMap) t =
                match t with
                | {value=EvaldExpr(v)} :: t' -> app acc (v.Value :: t')
                | {value=ExprVector(v)} :: t' ->
                    if v.Length <> 2 then failwith "invalid args to conj for map"
                    app (acc.Add(v.[0],v.[1])) t'
                | {value=EvaldDict(m)} :: t' ->
                    let mutable acc = acc
                    for kvp in m do acc <- acc.Add(kvp.Key,kvp.Value)
                    app acc t'
                | {value=ExprDict(prs)} :: t' ->
                    let mutable acc = acc
                    for k,v in prs do acc <- acc.Add(k,v)
                    app acc t'
                | [] -> EvaldDict(acc) |> e2v |> cont
                | _ -> failwith "invalid args to conj for map"
            app m t
        | EvaldSet(s) -> 
            let mutable s = s
            for x in t do s <- Set.add x s
            EvaldSet(s) |> e2v |> cont
        | EvaldSeq(s) -> evseq (seq {yield! s; yield! t}) |> cont
        | _ -> failwith "not a collection"
    | _ -> malformed "conj" (vect args)

and SyntaxQuote (cont : Continuation) env form args =
    let symsgend = Dictionary<string,IncValue>()

    let rec unquote v : IncValue = 
        let rec mapunquote acc  vs : list<IncValue> = 
            match vs with
            | h :: t ->
                match h.value with
                | Symbol(s) ->
                    let v = if s.EndsWith("#") then
                                if not(symsgend.ContainsKey(s)) then
                                    symsgend.[s] <- Globals.GenSymAuto(s.Substring(0,s.Length - 1)) 
                                symsgend.[s]
                            else 
                                sym(Globals.NSQualify(s))
                                
                    mapunquote (v :: acc) t
                | ExprList([{value=Symbol("splice-unquote")}; e]) -> 
                    let x = eval id env e
                    let rec splice acc' = function
                    | h' :: t' ->
                        splice (h' :: acc') t'
                    | [] -> mapunquote acc' t
                    match x with
                    | {value=EvaldSeq(s)} ->
                        splice acc (Seq.toList s)
                    | {value=ExprVector(uqs)} ->
                        splice acc (uqs.toList())
                    | {value=ExprList(uqs)} ->
                        splice acc uqs
                    | {value=Nil} ->
                        splice acc []
                    | _ ->  malformed "splice-unquote" e
                | _ -> 
                    let x = unquote h
                    mapunquote (x ::acc) t
            | [] -> List.rev acc

        match v.value with
        | ExprList([{value=Symbol("unquote")}; e]) -> eval id env e
        | ExprList(lst) ->
            ExprList(mapunquote [] lst) |> e2v 
        | ExprVector(a) ->
            let lst = a.toList()
            vect(mapunquote [] lst)  
        | ExprDict(m)  ->
            let m' = [for k,v in m -> (unquote k),(unquote v)]
            ExprDict(m') |> e2v
        | ExprSet(s)  ->
            ExprSet(mapunquote [] s) |> e2v
        | _ -> v
    match args with
    | [e] -> unquote e |> cont
    | _ -> malformed "syntax-quote" (vect args)

and Quote cont env form args = 
    match args with
    | [e] -> cont e 
    | _ -> malformed "quote" (vect args)

and UnQuote cont env form args = 
    match args with
    | [e] -> eval cont env e
    | _ -> malformed "unquote" (vect args)

and Eval cont env form args = 
    match args with 
    | [args] -> args |> eval (eval cont env) env 
    | _ -> malformed "eval" (vect args)

and Assign cont env form args = 
    match args with
    | [{value=Symbol(s)}; v] -> 
        let x = eval id env v
        Globals.setVar(s,x)
        x |> cont
    | _ -> malformed "set!" (vect args)

and SetValidator cont args = 
    match args with
    | [h; f] ->
        let tgt = 
            match h.value with
            | Symbol(s) -> match Globals.GetVar(s) with Some(v) -> v | _ -> failwith ("unable to locate : " + s)
            | Ref(_) 
            | Atom(_) 
            | Agent(_) 
            | Var(_) -> h
            | _ -> failwith "invalid target for validator"
        tgt.validator <- Some(f)
        Dummy("validator set") |> e2v |> cont
    | _ -> malformed "set-validator!" (vect args)

and SetMacro cont env form args = 
    match args with
    | [{value=Symbol(s)} as sm] ->
        sm.SetMacro()
        match Globals.GetVar(s) with
        | Some(v) -> 
            v.SetMacro()
            match v.value with
            | Var(r) -> let _,v = !r in v.SetMacro()
            | _ -> failwith "cannot happen"
        | _ -> failwith ("Unable to resolve symbol : " + s)
        Dummy(":macro set") |> e2v |> cont
    | _ -> malformed "set-macro" (vect args)

and Begin cont env form args =
    match args with
    | [v] -> eval cont env v
    | _ ->
        let mutable last = incNil
        for v in args do last <- eval id env v
        last |> cont
    
and MakeDelay cont env form args =
    let body = match args with
                | [v] -> v
                | _ -> lst(sym("do") :: args)
    Delay({body = body; env = env; evald = None}) |> e2v |> cont
   
and Force cont args =
    match args with
    | [{value=Delay(d)}] ->
        match d.evald with
        | Some(v) -> v |> cont
        | None ->
            let v = eval id d.env d.body
            d.evald <- Some(v)
            v |> cont
    | _ -> malformed "force (not a delay)" (vect args)
    
and GenSym cont args =
    match args with
    | [{value=String(prfx)}] -> Globals.GenSym(prfx) |> cont
    | [] -> Globals.GenSym() |> cont
    | _ -> malformed "gensym" (vect args)
    
and Get cont args =
    match args with
    | [coll; k] -> Get cont [coll; k; incNil]
    | [coll; k; nf] ->
       match coll.value with
       | EvaldExpr(x) -> Get cont [x.Value; k; nf]
       | ExprDict(_) 
       | EvaldDict(_) ->
           match (Find id [coll; k]).value with
           | MapEntry(kvp) -> kvp.Value |> cont
           | Nil -> nf |> cont
           | _ -> failwith "no way jose"
       | Nil -> nf |> cont
       | _ -> Nth cont args
    | _ -> malformed "get" (vect args)
    
and GetVar cont (env : Environment) form args = 
    match args with
    | [{value=Symbol(s)} as v] -> 
        match Globals.GetVar s with
        | Some(e) -> 
            e.metaMap <- v.metaMap
            e |> cont
        | None -> failwith ("Var not found : " + s )
    | _ -> malformed "var" (vect args)

and Deref cont args =
    match args with
    | [{value=Ref(r)}] ->
        readTVar r |> cont
    | [{value=Atom(r)}] -> !r |> cont
    | [{value=Delay(d)}] -> Force cont args
    | _ -> malformed "deref" (vect args)

and DefRef cont args =
    match args with
    | [v] -> let r = newTVar v
             IncValue.OfExpr(Ref(r)) |> cont
    | _ -> malformed "ref" (vect args)

and DefAtom cont args =
    match args with
    | [v] -> let r = ref v
             IncValue.OfExpr(Atom(r)) |> cont
    | _ -> malformed "atom" (vect args)

and DoSync cont env form vs =
    let rec _do l rslt =
        match l with
        | h :: t ->
            let r = eval id env h
            _do t r
        | [] -> rslt
    let rslt =
        if inTrans() then _do vs incNil
        else
            atomically <| 
                stm {
                    let r = _do vs incNil
                    return r
                } 
    rslt |> cont

and Alter cont env form args =
    if not(inTrans()) then  failwith "No transaction running"
    let v,r,t = match args with
                | {value=Symbol(s)} as sm :: t ->  
                    let v = Lookup env sm
                    match v with
                    | {value=Ref(r)} -> v,r,t
                    | _  -> failwith ("unable to locate : " + s)       
                | {value=Ref(r)} :: t -> args.Head,r,t
                | _ -> malformed "alter" (vect args)

    let oldv = TLog.Current.ReadTVar(r) 
    let f' = match t with
                | f :: t' -> ExprList(f :: oldv :: t') |> e2v
                | _ -> malformed "alter" (vect args)
    let newv = eval id env f'
    TLog.Current.WriteTVar(r, newv)
    fireWatchers env v oldv newv
    newv |> cont

and DefAgent cont env form (args : IncValue list) =
    match args with
    | h :: t ->
        let init = eval id env h
        let agent = new Agent<IncValue>(init)
        let v = IncValue.OfExpr(Agent(agent))
        let rec parseOptions l =
            match l with
            | {value=Keyword("meta")} :: m :: t ->
                let mutable meta = IncMap.Empty
                match m with 
                | {value=ExprDict(m)} ->
                    for k,v in m do meta <- meta.Add(k,v)
                | {value=EvaldDict(m)} ->
                    for kvp in m do meta <- meta.Add(kvp.Key,kvp.Value)
                | _ -> malformed "meta data" (vect args)
                v.metaMap <- Some(meta)
                parseOptions t
            | {value=Keyword("validator")} :: f :: t ->
                let f' = fun v -> eval id env (ExprList([f; v]) |> e2v)
                v.validator <- Some(f)
                agent.Validator <- fun v -> (f' v).IsTrue
                parseOptions t
            | {value=Keyword("error-handler")} :: f :: t ->
                agent.ErrorHandler <- fun ex -> eval id env (ExprList([f; e2v(Object(ex))]) |> e2v) |> ignore
                parseOptions t
            | [] -> ()
            | _ -> malformed "agent" (vect args)
        parseOptions t
        agent.Start()
        v |> cont
    | _ -> malformed "agent" (vect args)

and Send cont env form args =
    if not(inTrans()) then  failwith "No transaction running"
    let a,r,t = match args with
                | {value=Symbol(s)} as sm :: t -> 
                    let a = Lookup env sm 
                    match a with
                    | {value=Agent(r)} -> a,r,t
                    | _ -> failwith ("unable to locate : " + s)       
                | {value=Agent(r)} :: t -> args.Head,r,t
                | _ -> malformed "send" (vect args)

    let f' = match t with
                | f :: t' -> 
                     fun v -> eval id env (ExprList(f :: v :: t') |> e2v)
                | _ -> malformed "send" (vect args)
    r.Send(f')
    a |> cont

and AtomSwap cont env args =
    let a,r,t = match args with
                | {value=Symbol(s)} as sm :: t ->  
                    match Lookup env sm with
                    | {value=Atom(r)} as a -> a,r,t
                    | _  -> failwith ("unable to locate : " + s)       
                | {value=Atom(r)} :: t -> args.Head,r,t
                | _ -> malformed "swap!" (vect args)

    let rec compexch() =
        let v = !r
        let f' = match t with
                    | f :: t' -> ExprList(f :: v :: t') |> e2v
                    | _ -> malformed "swap!" (vect args)
        let newv = eval id env f'
        let oldv = Interlocked.CompareExchange(r, newv, v) 
        if v <> oldv then compexch() 
        else 
            fireWatchers env a oldv v
            newv


    compexch() |> cont

and AtomReset cont env args =
    match args with
    | [{value=Symbol(s)} as sm ; e] ->  
        let a = Lookup env sm
        match a with
        | {value=Atom(r)} -> 
            let oldv = !r
            let newv = eval id env e
            fireWatchers env a oldv newv
            r := newv
            !r |> cont
        | _  -> failwith ("unable to locate : " + s)       
    | [{value=Atom(r)}; e] -> 
            r := eval id env e
            !r |> cont
    | _ -> malformed "reset!" (vect args)

and Debug cont (env : Environment) form args =
    match args with
    | [] -> incUnbound |> cont
    | [x] -> eval cont env x
    | _ -> malformed "debug" (vect args) 

and Define cont (env : Environment) form args =
    match args with
    | [{value=Symbol(s)} as v; e] ->
        match Globals.GetVar(s) with
        | None -> intern env s incUnbound v.metaMap
        | Some(_) -> ()
        let def = eval id env e
        def.metaMap <- v.metaMap
        intern env s def v.metaMap
        
        Dummy("#'" + Globals.NSQualify(s)) |> e2v |> cont
    | [{value=Symbol(s)} as v] -> 
        intern env s incUnbound v.metaMap
        Dummy("#'" + Globals.NSQualify(s)) |> e2v |> cont
    | m -> malformed "def" (vect m)

and intern env nm def meta =
    let oldv =  Globals.Intern(nm,def,meta)

    match oldv with
    | Some(oldv) ->
        match Globals.GetVar(nm) with
        | Some(v) -> fireWatchers env v oldv def
        | _ -> failwith "can't happen"
    | _ -> ()

and load file = Load (fun _ -> Dummy("") |> e2v) [String(file) |> e2v] |> ignore

and Load cont args = 
    match args with
    | [{value=String(file)}] ->
        (File.OpenText(file)).ReadToEnd() |> List.ofSeq |> parse file 
         |> List.iter (fun top -> 
                        let nm = top.Name()
                        eval id [] top |> ignore
                       )
        Symbol(sprintf "Loaded '%s'." file) |> e2v |> cont
    | m -> malformed "load" (vect m)

and Print cont args =
    match args with
    | [e] -> print e |> printf "%s"; incNil |> cont
    | h :: t -> print h |> printf "%s "
                Print cont t
    | _ -> malformed "print" (vect args)

and Display cont (args : IncValue list) =
    let prn e fmt =
        match e.value with
        | String(s) -> "\"" + s + "\""
        | _ -> print e 
        |> printf fmt 
    match args with
    | [e] ->
        prn e "%s"
        incNil |> cont
    | h :: t -> prn h "%s "
                Display cont t
    | _ -> malformed "display" (vect args)

and Dissoc cont args =
    match args with
    | [m; k] ->
        match m.value with
        | EvaldDict(mp) -> EvaldDict(mp.Remove(k)) |> e2v |> cont
        | ExprDict(l) -> 
            let tl = [for tk,v in l do if tk <> k then yield tk,v]
            ExprDict(tl) |> e2v |> cont
        | EvaldSet(s) -> EvaldSet(s.Remove(k)) |> e2v |> cont
        | ExprSet(l) ->
            let tl = [for v in l do if v <> k then yield v]
            ExprSet(tl) |> e2v |> cont
        | _ -> malformed "dissoc" (vect args)
    | _ -> malformed "dissoc" (vect args)

and Try cont env form args =
    let mutable rem = List.rev args
    let body = ref []
    let catches = ref []
    let mutable fin = []

    match rem.Head with
    | {value=ExprList(l)} ->
        match l with
        | {value=Symbol(s)} :: t when s = "finally" -> 
            fin <- t
            rem <- rem.Tail
        | _ -> ()
    | _ -> ()
    
    let rec parsecatches a = 
        match a with
        | h :: t ->
            match h.value with
            | ExprList({value=Symbol("catch")} :: t') -> 
                catches := t' :: !catches
                parsecatches t
            | _ -> body := a
        | _ -> failwith "try has no body"
    parsecatches rem 

    let matchCatch ex =
        let rec _mtch = function
            | h :: t -> 
                match h with
                | {value=Symbol(clss)} :: {value=Symbol(nm)} :: xprs ->
                    let typ = System.Type.GetType(clss)
                    if typ.IsAssignableFrom(ex.GetType()) then
                        let env' = extend env [sym(nm), Object(ex) |> e2v]
                        Begin cont env' form xprs //  execute body
                    else
                        _mtch t
                | _ -> malformed "catch" (vect h)
            | [] -> raise ex
        _mtch !catches

    if fin = [] then 
        try
            if !catches = [] then
                Begin cont env form !body //  execute body
            else
                try 
                    Begin cont env form !body //  execute body
                with ex ->
                    matchCatch ex
                
        finally
            Begin id env form fin |> ignore

    else
        try 
            Begin cont env form !body //  execute body
        with ex ->
            matchCatch ex
    
and Binding cont env form args =
    match args with
    | [{value=ExprVector(bindings)}; body] ->
        let orgvars = GlobalEnvironment.DynVars
        let rec foldbind env' = function
            | {value=Symbol(s)} as sm :: e :: t -> 
                let x = eval id env e
                let env'' = extend env' [sm, x]
                foldbind env'' t
            | [] -> 
                GlobalEnvironment.DynVars <- env'
                let mutable rslt = incNil
                try
                    rslt <- eval id env body
                finally
                    GlobalEnvironment.DynVars <- orgvars
                rslt |> cont
            | _ -> failwith "Malformed binding."
        foldbind orgvars (Seq.toList (bindings.toSeq()))
    | _ -> malformed "binding" (vect args)

and InterOp cont env form args =
    match args with
    | h :: t ->
        let instanceMatch() =
            let i = eval id env h
            let o = i.value.ToObject()
            let typ = o.GetType()
            match t with 
            | [{value=Symbol(m)}] ->
                let i = typ.GetField(m)
                if i = null then
                    let i = typ.GetProperty(m)
                    if i = null then 
                        let meth = typ.GetMethod(m, [| |])
                        if meth = null then malformed "." (vect args)
                        else meth.Invoke(o, [| |])
                    else i.GetValue(o)
                else i.GetValue(o)
            | [{value=ExprList(l)}] -> 
                match l with
                | {value=Symbol(m)} :: t' ->
                    let args' = [|for x in t' -> (eval id env x).value.ToObject() |]
                    let typs = [| for a in args' -> o.GetType() |]
                    let meth = typ.GetMethod(m, typs)   // binding flags public?
                    meth.Invoke(o, args')
                | _ -> malformed "." (vect args)
            | {value=Symbol(m)} :: t' ->
                let meth = typ.GetMethod(m)   // binding flags public
                let args' = [|for x in t' -> (eval id env x).value.ToObject() |]
                meth.Invoke(o, args')
            | _ -> malformed "." (vect args)
        let o =
            match h.value with 
            | Symbol(s) -> 
                let s' = s.Replace("Inc.","Inc+")  
                let typ = System.Type.GetType(s')
                if typ = null then instanceMatch()
                else
                    match t with 
                    | [{value=Symbol(m)}] ->
                        let i = typ.GetField(m)
                        if i = null then
                            let i = typ.GetProperty(m)
                            if i = null then malformed "." (vect args)
                            else i.GetValue(null)
                        else i.GetValue(null)
                    | [{value=ExprList(l)}] -> 
                        match l with
                        | {value=Symbol(m)} :: t' ->
                            let meth = typ.GetMethod(m)   // binding flags public
                            let args' = [|for x in t' -> (eval id env x).value.ToObject() |]
                            meth.Invoke(null, args')
                        | _ -> malformed "." (vect args)
                    | {value=Symbol(m)} :: t' ->
                        let meth = typ.GetMethod(m)   // binding flags public
                        let args' = [|for x in t' -> (eval id env x).value.ToObject() |]
                        meth.Invoke(null, args')
                    | _ -> malformed "." (vect args)
            | _ -> instanceMatch()
        IncExpr.Lift(o) |> e2v |> cont
    | _ -> malformed "." (vect args)

and Cond cont env form args =
    let rec _cond vs =
        match vs with
        | tst :: xpr :: t ->
            let v = eval id env tst
            if v.IsTrue then eval cont env xpr 
            else _cond t
        | [] -> incNil |> cont
        | _ -> malformed "cond (uneven no of args)" (vect args)
    _cond args

and New cont env form args =
    match args with
    | {value=Symbol(s)} :: t ->
        let typ = System.Type.GetType(s)
        let args' = [|for x in t -> 
                          let v = eval id env x
                          v.value.ToObject() 
                    |]
        let o = Activator.CreateInstance(typ, args')
        IncValue.Lift(o) |> cont
    | _ -> malformed "new" (vect args)

and AddWatch cont env form args =
    match args with
    | [h; k; f] ->
        let rf = match h.value with
                 | Symbol(s) -> 
                     let v = Globals.GetVar(s)
                     match v with
                     | Some({value=Var(r)}) -> let _,v' = !r in v'
                     | _ -> failwith "not a var" 
                 | _ -> h

        if rf.IsIdentity then
            let key = eval id env k
            rf.SetWatcher(key,f)
            Dummy("Watcher added") |> e2v |> cont
        else failwith "targe for watch not a ref type"
    | _ -> malformed "add-watch" (vect args)

and fireWatchers env rf oldv newv =
    match rf.watchers with
    | Some(m) ->
        for kvp in m do
            let ps = vect([e2v(kvp.Key.value); rf; oldv; newv])
            FnStar ignore env None [ps; kvp.Value] 
    | _ -> ()

and Meta cont args =
    match args with
    | [v] -> 
        match v.metaMap with
        | Some(m) -> EvaldDict(m) |> e2v |> cont
        | _ -> incNil |> cont
    | _ -> malformed "meta" (vect args)

and WithMeta cont args =
    match args with
    | [v; {value=ExprDict(m)}] ->
         let m' = PersistentMap.ofPairs(m) 
         IncValue.OfExprM(v.value,Some(m'))
    | [v; {value=EvaldDict(m)}] ->
         IncValue.OfExprM(v.value,Some(m))
    | [v; {value=Nil}] -> v
    | _ -> malformed "with-meta" (vect args)

and MonitorEnter cont args =
    match args with
    | [v] -> 
        System.Threading.Monitor.Enter(v.lockObj)
        Dummy("monitor entered") |> e2v |> cont
    | _ -> malformed "monitor-enter" (vect args)

and MonitorExit cont args =
    match args with
    | [v] ->
        if System.Threading.Monitor.IsEntered(v.lockObj) then
            System.Threading.Monitor.PulseAll(v.lockObj)
            System.Threading.Monitor.Exit(v.lockObj)
            Dummy("monitor exited") |> e2v |> cont
        else Dummy("monitor not entered") |> e2v |> cont
    | _ -> malformed "monitor-enter" (vect args)

and MakeList cont env form args =
    let rec _lst l acc =
        match l with
        | h :: t ->
            _lst t ((eval id env h) :: acc)
        | [] -> 
            lst(List.rev acc) |> cont
    _lst args []

and MakeMap cont args =
    match args with
    | [{value=EvaldSeq(s)}] ->
        let rec rd rem (m : IncMap) =
            if Seq.isEmpty rem then m
            else rd (Seq.skip 2 rem) (m.SetItem(Seq.head rem, Seq.nth 1 rem))
        let m = rd s IncMap.Empty 
        EvaldDict(m) |> e2v |> cont
    | _ -> malformed "make-map" (vect args)

and MakeVector cont args =
    match args with
    | [{value=EvaldSeq(s)}] -> (vect s) |> cont
    | [{value=ExprVector(_)} as v] -> v |> cont
    | [x] -> (vect (x.ToSeq())) |> cont
    | _ -> malformed "vec" (vect args)

and RePattern cont args =
    match args with
    | [{value=String(s)}] ->
        Re(new Regex(s.Trim())) |> e2v |> cont
    | _ -> malformed "re-pattern" (vect args)

and ReMatcher cont args =
    match args with
    | [{value=Re(r)}; {value=String(s)}] ->
        ReMatch(r.Match(s)) |> e2v |> cont
    | _ -> malformed "re-matcher" (vect args)


and Recur cont (env : Environment) form args =
    let rec rcr (fs : Frame list) =
        match fs with
        | h :: t ->
            match h.RecurPt with
            | Some(prms,body) ->
                match prms with
                | {value=ExprVector(parameters)} ->
                    let binds = zipargs env false (Seq.toList (parameters.toSeq())) args 
                    for k,v in binds do h.SetItem(k,v)
                    eval cont fs body
                | _ -> rcr t // failwith "Malformed recursion point"
            | None -> rcr t
        | [] -> failwith "No recursion point found"
    env |> rcr

and MakeSymbol cont args =
    match args with
    | [{value=String(s)}] -> sym(s)
    | _ -> malformed "symbol" (vect args)

and MakeKeyword cont args =
    match args with
    | [{value=String(s)}] -> kwd(if s.StartsWith(":") then s.Substring(1) else s)
    | _ -> malformed "keyword" (vect args)

and tryLookup (env : Environment) (s : IncValue) : option<IncValue> = Globals.TryLookup(s, env)

and Lookup (env : Environment) (s : IncValue) =  Globals.Lookup(s, env) 


and IsChar (cont : Continuation) args =

    match args with
    | [v] ->
        match v.value with
        | Character(_) -> incTrue
        | _ -> incFalse
    | _ -> malformed "char?" (vect args)

and IsString (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | String(_) -> incTrue
        | _ -> incFalse
    | _ -> malformed "string?" (vect args)

and IsSymbol (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | Symbol(_) -> incTrue
        | _ -> incFalse

    | _ -> malformed "symbol?" (vect args)

and IsKeyword (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | Keyword(_) -> incTrue
        | _ -> incFalse
    | _ -> malformed "keyword?" (vect args)

and IsMap (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | EvaldDict(_) | ExprDict(_) -> incTrue
        | _ -> incFalse
    | _ -> malformed "map?" (vect args)

and IsVector (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | ExprVector(v) -> incTrue
        | EvaldExpr(e) -> IsVector cont [e.Value]
        | _ -> incFalse
    | _ -> malformed "vector?" (vect args)

and IsSeq (cont : Continuation) args =
    match args with
    | [v] -> ( if v.value.IsSeq() then incTrue else incFalse ) |> cont
    | _ -> malformed "seq?" (vect args)

and IsSeqable (cont : Continuation) args =
    match args with
    | [v] -> ( if v.value.IsSeqable() then incTrue else incFalse ) |> cont
    | _ -> malformed "seqable?" (vect args)

and IsNil (cont : Continuation) args =
    match args with
    | [v] ->
        match v.value with
        | Nil -> incTrue
        | _ -> incFalse
    | _ -> malformed "nil?" (vect args)

and Keys cont args =
    match args with
    | [v] ->
        match v.value with
        | EvaldDict(m) -> 
            let s = [for kvp in m -> kvp.Key]
            evseq s |> cont
        | ExprDict(l) -> 
            let s = [for k,v in l -> k]
            evseq s |> cont
        | _ -> malformed "keys" (vect args)
    | _ -> malformed "keys" (vect args)

and Vals cont args =
    match args with
    | [v] ->
        match v.value with
        | EvaldDict(m) -> 
            let s = [for kvp in m -> kvp.Value]
            evseq s |> cont
        | ExprDict(l) -> 
            let s = [for k,v in l -> v]
            evseq s |> cont
        | _ -> malformed "vals" (vect args)
    | _ -> malformed "vals" (vect args)

and Key cont args =
    match args with
    | [v] ->
        match v.value with
        | MapEntry(kvp) -> kvp.Key
        | _ -> malformed "key" (vect args)
    | _ -> malformed "key" (vect args)

and Val cont args =
    match args with
    | [v] ->
        match v.value with
        | MapEntry(kvp) -> kvp.Value
        | _ -> malformed "val" (vect args)
    | _ -> malformed "val" (vect args)



and Throw (cont : Continuation) env form args =
    match args with
    | [e] ->
        match (eval id env e).value with
        | Object(ex) ->
            match ex with
            | :? Exception as ex -> raise ex
            | _ -> failwith "not throwable"
        | String(s) ->  raise (Exception(s))
        | _ -> failwith "not throwable"
    | _ -> malformed "throw" (vect args)

and CoerceToInt cont args =
    match args with
    | [e] ->
        match e.value with
        | Number(n) -> Number(Int(n.ToInt())) 
        | Character(i) -> Number(Int(i)) 
        | _ -> failwith "Unable to coerce to int"
        |> e2v |> cont 
    | _ -> malformed "int" (vect args)

and ApplyTo (cont : Continuation) env form args =   
    match args with
    | f :: t ->
        let rec fltn acc (l : IncValue list) =
            match l with
            | [v] -> 
                let x = eval id env v
                if x.value.IsSeqable() then
                    let vs = Seq.toList (x.ToSeq())
                    fltn acc vs
                else fltn (v :: acc) []
            | [] -> 
                eval cont env (lst(f :: (List.rev acc)))
            | h :: t ->
                fltn (h :: acc) t
        fltn [] t
    | _ -> malformed "applyTo" (vect args)

and Partial (cont : Continuation) env form args =   
    match args with
    | f :: t ->
        let vs = [for v in t -> eval id env v]
        let closure cont' env' macro (args' : IncValue list) =
             let body = lst(f :: (vs @ args'))
             eval cont' env' body

        let def = IncValue.OfExpr(Special(closure)) 
        def |> cont
    | _ -> malformed "partial" (vect args)

and Peek (cont : Continuation) args =   
    match args with
    | [v] ->
        let x = 
            match v.value with
            | EvaldExpr(x) -> Peek cont [x.Value]
            | EvaldSeq(s) -> 
                if Seq.isEmpty s then incNil
                else Seq.head s 
            | ExprList(l) -> 
                match l with 
                | [] -> incNil
                | h :: t -> h
            | ExprVector(v) -> 
                let i = v.Length
                if i = 0 then incNil
                else v.[i - 1]
            | _ -> malformed "peek" (vect args)
        x |> cont
    | _ -> malformed "peek" (vect args)

and Pop (cont : Continuation) args =   
    match args with
    | [v] ->
        let x = 
            match v.value with
            | EvaldExpr(x) -> Pop cont [x.Value]
            | EvaldSeq(s) -> 
                if Seq.isEmpty s then failwith "nothing to pop"
                else evseq (Seq.skip 1 s) 
            | ExprList(l) -> 
                match l with 
                | [] -> failwith "nothing to pop"
                | h :: t -> lst t
            | ExprVector(v) ->  // not pretty :-(
                let i = v.Length
                if i = 0 then failwith "nothing to pos"
                let s = Seq.take (i - 1) (v.toSeq())
                vect s
            | _ -> malformed "pop" (vect args)
        x |> cont
    | _ -> malformed "pop" (vect args)

and apply (cont : Continuation) env fn args =
    let rec mapeval acc l = 
        match l with
        | h :: t -> 
            eval (fun a -> mapeval (a :: acc) t) env h
            //let a = eval id env h
            //mapeval (a :: acc) t
        | [] -> 
            fn cont (List.rev acc)
    mapeval [] args

and eval (cont : Continuation) (env : Environment) (vin : IncValue) : IncValue =

    match vin.value with
    | EvaldSeq(s) ->  //vin |> cont
        lst([for v in s -> v]) |> eval cont env

    | IncCons(cns) -> //vin |> cont
        let s = vin.ToSeq()
        lst(Seq.toList s) |> eval cont env

    | Symbol(s) -> 
        let x = if s = "*ns*" then NS(Globals.DefaultNS) |> e2v else (Lookup env vin)
        match x.value with
        | Unbound -> failwith (s + " is unbound")
        | _ -> x |> cont 

    | ExprList(h :: t) -> 
        match h.value with
        | Symbol(s) when s.StartsWith(".") && s.Length > 1 ->
            match t with
            | h' :: t' ->
                let newsym = sym (s.Substring(1))
                let newl = lst(dot :: h' :: newsym :: t') 
                eval cont env newl
            | _ -> malformed "exprlist" vin

        | Symbol(s) when s.EndsWith(".") && s.Length > 1 ->
            let newsym = sym (s.Substring(0,s.Length - 1))
            lst(sym("new") :: newsym :: t) |> eval cont env

        | Symbol(s) when s.Length > 1 && s.Contains("/") && s.Contains(".") ->
            let clss,memb = cutStr "/" s 
            lst(dot :: sym(clss) :: sym(memb) :: t) |> eval cont env 

        | Symbol(s) when s = "macroexpand-1" ->
            match t with
            | [th] ->
                let v = eval id env th
                match v.value with
                | ExprList({value=Symbol(s)} as sm :: t) ->
                    match tryLookup env sm with
                    | Some(tv) when tv.IsMacro() ->
                        match tv.value with
                        | Special(f) ->
                            f cont env (Some(v)) t
                        | _ -> v |> cont
                    | _ -> v |> cont
                | _ -> v |> cont
            | _ -> malformed "macroexpand-1" (vect t)
               
        | Symbol(s) when s = "macroexpand" ->
            match t with
            | [th] ->
                let rec ev v =
                    match v.value with
                    | ExprList({value=Symbol(s)} as sm :: t) ->
                        match tryLookup env sm with
                        | Some(tv) when tv.IsMacro() ->
                            match tv.value with
                            | Special(f) ->
                                ev (f id env (Some(v)) t)
                            | _ -> v |> cont
                        | _ -> v |> cont
                    | _ -> v |> cont
                ev (eval id env th)
            | _ -> malformed "macroexpand" (vect t)
               
        | _ -> 

            let mutable v = eval id env h
            match v.value with
            | EvaldExpr(x) -> v <- x.Value
            | _ -> ()

            match v.value with
            | Function(f) -> apply cont env f t
            | Special(f) ->
                if v.IsMacro() then
                    let x = f id env (Some(vin)) t
                    eval cont env x
                else
                    f cont env None t       
            | ExprDict(l) -> 
                match t with
                | [k] -> 
                    let k1 = eval id env k
                    match l |> List.tryFind (fun (k2,_) -> k2 = k1) with
                    | Some(_,v) -> v |> cont
                    | None -> incNil |> cont
                | _ -> malformed "index into map" (vect t)
            | EvaldDict(m) -> 
                match t with
                | [k] ->
                    let k1 = eval id env k
                    (if m.ContainsKey(k1) then m.[k1] else incNil) |> cont
                | _ -> malformed "index into map" (vect t)
            | ExprVector(v) -> 
                match t with
                | [k] -> 
                    let k1 = eval id env k
                    match k1.value with
                    | Number(n) -> v.[Convert.ToInt32(n.ToInt())] |> cont
                    | _ -> malformed "index into vector" (vect t)
                | _ -> malformed "index into vector" (vect t)
            | Keyword(k) -> 
                match t with
                | [m] ->
                    let m1 = eval id env m
                    Get cont [m1; v]  
                | _ -> malformed "keyword into map" (vect t)
            | m -> malformed "IncExpr" (e2v m)

    | ExprList([]) -> incNil |> cont 

    | ExprVector(v) -> 
        let v' = vect (seq {for x in v.toSeq() -> eval id env x}) 
        EvaldExpr(EvaluatedIncValue(v')) |> e2v |> cont

    | ExprDict(prs) ->
        let rec _map acc = function
            | (k, v) :: t -> 
                _map (((eval id env k),(eval id env v)) :: acc) t 
            | [] -> EvaldDict(IncMap.ofPairs(acc)) |> e2v |> cont
        _map [] prs

    | ExprSet(lst) ->
        let rec _map acc = function
            | h :: t -> eval (fun a -> _map (a :: acc) t) env h
            | [] -> EvaldSet(Set<IncValue>(acc)) |> e2v
        let elst = _map [] lst 
        EvaldExpr(EvaluatedIncValue(elst)) |> e2v |> cont

    | Dummy(s) -> sprintf "Cannot evaluate dummy value: %s" s |> failwith
    | Unbound -> failwith "Cannot evaluate unbound value"
    | _ -> vin |> cont

type Util() =
    static member identical(x : obj, y : obj) =
        if x = null || y = null then (x = null && y = null)
        elif x.GetType().IsValueType then x.Equals(y)
        else System.Object.ReferenceEquals(x,y)

// debugging assistance
    static member lookup(env : Environment, nm : string) =
        match lookup env (sym(nm)) with
        | Some(v) -> v
        | None -> failwith "not found" 