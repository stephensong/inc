module IncTypes

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


open System
open System.Text
open System.Text.RegularExpressions
open System.Xml
open System.Numerics
open System.Threading
open System.IO
open System.Collections
open System.Collections.Generic
open System.Collections.Concurrent
open ImmutableCollections
open System.Reflection
open Utils
open Numeric
open Stm
open agent

let newTVar (value : 'T) : TVar<'T> =
    TLog.NewTVarBoxedStruct(value)

let readTVar (tv : TVar<'T>) =
    let trans = TLog.Current 
    if trans = null then tv.Value
    else trans.ReadTVar(tv)

let nilObj = new obj()
let unboundObj = new obj()

let _id = ref 0L
let nextId() = Interlocked.Increment(_id)

let _gensymid = ref 0L
let nextGensymId() = Interlocked.Increment(_gensymid)

type Vec = vector.PersistentVector<IncValue>

and valVec = vector.PersistentVector<IncExpr>

and IncDelay = {body : IncValue; mutable env : Environment; mutable evald : IncValue option}

and IncLazyExpr = {mutable fn : (unit -> unit) option; mutable s : IncValue  }

and IncLazyCons = {head : IncValue; mutable tail : IncValue}

and [<CustomEquality; CustomComparison>] IncValue = 
                                                  { value : IncExpr; 
                                                    id : int64;
                                                    lockObj : obj;
                                                    mutable validator : IncValue option;
                                                    mutable watchers : IncMap option;
                                                    mutable metaMap : IncMap option}
    with
        static member OfExpr( e : IncExpr, ?m : IncMap) = IncValue.OfExprM(e,m)
        static member OfExprM( e : IncExpr, m : IncMap option) =
            let i = if e.IsIdentity then nextId() else 0L
            {value=e; id=i; lockObj = obj(); validator=None; watchers=None; metaMap=m}

        static member Lift(o) = IncValue.OfExpr(IncExpr.Lift(o))

        member this.SetWatcher(k,w) =
            if not(this.IsIdentity) then failwith "watchers only allowed on identity types"
            lock this.lockObj 
                (fun _ ->
                    let org = this.watchers
                    let ws = match this.watchers with
                             | Some(m) -> m.Add(k,w)
                             | None -> IncMap.ofPairs([k,w])
                    this.watchers <- Some(ws) 
                ) 

        member this.IsTrue = this.value.IsTrue

        member this.IsIdentity = this.value.IsIdentity

        member this.Name() =
            match this.MetaValue(":name") with
            | Some(v) -> v.ToString()
            | None -> ""


        member this.MetaValue(nm) =
            match this.metaMap with
            | None -> None
            | Some(m) ->
                let k = IncValue.OfExpr(Keyword(nm))
                if m.ContainsKey(k) then Some(m.[k])
                else None

        member this.GetMetaValue(nm) =
            match this.MetaValue(nm) with
            | Some(v) -> v
            | None -> failwith ("Missing meta value for : "+nm)

        member this.MetaIsTrue(nm) =
            match this.MetaValue(nm) with
            | Some(v) -> v.IsTrue
            | _ -> false

        member this.SetMetaValue(nm : string,v ) = this.SetMetaValue(IncValue.OfExpr(Keyword(nm)),v)
        member this.SetMetaValue(nm : IncValue,v ) =
            let m = match this.metaMap with
                    | None -> new IncMap([])
                    | Some(m) -> m
            this.metaMap <- Some(m.Add(nm,v))

        member this.IsDynamic() =
           match this.MetaValue("dynamic") with
           | None -> false
           | Some(v) -> v.IsTrue

        member this.SetDynamic() =  this.SetMetaValue(IncValue.Lift("dynamic"),IncValue.Lift(true))

        member this.IsMacro() =
            match this.MetaValue("macro") with
            | Some(v) -> v.IsTrue
            | _ -> false

        member this.SetMacro() = this.SetMetaValue("macro",IncValue.Lift(true))


        member this.IsOnce() =
            match this.MetaValue("once") with
            | Some(v) -> v.IsTrue
            | _ -> false

        member this.ToObject() =
            match this.value with
            | Var(r) -> this :> obj
            | _ -> this.value.ToObject()

        member this.ToPrint() = this.value.ToPrint()
        member this.ToSeq() = this.value.ToSeq()
        member this.IsSeq() = this.value.IsSeq()
        member this.ForceLazy() = this.value.ForceLazy()

        override this.ToString() = this.value.ToString()

        override this.GetHashCode() = 
            match this.value with
            | Ref(_) 
            | Atom(_) 
            | Agent(_)   
            | Var(_) -> comb 53 (hash this.id)
            | _ -> hash this.value 

        override a.Equals(o) =
            match o with
            | :? IncValue as b -> 
                if a.id > 0L && b.id > 0L then a.id = b.id
                else if a.id = 0L && b.id = 0L then a.value.Equals(b.value)
                else false
            | _ -> false

        interface System.IComparable with
            member a.CompareTo yobj =
                match yobj with
                | :? IncValue as b ->
                    if a.id > 0L && b.id > 0L then compare a.id b.id
                    else if a.id = 0L && b.id = 0L then compare a.value b.value
                    else failwith "unable to compare values of different types"
                | _ -> failwith "unable to compare values of different types"


and IncMap = PersistentMap<IncValue,IncValue>

and IncTypedColl<'T> when 'T : comparison =
    | TypedList of 'T list
    | TypedVector of vector.PersistentVector<'T>
    | TypedSet of Set<'T>
    | TypedSeq of seq<'T>

and IncGenericMap<'T,'U> when 'T : comparison =
    | ExprDict of ('T * 'U) list  // uneval'ed
    | EvaldDict of PersistentMap<'T,'U>  // eval'ed

and [<CustomEquality; CustomComparison>] IncExpr =
    | Unbound 
    | Nil 
    | Number of Numeric
    | DateTime of DateTime
    | String of string
    | Character of int
    | Boolean of bool
    | Symbol of string
    | Keyword of string
    | ExprList of IncValue list
    | ExprVector of Vec
    | ExprSet of IncValue list  
    | EvaldSet of Set<IncValue>
    | EvaldSeq of IncValue seq
    | ExprDict of (IncValue * IncValue) list  // uneval'ed
    | EvaldDict of IncMap  // eval'ed
    | MapEntry of KeyValuePair<IncValue,IncValue>
    | IncCons of IncLazyCons
    | IncLazy of IncLazyExpr
    | Function of (Continuation -> IncValue list -> IncValue)
    | Special of (Continuation -> Environment -> IncValue option -> IncValue list -> IncValue)  
    | Dummy of string
    | Object of Object
    | EvaldExpr of EvaluatedIncValue
    | Re of Regex
    | ReMatch of Group
    | Ref of IncValue TVar
    | Atom of IncValue ref
    | Agent of IncValue Agent
    | Var of (string * IncValue) ref
    | NS of Namespace
    | Delay of IncDelay
    with
        static member Lift(o : obj) =
            match o with
            | null -> Nil
            | :? char as c -> Character(int c)
            | :? string as s -> String(s)
            | :? bool as b -> Boolean(b)
            | :? DateTime as d -> DateTime(d)
            | :? int as i -> Number(Int(i))
            | :? int64 as i -> Number(Long(i))
            | :? BigInteger as i -> Number(BigInt(i))
            | :? Decimal as d -> Number(Decimal(d))
            | :? Double as f -> Number(Float(f))
            | :? Single as f -> Number(Float(float f))
            | :? Regex as r -> Re(r)
            | :? Group as m -> ReMatch(m)
            | :? IDictionary<obj,obj> as d ->
                EvaldDict(IncMap.ofPairs(seq {for kvp in d -> IncValue.Lift(kvp.Key),IncValue.Lift(kvp.Value)}))
            | :? IEnumerable as os -> 
                let s = seq { for x in os -> IncValue.Lift x }
                if Seq.isEmpty s then Nil else EvaldSeq(s)
            | _ -> Object(o)

        member this.ToObject(o : obj) =
            match this with
            | Nil -> null :> obj
            | Unbound -> null :> obj
            | Character(c) -> (char c) :> obj
            | String(s) -> s :> obj
            | Boolean(b) -> b :> obj
            | DateTime(d) -> d :> obj
            | Number(Int(i)) -> i :> obj
            | Number(BigInt(i)) -> i :> obj
            | Number(Decimal(d)) -> d :> obj
            | Number(Float(f)) -> f :> obj
            | Number(Rational(r)) -> r :> obj
            | EvaldSet(x) -> x :> obj
            | EvaldSeq(x) -> x :> obj
            | EvaldDict(dict) -> dict :> obj 
            | ExprList(l) -> l :> obj
            | ExprVector(v) -> v :> obj
            | ExprDict(d) -> d :> obj  
            | Var(r) -> let _,v = !r in v :> obj
            | Object(o) -> o
            | Re(r) -> r :> obj
            | ReMatch(m) -> m :> obj
            | EvaldExpr(x) -> 
                let v : IncValue = x.Value
                v.ToObject()
            | _ -> failwith "toobject not supported"

        member this.IsIdentity =
            match this with
            | Ref(_)
            | Atom(_)
            | Var(_)
            | Agent(_) -> true
            | _ -> false

        member this.IsTrue =
            match this with
            | Boolean(b) when not b  -> false
            | Nil -> false
            | EvaldExpr(x) -> 
                let v : IncValue = x.Value
                v.IsTrue
            | _ -> true

        override this.ToString() =
            let print x = x.ToString()
            match this with
            | IncLazy(lz) ->
                match lz.fn with
                | Some(f) -> "lazy-seq"
                | None -> lz.s.ToString()  
            | IncCons(_) -> 
                let rec prn c =
                    match c with
                    | IncCons(cns) ->
                        match cns.tail.value with
                        | Nil | Unbound ->  cns.head.ToString() 
                        | _ ->  cns.head.ToString() + " " + (prn cns.tail.value) + " "
                    | _ -> c.ToString()
                "(" + (prn this).TrimEnd() + ")"   
            | EvaldExpr(x) -> print x.Value.value
            | EvaldSet(x) -> "#{" + String.Join(" ", Set.map (fun v -> print v.value) x) + "}"
            | EvaldSeq(_) -> "(" + String.Join(" ", (Seq.map (fun v -> print v.value) (this.ToSeq()))) + ")"
            | EvaldDict(dict) -> 
                let prs = [for kvp in dict -> (print kvp.Key.value) + " " + (print kvp.Value.value)]
                "{" + String.Join(" ", prs) + "}"
            | MapEntry(kvp) -> "[" + (print kvp.Key.value) + " " + (print kvp.Value.value) + "]"
            | ExprList({value=Dummy(_)} :: _) -> "" // don't print accumulated statement dummy values
            | ExprList(l) -> "(" + String.Join(" ", [for v in l -> print v.value]) + ")"
            | ExprVector(v) -> "[" + String.Join(" ", (Seq.map (fun x -> print x.value) (v.toSeq()))) + "]"
            | ExprDict(dict) ->  
                let prs = [for (k,v) in dict -> (print k.value) + " " + (print v.value)]
                "{" + String.Join(" ", prs) + "}"
            | ExprSet(list) -> "#{" + String.Join(" ", [for v in list -> print v.value]) + "}"
            | Boolean(l) -> if l then "true" else "false"
            | Nil -> "nil"
            | Unbound -> "???"
            | String(s) -> s
            | Symbol(s) -> s
            | Re(r) -> "#\"" + r.ToString() + "\""
            | ReMatch(m) -> "\"" + m.Value + "\""
            | Var(r) -> let nm,v = !r in print v.value
            | Keyword(s) -> ":" + s
            | Number(n) -> n.ToString()
            | DateTime(d) -> 
                let utc = TimeZoneInfo.ConvertTimeToUtc(d);
                "#inst \"" + XmlConvert.ToString(utc, XmlDateTimeSerializationMode.Utc) + "\"";

            | Function(_) -> "Function"
            | Special(_) -> "Special"
            | Delay(d) -> "delay"
            | Ref(r) -> "Ref: " + print (readTVar r).value
            | Atom(r) -> "Atom: " + (print (!r).value)
            | Agent(a) -> "Agent: " + (print (a.Deref().value))
            | NS(x) -> "Namespace: " + x.Name
            | Dummy(s) -> ""
            | Character(i) -> 
                 let c = char i
                 match c with
                 | '\n' -> "\\n"
                 | '\t' -> "\\t"
                 | '\f' -> "\\f"
                 | '"' -> "\\\""
                 | _ -> "\\" + c.ToString()
            | Object(o) -> o.ToString() 


        member this.ToPrint() =
            let print (x : IncExpr) = x.ToPrint()
            match this with
            | IncLazy(_)  
            | IncCons(_) -> 
                let l = this.Unlazy()
                "(" + String.Join(" ", [for v in l -> print v.value]) + ")"   
            | EvaldExpr(x) -> print x.Value.value
            | EvaldSet(x) -> "#{" + String.Join(" ", Set.map (fun v -> print v.value) x) + "}"
            | EvaldSeq(_) -> "(" + String.Join(" ", (Seq.map (fun v -> print v.value) (this.ToSeq()))) + ")"
            | EvaldDict(dict) -> 
                let prs = [for kvp in dict -> (print kvp.Key.value) + " " + (print kvp.Value.value)]
                "{" + String.Join(" ", prs) + "}"
            | MapEntry(kvp) -> "[" + (print kvp.Key.value) + " " + (print kvp.Value.value) + "]"
            | ExprList({value=Dummy(_)} :: _) -> "" // don't print accumulated statement dummy values
            | ExprList(l) -> "(" + String.Join(" ", [for v in l -> print v.value]) + ")"
            | ExprVector(v) -> "[" + String.Join(" ", (Seq.map (fun x -> print x.value) (v.toSeq()))) + "]"
            | ExprDict(dict) ->  
                let prs = [for (k,v) in dict -> (print k.value) + " " + (print v.value)]
                "{" + String.Join(" ", prs) + "}"
            | ExprSet(list) -> "#{" + String.Join(" ", [for v in list -> print v.value]) + "}"
            | Boolean(l) -> if l then "true" else "false"
            | Nil -> "nil"
            | Unbound -> "???"
            | String(s) -> "\"" + s + "\""
            | ReMatch(m) -> "\"" + m.Value + "\""
            | Re(r) -> "#\"" + r.ToString() + "\""
            | Symbol(s) -> s
            | Var(r) -> let nm,v = !r in print v.value
            | Keyword(s) -> ":" + s
            | Number(n) -> n.ToString()
            | DateTime(d) -> 
                let utc = TimeZoneInfo.ConvertTimeToUtc(d);
                "#inst \"" + XmlConvert.ToString(utc, XmlDateTimeSerializationMode.Utc) + "\"";

            | Function(_) -> "Function"
            | Special(_) -> "Special"
            | Delay(d) -> "delay"
            | Ref(r) -> "Ref: " + print (readTVar r).value
            | Atom(r) -> "Atom: " + (print (!r).value)
            | Agent(a) -> "Agent: " + (print (a.Deref().value))
            | NS(x) -> "Namespace: " + x.Name
            | Dummy(s) -> ""
            | Character(_) -> this.ToString()
            | Object(o) -> o.ToString() 

        override x.GetHashCode() =
            match x with
            | EvaldExpr(x) -> hash x
            | Number(n) -> comb 2 (hash n)
            | DateTime(d) -> comb 3 (hash d)
            | String(s) -> comb 5 (hash s)
            | Boolean(l) -> comb 7 (hash l)
            | Nil -> hash 11 
            | Unbound -> hash 13
            | Symbol(s) -> comb 17 (hash s)
            | Keyword(k) -> comb 19 (hash k)
            | ExprVector(l) -> comb 23 (hashSeq <| l.toSeq())
            | ExprList(l) -> comb 23 (hashSeq l)
            | EvaldSeq(s) -> comb 23 (hashSeq s)
            | EvaldDict(m) -> comb 29 (hash m)
            | ExprDict(m) -> comb 29 (hashSeq <| seq { for k,v in m do yield k; yield v })
            | EvaldSet(s) ->  comb 31 (hashSeq <| Set.toSeq s)
            | Re(r) -> comb 37 (hash (r.ToString()))
            | ReMatch(m) -> comb 41 (hash m)
            | Character(i) -> comb 43 (hash i)
            | Object(o) -> comb 47 (hash o)
            | MapEntry(kvp) -> comb 53 (hashSeq [kvp.Key; kvp.Value])
            | IncLazy(_) 
            | Delay(_) 
            | IncCons(_) 
            | Ref(_) 
            | Atom(_)   
            | Agent(_)  
            | Var(_)
            | ExprDict(_) 
            | ExprSet(_)
            | Function(_)
            | Special(_)
            | NS(_)
            | Dummy(_) ->  failwith "Illegal attempt to take hash code"

        override a.Equals(o) =
            let _equals (a : IncValue, b : IncValue) = a.Equals(b)
            match o with
            | :? IncExpr as b ->
                match a,b with
                | Number(a), Number(b) -> a = b 
                | Boolean(a), Boolean(b) -> a = b 
                | String(a), String(b) -> a = b 
                | Character(a), Character(b) -> a = b 
                | DateTime(a), DateTime(b) -> a = b 
                | Re(a), Re(b) -> a.ToString() = b.ToString()
                | NS(a), NS(b) -> Object.ReferenceEquals(a, b)
                | Object(a), Object(b) -> Object.ReferenceEquals(a, b)
                | ExprList(a), ExprList(b) -> a.GetHashCode() = b.GetHashCode()
                | ExprVector(a), ExprVector(b) -> a.GetHashCode() = b.GetHashCode()
                | ExprSet(a), ExprSet(b) -> a.GetHashCode() = b.GetHashCode()
                | ExprDict(a), ExprDict(b)  -> a.GetHashCode() = b.GetHashCode()
                | MapEntry(a), MapEntry(b) -> a.Key = b.Key && a.Value = b.Value
                | Symbol(a), Symbol(b) -> a = b
                | Keyword(a), Keyword(b) -> a = b
                | Ref(a), Ref(b) -> Object.ReferenceEquals(a,b) 
                | Atom(a), Atom(b) -> Object.ReferenceEquals(a,b) 
                | Agent(a), Agent(b) -> Object.ReferenceEquals(a,b) 
                | _,_ -> Object.ReferenceEquals(a,b)
            | _ -> false

        member this.IsSeq() =
            match this with
            | EvaldExpr(x) -> x.Value.value.IsSeq()
            | EvaldSeq(_) 
            | ExprList(_) 
            | IncLazy(_) 
            | IncCons(_) -> true
            | Object(o) ->
                match o with
                | :? IEnumerable -> true
                | _ -> false
            | _ -> false

        member this.ForceLazy() = 
            match this with
            | IncLazy(lz) ->
                match lz.fn with
                | Some(f) -> 
                    lock lz
                       (fun _ ->
                            match lz.fn with
                            | Some(f) -> 
                                lz.fn <- None
                                f() 
                            | _ -> ()
                       )
                | _ -> ()
                lz.s
            | _ -> failwith "not a lazy-seq"

        member this.SplitHead() =
            let s = this.ToSeq()
            if Seq.isEmpty s then 
                let unb = IncValue.OfExpr(Unbound)
                unb,unb
            else 
                let h = Seq.head s
                let t = Seq.skip 1 s
                match h.value with
                | IncCons(cns) -> 
                    if not (Seq.isEmpty t) then failwith "error in cons"
                    cns.head,cns.tail
                | IncLazy(lz) -> 
                    h.ForceLazy(),IncValue.OfExpr(EvaldSeq(t))
                | _ -> h,IncValue.OfExpr(EvaldSeq(t))

        member this.DoRun() =
            let rec _run (x : IncExpr) =
                let h,t = x.SplitHead()
                match h.value with
                | Unbound -> ()
                | _ -> _run t.value
            _run this

        member this.Unlazy() =
            let rec _run (x : IncExpr) acc =
                let h,t = x.SplitHead()
                match h.value with
                | Unbound -> List.rev acc
                | IncLazy(_) | IncCons(_) ->
                    let l = h.value.Unlazy() 
                    _run t.value (IncValue.OfExpr(EvaldSeq(l)) :: acc)
                | _ -> _run t.value (h :: acc)
            _run this []

        member this.IsSeqable() =
            match this with
            | EvaldExpr(x) -> x.Value.value.IsSeqable()
            | EvaldSeq(_) 
            | ExprList(_) 
            | EvaldSet(_)
            | ExprVector(_) 
            | EvaldDict(_) 
            | ExprDict(_) 
            | MapEntry(_)
            | ExprSet(_)
            | IncLazy(_) 
            | IncCons(_) -> true
            | Object(o) ->
                match o with
                | :? IEnumerable -> true
                | _ -> false
            | _ -> false

        member this.ToSeq() =
            let rslt = 
                match this with
                | EvaldExpr(x) -> x.Value.value.ToSeq()
                | ExprList(l) -> List.toSeq l
                | ExprVector(l) -> l.toSeq()
                | EvaldSet(s) -> Set.toSeq s
                | IncCons(cns) -> seq { yield cns.head; 
                                        yield! cns.tail.ToSeq() }
                | IncLazy(_) -> this.ForceLazy().ToSeq()
                | EvaldSeq(s) -> s
                | EvaldDict(d) -> seq { for kvp in d -> IncValue.OfExpr(MapEntry(kvp)) }  
                | ExprDict(d) -> seq { for k,v in d -> IncValue.OfExpr(MapEntry(KeyValuePair(k,v))) }  
                | String(s) -> seq { for c in s -> IncValue.OfExpr(Character(int c)) }
                | MapEntry(kvp) -> seq { yield kvp.Key; yield kvp.Value}
                | Nil | Unbound -> Seq.empty 
                | Object(o) ->
                    match o with
                    | :? IEnumerable as os -> seq { for x in os -> IncValue.Lift(x) }
                    | _ -> failwith "invalid seq'able"
                    
                | _ -> failwith "invalid seq'able"
            rslt

        interface System.IComparable with
            member a.CompareTo yobj =
                match yobj with
                | :? IncValue as b -> compare a b.value
                | :? IncExpr as b ->
                    match a, b with
                    | Number(a), Number(b) -> compare a b 
                    | Boolean(a), Boolean(b) -> compare a b 
                    | String(a), String(b) -> compare a b 
                    | DateTime(a), DateTime(b) -> compare a b 
                    | Symbol(a), Symbol(b) -> compare a b 
                    | Character(a), Character(b) -> compare a b 
                    | Keyword(a), Keyword(b) -> compare a b 
                    | ExprVector(a), ExprVector(b) ->
                        let l = max a.Length b.Length
                        let a' = Seq.take l (a.toSeq())
                        let b' = Seq.take l (b.toSeq())
                        let rec cmp prs =
                           match prs with
                           | [] -> 0
                           | (x,y) :: t -> 
                               let z = compare x y
                               if z = 0 then cmp t else z
                        let n = cmp [for x', y' in Seq.zip a' b' -> (x',y')]
                        if n = 0 then 
                            if a.Length < b.Length then -1 else 1
                        else n
                    | ExprSet(a), ExprSet(b) 
                    | ExprList(a), ExprList(b) -> 
                        let l = max a.Length b.Length
                        let a' = Seq.take l a
                        let b' = Seq.take l b
                        let rec cmp prs =
                           match prs with
                           | [] -> 0
                           | (x,y) :: t -> 
                               let z = compare x y
                               if z = 0 then cmp t else z
                        let n = cmp [for x', y' in Seq.zip a' b' -> (x',y')]
                        if n = 0 then 
                            if a.Length < b.Length then -1 else 1
                        else n
                    | Re(a),Re(b) -> compare (a.ToString()) (b.ToString())
                    | Nil,_ -> -1
                    | _,Nil -> 1
                    | Number(_),_ -> -1
                    | _,Number(_) -> 1
                    | Boolean(_),_ -> -1
                    | _,Boolean(_) -> 1
                    | String(_),_ -> -1
                    | _,String(_) -> 1
                    | DateTime(_),_ -> -1
                    | _,DateTime(_) -> 1
                    | Symbol(_),_ -> -1
                    | _,Symbol(_) -> 1
                    | Character(_),_ -> -1
                    | _,Character(_) -> 1
                    | Keyword(_),_ -> -1
                    | _,Keyword(_) -> 1
                    | ExprDict(_),_ -> -1
                    | Re(_),_ -> -1
                    | _,Re(_) -> 1
                    | ReMatch(_),_ -> -1
                    | _,ReMatch(_) -> 1
                    | _,ExprDict(_) -> 1
                    | EvaldDict(_),_ -> -1
                    | _,EvaldDict(_) -> 1
                    | ExprSet(_),_ -> -1
                    | _,ExprSet(_) -> 1
                    | ExprList(_),_ -> -1
                    | _,ExprList(_) -> 1
                    | EvaldSeq(_),_ -> -1
                    | _,EvaldSeq(_) -> 1
                    | MapEntry(_),_ -> -1
                    | _,MapEntry(_) -> 1
                    | ExprVector(_),_ -> -1
                    | _,ExprVector(_) -> 1
                    | _,_ -> if Object.ReferenceEquals(a,b) then 0 else failwith "Unable to compare"
                | _ -> invalidArg "yobj" "cannot compare values of different types"

//and  [<CustomEquality; CustomComparison>] EvaluatedIncValue(e: IncValue) =  // can't figure this one out
and  EvaluatedIncValue(e: IncValue) =
    let mutable _hash = -1;
    let mutable hashed = false
    member this.Value = e
    override a.Equals(o) = a.GetHashCode() = o.GetHashCode()
    override this.GetHashCode() =  // probably should really use interlocked here
        if not(hashed) then
             _hash <- hash e
             hashed <- true
        _hash

and Continuation = IncValue -> IncValue
and RecursionPoint = IncValue * IncValue 
and Frame(env : Dictionary<IncValue,IncValue>, recurPt : RecursionPoint option) = 
    
    static member Empty() = Frame(Dictionary<IncValue,IncValue>(),None)
    static member RecurFrame(prms, body) = Frame(Dictionary<IncValue,IncValue>(),Some(prms,body))

    member __.Env = env
    member __.RecurPt = recurPt
    member __.ContainsKey(k) = env.ContainsKey(k)
    member __.Item with get(k) = env.[k]
    member __.SetItem(k,v) = env.[k] <- v

and Environment = Frame list

and Namespace(name : string) = 
    let e2v e = IncValue.OfExpr e
    let str s = String(s) |> e2v
    let kwd s = Keyword(s) |> e2v
    let interns = ref PersistentMap<string, IncValue>.Empty
    let aliases = ref PersistentMap<string, Namespace>.Empty
    let refers = ref PersistentMap<string, IncValue>.Empty  // nb - currently no way to trace where refers came from
    let atomicSet(r : PersistentMap<'k,'v> ref, newv : PersistentMap<'k,'v>) =  // afaics this does nothing useful :-(
        let rec swp() =
            let oldv = !r 
            if Interlocked.CompareExchange(r,newv,oldv) <> oldv then swp()
        swp()

    member this.Name with get() = name
    member private this.Interns with get() = !interns
    member private this.Aliases with get() = !aliases
    member private this.Refers with get() = !refers
    member this.Intern(sym, v) = this.Intern(sym,v,None) 
    member this.Intern(sym, v, m : IncMap option) = 
        match v.value with 
        | Var(_) -> failwith "already interned" 
        | _ ->
            v.SetMetaValue(kwd("name"),str(sym))
            v.SetMetaValue(kwd("ns"),str(this.Name)) 
            if interns.Value.ContainsKey(sym) then
                match interns.Value.[sym].value with
                | Var(r) -> 
                    let nm,oldv = !r
                    r := (this.Name,v)
                    interns.Value.[sym].metaMap <- m
                    Some(oldv)
                | _ -> failwith "can't happen (famous last words)"
            else 
                atomicSet(interns, interns.Value.Add(sym,IncValue.OfExprM(Var(ref (this.Name,v)),m)))
                None

    member this.UnIntern(sym) = 
        atomicSet(interns, interns.Value.Remove(sym))

    member this.GetVar(sym) =
        if interns.Value.ContainsKey(sym) then Some(interns.Value.[sym])
        else if refers.Value.ContainsKey(sym) then Some(refers.Value.[sym])
             else if aliases.Value.ContainsKey(sym) then 
                      let ns : Namespace = aliases.Value.[sym]
                      ns.GetVar(sym)
                  else None

    member this.Lookup(sym) =
        match this.GetVar(sym) with
        | Some(v) -> 
            match v.value with
            | Var(r) -> let _,v = !r in Some(v)
            | _ -> failwith ("not a var : " + sym)
        | None -> None

    member this.ReferAll(src : Namespace ) = 
        this.ReferOnly(src, [for kvp in src.Interns -> kvp.Key])

    member this.ReferExcept(src : Namespace, nms : list<string> ) =
        this.ReferOnly(src, [for kvp in src.Interns do if not( List.exists (fun s -> s =  kvp.Key) nms) then yield kvp.Key])

    member this.ReferOnly(src : Namespace, nms : list<string> ) =
        for s in nms do
            match src.GetVar(s) with
            | Some(o) -> 
                atomicSet(interns, interns.Value.SetItem(s, o))
            | None -> failwith ("Unable to locate" + s)

let lookup env (symbol : IncValue) =  
    env |> List.tryPick (fun (frame : Frame) -> frame.Env.TryFind symbol ) 


let e2v e = IncValue.OfExpr e
let withMeta m v = v.metaMap <- m; v
let sym s = Symbol(s) |> e2v
let str s = String(s) |> e2v
let chr c = Character(c) |> e2v
let kwd s = Keyword(s) |> e2v
let dot = sym "."
let lst l = ExprList(l) |> e2v
let vec v = ExprVector(v) |> e2v
let vect (v : IncValue seq) = vec (Vec.create(v))
let dic m = EvaldDict(m) |> e2v
let incTrue = IncExpr.Boolean(true) |> e2v
let incFalse = IncExpr.Boolean(false) |> e2v
let incNil = IncExpr.Nil |> e2v
let incUnbound = IncExpr.Unbound |> e2v
let incEmptySeq = EvaldSeq(Seq.empty) |> e2v

let evseq s =  EvaldSeq(s) |> e2v

    
let quote v = lst [sym("quote"); v]
let incInt i = Number(Int(i)) |> e2v

let isMacro env nm = 
    match lookup env nm with
    | Some(v) -> v.IsMacro()
    | None -> false

type GlobalEnvironment() =
    let coreNS = Namespace("core")
    let mutable loadedNS : list<Namespace> = [coreNS]
    let mutable defaultNS = coreNS

    [<ThreadStatic; DefaultValue>] 
    static val mutable private dynVars : Environment option
    [<ThreadStatic; DefaultValue>] 
    static val mutable private setVars : Frame option

    static member DynVars
        with get() : Environment = 
             match GlobalEnvironment.dynVars with
             | Some(e) -> e
             | None -> 
                 let f = Frame.Empty() 
                 GlobalEnvironment.setVars <- Some(f)
                 let e = [f]  
                 GlobalEnvironment.dynVars <- Some(e)  
                 e
         and set(v) = GlobalEnvironment.dynVars <- Some(v)

    member this.getThreadBinding(s) =
        match GlobalEnvironment.dynVars with
        | None -> None
        | Some(dic) -> lookup dic s 

    member this.pushThreadBindings(bindings) =
        let dic = Dictionary<IncValue,IncValue>()
        for k,v in bindings do
            match k.value with
            | Symbol(s) -> dic.[k] <- v 
            | _ -> failwith ("not a symbol")
        let f = Frame(dic,None)
        GlobalEnvironment.DynVars <- f :: GlobalEnvironment.DynVars

    member this.popThreadBindings() =
        match GlobalEnvironment.DynVars with
        | h :: t -> GlobalEnvironment.DynVars <- t
        | [] -> failwith "No bindings to pop"

    member this.getThreadBindings() = GlobalEnvironment.DynVars 

    member this.setVar(s : string,v) =
        let nm = if not( s.Contains("/") ) && not( s.Contains(".") ) then defaultNS.Name + "/" + s else s
            
        match GlobalEnvironment.setVars with
        | None ->
            let f = Frame.Empty()
            f.SetItem(IncValue.OfExpr(Symbol(nm)), v)
            GlobalEnvironment.setVars <- Some(f)
            GlobalEnvironment.dynVars <- Some([f])  
        | Some(f) -> 
            f.SetItem(IncValue.OfExpr(Symbol(nm)), v)

    member this.FindNS(nm) =
        let rec _find nm (l : list<Namespace>) =
            match l with
            | h :: t -> if h.Name = nm then Some(h) else _find nm t
            | [] -> None
        _find nm loadedNS

    member this.LoadNS(ns) =
        loadedNS <- ns :: loadedNS

    member this.CoreNS = coreNS
    member this.DefaultNS with get() = defaultNS
                          and  set(v : Namespace) = 
                              match this.FindNS(v.Name) with
                              | Some(ns) -> defaultNS <- v
                              | None -> 
                                  this.LoadNS(v) // failwith "Namespace has not been loaded"
                                  defaultNS <- v   

    member this.Intern(symbol : string, v, m) = 
        if symbol.Contains("/") && symbol.Length > 1 then
            let ns,sym = (cutStr "/" symbol)

            match this.FindNS(ns) with
            | Some(o) -> o.Intern(sym, v, m)
            | None -> None
        else 
            this.DefaultNS.Intern(symbol, v, m)
                                     
    member this.GetVar(symbol : string) =

        if symbol.Contains("/") && symbol.Length > 1 then
            let ns,sym = (cutStr "/" symbol)

            match this.FindNS(ns) with
            | Some(o) -> o.GetVar(sym)
            | None -> None
        else
            match defaultNS.GetVar(symbol) with
            | Some(v) -> Some(v)
            | None -> coreNS.GetVar(symbol)

    member this.NSQualify(symbol : string) =
        if (symbol.Contains("/")) then symbol
        else
            match this.GetVar(symbol) with
            | Some(v) ->
                match v.value with
                | Var(r) ->
                    let ns,v' = !r
                    if ns = "core" then symbol
                    else defaultNS.Name + "/" + symbol 
                | _ -> failwith "not a var"
            | None ->
                //symbol
                if symbol.Contains(".") then symbol 
                else defaultNS.Name + "/" + symbol  // failwith ("unable to resolve symbol : " + symbol)

    member this.TryLookup(sym : IncValue, env : Environment) : IncValue option =
        match lookup env sym with
        | Some(e) -> Some(e)
        | None ->
            let qsym =
                match sym.value with
                | Symbol(s) -> IncValue.OfExpr(Symbol(this.NSQualify(s)))
                | _ -> sym
            match this.getThreadBinding(qsym) with
            | Some(v) -> Some(v)
            | None ->
                match this.GetVar(sym.ToString()) with
                | Some(v) ->
                    match v.value with
                    | Var(r) -> let ns,vt = !r 
                                Some(vt)
                    | _ -> failwith "not a var" 
                | _ -> None

    member this.Lookup(s : IncValue, env : Environment) : IncValue =
        match this.TryLookup(s,env) with
        | Some(e) -> e
        | None -> failwith ("unable to resolve symbol : " + s.ToString())


    member this.GenSym(?prfx : string) =
        let p = defaultArg prfx "INC"
        let _id = nextGensymId()
        System.Diagnostics.Debug.WriteLine(_id.ToString())
        Symbol(p + "__" + _id.ToString()) |> e2v

    member this.GenSymAuto(?prfx : string) =
        let p = defaultArg prfx "INC"
        let _id = nextGensymId()
        System.Diagnostics.Debug.WriteLine(_id.ToString())
        Symbol(p + "__" + _id.ToString() + "__auto__") |> e2v


