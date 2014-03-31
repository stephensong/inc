module Utils

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
open System.Diagnostics
open System.Text
open System.Runtime.CompilerServices
open System.Collections.Generic

let comb (s : int) (h : int) = s ^^^ (h + 0x9e3779b9 + (s <<< 6) + (s >>> 2))

let hashSeq s = s |> Seq.fold (fun x y -> hash (x * (hash y)) ) 1

let bytesEqual (a : byte[]) (b : byte[]) =
    a.Length = b.Length && Array.TrueForAll((Array.zip a b), (fun (x,y) -> x.Equals(y)))

let compareBytes (a : byte[]) (b : byte[]) =
    Seq.compareWith (fun x y -> compare x y) a b


let cutStr (sep : string) (s : string) =
    let i = s.IndexOf(sep)
    if i = 0 then s, ""
    else s.Substring(0,i), s.Substring(i+sep.Length)

let rCutStr (sep : string) (s : string) =
    let i = s.LastIndexOf(sep)
    if i = 0 then s, ""
    else s.Substring(0,i), s.Substring(i+sep.Length)

let findBalancer (copen : char) (s : string) (start : int) =
    let i = if s.[start] = copen  then start + 1 else start
    let cClose = match copen with
                 | '(' -> ')'
                 | '[' -> ']'
                 | '{' -> '}'
                 | _ -> failwith "invalid balance char"
    let rec _find i n =
        if i >= s.Length then -1
        elif s.[i] = cClose then
            if n = 0 then i
            else
                _find (i + 1) (n - 1)
        elif s.[i] = copen then _find (i + 1) (n + 1)
        else _find (i + 1) n
    _find i 0

let cutBalancer copen s =
    let i = findBalancer copen s 0
    s.Substring(0,i), s.Substring(i + 1)

let joinStr (sep : string) (s : string seq) =
    let a = Seq.toArray(s)
    System.String.Join( sep, a ) 

let everyNth n elements =
    elements
    |> Seq.mapi (fun i e -> if i % n = n - 1 then Some(e) else None)
    |> Seq.choose id

let everyOdd elements =
    elements
    |> Seq.mapi (fun i e -> if i % 2 = 1 then Some(e) else None)
    |> Seq.choose id

let partition n elements =
    let rec split s = 
        seq { 
            if not( Seq.isEmpty s) then 
                yield (Seq.take n s) 
                yield! (split (Seq.skip n s)) 
             }
    split elements 

type StringParser( s : string, ?p : int )  =
    let mutable pos = defaultArg p 0

    member this.Pos = pos
    member this.String = s
    member this.Skip(n) = pos <- pos + n
    member this.Read(n) =
        let rslt = s.Substring(pos,n)
        this.Skip(n)
        rslt

    member this.Head =
        if pos > s.Length then failwith "Parser is corrupt"
        s.[pos]

    member this.Cut (sep : string) =
        let i = s.IndexOf(sep, pos)
        if i = 0 then 
            let rslt = s.Substring(pos)
            pos <- s.Length
            rslt
        else 
            let rslt = s.Substring(pos,i - pos)
            pos <- i + sep.Length
            rslt
        
type BytesParser (s : byte[], ?p : int ) =
    let mutable pos = defaultArg p 0 

    member this.Pos = pos
    member this.Bytes = s
    member this.Skip(n) = pos <- pos + n
    member this.Read(n : int) =
        let rslt : byte[] = Array.zeroCreate n
        Array.Copy(s,pos,rslt,0,n) 
        this.Skip(n)
        rslt
        
    member this.Head =
        if pos > s.Length then failwith "Parser is corrupt"
        s.[pos]

    member this.Cut (sep : byte) =
        let mutable i = pos
        while i < s.Length && s.[i] <> sep do i <- i + 1
        let l = i - pos
        let rslt : byte[] = Array.zeroCreate l
        Array.Copy(s, pos, rslt, 0, l)
        pos <- i + 1
        rslt



[<Extension>] 
type ExtraCSharpStyleExtensionMethodsInFSharp () = 

    [<Extension>] 
    static member inline In(x: 'T, xs: seq<'T>) = xs |> Seq.exists (fun o -> o = x)

    [<Extension>] 
    static member inline Contains(xs: seq<'T>, x: 'T) = xs |> Seq.exists (fun o -> o = x)

    [<Extension>] 
    static member inline NotIn(x: 'T, xs: seq<'T>) = xs |> Seq.forall (fun o -> o <> x)

    [<Extension>] 
    static member inline TryFind(d: IDictionary<'T,'U>, x: 'T) =
        if d.ContainsKey(x) then Some(d.[x]) else None


let ShuffleArray seed (ar : 'a array) = 
    let rng = new System.Random(seed)
    let n = ar.Length
    for x in 1..n do
        let i = n-x
        let j = rng.Next(i+1)
        let tmp = ar.[i]
        ar.[i] <- ar.[j]
        ar.[j] <- tmp
    ()

let Shuffle seed (s : 'a seq ) = 
    let ar = [| s |]
    ShuffleArray seed ar
    seq { for x in ar -> x }  
    
let ShuffleList seed (lst : 'a list ) =
    let ar = List.toArray lst
    ShuffleArray seed ar
    [for x in ar -> x]

let AllExcept (i : int) ( s : 'a seq) : 'a seq =
    let j = ref 0
    seq [
          for v in s do
             if i <> !j then yield v
             j := !j + 1
     ]

let PermuteSeq ( suss : seq<'a> ) (cnt : int) : seq<seq<'a>> =
    let rec perms (s : seq<'a>) count  : seq<seq<'a>> = 
        seq [
            if count = 0 then yield Seq.empty
            else
                for i in 0 .. (Seq.length s) - 1 do
                    let rem = AllExcept i s
                    let v =  Seq.nth i s 
                    let subperms = perms rem (count-1)
                    for perm in subperms do yield Seq.append [v] perm 
        ]
    perms suss cnt
            
let PermuteList ( suss : list<'a> ) (cnt : int) : list<list<'a>> =
    let ss = PermuteSeq suss cnt
    [for s in ss -> Seq.toList s]

//    let rec perms (s : list<'a>) (count : int)  : list<list<'a>> = 
//        [
//            if count = 0 then yield []
//            else
//                for i in 0 .. s.Length - 1 do
//                    let rem = AllExcept i s
//                    let v =  Seq.nth i s 
//                    let subperms = perms [for x in rem -> x] (count-1)
//                    for perm in subperms do yield v :: perm 
//        ]
//    perms suss cnt
            

(*
type FComparer<'a> =
  {compareF: 'a -> 'a -> int}
  static member Create(compareF) =
    {new FComparer<'a> with compareF = compareF}
  interface Collections.Generic.IComparer<'a> with
    member x.Compare(a, b) = x.compareF a b    

// a immutable sorted list - based on F# set
type SortedFList<'a when 'a : comparison > =
 {items: Tagged.Set<'a, Collections.Generic.IComparer<'a>> }
   
  member x.Min = x.items.MinimumElement
  member x.Items = seq {for item in x.items do yield item}
  member x.Length = x.items.Count
  member x.IsEmpty = x.items.IsEmpty
    
  static member FromList(list, sortFunction) = 
    let comparer = FComparer<'a>.Create(sortFunction)
    {new SortedFList<'a> with 
      items = Tagged.Set<'a>.Create(comparer,list)}
      
  static member FromListWithDefaultComparer(list) = 
    SortedFList<'a>.FromList(list,compare)    
      
  static member Empty(sortFunction) = 
    SortedFList<'a>.FromList([],sortFunction)
      
  static member EmptyWithDefaultComparer() = 
    SortedFList<'a>.Empty(compare)            
       
  member x.Add(y) =     
    {x with items = x.items.Add(y)}    

  member x.Remove(y) =     
    {x with items = x.items.Remove(y)}    

            
*)
