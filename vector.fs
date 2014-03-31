module vector

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


type Node<'T> =  
  | Empty
  | Values of 'T[]
  | Nodes of Node<'T>[]

let emptyNode = Node.Empty

//[<CustomEquality; CustomComparison>]
type PersistentVector<'T (*when 'T : equality and 'T : comparison*)>(cnt : int, shift : int, root : Node<'T>, tail : 'T[] )=

    let tailoff() = if cnt < 32 then 0 else ((cnt - 1) >>> 5) <<< 5

    let arrayFor(i) : 'T[] =
        if (i >= 0 && i < cnt) then
            if i >= tailoff() then tail
            else 
                let rec _loc (lvl : int) ( n : Node<'T>) : 'T[] =
                    if lvl = 0 then
                       match n with
                       | Values(a) -> a
                       | _ -> failwith "corrupt vector"
                    else
                       match n with
                       | Nodes(v) -> _loc (lvl-5) v.[(i >>> lvl) &&& 0x01f] 
                       | _ -> failwith "corrupt vector"
                _loc shift root
        else failwith "Index out of range"

    member this.Length = cnt

    member this.Item(i : int) : 'T =
        let v = arrayFor(i)
        v.[i &&& 0x01f] 

    static member create( s : seq<'T> ) =
        let v = PersistentVector<'T>(0,0,Node.Empty,[| |])
        v.append(s)

    member this.append( s : seq<'T> ) =
        let mutable v = this
        for o in s do  v <- v.cons(o)
        v
        
    member this.toSeq() =
        seq {for i in 0 .. (cnt - 1) -> this.[i] }

    member this.toList() = Seq.toList( this.toSeq() )

    member this.assocN(i : int, it : 'T) : PersistentVector<'T> =

        let rec _doAssoc(lvl, node : Node<'T>, i, v) =
            if lvl = 0 then
                match node with
                | Values(a) ->
                    let a' = Array.copy a
                    a'.[i &&& 0x01f] <- v
                    Values(a')
                | _ -> failwith "corrupt vector"
            else
                match node with
                | Nodes(a) ->
                    let i' = ( i >>> lvl ) &&& 0x01f;
                    let a' = Array.copy a
                    a'.[i'] <- _doAssoc(lvl-5, a.[i'], i, v);
                    Nodes(a')
                | _ -> failwith "corrupt vector"

        if (i < 0 || i > cnt) then failwith "Index out of range"
        else 
            if i = cnt then this.cons(it)
            else
                if i >= tailoff() then 
                    let newTail = Array.copy tail
                    newTail.[i &&& 0x01f] <- it
                    PersistentVector<'T>(cnt, shift, root, newTail)
                else
                    PersistentVector<'T>(cnt, shift, _doAssoc(shift, root, i, it), tail);
    
    member this.cons(v : 'T) =
        if cnt - tailoff() < 32 then
            let l = Array.length tail
            let newTail = Array.append tail [| v |]
            PersistentVector(cnt + 1, shift, root, newTail)
        else
            // full tail, push into tree
            let tailnode = Values(tail) 

            match root with 
            | Empty ->
                PersistentVector(cnt + 1, 0, tailnode, [| v |])
            | Values(_) -> 
                let a = Array.create 32 emptyNode 
                a.[0] <- root
                a.[1] <- tailnode
                PersistentVector(cnt + 1, 5, Nodes(a), [| v |])
            | Nodes(a) ->
                let rec newPath( lvl, node) =
                    if lvl = 0 then node
                    else
                        let a = Array.create 32 emptyNode
                        a.[0] <- newPath( lvl - 5, node)
                        Nodes( a )

                // overflow root?
                if (cnt >>> 5) > (1 <<< shift ) then

                    let a = Array.create 32 emptyNode 
                    let newroot = Nodes(a)
                    a.[0] <- root
                    a.[1] <- newPath(shift, tailnode)
                    PersistentVector(cnt + 1, shift + 5, newroot, [| v |] )

                else

                    let rec pushTail( lvl, prnt : Node<'T>, tailnode) =
                        match prnt with
                        | Nodes(a) ->
                            let a' = Array.copy a
                            let i' = ((cnt - 1) >>> lvl) &&& 0x01f
                            let child = a.[i']
                            a'.[i'] <- 
                                match child with
                                | Empty -> newPath( lvl - 5, tailnode)
                                | Nodes(a) -> pushTail(lvl - 5, child, tailnode)
                                | Values(_) -> failwith "corrupt vector"

                            Nodes(a')    
                        | _ -> failwith "corrupt vector"
                    let newroot = pushTail(shift, root, tailnode)
                    PersistentVector(cnt + 1, shift, newroot, [| v |] )

//    override this.GetHashCode() = this.toSeq() |> Seq.fold (fun x y -> hash (x * (hash y)) ) 1
//
//    override this.Equals(o) =
//        match o with
//        | :? PersistentVector<'T> as v ->
//            this.Length = v.Length && (Seq.zip (this.toSeq()) (v.toSeq())) |> Seq.forall (fun (a,b) -> a = b)  
//        | _ -> false
//
//    interface System.IComparable with
//        member this.CompareTo yobj =
//            match yobj with
//            | :? PersistentVector<'T> as b ->
//                    Seq.compareWith (fun x y -> compare x y) (this.toSeq()) (b.toSeq())
//            | _ -> invalidArg "yobj" "cannot compare values of different types"


let Map<'T,'U  (* when 'T : comparison and 'U : comparison *) >(v : PersistentVector<'T>, mpr : 'T -> 'U) =
    PersistentVector<'U>.create( Seq.map mpr (v.toSeq()) )

let testPersistentVector() =
    let s1 = [for i in 0 .. 31 -> i]
    let v1 = PersistentVector.create(s1)
    let v2 = v1.cons(32)
    let v3 = v1.cons(1024)
    if v1.[31] <> 31 then failwith "nth failure"
    if v2.[32] <> 32 then failwith "nth failure"
    if v3.[32] <> 1024 then failwith "nth failure"
    

    let s = [for i in 0 .. 500000 -> i]
    let v = PersistentVector.create(s)
    if v.Length <> 500001 then failwith ( "length failure : " + v.Length.ToString() )
    if v.[0] <> 0 then failwith "nth failure"
    if v.[31] <> 31 then failwith "nth failure"
    if v.[1000] <> 1000 then failwith "nth failure"
    if v.[5000] <> 5000 then failwith "nth failure"
    if v.[500000] <> 500000 then failwith "nth failure"
    
