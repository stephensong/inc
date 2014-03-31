module Bencode

open System
open System.IO
open System.Text
open Utils

[<CustomEquality; CustomComparison>]
type Value =
    | Bytes of byte[]
    | Int of int64
    | List of Value list
    | Dictionary of Map<Value,Value>
    with
        override this.ToString() =
            let print x = x.ToString()
            match this with
            | Bytes s -> Encoding.UTF8.GetString(s)
            | Int i -> "i" + i.ToString() + "e"
            | List l ->
                let sb = StringBuilder() 
                l |> List.iter (fun v -> sb.Append(v.ToString()) |> ignore) 
                "l" + sb.ToString() + "e"
            | Dictionary(dict) ->  
                let prs = [for KeyValue(k,v) in dict -> (print k) + (print v)]
                "d" + String.Join(", ", prs) + "e"

        override this.GetHashCode() =
            match this with
            | Bytes bs -> hash bs
            | Int i -> comb 2 (hash i)
            | List l -> comb 5 (hash l)
            | Dictionary d -> comb 7 (hash d)

        override this.Equals(o) =
            match o with
            | :? Value as o ->
                match this,o with
                | Bytes(a), Bytes(b) -> bytesEqual a b
                | Int(a), Int(b) -> a = b 
                | List(a), List(b) -> a = b
                | Dictionary(a), Dictionary(b) -> a = b
                | _,_ -> false
            | _ -> false

        interface System.IComparable with
            member this.CompareTo yobj =
                match yobj with
                | :? Value as b ->
                    match this, b with
                    | Bytes(a), Bytes(b) ->  compareBytes a b
                    | Int(a), Int(b) -> compare a b 
                    | List(a), List(b) -> compare a b
                    | Dictionary(a), Dictionary(b) -> compare a b
                    | _,_ when this = b -> 0 
                    | Bytes(_),_ -> -1
                    | _,Bytes(_) -> 1
                    | Int(_),_ -> -1
                    | _,Int(_) -> 1
                    | List(_),_ -> -1
                    | _,List(_) -> 1
                    | Dictionary(_),_ -> -1
                    | _,Dictionary(_) -> 1
                    | _,_ -> failwith "Unable to compare"
                | _ -> invalidArg "yobj" "cannot compare values of different types"


let Decode s =
  let p : BytesParser = BytesParser(s)
  let rec decode()  =
    let c = char(p.Head)
    match c with
    | d when Char.IsDigit(d) ->
        let s = p.Cut(byte(':'))
        let i = Int32.Parse(ASCIIEncoding.ASCII.GetString(s))
        Bytes (p.Read(i))
    | 'i' ->
        p.Skip(1)
        let s = p.Cut(byte('e'))
        Int (Int64.Parse(ASCIIEncoding.ASCII.GetString(s)))
    | 'l' ->
        p.Skip(1)
        let rec iter l =
            match char(p.Head) with
            | 'e' -> List (List.rev l)
            | _ ->
                let v = decode()
                iter (v :: l)
        iter []
    | 'd' ->
        p.Skip(1)
        let rec iter l =
          match char(p.Head) with
            | 'e' -> Dictionary (Map l)
            | _ ->
                match decode() with
                | Bytes key ->
                    let v = decode() 
                    iter ((Bytes key,v) :: l)
                | _ -> failwith "Parser corrupt" 
        
        iter []
    | _ -> failwith "Parser corrupt" 
  
  let v = decode()
  v

let Encode (v : Value) =
  use buf = new MemoryStream()
  let enc_bytes (s : byte[]) = 
      let bs = Encoding.ASCII.GetBytes(s.Length.ToString())
      buf.Write(bs, 0, bs.Length)
      buf.WriteByte(byte(':'))
      buf.Write(s, 0, s.Length)
  let rec encode v =
      match v with
      | Bytes s ->  enc_bytes s
      | Int i -> 
          let s = "i" + i.ToString() + "e"
          let bs = Encoding.ASCII.GetBytes(s)
          buf.Write(bs,0,bs.Length)
      | List l ->
          buf.WriteByte(byte('l'));
          List.iter encode l;
          buf.WriteByte(byte('e'))
      | Dictionary l ->
          buf.WriteByte(byte('d'));
          l |> Seq.iter (fun kvp -> 
                           match kvp.Key with
                           | Bytes key ->enc_bytes key; encode v
                           | _  -> failwith "corrupt dictionary"
                         ) 
          buf.WriteByte(byte('e'));
  encode v
  buf.ToArray()

let StringToValue (s : string) =  Bytes (Encoding.UTF8.GetBytes(s))
let ValueToString (v : Value) = 
    match v with
    | Bytes s -> Encoding.UTF8.GetString( s )
    | _ -> failwith "Not a byte string"

let test v =
   let e = Encode v
   let v2 = Decode e
   let e2 = Encode v2
   if not(bytesEqual e2 e) then failwith "Encode fail"
   if v2 <> v then failwith "Equality fail"
  
  
let testThrows s =
   let mutable ok = true
   try 
       StringToValue s |> ignore
   with _ -> 
       ok <- false
   if ok then failwith ("Throws failure : '" + s  )


let runtests() =
    let s = @"[1,2,3,4,
""a"", ""b"", ""c"",
{""foo"": ""bar"", ""core"": ""dump""},
true, false, true, true, null, false
]"
    
    test (StringToValue(s))
    test (Int 2131234L)

    let bs = Encoding.UTF8.GetBytes("d3:bar4:spam3:fooi42ee")
    let v = Decode bs
    match v with
    | Dictionary map ->
        if map.Count <> 2 then failwith "count not 2"
        if not(map.ContainsKey(StringToValue "bar")) then failwith "missing key 'bar'"
        if not(map.[StringToValue "bar"] = StringToValue("spam")) then failwith "value for key 'bar' not 'spam'"
        if not(map.ContainsKey(StringToValue "foo")) then failwith "missing key 'foo'"
        if not(map.[StringToValue "foo"] = (Int 42L)) then failwith "value for key 'foo' not 42"
    | _ -> failwith "Not a dict" 
    printfn "Bencode tests all passed"