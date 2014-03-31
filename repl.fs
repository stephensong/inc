module Repl

open IncTypes
open Inc
open System
open Utils

let prn v = print v

let prep env =
    List.ofSeq >> parse "__REPL__" >> List.head >> (eval id env) >> prn

let rep env =
    let eval' e =
        try eval id env e
        with ex ->  Dummy("Exception : " + ex.Message) |> e2v
    List.ofSeq >> parse "__REPL__" >> List.head >> eval' >> prn

let rec readFormFromConsole(rem) =
    let s = rem + Console.ReadLine()
    let mutable i = 0
    while i < s.Length && Char.IsWhiteSpace(s.[i]) do i <- i + 1
    let ti = i
    if s.[i].In( [ '{'; '['; '(' ] ) then
        let rec readRest (s : string) =
            let j = findBalancer s.[ti] s ti
            if j > 0 then
                if j = s.Length - 1 then s            
                else
                    s.Substring(0,j) |> rep [] |> printf "%s\n"
                    readFormFromConsole(s.Substring(j+1)) 
            else readRest (s + "\n" + Console.ReadLine())
        readRest s
    else s

let rec repl output =
    printf "%s\n%s=> " output Globals.DefaultNS.Name
    readFormFromConsole("") |> rep [] |> repl



