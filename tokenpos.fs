module tokens

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


open System

type Token =
    | Nil
    | True | False
    | Open | Close
    | OpenVector | CloseVector
    | OpenDict | CloseDict
    | OpenSet
    | Quote | Unquote | SyntaxQuote | SpliceUnquote
    | Number of string
    | Char of char
    | String of string
    | Symbol of string
    | Keyword of string
    | TagTok of string

type TokenPos = { tok : Token; startpos : int; startline : int; startcol : int; endpos : int; endline : int; endcol : int }

let tokenize source =
    let line = ref 1
    let col = ref 0
    let pos = ref 0
    let nOpen = ref 0
    let nOpenVect = ref 0
    let nOpenDict = ref 0
    let tp t  = 
        {tok = t; startpos = !pos; startline = !line; startcol = !col; endpos = !pos; endline = !line; endcol = !col}
    let tlc(t, p, l, c) = 
        {tok = t; startpos = p; startline = l; startcol = c; endpos = !pos; endline = !line; endcol = !col}
    let r n =
        col := !col + n
        pos := !pos + n
    let nl() = 
        incr line
        col := 0
        incr pos
    let decref r = 
        decr r
        if !r < 0 then failwith (sprintf "Unbalanced delimiters at line %i, col %i " !line !col)
    let rec string acc = function
        | '\\' :: '"' :: t -> r 2; string (acc + "\"") t // escaped quote becomes quote
        | '\\' :: 'b' :: t -> r 2; string (acc + "\b") t // escaped backspace
        | '\\' :: 'f' :: t -> r 2; string (acc + "\f") t // escaped formfeed
        | '\\' :: 'n' :: t -> r 2; string (acc + "\n") t // escaped newline
        | '\\' :: 'r' :: t -> r 2; string (acc + "\r") t // escaped return
        | '\\' :: 't' :: t -> r 2; string (acc + "\t") t // escaped tab
        | '\\' :: '\\' :: t -> r 2; string (acc + "\\") t // escaped backslash
        | '"' :: t -> r 1; acc, t // closing quote terminates
        | '\n' :: t -> nl(); string (acc + ("\n")) t // skip whitespace
        | c :: t -> r 1; string (acc + (c.ToString())) t // otherwise accumulate chars
        | _ -> failwith "Malformed string."
    let rec comment = function
        | '\n' :: t -> nl(); t // terminated by line end
        | [] -> [] // or by EOF
        | _ :: t -> r 1; comment t
    let rec token acc = function
        | ('(' :: _) as t -> acc, t 
        | ('[' :: _) as t -> acc, t  
        | ('{' :: _) as t -> acc, t  
        | (')' :: _) as t -> acc, t // closing paren terminates
        | (']' :: _) as t -> acc, t  
        | ('}' :: _) as t -> acc, t  
        | w :: t when Char.IsWhiteSpace(w) -> r 1; acc, t // whitespace terminates
        | (',' :: _) as t -> acc, t
        | [] -> acc, [] // end of list terminates
        | c :: t -> r 1; token (acc + (c.ToString())) t // otherwise accumulate chars
    let rec tokenize' acc = function
        | '\n' :: t -> nl(); tokenize' acc t // skip whitespace
        | w :: t when Char.IsWhiteSpace(w) -> r 1; tokenize' acc t // skip whitespace
        | ',' :: t -> r 1; tokenize' acc t // commas are whitespace
        | '(' :: t -> let tk = tp(Open) in r 1; incr nOpen; tokenize' (tk :: acc) t
        | ')' :: t -> let tk = tp(Close) in r 1 ; decref nOpen; tokenize' (tk :: acc) t
        | '[' :: t -> let tk = tp(OpenVector) in r 1; incr nOpenVect; tokenize' (tk :: acc) t
        | ']' :: t -> let tk = tp(CloseVector) in r 1; decref nOpenVect; tokenize' (tk :: acc) t
        | '{' :: t -> let tk = tp(OpenDict) in r 1; incr nOpenDict; tokenize' (tk :: acc) t
        | '}' :: t -> let tk = tp(CloseDict) in r 1; decref nOpenDict; tokenize' (tk :: acc) t
        | '#' :: '{' :: t -> let tk = tp(OpenSet) in r 2; incr nOpenDict; tokenize' (tk :: acc) t
        | '#' :: '\'' :: t -> 
            let tl,tc,tpos = !line,!col,!pos
            let tkc = tp(Close)
            let tko = tp(Open)
            r 2; 
            let s, t' = token "" t
            tokenize' (tkc :: tlc(Token.String(s),tpos,tl,tc) :: tlc(Token.String("var"),tpos,tl,tc) :: tko :: acc) t'
        | '\'' :: t -> let tk = tp(Quote) in r 1; tokenize' (tk :: acc) t
        | '~' :: '@' :: t -> let tk = tp(SpliceUnquote) in r 2; tokenize' (tk :: acc) t
        | '~' :: t -> let tk = tp(Unquote) in r 1; tokenize' (tk :: acc) t
        | '`' :: t -> let tk = tp(SyntaxQuote) in r 1; tokenize' (tk :: acc) t
        | '@' :: t -> 
            let tl,tc,tpos = !line,!col,!pos
            let tkc = tp(Close)
            let tko = tp(Open)
            r 1 
            let s, t' = token "" t
            tokenize' (tkc :: tlc(Token.Symbol(s),tpos,tl,tc) :: tlc(Token.Symbol("deref"),tpos,tl,tc) :: tko :: acc) t'
        | ';' :: t -> r 1; comment t |> tokenize' acc // skip over comments
        | '"' :: t -> // start of string
            let tl,tc,tpos = !line,!col,!pos
            r 1 
            let s, t' = string "" t
            tokenize' (tlc(Token.String(s),tpos,tl,tc) :: acc) t'
        | '#' :: '"' :: t -> // start of regex
            let tl,tc,tpos = !line,!col,!pos
            let tkc = tp(Close)
            let tko = tp(Open)
            r 2 
            let s, t' = string "" t
            tokenize' (tkc :: tlc(Token.String(s),tpos,tl,tc) :: tlc(Token.Symbol("re-pattern"),tpos,tl,tc) :: tko :: acc) t'
        | '-' :: d :: t when Char.IsDigit(d) -> // start of negative number
            let tl,tc,tpos = !line,!col,!pos
            r 2 
            let n, t' = token ("-" + d.ToString()) t
            tokenize' (tlc(Token.Number(n),tpos,tl,tc) :: acc) t'
        | '+' :: d :: t when Char.IsDigit(d)   -> // start of positive number
            let tl,tc,tpos = !line,!col,!pos
            r 2 
            let n, t' = token (d.ToString()) t
            tokenize' (tlc(Token.Number(n),tpos,tl,tc) :: acc) t'   
        | d :: t when Char.IsDigit(d) -> // start of positive number
            let tl,tc,tpos = !line,!col,!pos
            r 1
            let n, t' = token (d.ToString()) t
            tokenize' (tlc(Token.Number(n),tpos,tl,tc) :: acc) t'   
        | ':' :: t ->
            let tl,tc,tpos = !line,!col,!pos
            r 1
            let s, t' = token "" t
            tokenize' (tlc(Token.Keyword(s),tpos,tl,tc) :: acc) t'
        | '^' :: t ->   // metadata
            let tl,tc,tpos = !line,!col,!pos
            r 1
            match t with
            | '{' :: _ ->
                tokenize' (tlc(Token.TagTok("^"),tpos,tl,tc) :: acc) t
            | _ -> 
                let s, t' = token "" t
                let tkc = tp(CloseDict)
                let tko = tp(OpenDict)
                tokenize' (tkc :: tlc(Token.String(s),tpos,tl,tc) :: tlc(Token.Keyword("tag"),tpos,tl,tc) :: tko :: tlc(Token.TagTok("^"),tpos,tl,tc):: acc) t'
        | '#' :: '(' :: t ->
            let tl,tc,tpos = !line,!col,!pos
            nOpen := !nOpen + 1
            r 2
            tokenize' (tp(Open) :: tlc(Token.TagTok("__implicit_function__"),tpos,tl,tc) :: acc) t
        | '#' :: '_' :: t ->
            let tl,tc,tpos = !line,!col,!pos
            r 2
            tokenize'  (tlc(Token.TagTok("__ignore__"),tpos,tl,tc) :: acc) t
        | '#' :: t ->
            let tl,tc,tpos = !line,!col,!pos
            r 1
            let s, t' = token "" t
            tokenize' (tlc(Token.TagTok(s),tpos,tl,tc) :: acc) t'
        | '\\' :: t ->
            let tl,tc,tpos = !line,!col,!pos
            let c,t' = 
                match t with
                | 'n' :: 'e' :: 'w' :: 'l' :: 'i' :: 'n' :: 'e' :: t' -> 
                    r 7
                    '\n',t'
                | 's' :: 'p' :: 'a' :: 'c' :: 'e' :: t' -> 
                    r 5
                    ' ',t'
                | 't' :: 'a' :: 'b' :: t' -> 
                    r 3
                    '\t',t'
                | 'f' :: 'o' :: 'r' :: 'm' :: 'f' :: 'e' :: 'e' :: 'd' :: t' -> 
                    r 8
                    '\f',t'
                | 'b' :: 'a' :: 'c' :: 'k' :: 's' :: 'p' :: 'a' :: 'c' :: 'e' :: t' -> 
                    r 9
                    '\b',t'
                //todo: unicode, octals
                | h :: t' ->
                    r 1
                    h,t'
                | _ -> failwith "????"
            tokenize' (tlc(Token.Char(c),tpos,tl,tc) :: acc) t'
        | s :: t -> // otherwise start of symbol
            let tl,tc,tpos = !line,!col,!pos
            r 1
            let s, t' = token (s.ToString()) t
            tokenize' (tlc(Token.Symbol(s),tpos,tl,tc) :: acc) t'
        | [] -> 
            if !nOpen > 0 || !nOpenVect > 0 || !nOpenDict > 0 then
                failwith "Unbalanced delimiters"
            List.rev acc // end of list terminates
    tokenize' [] source


