module Numeric

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
open System.Numerics
open Rationals

[<CustomEquality; CustomComparison>]
type Numeric =
    | Int of Int32
    | Long of Int64
    | BigInt of BigInteger
    | Decimal of decimal
    | Rational of BigRational
    | Float of double
    with
        override this.GetHashCode()  = 
            match this with
            | Int(a) -> hash a
            | Long(a) -> hash a
            | BigInt(a) -> hash a
            | Decimal(a) -> hash a
            | Rational(a) -> hash a
            | Float(a) -> hash a

        member this.compare(o : Numeric) =
            match this with
            | Int(a) ->
                match o with
                | Int(b) -> compare a b
                | Long(b) -> compare (int64 a) b
                | BigInt(b) -> compare (BigInteger(a)) b
                | Decimal(b) -> compare (Convert.ToDecimal(a)) b
                | Rational(b) -> compare (BigRational.FromInt(a)) b
                | Float(b) -> compare (Convert.ToDouble(a)) b
            | Long(a) ->
                match o with
                | Int(b) -> compare a (int64 b)
                | Long(b) -> compare a b
                | BigInt(b) -> compare (BigInteger(a)) b
                | Decimal(b) -> compare (Convert.ToDecimal(a)) b
                | Rational(b) -> compare (BigRational.FromLong(a)) b
                | Float(b) -> compare (Convert.ToDouble(a)) b
            | BigInt(a) ->
                match o with
                | Int(b) -> compare a (BigInteger(b))
                | Long(b) -> compare a (BigInteger(b))
                | BigInt(b) -> compare a b
                | Decimal(b) -> compare (Convert.ToDecimal(a)) b
                | Rational(b) -> compare (BigRational.FromBigInt(a)) b
                | Float(b) -> compare (Convert.ToDouble(a)) b
            | Decimal(a) ->
                match o with
                | Int(b) -> compare a (Convert.ToDecimal(b))
                | Long(b) -> compare a (Convert.ToDecimal(b))
                | BigInt(b) -> compare a (Convert.ToDecimal(b))
                | Decimal(b) -> compare a b
                | Rational(b) -> compare (Convert.ToDouble(a)) (BigRational.ToDouble(b))
                | Float(b) -> compare (Convert.ToDouble(a)) b
            | Rational(a) ->
                match o with
                | Int(b) -> compare a (BigRational.FromInt(b))
                | Long(b) -> compare a (BigRational.FromLong(b))
                | BigInt(b) -> compare a (BigRational.FromBigInt(b))
                | Decimal(b) -> compare (BigRational.ToDouble(a)) (Convert.ToDouble(b))
                | Rational(b) -> compare a b
                | Float(b) -> compare (BigRational.ToDouble(a)) b
            | Float(a) ->
                match o with
                | Int(b) -> compare a (Convert.ToDouble(b))
                | Long(b) -> compare a (Convert.ToDouble(b))
                | BigInt(b) -> compare a (Convert.ToDouble(b))
                | Decimal(b) -> compare a (Convert.ToDouble(b))
                | Rational(b) -> compare a (BigRational.ToDouble(b))
                | Float(b) -> compare a b

        interface System.IComparable with
            member this.CompareTo(obj:obj) =
                match obj with
                | :? Numeric as o ->
                    this.compare(o)
                | _ -> failwith "Invalid comparison - Not a Numeric"

        override this.Equals(obj:obj) =
            match obj with
            | :? Numeric as o -> this.compare(o) = 0
            | _ -> false

 
        member this.ToDouble() =
            match this with
            | Int(n) -> Convert.ToDouble(n)
            | Long(n) -> Convert.ToDouble(n)
            | BigInt(n) -> Double.Parse(n.ToString())
            | Decimal(n) -> Convert.ToDouble(n)
            | Rational(r) -> BigRational.ToDouble(r) 
            | Float(n) -> n

        member this.ToDecimal() =
            match this with
            | Int(n) -> Convert.ToDecimal(n)
            | Long(n) -> Convert.ToDecimal(n)
            | BigInt(n) -> Decimal.Parse(n.ToString())
            | Decimal(n) -> n
            | Rational(r) -> Convert.ToDecimal(BigRational.ToDouble(r))
            | Float(n) -> Convert.ToDecimal(n)

        member this.ToInt() =
            match this with
            | Int(n) -> n
            | Long(n) -> int(n)
            | BigInt(n) -> int(n)
            | Decimal(n) -> Convert.ToInt32(n)
            | Rational(r) -> int(BigRational.ToBigInt(r))
            | Float(n) -> Convert.ToInt32(n)

        member this.ToLong() =
            match this with
            | Int(n) -> int64 n
            | Long(n) -> n
            | BigInt(n) -> int64(n)
            | Decimal(n) -> Convert.ToInt64(n)
            | Rational(r) -> int64(BigRational.ToBigInt(r))
            | Float(n) -> Convert.ToInt64(n)

        member this.ToBigInt() =
            match this with
            | Int(n) -> new BigInteger(n)
            | Long(n) -> new BigInteger(n)
            | BigInt(n) -> n
            | Decimal(n) -> new BigInteger(n)
            | Rational(r) -> BigRational.ToBigInt(r)
            | Float(n) -> new BigInteger(n)

        member this.ToRational() =
            match this with
            | Int(n) -> Rational(BigRational.FromBigInt(BigInteger(n)))
            | Long(n) -> Rational(BigRational.FromBigInt(BigInteger(n)))
            | BigInt(n) -> Rational(BigRational.FromBigInt(n))
            | Rational(r) -> this
            | Decimal(n) -> failwith "invalid conversion : Decimal to Rational"  // could do better here
            | Float(n) -> failwith "invalid conversion : Float to Rational"


        override this.ToString() =
            match this with
            | Int(n) -> n.ToString()
            | Long(n) -> n.ToString() 
            | BigInt(n) -> n.ToString() + "N"
            | Decimal(n) -> n.ToString() + "M"
            | Rational(r) -> r.ToString()
            | Float(n) -> n.ToString() + "f"

        static member Lift (o : obj) =
            match o with
            | :? int as i -> Int(i)
            | :? int64 as i -> Long(i)
            | :? BigInteger as i -> BigInt(i)
            | :? Decimal as d -> Decimal(d)
            | :? BigRational as r -> Rational(r)
            | :? Double as f -> Float(f)
            | :? Single as f -> Float(float f)
            | _ -> failwith "unable to Lift"
        
        static member Parse (s : string) =
            if   s.EndsWith("f") then Float(System.Double.Parse(s.Replace("f","")))
            elif s.EndsWith("M") then Decimal(System.Decimal.Parse(s.Replace("M","")))
            elif s.EndsWith("L") then Long(Int64.Parse(s.Replace("L","")))
            elif s.Contains(".") then Decimal(System.Decimal.Parse(s))
            elif s.Contains("N") then BigInt(BigInteger.Parse(s.Replace("N","")))
            elif s.Contains("/") then Rational(BigRational.Parse(s))
            else Numeric.ParseInt(s)

        static member ParseInt(s : string) =
            try
                Int(Int32.Parse(s))  
            with :? System.OverflowException ->
                try 
                    Long(Int64.Parse(s))
                with :? System.OverflowException -> 
                    BigInt(BigInteger.Parse(s))

        static member (+) (a : Numeric, b : Numeric) =
            match a,b with 
            | Int(a'),Int(b') -> 
                try
                    Int(Checked.(+) a' b')
                with _ ->
                    Long(int64 a') + Long(int64 b')
            | Long(a'),Long(b') -> 
                try
                    Long(Checked.(+) a' b')
                with _ ->
                    BigInt(BigInteger(a')) + BigInt(BigInteger(b'))
            | Long(a'),Int(b') -> 
                try
                    Long(Checked.(+) a' (int64 b'))
                with _ ->
                    BigInt(BigInteger(a')) + BigInt(BigInteger(b'))
            | Int(a'),Long(b') -> 
                try
                    Long(Checked.(+) (int64 a') b')
                with _ ->
                    BigInt(BigInteger(a')) + BigInt(BigInteger(b'))
            | BigInt(a'),BigInt(b') -> BigInt(a' + b')
            | BigInt(a'),Int(b') -> BigInt(a' + new BigInteger(b'))
            | BigInt(a'),Long(b') -> BigInt(a' + new BigInteger(b'))
            | Int(a'),BigInt(b') -> BigInt(new BigInteger(a') + b')
            | Decimal(a'),Decimal(b') -> Decimal(a' + b')
            | Decimal(a'),Int(b') -> Decimal(a' + Convert.ToDecimal(b'))
            | Decimal(a'),Long(b') -> Decimal(a' + Convert.ToDecimal(b'))
            | Decimal(a'),BigInt(b') -> Decimal(a' + Decimal.Parse(b'.ToString()))
            | Int(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') + b')
            | Long(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') + b')
            | BigInt(a'),Decimal(b') -> Decimal(Decimal.Parse(a'.ToString()) + b')
            | Rational(a'),Rational(b') -> Rational( a' + b')
            | Int(a'),Rational(b') -> a.ToRational() + b
            | Long(a'),Rational(b') -> a.ToRational() + b
            | BigInt(a'),Rational(b') -> a.ToRational() + b
            | Rational(a'),Int(b') -> a + b.ToRational()
            | Rational(a'),Long(b') -> a + b.ToRational()
            | Rational(a'),BigInt(b') -> a + b.ToRational()
            | _,_ -> Float(a.ToDouble() + b.ToDouble())
          
        static member (-) (a : Numeric, b : Numeric) =
            match a,b with 
            | Int(a'),Int(b') -> 
                try
                    Int(Checked.(-) a' b')
                with _ ->
                    Long(int64 a') - Long(int64 b')
            | Int(a'),Long(b') -> 
                try
                    Long(Checked.(-) (int64 a') b')
                with _ ->
                    Long(int64 a') - Long(int64 b')
            | Long(a'),Int(b') -> 
                try
                    Long(Checked.(-) a' (int64 b'))
                with _ ->
                    Long(int64 a') - Long(int64 b')
            | Long(a'),Long(b') -> 
                try
                    Long(Checked.(-) a' b')
                with _ ->
                    BigInt(BigInteger(a')) - BigInt(BigInteger(b'))
            | BigInt(a'),BigInt(b') -> BigInt(a' - b')
            | BigInt(a'),Int(b') -> // BigInt(a' - new BigInteger(b'))
                let i = BigInt(a' - new BigInteger(b'))
                if i < Int(Int32.MaxValue) then Int(i.ToInt()) 
                elif i < Long(Int64.MaxValue) then Long(i.ToLong()) 
                else i
            | Int(a'),BigInt(b') ->  // BigInt(new BigInteger(a') - b')
                let i = BigInt(new BigInteger(a') - b')
                if i < Int(Int32.MaxValue) then Int(i.ToInt()) 
                elif i < Long(Int64.MaxValue) then Long(i.ToLong()) 
                else i
            | Long(a'),BigInt(b') ->  // BigInt(new BigInteger(a') - b')
                let i = BigInt(new BigInteger(a') - b')
                if i < Long(Int64.MaxValue) then Long(i.ToLong()) else i
            | Decimal(a'),Decimal(b') -> Decimal(a' - b')
            | Decimal(a'),Int(b') -> Decimal(a' - Convert.ToDecimal(b'))
            | Decimal(a'),Long(b') -> Decimal(a' - Convert.ToDecimal(b'))
            | Decimal(a'),BigInt(b') -> Decimal(a' - Decimal.Parse(b'.ToString()))
            | Int(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') - b')
            | Long(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') - b')
            | BigInt(a'),Decimal(b') -> Decimal(Decimal.Parse(a'.ToString()) - b')
            | Rational(a'),Rational(b') -> Rational( a' - b')
            | Int(a'),Rational(b') -> a.ToRational() - b
            | Long(a'),Rational(b') -> a.ToRational() - b
            | BigInt(a'),Rational(b') -> a.ToRational() - b
            | Rational(a'),Int(b') -> a - b.ToRational()
            | Rational(a'),Long(b') -> a - b.ToRational()
            | Rational(a'),BigInt(b') -> a - b.ToRational()
            | _,_ -> Float(a.ToDouble() - b.ToDouble())
          
        static member (*) (a : Numeric, b : Numeric) =
            match a,b with 
            | Int(a'),Int(b') -> 
                try
                    Int(Checked.(*) a' b')
                with _ ->
                    Long(int64 a') * Long(int64 b')
            | Int(a'),Long(b') -> 
                try
                    Long(Checked.(*) (int64 a') b')
                with _ ->
                    Long(int64 a') * Long(int64 b')
            | Long(a'),Int(b') -> 
                try
                    Long(Checked.(*) a' (int64 b'))
                with _ ->
                    Long(int64 a') * Long(int64 b')
            | Long(a'),Long(b') -> 
                try
                    Long(Checked.(*) a' b')
                with _ ->
                    BigInt(BigInteger(a')) * BigInt(BigInteger(b'))
            | BigInt(a'),BigInt(b') -> BigInt(a' * b')
            | BigInt(a'),Int(b') -> BigInt(a' * new BigInteger(b'))
            | BigInt(a'),Long(b') -> BigInt(a' * new BigInteger(b'))
            | Int(a'),BigInt(b') -> BigInt(new BigInteger(a') * b')
            | Long(a'),BigInt(b') -> BigInt(new BigInteger(a') * b')
            | Decimal(a'),Decimal(b') -> Decimal(a' * b')
            | Decimal(a'),Int(b') -> Decimal(a' * Convert.ToDecimal(b'))
            | Decimal(a'),Long(b') -> Decimal(a' * Convert.ToDecimal(b'))
            | Decimal(a'),BigInt(b') -> Decimal(a' * Decimal.Parse(b'.ToString()))
            | Int(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') * b')
            | Long(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') * b')
            | BigInt(a'),Decimal(b') -> Decimal(Decimal.Parse(a'.ToString()) * b')
            | Rational(a'),Rational(b') -> Rational( a' * b')
            | Int(a'),Rational(b') -> a.ToRational() * b
            | Long(a'),Rational(b') -> a.ToRational() * b
            | BigInt(a'),Rational(b') -> a.ToRational() * b
            | Rational(a'),Int(b') -> a * b.ToRational()
            | Rational(a'),Long(b') -> a * b.ToRational()
            | Rational(a'),BigInt(b') -> a * b.ToRational()
            | _,_ -> Float(a.ToDouble() * b.ToDouble())
          
        static member (/) (a : Numeric, b : Numeric) =
            let rslt =
                match a,b with 
                | Rational(a'),Rational(b') -> Rational( a' / b')
                | Int(a'),Int(b') -> a.ToRational() / b.ToRational()
                | Long(a'),Int(b') -> a.ToRational() / b.ToRational()
                | Int(a'),Long(b') -> a.ToRational() / b.ToRational()
                | Long(a'),Long(b') -> a.ToRational() / b.ToRational()
                | BigInt(a'),BigInt(b') -> a.ToRational() / b.ToRational()
                | BigInt(a'),Int(b') -> a.ToRational() / b.ToRational()
                | BigInt(a'),Long(b') -> a.ToRational() / b.ToRational()
                | Int(a'),BigInt(b') -> a.ToRational() / b.ToRational()
                | Long(a'),BigInt(b') -> a.ToRational() / b.ToRational()
                | Int(a'),Rational(b') -> a.ToRational() / b
                | BigInt(a'),Rational(b') -> a.ToRational() / b
                | Rational(a'),Int(b') -> a / b.ToRational()
                | Rational(a'),Long(b') -> a / b.ToRational()
                | Rational(a'),BigInt(b') -> a / b.ToRational()
                | Int(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') / b')
                | Long(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') / b')
                | BigInt(a'),Decimal(b') -> Decimal(Decimal.Parse(a'.ToString()) + b')
                | Decimal(a'),Decimal(b') -> Decimal(a' / b')
                | Decimal(a'),Int(b') -> Decimal(a' / Convert.ToDecimal(b'))
                | Decimal(a'),Long(b') -> Decimal(a' / Convert.ToDecimal(b'))
                | Decimal(a'),BigInt(b') -> Decimal(a' / Decimal.Parse(b'.ToString()))
                | _,_ -> Float(a.ToDouble() / b.ToDouble())
            match rslt with
            | Rational(r) -> 
                if r.Denominator = BigInteger(1) then 
                    let i = r.Numerator 
                    if i < BigInteger(Int32.MaxValue) then Int(int32 i)
                    elif i < BigInteger(Int64.MaxValue) then Long(int64 i)
                    else BigInt(i)
                else rslt
            | _ -> rslt

          
        static member (%) (a : Numeric, b : Numeric) =
            match a,b with 
            | Int(a'),Int(b') -> Int(a' % b')
            | BigInt(a'),BigInt(b') -> BigInt(a' % b')
            | BigInt(a'),Int(b') -> BigInt(a' % new BigInteger(b'))
            | Int(a'),BigInt(b') -> BigInt(new BigInteger(a') % b')
            | Decimal(a'),Decimal(b') -> Decimal(a' % b')
            | Decimal(a'),Int(b') -> Decimal(a' % Convert.ToDecimal(b'))
            | Decimal(a'),BigInt(b') -> Decimal(a' % Decimal.Parse(b'.ToString()))
            | Int(a'),Decimal(b') -> Decimal(Convert.ToDecimal(a') % b')
            | BigInt(a'),Decimal(b') -> Decimal(Decimal.Parse(a'.ToString()) % b')
            | _,_ -> failwith "modulo (%) not supported " //Float(a.ToDouble() % b.ToDouble())

