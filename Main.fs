open IncTypes
open Inc
open Repl
Builtins.init()


open Test
load "\\dev\\Inc\\Prelude.inc"

Globals.DefaultNS <- Namespace("user")

test ()

repl "Welcome to INC (INC's Not Clojure, Interpreted Not Compiled)"