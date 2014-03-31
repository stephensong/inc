INC's Not Clojure
=================

This is INC, my own little experimental and ridiculously naive implementation of a Clojure-like language implemented in F#, these being hands down my two favourite programming languages (with F# still a clear preference over Clojure.)

INC is directly based on the awesome Fscheme from Ashley Feniello.  
(See http://blogs.msdn.com/b/ashleyf/archive/tags/fscheme/)

I'm sort of stuck with this project, and doubt that it is really worth investing much more time in, given that there is already a perfectly decent implementation of Clojure for the CLR, and that I am already a bit out of my depth with it.  I was originally hoping to use it to try to build a bridge to Datomic from f# / .net, but I now think that's probably a silly idea.

What might work (probably, .. possibly :):
-----------------------------

- Vectors.  (The first thing I did and the most satisfying)
- Macros.  (A pretty fair rendition of Clojure even if I do say so myself :)
- Lazy-seq's.  (Ditto.)
- Stm.  (Not really tested though.  All I did really was include an f# implementation I found on the interwebs.)
- Agents/Refs/Atoms.  (Again not really tested)
- Interop with .NET code


What definitely doesn't work.
-----------------------------

- Namespaces.  (very basic support only)
- Protocols / Datatypes (not implemented)
- Transients.

.. and much, much more. 

Personal Details.
-----------------

My name is Gary Stephenson.  I live in Sydney, Australia.

I am pushing 60 these days, and have been programming on and off for forty odd years, yet still find myself obsessed with it, and constantly disappointed with how badly I still suck at it.

My email is gary@oxide.net.au.  I am not currently employed, and may be interested in paid work involving either F# or Clojure (which is really the only reason I am publishing this code at all).


Licensing.
----------

Given that most of the macros in the prelude are slightly tweaked versions of those found in Clojure/core.clj, I guess it is beholden on me to go with the EPL a la Clojure itself.
