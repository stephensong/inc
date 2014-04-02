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
- Stm/Refs.  (Not really tested though.  All I did really was include an f# implementation I found on the interwebs.)
- Agents/Atoms.  (Again not really tested)
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

I am pushing 60 these days, and have been programming on and off for forty odd years, yet still find myself obsessed with it, and constantly disappointed with how badly I still suck at it (although I take some comfort in not being alone in this regard!).

My email is gary@oxide.net.au.  I am not currently employed, and may be interested in paid work involving either F# or Clojure (which is really the only reason I am publishing this code at all).


License.
----------

See individual files.

If not provided there, then in general :

  Copyright (c) 2014, Gary Stephenson
  All rights reserved.
  
  Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
  1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer. 
  2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution. 
  3. Neither the name of the author nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission. 
  
  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  
