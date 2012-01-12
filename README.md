# Core Language Compiler

Core Language from Simon Peyton Jones' book [Implementing functional languages: a tutorial](http://research.microsoft.com/en-us/um/people/simonpj/papers/pj-lester-book/)

I mostly wanted to do this because I can more or less understand how I'd implement either a C-like language or LISP like language in terms of another language i.e. writing the implementation in Python or Scheme or something. But I wanted to know how a compiler would work for that like Haskell's ghc. So I figure this should tell me.

And there's no answers to exercises so I actually have to work it out :)

### Possible Exercises After It's Done

* Writing the Parser as a monad
* Write Pratt Parser
* Use Haskell parser module Parsec
* Add data constructors like Haskell (instead of the Pack{1,2} stuff) \*NM I understand now. Supercomb = Pack{tag, arity} makes sense now. But it would still be cool to learn how to implement ADTs and stuff but I'll probably just look it up in ghc
* Type checking
* I *think* the entire compiler can be written as a state monad... when I finish chapter 2 maybe I'll look into that
