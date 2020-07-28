# Imper on IAL

*Reasoning about the Imper language using the Iowa Agda Library for Reed's CSCI 384*

This repo contains my Agda code for reasoning about a simple imperative language,
similar in style to what's done in Coq at the end of Pierce et al's Software 
Foundations Volume 1 and at the beginning of Volume 2. The main files are those
of the form `imper*.agda`. The remaining bulk of the repo's contents is the result
of my forking of the [Iowa Agda Library repo](https://github.com/cedille/ial)
developed by [Aaron Stump](http://homepage.cs.uiowa.edu/~astump/) and his research group.
I'm making a small addition, modeling the Imper language, that builds on their stuff, and
I am grateful to have access to their code.

My goal with this code is to develop a two-week program verification module for the Reed
CS course [**CSCI 384: Programming Languages**](https://jimfix.github.io/csci384/index.html)
I've chosen to use IAL, rather than the Agda standard library, because it is a bit more
compact, and the parts I rely on are much more self-contained. The code is given a very clear and concise
treatment in his text
[*Verified Functional Programming Agda*](https://www.amazon.com/Verified-Functional-Programming-Agda-Books/dp/1970001240).
If you are new to Agda and verification and have seen some functional programming (e.g. in Haskell), I recommend this text as
a good introduction.

### Week 1: Program Semantics in Agda

My goal here is to build off the ML coding of parsers and interpreters we perform in the first weeks of the semester, and
the large step semantics we develop in the next few weeks. Agda allows us to actually code up both (parser+interpreter and the 
mathematical semantics) and prove that they do the same thing. My hope is that this, along with a brief overview of what's in 
the IAL, will be a nice week-long introduction to Agda and dependently typed languages. 

In this first part, we define in Agda what it means to run an Imper program within the context of a frame of variables. This frame
gets modified by program statements, and so a frame is the state of an Imper program's execution. Imper statements include branches and
loops. These act according to conditions on the frame. These are expressed as logical operations over variable comparisons. For example

    [ x < y + 5 ] ^ [z == x - 1] v [ z == 0 ]

could be a condition. 

### Week 2: Hoare Logic

My second goal, after re-introducing the semantics of Imper, is to introduce Hoare triples and logical reasoning about program properties. When this goal is met,
hopefully I'll have a way of deducing formulae over frames. The hope is that, in Agda, the students can perform reasoning like:

    { [x > 5] ^ [y == 2] } x ::= x+y { [x > 7] }
    
They would do this using an engine that reasons about arithmetic and comparison of variable expressions over the natural numbers.

This second component, on Hoare logic, would be covered in a second week of the course. 

### Thanks

Many thanks go to [Henry Blanchette](https://github.com/Riib11) and [Eli Poppele](https://github.com/poppele) who developed this with me during the Summer of 2020.
Their work was funded by The Crandall Research Fund.

