Title: A Gentle Adventure Mechanising Message Passing Concurrency Systems

A play in three acts.


Act I: Binary Session Types (with a deeply embedded representation).

In the first part we discuss the implementation of binary session
types and a deeply embedded process calculus. We discuss a simple
session calculus, strategies to represent binders, and use Locally
Nameless through our EMTST tool to implement some metatheory about
it.


Act II: Smol-Zooid: multiparty with shallower embedding.

In the second part, we discuss how to avoid problems with binders, by
using a mixed deep/shallow embedding. We present Smol-Zooid, a process
calculus for multiparty computations, its semantics and a typing
relation that associates processes with their concurrent behaviour.


Act III: Processes and coinduction, properties of Smol-Zooid's global types.

In its third part, the tutorial will show how we have formalised
communication discipline in Coq: we will discuss how we get semantics
guarantees from multiparty session types. Global and local types are
coinductively described in Coq, and, through labelled transition
systems, we show that execution traces for processes are subtraces of
the global protocol ones.

Discussed topics: understanding of basic session types, implementing
shallow and deep embeddings in Coq, learning how to use locally
nameless (and EMTST), how to mechanise metatheory of session types
(both binary and multiparty), and using coinduction for semantic
representation of communication systems.
