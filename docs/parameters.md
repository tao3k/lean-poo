# Object syntax and positional specialization

## Construction grammar

The leading option prefix of `.o` is now:

```scheme
(.o self: receiver super: inherited inherit: (list parent ...)
    bind: (imported-slot ...) bind-these: #f
    (slot expression) ...)
```

All options are optional. `self:` names final self; `super:` names the ZERO-ARGUMENT
inherited computation for the current slot. It is the paper's `$slot-gen` inherit
thunk (Racket essay lines 419–434), not a reified super-instance or an arbitrary
parent slot lookup. `inherit:` is the ordinary C3 parent-list expression, evaluated
by the existing constructor. `bind:` imports explicit slot identifiers.
`bind-these:` is a literal Boolean (default `#t`) controlling automatic lexical
binding of this construction's declared/default slot names independently of those
imports. Unselected lexical names retain their surrounding Scheme bindings.

The prefix ends at the first ordinary slot form. Reserved option names can still
be declared as parenthesized slots, e.g. `(self 'data)`. Existing `(:: self parents
slots ...)`, ordinary keyword slots, shorthand capture, defaults, inherited next
names and `.o` match patterns retain their existing semantics. Repeated options,
invalid identifiers/import lists, nonliteral flags and self/super binding conflicts
refuse at expansion. Explicit per-slot next names and `super:` alias the same
existing delayed computation. All forms lower through one normalizer and existing
`object/init`; no alternate object representation, cache or inheritance engine is
introduced. Parent/slot Type errors remain the ordinary engine's errors.

## Persistent positional prefixes

Import `parameters` with a prefix and declare `.parameters` as an ordered proper
list of unique symbols, excluding `.parameters` itself. `(parameters.specialize
prototype argument ...)` binds a prefix using `.cc`, returning a receiver with the
remaining suffix in `.parameters`. Repeating partial specialization has the same final bindings as a single
concatenated specialization for extensional formulas; fresh receiver identities
and allocation traces are not equated. A closed receiver has an empty list; zero
arguments preserve receiver identity, after metadata validation. Malformed names
or excess values refuse before cloning; false/empty/procedure values remain data.
Remaining list spines are copied. Direct computed formulas use the NEW final self;
previous prototypes/partial receivers retain their own fields and caches.

Specialization does not invoke instantiation hooks, validate arbitrary values or
perform consumer effects. Complete receivers pass through the existing Type or
ObjectContract boundary before consumption. Parent/callback metadata must obey
ordinary supported mutation and invalidation discipline; this is not deep freezing
of source objects or arbitrary values, automatic dependency discovery, or a new
subtyping/type-inference system.

## Generic formals and complete chain

`.defgeneric` already delegated optional positional/keyword/default/rest handling
to Gerbil and `support/syntax.call<-formals`; its old TODO was stale. The acceptance
suite now exercises omitted and explicit-false values, dependent defaults evaluated
once/in lexical order, supplied defaults not evaluated, keyword/rest forwarding,
from:type exact receiver forwarding, method combination and missing-slot defaults.
Genuine method-body errors propagate. This does not add optional/keyword signatures
to the separate `Fun` Type descriptor language or arbitrary case-lambda overloads;
those remain in the type-system workstream.

`examples/parameter-service.ss` combines a C3 diamond with one shared base fee,
lexical region imports, explicit self/super names, partial/full `.parameters`
binding, default/keyword/rest generic calls, final-self recomputation and a checked
Reader/FUN action. Shape/type checks gate arithmetic/refinement and effects;
refusal never reaches the consumer, while successful multiple values are retained.
A capacity/tariff prefix 10/3 gives fee 11, total 41 and two-unit quote 82; independent
partial contexts and later clones retain the correct receiver semantics.

Lean `Functional.Parameters` proves thirteen pure laws: empty identity, excess
refusal, remaining suffix, prefix composition, incremental specialization equality,
unwritten-field preservation, invalid declaration refusal, valid suffix admission,
checked incremental equality, exact lexical binding membership, inherited-alias
lowering and supplied/absent optional selection. The actual fixture uses the
existing `Prototype.Method` delayed/final-self model. These are semantic laws for
normalized constructs, not a proof of the Gerbil macro expander, Scheme callback
termination, GC, compiler or runtime. Expansion/hygiene, exceptions, keyword syntax,
multiple values and effect/default ordering are separate executable controls.

This closes the declared syntax/positional-specialization TODO workstream. The
keyword surface and positional API develop the paper's extensible-prototype future
work; they are not claimed as literal APIs in its Racket implementation. General
polymorphism/inference, typed optional `Fun` signatures, layout/cache protocols,
collections and interpreter projects remain open. Scheme has no Lean dependency.
