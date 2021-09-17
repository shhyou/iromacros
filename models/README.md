Hygienic Macro System: Redex Models
=====
## `macro-subst.rkt`: Syntactic Closures and Macros That Work

A small-step semantics Redex model of a simple hygienic macro system.
The model is a slight modification of the macro model presented by
W. Clinger and J. Rees in the paper **Macros That Work**.

This Redex model is built on top of the binding forms, designed by Stansifer,
to emphasis the binding aspect of the environments and hide the mechanical
refreshening of variables behind the scenes.

Additionally, the metafunctions `transcribe`, `match` and `rewrite*` are called
`T`, `matches` and `substitute*` in this model. Their signature also differ from
the paper in that the environments are paired with the syntaxes to signify
that the syntaxes must be interpreted under some environment.

Side note. To expand the collapsed S-expressions (`(...)`), copy the
elided forms to the definition window or the prompt area of the REPL and
select "Expand S-expression" from the context menu.

1.  William Clinger and Jonathan Rees. **Macros That Work**. In _POPL'91_.
    <https://doi.org/10.1145/99583.99607>

2.  Paul Stansifer and Mitchell Wand. **Romeo: A System for More Flexible
    Binding-Safe Programming**. In _ICFP'14_.
    <https://doi.org/10.1145/2628136.2628162>

3.  Klein et al., **Run Your Research: On the Effectiveness of Lightweight
    Mechanization**. In _POPL'12_.
    - <https://doi.org/10.1145/2103656.2103691>
    - <https://docs.racket-lang.org/redex/index.html>
