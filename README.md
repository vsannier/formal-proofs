This repository collects formal proofs and mechanised metatheory developed
with [Metamath](https://us.metamath.org/),
[Coq](https://coq.inria.fr/), and [Lean](https://lean-lang.org/).

It also contains various scripts for tasks such as listing theorems
in a Metamath database, shortening proofs, showing repetitions, etc.
(see also <https://github.com/metamath/set.mm/tree/develop/scripts>),
and a syntax file `misc/metamath.sublime-syntax`
for use with text editors or typesetting programs
like [Typst](https://typst.app/docs/reference/text/raw/).

**Contributions are welcome.**

Other Metamath databases can be found
[here](https://github.com/metamath/set.mm/blob/develop/other-databases.md).

## Logics

| Logic/Theory            | File                           | Example theorem                                                   |
|-------------------------|--------------------------------|-------------------------------------------------------------------|
| Natural deduction (NJ)  | [`nj.mm`](src/nj.mm)           | $\Gamma \vdash (\phi \land \psi) \to (\phi \lor \phi)$ (`animor`) |
| SKI combinator calculus | [`ski.mm`](src/ski.mm)         | $\vdash \mathrm{Y}(f) \downarrow f(\mathrm{Y}(f))$ (`fix`)        |
| Four-term analogies     | [`analogy.mm`](src/analogy.mm) | $\vdash a \mathbin{:} a \mathrel{::} b \mathbin{:} b$ (`id`)      |

(Please note that these databases have *not* been used extensively,
and may therefore be incomplete or even unsound implementations
of the above theories.)

## Plurimetric Fuzz

[`PlurimetricFuzz.v`](src/Plurimetric%20Fuzz/PlurimetricFuzz.v) is a partial
formalisation of the metatheory of the deterministic fragment
of Plurimetric Fuzz, from Patrick Baillot and my FSCD 2024 paper.
See the [development's README](src/Plurimetric%20Fuzz/README.md) for details.

## Anki cloze deletions

[`Cloze.lean`](src/cloze/Cloze.lean) formalises
[Anki cloze deletions](https://docs.ankiweb.net/editing.html#cloze-deletion).
