<img align="center" width="120" src="https://us.metamath.org/mmlogotitle.svg">

This repository contains
the following [Metamath](https://us.metamath.org/) databases:

| Logic/Theory            | File                           | Example theorem                                                   |
|-------------------------|--------------------------------|-------------------------------------------------------------------|
| Natural deduction (NJ)  | [`nj.mm`](src/nj.mm)           | $\Gamma \vdash (\phi \land \psi) \to (\phi \lor \phi)$ (`animor`) |
| SKI combinator calculus | [`ski.mm`](src/ski.mm)         | $\vdash \mathrm{Y}(f) \downarrow f(\mathrm{Y}(f))$ (`fix`)        |
| Four-term analogies     | [`analogy.mm`](src/analogy.mm) | $\vdash a \mathbin{:} a \mathrel{::} b \mathbin{:} b$ (`id`)      |

(Please note that they have *not* been used extensively,
and may therefore be incomplete or even unsound implementations
of the above theories.)

It also contains various scripts for tasks such as listing theorems
in a database, shortening proofs, showing repetitions, etc.
(see also <https://github.com/metamath/set.mm/tree/develop/scripts>),
and a syntax file `misc/metamath.sublime-syntax`
for use with text editors or typesetting programs
like [Typst](https://typst.app/docs/reference/text/raw/).

**Contributions are welcome.**

## Other databases

Other Metamath databases include:

* [ql.mm](https://github.com/metamath/set.mm/blob/develop/ql.mm)
  for quantum logic by Norman Megill,
* [lof.mm](https://naipmoro.github.io/lofmm/)
  for Spencer-Brown's Primary Algebra by naipmoro,
* [q0.mm](https://github.com/tirix/q0.mm)
  for Peter Andrews' Q<sub>0</sub> by Stefan O'Rear,
* [matching-logic.mm](https://github.com/runtimeverification/proof-generation/blob/main/theory/matching-logic.mm)
  for matching logic by Xiaohong Chen et al.,
* [peano.mm](https://github.com/metamath/set.mm/blob/develop/peano.mm)
  for Peano arithmetic (PA) by Robert Solovay,
* [nat.mm](https://wiki.planetmath.org/cgi-bin/wiki.pl/Natural_deduction_based_metamath_system)
  for classical set theory by Frédéric Liné,
* [dtt.mm](https://github.com/digama0/dtt.mm)
  for dependent type theory
  and [hol.mm](https://github.com/metamath/set.mm/blob/develop/hol.mm)
  for Simple Type Theory (STT)
  by Mario Carneiro,
* [set.mm](https://github.com/metamath/set.mm/blob/develop/set.mm),
  [iset.mm](https://github.com/metamath/set.mm/blob/develop/iset.mm)
  and [nf.mm](https://github.com/metamath/set.mm/blob/develop/nf.mm)
  for various set theories by Norman Megill and many contributors.
