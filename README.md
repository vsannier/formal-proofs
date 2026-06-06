This repository contains
the following [Metamath](https://us.metamath.org/) databases
and [Dedukti](https://github.com/Deducteam/Dedukti/) theories:

| Logic/Theory            | File                           | Example theorem                                                   |
|-------------------------|--------------------------------|-------------------------------------------------------------------|
| Natural deduction (NJ)  | [`nj.mm`](src/nj.mm)           | $\Gamma \vdash (\phi \land \psi) \to (\phi \lor \phi)$ (`animor`) |
| SKI combinator calculus | [`ski.mm`](src/ski.mm)         | $\vdash \mathrm{Y}(f) \downarrow f(\mathrm{Y}(f))$ (`fix`)        |
| Four-term analogies     | [`analogy.mm`](src/analogy.mm) | $\vdash a \mathbin{:} a \mathrel{::} b \mathbin{:} b$ (`id`)      |

(Please note that they have *not* been used extensively,
and may therefore be incomplete or even unsound implementations
of the above theories.)

It also contains various scripts for tasks such as listing theorems
in a Metamath database, shortening proofs, showing repetitions, etc.
(see also <https://github.com/metamath/set.mm/tree/develop/scripts>),
and a syntax file `misc/metamath.sublime-syntax`
for use with text editors or typesetting programs
like [Typst](https://typst.app/docs/reference/text/raw/).

**Contributions are welcome.**

---

Other Metamath databases can be found [here](https://github.com/metamath/set.mm/blob/develop/other-databases.md).
