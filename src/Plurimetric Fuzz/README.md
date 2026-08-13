# Plurimetric Fuzz

The file `PlurimetricFuzz.v` contains a partial mechanisation
of the metatheory of Plurimetric Fuzz, a type system we presented
in a paper published at the FSCD 2024 conference;
see <https://doi.org/10.4230/LIPIcs.FSCD.2024.12>.

The main results proved in the file are
the admissibility of the structural rules and
subject reduction for closed terms.

Weakening is admissible for precontexts (`weakening_prectx`) and,
more generally, for contexts, where the parameter may also be decreased:

```coq
Theorem weakening_ctx p Γ t τ : has_type (p, Γ) t τ ->
  forall q Δ, param_le q p -> prectx_le Γ Δ ->
  has_type (q, Δ) t τ.
```

Renaming along injective, order-preserving maps is admissible:

```coq
Lemma renaming (p : param) (Γ Δ : prectx) (t : term) (τ : type)
  (ξ : var -> var) :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  has_type (p, Γ) t τ ->
  has_type (p, Δ) (t.[ren ξ]) τ.
```

Substitution of a closed value for the topmost variable is admissible:

```coq
Theorem substitution_closed (p : param) (Γ : prectx)
  (t v : term) (s : sens) (σ τ : type) :
  has_type (p, Some (s, σ) .: Γ) t τ ->
  has_type (p, prectx_empty) v σ ->
  has_type (p, Γ) (t.[v/]) τ.
```

The typing system satisfies subject reduction for closed terms:

```coq
Theorem subject_reduction_closed (p : param) (t v : term) (τ : type) :
  has_type (p, prectx_empty) t τ ->
  evals_to t v ->
  has_type (p, prectx_empty) v τ.
```

The development also contains a full set of inversion lemmas (`inversion_*`)
used in the proof of subject reduction.

## A remark on the (!I) typing rule

Note that the formulation of the introduction rule for the exponential modality
we use in this project has a different shape that the one in Reed ans Pierce's
original paper on Fuzz.

```coq
Inductive has_type : ctx -> term -> type -> Prop :=
  | ...
  | TBang p Γ Δ t τ s : prectx_comp Γ Δ ->
      has_type (p, Γ) t τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmBang t) (TyBang s τ)
  | ...
```

Specifically, we allow for an arbitrary precontext `Δ` to appear
in the conclusion, for otherwise, in the case `s = sens_infty`,
weakening would not hold.

## Use of Large Language Models

Parts of this formalisation — particularly at later stages,
after the primary definitions and theorem statements have been drafted —
were developed with assistance from Large Language Models (LLMs).
