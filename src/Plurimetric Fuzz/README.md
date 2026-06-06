# Plurimetric Fuzz

The file `PlurimetricFuzz.v` contains a partial mechanisation
of the metatheory of Plurimetric Fuzz, a type system we presented
in a paper published at the FSCD 2024 conference;
see <https://doi.org/10.4230/LIPIcs.FSCD.2024.12>.

```coq
Theorem weakening_ctx p Γ t τ : has_type (p, Γ) t τ ->
  forall q Δ, param_le q p -> prectx_le Γ Δ ->
  has_type (q, Δ) t τ.
```

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
