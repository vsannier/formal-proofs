(*
  Formalisation of the metatheory of Plurimetric Fuzz
  <https://doi.org/10.4230/LIPIcs.FSCD.2024.12>
  by Victor Sannier (2024–2026)
*)

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.ClassicalEpsilon.
From Stdlib Require Import Classical ClassicalChoice.
From Stdlib Require Import Program.Program.
From Stdlib Require Import Sets.Ensembles Sets.Finite_sets.
From Stdlib Require Import Sets.Finite_sets_facts Sets.Image.
From Autosubst Require Import Autosubst.

From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

(** * Parameters

    Each extended real number $p$ such that $p \geq 1$
    defines a distance given by: $(x, y) \mapsto \sqrt[p]{x^p + y^p}$. *)

(** A parameter is an extended real number greater than or equal to one. *)
Inductive param : Type :=
  | param_real (p : R) (H : 1 <= p) : param
  | param_infty : param.

Definition param_1 : param := param_real 1 (Rle_refl _).

Program Definition param_2 : param := param_real 2 _.
Next Obligation.
  lra.
Qed.

Definition param_lt (p q : param) : Prop :=
  match p, q with
  | param_real p _, param_real q _ => p < q
  | param_real _ _, param_infty => True
  | param_infty, param_real _ _ => False
  | param_infty, param_infty => False
  end.

Definition param_le (p q : param) : Prop := param_lt p q \/ p = q.

(** [param_le] is a reflexive relation. *)
Lemma param_le_refl (p : param) : param_le p p.
Proof.
  right; reflexivity.
Qed.

(** * Sensitivities *)

(** A sensitivity is a positive extended real number. *)
Inductive sens : Type :=
  | sens_real (r : R) (H : 0 < r)
  | sens_infty.

Definition sens_1 : sens := sens_real 1 Rlt_0_1.

Program Definition sens_2 : sens := sens_real 2 _.
Next Obligation.
  lra.
Qed.

(** If two real numbers are equal,
    then the corresponding sensitivity values are also equal. *)
Lemma sens_eq_real (r1 r2 : R) (H1 : 0 < r1) (H2 : 0 < r2) :
  sens_real r1 H1 = sens_real r2 H2 <-> r1 = r2.
Proof.
  intros.
  split; intro H.
  - now injection H.
  - subst r2.
    f_equal.
    apply proof_irrelevance.
Qed.

(** By [Req_EM_T], equality is decidable for real numbers,
    and therefore so it is for sensitivity values. *)
Lemma sens_eq_dec (s1 s2 : sens) : {s1 = s2} + {s1 <> s2}.
Proof.
  destruct s1 as [s1 H1|], s2 as [s2 H2|].
  all: try solve [right; discriminate | left; reflexivity].
  destruct (Req_EM_T s1 s2) as [-> | Hneq].
  - left; now apply sens_eq_real.
  - right; intro H; apply Hneq; now inversion H.
Qed.

Definition sens_lt (s1 s2 : sens) : Prop :=
  match s1, s2 with
  | sens_real r1 _, sens_real r2 _ => r1 < r2
  | sens_real _ _, sens_infty => True
  | sens_infty, sens_infty => False
  | sens_infty, sens_real _ _ => False
  end.

(** [sens_lt] is a transitive relation. *)
Lemma sens_lt_trans (s1 s2 s3 : sens) :
  sens_lt s1 s2 -> sens_lt s2 s3 -> sens_lt s1 s3.
Proof.
  unfold sens_lt.
  destruct s1; destruct s2; destruct s3.
  all: lra.
Qed.

Definition sens_le (r s : sens) : Prop := sens_lt r s \/ r = s.

(** [sens_le] is a reflexive relation. *)
Lemma sens_le_refl (s : sens) : sens_le s s.
Proof.
  right; reflexivity.
Qed.

(** [sens_le] is a transitive relation. *)
Lemma sens_le_trans (s1 s2 s3 : sens) :
  sens_le s1 s2 -> sens_le s2 s3 -> sens_le s1 s3.
Proof.
  unfold sens_le; intros [H12 | ->] [H23 | ->]; auto.
  left; eapply sens_lt_trans; eauto.
Qed.

Lemma sens_le_real (r1 r2 : R) (H1 : 0 < r1) (H2 : 0 < r2) :
  r1 <= r2 <-> sens_le (sens_real r1 H1) (sens_real r2 H2).
Proof.
  unfold sens_le, sens_lt; split; intro H.
  - destruct (Rle_lt_or_eq_dec _ _ H).
    + now left.
    + right; now apply sens_eq_real.
  - destruct H; [lra |].
    apply sens_eq_real in H; lra.
Qed.

Program Definition sens_inv (r : R) (Hr : 0 < r) : sens :=
  sens_real (/r) (Rinv_0_lt_compat r Hr).

Program Definition sens_sqrt (s : sens) :=
  match s with
  | sens_real s _ => sens_real (Rpower s (/2)) _
  | sens_infty => sens_infty
  end.
Next Obligation.
  apply exp_pos.
Qed.

Definition sens_plus (r s : sens) : sens :=
  match r, s with
  | sens_infty, _ => sens_infty
  | _, sens_infty => sens_infty
  | sens_real r Hr, sens_real s Hs =>
      sens_real (r + s) (Rplus_lt_0_compat r s Hr Hs)
  end.

Definition sens_mult (r s : sens) : sens :=
  match r, s with
  | sens_infty, _ => sens_infty
  | _, sens_infty => sens_infty
  | sens_real r Hr, sens_real s Hs =>
      sens_real (r * s) (Rmult_gt_0_compat r s Hr Hs)
  end.

(** [sens_1] is a left identity for [sens_mult]. *)
Lemma sens_mult_1_l (s : sens) : sens_mult sens_1 s = s.
Proof.
  unfold sens_mult.
  destruct s; simpl.
  - apply sens_eq_real; lra.
  - reflexivity.
Qed.

(** Multiplication of sensitivities is commutative. *)
Lemma sens_mult_comm : forall r s, sens_mult r s = sens_mult s r.
Proof.
  destruct r, s; try reflexivity.
  apply sens_eq_real, Rmult_comm.
Qed.

Lemma sens_mult_assoc (r s t : sens) :
  sens_mult r (sens_mult s t) = sens_mult (sens_mult r s) t.
Proof.
  destruct r as [r Hr |], s as [s Hs |], t as [t Ht |];
    try reflexivity.
  apply sens_eq_real.
  symmetry.
  apply Rmult_assoc.
Qed.

(** [sens_1] is a right identity for [sens_mult]. *)
Lemma sens_mult_1_r (s : sens) : (sens_mult s sens_1) = s.
Proof.
  rewrite sens_mult_comm.
  apply sens_mult_1_l.
Qed.

Lemma sens_mult_le (s r : sens) :
  sens_le sens_1 s ->
  sens_le r (sens_mult s r).
Proof.
  intro H.
  destruct s as [s |], r as [r |].
  - destruct H.
    + left.
      unfold sens_lt in *; simpl in *.
      replace r with (1 * r) at 1; [| lra].
      apply Rmult_lt_compat_r; lra.
    + right.
      unfold sens_mult; apply sens_eq_real.
      apply sens_eq_real in H; rewrite <- H.
      lra.
  - now right.
  - now left.
  - now right.
Qed.

Lemma sens_mult_le_inv (s1 : R) (H1 : s1 > 0) (s2 r : sens) :
  sens_le (sens_mult (sens_real s1 H1) s2) r ->
  sens_le s2 (sens_mult (sens_inv s1 H1) r).
Proof.
  destruct s2 as [s2 H2 |], r as [r H3 |].
  all: unfold sens_le, sens_lt, sens_mult, sens_inv in *.
  all: intro Hle; destruct Hle as [Hlt | Heq].
  all: try solve [ intuition | discriminate ].
  - left.
    assert (/ s1 * s1 = 1) by (apply Rinv_l; lra).
    nra.
  - right.
    inversion Heq.
    apply sens_eq_real.
    assert (/ s1 * s1 = 1) by (apply Rinv_l; lra).
    nra.
Qed.

Program Definition sens_max (r s : sens) : sens :=
  match r, s with
  | sens_infty, _ => sens_infty
  | _, sens_infty => sens_infty
  | sens_real r Hr, sens_real s Hs =>
      sens_real (Rmax r s) _
  end.
Next Obligation.
  unfold Rmax.
  destruct (Rle_dec r s).
  - exact Hs.
  - exact Hr.
Qed.

Lemma sens_le_max (s1 s2 : sens) : sens_le s1 s2 -> sens_max s1 s2 = s2.
Proof.
  intros [Hlt | ->].
  - unfold sens_lt in Hlt.
    destruct s1 as [r1 H1 |], s2 as [r2 H2 |].
    all: try (reflexivity || contradiction).
    apply sens_eq_real, Rmax_right; lra.
  - destruct s2 as [s2 H2 |]; try reflexivity.
    now apply sens_eq_real, Rmax_right.
Qed.

Definition sens_sqrt2 : sens := sens_sqrt sens_2.

Definition real_pnorm (p : R) (r s : R) : R :=
  Rpower ((Rpower r p) + (Rpower s p)) (/p).

Definition real_pad (p r_src r_tgt : R) : R :=
  Rpower (Rpower r_tgt p - Rpower r_src p) (/ p).

Lemma real_pad_sound (p r_src r_tgt : R)
  (Hp : 0 < p) (Hlt : 0 < r_src < r_tgt) :
  real_pnorm p r_src (real_pad p r_src r_tgt) = r_tgt.
Proof.
  assert (0 < Rpower r_tgt p - Rpower r_src p).
  {
    apply Rlt_0_minus.
    now apply Rlt_Rpower_l.
  }
  unfold real_pnorm, real_pad.
  rewrite Rpower_mult, Rinv_l, Rpower_1; try lra.
  rewrite Rplus_minus.
  rewrite Rpower_mult, Rinv_r, Rpower_1; try lra.
Qed.

Lemma real_pad_le (p s1 s2 s : R) :
  1 <= p -> 0 < s1 -> 0 < s2 -> 0 < s ->
  real_pnorm p s1 s2 <= s ->
  s2 <= real_pad p s1 s.
Proof.
  unfold real_pnorm, real_pad.
  intros Hp H1 H2 H Hle.
  replace s2 with (Rpower (Rpower s2 p) (/p)).
  - apply Rle_Rpower_l.
    + apply Rlt_le, Rinv_0_lt_compat; lra.
    + split; [apply exp_pos| ].
      apply Rplus_le_reg_l with (Rpower s1 p).
      apply Rle_trans with (Rpower s p); try lra.
      rewrite <- (Rpower_1 (Rpower s1 p + Rpower s2 p)).
      * replace 1 with (/ p * p); [| apply Rinv_l; lra].
        rewrite <- Rpower_mult.
        apply Rle_Rpower_l; [lra |].
        split; [apply exp_pos | exact Hle].
      * assert (Rpower s1 p > 0) by apply exp_pos.
        assert (Rpower s2 p > 0) by apply exp_pos.
        lra.
  - rewrite Rpower_mult, Rinv_r, Rpower_1; lra.
Qed.

(** The $L^p$ norm of two strictly positive real numbers is strictly greater
    than its first argument. *)
Lemma real_pnorm_strict (p ra rb : R) (Hp : 0 < p) (Hra : 0 < ra) (Hrb : 0 < rb) :
  ra < real_pnorm p ra rb.
Proof.
  unfold real_pnorm.
  replace ra with (Rpower (Rpower ra p) (/p)) at 1.
  - apply Rlt_Rpower_l.
    + apply Rinv_0_lt_compat; lra.
    + split; [apply exp_pos |].
      rewrite <- Rplus_0_r at 1.
      apply Rplus_lt_compat_l, exp_pos.
  - rewrite Rpower_mult, Rinv_r, Rpower_1; lra.
Qed.

(** Lifting of [real_pnorm] from real numbers to sensitivities. *)
Program Definition sens_pnorm (p : param) (r s : sens) : sens :=
  match p with
  | param_real p Hp =>
      match r, s with
       | sens_infty, _ => sens_infty
       | _, sens_infty => sens_infty
       | sens_real r Hr, sens_real s Hs => sens_real (real_pnorm p r s) _
      end
  | param_infty => sens_max r s
  end.
Next Obligation.
  apply exp_pos.
Qed.

(** For all [p], [sens_infty] is left-absorbing for [sens_pnorm p]. *)
Lemma sens_pnorm_infty_l (p : param) (s : sens) :
  sens_pnorm p sens_infty s = sens_infty.
Proof.
  now destruct p.
Qed.

(** For all [p], [sens_infty] is right-absorbing for [sens_pnorm p]. *)
Lemma sens_pnorm_infty_r (p : param) (s : sens) :
  sens_pnorm p s sens_infty = sens_infty.
Proof.
  destruct p, s; reflexivity.
Qed.

Lemma sens_1norm_1_1 : sens_pnorm param_1 sens_1 sens_1 = sens_2.
Proof.
  apply sens_eq_real.
  unfold real_pnorm.
  rewrite Rpower_1, Rinv_1, Rpower_1.
  all: lra.
Qed.

Lemma sens_2norm_1_1 : sens_pnorm param_2 sens_1 sens_1 = sens_sqrt2.
Proof.
  apply sens_eq_real.
  unfold real_pnorm, Rpower.
  rewrite ln_1, Rmult_0_r, exp_0.
  easy.
Qed.

(** [sens_pnorm] is commutative. *)
Lemma sens_pnorm_comm (p : param) (r s : sens) :
  sens_pnorm p r s = sens_pnorm p s r.
Proof.
  destruct r; destruct s.
  all: try reflexivity.
  destruct p; unfold sens_pnorm.
  - apply sens_eq_real.
    unfold real_pnorm.
    now rewrite Rplus_comm.
  - unfold sens_max.
    apply sens_eq_real.
    apply Rmax_comm.
Qed.

(** Multiplication distributes over the sensitivity [p]-norm. *)
Lemma sens_mult_pnorm (p : param) (r s t : sens) :
  sens_mult r (sens_pnorm p s t) =
  sens_pnorm p (sens_mult r s) (sens_mult r t).
Proof.
  destruct p as [p Hp |],
           r as [r Hr |],
           s as [s Hs |],
           t as [t Ht |];
    try reflexivity;
    unfold sens_mult, sens_pnorm.
  - apply sens_eq_real.
    unfold real_pnorm.
    assert (Hrpow : 0 < Rpower r p) by apply exp_pos.
    assert (Hsum : 0 < Rpower s p + Rpower t p).
    { apply Rplus_lt_0_compat; apply exp_pos. }
    rewrite <- (Rpower_mult_distr r s p Hr Hs).
    rewrite <- (Rpower_mult_distr r t p Hr Ht).
    rewrite <- (Rmult_plus_distr_l (Rpower r p) (Rpower s p) (Rpower t p)).
    rewrite <- (Rpower_mult_distr (Rpower r p) (Rpower s p + Rpower t p) (/ p) Hrpow Hsum).
    assert (Hinv : Rpower (Rpower r p) (/ p) = r).
    { rewrite Rpower_mult, Rinv_r, Rpower_1; lra. }
    rewrite Hinv.
    reflexivity.
  - unfold sens_max.
    apply sens_eq_real.
    unfold Rmax.
    destruct (Rle_dec s t);
    destruct (Rle_dec (r * s) (r * t));
    nra.
Qed.

(** [sens_pnorm] is associative. *)
Lemma sens_pnorm_assoc (p : param) (s1 s2 s3 : sens) :
  sens_pnorm p s1 (sens_pnorm p s2 s3) = sens_pnorm p (sens_pnorm p s1 s2) s3.
Proof.
  destruct p, s1, s2, s3.
  all: try reflexivity.
  all: apply sens_eq_real.
  - unfold real_pnorm.
    rewrite !Rpower_mult, Rinv_l by lra.
    rewrite !Rpower_1.
    f_equal; lra.
    all: apply Rplus_lt_0_compat.
    all: apply exp_pos.
  - apply Rmax_assoc.
Qed.

Lemma sens_pnorm_le_r (p : param) (s1 s2 : sens) :
  sens_le s1 (sens_pnorm p s1 s2).
Proof.
  destruct p, s1, s2.
  all: unfold sens_pnorm, sens_le, sens_lt, real_pnorm; simpl.
  all: try (left; exact I).
  all: try (right; reflexivity).
  - left.
    replace r with (Rpower (Rpower r p) (/p)) at 1.
    + apply Rlt_Rpower_l.
      * apply Rinv_0_lt_compat; lra.
      * split; [apply exp_pos |].
        rewrite <- Rplus_0_r at 1.
        apply Rplus_lt_compat_l, exp_pos.
    + rewrite Rpower_mult, Rinv_r, Rpower_1; lra.
  - destruct (Rlt_dec r r0) as [Hlt | Hge].
    + left.
      rewrite Rmax_right; lra.
    + right.
      apply sens_eq_real.
      rewrite Rmax_left; lra.
Qed.

Lemma sens_pnorm_le_l (p : param) (s1 s2 : sens) :
  sens_le s2 (sens_pnorm p s1 s2).
Proof.
  rewrite sens_pnorm_comm.
  apply sens_pnorm_le_r.
Qed.

Program Definition sens_pad (p : param) (s_src s_tgt : sens) : sens :=
  match p with
  | param_infty => s_tgt
  | param_real p Hp =>
      match s_src, s_tgt with
      | sens_real r_src Hr_src, sens_real r_tgt Hr_tgt =>
          sens_real (real_pad p r_src r_tgt) _
      | _, sens_infty => sens_infty
      | sens_infty, _ => sens_infty
      end
  end.
Next Obligation.
  unfold real_pad.
  apply exp_pos.
Qed.

Lemma sens_pad_sound (p : param) (s_src s_tgt : sens) :
  sens_lt s_src s_tgt ->
  sens_pnorm p s_src (sens_pad p s_src s_tgt) = s_tgt.
Proof.
  intro Hlt.
  destruct p;
  destruct s_src as [s_src |];
  destruct s_tgt as [s_tgt |].
  all: unfold sens_lt in Hlt.
  all: try (reflexivity || contradiction).
  - apply sens_eq_real.
    apply real_pad_sound; lra.
  - unfold sens_pnorm, sens_max; simpl.
    apply sens_eq_real, Rmax_right.
    now left.
Qed.

Lemma sens_pad_le (p : param) (s1 s2 s : sens) :
  sens_le (sens_pnorm p s1 s2) s ->
  sens_le s2 (sens_pad p s1 s).
Proof.
  intro Hle.
  destruct p as [p Hp |], s1 as [s1 H1 |], s2 as [s2 H2 |], s as [s H |].
  all: try solve [ left; exact I | right; reflexivity ].
  all: try exact Hle.
  all: unfold sens_pad in *.
  - unfold sens_le, sens_lt.
    rewrite sens_eq_real.
    apply real_pad_le; try lra.
    unfold sens_pnorm in Hle.
    now rewrite <- sens_le_real in Hle.
  - destruct Hle as [Hlt | Heq].
    + inversion Hlt.
    + inversion Heq.
  - eapply sens_le_trans; [apply sens_pnorm_le_l | exact Hle].
  - apply sens_le_trans with sens_infty.
    + now left.
    + exact Hle.
Qed.

(** If the [p]-norm of [ra] and [rb] is no greater than [ra],
    then this contradicts the strict positivity of [rb]. *)
Lemma sens_pnorm_not_le (p : R) (Hp : 1 <= p) (ra rb : R)
  (Hra : 0 < ra) (Hrb : 0 < rb) :
  sens_le (sens_pnorm (param_real p Hp) (sens_real ra Hra) (sens_real rb Hrb))
    (sens_real ra Hra) -> False.
Proof.
  intro H.
  apply sens_le_real in H.
  apply Rle_not_lt in H.
  apply H, real_pnorm_strict; lra.
Qed.

(** * Plurimetric Fuzz *)

(** ** Syntax *)

(** *** Types and Terms *)

Inductive ty_base : Type :=
  | TyUnit
  | TyNat.

Inductive type :=
  | TyVar (α : var)
  | TyBase (τ : ty_base)
  | TyArrow (p : param) (σ τ : type)
  | TyPair (p : param) (τ1 τ2 : type)
  | TyPlus (τ1 τ2 : type)
  | TyBang (s : sens) (τ : type)
  | TyRec (τ : {bind type}).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Definition TyBool := TyPlus (TyBase TyUnit) (TyBase TyUnit).

(** The recursive list type [mu alpha. Unit + (τ * alpha)].  The element
    type is lifted because [TyRec] binds the type variable at index zero. *)
Definition TyListBody (p : param) (τ : type) : type :=
  TyPlus (TyBase TyUnit) (TyPair p τ.[ren (+1%nat)] (TyVar 0%nat)).

Definition TyList (p : param) (τ : type) : type := TyRec (TyListBody p τ).

Lemma TyList_unfold (p : param) (τ : type) :
  (TyListBody p τ).[TyList p τ/] =
  TyPlus (TyBase TyUnit) (TyPair p τ (TyList p τ)).
Proof.
  unfold TyListBody.
  asimpl.
  reflexivity.
Qed.

Inductive term_base : Type :=
  | ValUnit : term_base
  | ValNat : nat -> term_base.

Inductive term :=
  | TmBase (t : term_base)
  | TmVar (x : var)
  | TmAbs (t : {bind term})
  | TmApp (tf t : term)
  | TmPair (t1 t2 : term)
  | TmLetPair (t : term) (tbody : {bind 2 of term})
  | TmInjL (t : term)
  | TmInjR (t : term)
  | TmCase (t : term) (tl tr : {bind term})
  | TmBang (t : term)
  | TmLetBang (t : term) (tbody : {bind term})
  | TmFold (τ : type) (t : term)
  | TmUnfold (τ : type) (t : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Definition TmUnit := TmBase ValUnit.

Definition TmNat (n : nat) := TmBase (ValNat n).

Definition TmTrue := TmInjL (TmBase ValUnit).

Definition TmFalse := TmInjR (TmBase ValUnit).

Definition TmNil (p : param) (τ : type) : term :=
  TmFold (TyList p τ) (TmInjL TmUnit).

Definition TmCons (p : param) (τ : type) (thead ttail : term) : term :=
  TmFold (TyList p τ) (TmInjR (TmPair thead ttail)).

Definition TmDiag := TmAbs (TmPair (TmVar 0%nat) (TmVar 0%nat)).

Definition TmSwap :=
  TmAbs (TmLetPair (TmVar 0%nat) (TmPair (TmVar 0%nat) (TmVar 1%nat))).

(** *** Precontexts and Contexts *)

Definition prectx_support (f : var -> option (sens * type)) : Ensemble var :=
  fun x => f x <> None.

(** Precontexts are finitely supported maps.  Finite support is part of the
    representation, rather than a side condition on selected typing rules. *)
Record prectx : Type := {
  prectx_lookup :> var -> option (sens * type);
  prectx_finite : Finite var (prectx_support prectx_lookup)
}.

Definition prectx_dom (Γ : prectx) : Ensemble var :=
  prectx_support Γ.

Lemma prectx_ext (Γ Δ : prectx) :
  (forall x, Γ x = Δ x) -> Γ = Δ.
Proof.
  destruct Γ as [Γ HΓ], Δ as [Δ HΔ]; simpl.
  intro Heq.
  assert (Γ = Δ) by (extensionality x; apply Heq).
  subst Δ.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition prectx_empty : prectx.
Proof.
  refine {| prectx_lookup := fun _ => None |}.
  replace (prectx_support (fun _ : var => None)) with (Empty_set var).
  - apply Empty_is_finite.
  - apply Extensionality_Ensembles; split; intros x Hx; contradiction.
Defined.

Lemma prectx_empty_lookup (x : var) : prectx_empty x = None.
Proof.
  reflexivity.
Qed.

(** Add a de Bruijn entry to the front of a precontext. *)
Definition prectx_cons (a : option (sens * type)) (Γ : prectx) : prectx.
Proof.
  refine {| prectx_lookup := a .: Γ |}.
  eapply Finite_downward_closed with
    (A := Add var (Im var var (prectx_dom Γ) S) 0%nat).
  - apply Add_preserves_Finite, finite_image, prectx_finite.
  - intros [|x] Hx.
    + apply Add_intro2.
    + apply Add_intro1.
      apply Im_intro with x; [exact Hx | reflexivity].
Defined.

Lemma prectx_cons_lookup (a : option (sens * type)) (Γ : prectx) (x : var) :
  prectx_cons a Γ x = (a .: Γ) x.
Proof.
  reflexivity.
Qed.

Lemma finite_preimage_injective (U V : Type) (f : U -> V)
  (A : Ensemble V) :
  (forall x y, f x = f y -> x = y) ->
  Finite V A ->
  Finite U (fun x => A (f x)).
Proof.
  intros Hinj Hfinite.
  induction Hfinite as [| A Hfinite IH y Hy].
  - replace (fun x => Empty_set V (f x)) with (Empty_set U).
    + apply Empty_is_finite.
    + apply Extensionality_Ensembles; split; intros x Hx; contradiction.
  - destruct (classic (exists x, f x = y)) as [[x Hfx] | Hnone].
    + replace (fun z => Add V A y (f z)) with
        (Add U (fun z => A (f z)) x).
      * apply Add_preserves_Finite; exact IH.
      * apply Extensionality_Ensembles; split; intros z Hz.
        -- apply Add_inv in Hz as [Hz | Hz].
           ++ apply Add_intro1; exact Hz.
           ++ assert (Hfz : f z = y) by congruence.
              destruct Hfz; apply Add_intro2.
        -- apply Add_inv in Hz as [Hz | Hz].
           ++ apply Add_intro1; exact Hz.
           ++ assert (Hzx : z = x) by (apply Hinj; congruence).
              destruct Hzx; apply Add_intro2.
    + replace (fun z => Add V A y (f z)) with (fun z => A (f z)).
      * exact IH.
      * apply Extensionality_Ensembles; split; intros z Hz.
        -- apply Add_intro1; exact Hz.
        -- apply Add_inv in Hz as [Hz | Hz].
           ++ exact Hz.
           ++ exfalso; apply Hnone; exists z; symmetry; exact Hz.
Qed.

(** Remove the first de Bruijn entry. *)
Definition prectx_tail (Γ : prectx) : prectx.
Proof.
  refine {| prectx_lookup := fun x => Γ (S x) |}.
  apply (finite_preimage_injective var var S (prectx_dom Γ)).
  - intros x y H; now injection H.
  - exact (prectx_finite Γ).
Defined.

Lemma prectx_tail_lookup (Γ : prectx) (x : var) :
  prectx_tail Γ x = Γ (S x).
Proof.
  reflexivity.
Qed.

Lemma prectx_tail_cons (a : option (sens * type)) (Γ : prectx) :
  prectx_tail (prectx_cons a Γ) = Γ.
Proof.
  apply prectx_ext; intro x.
  reflexivity.
Qed.

(** The cardinality of the (finite) domain of a precontext. *)
Definition prectx_card (Γ : prectx) : nat :=
  epsilon (inhabits 0%nat) (cardinal var (prectx_dom Γ)).

Lemma prectx_card_spec (Γ : prectx) :
  cardinal var (prectx_dom Γ) (prectx_card Γ).
Proof.
  unfold prectx_card.
  apply epsilon_spec, finite_cardinal, prectx_finite.
Qed.

Lemma prectx_card_dom_eq (Γ Δ : prectx) :
  prectx_dom Γ = prectx_dom Δ -> prectx_card Γ = prectx_card Δ.
Proof.
  intro Hdom.
  eapply cardinal_unicity.
  - apply prectx_card_spec.
  - rewrite Hdom.
    apply prectx_card_spec.
Qed.

Lemma prectx_card_lookup_eq (Γ Δ : prectx) :
  (forall x, Γ x = Δ x) -> prectx_card Γ = prectx_card Δ.
Proof.
  intro Hlookup.
  apply prectx_card_dom_eq.
  apply Extensionality_Ensembles; split; intros x Hx;
    unfold prectx_dom, prectx_support in *.
  - intro Hnone.
    apply Hx.
    exact (eq_trans (Hlookup x) Hnone).
  - intro Hnone.
    apply Hx.
    exact (eq_trans (eq_sym (Hlookup x)) Hnone).
Qed.

Lemma prectx_card_le_dom (Γ Δ : prectx) :
  Included var (prectx_dom Γ) (prectx_dom Δ) ->
  (prectx_card Γ <= prectx_card Δ)%nat.
Proof.
  intro Hincluded.
  eapply incl_card_le.
  - apply prectx_card_spec.
  - apply prectx_card_spec.
  - exact Hincluded.
Qed.

(** $N_Γ = \max(1, |\operatorname{dom}(Γ)|)$. *)
Definition prectx_N (Γ : prectx) : nat :=
  Nat.max 1 (prectx_card Γ).

Lemma prectx_N_card_eq (Γ Δ : prectx) :
  prectx_card Γ = prectx_card Δ -> prectx_N Γ = prectx_N Δ.
Proof.
  intro Hcard.
  unfold prectx_N.
  now rewrite Hcard.
Qed.

Lemma prectx_N_dom_eq (Γ Δ : prectx) :
  prectx_dom Γ = prectx_dom Δ -> prectx_N Γ = prectx_N Δ.
Proof.
  intro Hdom.
  apply prectx_N_card_eq, prectx_card_dom_eq, Hdom.
Qed.

Lemma prectx_N_le_card (Γ Δ : prectx) :
  (prectx_card Γ <= prectx_card Δ)%nat ->
  (prectx_N Γ <= prectx_N Δ)%nat.
Proof.
  intro Hcard.
  unfold prectx_N.
  now apply Nat.max_le_compat_l.
Qed.

Lemma prectx_N_pos (Γ : prectx) : (0 < INR (prectx_N Γ))%R.
Proof.
  apply lt_0_INR.
  unfold prectx_N.
  lia.
Qed.

Lemma prectx_N_ge_1 (Γ : prectx) : (1 <= INR (prectx_N Γ))%R.
Proof.
  replace 1%R with (INR 1) by reflexivity.
  apply le_INR.
  unfold prectx_N.
  apply Nat.le_max_l.
Qed.

Lemma prectx_empty_dom : prectx_dom prectx_empty = Empty_set var.
Proof.
  apply Extensionality_Ensembles; split; intros x Hx.
  - exfalso.
    apply Hx, prectx_empty_lookup.
  - contradiction.
Qed.

Lemma prectx_card_empty : prectx_card prectx_empty = 0%nat.
Proof.
  eapply cardinal_unicity.
  - apply prectx_card_spec.
  - rewrite prectx_empty_dom.
    apply card_empty.
Qed.

Lemma prectx_N_empty : prectx_N prectx_empty = 1%nat.
Proof.
  unfold prectx_N.
  now rewrite prectx_card_empty.
Qed.

Lemma prectx_cons_some_dom (a : sens * type) (Γ : prectx) :
  prectx_dom (prectx_cons (Some a) Γ) =
  Add var (Im var var (prectx_dom Γ) S) 0%nat.
Proof.
  apply Extensionality_Ensembles; split; intros [|x] Hx.
  - apply Add_intro2.
  - apply Add_intro1.
    apply Im_intro with x; [exact Hx | reflexivity].
  - unfold prectx_dom, prectx_support.
    discriminate.
  - apply Add_inv in Hx as [Hx | Hx].
    + inversion Hx as [y Hy z Hyz].
      injection Hyz as [= <-].
      exact Hy.
    + inversion Hx.
Qed.

Lemma prectx_card_cons_some (a : sens * type) (Γ : prectx) :
  prectx_card (prectx_cons (Some a) Γ) = S (prectx_card Γ).
Proof.
  destruct
    (cardinal_Im_intro var var (prectx_dom Γ) S (prectx_card Γ)
      (prectx_card_spec Γ))
    as [n Himage].
  assert (Hn : n = prectx_card Γ).
  {
    eapply injective_preserves_cardinal.
    - exact Nat.succ_inj.
    - apply prectx_card_spec.
    - exact Himage.
  }
  subst n.
  eapply cardinal_unicity.
  - apply prectx_card_spec.
  - rewrite prectx_cons_some_dom.
    apply card_add.
    + exact Himage.
    + intro Hzero.
      inversion Hzero as [x Hx y Hxy].
      discriminate Hxy.
Qed.

Definition param_recip (p : param) : R :=
  match p with
  | param_real r _ => / r
  | param_infty => 0
  end.

Lemma param_recip_antitone (p q : param) :
  param_le p q -> param_recip q <= param_recip p.
Proof.
  intros [Hpq | ->]; [| lra].
  destruct p as [p Hp |], q as [q Hq |]; simpl in *; try contradiction.
  - apply Rinv_le_contravar; lra.
  - apply Rlt_le, Rinv_0_lt_compat; lra.
Qed.

(** The finite-dimensional $L^p$/$L^q$ comparison factor
    $N_Γ^{1/p-1/q}$. *)
Definition real_dim_factor (Γ : prectx) (p q : param) : R :=
  Rpower (INR (prectx_N Γ)) (param_recip p - param_recip q).

Lemma real_dim_factor_pos (Γ : prectx) (p q : param) :
  real_dim_factor Γ p q > 0.
Proof.
  unfold real_dim_factor.
  apply exp_pos.
Qed.

Definition sens_dim_factor (Γ : prectx) (p q : param) : sens :=
  sens_real (real_dim_factor Γ p q) (real_dim_factor_pos Γ p q).

Lemma sens_dim_factor_refl (Γ : prectx) (p : param) :
  sens_dim_factor Γ p p = sens_1.
Proof.
  unfold sens_dim_factor, sens_1.
  apply sens_eq_real.
  unfold real_dim_factor.
  rewrite Rminus_diag.
  apply Rpower_O.
  apply prectx_N_pos.
Qed.

Lemma sens_dim_factor_ge_1 (Γ : prectx) (p q : param) :
  param_le p q -> sens_le sens_1 (sens_dim_factor Γ p q).
Proof.
  intro Hpq.
  apply sens_le_real.
  unfold sens_dim_factor, real_dim_factor.
  replace 1%R with (Rpower (INR (prectx_N Γ)) 0).
  - apply Rle_Rpower.
    + apply prectx_N_ge_1.
    + pose proof (param_recip_antitone p q Hpq); lra.
  - apply Rpower_O, prectx_N_pos.
Qed.

Lemma sens_dim_factor_empty (p q : param) :
  sens_dim_factor prectx_empty p q = sens_1.
Proof.
  unfold sens_dim_factor, sens_1, real_dim_factor.
  apply sens_eq_real.
  rewrite prectx_N_empty.
  simpl.
  unfold Rpower.
  rewrite ln_1, Rmult_0_r, exp_0.
  reflexivity.
Qed.

Lemma sens_dim_factor_card_eq (Γ Δ : prectx) p q :
  prectx_card Γ = prectx_card Δ ->
  sens_dim_factor Γ p q = sens_dim_factor Δ p q.
Proof.
  intro Hcard.
  unfold sens_dim_factor.
  apply sens_eq_real.
  unfold real_dim_factor.
  now rewrite (prectx_N_card_eq Γ Δ Hcard).
Qed.

Lemma sens_dim_factor_N_mono (Γ Δ : prectx) p q :
  param_le p q ->
  (prectx_N Γ <= prectx_N Δ)%nat ->
  sens_le (sens_dim_factor Γ p q) (sens_dim_factor Δ p q).
Proof.
  intros Hpq HN.
  apply sens_le_real.
  unfold real_dim_factor.
  apply Rle_Rpower_l.
  - pose proof (param_recip_antitone p q Hpq).
    lra.
  - split.
    + apply prectx_N_pos.
    + now apply le_INR.
Qed.

Example prectx_card_singleton (s : sens) (τ : type) :
  prectx_card (prectx_cons (Some (s, τ)) prectx_empty) = 1%nat.
Proof.
  rewrite prectx_card_cons_some, prectx_card_empty.
  reflexivity.
Qed.

Example prectx_N_two_variables (s : sens) (τ : type) :
  prectx_N
    (prectx_cons (Some (s, τ))
      (prectx_cons (Some (s, τ)) prectx_empty)) = 2%nat.
Proof.
  unfold prectx_N.
  repeat rewrite prectx_card_cons_some.
  rewrite prectx_card_empty.
  reflexivity.
Qed.

Example prectx_N_three_variables (s : sens) (τ : type) :
  prectx_N
    (prectx_cons (Some (s, τ))
      (prectx_cons (Some (s, τ))
        (prectx_cons (Some (s, τ)) prectx_empty))) = 3%nat.
Proof.
  unfold prectx_N.
  repeat rewrite prectx_card_cons_some.
  rewrite prectx_card_empty.
  reflexivity.
Qed.

Definition prectx_le (Γ1 Γ2 : prectx) : Prop :=
  forall x s1 τ, Γ1 x = Some (s1, τ) ->
  exists s2, (Γ2 x = Some (s2, τ) /\ sens_le s1 s2).

Lemma prectx_le_refl (Γ : prectx) : prectx_le Γ Γ.
Proof.
  unfold prectx_le.
  intros.
  exists s1.
  split.
  - exact H.
  - apply sens_le_refl.
Qed.

Lemma prectx_le_trans (Γ1 Γ2 Γ3 : prectx) :
  prectx_le Γ1 Γ2 -> prectx_le Γ2 Γ3 -> prectx_le Γ1 Γ3.
Proof.
  intros H12 H23.
  intros x s1 τ Hx.
  destruct (H12 x s1 τ Hx) as [s2 [Hx2 Hle12]].
  destruct (H23 x s2 τ Hx2) as [s3 [Hx3 Hle23]].
  exists s3; split; auto.
  eapply sens_le_trans; eauto.
Qed.

Lemma prectx_le_support (Γ Δ : prectx) :
  prectx_le Γ Δ -> Included var (prectx_dom Γ) (prectx_dom Δ).
Proof.
  intros Hle x Hx.
  unfold prectx_dom, prectx_support in *.
  destruct (Γ x) as [[s τ] |] eqn:HΓ.
  - destruct (Hle x s τ HΓ) as [sΔ [HΔ _]].
    intro Hnone; rewrite HΔ in Hnone; discriminate.
  - exfalso; apply Hx; exact HΓ.
Qed.

Lemma prectx_le_card (Γ Δ : prectx) :
  prectx_le Γ Δ -> (prectx_card Γ <= prectx_card Δ)%nat.
Proof.
  intro Hle.
  apply prectx_card_le_dom, prectx_le_support, Hle.
Qed.

Lemma prectx_le_N (Γ Δ : prectx) :
  prectx_le Γ Δ -> (prectx_N Γ <= prectx_N Δ)%nat.
Proof.
  intro Hle.
  apply prectx_N_le_card, prectx_le_card, Hle.
Qed.

Lemma sens_dim_factor_le (Γ Δ : prectx) p q :
  prectx_le Γ Δ ->
  param_le p q ->
  sens_le (sens_dim_factor Γ p q) (sens_dim_factor Δ p q).
Proof.
  intros Hle Hpq.
  apply sens_dim_factor_N_mono; [exact Hpq | now apply prectx_le_N].
Qed.

(** If [Γ] is smaller than or equal to [Δ],
    then they are pointwise compatible. *)
Lemma prectx_le_type_eq Γ Δ x s1 τ1 s2 τ2 : prectx_le Γ Δ ->
  Γ x = Some (s1, τ1) -> Δ x = Some (s2, τ2) -> τ1 = τ2.
Proof.
  intros Hle HΓ HΔ.
  destruct (Hle x s1 τ1 HΓ) as [s2' [HΔ' _]].
  congruence.
Qed.

Lemma prectx_le_lookup (Γ Δ : prectx)
  (x : var) (sΓ : sens) (τ : type) :
  prectx_le Γ Δ ->
  Γ x = Some (sΓ, τ) ->
  exists sΔ, Δ x = Some (sΔ, τ) /\ sens_le sΓ sΔ.
Proof.
  intros Hle HΓ.
  unfold prectx_le in Hle.
  specialize (Hle x sΓ τ HΓ).
  destruct Hle as [r ?].
  now exists r.
Qed.

Lemma prectx_le_cons (Γ Δ : prectx) τ :
  prectx_le Γ Δ -> prectx_le (prectx_cons τ Γ) (prectx_cons τ Δ).
Proof.
  unfold prectx_le.
  intros.
  destruct x as [| x]; simpl in *.
  - exists s1.
    split; [exact H0 | apply sens_le_refl].
  - now apply H in H0.
Qed.

Definition prectx_scale (s : sens) (Γ : prectx) : prectx.
Proof.
  refine
    {| prectx_lookup := fun x =>
         match Γ x with
         | Some (r, τ) => Some (sens_mult s r, τ)
         | None => None
         end |}.
  eapply Finite_downward_closed; [exact (prectx_finite Γ) |].
  intros x Hx.
  unfold prectx_support in *.
  destruct (Γ x) eqn:HΓ.
  - intro Hnone; rewrite HΓ in Hnone; discriminate.
  - exfalso; apply Hx; rewrite HΓ; reflexivity.
Defined.

Lemma prectx_scale_lookup (s : sens) (Γ : prectx) (x : var) :
  prectx_scale s Γ x =
  match Γ x with
  | Some (r, τ) => Some (sens_mult s r, τ)
  | None => None
  end.
Proof.
  reflexivity.
Qed.

Lemma prectx_scale_dom (s : sens) (Γ : prectx) :
  prectx_dom (prectx_scale s Γ) = prectx_dom Γ.
Proof.
  apply Extensionality_Ensembles; split; intros x Hx.
  - change (prectx_scale s Γ x <> None) in Hx.
    change (Γ x <> None).
    rewrite prectx_scale_lookup in Hx.
    destruct (Γ x) as [[r τ] |]; congruence.
  - change (Γ x <> None) in Hx.
    change (prectx_scale s Γ x <> None).
    rewrite prectx_scale_lookup.
    destruct (Γ x) as [[r τ] |]; congruence.
Qed.

Lemma prectx_scale_card (s : sens) (Γ : prectx) :
  prectx_card (prectx_scale s Γ) = prectx_card Γ.
Proof.
  apply prectx_card_dom_eq, prectx_scale_dom.
Qed.

Lemma prectx_scale_N (s : sens) (Γ : prectx) :
  prectx_N (prectx_scale s Γ) = prectx_N Γ.
Proof.
  apply prectx_N_card_eq, prectx_scale_card.
Qed.

Lemma sens_dim_factor_scale (s : sens) (Γ : prectx) p q :
  sens_dim_factor (prectx_scale s Γ) p q = sens_dim_factor Γ p q.
Proof.
  apply sens_dim_factor_card_eq, prectx_scale_card.
Qed.

Lemma prectx_scale_1 (Γ : prectx) : prectx_scale sens_1 Γ = Γ.
Proof.
  apply prectx_ext; intro x.
  change
    (match Γ x with
     | Some (r, τ) => Some (sens_mult sens_1 r, τ)
     | None => None
     end = Γ x).
  destruct (Γ x) as [[s τ] |].
  - repeat f_equal.
    apply sens_mult_1_l.
  - reflexivity.
Qed.

Lemma prectx_scale_empty (s : sens) :
  prectx_scale s prectx_empty = prectx_empty.
Proof.
  apply prectx_ext; intro x.
  rewrite prectx_scale_lookup, prectx_empty_lookup.
  reflexivity.
Qed.

Lemma prectx_scale_empty_inv (s : sens) (Γ : prectx) :
  prectx_scale s Γ = prectx_empty ->
  Γ = prectx_empty.
Proof.
  intro H.
  apply prectx_ext; intro x.
  destruct (Γ x) as [[r τ] |] eqn:HΓx; [| reflexivity].
  exfalso.
  assert (H' : prectx_scale s Γ x = None).
  { apply (f_equal (fun Θ : prectx => Θ x) H). }
  change
    (match Γ x with
     | Some (r, τ) => Some (sens_mult s r, τ)
     | None => None
     end = None) in H'.
  rewrite HΓx in H'.
  discriminate.
Qed.

Lemma prectx_scale_assoc (r s : sens) (Γ : prectx) :
  prectx_scale r (prectx_scale s Γ) =
  prectx_scale (sens_mult r s) Γ.
Proof.
  apply prectx_ext; intro x.
  repeat rewrite prectx_scale_lookup.
  destruct (Γ x) as [[t τ] |]; [| reflexivity].
  f_equal.
  f_equal.
  apply sens_mult_assoc.
Qed.

Lemma prectx_scale_cons (r s : sens) (τ : type) (Γ : prectx) :
  prectx_scale r (prectx_cons (Some (s, τ)) Γ) =
  prectx_cons (Some (sens_mult r s, τ)) (prectx_scale r Γ).
Proof.
  apply prectx_ext; intro x.
  destruct x; reflexivity.
Qed.

Lemma prectx_scale_le (s : sens) (Γ : prectx) :
  sens_le sens_1 s ->
  prectx_le Γ (prectx_scale s Γ).
Proof.
  intro H.
  intros x sΓ τΓ HΓ.
  exists (sens_mult s sΓ).
  split.
  - rewrite prectx_scale_lookup.
    now rewrite HΓ.
  - now apply sens_mult_le.
Qed.

Lemma prectx_scale_inv (s : R) (Hs : 0 < s) Γ :
  prectx_scale (sens_real s Hs) (prectx_scale (sens_inv s Hs) Γ) = Γ.
Proof.
  apply prectx_ext; intro x.
  repeat rewrite prectx_scale_lookup.
  unfold sens_inv.
  destruct (Γ x) as [[r τ]|]; [| reflexivity].
  repeat f_equal.
  destruct r; unfold sens_mult; [| reflexivity].
  apply sens_eq_real.
  rewrite <- Rmult_assoc.
  rewrite Rmult_inv_r; lra.
Qed.

Lemma prectx_scale_le_inv (s : R) (Hs : 0 < s) Γ Δ :
  prectx_le (prectx_scale (sens_real s Hs) Γ) Δ ->
  prectx_le Γ (prectx_scale (sens_inv s Hs) Δ).
Proof.
  intros Hle x s1 τ HΓ.
  destruct (Hle x (sens_mult (sens_real s Hs) s1) τ) as [r [HΔ Hr]].
  - rewrite prectx_scale_lookup.
    now rewrite HΓ.
  - exists (sens_mult (sens_inv s Hs) r).
    rewrite prectx_scale_lookup.
    rewrite HΔ.
    split; [reflexivity | now apply sens_mult_le_inv].
Qed.

(** Two precontexts are compatible iff they assign the same type
    to the same variable. *)
Definition prectx_comp (Γ Δ : prectx) : Prop := forall x s1 τ1 s2 τ2,
  Γ x = Some (s1, τ1) -> Δ x = Some (s2, τ2) -> τ1 = τ2.

(** A precontext is compatible with itself. *)
Lemma prectx_comp_refl (Γ : prectx) : prectx_comp Γ Γ.
Proof.
  unfold prectx_comp.
  intros x s1 τ1 s2 τ2 H1 H2.
  congruence.
Qed.

Lemma prectx_comp_empty_l (Γ : prectx) : prectx_comp prectx_empty Γ.
Proof.
  unfold prectx_comp.
  intros x s1 τ1 s2 τ2 H1 H2.
  discriminate.
Qed.

Lemma prectx_comp_empty_r (Γ : prectx) : prectx_comp Γ prectx_empty.
Proof.
  unfold prectx_comp.
  intros x s1 τ1 s2 τ2 H1 H2.
  rewrite prectx_empty_lookup in H2.
  discriminate H2.
Qed.

(** [prectx_comp] is a symmetric relation. *)
Lemma prectx_comp_sym (Γ Δ : prectx) : prectx_comp Γ Δ -> prectx_comp Δ Γ.
Proof.
  unfold prectx_comp.
  intros H x s1 τ1 s2 τ2 H1 H2.
  apply eq_sym.
  now apply H with x s2 s1.
Qed.

Lemma prectx_le_comp Γ Δ : prectx_le Γ Δ -> prectx_comp Γ Δ.
Proof.
  intros H x s1 τ1 s2 τ2 H1 H2.
  eapply prectx_le_type_eq; eauto.
Qed.

(** If [Γ] and [Δ] are compatible,
    then so are [prectx_scale s Γ] and [Δ]. *)
Lemma prectx_comp_scale_l (Γ Δ : prectx) (s : sens) :
  prectx_comp Γ Δ -> prectx_comp (prectx_scale s Γ) Δ.
Proof.
  unfold prectx_comp.
  intros H x s1 τ1 s2 τ2 H1 H2.
  rewrite prectx_scale_lookup in H1.
  destruct (Γ x) as [[sΓ τΓ]|] eqn:HΓ; [| discriminate].
  apply H with x sΓ s2; [| exact H2].
  rewrite HΓ.
  now inversion H1.
Qed.

(** If [Γ] and [Δ] are compatible,
    then so are [Γ] and [prectx_scale s Δ]. *)
Lemma prectx_comp_scale_r (Γ Δ : prectx) (s : sens) :
  prectx_comp Γ Δ -> prectx_comp Γ (prectx_scale s Δ).
Proof.
  unfold prectx_comp.
  intros H x s1 τ1 s2 τ2 H1 H2.
  rewrite prectx_scale_lookup in H2.
  destruct (Δ x) as [[sΔ τΔ]|] eqn:HΔ; [| discriminate].
  apply H with x s1 sΔ; [exact H1 |].
  rewrite HΔ.
  now inversion H2.
Qed.

Lemma prectx_comp_scale (r s : sens) (Γ Δ : prectx) :
  prectx_comp Γ Δ ->
  prectx_comp (prectx_scale r Γ) (prectx_scale s Δ).
Proof.
  intro Hcomp.
  apply prectx_comp_scale_l.
  now apply prectx_comp_scale_r.
Qed.

Definition prectx_contr (p : param) (Γ Δ : prectx) : prectx.
Proof.
  refine
    {| prectx_lookup := fun x =>
         match Γ x, Δ x with
         | Some (s1, τ1), Some (s2, _) => Some (sens_pnorm p s1 s2, τ1)
         | Some v, None => Some v
         | None, Some v => Some v
         | None, None => None
         end |}.
  eapply Finite_downward_closed with
    (A := Union var (prectx_dom Γ) (prectx_dom Δ)).
  - apply Union_preserves_Finite; apply prectx_finite.
  - intros x Hx.
    unfold prectx_dom, prectx_support in *.
    destruct (Γ x) eqn:HΓ, (Δ x) eqn:HΔ.
    + apply Union_introl; intro Hnone; rewrite HΓ in Hnone; discriminate.
    + apply Union_introl; intro Hnone; rewrite HΓ in Hnone; discriminate.
    + apply Union_intror; intro Hnone; rewrite HΔ in Hnone; discriminate.
    + exfalso; apply Hx; rewrite HΓ, HΔ; reflexivity.
Defined.

Lemma prectx_contr_lookup_eq (p : param) (Γ Δ : prectx) (x : var) :
  prectx_contr p Γ Δ x =
  match Γ x, Δ x with
  | Some (s1, τ1), Some (s2, _) => Some (sens_pnorm p s1 s2, τ1)
  | Some v, None => Some v
  | None, Some v => Some v
  | None, None => None
  end.
Proof.
  reflexivity.
Qed.

Lemma prectx_contr_empty_l (p : param) (Γ : prectx) :
  prectx_contr p prectx_empty Γ = Γ.
Proof.
  apply prectx_ext; intro x.
  rewrite prectx_contr_lookup_eq.
  now destruct (Γ x) as [[s τ] |].
Qed.

Lemma prectx_contr_empty_r (p : param) (Γ : prectx) :
  prectx_contr p Γ prectx_empty = Γ.
Proof.
  apply prectx_ext; intro x.
  rewrite prectx_contr_lookup_eq.
  now destruct (Γ x) as [[s τ] |].
Qed.

Lemma prectx_contr_empty_inv (p : param) (Γ Δ : prectx) :
  prectx_contr p Γ Δ = prectx_empty ->
  Γ = prectx_empty /\ Δ = prectx_empty.
Proof.
  intro H.
  split; apply prectx_ext; intro x.
  - destruct (Γ x) as [[s τ] |] eqn:HΓx; [| reflexivity].
    exfalso.
    assert (H' : prectx_contr p Γ Δ x = None).
    { apply (f_equal (fun Θ : prectx => Θ x) H). }
    rewrite prectx_contr_lookup_eq in H'.
    rewrite HΓx in H'.
    destruct (Δ x) as [[s' τ'] |]; discriminate.
  - destruct (Δ x) as [[s τ] |] eqn:HΔx; [| reflexivity].
    exfalso.
    assert (H' : prectx_contr p Γ Δ x = None).
    { apply (f_equal (fun Θ : prectx => Θ x) H). }
    rewrite prectx_contr_lookup_eq in H'.
    rewrite HΔx in H'.
    destruct (Γ x) as [[s' τ'] |]; discriminate.
Qed.

(** Contraction of compatible precontexts is commutative. *)
Lemma prectx_contr_comm (p : param) (Γ Δ : prectx) :
  prectx_comp Γ Δ -> 
  prectx_contr p Γ Δ = prectx_contr p Δ Γ.
Proof.
  intro H.
  apply prectx_ext; intro x.
  repeat rewrite prectx_contr_lookup_eq.
  specialize (H x).
  destruct (Γ x) as [[s1 τ1]|];
  destruct (Δ x) as [[s2 τ2]|].
  rewrite H with s1 τ1 s2 τ2.
  rewrite sens_pnorm_comm.
  all: reflexivity.
Qed.

(** Contraction of precontexts is associative. *)
Lemma prectx_contr_assoc (p : param) (Γ Δ Θ : prectx) :
  prectx_contr p Γ (prectx_contr p Δ Θ) =
  prectx_contr p (prectx_contr p Γ Δ) Θ.
Proof.
  intros.
  apply prectx_ext; intro x.
  repeat rewrite prectx_contr_lookup_eq.
  destruct (Γ x) as [[s1 τ1]|];
  destruct (Δ x) as [[s2 τ2]|];
  destruct (Θ x) as [[s3 τ3]|].
  rewrite sens_pnorm_assoc.
  all: reflexivity.
Qed.

Lemma prectx_scale_contr (p : param) (s : sens) (Γ Δ : prectx) :
  prectx_scale s (prectx_contr p Γ Δ) =
  prectx_contr p (prectx_scale s Γ) (prectx_scale s Δ).
Proof.
  apply prectx_ext; intro x.
  repeat rewrite prectx_scale_lookup.
  repeat rewrite prectx_contr_lookup_eq.
  repeat rewrite prectx_scale_lookup.
  destruct (Γ x) as [[r τr] |];
  destruct (Δ x) as [[t τt] |];
    try reflexivity.
  repeat f_equal.
  apply sens_mult_pnorm.
Qed.

Lemma prectx_contr_cons (p : param) (r s : sens) (τ : type)
  (Γ Δ : prectx) :
  prectx_contr p (prectx_cons (Some (r, τ)) Γ)
    (prectx_cons (Some (s, τ)) Δ) =
  prectx_cons (Some (sens_pnorm p r s, τ)) (prectx_contr p Γ Δ).
Proof.
  apply prectx_ext; intro x.
  destruct x; reflexivity.
Qed.

Lemma prectx_contr_le_l (p : param) (Γ Δ Θ : prectx)
  (x : var) (sΓ sΘ : sens) (τ : type) :
  prectx_le (prectx_contr p Γ Δ) Θ ->
  Γ x = Some (sΓ, τ) ->
  Θ x = Some (sΘ, τ) ->
  sens_le sΓ sΘ.
Proof.
  intros Hle HΓ HΘ.
  unfold prectx_le in Hle.
  destruct (Δ x) as [[sΔ τΔ] |] eqn:HΔ.
  - edestruct (Hle x (sens_pnorm p sΓ sΔ) τ) as [r [Hr Hpr]].
    { now rewrite prectx_contr_lookup_eq, HΓ, HΔ. }
    rewrite HΘ in Hr; injection Hr as [= <-].
    eapply sens_le_trans; [apply sens_pnorm_le_r | exact Hpr].
  - edestruct (Hle x sΓ τ) as [r [Hr Hpr]].
    { now rewrite prectx_contr_lookup_eq, HΓ, HΔ. }
    rewrite HΘ in Hr; injection Hr as [= <-].
    exact Hpr.
Qed.

(** If [x] is in [Γ], then it is also in [prectx_contr p Γ Δ],
    and with the same type. *)
Lemma prectx_contr_lookup (p : param) (Γ Δ : prectx)
  (x : var) (s : sens) (τ : type) :
  prectx_comp Γ Δ ->
  Γ x = Some (s, τ) ->
  exists s', prectx_contr p Γ Δ x = Some (s', τ).
Proof.
  intros Hcomp HΓ.
  rewrite prectx_contr_lookup_eq.
  rewrite HΓ.
  destruct (Δ x) as [[sΔ τΔ] |] eqn:HΔ.
  - specialize (Hcomp x s τ sΔ τΔ HΓ HΔ).
    subst τΔ.
    now exists (sens_pnorm p s sΔ).
  - now exists s.
Qed.

(** If [x] is in [Γ], then it is also in [Θ] with the same type,
    provided [Γ] is compatible with [Δ]
    and [prectx_contr p Γ Δ] is smaller than or equal to [Θ]. *)
Lemma prectx_contr_le_lookup (p : param) (Γ Δ Θ : prectx) :
  prectx_comp Γ Δ ->
  prectx_le (prectx_contr p Γ Δ) Θ ->
  forall x s τ, Γ x = Some (s, τ) ->
  exists s', Θ x = Some (s', τ).
Proof.
  intros Hcomp Hle x s τ HΓ.
  destruct (prectx_contr_lookup p Γ Δ x s τ Hcomp HΓ) as [s' Hcontr].
  destruct (Hle x s' τ Hcontr) as [s'' [HΘ _]].
  eauto.
Qed.

(** If [x] is in [Γ] and in [Θ] with the same type,
    then the scaled sensitivity of [x] in [Γ]
    is no greater than its sensitivity in [Θ]. *)
Lemma prectx_contr_scale_le_l (p : param) (s : sens) (Γ Δ Θ : prectx)
  (x : var) (sΓ sΘ : sens) (τ : type) :
  prectx_le (prectx_contr p (prectx_scale s Γ) Δ) Θ ->
  Γ x = Some (sΓ, τ) ->
  Θ x = Some (sΘ, τ) ->
  sens_le (sens_mult s sΓ) sΘ.
Proof.
  intros Hle HΓ HΘ.
  eapply prectx_contr_le_l with (p := p) (Γ := prectx_scale s Γ) (Δ := Δ) (Θ := Θ) (x := x) (τ := τ).
  - exact Hle.
  - rewrite prectx_scale_lookup.
    now rewrite HΓ.
  - exact HΘ.
Qed.

(** A context is the datum of a parameter and a precontext.
   In @FSCD2024, we write $(p) \; \Gamma$. *)
Definition ctx : Type := param * prectx.

Definition ctx_empty (p : param) : ctx := (p, prectx_empty).

Definition ctx_le (pΓ qΔ : ctx) : Prop :=
  let '(p, Γ) := pΓ in
  let '(q, Δ) := qΔ in
  param_le q p /\ prectx_le Γ Δ.

Lemma ctx_le_refl (pΓ : ctx) : ctx_le pΓ pΓ.
Proof.
  unfold ctx_le.
  destruct pΓ.
  split.
  - apply param_le_refl.
  - apply prectx_le_refl.
Qed.

(** ** Typing rules *)

Inductive has_type : ctx -> term -> type -> Prop :=
  | TUnit pΓ : has_type pΓ TmUnit (TyBase TyUnit)
  | TNat pΓ n : has_type pΓ (TmNat n) (TyBase TyNat)
  | TVar (p : param) (Γ : prectx) (τ : type) (s : sens) (x : var) :
      Γ x = Some (s, τ) -> sens_le sens_1 s ->
      has_type (p, Γ) (TmVar x) τ
  | TAbs p Γ t σ τ : has_type (p, prectx_cons (Some (sens_1, σ)) Γ) t τ ->
      has_type (p, Γ) (TmAbs t) (TyArrow p σ τ)
  | TApp p Γ Δ f t σ τ : prectx_comp Γ Δ ->
      has_type (p, Γ) f (TyArrow p σ τ) ->
      has_type (p, Δ) t σ ->
      has_type (p, prectx_contr p Γ Δ) (TmApp f t) τ
  | TPair p Γ Δ t1 t2 τ1 τ2 : prectx_comp Γ Δ ->
      has_type (p, Γ) t1 τ1 -> has_type (p, Δ) t2 τ2 ->
      has_type (p, prectx_contr p Γ Δ) (TmPair t1 t2) (TyPair p τ1 τ2)
  | TLetPair p Γ Δ tpair s t τ1 τ2 τ : prectx_comp Γ Δ ->
      has_type (p, Γ) tpair (TyPair p τ1 τ2) ->
      has_type (p, prectx_cons (Some (s, τ2))
        (prectx_cons (Some (s, τ1)) Δ)) t τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmLetPair tpair t) τ
  | TInjL pΓ t τ1 τ2 : has_type pΓ t τ1 ->
      has_type pΓ (TmInjL t) (TyPlus τ1 τ2)
  | TInjR pΓ t τ1 τ2 : has_type pΓ t τ2 ->
      has_type pΓ (TmInjR t) (TyPlus τ1 τ2)
  | TCase p Γ Δ t tl tr s τ1 τ2 τ : prectx_comp Γ Δ ->
      has_type (p, Γ) t (TyPlus τ1 τ2) ->
      has_type (p, prectx_cons (Some (s, τ1)) Δ) tl τ ->
      has_type (p, prectx_cons (Some (s, τ2)) Δ) tr τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmCase t tl tr) τ
  | TBang p Γ Δ t τ s : prectx_comp Γ Δ ->
      has_type (p, Γ) t τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmBang t) (TyBang s τ)
  | TLetBang p Γ Δ t1 t2 τ1 τ r s : prectx_comp Γ Δ ->
      has_type (p, Γ) t1 (TyBang r τ1) ->
      has_type (p, prectx_cons (Some (sens_mult r s, τ1)) Δ) t2 τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmLetBang t1 t2) τ
  | TFold pΓ t τ : has_type pΓ t (τ.[TyRec τ/]) ->
      has_type pΓ (TmFold (TyRec τ) t) (TyRec τ)
  | TUnfold pΓ t τ : has_type pΓ t (TyRec τ) ->
      has_type pΓ (TmUnfold (TyRec τ) t) (τ.[TyRec τ/])
  | TWeakGt p q Γ t τ : has_type (p, Γ) t τ -> param_lt q p ->
      has_type (q, Γ) t τ
  | TWeakLt p q Γ Δ t τ :
      has_type (p, Γ) t τ ->
      prectx_le Γ Δ ->
      param_le p q ->
      has_type
        (q, prectx_scale (sens_dim_factor Γ p q) Δ) t τ.

Example has_type_true : forall (pΓ : ctx), has_type pΓ TmTrue TyBool.
Proof.
  intro p.
  unfold TmTrue.
  apply TInjL.
  apply TUnit.
Qed.

Example has_type_nil (p : param) (Γ : prectx) (τ : type) :
  has_type (p, Γ) (TmNil p τ) (TyList p τ).
Proof.
  unfold TmNil.
  apply TFold.
  pose proof (TyList_unfold p τ) as Hunfold.
  unfold TyList in Hunfold.
  rewrite Hunfold.
  apply TInjL.
  apply TUnit.
Qed.

Example has_type_closed_cons (p : param) (τ : type) (vhead vtail : term) :
  has_type (p, prectx_empty) vhead τ ->
  has_type (p, prectx_empty) vtail (TyList p τ) ->
  has_type (p, prectx_empty) (TmCons p τ vhead vtail) (TyList p τ).
Proof.
  intros Hhead Htail.
  unfold TmCons.
  apply TFold.
  pose proof (TyList_unfold p τ) as Hunfold.
  unfold TyList in Hunfold.
  rewrite Hunfold.
  apply TInjR.
  rewrite <- (prectx_contr_empty_l p prectx_empty).
  apply TPair.
  - apply prectx_comp_refl.
  - exact Hhead.
  - exact Htail.
Qed.

Example has_type_unfold_nil (p : param) (Γ : prectx) (τ : type) :
  has_type
    (p, Γ)
    (TmUnfold (TyList p τ) (TmNil p τ))
    (TyPlus (TyBase TyUnit) (TyPair p τ (TyList p τ))).
Proof.
  rewrite <- TyList_unfold.
  apply TUnfold.
  apply has_type_nil.
Qed.

(** For all types $τ$, we can derive
    $(2) \; x :_sqrt(2) τ ⊢ (x, x) : τ ⊗_2 τ$. *)
Example has_type_pair2 (τ : type) :
  has_type (param_2, prectx_cons (Some (sens_sqrt2, τ)) prectx_empty)
  (TmPair (TmVar 0%nat) (TmVar 0%nat)) (TyPair param_2 τ τ).
Proof.
  remember (prectx_cons (Some (sens_1, τ)) prectx_empty) as Γ1.
  remember (prectx_cons (Some (sens_sqrt2, τ)) prectx_empty) as Γ2.
  assert (prectx_contr param_2 Γ1 Γ1 = Γ2).
  - apply prectx_ext; intro x.
    rewrite prectx_contr_lookup_eq.
    destruct x; rewrite HeqΓ1, HeqΓ2; simpl; auto.
    rewrite <- sens_2norm_1_1.
    now unfold sens_pnorm.
  - rewrite <- H.
    assert (has_type (param_2, Γ1) (TmVar 0%nat) τ).
    + apply TVar with sens_1.
      * now rewrite HeqΓ1.
      * apply sens_le_refl.
    + apply TPair; try easy.
      apply prectx_comp_refl.
Qed.

(** ** Big-step operational semantics *)

Inductive is_value : term -> Prop :=
  | ValBase b : is_value (TmBase b)
  | ValAbs t : is_value (TmAbs t)
  | ValPair v1 v2 : is_value v1 -> is_value v2 -> is_value (TmPair v1 v2)
  | ValInjL v : is_value v -> is_value (TmInjL v)
  | ValInjR v : is_value v -> is_value (TmInjR v)
  | ValBang v : is_value v -> is_value (TmBang v)
  | ValFold τ v : is_value v -> is_value (TmFold τ v).

Lemma is_value_true : is_value TmTrue.
Proof.
  apply ValInjL.
  apply ValBase.
Qed.

Lemma is_value_false : is_value TmFalse.
Proof.
  apply ValInjR.
  apply ValBase.
Qed.

Inductive evals_to : term -> term -> Prop :=
  | EvBase t : evals_to (TmBase t) (TmBase t)
  | EvAbs t : evals_to (TmAbs t) (TmAbs t)
  | EvApp f a tbody v va :
      evals_to f (TmAbs tbody) ->
      evals_to a va ->
      evals_to (tbody.[va/]) v ->
      evals_to (TmApp f a) v
  | EvPair t1 t2 v1 v2 : evals_to t1 v1 -> evals_to t2 v2 ->
      evals_to (TmPair t1 t2) (TmPair v1 v2)
  | EvLetPair t tbody v1 v2 v :
      evals_to t (TmPair v1 v2) ->
      evals_to (tbody.[v2 .: v1 .: ids]) v ->
      evals_to (TmLetPair t tbody) v
  | EvInjL t v : evals_to t v -> evals_to (TmInjL t) (TmInjL v)
  | EvInjR t v : evals_to t v -> evals_to (TmInjR t) (TmInjR v)
  | EvCaseL t tl tr v_inj v :
      evals_to t (TmInjL v_inj) ->
      evals_to (tl.[v_inj/]) v ->
      evals_to (TmCase t tl tr) v
  | EvCaseR t tl tr v_inj v :
      evals_to t (TmInjR v_inj) ->
      evals_to (tr.[v_inj/]) v ->
      evals_to (TmCase t tl tr) v
  | EvBang t v : evals_to t v -> evals_to (TmBang t) (TmBang v)
  | EvLetBang t tbody v_bang v :
      evals_to t (TmBang v_bang) ->
      evals_to (tbody.[v_bang/]) v ->
      evals_to (TmLetBang t tbody) v
  | EvFold τ t v :
      evals_to t v ->
      evals_to (TmFold τ t) (TmFold τ v)
  | EvUnfold τ t v :
      evals_to t (TmFold τ v) ->
      evals_to (TmUnfold τ t) v.

Ltac step_eval := eauto || (asimpl; eauto) || econstructor.

Example eval_id_nat :
  let TmIdNat := TmAbs  (TmVar 0%nat) in
  forall (n : nat),
  evals_to (TmApp TmIdNat (TmNat n)) (TmNat n).
Proof.
  intros id n.
  repeat step_eval.
Qed.

Example eval_swap_nat (m n : nat) :
  let pair l r : term := TmPair (TmNat l) (TmNat r) in
  evals_to (TmApp TmSwap (pair m n)) (pair n m).
Proof.
  intros.
  unfold TmSwap.
  repeat step_eval.
Qed.

Example eval_unfold_nil (p : param) (τ : type) :
  evals_to
    (TmUnfold (TyList p τ) (TmNil p τ))
    (TmInjL TmUnit).
Proof.
  unfold TmNil.
  repeat step_eval.
Qed.

Lemma evals_to_is_value t v : evals_to t v -> is_value v.
Proof.
  intros H; induction H.
  all: eauto using is_value.
  inversion IHevals_to; assumption.
Qed.

(** ** Metatheory *)

(** *** Weakening *)

(** Pointwise weakening is the reflexive-parameter instance of [W_dim]. *)
Lemma weakening_prectx pΓ t τ (H : has_type pΓ t τ) :
  match pΓ with
  | (p, Γ) => forall Δ, prectx_le Γ Δ -> has_type (p, Δ) t τ
  end.
Proof.
  destruct pΓ as [p Γ].
  intros Δ Hle.
  rewrite <- (prectx_scale_1 Δ).
  rewrite <- (sens_dim_factor_refl Γ p).
  eapply TWeakLt.
  - exact H.
  - exact Hle.
  - apply param_le_refl.
Qed.

(** The weakening rule for contexts is admissible. *)
Theorem weakening_ctx p Γ t τ : has_type (p, Γ) t τ ->
  forall q Δ, param_le q p -> prectx_le Γ Δ ->
  has_type (q, Δ) t τ.
Proof.
  intros H q Δ Hpq Hle.
  destruct Hpq as [Hlt | ->]; [apply TWeakGt with p; trivial |].
  all: now apply (weakening_prectx (p, Γ)).
Qed.

(** *** Inversion *)

Inductive ctx_struct : ctx -> ctx -> Prop :=
  | StructRefl pΓ :
      ctx_struct pΓ pΓ
  | StructGt p q Γ :
      param_lt q p -> ctx_struct (p, Γ) (q, Γ)
  | StructDim p q Γ Δ :
      prectx_le Γ Δ ->
      param_le p q ->
      ctx_struct (p, Γ)
        (q, prectx_scale (sens_dim_factor Γ p q) Δ)
  | StructTrans pΓ1 pΓ2 pΓ3 :
      ctx_struct pΓ1 pΓ2 -> ctx_struct pΓ2 pΓ3 -> ctx_struct pΓ1 pΓ3.

Lemma ctx_struct_none_inv pΓ1 pΓ2 :
  ctx_struct pΓ1 pΓ2 ->
  forall x,
    (snd pΓ2) x = None -> (snd pΓ1) x = None.
Proof.
  intros H.
  induction H; intros x Hnone.
  - exact Hnone.
  - exact Hnone.
  - destruct (Γ x) as [[s τ] |] eqn:HΓ; [| exact HΓ].
    destruct (H x s τ HΓ) as [sΔ [HΔ _]].
    change (prectx_scale (sens_dim_factor Γ p q) Δ x = None) in Hnone.
    rewrite prectx_scale_lookup, HΔ in Hnone.
    discriminate.
  - apply (IHctx_struct1 x), (IHctx_struct2 x), Hnone.
Qed.

Lemma ctx_struct_empty_inv p Γ q :
  ctx_struct (p, Γ) (q, prectx_empty) ->
  Γ = prectx_empty.
Proof.
  intros H.
  apply prectx_ext; intro x.
  apply (ctx_struct_none_inv (p, Γ) (q, prectx_empty) H x).
  reflexivity.
Qed.

Lemma has_type_struct pΓ1 pΓ2 t τ :
  ctx_struct pΓ1 pΓ2 -> has_type pΓ1 t τ -> has_type pΓ2 t τ.
Proof.
  intros Hstep; revert t τ.
  induction Hstep; intros t τ Htype; eauto using TWeakGt, TWeakLt.
Qed.

Ltac solve_inv_struct IH Heq Rule :=
  specialize (IH Heq);
  repeat match type of IH with
  | exists _, _ => destruct IH as [? IH]
  | _ /\ _ => destruct IH as [? IH]
  end;
  subst;
  repeat eexists; repeat split; eauto;
  eapply StructTrans; [ exact IH | apply Rule; assumption ].

Lemma inversion_TmBase pΓ b τ :
  has_type pΓ (TmBase b) τ ->
  match b with
  | ValUnit => τ = TyBase TyUnit
  | ValNat _ => τ = TyBase TyNat
  end.
Proof.
  intros H; remember (TmBase b) as t_base.
  induction H; try discriminate Heqt_base.
  - injection Heqt_base as [= <-]. reflexivity.
  - injection Heqt_base as [= <-]. reflexivity.
  - now apply IHhas_type.
  - now apply IHhas_type.
Qed.

Lemma inversion_TmUnit pΓ τ :
  has_type pΓ TmUnit τ ->
  τ = TyBase TyUnit.
Proof.
  apply inversion_TmBase.
Qed.

Lemma inversion_TmNat pΓ n τ :
  has_type pΓ (TmNat n) τ ->
  τ = TyBase TyNat.
Proof.
  apply inversion_TmBase.
Qed.

Lemma inversion_TmVar pΓ x τ :
  has_type pΓ (TmVar x) τ ->
  exists (p' : param) (Γ' : prectx) (s' : sens),
    Γ' x = Some (s', τ) /\
    sens_le sens_1 s' /\
    ctx_struct (p', Γ') pΓ.
Proof.
  intros H; remember (TmVar x) as t_var.
  induction H; try discriminate Heqt_var.
  - injection Heqt_var as [= ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_var StructGt.
  - solve_inv_struct IHhas_type Heqt_var StructDim.
Qed.

Lemma inversion_TmAbs pΓ t τ :
  has_type pΓ (TmAbs t) τ ->
  exists (p' : param) (Γ' : prectx) (σ' τ' : type),
    τ = TyArrow p' σ' τ' /\
    has_type (p', prectx_cons (Some (sens_1, σ')) Γ') t τ' /\
    ctx_struct (p', Γ') pΓ.
Proof.
  intros H; remember (TmAbs t) as t_abs.
  induction H; try discriminate Heqt_abs.
  - injection Heqt_abs as [= ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_abs StructGt.
  - solve_inv_struct IHhas_type Heqt_abs StructDim.
Qed.

Lemma inversion_TmApp pΓ f t τ :
  has_type pΓ (TmApp f t) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (σ' : type),
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') f (TyArrow p' σ' τ) /\
    has_type (p', Δ') t σ' /\
    ctx_struct (p', prectx_contr p' Γ' Δ') pΓ.
Proof.
  intros H; remember (TmApp f t) as t_app.
  induction H; try discriminate Heqt_app.
  - injection Heqt_app as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_app StructGt.
  - solve_inv_struct IHhas_type Heqt_app StructDim.
Qed.

Lemma inversion_TmPair pΓ t1 t2 τ :
  has_type pΓ (TmPair t1 t2) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (τ1' τ2' : type),
    τ = TyPair p' τ1' τ2' /\
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t1 τ1' /\
    has_type (p', Δ') t2 τ2' /\
    ctx_struct (p', prectx_contr p' Γ' Δ') pΓ.
Proof.
  intros H; remember (TmPair t1 t2) as t_pair.
  induction H; try discriminate Heqt_pair.
  - injection Heqt_pair as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_pair StructGt.
  - solve_inv_struct IHhas_type Heqt_pair StructDim.
Qed.

Lemma inversion_TmLetPair pΓ tpair t τ :
  has_type pΓ (TmLetPair tpair t) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (s' : sens) (τ1' τ2' : type),
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') tpair (TyPair p' τ1' τ2') /\
    has_type (p', prectx_cons (Some (s', τ2'))
      (prectx_cons (Some (s', τ1')) Δ')) t τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmLetPair tpair t) as t_letpair.
  induction H; try discriminate Heqt_letpair.
  - injection Heqt_letpair as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_letpair StructGt.
  - solve_inv_struct IHhas_type Heqt_letpair StructDim.
Qed.

Lemma inversion_TmInjL pΓ t τ :
  has_type pΓ (TmInjL t) τ ->
  exists τ1' τ2',
    τ = TyPlus τ1' τ2' /\
    has_type pΓ t τ1'.
Proof.
  intros H; remember (TmInjL t) as t_injl.
  induction H; try discriminate Heqt_injl.
  - injection Heqt_injl as [= ->].
    repeat eexists; eauto.
  - destruct (IHhas_type Heqt_injl) as [τ1' [τ2' [-> Htype]]].
    eexists; eexists; split; eauto.
    eapply TWeakGt; eauto.
  - destruct (IHhas_type Heqt_injl) as [τ1' [τ2' [-> Htype]]].
    eexists; eexists; split; eauto.
    eapply TWeakLt; eauto.
Qed.

Lemma inversion_TmInjR pΓ t τ :
  has_type pΓ (TmInjR t) τ ->
  exists τ1' τ2',
    τ = TyPlus τ1' τ2' /\
    has_type pΓ t τ2'.
Proof.
  intros H; remember (TmInjR t) as t_injr.
  induction H; try discriminate Heqt_injr.
  - injection Heqt_injr as [= ->].
    repeat eexists; eauto.
  - destruct (IHhas_type Heqt_injr) as [τ1' [τ2' [-> Htype]]].
    eexists; eexists; split; eauto.
    eapply TWeakGt; eauto.
  - destruct (IHhas_type Heqt_injr) as [τ1' [τ2' [-> Htype]]].
    eexists; eexists; split; eauto.
    eapply TWeakLt; eauto.
Qed.

Lemma inversion_TmCase pΓ t tl tr τ :
  has_type pΓ (TmCase t tl tr) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (s' : sens) (τ1' τ2' : type),
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t (TyPlus τ1' τ2') /\
    has_type (p', prectx_cons (Some (s', τ1')) Δ') tl τ /\
    has_type (p', prectx_cons (Some (s', τ2')) Δ') tr τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmCase t tl tr) as t_case.
  induction H; try discriminate Heqt_case.
  - injection Heqt_case as [= -> -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_case StructGt.
  - solve_inv_struct IHhas_type Heqt_case StructDim.
Qed.

Lemma inversion_TmBang pΓ t τ :
  has_type pΓ (TmBang t) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (τ' : type) (s' : sens),
    τ = TyBang s' τ' /\
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t τ' /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmBang t) as t_bang.
  induction H; try discriminate Heqt_bang.
  - injection Heqt_bang as [= ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_bang StructGt.
  - solve_inv_struct IHhas_type Heqt_bang StructDim.
Qed.

Lemma inversion_TmLetBang pΓ t1 t2 τ :
  has_type pΓ (TmLetBang t1 t2) τ ->
  exists (p' : param) (Γ' Δ' : prectx) (τ1' : type) (r' s' : sens),
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t1 (TyBang r' τ1') /\
    has_type (p', prectx_cons (Some (sens_mult r' s', τ1')) Δ') t2 τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmLetBang t1 t2) as t_letbang.
  induction H; try discriminate Heqt_letbang.
  - injection Heqt_letbang as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_letbang StructGt.
  - solve_inv_struct IHhas_type Heqt_letbang StructDim.
Qed.

Lemma inversion_TmFold pΓ rec_ty t τ :
  has_type pΓ (TmFold rec_ty t) τ ->
  exists body,
    rec_ty = TyRec body /\
    τ = TyRec body /\
    has_type pΓ t (body.[TyRec body/]).
Proof.
  intros H; remember (TmFold rec_ty t) as t_fold.
  induction H; try discriminate Heqt_fold.
  - injection Heqt_fold as [= Hrec Hterm].
    subst.
    repeat eexists; eauto.
  - destruct (IHhas_type Heqt_fold)
      as [body [Hrec [Hτ Htype]]].
    exists body; repeat split; eauto using TWeakGt.
  - destruct (IHhas_type Heqt_fold)
      as [body [Hrec [Hτ Htype]]].
    exists body; repeat split; eauto using TWeakLt.
Qed.

Lemma inversion_TmUnfold pΓ rec_ty t τ :
  has_type pΓ (TmUnfold rec_ty t) τ ->
  exists body,
    rec_ty = TyRec body /\
    τ = body.[TyRec body/] /\
    has_type pΓ t (TyRec body).
Proof.
  intros H; remember (TmUnfold rec_ty t) as t_unfold.
  induction H; try discriminate Heqt_unfold.
  - injection Heqt_unfold as [= Hrec Hterm].
    subst.
    repeat eexists; eauto.
  - destruct (IHhas_type Heqt_unfold)
      as [body [Hrec [Hτ Htype]]].
    exists body; repeat split; eauto using TWeakGt.
  - destruct (IHhas_type Heqt_unfold)
      as [body [Hrec [Hτ Htype]]].
    exists body; repeat split; eauto using TWeakLt.
Qed.

Lemma closed_contr_inv p Γ Δ q :
  ctx_struct (p, prectx_contr p Γ Δ) (q, prectx_empty) ->
  Γ = prectx_empty /\
  Δ = prectx_empty /\
  ctx_struct (p, prectx_empty) (q, prectx_empty).
Proof.
  intro Hstruct.
  assert (Hcontr : prectx_contr p Γ Δ = prectx_empty).
  { eapply ctx_struct_empty_inv; exact Hstruct. }
  destruct (prectx_contr_empty_inv p Γ Δ Hcontr) as [-> ->].
  repeat split; try reflexivity.
  rewrite Hcontr in Hstruct.
  exact Hstruct.
Qed.

Lemma closed_scale_contr_inv p s Γ Δ q :
  ctx_struct (p, prectx_contr p (prectx_scale s Γ) Δ) (q, prectx_empty) ->
  Γ = prectx_empty /\
  Δ = prectx_empty /\
  ctx_struct (p, prectx_empty) (q, prectx_empty).
Proof.
  intro Hstruct.
  assert (Hcontr :
    prectx_contr p (prectx_scale s Γ) Δ = prectx_empty).
  { eapply ctx_struct_empty_inv; exact Hstruct. }
  destruct (prectx_contr_empty_inv p (prectx_scale s Γ) Δ Hcontr)
    as [Hscale ->].
  assert (HΓ : Γ = prectx_empty).
  { eapply prectx_scale_empty_inv; exact Hscale. }
  subst Γ.
  repeat split; try reflexivity.
  rewrite Hcontr in Hstruct.
  exact Hstruct.
Qed.

Lemma inversion_closed_TmApp p f t τ :
  has_type (p, prectx_empty) (TmApp f t) τ ->
  exists p' σ,
    has_type (p', prectx_empty) f (TyArrow p' σ τ) /\
    has_type (p', prectx_empty) t σ /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmApp (p, prectx_empty) f t τ H)
    as [p' [Γ' [Δ' [σ' [Hcomp [Hf [Ht Hstruct]]]]]]].
  destruct (closed_contr_inv p' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Hf.
  - exact Ht.
  - exact Hstruct'.
Qed.

Lemma inversion_closed_TmPair p t1 t2 τ :
  has_type (p, prectx_empty) (TmPair t1 t2) τ ->
  exists p' τ1 τ2,
    τ = TyPair p' τ1 τ2 /\
    has_type (p', prectx_empty) t1 τ1 /\
    has_type (p', prectx_empty) t2 τ2 /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmPair (p, prectx_empty) t1 t2 τ H)
    as [p' [Γ' [Δ' [τ1' [τ2' [Hτ [Hcomp [Ht1 [Ht2 Hstruct]]]]]]]]].
  destruct (closed_contr_inv p' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Hτ.
  - exact Ht1.
  - exact Ht2.
  - exact Hstruct'.
Qed.

Lemma inversion_closed_TmLetPair p tpair tbody τ :
  has_type (p, prectx_empty) (TmLetPair tpair tbody) τ ->
  exists p' s τ1 τ2,
    has_type
      (p', prectx_empty)
      tpair
      (TyPair p' τ1 τ2) /\
    has_type
      (p',
        prectx_cons (Some (s, τ2))
          (prectx_cons (Some (s, τ1)) prectx_empty))
      tbody τ /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmLetPair (p, prectx_empty) tpair tbody τ H)
    as [p' [Γ' [Δ' [s' [τ1' [τ2' [Hcomp [Hpair [Hbody Hstruct]]]]]]]]].
  destruct (closed_scale_contr_inv p' s' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Hpair.
  - exact Hbody.
  - exact Hstruct'.
Qed.

Lemma inversion_closed_TmCase p t tl tr τ :
  has_type (p, prectx_empty) (TmCase t tl tr) τ ->
  exists p' s τ1 τ2,
    has_type
      (p', prectx_empty)
      t
      (TyPlus τ1 τ2) /\
    has_type
      (p', prectx_cons (Some (s, τ1)) prectx_empty)
      tl τ /\
    has_type
      (p', prectx_cons (Some (s, τ2)) prectx_empty)
      tr τ /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmCase (p, prectx_empty) t tl tr τ H)
    as [p' [Γ' [Δ' [s' [τ1' [τ2' [Hcomp [Ht [Htl [Htr Hstruct]]]]]]]]]].
  destruct (closed_scale_contr_inv p' s' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Ht.
  - exact Htl.
  - exact Htr.
  - exact Hstruct'.
Qed.

Lemma inversion_closed_TmBang p t τ :
  has_type (p, prectx_empty) (TmBang t) τ ->
  exists p' s σ,
    τ = TyBang s σ /\
    has_type (p', prectx_empty) t σ /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmBang (p, prectx_empty) t τ H)
    as [p' [Γ' [Δ' [τ' [s' [Hτ [Hcomp [Ht Hstruct]]]]]]]].
  destruct (closed_scale_contr_inv p' s' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Hτ.
  - exact Ht.
  - exact Hstruct'.
Qed.

Lemma inversion_closed_TmLetBang p t tbody τ :
  has_type (p, prectx_empty) (TmLetBang t tbody) τ ->
  exists p' r s σ,
    has_type
      (p', prectx_empty)
      t
      (TyBang r σ) /\
    has_type
      (p',
        prectx_cons (Some (sens_mult r s, σ)) prectx_empty)
      tbody τ /\
    ctx_struct
      (p', prectx_empty)
      (p, prectx_empty).
Proof.
  intros H.
  destruct (inversion_TmLetBang (p, prectx_empty) t tbody τ H)
    as [p' [Γ' [Δ' [τ1' [r' [s' [Hcomp [Ht [Hbody Hstruct]]]]]]]]].
  destruct (closed_scale_contr_inv p' s' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  repeat eexists; repeat split.
  - exact Ht.
  - exact Hbody.
  - exact Hstruct'.
Qed.

Lemma has_type_closed_pair p v1 v2 τ1 τ2 :
  has_type (p, prectx_empty) v1 τ1 ->
  has_type (p, prectx_empty) v2 τ2 ->
  has_type (p, prectx_empty) (TmPair v1 v2) (TyPair p τ1 τ2).
Proof.
  intros Hv1 Hv2.
  rewrite <- (prectx_contr_empty_l p prectx_empty).
  apply TPair.
  - apply prectx_comp_refl.
  - exact Hv1.
  - exact Hv2.
Qed.

Lemma has_type_closed_bang p v s σ :
  has_type (p, prectx_empty) v σ ->
  has_type (p, prectx_empty) (TmBang v) (TyBang s σ).
Proof.
  intro Hv.
  rewrite <- (prectx_scale_empty s).
  rewrite <- (prectx_contr_empty_r p (prectx_scale s prectx_empty)).
  apply TBang.
  - apply prectx_comp_refl.
  - exact Hv.
Qed.

Lemma inversion_closed_abs_value p tbody σ τ :
  has_type
    (p, prectx_empty)
    (TmAbs tbody)
    (TyArrow p σ τ) ->
  has_type
    (p, prectx_cons (Some (sens_1, σ)) prectx_empty)
    tbody τ.
Proof.
  intros H.
  destruct (inversion_TmAbs (p, prectx_empty) tbody (TyArrow p σ τ) H)
    as [p' [Γ' [σ' [τ' [Hτ [Hbody Hstruct]]]]]].
  assert (HΓ' : Γ' = prectx_empty).
  { eapply ctx_struct_empty_inv; exact Hstruct. }
  subst Γ'.
  injection Hτ as [= <- <- <-].
  exact Hbody.
Qed.

Lemma inversion_closed_pair_value p v1 v2 τ1 τ2 :
  has_type
    (p, prectx_empty)
    (TmPair v1 v2)
    (TyPair p τ1 τ2) ->
  has_type (p, prectx_empty) v1 τ1 /\
  has_type (p, prectx_empty) v2 τ2.
Proof.
  intros H.
  destruct (inversion_TmPair (p, prectx_empty) v1 v2 (TyPair p τ1 τ2) H)
    as [p' [Γ' [Δ' [τ1' [τ2' [Hτ [Hcomp [Hv1 [Hv2 Hstruct]]]]]]]]].
  destruct (closed_contr_inv p' Γ' Δ' p Hstruct)
    as [-> [-> _]].
  injection Hτ as [= <- <- <-].
  split; assumption.
Qed.

Lemma inversion_closed_injl_value p v τ1 τ2 :
  has_type
    (p, prectx_empty)
    (TmInjL v)
    (TyPlus τ1 τ2) ->
  has_type (p, prectx_empty) v τ1.
Proof.
  intros H.
  destruct (inversion_TmInjL (p, prectx_empty) v (TyPlus τ1 τ2) H)
    as [τ1' [τ2' [Hτ Hv]]].
  injection Hτ as [= <- <-].
  exact Hv.
Qed.

Lemma inversion_closed_injr_value p v τ1 τ2 :
  has_type
    (p, prectx_empty)
    (TmInjR v)
    (TyPlus τ1 τ2) ->
  has_type (p, prectx_empty) v τ2.
Proof.
  intros H.
  destruct (inversion_TmInjR (p, prectx_empty) v (TyPlus τ1 τ2) H)
    as [τ1' [τ2' [Hτ Hv]]].
  injection Hτ as [= <- <-].
  exact Hv.
Qed.

Lemma inversion_closed_bang_value p v r σ :
  has_type
    (p, prectx_empty)
    (TmBang v)
    (TyBang r σ) ->
  has_type (p, prectx_empty) v σ.
Proof.
  intros H.
  destruct (inversion_TmBang (p, prectx_empty) v (TyBang r σ) H)
    as [p' [Γ' [Δ' [τ' [s' [Hτ [Hcomp [Hv Hstruct]]]]]]]].
  destruct (closed_scale_contr_inv p' s' Γ' Δ' p Hstruct)
    as [-> [-> Hstruct']].
  injection Hτ as [= <- <-].
  eapply has_type_struct; eauto.
Qed.

(** *** Renaming *)

Definition is_injective (ξ : var -> var) : Prop :=
  forall x y, ξ x = ξ y -> x = y.

Lemma is_injective_up (ξ : var -> var) :
  is_injective ξ -> is_injective (0%nat .: ξ >>> (+1%nat)).
Proof.
  intros Hinj [|x] [|y] Heq; asimpl in Heq.
  - reflexivity.
  - discriminate.
  - discriminate.
  - f_equal.
    apply Hinj.
    now injection Heq.
Qed.

Definition is_pushforward (ξ : var -> var) (Γ Δ : prectx) : Prop :=
  (forall x, Γ x = Δ (ξ x)) /\
  (forall y, (forall x, ξ x <> y) -> Δ y = None).

Lemma is_pushforward_up (ξ : var -> var) Γ Δ v :
  is_pushforward ξ Γ Δ ->
  is_pushforward (0%nat .: ξ >>> (+1%nat))
    (prectx_cons v Γ) (prectx_cons v Δ).
Proof.
  intros [Heq Hnone]. split.
  - intros [|x]; now asimpl.
  - intros [|y] Hy; asimpl.
    + exfalso.
      now apply (Hy 0%nat).
    + apply Hnone.
      intros x Hx.
      apply (Hy (S x)).
      asimpl.
      now f_equal.
Qed.

Lemma is_injective_up2 (ξ : var -> var) :
  is_injective ξ ->
  is_injective (0%nat .: 1%nat .: ξ >>> (+2%nat)).
Proof.
  intro Hinj.
  pose proof
    (is_injective_up
       (0%nat .: ξ >>> (+1%nat))
       (is_injective_up ξ Hinj))
    as Hup.
  asimpl in Hup.
  exact Hup.
Qed.

Lemma is_pushforward_up2
  (ξ : var -> var) (Γ Δ : prectx)
  (v0 v1 : option (sens * type)) :
  is_pushforward ξ Γ Δ ->
  is_pushforward
    (0%nat .: 1%nat .: ξ >>> (+2%nat))
    (prectx_cons v0 (prectx_cons v1 Γ))
    (prectx_cons v0 (prectx_cons v1 Δ)).
Proof.
  intro Hpf.
  pose proof
    (is_pushforward_up
       (0%nat .: ξ >>> (+1%nat))
       (prectx_cons v1 Γ) (prectx_cons v1 Δ) v0
       (is_pushforward_up ξ Γ Δ v1 Hpf))
    as Hup.
  asimpl in Hup.
  exact Hup.
Qed.

Lemma pushforward_inv (ξ : var -> var) Γ Δ y v :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  Δ y = Some v ->
  exists! x, ξ x = y /\ Γ x = Some v.
Proof.
  intros Hinj [Hpf_eq Hpf_none] Hy.
  apply NNPP.
  intro Hnot.
  assert (Hempty : forall x, ξ x <> y).
  - intros x Hx.
    apply Hnot.
    exists x; repeat split; auto.
    + now rewrite Hpf_eq, Hx.
    + intros x' Hx'.
      apply Hinj.
      destruct Hx'; congruence.
  - apply Hpf_none in Hempty.
    congruence.
Qed.

Lemma pushforward_comp (ξ : var -> var) Γ1 Γ2 Δ1 Δ2 :
  is_injective ξ ->
  is_pushforward ξ Γ1 Δ1 ->
  is_pushforward ξ Γ2 Δ2 ->
  prectx_comp Γ1 Γ2 ->
  prectx_comp Δ1 Δ2.
Proof.
  intros Hinj Hpf1 Hpf2 Hcomp y s1 τ1 s2 τ2 HΔ1 HΔ2.
  destruct (pushforward_inv ξ Γ1 Δ1 y (s1, τ1) Hinj Hpf1 HΔ1) as [x1 [Hx1 HΓ1]].
  destruct (pushforward_inv ξ Γ2 Δ2 y (s2, τ2) Hinj Hpf2 HΔ2) as [x2 [Hx2 HΓ2]].
  assert (x1 = x2); destruct Hx1, Hx2.
  - apply Hinj; congruence.
  - subst x2; eapply Hcomp; eauto.
Qed.

Lemma pushforward_le (ξ : var -> var) Γ Δ Γ' Δ' :
  is_injective ξ ->
  is_pushforward ξ Γ Γ' ->
  is_pushforward ξ Δ Δ' ->
  prectx_le Γ Δ ->
  prectx_le Γ' Δ'.
Proof.
  intros Hinj HΓ HΔ Hle y s τ Hy.
  destruct (pushforward_inv ξ Γ Γ' y (s, τ) Hinj HΓ Hy)
    as [x [[Hxy Hx] _]].
  destruct (Hle x s τ Hx) as [sΔ [HxΔ Hsens]].
  exists sΔ; split; [| exact Hsens].
  rewrite <- Hxy, <- (proj1 HΔ x).
  exact HxΔ.
Qed.

Lemma pushforward_scale (ξ : var -> var) (s : sens) (Γ Δ : prectx) :
  is_pushforward ξ Γ Δ ->
  is_pushforward ξ (prectx_scale s Γ) (prectx_scale s Δ).
Proof.
  intros [Heq Hnone]. split.
  - intro x.
    repeat rewrite prectx_scale_lookup.
    now rewrite Heq.
  - intros y Hy.
    rewrite prectx_scale_lookup.
    now rewrite Hnone.
Qed.

Lemma pushforward_contr (ξ : var -> var) p Γ1 Γ2 Δ1 Δ2 :
  is_pushforward ξ Γ1 Δ1 ->
  is_pushforward ξ Γ2 Δ2 ->
  is_pushforward ξ (prectx_contr p Γ1 Γ2) (prectx_contr p Δ1 Δ2).
Proof.
  intros [Hpf1_eq Hpf1_none] [Hpf2_eq Hpf2_none].
  split; intros.
  - repeat rewrite prectx_contr_lookup_eq.
    now rewrite Hpf1_eq, Hpf2_eq.
  - rewrite prectx_contr_lookup_eq.
    now rewrite Hpf1_none, Hpf2_none.
Qed.

Lemma pushforward_unique (ξ : var -> var) Γ Δ1 Δ2 :
  is_pushforward ξ Γ Δ1 ->
  is_pushforward ξ Γ Δ2 ->
  Δ1 = Δ2.
Proof.
  intros [Heq1 Hnone1] [Heq2 Hnone2].
  apply prectx_ext; intro y.
  destruct (classic (exists x, ξ x = y)) as [[x Hx] | Hx].
  - subst y.
    now rewrite <- (Heq1 x), <- (Heq2 x).
  - assert (Hy : forall x, ξ x <> y).
    { intros x Heq. apply Hx. now exists x. }
    now rewrite (Hnone1 y Hy), (Hnone2 y Hy).
Qed.

Lemma pushforward_dom (ξ : var -> var) Γ Δ :
  is_pushforward ξ Γ Δ ->
  prectx_dom Δ = Im var var (prectx_dom Γ) ξ.
Proof.
  intros [Heq Hnone].
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct (classic (exists x, ξ x = y)) as [[x Hxy] | Habsent].
    + subst y.
      apply Im_intro with x; [| reflexivity].
      unfold prectx_dom, prectx_support in *.
      intro HΓnone.
      apply Hy.
      now rewrite <- (Heq x).
    + exfalso.
      apply Hy, Hnone.
      intros x Hxy.
      apply Habsent.
      now exists x.
  - inversion Hy as [x Hx y' Hxy].
    unfold prectx_dom, prectx_support in *.
    intro HΔnone.
    apply Hx.
    rewrite (Heq x), <- Hxy.
    exact HΔnone.
Qed.

Lemma pushforward_card (ξ : var -> var) Γ Δ :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  prectx_card Γ = prectx_card Δ.
Proof.
  intros Hinj Hpf.
  symmetry.
  eapply injective_preserves_cardinal.
  - exact Hinj.
  - apply prectx_card_spec.
  - rewrite <- (pushforward_dom ξ Γ Δ Hpf).
    apply prectx_card_spec.
Qed.

Lemma pushforward_N (ξ : var -> var) Γ Δ :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  prectx_N Γ = prectx_N Δ.
Proof.
  intros Hinj Hpf.
  unfold prectx_N.
  now rewrite (pushforward_card ξ Γ Δ Hinj Hpf).
Qed.

Lemma pushforward_dim_factor (ξ : var -> var) Γ Δ p q :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  sens_dim_factor Γ p q = sens_dim_factor Δ p q.
Proof.
  intros Hinj Hpf.
  unfold sens_dim_factor.
  apply sens_eq_real.
  unfold real_dim_factor.
  now rewrite (pushforward_N ξ Γ Δ Hinj Hpf).
Qed.

Lemma pushforward_exists (ξ : var -> var) Γ :
  is_injective ξ ->
  exists Δ, is_pushforward ξ Γ Δ.
Proof.
  intro Hinj.

  assert
    (Hchoice :
      forall y : var,
        exists o : option (sens * type),
          (forall x, ξ x = y -> o = Γ x) /\
          ((forall x, ξ x <> y) -> o = None)).
  {
    intro y.
    destruct (classic (exists x, ξ x = y)) as [[x Hx] | Hnone].
    - exists (Γ x).
      split.
      + intros x' Hx'.
        assert (x = x').
        { apply Hinj. congruence. }
        now subst x'.
      + intro Habsurd.
        exfalso.
        exact (Habsurd x Hx).
    - exists None.
      split.
      + intros x Hx.
        exfalso.
        apply Hnone.
        now exists x.
      + intros _.
        reflexivity.
  }

  destruct
    (choice
      (fun (y : var) (o : option (sens * type)) =>
        (forall x, ξ x = y -> o = Γ x) /\
        ((forall x, ξ x <> y) -> o = None))
      Hchoice)
    as [Δ HΔ].
  assert (Hfinite : Finite var (prectx_support Δ)).
  {
    eapply Finite_downward_closed with
      (A := Im var var (prectx_dom Γ) ξ).
    - apply finite_image, prectx_finite.
    - intros y Hy.
      destruct (classic (exists x, ξ x = y)) as [[x Hxy] | Hnone].
      + apply Im_intro with x.
        * unfold prectx_dom, prectx_support.
          intro HΓnone.
          apply Hy.
          rewrite (proj1 (HΔ y) x Hxy), HΓnone.
          reflexivity.
        * symmetry; exact Hxy.
      + exfalso; apply Hy.
        apply (proj2 (HΔ y)).
        intros x Hxy; apply Hnone; now exists x.
  }
  pose (Δ' :=
    ({| prectx_lookup := Δ; prectx_finite := Hfinite |} : prectx)).
  exists Δ'.
  split.
  - intro x.
    change (Γ x = Δ (ξ x)).
    symmetry.
    apply (proj1 (HΔ (ξ x)) x).
    reflexivity.
  - intros y Hy.
    change (Δ y = None).
    exact (proj2 (HΔ y) Hy).
Qed.

Ltac pushforward_contr_context :=
  match goal with
  | Hinj : is_injective ?ξ,
    Hpf : is_pushforward ?ξ (prectx_contr ?p ?Γ ?Δ) ?Θ |- _ =>
      let Γ' := fresh "Γ'" in
      let HΓ' := fresh "HΓ'" in
      let Δ' := fresh "Δ'" in
      let HΔ' := fresh "HΔ'" in
      destruct (pushforward_exists ξ Γ Hinj) as [Γ' HΓ'];
      destruct (pushforward_exists ξ Δ Hinj) as [Δ' HΔ'];
      assert (Θ = prectx_contr p Γ' Δ') by
        (eapply pushforward_unique;
         [ exact Hpf | apply pushforward_contr; assumption ]);
      subst Θ
  end.

Ltac pushforward_scale_contr_context :=
  match goal with
  | Hinj : is_injective ?ξ,
    Hpf : is_pushforward ?ξ
      (prectx_contr ?p (prectx_scale ?s ?Γ) ?Δ) ?Θ |- _ =>
      let Γ' := fresh "Γ'" in
      let HΓ' := fresh "HΓ'" in
      let Δ' := fresh "Δ'" in
      let HΔ' := fresh "HΔ'" in
      destruct (pushforward_exists ξ Γ Hinj) as [Γ' HΓ'];
      destruct (pushforward_exists ξ Δ Hinj) as [Δ' HΔ'];
      assert (Θ = prectx_contr p (prectx_scale s Γ') Δ') by
        (eapply pushforward_unique;
         [ exact Hpf
         | apply pushforward_contr;
           [ apply pushforward_scale; exact HΓ' | exact HΔ' ] ]);
      subst Θ
  end.

Ltac pushforward_scale_context :=
  match goal with
  | Hinj : is_injective ?ξ,
    Hpf : is_pushforward ?ξ (prectx_scale ?s ?Γ) ?Θ |- _ =>
      let Γ' := fresh "Γ'" in
      let HΓ' := fresh "HΓ'" in
      destruct (pushforward_exists ξ Γ Hinj) as [Γ' HΓ'];
      assert (Θ = prectx_scale s Γ') by
        (eapply pushforward_unique;
         [ exact Hpf | apply pushforward_scale; exact HΓ' ]);
      subst Θ
  end.

Lemma renaming_aux pΓ t τ (Hty : has_type pΓ t τ) :
  match pΓ with
  | (p, Γ) =>
      forall Δ ξ,
        is_injective ξ ->
        is_pushforward ξ Γ Δ ->
        has_type (p, Δ) (t.[ren ξ]) τ
  end.
Proof.
  induction Hty as
    [ pΓ
    | pΓ n
    | p Γ τ s x Hx Hs
    | p Γ t σ τ Ht IHt
    | p Γ Δ f t σ τ Hcomp Hf IHf Ht IHt
    | p Γ Δ t1 t2 τ1 τ2 Hcomp Ht1 IHt1 Ht2 IHt2
    | p Γ Δ tpair s t τ1 τ2 τ
        Hcomp Hpair IHpair Hbody IHbody
    | pΓ t τ1 τ2 Ht IHt
    | pΓ t τ1 τ2 Ht IHt
    | p Γ Δ t tl tr s τ1 τ2 τ
        Hcomp Ht IHt Htl IHtl Htr IHtr
    | p Γ Δ t τ s Hcomp Ht IHt
    | p Γ Δ t1 t2 τ1 τ r s
        Hcomp Ht1 IHt1 Ht2 IHt2
    | pΓ t τ Ht IHt
    | pΓ t τ Ht IHt
    | p q Γ t τ Ht IHt Hpq
    | p q Γ Δ t τ Ht IHt Hle Hpq
  ].
  all: try destruct pΓ as [p' Γ'].
  all: intros Θ ξ Hinj Hpf; asimpl.

  - apply TUnit.

  - apply TNat.

  - eapply TVar with (s := s).
    + rewrite <- (proj1 Hpf x).
      exact Hx.
    + exact Hs.

  - apply TAbs.
    eapply IHt.
    + apply is_injective_up.
      exact Hinj.
    + apply is_pushforward_up.
      exact Hpf.

  - pushforward_contr_context.
    eapply TApp with (σ := σ).
    + eapply pushforward_comp; eauto.
    + eapply IHf; eauto.
    + eapply IHt; eauto.

  - pushforward_contr_context.
    apply TPair.
    + eapply pushforward_comp; eauto.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.

  - pushforward_scale_contr_context.
    eapply TLetPair with
      (s := s) (τ1 := τ1) (τ2 := τ2).
    + eapply pushforward_comp; eauto.
    + eapply IHpair; eauto.
    + eapply IHbody.
      * apply is_injective_up2.
        exact Hinj.
      * apply is_pushforward_up2.
        exact HΔ'.

  - apply TInjL.
    eapply IHt; eauto.

  - apply TInjR.
    eapply IHt; eauto.

  - pushforward_scale_contr_context.
    eapply TCase with
      (s := s) (τ1 := τ1) (τ2 := τ2).
    + eapply pushforward_comp; eauto.
    + eapply IHt; eauto.
    + eapply IHtl.
      * apply is_injective_up.
        exact Hinj.
      * apply is_pushforward_up.
        exact HΔ'.
    + eapply IHtr.
      * apply is_injective_up.
        exact Hinj.
      * apply is_pushforward_up.
        exact HΔ'.

  - pushforward_scale_contr_context.
    eapply TBang with (Γ := Γ') (Δ := Δ').
    + eapply pushforward_comp; eauto.
    + eapply IHt; eauto.

  - pushforward_scale_contr_context.
    eapply TLetBang with
      (τ1 := τ1) (r := r) (s := s).
    + eapply pushforward_comp; eauto.
    + eapply IHt1; eauto.
    + eapply IHt2.
      * apply is_injective_up.
        exact Hinj.
      * apply is_pushforward_up.
        exact HΔ'.

  - apply TFold.
    eapply IHt; eauto.

  - apply TUnfold.
    eapply IHt; eauto.

  - eapply TWeakGt with (p := p).
    + eapply IHt; eauto.
    + exact Hpq.

  - pushforward_scale_context.
    destruct (pushforward_exists ξ Γ Hinj) as [Γ'' HΓ''].
    rewrite (pushforward_dim_factor ξ Γ Γ'' p q Hinj HΓ'').
    eapply TWeakLt with (p := p) (Γ := Γ'') (Δ := Γ').
    + eapply IHt; eauto.
    + eapply pushforward_le; eauto.
    + exact Hpq.
Qed.

Lemma renaming (p : param) (Γ Δ : prectx) (t : term) (τ : type)
  (ξ : var -> var) :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  has_type (p, Γ) t τ ->
  has_type (p, Δ) (t.[ren ξ]) τ.
Proof.
  intros Hinj Hpf Hty.
  exact (renaming_aux (p, Γ) t τ Hty Δ ξ Hinj Hpf).
Qed.

(** *** Substitution *)

(* [skip k] embeds a context after deleting position [k]. *)
Fixpoint skip (k x : nat) : nat :=
  match k, x with
  | 0, x       => S x
  | S k, 0     => 0
  | S k, S x   => S (skip k x)
  end.

Lemma skip_injective (k : nat) : is_injective (skip k).
Proof.
  induction k as [|k IH]; intros [|x] [|y] H; simpl in H.
  all: try reflexivity.
  all: try discriminate.
  all: f_equal.
  - now injection H.
  - apply IH.
    now injection H.
Qed.

Definition prectx_delete (k : nat) (Γ : prectx) : prectx.
Proof.
  refine {| prectx_lookup := fun x => Γ (skip k x) |}.
  apply (finite_preimage_injective var var (skip k) (prectx_dom Γ)).
  - apply skip_injective.
  - apply prectx_finite.
Defined.

Lemma prectx_delete_lookup (k : nat) (Γ : prectx) (x : var) :
  prectx_delete k Γ x = Γ (skip k x).
Proof.
  reflexivity.
Qed.

Fixpoint prectx_insert
  (k : nat) (a : option (sens * type)) (Γ : prectx) : prectx :=
  match k with
  | 0   => prectx_cons a Γ
  | S k => prectx_cons (Γ 0%nat) (prectx_insert k a (prectx_tail Γ))
  end.

Lemma prectx_insert_lookup (k : nat) a Γ x :
  prectx_insert k a Γ x =
  match k, x with
  | 0, 0 => a
  | 0, S x => Γ x
  | S _, 0 => Γ 0%nat
  | S k, S x => prectx_insert k a (prectx_tail Γ) x
  end.
Proof.
  destruct k, x; reflexivity.
Qed.

Lemma prectx_insert_cons (k : nat) a b Γ :
  prectx_insert (S k) a (prectx_cons b Γ) =
  prectx_cons b (prectx_insert k a Γ).
Proof.
  simpl.
  now rewrite prectx_tail_cons.
Qed.

(* Substitution for the variable at depth [k]. *)
Fixpoint subst_at (k : nat) (v : term) (x : var) : term :=
  match k, x with
  | 0, 0       => v
  | 0, S x     => TmVar x
  | S k, 0     => TmVar 0%nat
  | S k, S x   => (subst_at k v x).[ren (+1%nat)]
  end.

(** Elementary facts about deletion and insertion. *)
Lemma prectx_le_empty_l (Γ : prectx) : prectx_le prectx_empty Γ.
Proof.
  intros x s τ H.
  discriminate H.
Qed.

Lemma prectx_delete_insert (k : nat) a Γ :
  prectx_delete k (prectx_insert k a Γ) = Γ.
Proof.
  induction k as [|k IH] in Γ |- *.
  - apply prectx_ext; intro x.
    reflexivity.
  - apply prectx_ext; intro x.
    destruct x as [|x]; [reflexivity |].
    change
      (prectx_delete k
        (prectx_insert k a (prectx_tail Γ)) x = Γ (S x)).
    rewrite IH.
    reflexivity.
Qed.

Lemma prectx_insert_at (k : nat) a Γ :
  prectx_insert k a Γ k = a.
Proof.
  induction k as [|k IH] in Γ |- *; [reflexivity |].
  change
    (prectx_insert k a (prectx_tail Γ) k = a).
  apply IH.
Qed.

Lemma prectx_delete_cons (k : nat) a Γ :
  prectx_delete (S k) (prectx_cons a Γ) =
  prectx_cons a (prectx_delete k Γ).
Proof.
  apply prectx_ext; intro x.
  destruct x; reflexivity.
Qed.

Lemma prectx_delete_scale (k : nat) s Γ :
  prectx_delete k (prectx_scale s Γ) =
  prectx_scale s (prectx_delete k Γ).
Proof.
  apply prectx_ext; intro x.
  rewrite prectx_delete_lookup.
  repeat rewrite prectx_scale_lookup.
  rewrite prectx_delete_lookup.
  reflexivity.
Qed.

Lemma prectx_delete_contr (k : nat) p Γ Δ :
  prectx_delete k (prectx_contr p Γ Δ) =
  prectx_contr p (prectx_delete k Γ) (prectx_delete k Δ).
Proof.
  apply prectx_ext; intro x.
  rewrite prectx_delete_lookup.
  repeat rewrite prectx_contr_lookup_eq.
  repeat rewrite prectx_delete_lookup.
  reflexivity.
Qed.

Lemma prectx_delete_le (k : nat) Γ Δ :
  prectx_le Γ Δ ->
  prectx_le (prectx_delete k Γ) (prectx_delete k Δ).
Proof.
  intros Hle x s τ Hlookup.
  repeat rewrite prectx_delete_lookup in *.
  now apply Hle in Hlookup.
Qed.

Lemma prectx_delete_card_le (k : nat) (Γ : prectx) :
  (prectx_card (prectx_delete k Γ) <= prectx_card Γ)%nat.
Proof.
  destruct
    (cardinal_Im_intro var var (prectx_dom (prectx_delete k Γ))
      (skip k) (prectx_card (prectx_delete k Γ))
      (prectx_card_spec (prectx_delete k Γ)))
    as [n Hcard_image].
  assert (Hn : n = prectx_card (prectx_delete k Γ)).
  {
    eapply injective_preserves_cardinal.
    - apply skip_injective.
    - apply prectx_card_spec.
    - exact Hcard_image.
  }
  rewrite <- Hn.
  eapply incl_card_le.
  - exact Hcard_image.
  - apply prectx_card_spec.
  - intros y Hy.
    inversion Hy as [x Hx y' Hxy].
    unfold prectx_dom, prectx_support in *.
    intro Hnone.
    apply Hx.
    change (Γ (skip k x) = None).
    now rewrite <- Hxy.
Qed.

Lemma prectx_delete_N_le (k : nat) (Γ : prectx) :
  (prectx_N (prectx_delete k Γ) <= prectx_N Γ)%nat.
Proof.
  unfold prectx_N.
  apply Nat.max_le_compat_l, prectx_delete_card_le.
Qed.

Lemma sens_mult_le_compat_r (r s t : sens) :
  sens_le r s -> sens_le (sens_mult r t) (sens_mult s t).
Proof.
  intro Hle.
  destruct r as [r Hr |], s as [s Hs |], t as [t Ht |];
    try solve [right; reflexivity | left; exact I].
  - apply sens_le_real.
    apply sens_le_real in Hle.
    nra.
  - destruct Hle as [Hle | Hle]; [contradiction | discriminate].
Qed.

Lemma prectx_scale_mono (r s : sens) (Γ : prectx) :
  sens_le r s -> prectx_le (prectx_scale r Γ) (prectx_scale s Γ).
Proof.
  intros Hrs x u τ Hlookup.
  rewrite prectx_scale_lookup in Hlookup.
  destruct (Γ x) as [[v σ] |] eqn:HΓ; [| discriminate].
  inversion Hlookup; subst u σ.
  exists (sens_mult s v); split.
  - now rewrite prectx_scale_lookup, HΓ.
  - now apply sens_mult_le_compat_r.
Qed.

Lemma sens_dim_factor_delete_le (k : nat) (Γ : prectx) p q :
  param_le p q ->
  sens_le
    (sens_dim_factor (prectx_delete k Γ) p q)
    (sens_dim_factor Γ p q).
Proof.
  intro Hpq.
  apply sens_dim_factor_N_mono.
  - exact Hpq.
  - apply prectx_delete_N_le.
Qed.

Lemma prectx_comp_delete (k : nat) Γ Δ :
  prectx_comp Γ Δ ->
  prectx_comp (prectx_delete k Γ) (prectx_delete k Δ).
Proof.
  intros Hcomp x s1 τ1 s2 τ2 H1 H2.
  exact (Hcomp (skip k x) s1 τ1 s2 τ2 H1 H2).
Qed.

Lemma prectx_contr_lookup_r (p : param) (Γ Δ : prectx)
  (x : var) (s : sens) (τ : type) :
  prectx_comp Γ Δ ->
  Δ x = Some (s, τ) ->
  exists s', prectx_contr p Γ Δ x = Some (s', τ).
Proof.
  intros Hcomp HΔ.
  rewrite (prectx_contr_comm p Γ Δ Hcomp).
  eapply prectx_contr_lookup.
  - now apply prectx_comp_sym.
  - exact HΔ.
Qed.

Lemma prectx_contr_scale_lookup_l (p : param) (s : sens) (Γ Δ : prectx)
  (x : var) (r : sens) (τ : type) :
  prectx_comp Γ Δ ->
  Γ x = Some (r, τ) ->
  exists r',
    prectx_contr p (prectx_scale s Γ) Δ x = Some (r', τ).
Proof.
  intros Hcomp HΓ.
  eapply prectx_contr_lookup.
  - now apply prectx_comp_scale_l.
  - rewrite prectx_scale_lookup, HΓ.
    reflexivity.
Qed.

Lemma prectx_contr_scale_lookup_r (p : param) (s : sens) (Γ Δ : prectx)
  (x : var) (r : sens) (τ : type) :
  prectx_comp Γ Δ ->
  Δ x = Some (r, τ) ->
  exists r',
    prectx_contr p (prectx_scale s Γ) Δ x = Some (r', τ).
Proof.
  intros Hcomp HΔ.
  eapply prectx_contr_lookup_r.
  - now apply prectx_comp_scale_l.
  - exact HΔ.
Qed.

(** Substitution at depth [k] commutes with the binding constructors. *)
Lemma subst_at_abs (k : nat) v t :
  (TmAbs t).[subst_at k v] = TmAbs (t.[subst_at (S k) v]).
Proof.
  cbn.
  f_equal.
  f_equal.
  extensionality x.
  destruct x; asimpl; reflexivity.
Qed.

Lemma subst_at_letpair (k : nat) v t tbody :
  (TmLetPair t tbody).[subst_at k v] =
  TmLetPair (t.[subst_at k v]) (tbody.[subst_at (S (S k)) v]).
Proof.
  cbn.
  f_equal.
  f_equal.
  extensionality x.
  destruct x as [|[|x]]; asimpl; reflexivity.
Qed.

Lemma subst_at_case (k : nat) v t tl tr :
  (TmCase t tl tr).[subst_at k v] =
  TmCase (t.[subst_at k v])
    (tl.[subst_at (S k) v]) (tr.[subst_at (S k) v]).
Proof.
  cbn.
  f_equal; f_equal; extensionality x; destruct x; asimpl; reflexivity.
Qed.

Lemma subst_at_letbang (k : nat) v t tbody :
  (TmLetBang t tbody).[subst_at k v] =
  TmLetBang (t.[subst_at k v]) (tbody.[subst_at (S k) v]).
Proof.
  cbn.
  f_equal.
  f_equal.
  extensionality x.
  destruct x; asimpl; reflexivity.
Qed.

Lemma subst_pair_composition tbody v1 v2 :
  (tbody.[subst_at 1%nat v1]).[v2/] =
  tbody.[v2 .: v1 .: ids].
Proof.
  rewrite subst_comp.
  f_equal.
  extensionality x.
  asimpl.
  destruct x as [|[|x]]; asimpl; reflexivity.
Qed.

Lemma substitution_closed_var p (Θ : prectx) x τ sx :
  Θ x = Some (sx, τ) ->
  sens_le sens_1 sx ->
  forall k v,
    (forall s σ, Θ k = Some (s, σ) ->
      has_type (p, prectx_empty) v σ) ->
    has_type (p, prectx_delete k Θ)
      ((TmVar x).[subst_at k v]) τ.
Proof.
  intros Hx Hsx.
  induction k as [|k IH] in Θ, x, sx, τ, Hx, Hsx |- *;
    intros v Hv.
  - destruct x as [|x].
    + cbn.
      apply (weakening_prectx (p, prectx_empty) v τ (Hv sx τ Hx)).
      apply prectx_le_empty_l.
    + cbn.
      eapply TVar with (s := sx); eauto.
  - destruct x as [|x].
    + cbn.
      eapply TVar with (s := sx); eauto.
    + cbn.
      assert
        (Hrec :
          has_type
            (p, prectx_delete k (prectx_tail Θ))
            ((TmVar x).[subst_at k v]) τ).
      {
        eapply IH; eauto.
      }
      assert
        (Hinj : is_injective (+1%nat)).
      {
        intros y z Hyz.
        asimpl in Hyz.
        now injection Hyz.
      }
      assert
        (Hpf :
          is_pushforward (+1%nat)
            (prectx_delete k (prectx_tail Θ))
            (prectx_cons None (prectx_delete k (prectx_tail Θ)))).
      {
        split.
        - intro y.
          asimpl.
          reflexivity.
        - intros [|y] Hnone; [reflexivity |].
          exfalso.
          apply (Hnone y).
          asimpl.
          reflexivity.
      }
      pose proof
        (renaming p
          (prectx_delete k (prectx_tail Θ))
          (prectx_cons None (prectx_delete k (prectx_tail Θ)))
          ((TmVar x).[subst_at k v]) τ (+1%nat)
          Hinj Hpf Hrec) as Hren.
      apply
        (weakening_prectx
          (p, prectx_cons None (prectx_delete k (prectx_tail Θ)))
          _ τ Hren).
      * intros [|y] s σ Hy.
        -- discriminate Hy.
        -- exists s; split.
           ++ exact Hy.
           ++ apply sens_le_refl.
Qed.

Lemma substitution_closed_delete pΘ t τ (Hty : has_type pΘ t τ) :
  match pΘ with
  | (p, Θ) => forall k v,
      (forall s σ, Θ k = Some (s, σ) ->
        has_type (p, prectx_empty) v σ) ->
      has_type (p, prectx_delete k Θ) (t.[subst_at k v]) τ
  end.
Proof.
  induction Hty as
    [ pΘ
    | pΘ n
    | p Θ τ sx x Hx Hsx
    | p Γ t σ τ Ht IHt
    | p Γ Δ f t σ τ Hcomp Hf IHf Ht IHt
    | p Γ Δ t1 t2 τ1 τ2 Hcomp Ht1 IHt1 Ht2 IHt2
    | p Γ Δ tpair s t τ1 τ2 τ
        Hcomp Hpair IHpair Hbody IHbody
    | pΘ t τ1 τ2 Ht IHt
    | pΘ t τ1 τ2 Ht IHt
    | p Γ Δ t tl tr s τ1 τ2 τ
        Hcomp Ht IHt Htl IHtl Htr IHtr
    | p Γ Δ t τ s Hcomp Ht IHt
    | p Γ Δ t1 t2 τ1 τ r s
        Hcomp Ht1 IHt1 Ht2 IHt2
    | pΘ t τ Ht IHt
    | pΘ t τ Ht IHt
    | p q Γ t τ Ht IHt Hpq
    | p q Γ Δ t τ Ht IHt Hle Hpq
    ].
  all: try destruct pΘ as [p Γ].
  all: intros k v Hv.

  - change (has_type (p, prectx_delete k Γ) TmUnit (TyBase TyUnit)).
    apply TUnit.

  - change (has_type (p, prectx_delete k Γ) (TmNat n) (TyBase TyNat)).
    apply TNat.

  - eapply substitution_closed_var; eauto.

  - rewrite subst_at_abs.
    apply TAbs.
    pose proof (IHt (S k) v) as Hbody.
    rewrite prectx_delete_cons in Hbody.
    apply Hbody.
    intros s ρ Hlookup.
    apply (Hv s ρ).
    exact Hlookup.

  - change
      (has_type (p, prectx_delete k (prectx_contr p Γ Δ))
        (TmApp (f.[subst_at k v]) (t.[subst_at k v])) τ).
    rewrite prectx_delete_contr.
    eapply TApp with (σ := σ).
    + now apply prectx_comp_delete.
    + apply IHf.
      intros s ρ Hlookup.
      destruct
        (prectx_contr_lookup p Γ Δ k s ρ Hcomp Hlookup)
        as [s' Hlookup'].
      exact (Hv s' ρ Hlookup').
    + apply IHt.
      intros s ρ Hlookup.
      destruct
        (prectx_contr_lookup_r p Γ Δ k s ρ Hcomp Hlookup)
        as [s' Hlookup'].
      exact (Hv s' ρ Hlookup').

  - change
      (has_type (p, prectx_delete k (prectx_contr p Γ Δ))
        (TmPair (t1.[subst_at k v]) (t2.[subst_at k v]))
        (TyPair p τ1 τ2)).
    rewrite prectx_delete_contr.
    apply TPair.
    + now apply prectx_comp_delete.
    + apply IHt1.
      intros s ρ Hlookup.
      destruct
        (prectx_contr_lookup p Γ Δ k s ρ Hcomp Hlookup)
        as [s' Hlookup'].
      exact (Hv s' ρ Hlookup').
    + apply IHt2.
      intros s ρ Hlookup.
      destruct
        (prectx_contr_lookup_r p Γ Δ k s ρ Hcomp Hlookup)
        as [s' Hlookup'].
      exact (Hv s' ρ Hlookup').

  - rewrite subst_at_letpair.
    rewrite prectx_delete_contr, prectx_delete_scale.
    eapply TLetPair with (s := s) (τ1 := τ1) (τ2 := τ2).
    + now apply prectx_comp_delete.
    + apply IHpair.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_l p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').
    + pose proof (IHbody (S (S k)) v) as Hb.
      rewrite !prectx_delete_cons in Hb.
      apply Hb.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_r p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').

  - change
      (has_type (p, prectx_delete k Γ)
        (TmInjL (t.[subst_at k v])) (TyPlus τ1 τ2)).
    apply TInjL.
    now apply IHt.

  - change
      (has_type (p, prectx_delete k Γ)
        (TmInjR (t.[subst_at k v])) (TyPlus τ1 τ2)).
    apply TInjR.
    now apply IHt.

  - rewrite subst_at_case.
    rewrite prectx_delete_contr, prectx_delete_scale.
    eapply TCase with (s := s) (τ1 := τ1) (τ2 := τ2).
    + now apply prectx_comp_delete.
    + apply IHt.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_l p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').
    + pose proof (IHtl (S k) v) as Hl.
      rewrite prectx_delete_cons in Hl.
      apply Hl.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_r p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').
    + pose proof (IHtr (S k) v) as Hr.
      rewrite prectx_delete_cons in Hr.
      apply Hr.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_r p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').

  - change
      (has_type
        (p, prectx_delete k
          (prectx_contr p (prectx_scale s Γ) Δ))
        (TmBang (t.[subst_at k v])) (TyBang s τ)).
    rewrite prectx_delete_contr, prectx_delete_scale.
    eapply TBang with
      (Γ := prectx_delete k Γ) (Δ := prectx_delete k Δ).
    + now apply prectx_comp_delete.
    + apply IHt.
      intros r ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_l p s Γ Δ
          k r ρ Hcomp Hlookup)
        as [r' Hlookup'].
      exact (Hv r' ρ Hlookup').

  - rewrite subst_at_letbang.
    rewrite prectx_delete_contr, prectx_delete_scale.
    eapply TLetBang with (τ1 := τ1) (r := r) (s := s).
    + now apply prectx_comp_delete.
    + apply IHt1.
      intros u ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_l p s Γ Δ
          k u ρ Hcomp Hlookup)
        as [u' Hlookup'].
      exact (Hv u' ρ Hlookup').
    + pose proof (IHt2 (S k) v) as Hb.
      rewrite prectx_delete_cons in Hb.
      apply Hb.
      intros u ρ Hlookup.
      destruct
        (prectx_contr_scale_lookup_r p s Γ Δ
          k u ρ Hcomp Hlookup)
        as [u' Hlookup'].
      exact (Hv u' ρ Hlookup').

  - change
      (has_type (p, prectx_delete k Γ)
        (TmFold (TyRec τ) (t.[subst_at k v])) (TyRec τ)).
    apply TFold.
    now apply IHt.

  - change
      (has_type (p, prectx_delete k Γ)
        (TmUnfold (TyRec τ) (t.[subst_at k v])) (τ.[TyRec τ/])).
    apply TUnfold.
    now apply IHt.

  - change
      (has_type (q, prectx_delete k Γ) (t.[subst_at k v]) τ).
    eapply TWeakGt with (p := p).
    + apply IHt.
      intros s σ Hlookup.
      rewrite <- (prectx_scale_empty
        (sens_dim_factor prectx_empty q p)).
      eapply TWeakLt with
        (p := q) (Γ := prectx_empty) (Δ := prectx_empty).
      * exact (Hv s σ Hlookup).
      * apply prectx_le_refl.
      * left; exact Hpq.
    + exact Hpq.

  - change
      (has_type
        (q, prectx_delete k
          (prectx_scale (sens_dim_factor Γ p q) Δ))
        (t.[subst_at k v]) τ).
    rewrite prectx_delete_scale.
    assert
      (Hsub :
        has_type (p, prectx_delete k Γ) (t.[subst_at k v]) τ).
    {
      apply IHt.
      intros s σ Hlookup.
      destruct (Hle k s σ Hlookup) as [sΔ [HΔ _]].
      eapply weakening_ctx.
      - apply (Hv (sens_mult (sens_dim_factor Γ p q) sΔ) σ).
        now rewrite prectx_scale_lookup, HΔ.
      - exact Hpq.
      - apply prectx_le_refl.
    }
    assert
      (Hdim :
        has_type
          (q, prectx_scale
            (sens_dim_factor (prectx_delete k Γ) p q)
            (prectx_delete k Δ))
          (t.[subst_at k v]) τ).
    {
      eapply TWeakLt with
        (p := p) (Γ := prectx_delete k Γ) (Δ := prectx_delete k Δ).
      - exact Hsub.
      - now apply prectx_delete_le.
      - exact Hpq.
    }
    eapply (weakening_prectx _ _ _ Hdim).
    apply prectx_scale_mono, sens_dim_factor_delete_le.
    exact Hpq.
Qed.

Lemma substitution_closed_at p Θ t τ :
  has_type (p, Θ) t τ ->
  forall k Γ v s σ,
    prectx_le Θ
      (prectx_insert k (Some (s, σ)) Γ) ->
    has_type (p, prectx_empty) v σ ->
    has_type (p, Γ) (t.[subst_at k v]) τ.
Proof.
  intros Ht k Γ v s σ Hle Hv.
  assert
    (Ht' :
      has_type (p, prectx_insert k (Some (s, σ)) Γ) t τ).
  {
    apply (weakening_prectx (p, Θ) t τ Ht).
    - exact Hle.
  }
  rewrite <- (prectx_delete_insert k (Some (s, σ)) Γ).
  eapply (substitution_closed_delete
    (p, prectx_insert k (Some (s, σ)) Γ) t τ Ht').
  intros r ρ Hlookup.
  rewrite prectx_insert_at in Hlookup.
  inversion Hlookup; subst.
  exact Hv.
Qed.

Theorem substitution_closed (p : param) (Γ : prectx)
  (t v : term) (s : sens) (σ τ : type) :
  has_type (p, prectx_cons (Some (s, σ)) Γ) t τ ->
  has_type (p, prectx_empty) v σ ->
  has_type (p, Γ) (t.[v/]) τ.
Proof.
  intros Ht Hv.
  eapply substitution_closed_at
    with (Θ := prectx_cons (Some (s, σ)) Γ)
         (k := 0%nat) (s := s) (σ := σ).
  - exact Ht.
  - apply prectx_le_refl.
  - exact Hv.
Qed.

Lemma substitution_closed_pair
  (p : param) (tbody v1 v2 : term)
  (s : sens) (τ1 τ2 τ : type) :
  has_type
    (p,
      prectx_cons (Some (s, τ2))
        (prectx_cons (Some (s, τ1)) prectx_empty))
    tbody τ ->
  has_type (p, prectx_empty) v1 τ1 ->
  has_type (p, prectx_empty) v2 τ2 ->
  has_type
    (p, prectx_empty)
    (tbody.[v2 .: v1 .: ids])
    τ.
Proof.
  intros Htbody Hv1 Hv2.
  rewrite <- subst_pair_composition.
  apply
    (substitution_closed
      p prectx_empty (tbody.[subst_at 1%nat v1]) v2 s τ2 τ).
  - eapply substitution_closed_at with
      (Θ := prectx_cons (Some (s, τ2))
        (prectx_cons (Some (s, τ1)) prectx_empty))
      (k := 1%nat)
      (Γ := prectx_cons (Some (s, τ2)) prectx_empty)
      (v := v1) (s := s) (σ := τ1).
    + exact Htbody.
    + rewrite prectx_insert_cons.
      apply prectx_le_refl.
    + exact Hv1.
  - exact Hv2.
Qed.

(** *** Subject reduction *)

Theorem subject_reduction_closed (p : param) (t v : term) (τ : type) :
  has_type (p, prectx_empty) t τ ->
  evals_to t v ->
  has_type (p, prectx_empty) v τ.
Proof.
  intros Hty Hev.
  revert p τ Hty.

  induction Hev as
    [ b
    | tbody
    | f a tbody w va
        Hf_eval IHf Ha_eval IHa Hbody_eval IHbody
    | t1 t2 v1 v2
        H1_eval IH1 H2_eval IH2
    | tpair tbody v1 v2 w
        Hpair_eval IHpair Hbody_eval IHbody
    | t w H_eval IH
    | t w H_eval IH
    | t tl tr vinj w
        Hscrut_eval IHscrut Hbranch_eval IHbranch
    | t tl tr vinj w
        Hscrut_eval IHscrut Hbranch_eval IHbranch
    | t w H_eval IH
    | t tbody vbang w
        Hbang_eval IHbang Hbody_eval IHbody
    | rec_ty t w H_eval IH
    | rec_ty t w H_eval IH
    ];
    intros p τ Hty.

  (* EvBase *)
  - exact Hty.

  (* EvAbs *)
  - exact Hty.

  (* EvApp *)
  - destruct (inversion_closed_TmApp p f a τ Hty)
      as (p' & σ & Hf_ty & Ha_ty & Hstruct).

    specialize (IHf p' (TyArrow p' σ τ) Hf_ty).
    apply
      (inversion_closed_abs_value p' tbody σ τ)
      in IHf.

    specialize (IHa p' σ Ha_ty).

    eapply has_type_struct.
    + exact Hstruct.
    + apply IHbody.
      eapply substitution_closed.
      * exact IHf.
      * exact IHa.

  (* EvPair *)
  - destruct (inversion_closed_TmPair p t1 t2 τ Hty)
      as (p' & τ1 & τ2 &
          Hτ & Ht1_ty & Ht2_ty & Hstruct).

    subst τ.
    specialize (IH1 p' τ1 Ht1_ty).
    specialize (IH2 p' τ2 Ht2_ty).

    eapply has_type_struct.
    + exact Hstruct.
    + now apply has_type_closed_pair.

  (* EvLetPair *)
  - destruct
      (inversion_closed_TmLetPair p tpair tbody τ Hty)
      as (p' & s & τ1 & τ2 &
          Hpair_ty & Htbody_ty & Hstruct).

    specialize
      (IHpair p' (TyPair p' τ1 τ2) Hpair_ty).

    destruct
      (inversion_closed_pair_value
        p' v1 v2 τ1 τ2 IHpair)
      as [Hv1_ty Hv2_ty].

    eapply has_type_struct.
    + exact Hstruct.
    + apply IHbody.
      eapply substitution_closed_pair.
      * exact Htbody_ty.
      * exact Hv1_ty.
      * exact Hv2_ty.

  (* EvInjL *)
  - destruct
      (inversion_TmInjL
        (p, prectx_empty) t τ Hty)
      as (τ1 & τ2 & Hτ & Ht_ty).

    subst τ.
    apply TInjL.
    exact (IH p τ1 Ht_ty).

  (* EvInjR *)
  - destruct
      (inversion_TmInjR
        (p, prectx_empty) t τ Hty)
      as (τ1 & τ2 & Hτ & Ht_ty).

    subst τ.
    apply TInjR.
    exact (IH p τ2 Ht_ty).

  (* EvCaseL *)
  - destruct
      (inversion_closed_TmCase p t tl tr τ Hty)
      as (p' & s & τ1 & τ2 &
          Hscrut_ty & Htl_ty & Htr_ty & Hstruct).

    specialize
      (IHscrut p' (TyPlus τ1 τ2) Hscrut_ty).

    apply
      (inversion_closed_injl_value p' vinj τ1 τ2)
      in IHscrut.

    eapply has_type_struct.
    + exact Hstruct.
    + apply IHbranch.
      eapply substitution_closed.
      * exact Htl_ty.
      * exact IHscrut.

  (* EvCaseR *)
  - destruct
      (inversion_closed_TmCase p t tl tr τ Hty)
      as (p' & s & τ1 & τ2 &
          Hscrut_ty & Htl_ty & Htr_ty & Hstruct).

    specialize
      (IHscrut p' (TyPlus τ1 τ2) Hscrut_ty).

    apply
      (inversion_closed_injr_value p' vinj τ1 τ2)
      in IHscrut.

    eapply has_type_struct.
    + exact Hstruct.
    + apply IHbranch.
      eapply substitution_closed.
      * exact Htr_ty.
      * exact IHscrut.

  (* EvBang *)
  - destruct
      (inversion_closed_TmBang p t τ Hty)
      as (p' & s & σ & Hτ & Ht_ty & Hstruct).

    subst τ.
    specialize (IH p' σ Ht_ty).

    eapply has_type_struct.
    + exact Hstruct.
    + now apply has_type_closed_bang.

  (* EvLetBang *)
  - destruct
      (inversion_closed_TmLetBang p t tbody τ Hty)
      as (p' & r & s & σ &
          Ht_ty & Htbody_ty & Hstruct).

    specialize
      (IHbang p' (TyBang r σ) Ht_ty).

    apply
      (inversion_closed_bang_value p' vbang r σ)
      in IHbang.

    eapply has_type_struct.
    + exact Hstruct.
    + apply IHbody.
      eapply substitution_closed.
      * exact Htbody_ty.
      * exact IHbang.

  (* EvFold *)
  - destruct
      (inversion_TmFold (p, prectx_empty) rec_ty t τ Hty)
      as (body & Hrec & Hτ & Ht_ty).
    subst rec_ty; subst τ.
    apply TFold.
    exact (IH p (body.[TyRec body/]) Ht_ty).

  (* EvUnfold *)
  - destruct
      (inversion_TmUnfold (p, prectx_empty) rec_ty t τ Hty)
      as (body & Hrec & Hτ & Ht_ty).
    subst rec_ty; subst τ.
    specialize (IH p (TyRec body) Ht_ty).
    destruct
      (inversion_TmFold
        (p, prectx_empty) (TyRec body) w (TyRec body) IH)
      as (body' & Hrec & Hτ & Hw_ty).
    inversion Hrec; subst.
    exact Hw_ty.
Qed.
