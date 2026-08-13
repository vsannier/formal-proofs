(*
  Formalisation of the metatheory of Core Plurimetric Fuzz
  <https://doi.org/10.4230/LIPIcs.FSCD.2024.12>
  by Victor Sannier (2024–2026)
*)

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Program.Program.
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

(** The norm equivalence constant for $L^p$ norms in dimension $2$. *)
Definition real_pnorm_c (p q : param) : R :=
  match p, q with
  | param_real p _, param_real q _ => Rpower 2 (Rabs (/p - /q))
  | param_real p _, param_infty => Rpower 2 (/p)
  | param_infty, param_real q _ => Rpower 2 (/q)
  | param_infty, param_infty => 1
  end. 

Lemma real_pnorm_c_pos (p q : param) : real_pnorm_c p q > 0.
Proof.
  unfold real_pnorm_c.
  destruct p, q.
  all: try lra.
  all: apply exp_pos.
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

Definition sens_pnorm_c (p q : param) : sens :=
  sens_real (real_pnorm_c p q) (real_pnorm_c_pos p q).

Example c11 : (sens_pnorm_c param_1 param_1) = sens_1.
Proof.
  unfold sens_pnorm_c, sens_1.
  apply sens_eq_real.
  unfold real_pnorm_c; simpl.
  rewrite Rminus_diag_eq, Rabs_R0, Rpower_O.
  all: lra.
Qed.

Lemma sens_pnorm_c_ge_1 (p q : param) :
  sens_le sens_1 (sens_pnorm_c p q).
Proof.
  unfold sens_pnorm_c, real_pnorm_c.
  destruct p as [p |], q as [q |]; apply sens_le_real.
  all: replace 1 with (Rpower 2 0); [apply Rle_Rpower | apply Rpower_O].
  all: try lra.
  - apply Rabs_pos.
  - left; apply Rinv_0_lt_compat; lra.
  - left; apply Rinv_0_lt_compat; lra.
Qed.

(** * Plurimetric Fuzz *)

(** ** Syntax *)

(** *** Types and Terms *)

Inductive ty_base : Type :=
  | TyUnit
  | TyNat.

Inductive type :=
  | TyBase (τ : ty_base)
  | TyArrow (p : param) (σ τ : type)
  | TyPair (p : param) (τ1 τ2 : type)
  | TyPlus (τ1 τ2 : type)
  | TyBang (s : sens) (τ : type).

Definition TyBool := TyPlus (TyBase TyUnit) (TyBase TyUnit).

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
  | TmLetBang (t : term) (tbody : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Definition TmUnit := TmBase ValUnit.

Definition TmNat (n : nat) := TmBase (ValNat n).

Definition TmTrue := TmInjL (TmBase ValUnit).

Definition TmFalse := TmInjR (TmBase ValUnit).

Definition TmDiag := TmAbs (TmPair (TmVar 0%nat) (TmVar 0%nat)).

Definition TmSwap :=
  TmAbs (TmLetPair (TmVar 0%nat) (TmPair (TmVar 0%nat) (TmVar 1%nat))).

(** *** Precontexts and Contexts *)

Definition prectx := var -> option (sens * type).

Definition prectx_empty : prectx := (fun _ => None).

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
  prectx_le Γ Δ -> prectx_le (τ .: Γ) (τ .: Δ).
Proof.
  unfold prectx_le.
  intros.
  destruct x as [| x]; simpl in *.
  - exists s1.
    split; [exact H0 | apply sens_le_refl].
  - now apply H in H0.
Qed.

Definition prectx_scale (s : sens) (Γ : prectx) : prectx := fun x =>
  match (Γ x) with
  | Some (r, τ) => Some ((sens_mult s r), τ)
  | None => None
  end.

Lemma prectx_scale_1 (Γ : prectx) : prectx_scale sens_1 Γ = Γ.
Proof.
  extensionality x.
  unfold prectx_scale.
  destruct (Γ x) as [[s τ] |].
  - repeat f_equal.
    apply sens_mult_1_l.
  - reflexivity.
Qed.

Lemma prectx_scale_le (s : sens) (Γ : prectx) :
  sens_le sens_1 s ->
  prectx_le Γ (prectx_scale s Γ).
Proof.
  intro H.
  intros x sΓ τΓ HΓ.
  exists (sens_mult s sΓ).
  split.
  - unfold prectx_scale.
    now rewrite HΓ.
  - now apply sens_mult_le.
Qed.

Lemma prectx_scale_inv (s : R) (Hs : 0 < s) Γ :
  prectx_scale (sens_real s Hs) (prectx_scale (sens_inv s Hs) Γ) = Γ.
Proof.
  unfold prectx_scale, sens_inv.
  extensionality x.
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
  - unfold prectx_scale.
    now rewrite HΓ.
  - exists (sens_mult (sens_inv s Hs) r).
    unfold prectx_scale.
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
  unfold prectx_empty in H2.
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
  unfold prectx_comp, prectx_scale.
  intros H x s1 τ1 s2 τ2 H1 H2.
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
  unfold prectx_comp, prectx_scale.
  intros H x s1 τ1 s2 τ2 H1 H2.
  destruct (Δ x) as [[sΔ τΔ]|] eqn:HΔ; [| discriminate].
  apply H with x s1 sΔ; [exact H1 |].
  rewrite HΔ.
  now inversion H2.
Qed.

Definition prectx_contr (p : param) (Γ Δ : prectx) : prectx := fun x =>
  match (Γ x), (Δ x) with
  | Some (s1, τ1), Some (s2, τ2) => Some (sens_pnorm p s1 s2, τ1)
  | Some _, None => Γ x
  | None, Some _ => Δ x
  | None, None => None
  end.

Lemma prectx_contr_empty_l (p : param) (Γ : prectx) :
  prectx_contr p prectx_empty Γ = Γ.
Proof.
  extensionality x.
  unfold prectx_contr, prectx_empty.
  now destruct (Γ x) as [[s τ] |].
Qed.

Lemma prectx_contr_empty_r (p : param) (Γ : prectx) :
  prectx_contr p Γ prectx_empty = Γ.
Proof.
  extensionality x.
  unfold prectx_contr, prectx_empty.
  now destruct (Γ x) as [[s τ] |].
Qed.

(** Contraction of compatible precontexts is commutative. *)
Lemma prectx_contr_comm (p : param) (Γ Δ : prectx) :
  prectx_comp Γ Δ -> 
  prectx_contr p Γ Δ = prectx_contr p Δ Γ.
Proof.
  intro H.
  extensionality x.
  unfold prectx_contr.
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
  extensionality x.
  unfold prectx_contr.
  destruct (Γ x) as [[s1 τ1]|];
  destruct (Δ x) as [[s2 τ2]|];
  destruct (Θ x) as [[s3 τ3]|].
  rewrite sens_pnorm_assoc.
  all: reflexivity.
Qed.

Lemma prectx_contr_le_l (p : param) (Γ Δ Θ : prectx)
  (x : var) (sΓ sΘ : sens) (τ : type) :
  prectx_le (prectx_contr p Γ Δ) Θ ->
  Γ x = Some (sΓ, τ) ->
  Θ x = Some (sΘ, τ) ->
  sens_le sΓ sΘ.
Proof.
  intros Hle HΓ HΘ.
  unfold prectx_le, prectx_contr in Hle.
  destruct (Δ x) as [[sΔ τΔ] |] eqn:HΔ.
  - edestruct (Hle x (sens_pnorm p sΓ sΔ) τ) as [r [Hr Hpr]].
    { now rewrite HΓ, HΔ. }
    rewrite HΘ in Hr; injection Hr as [= <-].
    eapply sens_le_trans; [apply sens_pnorm_le_r | exact Hpr].
  - edestruct (Hle x sΓ τ) as [r [Hr Hpr]].
    { now rewrite HΓ, HΔ. }
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
  unfold prectx_contr.
  rewrite HΓ.
  destruct (Δ x) as [[sΔ τΔ] |] eqn:HΔ.
  - specialize (Hcomp x s τ sΔ τΔ HΓ HΔ).
    subst τΔ.
    now exists (sens_pnorm p s sΔ).
  - now exists s.
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
  | TVar p Γ τ s x : Γ x = Some (s, τ) -> sens_le sens_1 s ->
      has_type (p, Γ) (TmVar x) τ
  | TAbs p Γ t σ τ : has_type (p, Some (sens_1, σ) .: Γ) t τ ->
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
      has_type (p, Some (s, τ2) .: Some (s, τ1) .: Δ) t τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmLetPair tpair t) τ
  | TInjL pΓ t τ1 τ2 : has_type pΓ t τ1 ->
      has_type pΓ (TmInjL t) (TyPlus τ1 τ2)
  | TInjR pΓ t τ1 τ2 : has_type pΓ t τ2 ->
      has_type pΓ (TmInjR t) (TyPlus τ1 τ2)
  | TCase p Γ Δ t tl tr s τ1 τ2 τ : prectx_comp Γ Δ ->
      has_type (p, Γ) t (TyPlus τ1 τ2) ->
      has_type (p, Some (s, τ1) .: Δ) tl τ ->
      has_type (p, Some (s, τ2) .: Δ) tr τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmCase t tl tr) τ
  | TBang p Γ Δ t τ s : prectx_comp Γ Δ ->
      has_type (p, Γ) t τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmBang t) (TyBang s τ)
  | TLetBang p Γ Δ t1 t2 τ1 τ r s : prectx_comp Γ Δ ->
      has_type (p, Γ) t1 (TyBang r τ1) ->
      has_type (p, Some (sens_mult r s, τ1) .: Δ) t2 τ ->
      has_type (p, prectx_contr p (prectx_scale s Γ) Δ) (TmLetBang t1 t2) τ
  | TWeakGt p q Γ t τ : has_type (p, Γ) t τ -> param_lt q p ->
      has_type (q, Γ) t τ
  | TWeakLt p q Γ t τ : has_type (p, Γ) t τ -> param_lt p q ->
      has_type (q, prectx_scale (sens_pnorm_c p q) Γ) t τ.

Example has_type_true : forall (pΓ : ctx), has_type pΓ TmTrue TyBool.
Proof.
  intro p.
  unfold TmTrue.
  apply TInjL.
  apply TUnit.
Qed.

(** For all types $τ$, we can derive
    $(2) \; x :_sqrt(2) τ ⊢ (x, x) : τ ⊗_2 τ$. *)
Example has_type_pair2 (τ : type) :
  has_type (param_2, Some (sens_sqrt2, τ) .: prectx_empty)
  (TmPair (TmVar 0%nat) (TmVar 0%nat)) (TyPair param_2 τ τ).
Proof.
  remember (Some (sens_1, τ) .: prectx_empty) as Γ1.
  remember (Some (sens_sqrt2, τ) .: prectx_empty) as Γ2.
  assert (prectx_contr param_2 Γ1 Γ1 = Γ2).
  - unfold prectx_contr.
    extensionality x.
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
  | ValBang v : is_value v -> is_value (TmBang v).

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
      evals_to (TmLetBang t tbody) v.

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

Lemma evals_to_is_value t v : evals_to t v -> is_value v.
Proof.
  intros H; induction H.
  all: eauto using is_value.
Qed.

(** ** Metatheory *)

(** *** Weakening *)

Definition prectx_pad (p : param) (s : sens) (Γ1 Δ : prectx) : prectx :=
  fun x =>
  match p with
  | param_infty => Δ x
  | param_real _ _ =>
      match Γ1 x, Δ x with
      | Some (s1, τ1), Some (sΔ, τΔ) =>
          match sΔ with
          | sens_infty => Some (sens_infty, τ1)
          | sens_real _ _ =>
              if sens_eq_dec (sens_mult s s1) sΔ
              then None
              else Some (sens_pad p (sens_mult s s1) sΔ, τ1)
          end
      | None, Some (sΔ, τ) => Some (sΔ, τ)
      | _, _ => None
      end
  end.

Section PrectxPad.
  Context (p : param) (s : sens) (Γ1 Γ2 Δ : prectx).
  Hypothesis H12 : prectx_comp Γ1 Γ2.
  Hypothesis Hle : prectx_le (prectx_contr p (prectx_scale s Γ1) Γ2) Δ.

  Let Δ2 := prectx_pad p s Γ1 Δ.

  Lemma prectx_pad_comp : prectx_comp Γ1 Δ2.
  Proof.
    intros x s1 τ1 s2 τ2 H1 H2.
    unfold Δ2, prectx_pad in H2.
    destruct p as [? ? |].
    - rewrite H1 in H2.
      destruct (Δ x) as [[[rΔ HΔ |] τΔ]|]; try discriminate.
      + destruct (sens_eq_dec (sens_mult s s1) (sens_real rΔ HΔ)).
        * discriminate.
        * injection H2 as [= _ <-]; reflexivity.
      + injection H2 as [= _ <-]; reflexivity.
    - unfold prectx_le, prectx_contr, prectx_scale in Hle.
      specialize (Hle x).
      rewrite H1 in Hle.
      destruct (Γ2 x) as [[s_Γ2 τ_Γ2]|] eqn:HΓ2.
      1: edestruct (Hle (sens_pnorm param_infty (sens_mult s s1) s_Γ2) τ1) as [sΔ [H _]].
      3: edestruct (Hle (sens_mult s s1) τ1) as [sΔ [H _]].
      all: try reflexivity.
      all: rewrite H in H2; injection H2 as [= _ <-]; reflexivity.
  Qed.

  Lemma prectx_pad_sound : Δ = prectx_contr p (prectx_scale s Γ1) Δ2.
  Proof.
    (* TODO: state and prove helper lemmas *)
  Admitted.

  Lemma prectx_pad_le : prectx_le Γ2 Δ2.
  Proof.
    (* TODO: state and prove helper lemmas *)
  Admitted.
End PrectxPad.

(** The weakening rule for precontexts is admissible. *)
Lemma weakening_prectx pΓ t τ (H : has_type pΓ t τ) :
  match pΓ with
  | (p, Γ) => forall Δ, prectx_le Γ Δ -> has_type (p, Δ) t τ
  end.
Proof.
  induction H; try destruct pΓ as [p Γ]; intros Θ Hle.
  all: try constructor.
  - unfold prectx_le in Hle.
    destruct (Hle x s τ H) as [sΘ [HΘ ?]].
    apply (TVar p Θ τ sΘ x HΘ).
    now apply sens_le_trans with s.
  - apply IHhas_type.
    now apply prectx_le_cons.
  - assert (Hpad : prectx_le (prectx_contr p (prectx_scale sens_1 Γ) Δ) Θ)
      by (rewrite prectx_scale_1; exact Hle).
    rewrite (prectx_pad_sound p sens_1 Γ Δ Θ H Hpad).
    rewrite prectx_scale_1.
    apply TApp with σ.
    * now apply prectx_pad_comp with Δ.
    * exact H0.
    * apply IHhas_type2, (prectx_pad_le p sens_1 Γ Δ Θ H Hpad).
  - assert (Hpad : prectx_le (prectx_contr p (prectx_scale sens_1 Γ) Δ) Θ)
      by (rewrite prectx_scale_1; exact Hle).
    rewrite (prectx_pad_sound p sens_1 Γ Δ Θ H Hpad).
    rewrite prectx_scale_1.
    apply TPair.
    * now apply prectx_pad_comp with Δ.
    * exact H0.
    * apply IHhas_type2, (prectx_pad_le p sens_1 Γ Δ Θ H Hpad).
  - rewrite (prectx_pad_sound p s Γ Δ Θ H Hle).
    apply TLetPair with τ1 τ2.
    * now apply prectx_pad_comp with Δ.
    * exact H0.
    * apply IHhas_type2.
      repeat apply prectx_le_cons.
      now apply prectx_pad_le.
  - now apply IHhas_type.
  - now apply IHhas_type.
  - rewrite (prectx_pad_sound p s Γ Δ Θ H Hle).
    apply TCase with τ1 τ2.
    + now apply prectx_pad_comp with Δ.
    + exact H0.
    + apply IHhas_type2.
      repeat apply prectx_le_cons.
      now apply prectx_pad_le.
    + apply IHhas_type3.
      repeat apply prectx_le_cons.
      now apply prectx_pad_le.
  - rewrite (prectx_pad_sound p s Γ Δ Θ H Hle).
    apply TBang.
    + now apply prectx_pad_comp with Δ.
    + exact H0.
  - rewrite (prectx_pad_sound p s Γ Δ Θ H Hle).
    apply TLetBang with τ1 r.
    * now apply prectx_pad_comp with Δ.
    * exact H0.
    * apply IHhas_type2.
      repeat apply prectx_le_cons.
      now apply prectx_pad_le.
  - apply TWeakGt with p.
    + now apply IHhas_type.
    + exact H0.
  - rewrite <- (prectx_scale_inv (real_pnorm_c p q) (real_pnorm_c_pos p q) Θ).
    apply TWeakLt.
    + apply IHhas_type.
      now apply prectx_scale_le_inv.
    + exact H0.
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
  | StructLt p q Γ :
      param_lt p q -> ctx_struct (p, Γ) (q, prectx_scale (sens_pnorm_c p q) Γ)
  | StructTrans pΓ1 pΓ2 pΓ3 :
      ctx_struct pΓ1 pΓ2 -> ctx_struct pΓ2 pΓ3 -> ctx_struct pΓ1 pΓ3.

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
  exists p' Γ' s',
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
  - solve_inv_struct IHhas_type Heqt_var StructLt.
Qed.

Lemma inversion_TmAbs pΓ t τ :
  has_type pΓ (TmAbs t) τ ->
  exists p' Γ' σ' τ',
    τ = TyArrow p' σ' τ' /\
    has_type (p', Some (sens_1, σ') .: Γ') t τ' /\
    ctx_struct (p', Γ') pΓ.
Proof.
  intros H; remember (TmAbs t) as t_abs.
  induction H; try discriminate Heqt_abs.
  - injection Heqt_abs as [= ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_abs StructGt.
  - solve_inv_struct IHhas_type Heqt_abs StructLt.
Qed.

Lemma inversion_TmApp pΓ f t τ :
  has_type pΓ (TmApp f t) τ ->
  exists p' Γ' Δ' σ',
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
  - solve_inv_struct IHhas_type Heqt_app StructLt.
Qed.

Lemma inversion_TmPair pΓ t1 t2 τ :
  has_type pΓ (TmPair t1 t2) τ ->
  exists p' Γ' Δ' τ1' τ2',
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
  - solve_inv_struct IHhas_type Heqt_pair StructLt.
Qed.

Lemma inversion_TmLetPair pΓ tpair t τ :
  has_type pΓ (TmLetPair tpair t) τ ->
  exists p' Γ' Δ' s' τ1' τ2',
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') tpair (TyPair p' τ1' τ2') /\
    has_type (p', Some (s', τ2') .: Some (s', τ1') .: Δ') t τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmLetPair tpair t) as t_letpair.
  induction H; try discriminate Heqt_letpair.
  - injection Heqt_letpair as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_letpair StructGt.
  - solve_inv_struct IHhas_type Heqt_letpair StructLt.
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
  exists p' Γ' Δ' s' τ1' τ2',
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t (TyPlus τ1' τ2') /\
    has_type (p', Some (s', τ1') .: Δ') tl τ /\
    has_type (p', Some (s', τ2') .: Δ') tr τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmCase t tl tr) as t_case.
  induction H; try discriminate Heqt_case.
  - injection Heqt_case as [= -> -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_case StructGt.
  - solve_inv_struct IHhas_type Heqt_case StructLt.
Qed.

Lemma inversion_TmBang pΓ t τ :
  has_type pΓ (TmBang t) τ ->
  exists p' Γ' Δ' τ' s',
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
  - solve_inv_struct IHhas_type Heqt_bang StructLt.
Qed.

Lemma inversion_TmLetBang pΓ t1 t2 τ :
  has_type pΓ (TmLetBang t1 t2) τ ->
  exists p' Γ' Δ' τ1' r' s',
    prectx_comp Γ' Δ' /\
    has_type (p', Γ') t1 (TyBang r' τ1') /\
    has_type (p', Some (sens_mult r' s', τ1') .: Δ') t2 τ /\
    ctx_struct (p', prectx_contr p' (prectx_scale s' Γ') Δ') pΓ.
Proof.
  intros H; remember (TmLetBang t1 t2) as t_letbang.
  induction H; try discriminate Heqt_letbang.
  - injection Heqt_letbang as [= -> ->].
    repeat eexists; repeat split; eauto.
    apply StructRefl.
  - solve_inv_struct IHhas_type Heqt_letbang StructGt.
  - solve_inv_struct IHhas_type Heqt_letbang StructLt.
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
  is_pushforward (0%nat .: ξ >>> (+1%nat)) (v .: Γ) (v .: Δ).
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

From Stdlib Require Import Classical.

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

Lemma pushforward_scale (ξ : var -> var) (s : sens) (Γ Δ : prectx) :
  is_pushforward ξ Γ Δ ->
  is_pushforward ξ (prectx_scale s Γ) (prectx_scale s Δ).
Proof.
  intros [Heq Hnone]. split.
  - intro x.
    unfold prectx_scale.
    now rewrite Heq.
  - intros y Hy.
    unfold prectx_scale.
    now rewrite Hnone.
Qed.

Lemma pushforward_contr (ξ : var -> var) p Γ1 Γ2 Δ1 Δ2 :
  is_pushforward ξ Γ1 Δ1 ->
  is_pushforward ξ Γ2 Δ2 ->
  is_pushforward ξ (prectx_contr p Γ1 Γ2) (prectx_contr p Δ1 Δ2).
Proof.
  intros [Hpf1_eq Hpf1_none] [Hpf2_eq Hpf2_none].
  split; intros; unfold prectx_contr.
  - now rewrite Hpf1_eq, Hpf2_eq. 
  - now rewrite Hpf1_none, Hpf2_none.
Qed.

Lemma renaming (p : param) (Γ Δ : prectx) (t : term) (τ : type)
  (ξ : var -> var) :
  is_injective ξ ->
  is_pushforward ξ Γ Δ ->
  has_type (p, Γ) t τ ->
  has_type (p, Δ) (t.[ren ξ]) τ.
Admitted.

(** *** Substitution *)

Lemma substitution (p : param) (Γ Δ : prectx)
  (t v : term) (s : sens) (σ τ : type) :
  has_type (p, Some (s, σ) .: Γ) t τ ->
  has_type (p, Δ) v σ ->
  prectx_comp Γ Δ ->
  has_type (p, prectx_contr p Γ (prectx_scale s Δ)) (t.[v/]) τ.
Admitted.

(** *** Subject reduction *)

Theorem subject_reduction (p : param) (Γ : prectx) (t v : term) (τ : type) :
  evals_to t v ->
  has_type (p, Γ) t τ ->
  has_type (p, Γ) v τ.
Admitted.
