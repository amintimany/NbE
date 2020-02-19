From Coq.micromega Require Import Lia.
From Coq.ssr Require Export ssreflect.
From Coq.Unicode Require Export Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
Require Import Equations.Equations.

Import Compare_dec.

Import ListNotations.

Set Equations Transparent.

Derive NoConfusion for nat.
Derive NoConfusion for list.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = match lt_dec x m with left _ => ids x | right _ => rename (+m) (f (x - m)) end.
  Proof.
    revert x; induction m as [|m IH]; intros [|x];
      repeat (destruct lt_dec || asimpl || rewrite IH); auto; lia.
  Qed.
End Autosubst_Lemmas.

Class Base_Domain :=
  { UnitDom : Type
  }.

Class Base_Elems `{!Base_Domain} :=
  { UnitElem : UnitDom
  }.

Inductive term : Type :=
| Var : var → term
| un : term
| App : term → term → term
| Lam : {bind term} → term.

Derive NoConfusion for term.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive type : Type :=
  Un
| Arr : type → type → type.

Global Instance type_eqdec : EqDec type.
Proof. intros ??; decide equality. Defined.

Definition ctx := list type.

Inductive typed : ctx → term → type → Type :=
| TVarO Γ T : typed (T :: Γ) (Var 0) T
| TVarS Γ x T T' : typed Γ (Var x) T → typed (T' :: Γ) (Var (S x)) T
| TUnit Γ : typed Γ un Un
| TLam Γ t S T : typed (S :: Γ) t T → typed Γ (Lam t) (Arr S T)
| TApp Γ t t' S T : typed Γ t (Arr S T) → typed Γ t' S → typed Γ (App t t') T.

Lemma typed_weaken_var Δ1 Δ2 Δ3 x T :
  typed (Δ1 ++ Δ3) (Var x) T →
  typed (Δ1 ++ Δ2 ++ Δ3) (Var x).[upn (length Δ1) (ren (+ length Δ2))] T.
Proof.
  asimpl.
  rewrite iter_up.
  destruct lt_dec as [Hx|Hx]; simpl.
  - revert x Hx Δ2 Δ3. induction Δ1; simpl in *; intros x Hx Δ2 Δ3.
    { exfalso; lia. }
    destruct x.
    + inversion 1; constructor.
    + inversion 1; subst.
      constructor.
      apply IHΔ1; last assumption.
      lia.
  - revert x Hx Δ2 Δ3. induction Δ1; simpl in *; intros x Hx Δ2 Δ3.
    + rewrite PeanoNat.Nat.sub_0_r.
      induction Δ2; simpl; first by trivial.
      intros.
      constructor; auto.
    + intros Htp.
      destruct x; first (exfalso; lia).
      inversion Htp; subst.
      constructor.
      apply IHΔ1; last by auto.
      lia.
Qed.

Lemma typed_weaken Δ1 Δ2 Δ3 t T :
  typed (Δ1 ++ Δ3) t T →
  typed (Δ1 ++ Δ2 ++ Δ3) t.[upn (length Δ1) (ren (+ length Δ2))] T.
Proof.
  intros Htp.
  remember (Δ1 ++ Δ3) as Π.
  revert Δ1 Δ2 Δ3 HeqΠ.
  induction Htp; intros Δ1 Δ2 Δ3 HeqΠ.
  - apply typed_weaken_var.
    rewrite -HeqΠ; constructor.
  - apply typed_weaken_var.
    by rewrite -HeqΠ; constructor.
  - constructor.
  - asimpl.
    econstructor.
    eapply (IHHtp (_ :: _)).
    by rewrite HeqΠ.
  - asimpl.
    econstructor.
    + by apply IHHtp1.
    + by apply IHHtp2.
Qed.

Derive Signature for typed.

Fixpoint type_interp `{!Base_Domain} (T : type) : Type :=
  match T with
  | Un => UnitDom
  | Arr W W' => (type_interp W) → (type_interp W')
  end.

Fixpoint ctx_interp_type `{!Base_Domain} Γ : Type :=
  match Γ with
  | [] => Datatypes.unit
  | T :: Γ' => (type_interp T) * ctx_interp_type Γ'
  end.

Equations interp `{!Base_Domain, !Base_Elems}
          Γ (ρ : ctx_interp_type Γ) t T (Ht : typed Γ t T) : type_interp T :=
interp Γ ρ (Var 0) T (TVarO _ _) := fst ρ;
interp (T' :: Γ) ρ (Var (S x)) T (TVarS Γ x T T' Hx) :=
  interp Γ (snd ρ) (Var x) T Hx;
interp Γ ρ un T (TUnit _) := UnitElem;
interp Γ ρ (Lam t) _ (TLam Γ t T1 T2 Ht) := λ a, interp (T1 :: Γ) (a, ρ) _ _ Ht;
interp Γ ρ (App t1 t2) T (TApp Γ t1 t2 T1 T2 Ht1 Ht2) :=
  (interp _ _ _ _ Ht1) (interp _ _ _ _ Ht2).

Inductive NF : ctx → term → type → Prop :=
  NF_unit Γ : NF Γ un Un
| NE_NF Γ t : NE Γ t Un → NF Γ t Un
| NF_Lam Γ t S T : NF (S :: Γ) t T → NF Γ (Lam t) (Arr S T)
with
NE : ctx → term → type → Prop :=
  NE_varO Γ T : NE (T :: Γ) (Var 0) T
| NE_varS Γ x T T' : NE Γ (Var x) T → NE (T' :: Γ) (Var (S x)) T
| NE_App Γ t t' S T : NE Γ t (Arr S T) → NF Γ t' S → NE Γ (App t t') T.

Arguments NE_NF {_ _}.
Arguments NF_Lam {_ _ _ _} _.
Arguments NE_App {_ _ _ _ _} _ _.

Definition NFtype T := ∀ Γ, sigT (λ t, NF Γ t T).
Definition NEtype T := ∀ Γ, option (sigT (λ t, NE Γ t T))%type.

Definition NFinterp (T : type) : Type :=
  let _ := {| UnitDom := (NFtype Un) |} in type_interp T.

Equations is_prefix (Δ Γ : ctx) : option ctx :=
is_prefix [] Γ := Some Γ;
is_prefix (T :: Δ) [] := None;
is_prefix (T :: Δ) (T' :: Γ) :=
  match eq_dec T T' with
  | left _ => is_prefix Δ Γ
  | right _ => None
  end.

Lemma is_prefix_correct Δ Γ Ξ : is_prefix Δ Γ = Some Ξ → Γ = Δ ++ Ξ.
Proof.
  revert Γ; induction Δ; intros Γ.
  - inversion 1; reflexivity.
  - destruct Γ; simpl; first (inversion 1; fail).
    destruct eq_dec; last (inversion 1; fail).
    subst.
    intros HΔ.
    rewrite (IHΔ Γ HΔ).
    trivial.
Defined.

Lemma app_nil_r {A} (l : list A) : l ++ [] = l.
Proof.
  induction l as [|a l IHl]; first trivial.
  rewrite /= IHl //.
Defined.

Lemma app_assoc {A} (l1 l2 l3 : list A) : l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  revert l2 l3; induction l1 as [|a1 l1 IHl1]; intros l2 l3.
  - reflexivity.
  - rewrite /= IHl1 //.
Defined.

(* Lemma app_cons {A} (l l' : list A) (a : A) : l ++ a :: l' = (l ++ [a]) ++ l'. *)
(* Proof. *)
(*   induction l as [|b l IHl]; first reflexivity. *)
(*   rewrite /= IHl //. *)
(* Defined. *)

Lemma add_zero x : x + 0 = x.
Proof. induction x as [|x IHx]; first reflexivity. rewrite -IHx //. Defined.

Lemma Succ_add x y : S (x + y) = x + S y.
Proof.
  revert y; induction x; simpl; intros y; first reflexivity.
  rewrite IHx //.
Defined.

(* Lemma add_comm x y : x + y = y + x. *)
(* Proof. *)
(*   revert y; induction x as [|x IHx]; intros y. *)
(*   - rewrite add_zero //. *)
(*   - rewrite /= IHx Succ_add //. *)
(* Defined. *)

(* (* Lemma length_app_singleton {A} (l : list A) (a : A) : *) *)
(* (*   length (l ++ [a]) = length (a :: l). *) *)
(* (* Proof. *) *)
(* (*   induction l as [|b l IHl]; first reflexivity. *) *)
(* (*   rewrite /= IHl //. *) *)
(* (* Defined. *) *)

(* Lemma NE_var_lift Γ Δ x T : NE Γ (Var x) T → NE (Γ ++ Δ) (Var (length Δ + x)) T. *)
(* Proof. *)
(*   revert Γ x; induction Δ as [|T' Δ IHΔ]; intros Γ x. *)
(*   - rewrite app_nil_r; trivial. *)
(*   - rewrite app_cons /= Succ_add. *)
(*     intros. *)
(*     apply (IHΔ (Γ ++ [T']) (S x)). *)

Lemma rev_app {A} (l l' : list A) : rev (l ++ l') = rev l' ++ rev l.
Proof.
  revert l'; induction l as [|a l IHl]; intros l'.
  - rewrite /= app_nil_r //.
  - rewrite /= IHl app_assoc //.
Defined.

Lemma rev_involutive {A} (l : list A) : rev (rev l) = l.
Proof.
  induction l; simpl; trivial.
  rewrite rev_app IHl //.
Defined.

Lemma length_app {A} (l l' : list A) : length (l ++ l') = length l + length l'.
Proof.
  induction l as [|a l IHl]; first reflexivity.
  rewrite /= IHl //.
Defined.

Lemma rev_length {A} (l : list A) : length (rev l) = length l.
Proof.
  induction l as [|a l IHl]; first reflexivity.
  rewrite /= length_app IHl -Succ_add add_zero //.
Defined.

Equations NE_var_lift {Δ x T} Ξ :
  NE Δ (Var x) T → NE (Ξ ++ Δ) (Var (length Ξ + x)) T :=
  NE_var_lift [] Hx := Hx;
  NE_var_lift (T :: Ξ') Hx := NE_varS _ _ _ _ (NE_var_lift Ξ' Hx).

Lemma var_conv {Γ Δ x T Ξ} :
  is_prefix (rev Δ) (rev Γ) = Some Ξ →
  NE Δ (Var x) T →
  NE Γ (Var (length (rev Ξ) + x)) T.
Proof.
  intros Heq.
  rewrite -(rev_involutive Γ).
  rewrite (f_equal (@rev type) (is_prefix_correct _ _ _ Heq)).
  rewrite rev_app rev_involutive.
  apply NE_var_lift.
Defined.

(* Inductive is_prefix : ctx → ctx → Type := *)
(* | is_prefix_nil Ξ : is_prefix [] Ξ *)
(* | is_prefix_cons T Γ Ξ : is_prefix Γ Ξ → is_prefix (T :: Γ) (T :: Ξ). *)

(* Equations is_prefix_comp (Γ Ξ : ctx) : option (is_prefix Γ Ξ) := *)
(* is_prefix_comp [] Ξ := Some (is_prefix_nil Ξ); *)
(* is_prefix_comp (T :: Γ') [] := None; *)
(* is_prefix_comp (T :: Γ') (T' :: Ξ') := *)
(*   match eq_dec T T' with *)
(*   | left heq => *)
(*     match is_prefix_comp Γ' Ξ' with *)
(*     | None => None *)
(*     | Some ip => *)
(*       match heq in _ = z return option (is_prefix (T :: Γ') (z :: Ξ')) with *)
(*         | eq_refl => Some (is_prefix_cons T Γ' Ξ' ip) *)
(*       end *)
(*     end *)
(*   | right _ => None *)
(*   end. *)

(* Inductive nth_type_is (T : type) : nat → ctx → Prop := *)
(* | nth_type_is_here Γ : nth_type_is T 0 (T :: Γ) *)
(* | nth_type_is_there n T' Γ : nth_type_is T n Γ → nth_type_is T (S n) (T' :: Γ). *)

(* Equations NE_variable_is_prefix T (x : var) (Γ Ξ : ctx) : *)
(*   is_prefix Γ Ξ → nth_type_is T x Γ → option {t : term & NE Γ t T} := *)
(* NE_variable_is_prefix T x (T :: Γ) Ξ (nth_type_is_here Γ) := _. *)
(* NE_variable T (S _) [] Hx Ξ := _; *)
(* NE_variable T 0 (T' :: Γ) Hx [] := None; *)
(* NE_variable T 0 (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match (eq_trans (eq_sym (Some_eq Hx)) heq) in _ = u return *)
(*           option {t : term & NE (u :: Ξ) t T} with *)
(*     | eq_refl => (Some (existT (λ t, NE (T :: Ξ) t T) (Var 0) (NE_varO Ξ T))) *)
(*     end *)
(*   | right _ => None *)
(*   end; *)
(* NE_variable T (S x) (T' :: Γ) Hx [] := None; *)
(* NE_variable T (S x) (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match NE_variable T x Γ Hx Ξ with *)
(*     | None => None *)
(*     | Some (existT _ t Ht) => _ *)
(*     end *)
(*   | right _ => None *)
(*   end *)
(*   (* _ (NE_variable T x Γ Hx Ξ) *). *)
(* Next Obligation. *)


(* Equations NE_variable T (x : var) (Γ : ctx) : *)
(*     nth_error Γ x = Some T → NEtype T := *)
(* NE_variable T 0 [] Hx Ξ := _; *)
(* NE_variable T (S _) [] Hx Ξ := _; *)
(* NE_variable T 0 (T' :: Γ) Hx [] := None; *)
(* NE_variable T 0 (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match (eq_trans (eq_sym (Some_eq Hx)) heq) in _ = u return *)
(*           option {t : term & NE (u :: Ξ) t T} with *)
(*     | eq_refl => (Some (existT (λ t, NE (T :: Ξ) t T) (Var 0) (NE_varO Ξ T))) *)
(*     end *)
(*   | right _ => None *)
(*   end; *)
(* NE_variable T (S x) (T' :: Γ) Hx [] := None; *)
(* NE_variable T (S x) (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match NE_variable T x Γ Hx Ξ with *)
(*     | None => None *)
(*     | Some (existT _ t Ht) => _ *)
(*     end *)
(*   | right _ => None *)
(*   end *)
(*   (* _ (NE_variable T x Γ Hx Ξ) *). *)
(* Next Obligation. *)


(* Definition Some_eq {A} {x y : A} : Some x = Some y → x = y := *)
(*   λ H, *)
(*   match H in _ = z return x = (λ u, match u with | Some t => t | None => x end) z with *)
(*     eq_refl => eq_refl *)
(*   end. *)

(* Equations NE_variable T (x : var) (Γ : ctx) : *)
(*     nth_error Γ x = Some T → NEtype T := *)
(* NE_variable T 0 [] Hx Ξ := _; *)
(* NE_variable T (S _) [] Hx Ξ := _; *)
(* NE_variable T 0 (T' :: Γ) Hx [] := None; *)
(* NE_variable T 0 (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match (eq_trans (eq_sym (Some_eq Hx)) heq) in _ = u return *)
(*           option {t : term & NE (u :: Ξ) t T} with *)
(*     | eq_refl => (Some (existT (λ t, NE (T :: Ξ) t T) (Var 0) (NE_varO Ξ T))) *)
(*     end *)
(*   | right _ => None *)
(*   end; *)
(* NE_variable T (S x) (T' :: Γ) Hx [] := None; *)
(* NE_variable T (S x) (T' :: Γ) Hx (T'' :: Ξ) := *)
(*   match eq_dec T' T'' with *)
(*   | left heq => *)
(*     match NE_variable T x Γ Hx Ξ with *)
(*     | None => None *)
(*     | Some (existT _ t Ht) => _ *)
(*     end *)
(*   | right _ => None *)
(*   end *)
(*   (* _ (NE_variable T x Γ Hx Ξ) *). *)

(* Definition NE_variable T (x : var) (Γ : ctx) : *)
(*     nth_error Γ x = Some T → NEtype T. *)
(* Admitted. *)

Definition NE_variable {Γ x T} : NE Γ (Var x) T → NEtype T :=
  λ Hx Δ,
  match is_prefix (rev Γ) (rev Δ) as u return
        is_prefix (rev Γ) (rev Δ) = u → option {t : term & NE Δ t T}
  with
  | Some _ => λ heq, Some (existT _ _ (var_conv heq Hx))
  | None => λ _, None
  end eq_refl.

Equations reflect T (neT : NEtype T) : NFinterp T := {
reflect Un neT :=
  λ Γ, match neT Γ with
       | None => existT _ un (NF_unit Γ)
       | Some ne => existT _ (projT1 ne) (NE_NF (projT2 ne))
       end;
reflect (Arr T1 T2) neT :=
  λ nfT1 : NFinterp T1,
    reflect
      T2
      (λ Γ, match neT Γ with
            | None => None
            | Some ne =>
              let r := (reify T1 nfT1 Γ) in
              Some
                (existT
                   _
                   (App (projT1 ne) (projT1 r))
                   (NE_App (projT2 ne) (projT2 r)))
            end)
}
with
reify T (t : NFinterp T) : NFtype T := {
reify Un := λ nf, nf;
reify (Arr T1 T2) :=
  λ f Γ,
  let r := reify T2 (f (reflect T1 (NE_variable (NE_varO Γ T1)))) (T1 :: Γ) in
  existT _ (Lam (projT1 r)) (NF_Lam (projT2 r))
}.

Fixpoint reflect_ctx_rec (Δ Ξ : ctx) :
    let _ := {| UnitDom := (NFtype Un) |} in
    ctx_interp_type Ξ :=
  match Ξ as u return ctx_interp_type u with
  | [] => tt
  | (T :: Ξ') =>
    (reflect T (NE_variable (NE_var_lift Δ (NE_varO Ξ' T))),
     reflect_ctx_rec (Δ ++ [T]) Ξ')
  end.

Definition reflect_ctx Γ := reflect_ctx_rec [] Γ.

Definition interp_with_reflected_ctx {Γ t T} :
  typed Γ t T → @type_interp {| UnitDom := (NFtype Un) |} T :=
  let BD := {| UnitDom := (NFtype Un) |} in
  let BE := Build_Base_Elems BD (λ Γ, existT _ un (NF_unit Γ)) in
  @interp BD BE _ (reflect_ctx Γ) _ _.

Definition nf {Γ t T} (Htp : typed Γ t T) : sigT (λ t, NF Γ t T) :=
  reify T (interp_with_reflected_ctx Htp) Γ.

Definition ex_term := App (Lam (Var 0)) un.

Lemma ex_term_tp : typed [] ex_term Un.
Proof. repeat econstructor. Defined.

Definition nf_ex_term := projT1 (nf ex_term_tp).

Lemma nf_ex_term_correct : nf_ex_term = un.
Proof. reflexivity. Qed.

Definition ex2_term := App (Lam (App (Lam (Var 0)) (Var 0))) (Lam (Var 0)).

Lemma ex2_term_tp : typed [] ex2_term (Arr Un Un).
Proof. repeat econstructor. Defined.

Definition nf_ex2_term := projT1 (nf ex2_term_tp).

Lemma nf_ex2_term_correct : nf_ex2_term = Lam (Var 0).
Proof. reflexivity. Qed.

Definition ex3_term := App (Lam (Var 0)) (Var 1).

Lemma ex3_term_tp T T' : typed [T; T'] ex3_term T'.
Proof. repeat econstructor. Defined.

Definition nf_ex3_term T T' := projT1 (nf (ex3_term_tp T T')).

Lemma nf_ex3_open_term_correct_1 :
  nf_ex3_term Un (Arr Un Un) = Lam (App (Var 2) (Var 0)).
Proof. reflexivity. Qed.

Lemma nf_ex3_open_term_correct_2 :
  nf_ex3_term Un (Arr Un (Arr Un Un)) = Lam (Lam (App (App (Var 3) (Var 1)) (Var 0))).
Proof. reflexivity. Qed.

Inductive beta_eta : ctx → term → term → type → Type :=
| BE_refl Γ t T : beta_eta Γ t t T
| BE_trans Γ t1 t2 t3 T : beta_eta Γ t1 t2 T → beta_eta Γ t2 t3 T →
  beta_eta Γ t1 t3 T
| BE_symm Γ t1 t2 T : beta_eta Γ t1 t2 T → beta_eta Γ t2 t1 T
| BE_beta Γ t1 t2 T : beta_eta Γ (App (Lam t1) t2) (t1.[t2/]) T
| BE_eta Γ t T1 T2 : beta_eta Γ t (Lam (App t.[ren (+1)] (Var 0))) (Arr T1 T2)
| BE_app_L Γ t1 t1' t2 T1 T2 : beta_eta Γ t1 t1' (Arr T1 T2) →
                            beta_eta Γ (App t1 t2) (App t1' t2) T2
| BE_app_R Γ t1 t2 t2' T1 T2 : beta_eta Γ t2 t2' T1 →
                            beta_eta Γ (App t1 t2) (App t1 t2') T2
| BE_lam Γ t1 t2 T1 T2 : beta_eta (T1 :: Γ) t1 t2 T2 →
                            beta_eta Γ (Lam t1) (Lam t2) (Arr T1 T2).

Lemma beta_eta_typed Γ t t' T :
  beta_eta Γ t t' T → (typed Γ t T → typed Γ t' T) * (typed Γ t' T → typed Γ t T).
Proof.
  intros Hbe.
  induction Hbe.
  - intuition.
  - intuition.
  - intuition.
  - split.
    + intros Htp.
      inversion Htp; subst.
      inversion X; subst.
      


Lemma beta_eta_weaken Δ1 Δ2 Δ3 t t' T :
  beta_eta (Δ1 ++ Δ3) t t' T →
  beta_eta (Δ1 ++ Δ2 ++ Δ3)
           t.[upn (length Δ1) (ren (+ length Δ2))]
           t'.[upn (length Δ1) (ren (+ length Δ2))]
           T.
Proof.
  intros Hbe.
  remember (Δ1 ++ Δ3) as Π.
  revert Δ1 Δ2 Δ3 HeqΠ.
  induction Hbe; intros Δ1 Δ2 Δ3 HeqΠ.
  - apply BE_refl.
  - eapply BE_trans; eauto.
  - eapply BE_symm; auto.
  - replace (App (Lam t1) t2).[upn (length Δ1) (ren (+length Δ2))] with
        (App (Lam t1.[upn (S (length Δ1)) (ren (+length Δ2))])
             t2.[upn (length Δ1) (ren (+length Δ2))]); last by asimpl.
    replace t1.[t2/].[upn (length Δ1) (ren (+length Δ2))] with
    t1.[upn (S (length Δ1)) (ren (+length Δ2))]
       .[t2.[upn (length Δ1) (ren (+length Δ2))]/]; last by asimpl.
    apply BE_beta.
  - replace (Lam (App t.[ren (+1)] (Var 0))).[upn (length Δ1) (ren (+length Δ2))]
      with (Lam (App t.[upn (length Δ1) (ren (+length Δ2))].[ren (+1)] (Var 0)));
      last by asimpl.
    apply BE_eta.
  - asimpl.
    eapply BE_app_L; first by auto.
  - asimpl.
    eapply BE_app_R; last by auto.
  - asimpl.
    apply BE_lam.
    apply (IHHbe (_ :: _)).
    by rewrite HeqΠ.
Qed.

Definition term_nfinterp_pair Γ T : Type :=
  {t : term & typed Γ t T} * NFinterp T.

Program Fixpoint logrel (Γ : ctx) (T : type) (ta : term_nfinterp_pair Γ T) : Prop :=
  match T as u return (term_nfinterp_pair Γ u) → Prop with
  | Un => λ x,
         ∀ Γ', beta_eta (Γ' ++ Γ) (projT1 (fst ta)).[ren (+ length Γ')]
                          (projT1 (reify _ (snd x) (Γ' ++ Γ))) Un
  | Arr T1 T2 =>
    λ f, ∀ Γ' ta',
        logrel (Γ' ++ Γ) T1 ta' →
        logrel (Γ' ++ Γ)
               T2
               (existT
                  _
                  (App (projT1 (fst f)).[ren (+ length Γ')]
                                           (projT1 (fst ta')))
                  (TApp _ _ _ _ _
                        (typed_weaken [] _ _ _ _ (projT2 (fst f)))
                        (projT2 (fst ta'))), (snd f) (snd ta'))
  end ta.

Fixpoint term_interp_pairs (Γ : ctx) (Δ : ctx) : Type :=
  match Δ with
  | nil => unit
  | T :: Δ' => {x : term_nfinterp_pair Γ T | logrel Γ T x}
             * term_interp_pairs Γ Δ'
  end.

Fixpoint subst_of {Γ Δ} (ts : term_interp_pairs Γ Δ) : var → term :=
  match Δ as u return term_interp_pairs Γ u → var → term with
  | [] => λ _, ids
  | T :: Δ' => λ ts', projT1 (fst (proj1_sig (fst ts'))) .: (subst_of (snd ts'))
  end ts.

Fixpoint ctx_interp_of {Γ Δ} (ts : term_interp_pairs Γ Δ) : ctx_interp_type Δ :=
  match Δ as u return term_interp_pairs Γ u → ctx_interp_type u with
  | [] => λ _, tt
  | T :: Δ' => λ ts', (snd (proj1_sig (fst ts')), ctx_interp_of (snd ts'))
  end ts.

  (* let BD := {| UnitDom := (NFtype Un) |} in *)
  (* let BE := Build_Base_Elems BD (λ Γ, existT un (NF_unit Γ)) in *)
  (* @term_interp BD BE _ (reflect_ctx Γ) _ _ *)

(* Axiom UIP : ∀ {T : Type} {x : T} (e : x = x), e = eq_refl. *)

Lemma logrel_closed_under_beta_eta Γ T t t' a :
  beta_eta Γ (projT1 t) (projT1 t') T → logrel Γ T (t, a) → logrel Γ T (t', a).
Proof.
  revert Γ t t' a.
  induction T.
  - intros Γ t t' a Hbe Hta Γ'.
    specialize (Hta Γ').
    simpl in *.
    eapply BE_trans; last eauto.
    apply BE_symm.
    by apply (beta_eta_weaken []).
  - simpl in *.
    intros Γ t t' a Hbe Hta Γ' ta' Hta'.
    eapply IHT2; last by eauto.
    eapply BE_app_L.
    + apply (beta_eta_weaken []); eauto.
    + apply (projT2 (fst ta')).
Qed.

Lemma logrel_subst
      Ξ1 Ξ2 t T (Htp : typed (Ξ1 ++ Ξ2) t T) Δ (ts : term_interp_pairs Δ Ξ2) :
  typed (Ξ1 ++ Δ) t.[upn (length Ξ1) (subst_of ts)] T.
Proof.
  remember (Ξ1 ++ Ξ2) as Ξ.
  revert Ξ1 Ξ2 Δ ts HeqΞ.
  induction Htp; intros Ξ1 Ξ2 Δ ts HeqΞ.
  - asimpl.
    destruct Ξ1; inversion HeqΞ; subst; asimpl.
    + destruct Ξ2; inversion HeqΞ; subst.
      destruct ts as [[u ?] ?]; simpl.
      apply (projT2 (fst u)).
    + constructor.
  - asimpl.
    destruct Ξ1; inversion HeqΞ; subst; asimpl.
    + destruct Ξ2; inversion HeqΞ; subst.
      destruct ts as [? ts']; simpl.
      simpl in *.
      by apply (IHHtp []).
    + apply (typed_weaken [] [_]); simpl.
      by apply IHHtp.
  - constructor.
  - simpl; constructor.
    apply (IHHtp (_ :: _)).
    by rewrite HeqΞ.
  - asimpl.
    econstructor; eauto.
Qed.

Lemma fundamental Γ t T (Htp : typed Γ t T) :
  ∀ Δ (ts : term_interp_pairs Δ Γ) Htp',
    logrel Δ T ((existT _ t.[subst_of ts] Htp'),
                let BD := {| UnitDom := (NFtype Un) |} in
                let BE := Build_Base_Elems BD (λ Γ, existT _ un (NF_unit Γ)) in
                @interp BD BE _ (ctx_interp_of ts) t T Htp).
Proof.
  induction Htp; simpl in *.
  - intros Δ ts.
    rewrite /apply_noConfusion /=.
    pose proof (proj2_sig (fst ts)) as Hx; simpl in *.
    revert Hx. case: (proj1_sig (fst ts)); simpl; auto.
  - asimpl.
    intros Δ ts.
    apply IHHtp.
  - intros Δ ts Γ'.
    constructor.
  - asimpl.
    intros Δ ts Γ' ta' Hta'.
    


  - intros Δ ts.
    revert dependent x.
    induction Γ; asimpl; first done.
    intros x e.
    destruct x.
    + simpl in *; inversion e; simplify_eq.
      destruct ts as [[[] []] ?]; simpl in *.
      rewrite (UIP e) //=.
    + simpl in *.
      destruct ts; simpl in *.
      apply IHΓ.
  - intros; constructor.
  - 
















































Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = match lt_dec x m with left _ => ids x | right _ => rename (+m) (f (x - m)) end.
  Proof.
    revert x; induction m as [|m IH]; intros [|x];
      repeat (destruct lt_dec || asimpl || rewrite IH); auto with lia.
  Qed.
End Autosubst_Lemmas.

Definition f_equal {A B} (f : A → B) {x y : A} : x = y → f x = f y :=
  λ H, match H in _ = u return f x = f u with eq_refl => eq_refl end.

Definition Some_inj {A} : Inj (=) (=) (@Some A) :=
  λ x y H, f_equal (λ u, match u with Some w => w | None => x end) H.

Section list_ops.
  Context {A : Type}.

  Lemma reverse_involutive (l : list A) : reverse (reverse l) = l.
  Proof.
    rewrite /reverse.
    change l with (rev_append [] l) at 2.
    generalize (@nil A) at 1 3 as z.
    induction l; intros z; trivial.
    simpl; rewrite IHl; trivial.
  Defined.

  Lemma reverse_append_nil (l w z : list A) :
    rev_append l (w ++ z) = rev_append l w ++ z.
  Proof.
    revert w z; induction l; intros w z; rewrite //= (IHl (_ :: _)) //.
  Defined.

  Lemma reverse_app (l1 l2 : list A) :
    reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
  Proof.
    rewrite /reverse.
    generalize (@nil A) at 1 3 as z.
    revert l2; induction l1; intros l2 z; simpl.
    - apply (reverse_append_nil _ []).
    - rewrite IHl1 //.
  Defined.

  Context `{EqDecision A}.

  Fixpoint take_postfix (pre l: list A) : option (list A) :=
    match pre with
    | [] => Some l
    | x :: pre' =>
      match l with
      | [] => None
      | a :: l' => if decide (a = x) is left _ then take_postfix pre' l' else None
      end
    end.

  Lemma take_postfix_post pre l post :
    take_postfix pre l = Some post → l = pre ++ post.
  Proof.
    revert l post; induction pre as [|x pre];
      intros l post; first by inversion 1.
    destruct l as [|z l]; first by inversion 1.
    simpl; destruct decide; last by inversion 1.
    inversion 1; simplify_eq; apply f_equal. by apply IHpre.
  Defined.

  Definition take_prefix (pre l: list A) : option (list A) :=
    (take_postfix (reverse pre) (reverse l)) ≫= (λ x, Some (reverse x)).

  Lemma take_prefix_pre post l pre :
    take_prefix post l = Some pre → l = pre ++ post.
  Proof.
    rewrite /take_prefix.
    destruct (take_postfix (reverse post) (reverse l)) as [p|] eqn:Heq;
      last done.
    simpl; inversion 1; subst.
    rewrite -(reverse_involutive l) -(reverse_involutive post) -reverse_app.
    by apply f_equal; apply take_postfix_post.
  Defined.

End list_ops.

Inductive term : Type :=
| Var : var → term
| un : term
| App : term → term → term
| Lam : {bind term} → term.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Global Instance term_eqdec : EqDecision term.
Proof.
  intros ? ?; unfold Decision. decide equality.
  decide equality.
Qed.

Class Base_Domain :=
  { UnitDom : Type
  }.

Class Base_Elems `{!Base_Domain} :=
  { UnitElem : UnitDom
  }.

Inductive type : Type :=
  Un
| Arr : type → type → type.

Global Instance type_eqdec : EqDecision type.
Proof.
  intros ? ?; unfold Decision. decide equality.
Defined.

Fixpoint type_interp `{!Base_Domain} (T : type) : Type :=
  match T with
  | Un => UnitDom
  | Arr W W' => (type_interp W) → (type_interp W')
  end.

Definition ctx := list type.

Fixpoint ctx_interp `{!Base_Domain} Γ : Type :=
  match Γ with
  | [] => Datatypes.unit
  | T :: Γ' => (type_interp T) * ctx_interp Γ'
  end.

Program Fixpoint var_interp `{!Base_Domain, !Base_Elems}
        Γ (ρ : ctx_interp Γ) (x : var) T :
  Γ !! x = Some T → type_interp T :=
  λ H,
  match x as z return ctx_interp Γ → Γ !! z = Some T → type_interp T with
  | O => match Γ as u return ctx_interp u → u !! O = Some T → type_interp T with
        | [] => λ ρ H,
               False_rect
                 (type_interp T)
                 match
                   f_equal (λ x, match x return Prop with None => True | _ => False end) H
                   in _ = W return W with
                   eq_refl => I
                 end
        | U :: _ => λ ρ H,
                   match Some_inj _ _ H in _ = W return type_interp W with
                     eq_refl => fst ρ
                   end
        end
  | S n => match Γ as u return ctx_interp u → u !! S n = Some T → type_interp T
          with
          | [] => λ ρ H,
                 False_rect
                   (type_interp T)
                   match
                     f_equal (λ x, match x return Prop with None => True | _ => False end) H
                     in _ = W return W with
                     eq_refl => I
                   end
          | U :: Γ' => λ ρ H, var_interp Γ' (snd ρ) n T H
          end
  end ρ H.

Inductive typed : ctx → term → type → Type :=
| TVar Γ x T : Γ !! x = Some T → typed Γ (Var x) T
| TUnit Γ : typed Γ un Un
| TLam Γ t S T : typed (S :: Γ) t T → typed Γ (Lam t) (Arr S T)
| TApp Γ t t' S T : typed Γ t (Arr S T) → typed Γ t' S → typed Γ (App t t') T
.

Program Fixpoint term_interp `{!Base_Domain, !Base_Elems}
        Γ (ρ : ctx_interp Γ) t T :
  typed Γ t T → type_interp T :=
  match t as u return typed Γ u T → type_interp T with
  | Var n => λ H, var_interp Γ ρ n T _
  | un => λ H, match _ : Un = T in _ = y return type_interp y with
                  eq_refl => UnitElem end
  | App t1 t2 => λ H,
               (λ HAPP :
                  sigT (λ T',
                        sigT (λ HtT,
                              (sigT (λ Ht'T, H = TApp Γ t1 t2 T' T HtT Ht'T)))),
                  (term_interp Γ ρ t1 (Arr (projT1 HAPP) T)
                               (projT1 (projT2 HAPP)))
                    (term_interp Γ ρ t2 (projT1 HAPP)
                                 (projT1 (projT2 (projT2 HAPP))))
               ) _
  | Lam s => λ H,
               (λ HLAM :
                  sigT (λ T1,
                        sigT (λ T2,
                              sigT (λ Teq : T = Arr T1 T2,
                                   (sigT (λ HsT,
                                          match Teq in _ = U
                                                return typed Γ (Lam s) U with
                                            eq_refl => H
                                          end= TLam Γ s T1 T2 HsT))))),
                  match
                    eq_sym (projT1 (projT2 (projT2 HLAM)))
                    in _ = U return type_interp U with
                    eq_refl => λ a,
                              term_interp
                                (projT1 HLAM :: Γ) (a, ρ) s
                                (projT1 (projT2 HLAM))
                                (projT1 (projT2 (projT2 (projT2 HLAM))))
                  end
               ) _
  end.

Next Obligation.
Proof. by intros ? ? ? ? ? ? ? Htp; inversion Htp; subst. Defined.

Next Obligation.
Proof. by intros ? ? ? ? ? ? Htp; inversion Htp; subst. Defined.

Next Obligation.
Proof.
  intros HDM ? ? _ _ T t1 t2 Htp.
  clear dependent HDM.
  set (Δ := Γ); unfold Δ.
  set (s := App t1 t2); unfold s.
  set (U := T); unfold U.
  pose (Htp : typed Δ s U) as TP.
  pose (eq_refl : Δ = Γ) as HΓ.
  pose (eq_refl : U = T) as HT.
  pose (eq_refl : s = (App t1 t2)) as Ht.
  pose (eq_refl :
          match HΓ in _ = u return typed u (App t1 t2) T with
            eq_refl =>
            match Ht in _ = z return typed Δ z T with
              eq_refl =>
              match HT in _ = W return typed Δ s W with
                eq_refl => TP
              end
            end
          end = Htp) as Htpeq.
  clearbody Htpeq HT HΓ Ht TP.
  clearbody Δ s U.
  destruct TP; inversion Ht; simplify_eq.
  exists S, TP1, TP2.
    by rewrite (eq_pi _ _ Ht eq_refl).
Defined.

Next Obligation.
Proof.
  intros HDM ? ? _ _ T t Htp.
  clear dependent HDM.
  set (Δ := Γ); unfold Δ.
  set (s := Lam t); unfold s.
  set (U := T); unfold U.
  pose (Htp : typed Δ s U) as TP.
  pose (eq_refl : Δ = Γ) as HΓ.
  pose (eq_refl : U = T) as HT.
  pose (eq_refl : s = Lam t) as Ht.
  pose (eq_refl :
          match HΓ in _ = u return typed u (Lam t) T with
            eq_refl =>
            match Ht in _ = z return typed Δ z T with
              eq_refl =>
              match HT in _ = W return typed Δ s W with
                eq_refl => TP
              end
            end
          end = Htp) as Htpeq.
  clearbody Htpeq HT HΓ Ht TP.
  clearbody Δ s U.
  destruct TP; try discriminate. (* a bug similar to the one above prevents
                                    rewriting some of the equalities or
                                    using subst or simplify_eq *)
  assert (t0 = t) as Hteq by congruence.
  eexists _, _, (eq_sym HT),
  (match HΓ in _ = u return
         typed (S :: u) t T0
   with
     eq_refl =>
     match Hteq in _ = w return
           typed (S :: Γ0) w T0
     with
       eq_refl => TP
     end
   end
  ).
  rewrite <- Htpeq; clear Htpeq.
  destruct HΓ. destruct Hteq.
  destruct HT; simpl.
  by rewrite (eq_pi _ _ Ht eq_refl).
Defined.

Inductive NF : ctx → term → type → Prop :=
  NF_unit Γ : NF Γ un Un
| NE_NF Γ t : NE Γ t Un → NF Γ t Un
| NF_Lam Γ t S T : NF (S :: Γ) t T → NF Γ (Lam t) (Arr S T)
with
NE : ctx → term → type → Prop :=
  NE_var Γ x T : Γ !! x = Some T → NE Γ (Var x) T
| NE_App Γ t t' S T : NE Γ t (Arr S T) → NF Γ t' S → NE Γ (App t t') T
.

Lemma NF_lift Ξ Δ Γ t T :
  NF (Ξ ++ Γ) t T → NF (Ξ ++ Δ ++ Γ) t.[upn (length Ξ) (ren (+(length Δ)))] T
with
NE_lift Ξ Δ Γ t T :
  NE (Ξ ++ Γ) t T → NE (Ξ ++ Δ ++ Γ) t.[upn (length Ξ) (ren (+(length Δ)))] T.
Proof.
  - intros HNF. remember (Ξ ++ Γ) as ξ. revert Ξ Γ Heqξ.
    induction HNF => Ξ Γ' Heqξ.
    + apply NF_unit.
    + apply NE_NF. apply NE_lift. rewrite -Heqξ //.
    + simpl. apply NF_Lam.
      apply (IHHNF (_ :: _)).
      rewrite Heqξ //.
  - intros HNF. remember (Ξ ++ Γ) as ξ. revert Ξ Γ Heqξ.
    induction HNF as [? x ? Hlu|] => Ξ Γ' Heqξ.
    + subst.
      asimpl. rewrite iter_up.
      destruct lt_dec.
      * apply NE_var.
        rewrite lookup_app_l // in Hlu.
        rewrite lookup_app_l //.
      * rewrite lookup_app_r in Hlu; last eauto with omega.
        apply NE_var; simpl.
        rewrite lookup_app_r; last eauto with omega.
        replace (length Ξ + (length Δ + (x - length Ξ)) - length Ξ) with
               ((length Δ + x - length Ξ)) by omega.
        rewrite lookup_app_r; last eauto with omega.
        replace (length Δ + x - length Ξ - length Δ) with (x - length Ξ)
          by omega.
        trivial.
    + subst.
      eapply NE_App; eauto.
Qed.

Definition NFtype T := ∀ Γ, sigT (λ t, NF Γ t T).
Definition NEtype T := ∀ Γ, option (sigT (λ t, NE Γ t T))%type.

Definition NFinterp (T : type) : Type :=
  let _ := {| UnitDom := (NFtype Un) |} in
  type_interp T.

Definition NE_variable T (x : var) (Γ : ctx) :
    Γ !! x = Some T → NEtype T :=
  λ Hx Ξ,
  match take_prefix Γ Ξ as u return
        (match u return Type with
        | None => unit
        | Some z => z ++ Γ = Ξ
        end) → option (sigT (λ t, NE Ξ t T))
  with
  | None => λ _, None
  | Some Δ =>
    λ H,
    match H in _ = z return option (sigT (λ t, NE z t T)) with
    | eq_refl => Some (existT _ (NE_lift [] Δ Γ _ _ (NE_var _ _ _ Hx)))
    end
  end
    (match take_prefix Γ Ξ as u return
           take_prefix Γ Ξ = u → (match u return Type with
                                  | None => unit
                                  | Some w => w ++ Γ = Ξ
                                  end)
     with
     | None => λ _, ()
     | Some z => λ H, eq_sym (take_prefix_pre _ _ _ H)
     end eq_refl
    ).

Program Fixpoint reflect T (neT : NEtype T) : NFinterp T :=
  match T as U return NEtype U → NFinterp U with
  | Un => λ neT Γ,
           match neT Γ with
           | None => existT un (NF_unit Γ)
           | Some s => existT (projT1 s)
                             (NE_NF _ _ (projT2 s))
           end
  | Arr W W' =>
    λ neW s,
    reflect W'
         (λ Γ,
          match neW Γ with
          | None => None
          | Some t =>
            Some
              (existT
                 (App (projT1 t)
                      (projT1 (reify W s Γ)))
                 (NE_App _ _ _ _ _ (projT2 t) (projT2 (reify W s Γ))))
          end)
  end neT
with
reify T (t : NFinterp T) : NFtype T :=
  match T as U return NFinterp U → NFtype U with
  | Un => λ s, s
  | Arr W W' =>
    λ f Γ,
    existT
      (Lam
         (projT1
            (reify
               W'
               (f (reflect W (NE_variable W 0 (W :: Γ) eq_refl))) (W :: Γ))))
      (NF_Lam
         _ _ _ _
         (projT2
            (reify
               W'
               (f (reflect W (NE_variable W 0 (W :: Γ) eq_refl))) (W :: Γ))))
  end t.

Program Fixpoint reflect_ctx_rec Γ Δ Ξ :
    let _ := {| UnitDom := (NFtype Un) |} in
    Γ = Δ ++ Ξ → ctx_interp Ξ :=
  match Ξ as u return Γ = Δ ++ u → ctx_interp u with
    | [] => λ _, ()
    | T :: Ξ' => λ H, (reflect T (NE_variable T (length Δ) Γ _),
                      (reflect_ctx_rec Γ (Δ ++ [T]) Ξ' _))
  end.

Next Obligation.
Proof.
  intros Γ Δ Ξ T Γ' Heq; rewrite Heq; clear Γ Heq; revert T Γ'.
  induction Δ; intros T Γ'; first trivial.
  apply IHΔ.
Defined.

Next Obligation.
Proof.
  intros Γ Δ _ T Ξ' ->.
  rewrite -assoc //.
Defined.

Definition reflect_ctx Γ := reflect_ctx_rec Γ [] Γ eq_refl.

Definition interp_with_reflected_ctx {Γ t T} :
  typed Γ t T → @type_interp {| UnitDom := (NFtype Un) |} T :=
  let BD := {| UnitDom := (NFtype Un) |} in
  let BE := Build_Base_Elems BD (λ Γ, existT un (NF_unit Γ)) in
  @term_interp BD BE _ (reflect_ctx Γ) _ _.

Definition nf {Γ t T} (Htp : typed Γ t T) : sigT (λ t, NF Γ t T) :=
  reify T (interp_with_reflected_ctx Htp) Γ.

Definition ex_term := App (Lam (Var 0)) un.

Lemma ex_term_tp : typed [] ex_term Un.
Proof. repeat econstructor. Defined.

Definition nf_ex_term := projT1 (nf ex_term_tp).

Lemma nf_ex_term_correct : nf_ex_term = un.
Proof. reflexivity. Qed.

Definition ex2_term := App (Lam (App (Lam (Var 0)) (Var 0))) (Lam (Var 0)).

Lemma ex2_term_tp : typed [] ex2_term (Arr Un Un).
Proof. repeat econstructor. Defined.

Definition nf_ex2_term := projT1 (nf ex2_term_tp).

Lemma nf_ex2_term_correct : nf_ex2_term = Lam (Var 0).
Proof. reflexivity. Qed.

Definition ex3_term := App (Lam (Var 0)) (Var 1).

Lemma ex3_term_tp T T' : typed [T; T'] ex3_term T'.
Proof. repeat econstructor. Defined.

Definition nf_ex3_term T T' := projT1 (nf (ex3_term_tp T T')).

Lemma nf_ex3_open_term_correct_1 :
  nf_ex3_term Un (Arr Un Un) = Lam (App (Var 2) (Var 0)).
Proof. reflexivity. Qed.

Lemma nf_ex3_open_term_correct_2 :
  nf_ex3_term Un (Arr Un (Arr Un Un)) = Lam (Lam (App (App (Var 3) (Var 1)) (Var 0))).
Proof. reflexivity. Qed.

Inductive beta_eta : ctx → term → term → type → Prop :=
| BE_refl Γ t T : beta_eta Γ t t T
| BE_trans Γ t1 t2 t3 T : beta_eta Γ t1 t2 T → beta_eta Γ t2 t3 T →
  beta_eta Γ t1 t3 T
| BE_symm Γ t1 t2 T : beta_eta Γ t1 t2 T → beta_eta Γ t2 t1 T
| BE_beta Γ t1 t2 T : beta_eta Γ (App (Lam t1) t2) (t1.[t2/]) T
| BE_eta Γ t T1 T2 : beta_eta Γ t (Lam (App t (Var 0))) (Arr T1 T2)
| BE_app_L Γ t1 t1' t2 T1 T2 : beta_eta Γ t1 t1' (Arr T1 T2) → typed Γ t2 T1 →
                            beta_eta Γ (App t1 t2) (App t1' t2) T2
| BE_app_R Γ t1 t2 t2' T1 T2 : typed Γ t1 (Arr T1 T2) → beta_eta Γ t2 t2' T1 →
                            beta_eta Γ (App t1 t2) (App t1 t2') T2
| under_lam Γ t1 t2 T1 T2 : beta_eta (T1 :: Γ) t1 t2 T2 →
                            beta_eta Γ (Lam t1) (Lam t2) (Arr T1 T2).

Fixpoint logrel (Γ : ctx) (T : type) (ta : term * NFinterp T) : Prop :=
  match T as u return NFinterp u → Prop with
  | Un => λ x, ∀ Γ', beta_eta Γ ta.1 (projT1 (reify _ x (Γ' ++ Γ))) Un
  | Arr T1 T2 => λ f, ∀ Γ' ta', logrel (Γ' ++ Γ) T1 ta' →
                            logrel (Γ' ++ Γ) T2 (App ta.1 ta'.1, f ta'.2)
  end ta.2.

Fixpoint term_interp_pairs (Γ : ctx) (Δ : ctx) : Type :=
  match Δ with
  | nil => unit
  | T :: Δ' => {x : (term * NFinterp T) & (typed Γ x.1 T * logrel Γ T x)%type}
             * term_interp_pairs Γ Δ'
  end.

Fixpoint subst_of {Γ Δ} (ts : term_interp_pairs Γ Δ) : var → term :=
  match Δ as u return term_interp_pairs Γ u → var → term with
  | [] => λ _, ids
  | T :: Δ' => λ ts', (projT1 ts'.1).1 .: (subst_of ts'.2)
  end ts.

Fixpoint ctx_interp_of {Γ Δ} (ts : term_interp_pairs Γ Δ) : ctx_interp Δ :=
  match Δ as u return term_interp_pairs Γ u → ctx_interp u with
  | [] => λ _, ()
  | T :: Δ' => λ ts', ((projT1 ts'.1).2, ctx_interp_of ts'.2)
  end ts.

  (* let BD := {| UnitDom := (NFtype Un) |} in *)
  (* let BE := Build_Base_Elems BD (λ Γ, existT un (NF_unit Γ)) in *)
  (* @term_interp BD BE _ (reflect_ctx Γ) _ _ *)

Axiom UIP : ∀ {T : Type} {x : T} (e : x = x), e = eq_refl.

Lemma fundamental Γ t T (Htp : typed Γ t T) :
  ∀ Δ (ts : term_interp_pairs Δ Γ),
    logrel Δ T (t.[subst_of ts],
                let BD := {| UnitDom := (NFtype Un) |} in
                let BE := Build_Base_Elems BD (λ Γ, existT un (NF_unit Γ)) in
                @term_interp BD BE _ (ctx_interp_of ts) t T Htp).
Proof.
  induction Htp; simpl in *.
  - intros Δ ts.
    revert dependent x.
    induction Γ; asimpl; first done.
    intros x e.
    destruct x.
    + simpl in *; inversion e; simplify_eq.
      destruct ts as [[[] []] ?]; simpl in *.
      rewrite (UIP e) //=.
    + simpl in *.
      destruct ts; simpl in *.
      apply IHΓ.
  - intros; constructor.
  - 




