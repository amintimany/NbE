From Coq.ssr Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
From stdpp Require Import base list option proof_irrel.
From Autosubst Require Import Autosubst.

Ltac done := stdpp.tactics.done.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = match lt_dec x m with left _ => ids x | right _ => rename (+m) (f (x - m)) end.
  Proof.
    revert x; induction m as [|m IH]; intros [|x];
      repeat (case_match || asimpl || rewrite IH); auto with omega.
  Qed.
End Autosubst_Lemmas.

Definition f_equal {A B} (f : A → B) {x y : A} : x = y → f x = f y :=
  λ H, match H in _ = u return f x = f u with eq_refl => eq_refl end.

Program Definition Some_inj {A} : Inj (=) (=) (@Some A) :=
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
  λ Htp, @term_interp BD BE _ (reflect_ctx Γ) _ _ Htp.

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
