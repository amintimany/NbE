From stdpp Require Import base list proof_irrel.
From Autosubst Require Import Autosubst.

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

Fixpoint type_interp `{!Base_Domain} (T : type) : Type :=
  match T with
  | Un => UnitDom
  | Arr W W' => (type_interp W) → (type_interp W')
  end.

Global Instance type_eqdec : EqDecision type.
Proof.
  intros ? ?; unfold Decision. decide equality.
Qed.

Definition ctx := list type.

Fixpoint ctx_interp `{!Base_Domain} Γ : Type :=
  match Γ with
  | [] => Datatypes.unit
  | T :: Γ' => (type_interp T) * ctx_interp Γ'
  end.

Definition f_equal {A B} (f : A → B) {x y : A} : x = y → f x = f y :=
  λ H, match H in _ = u return f x = f u with eq_refl => eq_refl end.

Program Definition Some_inj {A} : Inj (=) (=) (@Some A) :=
  λ x y H, f_equal (λ u, match u with Some w => w | None => x end) H.

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
| NE_NF Γ t Unit : NE Γ t Unit → NF Γ t Unit
| NF_Lam Γ t S T : NF (S :: Γ) t T → NF Γ (Lam t) (Arr S T)
with
NE : ctx → term → type → Prop :=
  NE_var Γ x T : Γ !! x = Some T → NE Γ (Var x) T
| NE_App Γ t t' S T : NE Γ t (Arr S T) → NF Γ t' S → NE Γ (App t t') T
.

Definition NFtype T := ∀ Γ, sigT (λ t, NF Γ t T).
Definition NEtype T := ∀ Γ, option (sigT (λ t, NE Γ t T)).

Definition NFinterp (T : type) : Type :=
  let _ := {| UnitDom := (NFtype Un) |} in
  type_interp T.

Program Definition NE_variable T (x : var) : NEtype T :=
  λ Γ,
  match Γ !! x as u return Γ !! x = u → option (sigT (λ t, NE Γ t T)) with
  | None => λ H, None
  | Some U => λ H,
    match decide (T = U) with
    | left H' => Some (existT (Var x) (NE_var Γ x T _))
    | right _ => None
    end
  end eq_refl.

Next Obligation.
Proof. intros; by destruct H'. Qed.

Program Fixpoint reflect T (neT : NEtype T) : NFinterp T :=
  match T as U return NEtype U → NFinterp U with
  | Un => λ neT Γ,
           match neT Γ with
           | None => existT un (NF_unit Γ)
           | Some s => existT (projT1 s) (NE_NF _ _ _ (projT2 s))
           end
  | Arr W W' =>
    λ neT s,
    reflect W'
         (λ Γ, match neT Γ with
                 | None => None
                 | Some t =>
                   Some
                     (existT
                        (App (projT1 t) (projT1 (reify W s Γ)))
                        (NE_App _ _ _ _ _ (projT2 t) (projT2 (reify W s Γ))))
               end)
  end neT
with
reify T (t : NFinterp T) : NFtype T :=
  match T as U return NFinterp U → NFtype U with
  | Un => λ s, s
  | Arr W W' =>
    λ f Γ, existT
             (Lam (projT1
                     (reify W' (f (reflect W (NE_variable W 0))) (W :: Γ))))
             (NF_Lam _ _ _ _
                     (projT2
                        (reify W' (f (reflect W (NE_variable W 0))) (W :: Γ))))
  end t.

Fixpoint reflect_ctx_rec Γ x :
    let _ := {| UnitDom := (NFtype Un) |} in
    ctx_interp Γ :=
  match Γ as u return ctx_interp u with
    | [] => ()
    | T :: Γ' => (reflect T (NE_variable T x),(reflect_ctx_rec Γ' (S x)))
  end.

Definition reflect_ctx Γ := reflect_ctx_rec Γ 0.

Definition interp_with_reflected_ctx {Γ t T} :
  typed Γ t T → @type_interp {| UnitDom := (NFtype Un) |} T :=
  let BD := {| UnitDom := (NFtype Un) |} in
  let BE := Build_Base_Elems BD (λ Γ, existT un (NF_unit Γ)) in
  λ Htp, @term_interp BD BE _ (reflect_ctx Γ) _ _ Htp.


Definition nf {Γ t T} (Htp : typed Γ t T) :=
  reify T (interp_with_reflected_ctx Htp) Γ.

Definition ex_term := App (Lam (Var 0)) un.

Lemma ex_term_tp : typed [] ex_term Un.
Proof. repeat econstructor. Defined.

Definition nf_ex_term := projT1 (nf ex_term_tp).

Lemma nf_ex_term_correct : nf_ex_term = un.
Proof. reflexivity. Qed.
