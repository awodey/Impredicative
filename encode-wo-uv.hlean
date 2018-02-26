import imp_prop_trunc 

open funext eq trunc is_trunc prod sum pi function is_equiv

attribute trunc.rec [recursor] 

definition my.inv (A : Type)(x y : A)(p : x = y) : y = x :=
  eq.rec (eq.refl x) p

abbreviation U     := Type.{0} 
abbreviation UPrp  := trunctype.{0} -1
abbreviation USet  := trunctype.{0} 0
abbreviation UGpd  := trunctype.{0} 1 

definition tprod {n : ℕ₋₂} {A : Type} (B : A → trunctype.{0} n) 
  :  trunctype.{0} n
  := trunctype.mk (∀ x, B x) (is_trunc_pi B n)
notation `π` binders `,` r:(scoped P, tprod P) := r
definition tto {n : ℕ₋₂} (A B : trunctype.{0} n) : trunctype.{0} n
  := π x : A, B
reserve infix ` ⇒ `:21
infix ` ⇒ ` := tto

axioms (A : Type) (B : A → UPrp)
--check P x : A, B x


/- Encoding of Propostions -/

/- conjunction of propositions -/

definition and (A B : UPrp) : UPrp := π X : UPrp, (A ⇒ (B ⇒ X)) ⇒ X
definition con {A B : UPrp} (p : A) (q : B) :  and A B := λ X f, f p q
definition and_rec {A B C : UPrp} (f : A ⇒ (B ⇒ C))  (p : and A B) : C := p C f
definition and_beta {A B C : UPrp} (f : A ⇒ (B ⇒ C)) (a : A) (b : B) 
  : and_rec f (@con A B a b) = f a b := rfl
definition and_eta {A B C : UPrp} (f : and A B ⇒ C)
  :  f = and_rec (λ a b, f (@con A B a b)) 
  := eq_of_homotopy (λ x, is_prop.elim _ _)
definition and_univ_prop {A B C : UPrp} : (and A B ⇒ C) ≃ (A ⇒ (B ⇒ C)) 
  := equiv_of_is_prop (λ f a b, f (@con A B a b)) and_rec
definition and_prl {A B : UPrp} (p : and A B) : A := p (λ x y, x)
definition and_prr {A B : UPrp} (p : and A B) : B := p (λ x y, y)

/- Disjunction of propositions -/

definition or (A B : UPrp) : UPrp := π X : UPrp, (A ⇒ X) ⇒ ((B ⇒ X) ⇒ X)
definition or_inl {A B : UPrp} (a : A) : or A B := λX f g, f a
definition or_inr {A B : UPrp} (b : B) : or A B := λX f g, g b
definition or_rec {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (v : or A B) : C 
  := v C f g
definition or_beta_l {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (a : A)
  : or_rec f g (@or_inl A B a) = f a := rfl
definition or_beta_r {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (b : B)
  : or_rec f g (@or_inr A B b) = g b := rfl
definition or_eta {A B C : UPrp} (h : or A B ⇒ C)
  : h = or_rec (λ a, h (@or_inl A B a)) (λ b, h (@or_inr A B b)) 
  := eq_of_homotopy (λ v, is_prop.elim _ _)
definition or_univ_prop {A B C : UPrp} 
  :  (or A B ⇒ C) ≃ and (A ⇒ C) (B ⇒ C)
  := equiv_of_is_prop (λ h X k, k (h ∘ or_inl) (h ∘ or_inr))
     (λ p v, v C (p _ (λ x y, x)) (p _ (λ x y, y)))

/- Propositional truncation of small types -/

definition  PropTrunc (A : U) : U := -- could be Type instead of U
  Π(X : UPrp), (A → X) → X

definition PropTrunc_is_prop (A : U) : is_prop (PropTrunc A) :=
  begin
  apply is_trunc_pi
  end

definition  prop_trunc (A : U) : UPrp :=
 trunctype.mk (PropTrunc A) (PropTrunc_is_prop A)

definition trunc_minus_one (A : U) : UPrp := trunctype.mk (trunc -1 A)(is_prop.mk (is_prop.elim))

definition prop_trunc_is_trunc_minus_one (A : U) 
  :  (prop_trunc A) ≃ (trunc_minus_one A) 
  := equiv_of_is_prop (λ a, a (trunc_minus_one A) tr) (trunc.rec (λ a X f, f a))

definition eq_of_props (A B : UPrp) : (A = B :> Type₀) -> A = B :=
  begin
    intro, induction A with A p, induction B with B q, esimp at a, fapply apd011 Prop.mk,
    exact a, fapply is_prop.elimo
  end  

definition prop_trunc_is_trunc_minus_one_in_Prop (A : U) :
           (prop_trunc A) = (trunc_minus_one A) :=
  begin
  apply eq_of_props (prop_trunc A) (trunc_minus_one A), 
  exact prop_trunc_is_trunc_minus_one A
  end

/- Propositional truncation of large types -/

definition  PropTruncL (A : Type) : U := 
  Π(X : UPrp), (A → X) → X

definition PropTruncL_is_prop (A : Type) : is_prop (PropTruncL A) :=
  begin
  apply is_trunc_pi
  end

definition  prop_truncL (A : Type) : UPrp :=
 trunctype.mk (PropTruncL A) (PropTruncL_is_prop A)

definition trunc_minus_oneL (A : Type) : Prop := 
  trunctype.mk (trunc -1 A)(is_prop.mk (is_prop.elim))

definition  propL {A : Type} (a : A) : (PropTruncL A) :=
begin
intro, intro f, exact f a  
end

definition prop_truncL_is_Prop0_resizing (A : Type) (P : UPrp) : 
  ((prop_truncL A) → P) ≃ (A → P) :=
  begin
  fapply equiv.MK, intro f a, exact f (propL a),
  intro f, intro, exact a P f,
  intro, fapply is_prop.elim,
  intro, fapply is_prop.elim
  end

/- Set encodings -/

/- Encoding of a set -/


definition PreSetEncode (A : USet) : U := 
  Π(X : USet), (A → X) → X

definition postcompose (A : USet) { X Y : USet} (f : X → Y) : (A → X) → (A → Y) :=
  λ g : A → X, f ∘ g 

notation f `^` A := postcompose A f 

definition  SetEncode (A : USet) : U := 
  Σ(α : PreSetEncode A), Π(X Y : USet), Π(f : X → Y), α Y ∘ (f^A) ~ f ∘ α X

definition eta (A : USet) (a : A) : SetEncode A :=
  begin
  fapply sigma.mk, 
 { intro, intro f , exact f a },
  intros X Y f,  intro g, esimp
  end

open sigma.ops sigma
definition ispropelim := @is_prop.elimo

/- The "Basic Lemma" -/

definition eta_is_equiv (A : USet) : is_equiv (eta A) :=
  begin
 fapply adjointify, 
 {intro e, exact e.1 A id },
 {intro e, fapply sigma_eq, unfold eta, apply eq_of_homotopy, 
   intro X, apply eq_of_homotopy, intro f,
   note p:= e.2 A X f, symmetry, exact p id, apply ispropelim},
   intro a, reflexivity 
end

/- Product A × B of sets -/

definition  preProduct (A B : USet) : U :=
  Π(X : USet), (A → B → X) → X

definition preProduct_is_set [instance] (A B : USet) : is_set (preProduct A B) :=
  begin
    apply is_trunc_pi
  end

definition product_functor (A B : USet) { X Y : USet} (f : X → Y) : (A → B → X) → (A → B → Y) :=
    λ g : A → B → X, λ a : A, f ∘ (g a)

definition  Product (A B : USet) : U := 
  Σ(α : preProduct A B), Π(X Y : USet), Π(f : X → Y), (α Y) ∘ (product_functor A B f) ~ f ∘ α X

definition SetProduct (A B : USet) : USet :=
  trunctype.mk (Product A B) !is_trunc_sigma

definition Pair {A B : USet} (a : A) (b : B) : Product A B :=
  begin
  fapply sigma.mk, 
  {intro X f, exact f a b},
  {intros X Y f, intro g, esimp}
  end

definition Proj1 {A B : USet} (c : Product A B) : A :=
  begin
  induction c with alpha p,
  exact alpha A (λ x:A, λ y:B, x)
  end

definition Proj2 {A B : USet} (c : Product A B) : B :=
  begin
  induction c with alpha p,
  exact alpha B (λ x:A, λ y:B, y),
  end

definition product_to_times (A B : USet)(u : Product A B) : A × B := 
  begin
fapply pair,
    {exact Proj1 u},
    {exact Proj2 u},
  end

definition times_to_product (A B : USet)(v : A × B) : Product A B :=
  begin
  fapply sigma.mk, 
    {intro X, intro f, exact f (pr1 v) (pr2 v)},
    {intro X Y f, intro g, esimp}
  end

open prod.ops

definition times_is_equiv_product (A B : USet) : is_equiv (times_to_product A B) :=
begin
fapply adjointify,
  {exact  product_to_times A B},
  {intros u, esimp, induction u with f p, fapply sigma_eq, 
    {esimp[product_to_times, times_to_product, Proj1, Proj2],
     fapply eq_of_homotopy2, intros X g, 
     note z := p (A ×t B) X (λ(v : A × B), g v.1 v.2) pair, 
     refine _ ⬝ z⁻¹,
     note zA := p (A ×t B) A pr1 pair,
     note zB := p (A ×t B) B pr2 pair,
     esimp at *,
     rewrite [-zA, -zB]},
   apply is_prop.elimo},
  {intro a, induction a with a b, esimp[product_to_times, times_to_product]}
end

open sigma.ops

-- the eta-rule for the encoded Product.

definition Product_eta (A B : USet) (f : Product A B) : f.1 (SetProduct A B) Pair = f :=
begin 
  apply subtype_eq, apply eq_of_homotopy2, intro X h, 
   note z := f.2 (SetProduct A B) X,
   note z2 := z (λ(g : SetProduct A B), g.1 X h) Pair,
  esimp at z2,
  exact z2⁻¹
end

-- left adjoint UMP of Product w/o assuming times.

definition UP_of_Product_map (A B X : USet) : ((Product A B) → X) → (A → B → X) :=
  begin
  intro h, intro a b, exact h (Pair a b),
  end

definition UP_of_Product (A B : USet) {X : USet} : is_equiv (UP_of_Product_map A B X) :=
  begin
  fapply adjointify,
  {intro f, intro u, exact u.1 X f},
  {intro f, fapply eq_of_homotopy, unfold UP_of_Product_map},
  {intro g, fapply eq_of_homotopy, intro u, intro, induction u with f p, esimp,
      note z := p (SetProduct A B) X g Pair,
    esimp at z, refine z ⬝ _ , exact ap g (Product_eta A B ⟨f, p⟩)}
  end


/- Sum A + B of sets -/

definition  preSum (A B : USet) : U :=
  Π(X : USet), (A → X) × (B → X) → X

definition preSum_is_set [instance] (A B : USet) : is_set (preSum A B) :=
  begin
    apply is_trunc_pi
  end

definition sum_functor (A B : USet) { X Y : USet} (f : X → Y) :  ((A → X) × (B → X)) → ((A → Y) × (B → Y)) :=
  λ g : (A → X) × (B → X) , pair (f ∘ g.1) (f ∘ g.2)  

definition  Sum (A B : USet) : U := 
  Σ(α : preSum A B), Π(X Y : USet), Π(f : X → Y), α Y ∘ (sum_functor A B f) ~ f ∘ α X

definition setSum (A B : USet) : USet :=
  trunctype.mk (Sum A B) !is_trunc_sigma

definition Incl_left (A B : USet) (a : A): Sum A B :=
  begin
   fapply sigma.mk,
  { intro X, intro g, exact g.1 a},
  { intros X Y f, intro g, esimp}   
  end

definition Incl_right (A B : USet) (b : B): Sum A B :=
  begin
   fapply sigma.mk,
  { intro X, intro g, exact g.2 b},
  { intros X Y f, intro g, esimp}   
  end

definition coPair (A B X : USet) (f : A → X) (g : B → X) (c : Sum A B) : X := 
 c.1 X (pair f g)

