import .imp_prop_trunc 

open funext eq trunc is_trunc prod sum pi function is_equiv

attribute trunc.rec [recursor] 

axiom UA_for_props (A B : Prop) : (A ↔ B) → (A = B :> Type)

definition my.inv (A : Type)(x y : A)(p : x = y) : y = x :=
eq.rec (eq.refl x) p

-- check ℕ
-- check Π(X : Type.{0}), ℕ

/- Encoding of Propostions -/

/- Disjunction of propositions -/

definition  Or (A B : Prop.{0}) : Type.{0} :=
  Π(X : Prop.{0}), (A → X) → ((B → X) → X)

definition Or_is_prop (A B : Prop.{0}) : is_prop (Or A B) :=
  begin
  fapply is_prop.mk, intros, fapply eq_of_homotopy, intro p, fapply eq_of_homotopy, 
  intro g, fapply eq_of_homotopy, intro h, apply is_prop.elim 
  end

definition  or (A B : Prop.{0}) : Prop.{0} :=
 trunctype.mk (Or A B) (Or_is_prop A B)

definition eq_of_iff (p q : Type.{0}) (h : is_prop p) (k : is_prop q) 
           : (p ↔ q) → (p = q) := 
  begin
  intro a, apply ua, cases a with f g, fapply equiv.MK, 
  exact f, exact g, intro b, apply is_prop.elim,
  intro a, apply is_prop.elim
  end

definition or_is_disjunction (A B : Prop.{0}) : (or A B) = trunc -1 (A + B) :=
  begin
  fapply  UA_for_props (or A B) (trunctype.mk (trunc -1 (A + B)) _),  
   fapply iff.intro, 
  {intro p, apply p (trunctype.mk (trunc -1 (A + B)) !is_trunc_trunc),
   {esimp, intro a, apply tr, exact inl a},
   {esimp, intro b, apply tr, exact inr b} },
  {intro x, induction x with s, cases s with a b, 
   {intro,intro f g, exact f a },
   {intro,intro f g, exact g b } }
  end

-- print axioms or_is_disjunction

/- Propositional truncation of small types -/

definition  PropTrunc (A : Type.{0}) : Type.{0} := 
  Π(X : Prop.{0}), (A → X) → X

definition PropTrunc_is_prop (A : Type.{0}) : is_prop (PropTrunc A) :=
  begin
  apply is_trunc_pi
-- fapply is_prop.mk, intros f g, fapply eq_of_homotopy, 
-- intros X, fapply eq_of_homotopy, intros u, apply is_prop.elim,  
  end

definition  prop_trunc (A : Type.{0}) : Prop.{0} :=
 trunctype.mk (PropTrunc A) (PropTrunc_is_prop A)

definition trunc_minus_one (A : Type.{0}) : Prop.{0} := trunctype.mk (trunc -1 A)(is_prop.mk (is_prop.elim))

definition prop_trunc_is_trunc_minus_one (A : Type.{0}) : (prop_trunc A) = (trunc_minus_one A) :> Type₀ :=
  begin
  fapply eq_of_iff, 
  exact PropTrunc_is_prop A, 
  apply is_trunc_trunc, 
  fapply iff.intro,
  intros, exact (a (trunc_minus_one A)) tr,
  intros p, induction p, intro X, intro f, exact f a 
  end

definition is_prop_is_prop (A : Type.{0}) : is_prop (is_prop A) := _

definition eq_of_props (A B : Prop.{0}) : (A = B :> Type₀) -> A = B :=
  begin
    intro, induction A with A p, induction B with B q, esimp at a, fapply apd011 Prop.mk,
    exact a, fapply is_prop.elimo
  end  

definition prop_trunc_is_trunc_minus_one_in_Prop (A : Type.{0}) :
           (prop_trunc A) = (trunc_minus_one A) :=
  begin
  apply eq_of_props (prop_trunc A) (trunc_minus_one A), 
  exact prop_trunc_is_trunc_minus_one A
  end

/- Propositional truncation of large types -/

definition  PropTruncL (A : Type) : Type.{0} := 
  Π(X : Prop.{0}), (A → X) → X

definition PropTruncL_is_prop (A : Type) : is_prop (PropTruncL A) :=
  begin
  apply is_trunc_pi
  end

definition  prop_truncL (A : Type) : Prop.{0} :=
 trunctype.mk (PropTruncL A) (PropTruncL_is_prop A)

definition trunc_minus_oneL (A : Type) : Prop := 
  trunctype.mk (trunc -1 A)(is_prop.mk (is_prop.elim))

definition  propL {A : Type} (a : A) : (PropTruncL A) :=
begin
intro, intro f, exact f a  
end

definition prop_truncL_is_Prop0_resizing (A : Type) (P : Prop.{0}) : 
  ((prop_truncL A) → P) ≃ (A → P) :=
  begin
  fapply equiv.MK, intro f a, exact f (propL a),
  intro f, intro, exact a P f,
  intro, fapply is_prop.elim,
  intro, fapply is_prop.elim
  end

/- Set encodings -/

/- Encoding of a set -/

notation `Set₀`  := Set.{0} 

definition PreSetEncode (A : Set.{0}) : Type.{0} := 
  Π(X : Set.{0}), (A → X) → X

definition postcompose (A : Set.{0}) { X Y : Set.{0}} (f : X → Y) : (A → X) → (A → Y) :=
  λ g : A → X, f ∘ g 

notation f `^` A := postcompose A f 

definition  SetEncode (A : Set.{0}) : Type.{0} := 
  Σ(α : PreSetEncode A), Π(X Y : Set.{0}), Π(f : X → Y), α Y ∘ (f^A) ~ f ∘ α X

definition eta (A : Set₀) (a : A) : SetEncode A :=
  begin
  fapply sigma.mk, 
 { intro, intro f , exact f a },
  intros X Y f,  intro g, esimp
  end

open sigma.ops sigma
definition ispropelim := @is_prop.elimo

/- The "Basic Lemma" -/

definition eta_is_equiv (A : Set.{0}) : is_equiv (eta A) :=
  begin
 fapply adjointify, 
 {intro e, exact e.1 A id },
 {intro e, fapply sigma_eq, unfold eta, apply eq_of_homotopy, 
   intro X, apply eq_of_homotopy, intro f,
   note p:= e.2 A X f, symmetry, exact p id, apply ispropelim},
   intro a, reflexivity 
end

/- Product A × B of sets -/

definition  preProduct (A B : Set₀) : Type.{0} :=
  Π(X : Set₀), (A → B → X) → X

definition preProduct_is_set (A B : Set₀) : is_set (preProduct A B) :=
  begin
    apply is_trunc_pi
  end

definition product_functor (A B : Set₀) { X Y : Set₀} (f : X → Y) : (A → B → X) → (A → B → Y) :=
    λ g : A → B → X, λ a : A, f ∘ (g a)

definition  Product (A B : Set₀) : Type.{0} := 
  Σ(α : preProduct A B), Π(X Y : Set₀), Π(f : X → Y), (α Y) ∘ (product_functor A B f) ~ f ∘ α X

definition Pair {A B : Set₀} (a : A) (b : B) : Product A B :=
  begin
  fapply sigma.mk, 
  {intro X f, exact f a b},
  {intros X Y f, intro g, esimp}
  end

definition product_to_times (A B : Set₀)(u : Product A B) : A × B := 
  begin
fapply pair,
    {begin induction u with f p, exact (f A)(λ x:A, λ y:B, x) end},
    {begin induction u with f p, exact (f B)(λ x:A, λ y:B, y) end}
  end

definition times_to_product (A B : Set₀)(v : A × B) : Product A B :=
  begin
  fapply sigma.mk, 
    {intro X, intro f, exact f (pr1 v) (pr2 v)},
    {intro X Y f, intro g, esimp}
  end

open prod.ops
definition times_is_equiv_product (A B : Set₀) : is_equiv (times_to_product A B) :=
begin
fapply adjointify,
  {exact product_to_times A B},
  {intros u, esimp, induction u with f p, 
  fapply sigma_eq, esimp[product_to_times, times_to_product],
{fapply eq_of_homotopy2, intro X g, note z := p (A ×t B) X (λ(v : A × B), g v.1 v.2) pair, esimp [product_functor] at z, 
  sorry }
-- intro,  fapply eq_of_homotopy, intro g,   fapply eq_of_homotopy, }
  sorry }
end

-- left adjoint UMP of Product, w/o assuming times.

definition UP_of_Product_map (A B X : Set₀) : ((Product A B) → X) → (A → B → X) :=
  begin
  intro h, intro a b, exact h (Pair a b),
  end

definition UP_of_Product (A B : Set₀) {X : Set₀} : is_equiv (UP_of_Product_map A B X)  :=
  begin
  fapply adjointify,
  { intro f, intro u, exact u.1 X f },
  { intro f, fapply eq_of_homotopy, unfold UP_of_Product_map},
  { intro f, fapply eq_of_homotopy, intro u, intro, 
    note g := UP_of_Product_map A B X, unfold UP_of_Product_map,  
    sorry},
  end


/- Coproduct A + B of sets -/

definition  preSum (A B : Set₀) : Type.{0} :=
  Π(X : Set₀), (A × B → X) → X

definition preSum_is_set (A B : Set₀) : is_set (preSum A B) :=
  begin
    apply is_trunc_pi
  end

definition sum_functor (A B : Set₀) { X Y : Set₀} (f : X → Y) : (A × B → X) → (A × B → Y) :=
  λ g : A × B → X, f ∘ g 

definition  Sum (A B : Set₀) : Type.{0} := 
  Σ(α : preSum A B), Π(X Y : Set₀), Π(f : X → Y), α Y ∘ (sum_functor A B f) ~ f ∘ α X





/--

definition  or (A B : Prop.{0}) : Prop.{0} :=
 trunctype.mk (Or A B) (Or_is_prop A B)

definition eq_of_iff (p q : Type.{0}) (h : is_prop p) (k : is_prop q) 
           : (p ↔ q) → (p = q) := 
  begin
  intro a, apply ua, cases a with f g, fapply equiv.MK, 
  exact f, exact g, intro b, apply is_prop.elim,
  intro a, apply is_prop.elim
  end

-- check trunc -1 (A + B)

definition or_is_disjunction (A B : Prop.{0}) : (or A B) = trunc -1 (A + B) :=
  begin
  fapply eq_of_iff, exact Or_is_prop A B, apply is_trunc_trunc, fapply iff.intro, 
  {intro p, apply p (trunctype.mk (trunc -1 (A + B)) !is_trunc_trunc),
   {esimp, intro a, apply tr, exact inl a},
   {esimp, intro b, apply tr, exact inr b} },
  {intro x, induction x with s, cases s with a b, 
   {intro,intro f g, exact f a },
   {intro,intro f g, exact g b } }
  end

--/
