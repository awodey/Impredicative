import imp_prop_trunc 

open funext eq trunc is_trunc prod sum pi function is_equiv sigma sigma.ops


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
definition tto {n : ℕ₋₂} (A : Type) (B : trunctype.{0} n) : trunctype.{0} n
  := π x : A, B
reserve infixr ` ⇒ `:21
infixr ` ⇒ ` := tto
-- definition tsig {n : ℕ₋₂} {A : USet} (B : A → U) [H : Π a, is_prop (B a)] : USet
--   := trunctype.mk (sigma B) !is_trunc_sigma
-- notation `σ` binders `,` r:(scoped P, tsig P) := r

/- Encoding of Propostions -/

/- conjunction of propositions -/

definition and (A B : UPrp) : UPrp := π X:UPrp, (A ⇒ B ⇒ X) ⇒ X
-- constructor
definition con {A B : UPrp} (p : A) (q : B) : and A B := λ X f, f p q
-- recursor
definition and_rec {A B C : UPrp} (f : A ⇒ B ⇒ C)  (p : and A B) : C := p C f
-- beta rule
definition and_beta {A B C : UPrp} (f : A ⇒ B ⇒ C) (a : A) (b : B) 
  : and_rec f (con a b) = f a b := rfl
-- eta rule
definition and_eta {A B C : UPrp} (f : and A B ⇒ C)
  :  f = and_rec (λ a b, f (con a b)) 
  := eq_of_homotopy (λ x, !is_prop.elim)
-- universal property
definition and_univ_prop {A B C : UPrp} : (and A B ⇒ C) ≃ (A ⇒ B ⇒ C) 
  := equiv_of_is_prop (λ f a b, f (@con A B a b)) and_rec
-- eliminators
-- definition and_prl {A B : UPrp} (p : and A B) : A := p (λ x y, x)
-- definition and_prr {A B : UPrp} (p : and A B) : B := p (λ x y, y)


/- Disjunction of propositions -/

definition or (A B : UPrp) : UPrp := π X : UPrp, (A ⇒ X) ⇒ (B ⇒ X) ⇒ X
-- constructors
definition or_inl {A B : UPrp} (a : A) : or A B := λX f g, f a
definition or_inr {A B : UPrp} (b : B) : or A B := λX f g, g b
-- recursor
definition or_rec {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (v : or A B) : C
  := v C f g
-- beta rules
definition or_beta_l {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (a : A)
  : or_rec f g (@or_inl A B a) = f a := rfl
definition or_beta_r {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (b : B)
  : or_rec f g (@or_inr A B b) = g b := rfl
-- eta rule
definition or_eta {A B C : UPrp} (h : or A B ⇒ C)
  : h = or_rec (λ a, h (@or_inl A B a)) (λ b, h (@or_inr A B b)) 
  := eq_of_homotopy (λ v, !is_prop.elim)
-- universal property
definition or_univ_prop {A B C : UPrp} 
  :  (or A B ⇒ C) ≃ and (A ⇒ C) (B ⇒ C)
  := equiv_of_is_prop (λ h X k, k (h ∘ or_inl) (h ∘ or_inr))
     (λ p v, v C (p _ (λ x y, x)) (p _ (λ x y, y)))

/- Propositional truncation -/

definition prop_trunc (A : Type) : UPrp := π X : UPrp, (A ⇒ X) ⇒ X
-- constructors
definition prop_trunc_in {A : U} (a : A) : prop_trunc A := λ X f, f a
definition prop_trunc_eq {A : U} (x y : prop_trunc A) : x=y := is_prop.elim x y
-- recursor
definition prop_trunc_rec {A : U} {P : UPrp} (f : A → P) (a : prop_trunc A) : P
  := a _ f
-- beta rules (as in HoTT book, 199)
definition prop_trunc_beta {A : U} {P : UPrp} (f : A → P) (a : A) 
  :  prop_trunc_rec f (prop_trunc_in a) = f a := rfl
definition prop_trunc_beta' {A : U} {P : UPrp} (f : A → P) (a b : prop_trunc A)
  :  ap (prop_trunc_rec f) (prop_trunc_eq a b) 
     = is_prop.elim (prop_trunc_rec f a) (prop_trunc_rec f b) := !is_prop.elim
-- eta rule
definition prop_trunc_eta {A : U} {P : UPrp} (f : prop_trunc A → P)
  :  f = prop_trunc_rec (f ∘ prop_trunc_in) 
  := eq_of_homotopy (λ x, !is_prop.elim)
-- universal property
definition prop_trunc_univ_prop {A : U} {P : UPrp} 
  :  (prop_trunc A ⇒ P) ≃ (A ⇒ P)
  := equiv_of_is_prop (λ f a, f (prop_trunc_in a)) (λ a x, x P a)


/- Set encodings -/

/- Encoding of a set -/

definition PreSetEncode (A : USet) : U := 
  Π(X : USet), (A → X) → X

definition postcompose (A : USet) {X Y : USet} (f : X → Y) 
  :  (A → X) → (A → Y) := λ g : A → X, f ∘ g 

notation f `^` A := postcompose A f 

definition  SetEncode (A : USet) : U 
  := Σ(α : PreSetEncode A), Π(X Y : USet), Π(f : X → Y), α Y ∘ (f^A) ~ f ∘ α X

definition eta (A : USet) (a : A) : SetEncode A 
  := ⟨λ X f, f a, λ X Y f g, refl ((f ^ A) g a)⟩

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

definition  preProduct (A B : USet) : USet :=
  π (X : USet), (A ⇒ B ⇒ X) ⇒ X
definition product_functor (A B : USet) {X Y : USet} (f : X → Y) 
  :  (A → B → X) → (A → B → Y) 
  := λ g : A → B → X, λ a : A, f ∘ (g a)
definition  Product (A B : USet) : USet 
  := trunctype.mk 
       (Σ(α : preProduct A B), Π{X Y : USet} (f : X → Y), 
         (α Y) ∘ (product_functor A B f) ~ f ∘ α X)
       !is_trunc_sigma
-- constructor
definition Pair {A B : USet} (a : A) (b : B) : Product A B 
  := ⟨λ X f, f a b, λ X Y f g, refl (product_functor A B f g a b)⟩
-- eliminators
definition Proj1 {A B : USet} : Product A B → A 
  := sigma.rec (λ alpha p, alpha A (λ x y, x))
definition Proj2 {A B : USet} : Product A B → B 
  := sigma.rec (λ alpha p, alpha B (λ x y, y))
-- recursor
definition Product_rec {A B C : Set} (f : A ⇒ B ⇒ C) (p : Product A B) : C 
  := p.1 C f
-- beta rule
definition Product_beta {A B C : USet} (f : A → B → C) (a : A) (b : B) 
  :  Product_rec f (Pair a b) = f a b := rfl
-- weak eta rule
definition Product_weak_eta {A B : USet} (x : Product A B)
  :  x = Product_rec Pair x
  := begin induction x with p n, refine _ ⬝ (n id Pair)⁻¹, fapply sigma_eq, 
     apply eq_of_homotopy2, intros X f, exact (n (Product_rec f) Pair), 
     apply is_prop.elimo end
-- commuting conversion
definition Product_com_con {A B C D : USet} (f : A → B → C) (g : C → D)
  :  g ∘ Product_rec f = Product_rec (λ a b, g (f a b))
  := begin apply eq_of_homotopy, intro x, induction x with x n, symmetry, 
  apply n end
-- eta rule
definition Product_eta {A B C : USet} (g : Product A B → C) 
  :  g = Product_rec (λ a b, g (Pair a b))
  := eq_of_homotopy (λ x, ap g (Product_weak_eta x)) ⬝ Product_com_con Pair g
-- universal property
definition Product_univ_prop {A B C : USet} : is_equiv (@Product_rec A B C)
  := begin
fconstructor,intro f a b, apply f, exact Pair a b, intro f, symmetry, 
apply Product_eta, intro g, apply eq_of_homotopy2, intro a b, 
apply Product_beta, intro f, apply is_prop.elim,
end
-- -- induction principle
-- definition product_ind {A B : USet} {P : Product A B → U} [K : Π x, is_prop (P x)]
-- (H : Π (a : A) (b : B), P (Pair a b)) (x : Product A B) : P x 
--   := begin
-- exact sorry 
-- end

/- Sum A + B of sets -/

-- System F encoding
definition  preSum (A B : USet) : USet :=
  π(X : USet), (A ⇒ X) ⇒ (B ⇒ X) ⇒ X
-- naturality condition
definition nSum {A B : USet} (a : preSum A B) : UPrp 
  := π (X Y : USet) (f : X → Y) (h : A → X) (k : B → X), 
     Prop.mk (f(a X h k) = a Y (f∘h) (f∘k)) !is_trunc_eq
-- refined System F encoding
definition Sum (A B : USet) : USet 
  := Set.mk (sigma (@nSum A B)) !is_trunc_sigma
-- constructors
definition Sum_inl {A B : USet} (a : A) : Sum A B 
  := ⟨λ X f g, f a, λ X Y f h k, rfl⟩
definition Sum_inr {A B : USet} (b : B) : Sum A B 
  := ⟨λ X f g, g b, λ X Y f h k, rfl⟩
-- recursor
definition Sum_rec {A B X : USet} (f : A → X) (g : B → X) (c : Sum A B) : X 
  := c.1 X f g
-- beta rules
definition Sum_beta_l {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inl = f := rfl
definition Sum_beta_r {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inr = g := rfl
-- weak eta
definition Sum_weak_eta {A B : USet} (x : Sum A B) 
  : Sum_rec Sum_inl Sum_inr x = x
  := begin induction x with α p, fapply sigma_eq, 
     apply eq_of_homotopy3, intro X f g,  unfold Sum_rec, apply p, 
     apply is_prop.elimo end
-- commuting conversion 
definition Sum_com_con {A B X Y : USet} (f : A → X) (g : B → X) (h : X → Y) 
  :  h ∘ Sum_rec f g = Sum_rec (h ∘ f) (h ∘ g)
  := begin apply eq_of_homotopy, intro α, induction α with α p, apply p end
-- strong eta
definition Sum_eta {A B X : USet} (h : Sum A B → X) 
  :  h = Sum_rec (h∘Sum_inl) (h∘Sum_inr)
  := eq_of_homotopy (λ x, ap h (Sum_weak_eta x)⁻¹) ⬝ Sum_com_con _ _ _
--universal property
definition Sum_univ_prop {A B X : USet} 
  :  (Sum A B ⇒ X) ≃ (Product (A ⇒ X) (B ⇒ X))
  := begin
fapply equiv.MK,

intro h, apply Pair,
exact h ∘ Sum_inl, exact h ∘ Sum_inr, 
intro, 
apply Sum_rec, 
exact Proj1 a, exact Proj2 a,
intro p, esimp,

refine product_ind _ p,
intros, clear p, reflexivity,
intro, apply eq_of_homotopy, intro,
end

/- Natural numbers -/

-- System F encoding
definition preNat : USet := π X : USet, (X ⇒ X) ⇒ X ⇒ X

-- naturality condition
definition nNat (α : preNat) : UPrp 
  := π(X Y : USet) (x : X) (y : Y) (h : X → X) (k : Y → Y) (f : X → Y),
         f x = y ⇒ f ∘ h = k ∘ f ⇒ Prop.mk (f (α X h x) = α Y k y) !is_trunc_eq

-- refined encoding
definition Nat : USet := Set.mk (Σ α : preNat, nNat α) !is_trunc_sigma

-- constructors
definition Z : Nat := ⟨λ X f x, x, λ X Y x y h k f u v, u⟩

definition S (n : Nat) : Nat
  := begin
 induction n with n p, fconstructor, λ X h x, h (n X h x),
 intros X Y x y h k f u v,
 refine (ap (λ f, f (n X h x)) v) ⬝ _,
 apply ap k, apply p, exact u, assumption,
 end

-- recursor
definition Nat_rec {X : USet} (h : X → X) (x : X) (n : Nat) : X := n.1 X h x

-- beta rules
definition Nat_beta {X : USet} (h : X → X) (x : X) : Nat_rec h x Z = x := rfl
-- this would be definitional if Lean had definitional eta for Sigma.
definition Nat_beta' {X : USet} (h : X → X) (x : X) (n : Nat) 
  :  Nat_rec h x (S n) = h (Nat_rec h x n) 
  := begin induction n, reflexivity end

