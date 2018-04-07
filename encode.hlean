-- Impredicative encodings of (higher) inductive types
-- formalization by Steve Awodey and Jonas Frey

import imp_prop_trunc .helpers

open funext eq trunc is_trunc prod sum pi function is_equiv sigma sigma.ops

abbreviation U     := Type.{0} 
abbreviation UPrp  := trunctype.{0} -1
abbreviation USet  := trunctype.{0} 0
abbreviation UGpd  := trunctype.{0} 1 
notation `t` x   := trunctype.mk x !is_trunc_pi -- shorthand to truncate Pi's
notation x `=⟨` n `⟩` y := @trunctype.mk n (x = y) !is_trunc_eq
notation `σ` binders `,` r:(scoped P, sigma P) := trunctype.mk r !is_trunc_sigma

-- trucated arrows
definition tto {n : ℕ₋₂} (A : Type) (B : trunctype.{0} n) : trunctype.{0} n
  := tΠ x : A, B
reserve infixr ` ⇒ `:21
infixr ` ⇒ ` := tto

-- truncated equality
definition teq {n : ℕ₋₂} {A : trunctype.{0} (n.+1)} (x y : A) : trunctype.{0} n
  := trunctype.mk (x=y) !is_trunc_eq
reserve infix ` == `:50
infix ` == ` := teq

/- Encoding of Propostions -/

/- Conjunction of propositions -/

definition and (A B : UPrp) : UPrp := tΠ X : UPrp, (A ⇒ B ⇒ X) ⇒ X

-- constructor
definition con  {A B : UPrp} (p : A) (q : B) : and A B := λ X f, f p q

-- projections
definition proj1 {A B : UPrp} (p : and A B) : A := p A (λ x y, x)
definition proj2 {A B : UPrp} (p : and A B) : B := p B (λ x y, y)

-- recursor
definition and_rec {A B C : UPrp} (f : A ⇒ B ⇒ C)  (p : and A B) : C := p C f

-- β rule
definition and_β {A B C : UPrp} (f : A ⇒ B ⇒ C) (a : A) (b : B) 
  : and_rec f (con a b) = f a b := rfl

-- η rule
definition and_η {A B C : UPrp} (f : and A B ⇒ C)
  :  f = and_rec (λ a b, f (con a b)) 
  := eq_of_homotopy (λ x, !is_prop.elim)

-- universal property
definition and_univ_prop {A B C : UPrp} : (and A B ⇒ C) ≃ (A ⇒ B ⇒ C) 
  := equiv_of_is_prop (λ f a b, f (@con A B a b)) and_rec

-- eliminators
-- definition and_prl {A B : UPrp} (p : and A B) : A := p (λ x y, x)
-- definition and_prr {A B : UPrp} (p : and A B) : B := p (λ x y, y)


/- Disjunction of propositions -/

definition or (A B : UPrp) : UPrp := tΠ X : UPrp, (A ⇒ X) ⇒ (B ⇒ X) ⇒ X

-- constructors
definition or_inl {A B : UPrp} (a : A) : or A B := λX f g, f a

definition or_inr {A B : UPrp} (b : B) : or A B := λX f g, g b

-- recursor
definition or_rec {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (v : or A B) : C
  := v C f g

-- β rules
definition or_β_l {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (a : A)
  : or_rec f g (@or_inl A B a) = f a := rfl

definition or_β_r {A B C : UPrp} (f : A ⇒ C) (g : B ⇒ C) (b : B)
  : or_rec f g (@or_inr A B b) = g b := rfl

-- η rule
definition or_η {A B C : UPrp} (h : or A B ⇒ C)
  : h = or_rec (λ a, h (@or_inl A B a)) (λ b, h (@or_inr A B b)) 
  := eq_of_homotopy (λ v, !is_prop.elim)

-- universal property
definition or_univ_prop {A B C : UPrp} 
  :  (or A B ⇒ C) ≃ and (A ⇒ C) (B ⇒ C)
  := equiv_of_is_prop (λ h X k, k (h ∘ or_inl) (h ∘ or_inr))
     (λ p v, v C (p _ (λ x y, x)) (p _ (λ x y, y)))

/- Propositional truncation -/

definition prop_trunc (A : Type) : UPrp := tΠ ⦃X : UPrp⦄, (A ⇒ X) ⇒ X

-- constructors
definition prop_trunc_in {A : U} (a : A) : prop_trunc A := λ X f, f a

definition prop_trunc_eq {A : U} (x y : prop_trunc A) : x = y := !is_prop.elim

-- recursor
definition prop_trunc_rec {A:U} {P:UPrp} (f:A→P) (a : prop_trunc A) : P := a f

-- β rules (as in HoTT book, 199)
definition prop_trunc_β {A : U} {P : UPrp} (f : A → P) (a : A) 
  :  prop_trunc_rec f (prop_trunc_in a) = f a := rfl

definition prop_trunc_β' {A : U} {P : UPrp} (f : A → P) (a b : prop_trunc A)
  :  ap (prop_trunc_rec f) (prop_trunc_eq a b) 
     = is_prop.elim (prop_trunc_rec f a) (prop_trunc_rec f b) := !is_prop.elim

-- η rule
definition prop_trunc_η {A : U} {P : UPrp} (f : prop_trunc A → P)
  :  f = prop_trunc_rec (f ∘ prop_trunc_in) 
  := eq_of_homotopy (λ x, !is_prop.elim)

-- universal property
definition prop_trunc_univ_prop {A : U} {P : UPrp} 
  :  (prop_trunc A ⇒ P) ≃ (A ⇒ P)
  := equiv_of_is_prop (λ f a, f (prop_trunc_in a)) (λ a x, x P a)


/- Set encodings -/

/- Encoding of a set -/

-- System F style encoding
definition preSetEncode (A : USet) : USet := 
  tΠ ⦃X : USet⦄,  (A ⇒ X) ⇒ X

-- naturality condition
definition nSetEncode {A : USet} (α : preSetEncode A) : UPrp 
  :=  tΠ (X Y : USet) (f : X → Y) (h : A → X), α (f ∘ h) == f (α h)

--refined encoding
definition  SetEncode (A : USet) : USet := σ(α : preSetEncode A), nSetEncode α

-- constructor
definition η {A : USet} (a : A) : SetEncode A := ⟨λ X f, f a, λ X Y f h, rfl⟩

/- The "Basic Lemma" -/

definition helper {A : USet} (x : SetEncode A) : is_prop (nSetEncode x.1)
  := begin exact _, end

definition η_is_equiv (A : USet) : is_equiv (@η A) 
  := begin fapply adjointify,
           {λ e, e.1 A id},
           {intro, induction b with b n, fapply sigma_eq, 
           apply eq_of_homotopy2, intro X f, symmetry, apply n, 
           apply is_prop.elimo},
           {λ x, rfl}
     end

/- Product A × B of sets -/

-- System F encoding
definition  preProduct (A B : USet) : USet :=
  tΠ (X : USet), (A ⇒ B ⇒ X) ⇒ X

-- naturality condition
definition nProduct {A B : USet} (α : preProduct A B) : UPrp 
  := tΠ(X Y : USet) (f : X → Y) (h : A ⇒ B ⇒ X), f (α X h) == α Y (λ a, f ∘ h a)

-- refined encoding
definition  Product (A B : USet) : USet := σ(α : preProduct A B), nProduct α
     
-- constructor
definition Pair {A B : USet} (a : A) (b : B) : Product A B 
  := ⟨λ X f, f a b, λ X Y f g, rfl⟩

-- eliminators
definition Proj1 {A B : USet} : Product A B → A 
  := sigma.rec (λ alpha p, alpha A (λ x y, x))

definition Proj2 {A B : USet} : Product A B → B 
  := sigma.rec (λ alpha p, alpha B (λ x y, y))

-- recursor
definition Product_rec {A B C : Set} (f : A ⇒ B ⇒ C) (p : Product A B) : C 
  := p.1 C f

-- β rule
definition Product_β {A B C : USet} (f : A → B → C) (a : A) (b : B) 
  :  Product_rec f (Pair a b) = f a b := rfl

-- weak η rule
definition Product_weak_η {A B : USet} (x : Product A B)
  :  Product_rec Pair x = x
  := begin induction x with p n, fapply sigma_eq, apply eq_of_homotopy2, 
     intros X f, exact (n _ _ (Product_rec f) Pair), apply is_prop.elimo end

-- commuting conversion
definition Product_com_con {A B C D : USet} (f : A → B → C) (g : C → D)
  :  Product_rec (λ a b, g (f a b)) = g ∘ Product_rec f
  := (eq_of_homotopy (λ x, x.2 C D g f))⁻¹

-- strong η rule
definition Product_η {A B C : USet} (g : Product A B → C) 
  :  Product_rec (λ a b, g (Pair a b)) = g
  := (Product_com_con Pair g) ⬝ eq_of_homotopy (λ x, ap g (Product_weak_η x))

-- classical η rule
definition Product_classical_η {A B : USet} (p : Product A B) 
  :   Pair (Proj1 p) (Proj2 p) = p
  :=  ap (λ f, f p) (Product_η _)⁻¹ ⬝ (Product_weak_η p)
        
-- universal property
definition Product_univ_prop {A B C : USet} : is_equiv (@Product_rec A B C)
  := adjointify Product_rec 
                (λ f a b, f (Pair a b))
                Product_η
                (λ g, eq_of_homotopy2 (Product_β g))

/- Sum A + B of sets -/

-- System F encoding
definition  preSum (A B : USet) : USet :=
  tΠ(X : USet), (A ⇒ X) ⇒ (B ⇒ X) ⇒ X

-- naturality condition
definition nSum {A B : USet} (a : preSum A B) : UPrp 
  := tΠ(X Y : USet) (f : X→Y) (h : A→X) (k : B→X), f(a X h k) == a Y (f∘h) (f∘k)

-- refined encoding
definition Sum (A B : USet) : USet := σ(α : preSum A B), nSum α

-- constructors
definition Sum_inl {A B : USet} (a : A) : Sum A B 
  := ⟨λ X f g, f a, λ X Y f h k, rfl⟩

definition Sum_inr {A B : USet} (b : B) : Sum A B 
  := ⟨λ X f g, g b, λ X Y f h k, rfl⟩

-- recursor
definition Sum_rec {A B X : USet} (f : A → X) (g : B → X) (c : Sum A B) : X 
  := c.1 X f g

-- β rules
definition Sum_β_l {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inl = f := rfl

definition Sum_β_r {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inr = g := rfl

-- weak η
definition Sum_weak_η {A B : USet} (x : Sum A B) 
  : Sum_rec Sum_inl Sum_inr x = x
  := begin induction x with α p, fapply sigma_eq, 
     apply eq_of_homotopy3, intro X f g,  unfold Sum_rec, apply p, 
     apply is_prop.elimo end

--commuting conversion 
definition Sum_com_con {A B X Y : USet} (f : A → X) (g : B → X) (h : X → Y) 
  :  Sum_rec (h ∘ f) (h ∘ g) = h ∘ Sum_rec f g
  := begin apply eq_of_homotopy, intro α, induction α with α p, symmetry, apply p end

-- strong η
definition Sum_η {A B X : USet} (h : Sum A B → X) 
  :  Sum_rec (h∘Sum_inl) (h∘Sum_inr) = h
  := !Sum_com_con ⬝ eq_of_homotopy (λ x, ap h (Sum_weak_η x))

--universal property
definition Sum_univ_prop {A B X : USet} 
  :  (Sum A B ⇒ X) ≃ (Product (A ⇒ X) (B ⇒ X))
  := equiv.MK (λ h, Pair (h ∘ Sum_inl) (h ∘ Sum_inr))
              (λ a, Sum_rec (Proj1 a) (Proj2 a))
              Product_classical_η
              Sum_η

/- Natural numbers -/

-- System F encoding
definition preNat : USet := tΠ X : USet, (X ⇒ X) ⇒ X ⇒ X

-- naturality condition
definition nNat (α : preNat) : UPrp 
  := tΠ (X Y : USet) (x : X) (y : Y) (h : X → X) (k : Y → Y) (f : X → Y),
         f x = y ⇒ f ∘ h = k ∘ f ⇒ f (α X h x) == α Y k y

-- refined encoding
definition Nat : USet := σ(α : preNat), nNat α

-- constructors
definition Z : Nat := ⟨λ X f x, x, λ X Y x y h k f u v, u⟩

definition S (n : Nat) : Nat
  := begin fconstructor, λ X h x, h (n.1 X h x), intros X Y x y h k f u v,
     refine (ap (λ f, f (n.1 X h x)) v) ⬝ _, apply ap k, apply n.2, exact u, 
     assumption end

-- recursor
definition Nat_rec {X : USet} (h : X → X) (x : X) (n : Nat) : X := n.1 X h x

-- β rules
definition Nat_β {X : USet} (h : X → X) (x : X) : Nat_rec h x Z = x := rfl
definition Nat_β' {X : USet} (h : X → X) (x : X) (n : Nat) 
  :  Nat_rec h x (S n) = h (Nat_rec h x n) := rfl 

-- η rules
definition Nat_weak_η (n : Nat) : Nat_rec S Z n = n
  := begin 
     induction n with n p, 
     fapply sigma_eq, apply eq_of_homotopy3, intro X h x, 
     apply p Nat X Z x S h (Nat_rec h x), reflexivity, apply eq_of_homotopy,
     intro, reflexivity, apply is_prop.elimo end

definition Nat_η {X:USet} (h:X→X) (x:X) (f:Nat→X) (p : f Z = x) (q:f∘S=h∘ f)
  :  f = Nat_rec h x
  := begin fapply eq_of_homotopy, intro n, refine (ap f (Nat_weak_η n))⁻¹ ⬝ _,
     unfold Nat_rec, induction n with m k, apply k, assumption, assumption end


/- 1-types -/

/- 1 Sphere -/

-- loop space functor
definition Ω (A : Type)            : Type      := Σ a : A, a = a
definition Ω' {A B : Type} (f:A→B) : Ω A → Ω B := sigma.rec (λ a l, ⟨f a, f ◅ l⟩)
definition Ωi {A : Type} (l : Ω A) 
  : Ω' id l = l
  := begin induction l, fapply sigma_eq, reflexivity, apply po_of_eq, apply ap_id end
definition Ωc {A B C : Type} {f : A → B} {g : B → C} (l : Ω A) 
  : Ω'(g ∘ f) l = Ω' g (Ω' f l)
  := begin induction l, fapply sigma_eq, reflexivity, apply po_of_eq, 
     apply ap_compose end

-- first projection out of the loopspace is a natural transformation
definition pi_nat {A B : Type} (f : A → B) (l : Ω A) 
  : (Ω' f l).1 = f l.1
  := begin induction l, reflexivity end

-- pre-encoding, naturality, coherences, S1
definition preS1 : UGpd := tΠ {X : UGpd}, Ω X → X
definition nS1 (α : preS1) : USet 
  := tΠ {X Y : UGpd} (f:X→Y) (l:Ω X), α (Ω' f l) == f (α l)
definition cS1id {α : preS1} (θ : nS1 @α) : UPrp
  := tΠ {X : UGpd} (l : Ω X), θ id l =⟨-1⟩ @α X ◅ Ωi l
definition cS1comp {α : preS1} (θ : nS1 @α) : UPrp
  := tΠ {X Y Z : UGpd} (f : X → Y) (g : Y → Z) (l : Ω X), 
             θ (g ∘ f) l =⟨-1⟩ (α ◅ Ωc l) ⬝ θ g (Ω' f l) ⬝ g ◅ (θ f l)
definition S1 : UGpd := σ(α : preS1)(θ : nS1 @α)(ι : cS1id @θ), (cS1comp @θ)

-- base point
definition preB   : preS1    := λ X l, l.1
definition nB     : nS1 preB := begin intros, induction l, constructor end
definition cidB   : cS1id nB   
  := begin intros, induction l, refine _⬝!sigma_eq_pr1⁻¹, reflexivity end
definition ccompB : cS1comp nB 
  := begin intros, induction l, refine _⬝!sigma_eq_pr1⁻¹, reflexivity end
definition B      : S1       := ⟨@preB, @nB, @cidB, @ccompB⟩

definition aux1 (α β : preS1) (p : α = β) (θ : nS1 α) (ζ : nS1 β)
  (H : Π {X Y : UGpd}(f:X→Y)(l:Ω X), θ f l ⬝ f◅(p▻X▻l) = p▻Y▻(Ω' f l) ⬝ ζ f l)
  :  θ =[p] ζ
  := begin induction p, apply po_of_eq, repeat (apply ↑; intro), refine !H⬝_, 
     exact !idp_con end

-- loop
definition preL : preB =       preB := ↑(λX,↑(λl,l.2))
definition nL   : nB   =[preL] nB 
  := begin fapply aux1, intros, induction l, krewrite idp_con, 
     repeat krewrite aux2 end
definition L    : Ω S1
  := begin fconstructor, exact B, fapply sigma_eq, exact preL, 
     fapply sigma_pathover', exact nL, apply is_prop.elimo end

-- recursor
definition S1_rec {X:UGpd} (l:Ω X) (a:S1) : X := a.1 X l

definition aux {X : UGpd} (l : Ω X) {a b : S1} (p : a = b) 
  : S1_rec l ◅ p = p..1 ▻ X ▻ l := eq.rec rfl p
definition aux3 (α:preS1) (θ: nS1 @α) {X Y : UGpd} (f:X→Y) (l m : Ω X) (p:l=m) 
  : f ◅ (α ◅ p) ⬝ (θ f m)⁻¹ = (θ f l)⁻¹ ⬝ @α Y ◅ (Ω' f ◅ p)
  := begin induction p, refine _⬝ !idp_con, reflexivity end
definition aux4 {Y : UGpd} {h k : S1 → Y} (p : h = k) (α : preS1) (θ : nS1 @α)
  :  θ h L ⬝ p ▻ α L = α ◅ (Ω' ◅ p ▻ L) ⬝ θ k L 
  := begin induction p, refine _⬝!idp_con⁻¹, reflexivity end
definition aux5 {X Y : UGpd} {f g : X → Y} (p : f = g) (x : X) (l : x = x)
  : pr₁ ◅ (Ω' ◅ p ▻ ⟨x,l⟩) = p ▻ x
  := begin induction p, reflexivity end
definition aux7 {X Y : UGpd} {f : X → Y} {l m: Ω X} (p : l = m)
  : pr₁ ◅ (Ω' f ◅ p)  = !pi_nat ⬝ f ◅ (pr1 ◅ p) ⬝ !pi_nat⁻¹
  := begin induction p, exact !con.right_inv⁻¹ end

-- beta rules
definition S1_β_B (X : UGpd) (l : Ω X) : S1_rec l B = l.1 := rfl
definition S1_β_L {X : UGpd} (l : Ω X) : Ω' (S1_rec l) L = l 
  := begin fapply sigma_eq, reflexivity, apply po_of_eq, refine !aux⬝_,
     refine ((λ x, x ▻ X ▻ l) ◅ !sigma_eq_pr1)⬝_,
     refine ((λ x, x ▻ l) ◅ !aux2)⬝_, apply aux2
     end

-- commuting conversion
definition S1_com_con {X Y : UGpd} (f : X → Y) (l : Ω X)
  : S1_rec (Ω' f l) ~ f ∘ S1_rec l  := λ a, a.2.1 X Y f l

-- eta rules
set_option unifier.max_steps 30000
definition S1_weak_η : S1_rec L = id
  := begin apply ↑, intro a, induction a with α n, induction n with θ ξ,
induction ξ with ξ ρ, fapply sigma_eq, 
{ apply ↑, intro X, apply ↑, intro l, refine (θ (S1_rec l) L)⁻¹ ⬝ _,
  apply ap α, apply S1_β_L}, 
  fapply sigma_pathover',
{ apply aux1, intros X Y f l, 
  repeat rewrite aux2, repeat rewrite ap_con, repeat rewrite con.assoc',
  apply flri, refine !con.assoc⬝((ap (λ x,_ ⬝x) !aux3)⬝(!con.assoc'⬝_)), 
  apply frri, apply frr, refine ((λx,_⬝x)◅!ap_inv)⬝_,
  apply frr, refine _⬝(ap (λx,_⬝x)(frl(ρ(S1_rec l)f L⬝!con.assoc)))⬝!con.assoc',
  refine (aux2 (S1_com_con f l) (α L))⁻¹⬝_⬝!con.assoc'⬝!con.assoc',
  apply fll, refine aux4 (↑(S1_com_con f l)) @α @θ ⬝(_⬝!con.assoc⬝!con.assoc),
  apply ap (λ x, x⬝  θ (f ∘ S1_rec l) L), apply flr, apply flr,
  repeat rewrite -ap_con, apply ap (λx, α ◅ x),
  apply sigma_eq2, apply is_prop.elimo, induction l with x l,
  refine !ap_con⬝_, rewrite ap_con, krewrite aux5, rewrite aux2,
  rewrite con.assoc, refine !idp_con⬝(concat◅!sigma_eq_pr1 ▻_⬝(!idp_con⬝_)), 
  krewrite aux7, unfold pi_nat, refine !idp_con⬝_, refine f◅◅!sigma_eq_pr1 ⬝ _, 
  krewrite sigma_eq_pr1},
apply is_prop.elimo,
end
definition S1_η {X : UGpd} (f : S1 → X) : S1_rec (Ω' f L) = f
  := ↑(S1_com_con f L) ⬝ compose f ◅ S1_weak_η

-- universal property : S1 represents the unbased loopspace functor on UGpd
definition S1_univ_prop {X : UGpd} : (S1 → X) ≃ Ω X
  := equiv.MK (λ f, Ω' f L) S1_rec S1_β_L S1_η
