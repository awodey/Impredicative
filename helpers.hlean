import imp_prop_trunc

open funext eq trunc is_trunc prod sum pi function is_equiv sigma sigma.ops

notation `↑`       := eq_of_homotopy   -- type \u

variables {A : Type} {B : Type} {C : A → B → Type} 
{a a' : A} (p : a = a') 
{a0 a1 a2 : A} {p2 : a0 = a1} {p0 : a1 = a2} {p1 : a0 = a2} 
(b b' : B)
(f : Π b, C a b)(f' : Π b, C a' b) {X Y Z: Type} {x x' : X} 
(q : x = x') (h : X → Y) (k : Y → Z) (y : Y) 
 {D : A → Type} {u v : Π a, D a}


definition pa (p : u = v) (a : A) : u a = v a := p ▸ rfl

infix ` ▻ `:76 := pa -- type \t4
infix ` ◅ `:76 := ap -- type \t8

definition ap_const : rfl =  (λ x, y) ◅ q := eq.rec rfl q

definition path_lift : b =[p] p▸b := begin induction p, constructor end
definition path_lift' : p⁻¹ ▸ b' =[p] b' := begin induction p, constructor end

definition trans_fun : (p ▸ f) (p ▸ b) = path_lift p b ▸o f b  
  := begin induction p, esimp  end

definition trans_fun' : (p ▸ f)  b' = path_lift' p b' ▸o f (p⁻¹ ▸ b')
  := begin induction p, esimp  end

definition po_of_eq {d d' : D a} (r : d = d') : d =[refl a] d'
  := begin induction r, constructor end

definition pathover_of_homotopy : (Π b, f b =[p] f' b) → f=[p] f'
  := begin 
intro H,induction p, apply po_of_eq, apply eq_of_homotopy, intro b, 
apply @eq_of_pathover_idp _ _ a, apply H,
end

definition nfext0 {A : Type} {B : A → Type} {f g : Π a, B a} (p q : f ~ g)
  : (Π a, p  a = q  a) → p = q 
  := begin intro H, apply eq_of_homotopy, assumption  end
definition nfext {A : Type} {B : A → Type} {f g : Π a, B a} (p q : f = g)
  : (Π a, p ▻ a = q ▻ a) → p = q 
  := begin intro H,  
note z := nfext0 (apd10 p) (apd10 q),
assert K : apd10 p = apd10 q → p = q,intro, 
refine _ ⬝ is_equiv.left_inv apd10 q,
symmetry,
refine _ ⬝ is_equiv.left_inv apd10 p,
symmetry,
exact ap _ a, apply K, clear K, apply z, intro a, apply H
end

definition aux2 {A : Type} {B : A → Type} {f g : Π a, B a} (H : f ~ g) (a : A) 
  : ↑H ▻ a = H a := right_inv apd10 H ▻ a

definition apap {A B : Type} (f : A → B) {x y : A} {p q : x = y} : p = q → f ◅ p = f ◅ q 
  := begin intro, apply ap (ap f), assumption end

infix ` ◅◅ `:76 := apap -- type \t8

-- flipping equalities between compositions
definition frri : p2 = p1 ⬝ p0⁻¹ → p2 ⬝ p0 = p1 
  := begin induction p0, exact id end
definition frli : p0 = p2⁻¹ ⬝ p1 → p2 ⬝ p0 = p1 
  := begin induction p2, intro, refine !idp_con⬝_, exact a⬝!idp_con end
definition flri :  p1 ⬝ p0⁻¹ = p2 → p1 = p2 ⬝ p0 
  := begin induction p0, exact id end
definition flli : p2⁻¹ ⬝ p1 = p0 → p1 = p2 ⬝ p0 
  := begin  induction p2, intro, refine _⬝!idp_con⁻¹, exact !idp_con⁻¹⬝a end
definition flr : p2 ⬝ p0 = p1 → p2 = p1 ⬝ p0⁻¹ 
  := begin induction p0, exact id end
definition fll : p2 ⬝ p0 = p1 → p0 = p2⁻¹ ⬝ p1 
  := begin  induction p2, intro, refine _⬝!idp_con⁻¹, exact !idp_con⁻¹⬝a end
definition frr : p1 = p2 ⬝ p0 → p1 ⬝ p0⁻¹ = p2 
  := begin induction p0, exact id end
definition frl : p1 = p2 ⬝ p0 → p2⁻¹ ⬝ p1 = p0 
  := begin  induction p2, intro, refine !idp_con⬝_, exact a⬝!idp_con end
