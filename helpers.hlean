import imp_prop_trunc

open funext eq trunc is_trunc prod sum pi function is_equiv sigma sigma.ops

variables {A : Type} {B : Type} {C : A → B → Type} 
{a a' : A} (p : a = a') (b b' : B)
(f : Π b, C a b)(f' : Π b, C a' b) {X Y Z: Type} {x x' : X} 
(q : x = x') (h : X → Y) (k : Y → Z) (y : Y) 
 {D : A → Type} {u v : Π a, D a}
definition ap_id : q = ap id q := eq.rec rfl q

definition ap_comp : ap k (ap h q) = ap (k ∘ h) q 
 := @eq.rec _ _ (λ y q, ap k (ap h q) = ap (k ∘ h) q) rfl x' q

definition ap_const : rfl = ap (λ x, y) q := eq.rec rfl q

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

definition pa (p : u = v) (a : A) : u a = v a :=
begin
induction p, reflexivity,
end

infix ` ▻ `:76 := pa -- type \t4
infix ` ◅ `:76 := ap -- type \t8

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
