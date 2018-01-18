
open funext eq trunc is_trunc prod sum

attribute trunc.rec [recursor] 

definition my.inv (A : Type)(x y : A)(p : x=y) : y = x :=
eq.rec (eq.refl x) p

-- check ℕ
-- check Π(X : Type.{0}), ℕ

definition  Or (A B : Prop.{0}) : Type.{0} :=
  Π(X : Prop.{0}), (A → X) → ((B → X) → X)

definition Or_is_prop (A B : Prop.{0}) : is_prop (Or A B) :=
  begin
  fapply is_prop.mk, intros, fapply eq_of_homotopy, intro p, fapply eq_of_homotopy, intro g, fapply eq_of_homotopy, intro h, apply is_prop.elim 
  end

definition  or (A B : Prop.{0}) : Prop.{0} :=
 trunctype.mk (Or A B) (Or_is_prop A B)

definition eq_of_iff (p q : Type.{0}) (h : is_prop p) (k : is_prop q) : (p ↔ q) → (p = q) := 
begin
intro a, apply ua, cases a with f g, fapply equiv.MK, exact f, exact g, intro b, apply is_prop.elim,
intro a, apply is_prop.elim
end

definition or_is_disjunciton (A B : Prop.{0}) : (or A B) = trunc -1 (A + B) :=
  begin
  fapply eq_of_iff, exact Or_is_prop A B, apply is_trunc_trunc, fapply iff.intro, 
  {intro p, apply p (trunctype.mk (trunc -1 (A + B)) !is_trunc_trunc ),
   {esimp, intro a, apply tr, exact inl a},
   {esimp, intro b, apply tr, exact inr b}},
  {intro x, induction x with s, cases s with a b, 
    {intro,intro f g, exact f a },
    {intro,intro f g, exact g b }}
  end



