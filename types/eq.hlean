/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about path types (identity types)
-/

import types.sigma
open eq sigma sigma.ops equiv is_equiv is_trunc

namespace eq
  /- Path spaces -/
  section
  variables {A B : Type} {a a₁ a₂ a₃ a₄ a' : A} {b b1 b2 : B} {f g : A → B} {h : B → A}
            {p p' p'' : a₁ = a₂}

  /- The path spaces of a path space are not, of course, determined; they are just the
      higher-dimensional structure of the original space. -/

  /- some lemmas about whiskering or other higher paths -/

  definition whisker_left_con_right (p : a₁ = a₂) {q q' q'' : a₂ = a₃} (r : q = q') (s : q' = q'')
    : whisker_left p (r ⬝ s) = whisker_left p r ⬝ whisker_left p s :=
  begin
    induction p, induction r, induction s, reflexivity
  end

  definition whisker_right_con_right (q : a₂ = a₃) (r : p = p') (s : p' = p'')
    : whisker_right q (r ⬝ s) = whisker_right q r ⬝ whisker_right q s :=
  begin
    induction q, induction r, induction s, reflexivity
  end

  definition whisker_left_con_left (p : a₁ = a₂) (p' : a₂ = a₃) {q q' : a₃ = a₄} (r : q = q')
    : whisker_left (p ⬝ p') r = !con.assoc ⬝ whisker_left p (whisker_left p' r) ⬝ !con.assoc' :=
  begin
    induction p', induction p, induction r, induction q, reflexivity
  end

  definition whisker_right_con_left {p p' : a₁ = a₂} (q : a₂ = a₃) (q' : a₃ = a₄) (r : p = p')
    : whisker_right (q ⬝ q') r = !con.assoc' ⬝ whisker_right q' (whisker_right q r) ⬝ !con.assoc :=
  begin
    induction q', induction q, induction r, induction p, reflexivity
  end

  definition whisker_left_inv_left (p : a₂ = a₁) {q q' : a₂ = a₃} (r : q = q')
    : !con_inv_cancel_left⁻¹ ⬝ whisker_left p (whisker_left p⁻¹ r) ⬝ !con_inv_cancel_left = r :=
  begin
    induction p, induction r, induction q, reflexivity
  end

  definition whisker_left_inv (p : a₁ = a₂) {q q' : a₂ = a₃} (r : q = q')
    : whisker_left p r⁻¹ = (whisker_left p r)⁻¹ :=
  by induction r; reflexivity

  definition whisker_right_inv {p p' : a₁ = a₂} (q : a₂ = a₃) (r : p = p')
    : whisker_right q r⁻¹ = (whisker_right q r)⁻¹ :=
  by induction r; reflexivity

  definition ap_eq_apd10 [unfold 5] {B : A → Type} {f g : Πa, B a} (p : f = g) (a : A) :
    ap (λh, h a) p = apd10 p a :=
  by induction p; reflexivity

  definition inverse2_right_inv (r : p = p') : r ◾ inverse2 r ⬝ con.right_inv p' = con.right_inv p :=
  by induction r;induction p;reflexivity

  definition inverse2_left_inv (r : p = p') : inverse2 r ◾ r ⬝ con.left_inv p' = con.left_inv p :=
  by induction r;induction p;reflexivity

  definition ap_con_right_inv (f : A → B) (p : a₁ = a₂)
    : ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p) ⬝ con.right_inv (ap f p)
      = ap (ap f) (con.right_inv p) :=
  by induction p;reflexivity

  definition ap_con_left_inv (f : A → B) (p : a₁ = a₂)
    : ap_con f p⁻¹ p ⬝ whisker_right _ (ap_inv f p) ⬝ con.left_inv (ap f p)
      = ap (ap f) (con.left_inv p) :=
  by induction p;reflexivity

  definition idp_con_whisker_left {q q' : a₂ = a₃} (r : q = q') :
  !idp_con⁻¹ ⬝ whisker_left idp r = r ⬝ !idp_con⁻¹ :=
  by induction r;induction q;reflexivity

  definition whisker_left_idp_con {q q' : a₂ = a₃} (r : q = q') :
  whisker_left idp r ⬝ !idp_con = !idp_con ⬝ r :=
  by induction r;induction q;reflexivity

  definition idp_con_idp {p : a = a} (q : p = idp) : idp_con p ⬝ q = ap (λp, idp ⬝ p) q :=
  by cases q;reflexivity

  definition ap_is_constant [unfold 8] {A B : Type} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) : ap f q = p x ⬝ (p y)⁻¹ :=
  by induction q;exact !con.right_inv⁻¹

  definition inv2_inv {p q : a = a'} (r : p = q) : inverse2 r⁻¹ = (inverse2 r)⁻¹ :=
  by induction r;reflexivity

  definition inv2_con {p p' p'' : a = a'} (r : p = p') (r' : p' = p'')
    : inverse2 (r ⬝ r') = inverse2 r ⬝ inverse2 r' :=
  by induction r';induction r;reflexivity

  definition con2_inv {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : (r₁ ◾ r₂)⁻¹ = r₁⁻¹ ◾ r₂⁻¹ :=
  by induction r₁;induction r₂;reflexivity

  definition eq_con_inv_of_con_eq_whisker_left {A : Type} {a a₂ a₃ : A}
    {p : a = a₂} {q q' : a₂ = a₃} {r : a = a₃} (s' : q = q') (s : p ⬝ q' = r) :
    eq_con_inv_of_con_eq (whisker_left p s' ⬝ s)
      = eq_con_inv_of_con_eq s ⬝ whisker_left r (inverse2 s')⁻¹ :=
  by induction s';induction q;induction s;reflexivity

  definition right_inv_eq_idp {A : Type} {a : A} {p : a = a} (r : p = idpath a) :
    con.right_inv p = r ◾ inverse2 r :=
  by cases r;reflexivity

  /- Transporting in path spaces.

     There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

     - `l` means the left endpoint varies
     - `r` means the right endpoint varies
     - `F` means application of a function to that (varying) endpoint.
  -/

  definition eq_transport_l (p : a₁ = a₂) (q : a₁ = a₃)
    : transport (λx, x = a₃) p q = p⁻¹ ⬝ q :=
  by induction p; exact !idp_con⁻¹

  definition eq_transport_r (p : a₂ = a₃) (q : a₁ = a₂)
    : transport (λx, a₁ = x) p q = q ⬝ p :=
  by induction p; reflexivity

  definition eq_transport_lr (p : a₁ = a₂) (q : a₁ = a₁)
    : transport (λx, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  by induction p; exact !idp_con⁻¹

  definition eq_transport_Fl [unfold 7] (p : a₁ = a₂) (q : f a₁ = b)
    : transport (λx, f x = b) p q = (ap f p)⁻¹ ⬝ q :=
  by induction p; exact !idp_con⁻¹

  definition eq_transport_Fr (p : a₁ = a₂) (q : b = f a₁)
    : transport (λx, b = f x) p q = q ⬝ (ap f p) :=
  by induction p; reflexivity

  definition eq_transport_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁)
    : transport (λx, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  by induction p; exact !idp_con⁻¹

  definition eq_transport_FlFr_D {B : A → Type} {f g : Πa, B a}
    (p : a₁ = a₂) (q : f a₁ = g a₁)
      : transport (λx, f x = g x) p q = (apdt f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apdt g p) :=
  by induction p; exact !ap_id⁻¹ ⬝ !idp_con⁻¹

  definition eq_transport_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁)
    : transport (λx, h (f x) = x) p q = (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  by induction p; exact !idp_con⁻¹

  definition eq_transport_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁))
    : transport (λx, x = h (f x)) p q = p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  by induction p; exact !idp_con⁻¹

  /- Pathovers -/

  -- In the comment we give the fibration of the pathover

  -- we should probably try to do everything just with pathover_eq (defined in cubical.square),

  definition eq_pathover_l (p : a₁ = a₂) (q : a₁ = a₃) : q =[p] p⁻¹ ⬝ q := /-(λx, x = a₃)-/
  by induction p; induction q; exact idpo

  definition eq_pathover_r (p : a₂ = a₃) (q : a₁ = a₂) : q =[p] q ⬝ p := /-(λx, a₁ = x)-/
  by induction p; induction q; exact idpo

  definition eq_pathover_lr (p : a₁ = a₂) (q : a₁ = a₁) : q =[p] p⁻¹ ⬝ q ⬝ p := /-(λx, x = x)-/
  by induction p; rewrite [▸*,idp_con]; exact idpo

  definition eq_pathover_Fl (p : a₁ = a₂) (q : f a₁ = b) : q =[p] (ap f p)⁻¹ ⬝ q := /-(λx, f x = b)-/
  by induction p; induction q; exact idpo

  definition eq_pathover_Fl' (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) ⬝ q =[p] q := /-(λx, f x = b)-/
  by induction p; induction q; exact idpo


  definition eq_pathover_Fr (p : a₁ = a₂) (q : b = f a₁) : q =[p] q ⬝ (ap f p) := /-(λx, b = f x)-/
  by induction p; exact idpo

  definition eq_pathover_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) : q =[p] (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  /-(λx, f x = g x)-/
  by induction p; rewrite [▸*,idp_con]; exact idpo

  definition eq_pathover_FlFr_D {B : A → Type} {f g : Πa, B a} (p : a₁ = a₂) (q : f a₁ = g a₁)
    : q =[p] (apdt f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apdt g p) := /-(λx, f x = g x)-/
  by induction p; rewrite [▸*,idp_con,ap_id];exact idpo

  definition eq_pathover_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) : q =[p] (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  /-(λx, h (f x) = x)-/
  by induction p; rewrite [▸*,idp_con];exact idpo

  definition eq_pathover_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) : q =[p] p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  /-(λx, x = h (f x))-/
  by induction p; rewrite [▸*,idp_con];exact idpo

  definition eq_pathover_r_idp (p : a₁ = a₂) : idp =[p] p := /-(λx, a₁ = x)-/
  by induction p; exact idpo

  definition eq_pathover_l_idp (p : a₁ = a₂) : idp =[p] p⁻¹ := /-(λx, x = a₁)-/
  by induction p; exact idpo

  definition eq_pathover_l_idp' (p : a₁ = a₂) : idp =[p⁻¹] p := /-(λx, x = a₂)-/
  by induction p; exact idpo

  -- The Functorial action of paths is [ap].

  /- Equivalences between path spaces -/

  /- [is_equiv_ap] is in init.equiv  -/

  definition equiv_ap [constructor] (f : A → B) [H : is_equiv f] (a₁ a₂ : A)
    : (a₁ = a₂) ≃ (f a₁ = f a₂) :=
  equiv.mk (ap f) _

  /- Path operations are equivalences -/

  definition is_equiv_eq_inverse [constructor] (a₁ a₂ : A)
    : is_equiv (inverse : a₁ = a₂ → a₂ = a₁) :=
  is_equiv.mk inverse inverse inv_inv inv_inv (λp, eq.rec_on p idp)
  local attribute is_equiv_eq_inverse [instance]

  definition eq_equiv_eq_symm [constructor] (a₁ a₂ : A) : (a₁ = a₂) ≃ (a₂ = a₁) :=
  equiv.mk inverse _

  definition is_equiv_concat_left [constructor] [instance] (p : a₁ = a₂) (a₃ : A)
    : is_equiv (concat p : a₂ = a₃ → a₁ = a₃) :=
  is_equiv.mk (concat p) (concat p⁻¹)
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              abstract (λq, by induction p;induction q;reflexivity) end
  local attribute is_equiv_concat_left [instance]

  definition equiv_eq_closed_left [constructor] (a₃ : A) (p : a₁ = a₂) : (a₁ = a₃) ≃ (a₂ = a₃) :=
  equiv.mk (concat p⁻¹) _

  definition is_equiv_concat_right [constructor] [instance] (p : a₂ = a₃) (a₁ : A)
    : is_equiv (λq : a₁ = a₂, q ⬝ p) :=
  is_equiv.mk (λq, q ⬝ p) (λq, q ⬝ p⁻¹)
              (λq, inv_con_cancel_right q p)
              (λq, con_inv_cancel_right q p)
              (λq, by induction p;induction q;reflexivity)
  local attribute is_equiv_concat_right [instance]

  definition equiv_eq_closed_right [constructor] (a₁ : A) (p : a₂ = a₃) : (a₁ = a₂) ≃ (a₁ = a₃) :=
  equiv.mk (λq, q ⬝ p) _

  definition eq_equiv_eq_closed [constructor] (p : a₁ = a₂) (q : a₃ = a₄) : (a₁ = a₃) ≃ (a₂ = a₄) :=
  equiv.trans (equiv_eq_closed_left a₃ p) (equiv_eq_closed_right a₂ q)

  definition loop_equiv_eq_closed [constructor] {A : Type} {a a' : A} (p : a = a')
    : (a = a) ≃ (a' = a') :=
  eq_equiv_eq_closed p p

  definition is_equiv_whisker_left [constructor] (p : a₁ = a₂) (q r : a₂ = a₃)
  : is_equiv (whisker_left p : q = r → p ⬝ q = p ⬝ r) :=
  begin
  fapply adjointify,
    {intro s, apply (!cancel_left s)},
    {intro s,
      apply concat, {apply whisker_left_con_right},
      apply concat, rotate_left 1, apply (whisker_left_inv_left p s),
      apply concat2,
        {apply concat, {apply whisker_left_con_right},
          apply concat2,
            {induction p, induction q, reflexivity},
            {reflexivity}},
        {induction p, induction r, reflexivity}},
    {intro s, induction s, induction q, induction p, reflexivity}
  end

  definition eq_equiv_con_eq_con_left [constructor] (p : a₁ = a₂) (q r : a₂ = a₃)
    : (q = r) ≃ (p ⬝ q = p ⬝ r) :=
  equiv.mk _ !is_equiv_whisker_left

  definition is_equiv_whisker_right [constructor] {p q : a₁ = a₂} (r : a₂ = a₃)
    : is_equiv (λs, whisker_right r s : p = q → p ⬝ r = q ⬝ r) :=
  begin
  fapply adjointify,
    {intro s, apply (!cancel_right s)},
    {intro s, induction r, cases s, induction q, reflexivity},
    {intro s, induction s, induction r, induction p, reflexivity}
  end

  definition eq_equiv_con_eq_con_right [constructor] (p q : a₁ = a₂) (r : a₂ = a₃)
    : (p = q) ≃ (p ⬝ r = q ⬝ r) :=
  equiv.mk _ !is_equiv_whisker_right

  /-
    The following proofs can be simplified a bit by concatenating previous equivalences.
    However, these proofs have the advantage that the inverse is definitionally equal to
    what we would expect
  -/
  definition is_equiv_con_eq_of_eq_inv_con [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_inv_con : p = r⁻¹ ⬝ q → r ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_inv_con_of_con_eq},
    { intro s, induction r, rewrite [↑[con_eq_of_eq_inv_con,eq_inv_con_of_con_eq],
        con.assoc,con.assoc,con.left_inv,▸*,-con.assoc,con.right_inv,▸* at *,idp_con s]},
    { intro s, induction r, rewrite [↑[con_eq_of_eq_inv_con,eq_inv_con_of_con_eq],
        con.assoc,con.assoc,con.right_inv,▸*,-con.assoc,con.left_inv,▸* at *,idp_con s] },
  end

  definition eq_inv_con_equiv_con_eq [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  equiv.mk _ !is_equiv_con_eq_of_eq_inv_con

  definition is_equiv_con_eq_of_eq_con_inv [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_con_inv : r = q ⬝ p⁻¹ → r ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_con_inv_of_con_eq},
    { intro s, induction p, rewrite [↑[con_eq_of_eq_con_inv,eq_con_inv_of_con_eq]]},
    { intro s, induction p, rewrite [↑[con_eq_of_eq_con_inv,eq_con_inv_of_con_eq]] },
  end

  definition eq_con_inv_equiv_con_eq [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
  equiv.mk _ !is_equiv_con_eq_of_eq_con_inv

  definition is_equiv_inv_con_eq_of_eq_con [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : is_equiv (inv_con_eq_of_eq_con : p = r ⬝ q → r⁻¹ ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_con_of_inv_con_eq},
    { intro s, induction r, rewrite [↑[inv_con_eq_of_eq_con,eq_con_of_inv_con_eq],
        con.assoc,con.assoc,con.left_inv,▸*,-con.assoc,con.right_inv,▸* at *,idp_con s]},
    { intro s, induction r, rewrite [↑[inv_con_eq_of_eq_con,eq_con_of_inv_con_eq],
        con.assoc,con.assoc,con.right_inv,▸*,-con.assoc,con.left_inv,▸* at *,idp_con s] },
  end

  definition eq_con_equiv_inv_con_eq [constructor] (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
  equiv.mk _ !is_equiv_inv_con_eq_of_eq_con

  definition is_equiv_con_inv_eq_of_eq_con [constructor] (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_inv_eq_of_eq_con : r = q ⬝ p → r ⬝ p⁻¹ = q) :=
  begin
    fapply adjointify,
    { apply eq_con_of_con_inv_eq},
    { intro s, induction p, rewrite [↑[con_inv_eq_of_eq_con,eq_con_of_con_inv_eq]]},
    { intro s, induction p, rewrite [↑[con_inv_eq_of_eq_con,eq_con_of_con_inv_eq]] },
  end

  definition eq_con_equiv_con_inv_eq (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
   equiv.mk _ !is_equiv_con_inv_eq_of_eq_con

  local attribute is_equiv_inv_con_eq_of_eq_con
                  is_equiv_con_inv_eq_of_eq_con
                  is_equiv_con_eq_of_eq_con_inv
                  is_equiv_con_eq_of_eq_inv_con [instance]

  definition is_equiv_eq_con_of_inv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_inv_con_eq : r⁻¹ ⬝ q = p → q = r ⬝ p) :=
  is_equiv_inv inv_con_eq_of_eq_con

  definition is_equiv_eq_con_of_con_inv_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_con_inv_eq : q ⬝ p⁻¹ = r → q = r ⬝ p) :=
  is_equiv_inv con_inv_eq_of_eq_con

  definition is_equiv_eq_con_inv_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_inv_of_con_eq : r ⬝ p = q → r = q ⬝ p⁻¹) :=
  is_equiv_inv con_eq_of_eq_con_inv

  definition is_equiv_eq_inv_con_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_inv_con_of_con_eq : r ⬝ p = q → p = r⁻¹ ⬝ q) :=
  is_equiv_inv con_eq_of_eq_inv_con

  definition is_equiv_con_inv_eq_idp [constructor] (p q : a₁ = a₂)
    : is_equiv (con_inv_eq_idp : p = q → p ⬝ q⁻¹ = idp) :=
  begin
    fapply adjointify,
    { apply eq_of_con_inv_eq_idp},
    { intro s, induction q, esimp at *, cases s, reflexivity},
    { intro s, induction s, induction p, reflexivity},
  end

  definition is_equiv_inv_con_eq_idp [constructor] (p q : a₁ = a₂)
    : is_equiv (inv_con_eq_idp : p = q → q⁻¹ ⬝ p = idp) :=
  begin
    fapply adjointify,
    { apply eq_of_inv_con_eq_idp},
    { intro s, induction q, esimp [eq_of_inv_con_eq_idp] at *,
      eapply is_equiv_rect (eq_equiv_con_eq_con_left idp p idp), clear s,
      intro s, cases s, reflexivity},
    { intro s, induction s, induction p, reflexivity},
  end

  definition eq_equiv_con_inv_eq_idp [constructor] (p q : a₁ = a₂) : (p = q) ≃ (p ⬝ q⁻¹ = idp) :=
  equiv.mk _ !is_equiv_con_inv_eq_idp

  definition eq_equiv_inv_con_eq_idp [constructor] (p q : a₁ = a₂) : (p = q) ≃ (q⁻¹ ⬝ p = idp) :=
  equiv.mk _ !is_equiv_inv_con_eq_idp

  /- Pathover Equivalences -/

  definition eq_pathover_equiv_l (p : a₁ = a₂) (q : a₁ = a₃) (r : a₂ = a₃) : q =[p] r ≃ q = p ⬝ r :=
  /-(λx, x = a₃)-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  definition eq_pathover_equiv_r (p : a₂ = a₃) (q : a₁ = a₂) (r : a₁ = a₃) : q =[p] r ≃ q ⬝ p = r :=
  /-(λx, a₁ = x)-/
  by induction p; apply pathover_idp

  definition eq_pathover_equiv_lr (p : a₁ = a₂) (q : a₁ = a₁) (r : a₂ = a₂)
    : q =[p] r ≃ q ⬝ p = p ⬝ r := /-(λx, x = x)-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  definition eq_pathover_equiv_Fl (p : a₁ = a₂) (q : f a₁ = b) (r : f a₂ = b)
    : q =[p] r ≃ q = ap f p ⬝ r := /-(λx, f x = b)-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  definition eq_pathover_equiv_Fr (p : a₁ = a₂) (q : b = f a₁) (r : b = f a₂)
    : q =[p] r ≃ q ⬝ ap f p = r := /-(λx, b = f x)-/
  by induction p; apply pathover_idp

  definition eq_pathover_equiv_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) (r : f a₂ = g a₂)
    : q =[p] r ≃ q ⬝ ap g p = ap f p ⬝ r := /-(λx, f x = g x)-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  definition eq_pathover_equiv_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) (r : h (f a₂) = a₂)
    : q =[p] r ≃ q ⬝ p = ap h (ap f p) ⬝ r :=
  /-(λx, h (f x) = x)-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  definition eq_pathover_equiv_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) (r : a₂ = h (f a₂))
    : q =[p] r ≃ q ⬝ ap h (ap f p) = p ⬝ r :=
  /-(λx, x = h (f x))-/
  by induction p; exact !pathover_idp ⬝e !equiv_eq_closed_right !idp_con⁻¹

  -- a lot of this library still needs to be ported from Coq HoTT

  -- the behavior of equality in other types is described in the corresponding type files

  -- encode decode method

  open is_trunc
  definition encode_decode_method' (a₀ a : A) (code : A → Type) (c₀ : code a₀)
    (decode : Π(a : A) (c : code a), a₀ = a)
    (encode_decode : Π(a : A) (c : code a), c₀ =[decode a c] c)
    (decode_encode : decode a₀ c₀ = idp) : (a₀ = a) ≃ code a :=
  begin
    fapply equiv.MK,
    { intro p, exact p ▸ c₀},
    { apply decode},
    { intro c, apply tr_eq_of_pathover, apply encode_decode},
    { intro p, induction p, apply decode_encode},
  end

  end

  section
    parameters {A : Type} (a₀ : A) (code : A → Type) (H : is_contr (Σa, code a))
      (p : (center (Σa, code a)).1 = a₀)
    include p
    protected definition encode {a : A} (q : a₀ = a) : code a :=
    (p ⬝ q) ▸ (center (Σa, code a)).2

    protected definition decode' {a : A} (c : code a) : a₀ = a :=
    (is_prop.elim ⟨a₀, encode idp⟩ ⟨a, c⟩)..1

    protected definition decode {a : A} (c : code a) : a₀ = a :=
    (decode' (encode idp))⁻¹ ⬝ decode' c

    definition total_space_method (a : A) : (a₀ = a) ≃ code a :=
    begin
      fapply equiv.MK,
      { exact encode},
      { exact decode},
      { intro c,
        unfold [encode, decode, decode'],
        induction p, esimp, rewrite [is_prop_elim_self,▸*,+idp_con],
        apply tr_eq_of_pathover,
        eapply @sigma.rec_on _ _ (λx, x.2 =[(is_prop.elim ⟨x.1, x.2⟩ ⟨a, c⟩)..1] c)
          (center (sigma code)),
        intro a c, apply eq_pr2},
      { intro q, induction q, esimp, apply con.left_inv, },
    end
  end

  definition encode_decode_method {A : Type} (a₀ a : A) (code : A → Type) (c₀ : code a₀)
    (decode : Π(a : A) (c : code a), a₀ = a)
    (encode_decode : Π(a : A) (c : code a), c₀ =[decode a c] c) : (a₀ = a) ≃ code a :=
  begin
    fapply total_space_method,
    { fapply @is_contr.mk,
      { exact ⟨a₀, c₀⟩},
      { intro p, fapply sigma_eq,
          apply decode, exact p.2,
        apply encode_decode}},
    { reflexivity}
  end

end eq
