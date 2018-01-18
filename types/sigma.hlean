/-
Copyright (c) 2014-15 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about sigma-types (dependent sums)
-/

import types.prod

open eq sigma sigma.ops equiv is_equiv function is_trunc sum unit

namespace sigma
  variables {A A' : Type} {B : A → Type} {B' : A' → Type} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

  definition destruct := @sigma.cases_on

  /- Paths in a sigma-type -/

  protected definition eta [unfold 3] : Π (u : Σa, B a), ⟨u.1 , u.2⟩ = u
  | eta ⟨u₁, u₂⟩ := idp

  definition eta2 : Π (u : Σa b, C a b), ⟨u.1, u.2.1, u.2.2⟩ = u
  | eta2 ⟨u₁, u₂, u₃⟩ := idp

  definition eta3 : Π (u : Σa b c, D a b c), ⟨u.1, u.2.1, u.2.2.1, u.2.2.2⟩ = u
  | eta3 ⟨u₁, u₂, u₃, u₄⟩ := idp

  definition dpair_eq_dpair [unfold 8] (p : a = a') (q : b =[p] b') : ⟨a, b⟩ = ⟨a', b'⟩ :=
  apd011 sigma.mk p q

  definition sigma_eq [unfold 5 6] (p : u.1 = v.1) (q : u.2 =[p] v.2) : u = v :=
  by induction u; induction v; exact (dpair_eq_dpair p q)

  definition sigma_eq_right [unfold 6] (q : b₁ = b₂) : ⟨a, b₁⟩ = ⟨a, b₂⟩ :=
  ap (dpair a) q

  definition eq_pr1 [unfold 5] (p : u = v) : u.1 = v.1 :=
  ap pr1 p

  postfix `..1`:(max+1) := eq_pr1

  definition eq_pr2 [unfold 5] (p : u = v) : u.2 =[p..1] v.2 :=
  by induction p; exact idpo

  postfix `..2`:(max+1) := eq_pr2

  definition dpair_sigma_eq (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : ⟨(sigma_eq p q)..1, (sigma_eq p q)..2⟩ = ⟨p, q⟩ :=
  by induction u; induction v;esimp at *;induction q;esimp

  definition sigma_eq_pr1 (p : u.1 = v.1) (q : u.2 =[p] v.2) : (sigma_eq p q)..1 = p :=
  (dpair_sigma_eq p q)..1

  definition sigma_eq_pr2 (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : (sigma_eq p q)..2 =[sigma_eq_pr1 p q] q :=
  (dpair_sigma_eq p q)..2

  definition sigma_eq_eta (p : u = v) : sigma_eq (p..1) (p..2) = p :=
  by induction p; induction u; reflexivity

  definition eq2_pr1 {p q : u = v} (r : p = q) : p..1 = q..1 :=
  ap eq_pr1 r

  definition eq2_pr2 {p q : u = v} (r : p = q) : p..2 =[eq2_pr1 r] q..2 :=
  !pathover_ap (apd eq_pr2 r)

  definition tr_pr1_sigma_eq {B' : A → Type} (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : transport (λx, B' x.1) (sigma_eq p q) = transport B' p :=
  by induction u; induction v; esimp at *;induction q; reflexivity

  protected definition ap_pr1 (p : u = v) : ap (λx : sigma B, x.1) p = p..1 := idp

  /- the uncurried version of sigma_eq. We will prove that this is an equivalence -/

  definition sigma_eq_unc [unfold 5] : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2), u = v
  | sigma_eq_unc ⟨pq₁, pq₂⟩ := sigma_eq pq₁ pq₂

  definition dpair_sigma_eq_unc : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2),
    ⟨(sigma_eq_unc pq)..1, (sigma_eq_unc pq)..2⟩ = pq
  | dpair_sigma_eq_unc ⟨pq₁, pq₂⟩ := dpair_sigma_eq pq₁ pq₂

  definition sigma_eq_pr1_unc (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
    : (sigma_eq_unc pq)..1 = pq.1 :=
  (dpair_sigma_eq_unc pq)..1

  definition sigma_eq_pr2_unc (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2) :
    (sigma_eq_unc pq)..2 =[sigma_eq_pr1_unc pq] pq.2 :=
  (dpair_sigma_eq_unc pq)..2

  definition sigma_eq_eta_unc (p : u = v) : sigma_eq_unc ⟨p..1, p..2⟩ = p :=
  sigma_eq_eta p

  definition tr_sigma_eq_pr1_unc {B' : A → Type}
    (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
      : transport (λx, B' x.1) (@sigma_eq_unc A B u v pq) = transport B' pq.1 :=
  destruct pq tr_pr1_sigma_eq

  definition is_equiv_sigma_eq [instance] [constructor] (u v : Σa, B a)
      : is_equiv (@sigma_eq_unc A B u v) :=
  adjointify sigma_eq_unc
             (λp, ⟨p..1, p..2⟩)
             sigma_eq_eta_unc
             dpair_sigma_eq_unc

  definition sigma_eq_equiv [constructor] (u v : Σa, B a)
    : (u = v) ≃ (Σ(p : u.1 = v.1),  u.2 =[p] v.2) :=
  (equiv.mk sigma_eq_unc _)⁻¹ᵉ

  definition dpair_eq_dpair_con (p1 : a  = a' ) (q1 : b  =[p1] b' )
                                (p2 : a' = a'') (q2 : b' =[p2] b'') :
    dpair_eq_dpair (p1 ⬝ p2) (q1 ⬝o q2) = dpair_eq_dpair p1 q1 ⬝ dpair_eq_dpair  p2 q2 :=
  by induction q1; induction q2; reflexivity

  definition sigma_eq_con (p1 : u.1 = v.1) (q1 : u.2 =[p1] v.2)
                          (p2 : v.1 = w.1) (q2 : v.2 =[p2] w.2) :
    sigma_eq (p1 ⬝ p2) (q1 ⬝o q2) = sigma_eq p1 q1 ⬝ sigma_eq p2 q2 :=
  by induction u; induction v; induction w; apply dpair_eq_dpair_con

  local attribute dpair_eq_dpair [reducible]
  definition dpair_eq_dpair_con_idp (p : a = a') (q : b =[p] b') :
    dpair_eq_dpair p q = dpair_eq_dpair p !pathover_tr ⬝
    dpair_eq_dpair idp (pathover_idp_of_eq (tr_eq_of_pathover q)) :=
  by induction q; reflexivity

  /- eq_pr1 commutes with the groupoid structure. -/

  definition eq_pr1_idp (u : Σa, B a)           : (refl u) ..1 = refl (u.1)      := idp
  definition eq_pr1_con (p : u = v) (q : v = w) : (p ⬝ q)  ..1 = (p..1) ⬝ (q..1) := !ap_con
  definition eq_pr1_inv (p : u = v)             : p⁻¹      ..1 = (p..1)⁻¹        := !ap_inv

  /- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/

  definition ap_dpair (q : b₁ = b₂) :
    ap (sigma.mk a) q = dpair_eq_dpair idp (pathover_idp_of_eq q) :=
  by induction q; reflexivity

  /- Dependent transport is the same as transport along a sigma_eq. -/

  definition transportD_eq_transport (p : a = a') (c : C a b) :
      p ▸D c = transport (λu, C (u.1) (u.2)) (dpair_eq_dpair p !pathover_tr) c :=
  by induction p; reflexivity

  definition sigma_eq_eq_sigma_eq {p1 q1 : a = a'} {p2 : b =[p1] b'} {q2 : b =[q1] b'}
      (r : p1 = q1) (s : p2 =[r] q2) : sigma_eq p1 p2 = sigma_eq q1 q2 :=
  by induction s; reflexivity

  /- A path between paths in a total space is commonly shown component wise. -/
  definition sigma_eq2 {p q : u = v} (r : p..1 = q..1) (s : p..2 =[r] q..2)
    : p = q :=
  begin
    induction p, induction u with u1 u2,
    transitivity sigma_eq q..1 q..2,
      apply sigma_eq_eq_sigma_eq r s,
      apply sigma_eq_eta,
  end

  definition sigma_eq2_unc {p q : u = v} (rs : Σ(r : p..1 = q..1), p..2 =[r] q..2) : p = q :=
  destruct rs sigma_eq2

  definition ap_dpair_eq_dpair (f : Πa, B a → A') (p : a = a') (q : b =[p] b')
    : ap (sigma.rec f) (dpair_eq_dpair p q) = apd011 f p q :=
  by induction q; reflexivity

  /- Transport -/

  /- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why `transport` alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

  definition sigma_transport (p : a = a') (bc : Σ(b : B a), C a b)
    : p ▸ bc = ⟨p ▸ bc.1, p ▸D bc.2⟩ :=
  by induction p; induction bc; reflexivity

  /- The special case when the second variable doesn't depend on the first is simpler. -/
  definition sigma_transport_nondep {B : Type} {C : A → B → Type} (p : a = a')
    (bc : Σ(b : B), C a b) : p ▸ bc = ⟨bc.1, p ▸ bc.2⟩ :=
  by induction p; induction bc; reflexivity

  /- Or if the second variable contains a first component that doesn't depend on the first. -/

  definition sigma_transport2_nondep {C : A → Type} {D : Π a:A, B a → C a → Type} (p : a = a')
      (bcd : Σ(b : B a) (c : C a), D a b c) : p ▸ bcd = ⟨p ▸ bcd.1, p ▸ bcd.2.1, p ▸D2 bcd.2.2⟩ :=
  begin
    induction p, induction bcd with b cd, induction cd, reflexivity
  end

  /- Pathovers -/

  definition etao (p : a = a') (bc : Σ(b : B a), C a b)
    : bc =[p] ⟨p ▸ bc.1, p ▸D bc.2⟩ :=
  by induction p; induction bc; apply idpo

  -- TODO: interchange sigma_pathover and sigma_pathover'
  definition sigma_pathover (p : a = a') (u : Σ(b : B a), C a b) (v : Σ(b : B a'), C a' b)
    (r : u.1 =[p] v.1) (s : u.2 =[apd011 C p r] v.2) : u =[p] v :=
  begin
    induction u, induction v, esimp at *, induction r,
    esimp [apd011] at s, induction s using idp_rec_on, apply idpo
  end

  definition sigma_pathover' (p : a = a') (u : Σ(b : B a), C a b) (v : Σ(b : B a'), C a' b)
    (r : u.1 =[p] v.1) (s : pathover (λx, C x.1 x.2) u.2 (sigma_eq p r) v.2) : u =[p] v :=
  begin
    induction u, induction v, esimp at *, induction r,
    induction s using idp_rec_on, apply idpo
  end

  definition sigma_pathover_nondep {B : Type} {C : A → B → Type} (p : a = a')
    (u : Σ(b : B), C a b) (v : Σ(b : B), C a' b)
    (r : u.1 = v.1) (s : pathover (λx, C (prod.pr1 x) (prod.pr2 x)) u.2 (prod.prod_eq p r) v.2) : u =[p] v :=
  begin
    induction p, induction u, induction v, esimp at *, induction r,
    induction s using idp_rec_on, apply idpo
  end

  definition pathover_pr1 [unfold 9] {A : Type} {B : A → Type} {C : Πa, B a → Type}
    {a a' : A} {p : a = a'} {x : Σb, C a b} {x' : Σb', C a' b'}
    (q : x =[p] x') : x.1 =[p] x'.1 :=
  begin induction q, constructor end

/- 
 definition sigma_pathover_equiv_of_is_prop {A : Type} {B : A → Type} (C : Πa, B a → Type)
    {a a' : A} (p : a = a') (x : Σb, C a b) (x' : Σb', C a' b')
    [Πa b, is_prop (C a b)] : x =[p] x' ≃ x.1 =[p] x'.1 :=
  begin
    fapply equiv.MK,
    { exact pathover_pr1 },
    { intro q, induction x with b c, induction x' with b' c', esimp at q, induction q,
      apply pathover_idp_of_eq, exact sigma_eq idp !is_prop.elimo },
    { intro q, induction x with b c, induction x' with b' c', esimp at q, induction q,
      have c = c', from !is_prop.elim, induction this,
      rewrite [▸*, is_prop_elimo_self (C a) c] },
    { intro q, induction q, induction x with b c, rewrite [▸*, is_prop_elimo_self (C a) c] }
  end
-/

  /-
    TODO:
    * define the projections from the type u =[p] v
    * show that the uncurried version of sigma_pathover is an equivalence
  -/
  /- Squares in a sigma type are characterized in cubical.squareover (to avoid circular imports) -/

  /- Functorial action -/
  variables (f : A → A') (g : Πa, B a → B' (f a))

  definition sigma_functor [unfold 7] (u : Σa, B a) : Σa', B' a' :=
  ⟨f u.1, g u.1 u.2⟩

  definition total [reducible] [unfold 5] {B' : A → Type} (g : Πa, B a → B' a) : (Σa, B a) → (Σa, B' a) :=
  sigma_functor id g

  /- Equivalences -/
  definition is_equiv_sigma_functor [constructor] [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
      : is_equiv (sigma_functor f g) :=
  adjointify (sigma_functor f g)
             (sigma_functor f⁻¹ (λ(a' : A') (b' : B' a'),
               ((g (f⁻¹ a'))⁻¹ (transport B' (right_inv f a')⁻¹ b'))))
  abstract begin
    intro u', induction u' with a' b',
    apply sigma_eq (right_inv f a'),
    rewrite [▸*,right_inv (g (f⁻¹ a')),▸*],
    apply tr_pathover
  end end
  abstract begin
    intro u,
    induction u with a b,
    apply (sigma_eq (left_inv f a)),
    apply pathover_of_tr_eq,
    rewrite [▸*,adj f,-(fn_tr_eq_tr_fn (left_inv f a) (λ a, (g a)⁻¹)),
             ▸*,tr_compose B' f,tr_inv_tr,left_inv]
  end end

  definition sigma_equiv_sigma_of_is_equiv [constructor]
    [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)] : (Σa, B a) ≃ (Σa', B' a') :=
  equiv.mk (sigma_functor f g) !is_equiv_sigma_functor

  definition sigma_equiv_sigma [constructor] (Hf : A ≃ A') (Hg : Π a, B a ≃ B' (to_fun Hf a)) :
      (Σa, B a) ≃ (Σa', B' a') :=
  sigma_equiv_sigma_of_is_equiv (to_fun Hf) (λ a, to_fun (Hg a))

  definition sigma_equiv_sigma_right [constructor] {B' : A → Type} (Hg : Π a, B a ≃ B' a)
    : (Σa, B a) ≃ Σa, B' a :=
  sigma_equiv_sigma equiv.rfl Hg

  definition sigma_equiv_sigma_left [constructor] (Hf : A ≃ A') :
    (Σa, B a) ≃ (Σa', B (to_inv Hf a')) :=
  sigma_equiv_sigma Hf (λ a, equiv_ap B !right_inv⁻¹)

  definition sigma_equiv_sigma_left' [constructor] (Hf : A' ≃ A) : (Σa, B (Hf a)) ≃ (Σa', B a') :=
  sigma_equiv_sigma Hf (λa, erfl)

  definition ap_sigma_functor_eq_dpair (p : a = a') (q : b =[p] b') :
    ap (sigma_functor f g) (sigma_eq p q) = sigma_eq (ap f p) (pathover.rec_on q idpo) :=
  by induction q; reflexivity

  definition sigma_ua {A B : Type} (C : A ≃ B → Type) :
    (Σ(p : A = B), C (equiv_of_eq p)) ≃ Σ(e : A ≃ B), C e :=
  sigma_equiv_sigma_left' !eq_equiv_equiv

  -- definition ap_sigma_functor_eq (p : u.1 = v.1) (q : u.2 =[p] v.2)
  --   : ap (sigma_functor f g) (sigma_eq p q) =
  --     sigma_eq (ap f p)
  --      ((tr_compose B' f p (g u.1 u.2))⁻¹ ⬝ (fn_tr_eq_tr_fn p g u.2)⁻¹ ⬝ ap (g v.1) q) :=
  -- by induction u; induction v; apply ap_sigma_functor_eq_dpair

  /- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/

  definition is_equiv_pr1 [instance] [constructor] (B : A → Type) [H : Π a, is_contr (B a)]
      : is_equiv (@pr1 A B) :=
  adjointify pr1
             (λa, ⟨a, !center⟩)
             (λa, idp)
             (λu, sigma_eq idp (pathover_idp_of_eq !center_eq))

  definition sigma_equiv_of_is_contr_right [constructor] [H : Π a, is_contr (B a)]
    : (Σa, B a) ≃ A :=
  equiv.mk pr1 _

  /- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

  definition sigma_equiv_of_is_contr_left [constructor] (B : A → Type) [H : is_contr A]
    : (Σa, B a) ≃ B (center A) :=
  equiv.MK
    (λu, (center_eq u.1)⁻¹ ▸ u.2)
    (λb, ⟨!center, b⟩)
    abstract (λb, ap (λx, x ▸ b) !prop_eq_of_is_contr) end
    abstract (λu, sigma_eq !center_eq !tr_pathover) end

  /- Associativity -/

  --this proof is harder than in Coq because we don't have eta definitionally for sigma
  definition sigma_assoc_equiv [constructor] (C : (Σa, B a) → Type)
    : (Σa b, C ⟨a, b⟩) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
    (λuc, ⟨uc.1.1, uc.1.2, !sigma.eta⁻¹ ▸ uc.2⟩)
    abstract begin intro uc, induction uc with u c, induction u, reflexivity end end
    abstract begin intro av, induction av with a v, induction v, reflexivity end end)

  open prod prod.ops
  definition assoc_equiv_prod [constructor] (C : (A × A') → Type) : (Σa a', C (a,a')) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨(av.1, av.2.1), av.2.2⟩)
    (λuc, ⟨pr₁ (uc.1), pr₂ (uc.1), !prod.eta⁻¹ ▸ uc.2⟩)
    abstract proof (λuc, destruct uc (λu, prod.destruct u (λa b c, idp))) qed end
    abstract proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed end)

  /- Symmetry -/

  definition comm_equiv_unc (C : A × A' → Type) : (Σa a', C (a, a')) ≃ (Σa' a, C (a, a')) :=
  calc
    (Σa a', C (a, a')) ≃ Σu, C u          : assoc_equiv_prod
                   ... ≃ Σv, C (flip v)   : sigma_equiv_sigma !prod_comm_equiv
                                              (λu, prod.destruct u (λa a', equiv.rfl))
                   ... ≃ Σa' a, C (a, a') : assoc_equiv_prod

  definition sigma_comm_equiv [constructor] (C : A → A' → Type)
    : (Σa a', C a a') ≃ (Σa' a, C a a') :=
  comm_equiv_unc (λu, C (prod.pr1 u) (prod.pr2 u))

  definition equiv_prod [constructor] (A B : Type) : (Σ(a : A), B) ≃ A × B :=
  equiv.mk _ (adjointify
    (λs, (s.1, s.2))
    (λp, ⟨pr₁ p, pr₂ p⟩)
    proof (λp, prod.destruct p (λa b, idp)) qed
    proof (λs, destruct s (λa b, idp)) qed)

  definition comm_equiv_nondep (A B : Type) : (Σ(a : A), B) ≃ Σ(b : B), A :=
  calc
    (Σ(a : A), B) ≃ A × B       : equiv_prod
              ... ≃ B × A       : prod_comm_equiv
              ... ≃ Σ(b : B), A : equiv_prod

  definition sigma_assoc_comm_equiv {A : Type} (B C : A → Type)
    : (Σ(v : Σa, B a), C v.1) ≃ (Σ(u : Σa, C a), B u.1) :=
  calc    (Σ(v : Σa, B a), C v.1)
        ≃ (Σa (b : B a), C a)     : sigma_assoc_equiv
    ... ≃ (Σa (c : C a), B a)     : sigma_equiv_sigma_right (λa, !comm_equiv_nondep)
    ... ≃ (Σ(u : Σa, C a), B u.1) : sigma_assoc_equiv

  /- Interaction with other type constructors -/

  definition sigma_empty_left [constructor] (B : empty → Type) : (Σx, B x) ≃ empty :=
  begin
    fapply equiv.MK,
    { intro v, induction v, contradiction},
    { intro x, contradiction},
    { intro x, contradiction},
    { intro v, induction v, contradiction},
  end

  definition sigma_empty_right [constructor] (A : Type) : (Σ(a : A), empty) ≃ empty :=
  begin
    fapply equiv.MK,
    { intro v, induction v, contradiction},
    { intro x, contradiction},
    { intro x, contradiction},
    { intro v, induction v, contradiction},
  end

  definition sigma_unit_left [constructor] (B : unit → Type) : (Σx, B x) ≃ B star :=
  !sigma_equiv_of_is_contr_left

  definition sigma_unit_right [constructor] (A : Type) : (Σ(a : A), unit) ≃ A :=
  !sigma_equiv_of_is_contr_right

  definition sigma_sum_left [constructor] (B : A + A' → Type)
    : (Σp, B p) ≃ (Σa, B (inl a)) + (Σa, B (inr a)) :=
  begin
    fapply equiv.MK,
    { intro v,
      induction v with p b,
      induction p,
      { apply inl, constructor, assumption },
      { apply inr, constructor, assumption }},
    { intro p, induction p with v v: induction v; constructor; assumption},
    { intro p, induction p with v v: induction v; reflexivity},
    { intro v, induction v with p b, induction p: reflexivity},
  end

  definition sigma_sum_right [constructor] (B C : A → Type)
    : (Σa, B a + C a) ≃ (Σa, B a) + (Σa, C a) :=
  begin
    fapply equiv.MK,
    { intro v,
      induction v with a p,
      induction p,
      { apply inl, constructor, assumption},
      { apply inr, constructor, assumption}},
    { intro p,
      induction p with v v,
      { induction v, constructor, apply inl, assumption },
      { induction v, constructor, apply inr, assumption }},
    { intro p, induction p with v v: induction v; reflexivity},
    { intro v, induction v with a p, induction p: reflexivity},
  end

  definition sigma_sigma_eq_right {A : Type} (a : A) (P : Π(b : A), a = b → Type)
    : (Σ(b : A) (p : a = b), P b p) ≃ P a idp :=
  calc
    (Σ(b : A) (p : a = b), P b p) ≃ (Σ(v : Σ(b : A), a = b), P v.1 v.2) : sigma_assoc_equiv
      ... ≃ P a idp : !sigma_equiv_of_is_contr_left

  definition sigma_sigma_eq_left {A : Type} (a : A) (P : Π(b : A), b = a → Type)
    : (Σ(b : A) (p : b = a), P b p) ≃ P a idp :=
  calc
    (Σ(b : A) (p : b = a), P b p) ≃ (Σ(v : Σ(b : A), b = a), P v.1 v.2) : sigma_assoc_equiv
      ... ≃ P a idp : !sigma_equiv_of_is_contr_left

  /- ** Universal mapping properties -/
  /- *** The positive universal property. -/

  section
  definition is_equiv_sigma_rec [instance] (C : (Σa, B a) → Type)
    : is_equiv (sigma.rec : (Πa b, C ⟨a, b⟩) → Πab, C ab) :=
  adjointify _ (λ g a b, g ⟨a, b⟩)
               (λ g, proof eq_of_homotopy (λu, destruct u (λa b, idp)) qed)
               (λ f, refl f)

  definition equiv_sigma_rec (C : (Σa, B a) → Type)
    : (Π(a : A) (b: B a), C ⟨a, b⟩) ≃ (Πxy, C xy) :=
  equiv.mk sigma.rec _

  /- *** The negative universal property. -/

  protected definition coind_unc (fg : Σ(f : Πa, B a), Πa, C a (f a)) (a : A)
    : Σ(b : B a), C a b :=
  ⟨fg.1 a, fg.2 a⟩

  protected definition coind (f : Π a, B a) (g : Π a, C a (f a)) (a : A) : Σ(b : B a), C a b :=
  sigma.coind_unc ⟨f, g⟩ a

  --is the instance below dangerous?
  --in Coq this can be done without function extensionality
  definition is_equiv_coind [instance] (C : Πa, B a → Type)
    : is_equiv (@sigma.coind_unc _ _ C) :=
  adjointify _ (λ h, ⟨λa, (h a).1, λa, (h a).2⟩)
               (λ h, proof eq_of_homotopy (λu, !sigma.eta) qed)
               (λfg, destruct fg (λ(f : Π (a : A), B a) (g : Π (x : A), C x (f x)), proof idp qed))

  definition sigma_pi_equiv_pi_sigma : (Σ(f : Πa, B a), Πa, C a (f a)) ≃ (Πa, Σb, C a b) :=
  equiv.mk sigma.coind_unc _
  end

  /- Subtypes (sigma types whose second components are props) -/

  definition subtype [reducible] {A : Type} (P : A → Type) [H : Πa, is_prop (P a)] :=
  Σ(a : A), P a
  notation [parsing_only] `{` binder `|` r:(scoped:1 P, subtype P) `}` := r

  /- To prove equality in a subtype, we only need equality of the first component. -/
  definition subtype_eq [unfold_full] [H : Πa, is_prop (B a)] {u v : {a | B a}} :
    u.1 = v.1 → u = v :=
  sigma_eq_unc ∘ inv pr1

  definition is_equiv_subtype_eq [constructor] [H : Πa, is_prop (B a)] (u v : {a | B a})
      : is_equiv (subtype_eq : u.1 = v.1 → u = v) :=
  !is_equiv_compose
  local attribute is_equiv_subtype_eq [instance]

  definition equiv_subtype [constructor] [H : Πa, is_prop (B a)] (u v : {a | B a}) :
    (u.1 = v.1) ≃ (u = v) :=
  equiv.mk !subtype_eq _

  definition subtype_eq_equiv [constructor] [H : Πa, is_prop (B a)] (u v : {a | B a}) :
    (u = v) ≃ (u.1 = v.1) :=
  (equiv_subtype u v)⁻¹ᵉ

  definition subtype_eq_inv {A : Type} {B : A → Type} [H : Πa, is_prop (B a)] (u v : Σa, B a)
    : u = v → u.1 = v.1 :=
  subtype_eq⁻¹ᶠ

  local attribute subtype_eq_inv [reducible]
  definition is_equiv_subtype_eq_inv {A : Type} {B : A → Type} [H : Πa, is_prop (B a)]
    (u v : Σa, B a) : is_equiv (subtype_eq_inv u v) :=
  _

  /- truncatedness -/
  theorem is_trunc_sigma (B : A → Type) (n : trunc_index)
      [HA : is_trunc n A] [HB : Πa, is_trunc n (B a)] : is_trunc n (Σa, B a) :=
  begin
  revert A B HA HB,
  induction n with n IH,
  { intro A B HA HB, fapply is_trunc_equiv_closed_rev, apply sigma_equiv_of_is_contr_left},
  { intro A B HA HB, apply is_trunc_succ_intro, intro u v,
    apply is_trunc_equiv_closed_rev,
      apply sigma_eq_equiv,
      exact IH _ _ _ _}
  end

  theorem is_trunc_subtype (B : A → Prop) (n : trunc_index)
      [HA : is_trunc (n.+1) A] : is_trunc (n.+1) (Σa, B a) :=
  @(is_trunc_sigma B (n.+1)) _ (λa, !is_trunc_succ_of_is_prop)

  /- if the total space is a mere proposition, you can equate two points in the base type by
     finding points in their fibers -/
  definition eq_base_of_is_prop_sigma {A : Type} (B : A → Type) (H : is_prop (Σa, B a)) {a a' : A}
    (b : B a) (b' : B a') : a = a' :=
  (is_prop.elim ⟨a, b⟩ ⟨a', b'⟩)..1

end sigma

attribute sigma.is_trunc_sigma [instance] [priority 1490]
attribute sigma.is_trunc_subtype [instance] [priority 1200]

namespace sigma

  /- pointed sigma type -/
  open pointed

  definition pointed_sigma [instance] [constructor] {A : Type} (P : A → Type) [G : pointed A]
      [H : pointed (P pt)] : pointed (Σx, P x) :=
  pointed.mk ⟨pt,pt⟩

  definition psigma [constructor] {A : Type*} (P : A → Type*) : Type* :=
  pointed.mk' (Σa, P a)

  notation `Σ*` binders `, ` r:(scoped P, psigma P) := r

  definition ppr1 [constructor] {A : Type*} {B : A → Type*} : (Σ*(x : A), B x) →* A :=
  pmap.mk pr1 idp

  definition ppr2 [unfold_full] {A : Type*} {B : A → Type*} (v : (Σ*(x : A), B x)) : B (ppr1 v) :=
  pr2 v

  definition ptsigma [constructor] {n : ℕ₋₂} {A : n-Type*} (P : A → n-Type*) : n-Type* :=
  ptrunctype.mk' n (Σa, P a)

end sigma
