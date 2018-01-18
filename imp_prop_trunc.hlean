/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Proof of the theorem that (is_trunc n A) is a mere proposition
We prove this here to avoid circular dependency of files
We want to use this in .equiv; .equiv is imported by .function and .function is imported by .trunc
-/

import types.pi

open equiv sigma sigma.ops eq function pi

namespace is_trunc
  definition is_contr.sigma_char (A : Type) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.MK,
    { intro S, exact (is_contr.mk S.1 S.2)},
    { intro H, cases H with H', cases H' with ce co, exact ⟨ce, co⟩},
    { intro H, cases H with H', cases H' with ce co, exact idp},
    { intro S, cases S, apply idp}
  end

  definition is_trunc.pi_char (n : trunc_index) (A : Type) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.MK,
    { intro H, apply is_trunc_succ_intro},
    { intro H x y, apply is_trunc_eq},
    { intro H, cases H, apply idp},
    { intro P, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro b,
      change is_trunc.mk (to_internal n (a = b)) = P a b,
      induction (P a b), apply idp},
  end

  definition is_prop_is_trunc (n : trunc_index) :
    Π (A : Type), is_prop (is_trunc n A) :=
  begin
    induction n,
    { intro A,
      apply is_trunc_is_equiv_closed,
      { apply equiv.to_is_equiv, apply is_contr.sigma_char},
      apply is_prop.mk, intros,
      fapply sigma_eq, apply x.2,
      apply is_prop.elimo},
    { intro A,
      apply is_trunc_is_equiv_closed,
      apply equiv.to_is_equiv,
      apply is_trunc.pi_char},
  end

  local attribute is_prop_is_trunc [instance]
  definition is_trunc_succ_is_trunc [instance] (n m : ℕ₋₂) (A : Type) :
    is_trunc (n.+1) (is_trunc m A) :=
  !is_trunc_succ_of_is_prop

end is_trunc
