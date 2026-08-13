/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Products of submodules and their quotients

A product submodule `p.prod q ≤ M × N` is, as a module, the product `p × q`, and the quotient by
it is the product of the two quotients:

`(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.

Mathlib has the corresponding statement for setoids (`Setoid.prodQuotientEquiv`) and for a ring
quotient by a pair of complementary idempotents (`AlgEquiv.prodQuotientOfIsIdempotentElem`), but
not for submodules.

## Main declarations

* `Submodule.prodSubtypeEquiv`: `↥(p.prod q) ≃ₗ p × q`.
* `Submodule.quotientProdEquiv`: `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`.
* `Submodule.finrank_quotient_prod`: the ranks of the quotients add.
-/

public section

namespace Submodule

section

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- A product submodule, as a module, is the product of the two submodules. -/
def prodSubtypeEquiv (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem prodSubtypeEquiv_apply (p : Submodule R M) (q : Submodule R N) (x : ↥(p.prod q)) :
    prodSubtypeEquiv p q x = (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) :=
  (rfl)

/-- The quotient by a product of submodules is the product of the quotients. -/
noncomputable def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) := by
  let f : M × N →ₗ[R] (M ⧸ p) × (N ⧸ q) := p.mkQ.prodMap q.mkQ
  have hker : LinearMap.ker f = p.prod q := by
    simp [f]
  let g : ((M × N) ⧸ p.prod q) →ₗ[R] (M ⧸ p) × (N ⧸ q) := (p.prod q).liftQ f hker.ge
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (p.prod q) f hker.ge hker.le)
  · rintro ⟨⟨x⟩, ⟨y⟩⟩
    refine ⟨(p.prod q).mkQ (x, y), ?_⟩
    simp only [g, Submodule.mkQ_apply, Submodule.liftQ_apply, f, LinearMap.prodMap_apply,
      Submodule.Quotient.quot_mk_eq_mk]

@[simp]
theorem quotientProdEquiv_mk (p : Submodule R M) (q : Submodule R N) (x : M × N) :
    quotientProdEquiv p q ((p.prod q).mkQ x) = (p.mkQ x.1, q.mkQ x.2) :=
  (rfl)

end

section Finrank

variable {R M N : Type*} [DivisionRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The quotient by a product of submodules has rank the sum of the two quotients' ranks. -/
theorem finrank_quotient_prod (p : Submodule R M) (q : Submodule R N)
    [FiniteDimensional R (M ⧸ p)] [FiniteDimensional R (N ⧸ q)] :
    Module.finrank R ((M × N) ⧸ p.prod q)
      = Module.finrank R (M ⧸ p) + Module.finrank R (N ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, Module.finrank_prod]

end Finrank

end Submodule
