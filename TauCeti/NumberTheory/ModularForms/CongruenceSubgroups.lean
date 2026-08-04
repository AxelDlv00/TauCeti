/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Congruence subgroup infrastructure for `Γ₁(N) ⊴ Γ₀(N)`

Foundational results about the pair `Γ₁(N) ≤ Γ₀(N)` beyond Mathlib's
`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`: `Γ₀(N)` normalizes `Γ₁(N)` (also
after mapping to `GL₂(ℝ)`), the ratio of two `Γ₀(N)`-elements with equal lower-right entry
lies in `Γ₁(N)`, and the lower-right-entry map `Γ₀(N) →* (ZMod N)ˣ` is surjective.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted from
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` as congruence-subgroup
infrastructure independent of the diamond operators.

## Main results

* `CongruenceSubgroup.Gamma0_normalizes_Gamma1`: conjugation by `Γ₀(N)` preserves `Γ₁(N)`.
* `CongruenceSubgroup.Gamma1_map_inv_conjAct_eq`: `(Gamma1 N).map (mapGL ℝ)` is invariant
  under conjugation by `Γ₀(N)` elements in `GL₂(ℝ)`.
* `CongruenceSubgroup.Gamma0Map_toHomUnits_surjective`: every unit of `ZMod N` is the
  lower-right entry of a matrix in `Γ₀(N)` (via strong approximation for `SL₂`).
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

variable {N : ℕ}

namespace CongruenceSubgroup

/-- Conjugation by a `Gamma0 N` element preserves `Gamma1 N`.
This is the foundation for the diamond operator `⟨d⟩` on modular forms. -/
theorem Gamma0_normalizes_Gamma1 (g : ↥(Gamma0 N)) (h : SL(2, ℤ)) (hh : h ∈ Gamma1 N) :
    (g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
  (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <|
    (Gamma0Map N).normal_ker.conj_mem ⟨h, Gamma1_in_Gamma0 N hh⟩
      ((Gamma1_to_Gamma0_mem _).mpr ((Gamma1_mem _ _).mp hh)) g

/-- `(Gamma1 N).map (mapGL ℝ)` is invariant under conjugation by `Gamma0 N` elements
in `GL₂(ℝ)`. -/
theorem Gamma1_map_inv_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ)))⁻¹ •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    have hmem : (g : SL(2, ℤ))⁻¹ * σ * (g : SL(2, ℤ)) ∈ Gamma1 N := by
      simpa [inv_inv] using Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ σ hσ
    exact ⟨_, hmem, by
      simp only [map_mul, map_inv, hσy]
      group⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨(g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹,
      Gamma0_normalizes_Gamma1 g σ hσ, by simp [map_mul, map_inv]⟩

/-- If two `Γ₀(N)` elements have equal image under `Gamma0Map`, their ratio
`g₁ · g₂⁻¹` lies in `Γ₁(N)` (as an `SL₂(ℤ)` element). -/
lemma mul_inv_mem_Gamma1_of_Gamma0Map_eq (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
  have hker : g₁ * g₂⁻¹ ∈ (Gamma0Map N).ker := by
    rw [← div_eq_mul_inv]
    exact (MonoidHom.div_mem_ker_iff (Gamma0Map N)).mpr heq
  exact (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp hker

/-- The diagonal matrix `!![u⁻¹, 0; 0, u]` as an element of `SL₂(ZMod N)`. -/
private def diagUnit (u : (ZMod N)ˣ) : SpecialLinearGroup (Fin 2) (ZMod N) :=
  ⟨!![(↑u⁻¹ : ZMod N), 0; 0, ↑u], by simp [det_fin_two_of]⟩

private lemma coe_diagUnit (u : (ZMod N)ˣ) :
    (diagUnit u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![(↑u⁻¹ : ZMod N), 0; 0, ↑u] := rfl

/-- `(Gamma0Map N).toHomUnits` is surjective: every unit `u ∈ (ZMod N)ˣ` is realized as the
lower-right entry of some `g ∈ Gamma0 N`, by strong approximation for `SL₂`. -/
theorem Gamma0Map_toHomUnits_surjective [NeZero N] :
    Function.Surjective ((Gamma0Map N).toHomUnits) := fun u ↦ by
  obtain ⟨g, hg⟩ := map_intCast_zmod_surjective (diagUnit u)
  have hentry : ∀ i j, ((g i j : ℤ) : ZMod N) =
      (!![(↑u⁻¹ : ZMod N), 0; 0, ↑u] : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := fun i j => by
    have h := congrArg
      (fun A : SpecialLinearGroup (Fin 2) (ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N)) i j)
      hg
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
      coe_diagUnit] using h
  have h10 : ((g 1 0 : ℤ) : ZMod N) = 0 := by rw [hentry]; simp
  have h11 : ((g 1 1 : ℤ) : ZMod N) = u := by rw [hentry]; simp
  exact ⟨⟨g, Gamma0_mem.mpr h10⟩, Units.ext (by simpa [Gamma0Map] using h11)⟩

end CongruenceSubgroup
