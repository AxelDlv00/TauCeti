/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon (claude+codex), Axel Delaval, Chunlei Liu,
Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Chart Gram matrices of a Riemannian metric

This file constructs the Gram matrix of the canonical Riemannian metric in the local frame
induced by a tangent-bundle trivialization and proves that its entries and the entries of its
inverse are smooth on the trivialization base set. The construction uses
`Bundle.Trivialization.localFrame` and `Bundle.Trivialization.basisAt`, so it applies unchanged
when the model space has dimension zero.

The Gram-matrix and inverse-matrix declarations are adapted from stages 1--5 of the Apache-2.0
Poincare-Conjecture source file
`DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. That source uses an explicit metric and a custom
chart frame; here Mathlib's canonical `RiemannianBundle` metric and local-frame API replace them.
As in the source, inverse-entry smoothness is proved through the determinant and adjugate formula.

## Main definitions and results

* `Riemannian.Tensor.chartLocalFrame`: the frame induced by the tangent trivialization at a chart
  centre and `Module.finBasis`.
* `Riemannian.Tensor.chartGramMatrix`: the metric Gram matrix in this frame.
* `Riemannian.Tensor.chartGramMatrix_posDef`: positive-definiteness on the base set.
* `Riemannian.Tensor.chartGramMatrix_det_pos`: strict positivity of its determinant there.
* `Riemannian.Tensor.chartGramMatrix_entry_contMDiffOn`: smoothness of Gram-matrix entries.
* `Riemannian.Tensor.chartInvGramMatrix`: the inverse Gram matrix.
* `Riemannian.Tensor.chartInvGramMatrix_entry_contMDiffOn`: smoothness of inverse entries.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
* Poincare-Conjecture, `DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, stages 1--5,
  revision `24f32e4d600878bfaac6bc2f2f9324175571c321` (Apache-2.0).

-/

@[expose] public section

noncomputable section

open Bundle FiberBundle Manifold Set
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-local frame obtained from the tangent-bundle trivialization centred at `α` and
the chosen `Module.finBasis` basis of the model space. Outside the trivialization base set it has
Mathlib's standard junk value `0`. -/
def chartLocalFrame (α : M) :
    Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).localFrame (Module.finBasis ℝ E)

@[simp]
theorem chartLocalFrame_apply_of_mem_baseSet (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartLocalFrame (I := I) α i x =
      (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E)
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx) i := by
  simpa only [chartLocalFrame, TangentBundle.trivializationAt_baseSet] using
    (trivializationAt E (TangentSpace I) α).localFrame_apply_of_mem_baseSet
      (Module.finBasis ℝ E) (i := i) (by
        simpa only [TangentBundle.trivializationAt_baseSet] using hx)

/-- Each member of `chartLocalFrame` is smooth on the tangent-trivialization base set. -/
theorem chartLocalFrame_contMDiffOn (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ TotalSpace.mk' E x (chartLocalFrame (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (trivializationAt E (TangentSpace I) α).contMDiffOn_localFrame_baseSet
    (n := ∞) (Module.finBasis ℝ E) i

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Gram matrix of `chartLocalFrame α` for the canonical Riemannian metric at `x`. Its
entries are the coordinate metric coefficients used in do Carmo, *Riemannian Geometry*,
Chapter 2. -/
def chartGramMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.gram ℝ fun i ↦ chartLocalFrame (I := I) α i x

@[simp]
theorem chartGramMatrix_apply (α x : M) (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) α x i j =
      inner ℝ (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) :=
  rfl

/-- The chart Gram matrix is Hermitian, equivalently symmetric over `ℝ`. -/
theorem chartGramMatrix_isHermitian (α x : M) :
    (chartGramMatrix (I := I) α x).IsHermitian :=
  Matrix.isHermitian_gram ℝ _

/-- The Gram-matrix quadratic form equals the squared norm, in the canonical Riemannian metric,
of the corresponding linear combination of chart-frame vectors. -/
theorem chartGramMatrix_dotProduct_mulVec
    (α x : M) (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix (I := I) α x) *ᵥ c =
      inner ℝ
        (∑ i, c i • chartLocalFrame (I := I) α i x)
        (∑ j, c j • chartLocalFrame (I := I) α j x) :=
  Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) _ c c

/-- The Gram matrix of the chart-local frame is positive-definite on the tangent-trivialization
base set. -/
theorem chartGramMatrix_posDef (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix (I := I) α x).PosDef :=
  Matrix.posDef_gram_of_linearIndependent <|
    ((trivializationAt E (TangentSpace I) α).isLocalFrameOn_localFrame_baseSet
      I ∞ (Module.finBasis ℝ E)).linearIndependent hx

/-- The determinant of the chart Gram matrix is strictly positive on the tangent-trivialization
base set. -/
theorem chartGramMatrix_det_pos (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < (chartGramMatrix (I := I) α x).det :=
  (chartGramMatrix_posDef (I := I) α hx).det_pos

section Smooth

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] in
private lemma contMDiffOn_inner_tangent
    {s : Set M} {X Y : ∀ x : M, TangentSpace I x}
    (hX : CMDiff[s] ∞ (T% X)) (hY : CMDiff[s] ∞ (T% Y)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ inner ℝ (X x) (Y x)) s :=
  ContMDiffOn.inner_bundle hX hY

/-- Every entry of the chart Gram matrix is smooth on the tangent-trivialization base set. -/
theorem chartGramMatrix_entry_contMDiffOn
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ chartGramMatrix (I := I) α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  exact contMDiffOn_inner_tangent (chartLocalFrame_contMDiffOn (I := I) α i)
    (chartLocalFrame_contMDiffOn (I := I) α j)

/-- The determinant of the chart Gram matrix is smooth on the tangent-trivialization base set.
The proof expands the determinant as a finite sum of finite products of entries. -/
theorem chartGramMatrix_det_contMDiffOn (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ (chartGramMatrix (I := I) α x).det)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M ↦ (chartGramMatrix (I := I) α x).det) =
        fun x : M ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) * ∏ i, chartGramMatrix (I := I) α x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum fun σ _ ↦ ?_
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd fun i _ ↦ ?_
  exact chartGramMatrix_entry_contMDiffOn (I := I) α (σ i) i

/-- Every adjugate entry of the chart Gram matrix is smooth on the tangent-trivialization base
set. The proof realizes the entry as the determinant of a row-updated matrix. -/
theorem chartGramMatrix_adjugate_entry_contMDiffOn
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M ↦ (chartGramMatrix (I := I) α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M ↦ (chartGramMatrix (I := I) α x).adjugate i j) =
        fun x : M ↦ ((chartGramMatrix (I := I) α x).updateRow j
          (Pi.single i (1 : ℝ))).det := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp' :
      (fun x : M ↦ ((chartGramMatrix (I := I) α x).updateRow j
          (Pi.single i (1 : ℝ))).det) =
        fun x : M ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (chartGramMatrix (I := I) α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp']
  refine contMDiffOn_finsetSum fun σ _ ↦ ?_
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd fun k _ ↦ ?_
  by_cases hσk : σ k = j
  · have heq :
        (fun x : M ↦ (chartGramMatrix (I := I) α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          fun _ : M ↦
            Pi.single (M := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i (1 : ℝ) k := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun x : M ↦ (chartGramMatrix (I := I) α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          fun x : M ↦ chartGramMatrix (I := I) α x (σ k) k := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) α (σ k) k

end Smooth

/-- The inverse coordinate-metric matrix from do Carmo, *Riemannian Geometry*, Chapter 2. On the
tangent-trivialization base set this is the inverse of a positive-definite matrix. -/
def chartInvGramMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) α x)⁻¹

/-- On the tangent-trivialization base set, the inverse Gram matrix is a left inverse. -/
theorem chartInvGramMatrix_mul_chartGramMatrix (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) α x * chartGramMatrix (I := I) α x = 1 := by
  have hdet_unit : IsUnit (chartGramMatrix (I := I) α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) α hx))
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- On the tangent-trivialization base set, the inverse Gram matrix is a right inverse. -/
theorem chartGramMatrix_mul_chartInvGramMatrix (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) α x * chartInvGramMatrix (I := I) α x = 1 := by
  have hdet_unit : IsUnit (chartGramMatrix (I := I) α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) α hx))
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

section Smooth

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Every entry of the inverse chart Gram matrix is smooth on the tangent-trivialization base
set. Following the source, the proof uses the determinant/adjugate formula. -/
theorem chartInvGramMatrix_entry_contMDiffOn
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x : M ↦ chartInvGramMatrix (I := I) α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) α x i j =
        ((chartGramMatrix (I := I) α x).det)⁻¹ *
          (chartGramMatrix (I := I) α x).adjugate i j := by
    intro x _
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) α x).det •
          (chartGramMatrix (I := I) α x).adjugate) i j =
      ((chartGramMatrix (I := I) α x).det)⁻¹ *
        (chartGramMatrix (I := I) α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr (ContMDiffOn.mul ?_ ?_) hcongr
  · have hdet_smooth := chartGramMatrix_det_contMDiffOn (I := I) α
    intro x hx
    have hdet_ne : (chartGramMatrix (I := I) α x).det ≠ 0 :=
      ne_of_gt (chartGramMatrix_det_pos (I := I) α hx)
    have hinv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ y⁻¹)
        (chartGramMatrix (I := I) α x).det :=
      contDiffAt_inv _ hdet_ne
    exact hinv.contMDiffAt.comp_contMDiffWithinAt x (hdet_smooth x hx)
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) α i j

end Smooth

end Tensor
end Riemannian
