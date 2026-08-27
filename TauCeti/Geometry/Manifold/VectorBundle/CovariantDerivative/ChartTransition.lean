/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Chart transitions and their derivatives

This module packages the chart-transition family used by covariant derivatives and Christoffel
transformation laws.  For charts centred at `β` and `α`, `chartTransition β α` is
the extended-coordinate map from `β` to `α`, restricted by `chartTransitionSource β α` to their
common overlap.  The module records the overlap identities, smoothness, first derivative, and
the coordinate entries of the first and second derivatives.

The declarations port the transition section of
`DoCarmoLib/Riemannian/Connection/ChartChristoffelChange.lean` at source revision
`24f32e4d600878bfaac6bc2f2f9324175571c321` ([poincareConjectureDoCarmo]).  Keeping this family
below both the along-curve and Christoffel-change layers follows the source import direction. The
definitions only use the manifold structure, so this port removes the staging implementation's
unnecessary dependency on a Riemannian metric.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Section 2, Proposition 2.2
  ([doCarmo1992]).
* John M. Lee, *Introduction to Riemannian Manifolds*, Chapter 4, Proposition 4.7,
  equation (4.10) ([lee2018]).
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Transition

variable [I.Boundaryless]

/-- The transition from `β`-coordinates to `α`-coordinates on the extended chart model
([doCarmo1992]). -/
def chartTransition (β α : M) : E → E :=
  extChartAt I α ∘ (extChartAt I β).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- Unfold the chart-transition map ([doCarmo1992]). -/
@[simp]
theorem chartTransition_def (β α : M) (y : E) :
    chartTransition (I := I) β α y =
      extChartAt I α ((extChartAt I β).symm y) := rfl

/-- The overlap of the two extended charts, written in `β`-coordinates ([doCarmo1992]). -/
def chartTransitionSource (β α : M) : Set E :=
  ((extChartAt I β).symm.trans (extChartAt I α)).source

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The transition-source formula in terms of the extended chart target and source
([doCarmo1992]). -/
theorem chartTransitionSource_eq (β α : M) :
    chartTransitionSource (I := I) (M := M) β α =
      (extChartAt I β).target ∩
        (extChartAt I β).symm ⁻¹' (chartAt H α).source := by
  unfold chartTransitionSource
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, extChartAt_source]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The common transition source is open ([doCarmo1992]). -/
theorem isOpen_chartTransitionSource (β α : M) :
    IsOpen (chartTransitionSource (I := I) (M := M) β α) := by
  rw [chartTransitionSource_eq]
  exact ContinuousOn.isOpen_inter_preimage (continuousOn_extChartAt_symm β)
    (isOpen_extChartAt_target β) (chartAt H α).open_source

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The inverse `β`-chart coordinate of an overlap point comes from the `β` chart source. -/
lemma extChartAt_symm_mem_chartAt_source_left {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    (extChartAt I β).symm y ∈ (chartAt H β).source := by
  rw [chartTransitionSource_eq] at hy
  have h := (extChartAt I β).map_target hy.1
  rwa [extChartAt_source] at h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The inverse `β`-chart coordinate of an overlap point also lies in the `α` chart source. -/
lemma extChartAt_symm_mem_chartAt_source_right {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    (extChartAt I β).symm y ∈ (chartAt H α).source := by
  rw [chartTransitionSource_eq] at hy
  exact hy.2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The transition image lies in the target of the `α` extended chart. -/
lemma chartTransition_mem_target {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    chartTransition (I := I) β α y ∈ (extChartAt I α).target := by
  refine (extChartAt I α).map_source ?_
  rw [extChartAt_source]
  exact extChartAt_symm_mem_chartAt_source_right (I := I) hy

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The inverse `α`-chart map recovers the inverse `β`-chart map on the overlap. -/
lemma extChartAt_symm_chartTransition {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    (extChartAt I α).symm (chartTransition (I := I) β α y) =
      (extChartAt I β).symm y := by
  refine (extChartAt I α).left_inv ?_
  rw [extChartAt_source]
  exact extChartAt_symm_mem_chartAt_source_right (I := I) hy

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- A point in both chart sources yields a point in the transition source ([doCarmo1992]). -/
theorem extChartAt_mem_chartTransitionSource {β α : M} {x : M}
    (hxβ : x ∈ (chartAt H β).source) (hxα : x ∈ (chartAt H α).source) :
    extChartAt I β x ∈ chartTransitionSource (I := I) (M := M) β α := by
  have hxβ' : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact hxβ
  rw [chartTransitionSource_eq]
  refine ⟨(extChartAt I β).map_source hxβ', ?_⟩
  rw [mem_preimage, (extChartAt I β).left_inv hxβ']
  exact hxα

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The transition map sends a `β`-chart coordinate back to the `α`-chart coordinate
([doCarmo1992]). -/
theorem chartTransition_extChartAt {β α : M} {x : M}
    (hxβ : x ∈ (chartAt H β).source) :
    chartTransition (I := I) β α (extChartAt I β x) = extChartAt I α x := by
  have hxβ' : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact hxβ
  rw [chartTransition_def, (extChartAt I β).left_inv hxβ']

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Smoothness of the chart transition on its overlap source ([doCarmo1992]). -/
theorem contDiffOn_chartTransition (β α : M) :
    ContDiffOn ℝ ∞ (chartTransition (I := I) β α)
      (chartTransitionSource (I := I) (M := M) β α) :=
  contDiffOn_ext_coord_change (I := I) α β

omit [FiniteDimensional ℝ E] in
/-- Smoothness of a chart transition at a point of its overlap ([doCarmo1992]). -/
theorem contDiffAt_chartTransition {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    ContDiffAt ℝ ∞ (chartTransition (I := I) β α) y :=
  (contDiffOn_chartTransition (I := I) β α).contDiffAt
    ((isOpen_chartTransitionSource (I := I) β α).mem_nhds hy)

omit [FiniteDimensional ℝ E] in
/-- The derivative of a chart transition is the tangent-coordinate change ([doCarmo1992]). -/
theorem hasFDerivAt_chartTransition {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    HasFDerivAt (chartTransition (I := I) β α)
      (tangentCoordChange I β α ((extChartAt I β).symm y)) y := by
  have hβ : (extChartAt I β).symm y ∈ (extChartAt I β).source := by
    have hy' : y ∈ (extChartAt I β).target := by
      rw [chartTransitionSource_eq] at hy
      exact hy.1
    simpa only [extChartAt_source] using (extChartAt I β).map_target hy'
  have hα : (extChartAt I β).symm y ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    rw [chartTransitionSource_eq] at hy
    exact hy.2
  have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hβ, hα⟩
  rw [I.range_eq_univ] at hw
  rw [show extChartAt I β ((extChartAt I β).symm y) = y by
    exact (extChartAt I β).right_inv (by
      rw [chartTransitionSource_eq] at hy
      exact hy.1)] at hw
  exact hasFDerivWithinAt_univ.mp hw

omit [FiniteDimensional ℝ E] in
/-- The Fréchet derivative of a chart transition, in the overlap source ([doCarmo1992]). -/
theorem fderiv_chartTransition {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    fderiv ℝ (chartTransition (I := I) β α) y =
      tangentCoordChange I β α ((extChartAt I β).symm y) :=
  (hasFDerivAt_chartTransition (I := I) hy).fderiv

/-- The coordinate entries of the first derivative of a chart transition. -/
def transitionDeriv (β α : M) (a i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (Module.finBasis ℝ E).coord a
    (fderiv ℝ (chartTransition (I := I) β α) y ((Module.finBasis ℝ E) i))

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- **Math.** Unfolding the first transition derivative exposes its coordinate definition. -/
@[simp] lemma transitionDeriv_def (β α : M) (a i : Fin (Module.finrank ℝ E)) (y : E) :
    transitionDeriv (I := I) β α a i y
      = (Module.finBasis ℝ E).coord a
          (fderiv ℝ (chartTransition (I := I) β α) y ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** `B^a_{ki}(y)`: the second-derivative coefficient of the transition —
classically `∂²x^a/∂y^k∂y^i`. -/
def transitionSndDeriv (β α : M) (a k i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (Module.finBasis ℝ E).coord a
    (fderiv ℝ (fderiv ℝ (chartTransition (I := I) β α)) y ((Module.finBasis ℝ E) k)
      ((Module.finBasis ℝ E) i))

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- **Math.** Unfolding the second transition derivative exposes its coordinate definition. -/
@[simp] lemma transitionSndDeriv_def (β α : M)
    (a k i : Fin (Module.finrank ℝ E)) (y : E) :
    transitionSndDeriv (I := I) β α a k i y
      = (Module.finBasis ℝ E).coord a
          (fderiv ℝ (fderiv ℝ (chartTransition (I := I) β α)) y
            ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** **Schwarz symmetry** of the transition second derivative in the two
differentiation directions: `∂²x^a/∂y^k∂y^i = ∂²x^a/∂y^i∂y^k` on the overlap. -/
lemma transitionSndDeriv_symm {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α)
    (a k i : Fin (Module.finrank ℝ E)) :
    transitionSndDeriv (I := I) β α a k i y
      = transitionSndDeriv (I := I) β α a i k y := by
  have hsymm : IsSymmSndFDerivAt ℝ (chartTransition (I := I) β α) y := by
    refine (contDiffAt_chartTransition (I := I) hy).isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  rw [transitionSndDeriv_def, transitionSndDeriv_def, hsymm.eq]

omit [FiniteDimensional ℝ E] in
/-- **Math.** The moving transition derivative `y ↦ Dτ(y)` is differentiable on the
overlap (as a map into continuous linear maps), with derivative the second
derivative of the transition. -/
lemma hasFDerivAt_fderiv_chartTransition {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α) :
    HasFDerivAt (fderiv ℝ (chartTransition (I := I) β α))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) β α)) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (chartTransition (I := I) β α)) y := by
    refine (contDiffAt_chartTransition (I := I) hy).fderiv_right ?_
    exact WithTop.coe_le_coe.2 le_top
  exact (h1.differentiableAt one_ne_zero).hasFDerivAt

/-- **Math.** The matrix-entry function `A^a_i` is differentiable on the overlap,
with partial derivatives the second-derivative coefficients `B^a_{ki}`. -/
lemma hasFDerivAt_transitionDeriv {β α : M} {y : E}
    (hy : y ∈ chartTransitionSource (I := I) (M := M) β α)
    (a i : Fin (Module.finrank ℝ E)) :
    HasFDerivAt (transitionDeriv (I := I) β α a i)
      (((Module.finBasis ℝ E).coord a).toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
          (fderiv ℝ (fderiv ℝ (chartTransition (I := I) β α)) y))) y := by
  have h2 := hasFDerivAt_fderiv_chartTransition (I := I) hy
  have h3 := ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).hasFDerivAt.comp
    y h2)
  exact ((Module.finBasis ℝ E).coord a).toContinuousLinearMap.hasFDerivAt.comp y h3

end Transition

end TauCeti.Manifold

end
