/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Change of chart for tangent frames and Gram matrices

This file ports the zeroth-order chart bridge used in the geodesic development.  Over a chart
source, the inverse tangent trivialization expands in the canonical local frame; the same
readback is the tangent coordinate change, and the Gram coefficients therefore obey the usual
change-of-frame formula.  The source architecture is retained while its explicit metric and
custom frame are replaced by Mathlib's canonical `Bundle.RiemannianBundle` and
`Riemannian.Tensor.chartLocalFrame` APIs.

The identities are adapted from the Apache-2.0 Poincare-Conjecture source file cited below.
Their geometric meaning is the coordinate-frame calculus used for covariant differentiation and
metric compatibility in do Carmo. Metric/norm and length bridges from that source belong to the
Layer 0 metric reconciliation and are intentionally not included here.

The chart-source hypotheses in every statement are essential: outside a source, the tangent
coordinate changes and local-frame sections have junk values, so no global chart identity is
asserted.

## References

* [doCarmo1992], Chapter 2, Section 2, Proposition 2.2 (coordinate-frame expansion for covariant
  differentiation), and Section 3, Proposition 3.2 (metric compatibility in coordinate
  coefficients).
* [poincareConjectureDoCarmo],
  `DoCarmoLib/Riemannian/Geodesic/HopfRinow/MetricBridge.lean`, declarations
  `trivializationAt_symm_eq_sum_chartBasisVecFiber`,
  `trivializationAt_symm_eq_tangentCoordChange`,
  `chartBasisVecFiber_eq_symm_tangentCoordChange`, and `chartGramMatrix_change`, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open Bundle FiberBundle Manifold Set
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace Riemannian

open Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section ChartFrame

variable [FiniteDimensional ℝ E]

/-- The inverse tangent trivialization expands in the canonical chart-local frame. This adapts the
source `trivializationAt_symm_eq_sum_chartBasisVecFiber`, with `chartLocalFrame` as the current
canonical frame API.  The coefficients are the coordinates in `Module.finBasis ℝ E`, and the
chart-source hypothesis is required for the readback to be meaningful. This is the coordinate-frame
expansion used in Chapter 2, Section 2, Proposition 2.2 of [doCarmo1992]. It ports the
`trivializationAt_symm_eq_sum_chartBasisVecFiber` declaration of [poincareConjectureDoCarmo],
revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. -/
theorem trivializationAt_symm_eq_sum_chartLocalFrame (α : M) (b : M) (a : E)
    (hb : b ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).symm b a
      = ∑ i, (Module.finBasis ℝ E).repr a i • chartLocalFrame (I := I) α i b := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hb']
  conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change ((Module.finBasis ℝ E).repr a) i •
      (Bundle.Trivialization.symmₗ ℝ (trivializationAt E (TangentSpace I) α) b)
        ((Module.finBasis ℝ E) i)
    = ((Module.finBasis ℝ E).repr a) i • chartLocalFrame (I := I) α i b
  rw [Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hb']
  rw [chartLocalFrame_apply_of_mem_chart_source (I := I) α hb i]
  rfl

end ChartFrame

/-- The inverse tangent trivialization is the tangent coordinate change at a foot in the chart
source.  This is the source `trivializationAt_symm_eq_tangentCoordChange`; no metric or
positive-dimensionality hypothesis is needed. It is the coordinate readback underlying Chapter 2,
Section 2, Proposition 2.2 of [doCarmo1992], and ports the
`trivializationAt_symm_eq_tangentCoordChange` declaration of [poincareConjectureDoCarmo], revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. -/
theorem trivializationAt_symm_eq_tangentCoordChange (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm b a = tangentCoordChange I α b b a := by
  have h := TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := α) (b := b) hb
  have hb' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hb' a]
  exact congrArg (fun f ↦ f a) h

section ChartFrame

variable [FiniteDimensional ℝ E]

/-- At a common foot in two chart sources, the `β` chart-local frame vector is the `α`
readback of the tangent coordinate change from `β` to `α`. This is the frame-transition identity
underlying Chapter 2, Section 2,
Proposition 2.2 of [doCarmo1992], and ports the
`chartBasisVecFiber_eq_symm_tangentCoordChange` declaration of [poincareConjectureDoCarmo], revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. -/
theorem chartLocalFrame_eq_symm_tangentCoordChange (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartLocalFrame (I := I) β i x
      = (trivializationAt E (TangentSpace I) α).symm x
          (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) := by
  have hα : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hxα
  have hβ : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact hxβ
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hframe :
      chartLocalFrame (I := I) β i x
        = (trivializationAt E (TangentSpace I) β).symm x ((Module.finBasis ℝ E) i) := by
    rw [chartLocalFrame_apply_of_mem_chart_source (I := I) β hxβ i]
    rfl
  rw [hframe,
    trivializationAt_symm_eq_tangentCoordChange β hxβ ((Module.finBasis ℝ E) i),
    trivializationAt_symm_eq_tangentCoordChange α hxα
      (tangentCoordChange I β α x ((Module.finBasis ℝ E) i))]
  exact (tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hx⟩).symm

end ChartFrame

section Gram

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Gram matrix transforms as a `(0,2)` tensor under a change of chart.  At a foot in the
overlap, the `β` entry is the finite double sum of the `α` entries and the two tangent-coordinate
change coefficients.  The proof factors through the intrinsic fibre inner product via the frame
comparison above. This is the coordinate metric-coefficient calculus used in Chapter 2, Section 3,
Proposition 3.2 of [doCarmo1992], and ports the `chartGramMatrix_change` declaration of
[poincareConjectureDoCarmo], revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. -/
theorem chartGramMatrix_change (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) β x i j
      = ∑ a, ∑ b, chartGramMatrix (I := I) α x a b
          * (Module.finBasis ℝ E).repr
              (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) a
          * (Module.finBasis ℝ E).repr
              (tangentCoordChange I β α x ((Module.finBasis ℝ E) j)) b := by
  rw [chartGramMatrix_apply (I := I) β x i j,
    chartLocalFrame_eq_symm_tangentCoordChange (I := I) α β hxα hxβ i,
    chartLocalFrame_eq_symm_tangentCoordChange (I := I) α β hxα hxβ j]
  rw [trivializationAt_symm_eq_sum_chartLocalFrame (I := I) α x _ hxα,
    trivializationAt_symm_eq_sum_chartLocalFrame (I := I) α x _ hxα]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  simp_rw [chartGramMatrix_apply (I := I) α x]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  ring

end Gram

end Riemannian

end
