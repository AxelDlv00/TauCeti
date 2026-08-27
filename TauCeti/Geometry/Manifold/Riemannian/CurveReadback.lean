/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ChartMetric
public import TauCeti.Geometry.Manifold.Riemannian.PathELength

/-!
# Reading a curve through one chart

This module supplies the first-order chart transfer and path-length bridge used by the Layer 0
chart-polygon argument.  It follows the declarations
`hasMFDerivAt_of_hasDerivAt_extChartAt`, `mfderiv_eq_of_hasDerivAt_extChartAt`,
`enorm_mfderiv_eq_of_hasDerivAt_extChartAt`, `contDiffOn_extChartAt_comp`, and
`pathELength_eq_ofReal_integral_chartMetricInner` in
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/CurveReadback.lean` from the read-only
Poincare-Conjecture source at revision `24f32e4d600878bfaac6bc2f2f9324175571c321`
(`[poincareConjectureDoCarmo]`), while using the canonical `RiemannianBundle` and
`Manifold.pathELength` APIs already present in Tau Ceti.

The chart-source hypotheses are intentional: extended-chart values and tangent coordinate changes
are junk outside their natural domains.  The length identity is the coordinate form of do Carmo,
Chapter 3, Definition 3.1 and Chapter 7, Definition 2.4 (`[doCarmo1992]`).  Exact corner
smoothing and lower-semicontinuity remain outside this Layer 0 slice.
-/

@[expose] public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
/-- Transfer a derivative of a curve read in the chart at `α` to a manifold derivative at the
current point of the curve. -/
theorem hasMFDerivAt_of_hasDerivAt_extChartAt {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tangentCoordChange I α (γ t) (γ t) ξ)) := by
  have hα : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hsrc
  have hself : γ t ∈ (extChartAt I (γ t)).source := mem_extChartAt_source (γ t)
  have htrans : HasFDerivAt (extChartAt I (γ t) ∘ (extChartAt I α).symm)
      (tangentCoordChange I α (γ t) (γ t)) (extChartAt I α (γ t)) := by
    have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hα, hself⟩
    rw [I.range_eq_univ] at hw
    exact hasFDerivWithinAt_univ.mp hw
  have hcomp := htrans.comp_hasDerivAt t hd
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source :=
    hcont.preimage_mem_nhds ((isOpen_extChartAt_source α).mem_nhds hα)
  have hread : HasDerivAt (fun s => extChartAt I (γ t) (γ s))
      (tangentCoordChange I α (γ t) (γ t) ξ) t := by
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    change extChartAt I (γ t) (γ s) =
      (extChartAt I (γ t) ∘ (extChartAt I α).symm) (extChartAt I α (γ s))
    simp only [Function.comp_apply, (extChartAt I α).left_inv hs]
  refine ⟨hcont, ?_⟩
  have hf : HasFDerivAt (fun s => extChartAt I (γ t) (γ s))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tangentCoordChange I α (γ t) (γ t) ξ)) t := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    exact hread.hasFDerivAt
  rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
  exact hf.hasFDerivWithinAt

omit [FiniteDimensional ℝ E] in
/-- Value form of `hasMFDerivAt_of_hasDerivAt_extChartAt`. -/
theorem mfderiv_eq_of_hasDerivAt_extChartAt {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    mfderiv 𝓘(ℝ, ℝ) I γ t 1 = tangentCoordChange I α (γ t) (γ t) ξ := by
  rw [(hasMFDerivAt_of_hasDerivAt_extChartAt hcont hsrc hd).mfderiv]
  exact one_smul ℝ _

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The fibre enorm of the intrinsic velocity is the chart-Gram norm of the coordinate velocity. -/
theorem enorm_mfderiv_eq_of_hasDerivAt_extChartAt {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ =
      ENNReal.ofReal (Real.sqrt
        (chartMetricInner (I := I) α (extChartAt I α (γ t)) ξ ξ)) := by
  rw [mfderiv_eq_of_hasDerivAt_extChartAt hcont hsrc hd]
  have hcoord :=
    Riemannian.trivializationAt_symm_eq_tangentCoordChange (I := I) α hsrc ξ
  have hinner := chartMetricInner_eq_inner_at_target (I := I) α
    ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc)) ξ ξ
  have hvec : (tangentCoordChange I α (γ t) (γ t) ξ : TangentSpace I (γ t)) =
      (trivializationAt E (TangentSpace I) α).symm (γ t) ξ := hcoord.symm
  rw [hvec]
  rw [hinner]
  rw [(extChartAt I α).left_inv (by
    rw [extChartAt_source]
    exact hsrc)]
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]

omit [FiniteDimensional ℝ E] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The chart reading of a `C¹` curve is a `C¹` model-space curve on any set mapped into the chart
source. -/
theorem contDiffOn_extChartAt_comp {γ : ℝ → M} {s : Set ℝ} {α : M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hsrc : ∀ t ∈ s, γ t ∈ (chartAt H α).source) :
    ContDiffOn ℝ 1 (fun t => extChartAt I α (γ t)) s := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiffOn_extChartAt (n := 1)).comp hγ fun t ht => hsrc t ht

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Length bridge.**  On a fixed chart source, `pathELength` is the integral of the chart-Gram
norm of the within derivative of the chart reading.  This adapts
`pathELength_eq_ofReal_integral_chartMetricInner` in
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/CurveReadback.lean`, revision
`24f32e4d600878bfaac6bc2f2f9324175571c321` (`[poincareConjectureDoCarmo]`). -/
theorem pathELength_eq_ofReal_integral_chartMetricInner {γ : ℝ → M} {a b : ℝ} {α : M}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source) :
    Manifold.pathELength I γ a b =
      ENNReal.ofReal (∫ t in a..b, Real.sqrt
        (chartMetricInner (I := I) α (extChartAt I α (γ t))
          (derivWithin (fun s => extChartAt I α (γ s)) (Icc a b) t)
          (derivWithin (fun s => extChartAt I α (γ s)) (Icc a b) t))) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [Manifold.pathELength_self]
  set u : ℝ → E := fun s => extChartAt I α (γ s) with hu_def
  set u' : ℝ → E := derivWithin u (Icc a b) with hu'_def
  have huC1 : ContDiffOn ℝ 1 u (Icc a b) := contDiffOn_extChartAt_comp hγ hsrc
  have hu'cont : ContinuousOn u' (Icc a b) :=
    huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hu'deriv : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t := by
    intro t ht
    have h1 : HasDerivWithinAt u (u' t) (Icc a b) t :=
      (huC1.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    exact h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hint_cont : ContinuousOn
      (fun t => Real.sqrt (chartMetricInner (I := I) α (u t) (u' t) (u' t)))
      (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn
      (continuousOn_chartMetricInner_along (I := I) α huC1.continuousOn hu'cont hu'cont
        (fun t ht => htgt t ht))
  have hint : IntegrableOn
      (fun t => Real.sqrt (chartMetricInner (I := I) α (u t) (u' t) (u' t)))
      (Ioo a b) := (hint_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpt : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ =
      ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) α (u t) (u' t) (u' t))) := by
    intro t ht
    exact enorm_mfderiv_eq_of_hasDerivAt_extChartAt
      (I := I) (hγ.continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2))
      (hsrc t (Ioo_subset_Icc_self ht)) (hu'deriv t ht)
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    setLIntegral_congr_fun measurableSet_Ioo hpt,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (MeasureTheory.ae_of_all _ fun t => Real.sqrt_nonneg _)]

end Geodesic
end Riemannian
