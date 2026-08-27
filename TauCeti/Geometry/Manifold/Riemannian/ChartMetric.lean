/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.MetricBridge

/-!
# Chart-Gram quadratic forms for the Riemannian bundle

The chart-polygon comparison reads the canonical fibre metric in one extended chart.  This module
packages that reading as a quadratic form and records the elementary positivity and continuity
facts used by the local comparison argument.  It is an adaptation of the chart metric bridge and
Gram-bound portions of the Apache-2.0 Poincare-Conjecture source at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`.

The public declarations use the current `Bundle.RiemannianBundle` instance directly; no separate
metric or length structure is introduced.  The coercivity argument follows
`exists_sq_norm_le_chartMetricInner` in
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/GramBound.lean` from
`[poincareConjectureDoCarmo]` at the revision above.  The coordinate-frame expansion is the one
used in do Carmo, Chapter 2, Section 2, Proposition 2.2 (`[doCarmo1992]`); together with the
piecewise-curve convention of Chapter 3, Definition 3.1 it supports Chapter 7, Definition 2.4
and the `HopfRinow` roadmap Layer 0 node.
-/

@[expose] public section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A chart Gram entry pulled back to the model space through the extended-chart inverse. -/
def chartGramOnE (α : M) (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y ↦ chartGramMatrix (I := I) α ((extChartAt I α).symm y) i j

/-- Unfold the coordinate pullback of a chart Gram entry. -/
@[simp]
theorem chartGramOnE_def (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) α i j y =
      chartGramMatrix (I := I) α ((extChartAt I α).symm y) i j :=
  rfl

/-- Symmetry of the chart Gram entries pulled back to the model space. -/
theorem chartGramOnE_symm (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) α i j y = chartGramOnE (I := I) α j i y := by
  rw [chartGramOnE_def, chartGramOnE_def, chartGramMatrix_apply, chartGramMatrix_apply]
  exact real_inner_comm _ _

section SmoothGram

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A chart Gram entry pulled back to the model space is smooth on the extended-chart target. -/
theorem chartGramOnE_contDiffOn (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) α i j) (extChartAt I α).target := by
  let _ : IsManifold I (∞ + 1 : ℕ∞ω) M := IsManifold.of_le (n := ∞)
    (by exact_mod_cast le_top)
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M ↦ chartGramMatrix (I := I) α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    contMDiffOn_chartGramMatrix_entry (I := I) α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source] at hsource
    rw [TangentBundle.trivializationAt_baseSet]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M ↦ chartGramMatrix (I := I) α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

end SmoothGram

/-- The `i`th coordinate of a model-space vector in Mathlib's canonical finite basis. -/
def chartCoord (i : Fin (Module.finrank ℝ E)) (a : E) : ℝ :=
  (Module.finBasis ℝ E).repr a i

/-- The continuous linear functional extracting one coordinate in `Module.finBasis`. -/
noncomputable def chartCoordFunctional (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  { (Finsupp.lapply i).comp (Module.finBasis ℝ E).repr.toLinearMap with
    cont := LinearMap.continuous_of_finiteDimensional _ }

/-- Reading a coordinate through `chartCoordFunctional` agrees with `chartCoord`. -/
@[simp]
theorem chartCoordFunctional_apply (i : Fin (Module.finrank ℝ E)) (a : E) :
    chartCoordFunctional (E := E) i a = chartCoord i a :=
  rfl

/-- The finite Gram expression for the fibre inner product read in the `α` extended chart at
coordinate `y`.  On `(extChartAt I α).target` it agrees with the intrinsic fibre inner product;
outside that target it is only the total finite expression, using the extended chart's junk values.
The Gram entries come from the canonical `RiemannianBundle` instance, so this is only a coordinate
presentation of the existing metric, not a second metric structure. -/
def chartMetricInner (α : M) (y a b : E) : ℝ :=
  ∑ i, ∑ j, chartGramOnE (I := I) α i j y * chartCoord i a * chartCoord j b

/-- The chart-Gram form vanishes when its left vector is zero. -/
@[simp]
theorem chartMetricInner_zero_left (α : M) (y b : E) :
    chartMetricInner (I := I) α y 0 b = 0 := by
  simp [chartMetricInner, chartCoord]

/-- The chart-Gram form vanishes when its right vector is zero. -/
@[simp]
theorem chartMetricInner_zero_right (α : M) (y a : E) :
    chartMetricInner (I := I) α y a 0 = 0 := by
  simp [chartMetricInner, chartCoord]

/-- The chart-Gram form is additive in its left vector. -/
theorem chartMetricInner_add_left (α : M) (y a a' b : E) :
    chartMetricInner (I := I) α y (a + a') b =
      chartMetricInner (I := I) α y a b + chartMetricInner (I := I) α y a' b := by
  simp only [chartMetricInner, chartCoord, map_add, Finsupp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The chart-Gram form is additive in its right vector. -/
theorem chartMetricInner_add_right (α : M) (y a b b' : E) :
    chartMetricInner (I := I) α y a (b + b') =
      chartMetricInner (I := I) α y a b + chartMetricInner (I := I) α y a b' := by
  simp only [chartMetricInner, chartCoord, map_add, Finsupp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The chart-Gram form is homogeneous in its left vector. -/
theorem chartMetricInner_smul_left (α : M) (y : E) (r : ℝ) (a b : E) :
    chartMetricInner (I := I) α y (r • a) b =
      r * chartMetricInner (I := I) α y a b := by
  simp only [chartMetricInner, chartCoord]
  simp_rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ = ∑ i, ∑ j, r * (chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, r * (∑ j, chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = r * ∑ i, ∑ j, chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j := by
      rw [Finset.mul_sum]

/-- The chart-Gram form is homogeneous in its right vector. -/
theorem chartMetricInner_smul_right (α : M) (y : E) (r : ℝ) (a b : E) :
    chartMetricInner (I := I) α y a (r • b) =
      r * chartMetricInner (I := I) α y a b := by
  simp only [chartMetricInner, chartCoord]
  simp_rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ = ∑ i, ∑ j, r * (chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, r * (∑ j, chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = r * ∑ i, ∑ j, chartGramOnE (I := I) α i j y *
        (Module.finBasis ℝ E).repr a i * (Module.finBasis ℝ E).repr b j := by
      rw [Finset.mul_sum]

/-- The chart-Gram form is symmetric in its vector arguments. -/
theorem chartMetricInner_symm (α : M) (y a b : E) :
    chartMetricInner (I := I) α y a b = chartMetricInner (I := I) α y b a := by
  unfold chartMetricInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [chartGramOnE_symm (I := I)]
  ring

/-- On an extended-chart target, `chartMetricInner` is the fibre inner product of the two
coordinate readbacks.  This is the bridge from the finite Gram presentation to the intrinsic
Riemannian norm used by `Manifold.pathELength`. -/
theorem chartMetricInner_eq_inner_at_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (a b : E) :
    chartMetricInner (I := I) α y a b =
      @inner ℝ (TangentSpace I ((extChartAt I α).symm y)) _
        ((trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) a)
        ((trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) b) := by
  have hsource : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hsource' : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source] at hsource'
    exact hsource'
  rw [chartMetricInner]
  rw [Riemannian.trivializationAt_symm_eq_sum_chartLocalFrame
    (I := I) α ((extChartAt I α).symm y) a hsource]
  rw [Riemannian.trivializationAt_symm_eq_sum_chartLocalFrame
    (I := I) α ((extChartAt I α).symm y) b hsource]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chartGramOnE_def, chartGramMatrix_apply]
  simp [chartCoord]
  ring

/-- The chart-Gram quadratic form is nonnegative on the extended-chart target. -/
theorem chartMetricInner_self_nonneg_of_mem_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (a : E) :
    0 ≤ chartMetricInner (I := I) α y a a := by
  rw [chartMetricInner_eq_inner_at_target (I := I) α hy]
  exact real_inner_self_nonneg

/-- At the chart center, the chart-Gram quadratic form is positive on nonzero coordinate vectors. -/
theorem chartMetricInner_self_pos_at_center (α : M) (a : E) (ha : a ≠ 0) :
    0 < chartMetricInner (I := I) α (extChartAt I α α) a a := by
  rw [chartMetricInner_eq_inner_at_target (I := I) α (mem_extChartAt_target α)]
  have hread : (trivializationAt E (TangentSpace I) α).symm α a = a := by
    rw [Riemannian.trivializationAt_symm_eq_tangentCoordChange (I := I) α
      (mem_chart_source H α) a]
    exact tangentCoordChange_self (I := I) (x := α) (z := α) (v := a)
      (mem_extChartAt_source α)
  rw [(extChartAt I α).left_inv (mem_extChartAt_source α)]
  rw [hread]
  exact real_inner_self_pos.mpr ha

/-! The next lemma is the finite-dimensional coercivity step in the source chart-polygon proof.
The public wrapper below additionally handles the zero-dimensional model space. -/

private theorem exists_sq_norm_le_chartMetricInner_of_nontrivial
    (α : M) [Nontrivial E]
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    ∃ (c : ℝ) (V : Set E), 0 < c ∧ V ∈ 𝓝 (extChartAt I α α) ∧
      V ⊆ (extChartAt I α).target ∧
      ∀ y ∈ V, ∀ u : E, ‖u‖ ^ 2 ≤ c * chartMetricInner (I := I) α y u u := by
  classical
  set y₀ : E := extChartAt I α α with hy₀
  have hy₀tgt : y₀ ∈ (extChartAt I α).target := by
    exact mem_extChartAt_target α
  have htargetOpen : IsOpen (extChartAt I α).target := isOpen_extChartAt_target α
  have hQ : ContinuousOn
      (fun z : E × E ↦ chartMetricInner (I := I) α z.1 z.2 z.2)
      ((extChartAt I α).target ×ˢ (Set.univ : Set E)) := by
    unfold chartMetricInner
    refine continuousOn_finsetSum Finset.univ ?_
    intro i hi
    refine continuousOn_finsetSum Finset.univ ?_
    intro j hj
    have hG : ContinuousOn
        (fun z : E × E ↦ chartGramOnE (I := I) α i j z.1)
        ((extChartAt I α).target ×ˢ (Set.univ : Set E)) := by
      have hG' := (chartGramOnE_contDiffOn (I := I) α i j).continuousOn
      exact hG'.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)
    have hci : Continuous (fun z : E × E ↦ chartCoord (E := E) i z.2) := by
      simpa only [Function.comp_def, chartCoordFunctional_apply] using
        (chartCoordFunctional (E := E) i).continuous.comp continuous_snd
    have hcj : Continuous (fun z : E × E ↦ chartCoord (E := E) j z.2) := by
      simpa only [Function.comp_def, chartCoordFunctional_apply] using
        (chartCoordFunctional (E := E) j).continuous.comp continuous_snd
    exact (hG.mul hci.continuousOn).mul hcj.continuousOn
  have hQ₀ : Continuous (fun u : E ↦ chartMetricInner (I := I) α y₀ u u) := by
    unfold chartMetricInner
    refine continuous_finsetSum Finset.univ ?_
    intro i hi
    refine continuous_finsetSum Finset.univ ?_
    intro j hj
    have hci : Continuous (fun u : E ↦ chartCoord (E := E) i u) := by
      change Continuous (chartCoordFunctional (E := E) i)
      exact (chartCoordFunctional (E := E) i).continuous
    have hcj : Continuous (fun u : E ↦ chartCoord (E := E) j u) := by
      change Continuous (chartCoordFunctional (E := E) j)
      exact (chartCoordFunctional (E := E) j).continuous
    exact (continuous_const.mul hci).mul hcj
  have hpos : ∀ u : E, u ≠ 0 → 0 < chartMetricInner (I := I) α y₀ u u := by
    intro u hu
    rw [hy₀]
    exact chartMetricInner_self_pos_at_center (I := I) α u hu
  have hsphereCompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere 0 1
  have hsphereNonempty : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u₀, hu₀sphere, hu₀min⟩ :=
    hsphereCompact.exists_isMinOn hsphereNonempty hQ₀.continuousOn
  set m : ℝ := chartMetricInner (I := I) α y₀ u₀ u₀ with hm
  have hu₀ne : u₀ ≠ 0 := by
    intro hu
    rw [mem_sphere_iff_norm, sub_zero, hu, norm_zero] at hu₀sphere
    norm_num at hu₀sphere
  have hmpos : 0 < m := hpos u₀ hu₀ne
  have hUopen : IsOpen
      (((extChartAt I α).target ×ˢ (Set.univ : Set E)) ∩
        (fun z : E × E ↦ chartMetricInner (I := I) α z.1 z.2 z.2) ⁻¹' Ioi (m / 2)) :=
    hQ.isOpen_inter_preimage (htargetOpen.prod isOpen_univ) isOpen_Ioi
  have hsub : ({y₀} : Set E) ×ˢ Metric.sphere (0 : E) 1 ⊆
      ((extChartAt I α).target ×ˢ (Set.univ : Set E)) ∩
        (fun z : E × E ↦ chartMetricInner (I := I) α z.1 z.2 z.2) ⁻¹' Ioi (m / 2) := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    change y ∈ ({y₀} : Set E) at hy
    rw [mem_singleton_iff] at hy
    rw [hy]
    refine ⟨⟨hy₀tgt, mem_univ _⟩, ?_⟩
    have hmin : m ≤ chartMetricInner (I := I) α y₀ u u := hu₀min hu
    have hhalf : m / 2 < m := by linarith
    exact hhalf.trans_le hmin
  obtain ⟨U, W, hUopen, hWopen, hUsub, hWsub, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hsphereCompact hUopen hsub
  refine ⟨2 / m, U ∩ (extChartAt I α).target,
    div_pos two_pos hmpos,
    Filter.inter_mem (hUopen.mem_nhds (hUsub (mem_singleton y₀)))
      (htargetOpen.mem_nhds hy₀tgt),
    inter_subset_right, ?_⟩
  intro y hy u
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnuPos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have huSphere : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hnu]
  have hmem : ((y, ‖u‖⁻¹ • u) : E × E) ∈ U ×ˢ W :=
    ⟨hy.1, hWsub huSphere⟩
  have hgt : m / 2 < chartMetricInner (I := I) α y (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) :=
    (hUW hmem).2
  have hexp : chartMetricInner (I := I) α y (‖u‖⁻¹ • u) (‖u‖⁻¹ • u) =
      ‖u‖⁻¹ * (‖u‖⁻¹ * chartMetricInner (I := I) α y u u) := by
    rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
  rw [hexp] at hgt
  have hkey : ‖u‖ ^ 2 * (m / 2) < chartMetricInner (I := I) α y u u := by
    have h2 := mul_lt_mul_of_pos_left hgt (pow_pos hnuPos 2)
    calc
      ‖u‖ ^ 2 * (m / 2) <
          ‖u‖ ^ 2 * (‖u‖⁻¹ * (‖u‖⁻¹ * chartMetricInner (I := I) α y u u)) := h2
      _ = (‖u‖ * ‖u‖⁻¹) * ((‖u‖ * ‖u‖⁻¹) *
          chartMetricInner (I := I) α y u u) := by ring
      _ = chartMetricInner (I := I) α y u u := by
        rw [mul_inv_cancel₀ hnu, one_mul, one_mul]
  rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
  linarith [hkey]

/-- A finite-dimensional chart-Gram form dominates the squared model-space norm on a
neighbourhood of the chart centre.  This is the local coercivity input to
`Riemannian.exists_piecewiseSmooth_pathELength_le`, adapting
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/GramBound.lean` at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321` (`[poincareConjectureDoCarmo]`).  The
zero-dimensional case is included, so the public approximation theorem has no artificial
positive-dimension assumption. -/
theorem exists_sq_norm_le_chartMetricInner (α : M) [I.Boundaryless]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    ∃ (c : ℝ) (V : Set E), 0 < c ∧ V ∈ 𝓝 (extChartAt I α α) ∧
      V ⊆ (extChartAt I α).target ∧
      ∀ y ∈ V, ∀ u : E, ‖u‖ ^ 2 ≤ c * chartMetricInner (I := I) α y u u := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have hzero : ∀ u : E, u = 0 :=
      (finrank_zero_iff_forall_zero (K := ℝ) (V := E)).mp hdim
    refine ⟨1, (extChartAt I α).target, zero_lt_one,
      (isOpen_extChartAt_target α).mem_nhds (mem_extChartAt_target α), subset_rfl, ?_⟩
    intro y hy u
    rw [hzero u]
    simp
  · let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero hdim)
    exact exists_sq_norm_le_chartMetricInner_of_nontrivial (I := I) α

section Smooth

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The chart-Gram quadratic form is continuous on the chart target when its vector arguments are
continuous. -/
theorem continuousOn_chartMetricInner (α : M) {s : Set E} {u v : E → E}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s)
  (hs : s ⊆ (extChartAt I α).target) :
    ContinuousOn (fun y ↦ chartMetricInner (I := I) α y (u y) (v y)) s := by
  have hcoord (i : Fin (Module.finrank ℝ E)) : Continuous (chartCoord (E := E) i) := by
    let f : E →ₗ[ℝ] ℝ := (Finsupp.lapply i).comp (Module.finBasis ℝ E).repr.toLinearMap
    have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
    rw [show chartCoord (E := E) i = f from by
      funext a
      rfl]
    exact hf
  unfold chartMetricInner
  refine continuousOn_finsetSum Finset.univ ?_
  intro i hi
  refine continuousOn_finsetSum Finset.univ ?_
  intro j hj
  have hG := (chartGramOnE_contDiffOn (I := I) α i j).continuousOn.mono hs
  have hui : ContinuousOn (fun y ↦ chartCoord (E := E) i (u y)) s := by
    simpa [Function.comp_def] using (hcoord i).comp_continuousOn hu
  have hvj : ContinuousOn (fun y ↦ chartCoord (E := E) j (v y)) s := by
    simpa [Function.comp_def] using (hcoord j).comp_continuousOn hv
  have hterm := (hG.mul hui).mul hvj
  exact hterm.congr fun y hy => by rfl

/-- The same continuity statement when the base coordinate and both vector arguments are read
along a parameter set.  This form is the one used by the path-length bridge. -/
theorem continuousOn_chartMetricInner_along (α : M) {s : Set ℝ}
    {u v w : ℝ → E} (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (hw : ContinuousOn w s) (hs : ∀ t ∈ s, u t ∈ (extChartAt I α).target) :
    ContinuousOn (fun t ↦ chartMetricInner (I := I) α (u t) (v t) (w t)) s := by
  have hcoord (i : Fin (Module.finrank ℝ E)) : Continuous (chartCoord (E := E) i) := by
    let f : E →ₗ[ℝ] ℝ := (Finsupp.lapply i).comp (Module.finBasis ℝ E).repr.toLinearMap
    have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
    rw [show chartCoord (E := E) i = f from by
      funext a
      rfl]
    exact hf
  unfold chartMetricInner
  refine continuousOn_finsetSum Finset.univ ?_
  intro i hi
  refine continuousOn_finsetSum Finset.univ ?_
  intro j hj
  have hG := (chartGramOnE_contDiffOn (I := I) α i j).continuousOn.comp hu
    (fun t ht ↦ hs t ht)
  have hvi : ContinuousOn (fun t ↦ chartCoord (E := E) i (v t)) s := by
    simpa [Function.comp_def] using (hcoord i).comp_continuousOn hv
  have hwj : ContinuousOn (fun t ↦ chartCoord (E := E) j (w t)) s := by
    simpa [Function.comp_def] using (hcoord j).comp_continuousOn hw
  have hterm := (hG.mul hvi).mul hwj
  exact hterm.congr fun t ht ↦ by rfl

end Smooth

end Riemannian
