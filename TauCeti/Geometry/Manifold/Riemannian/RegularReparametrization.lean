/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Geometry.Manifold.Riemannian.RiemannianSpeed

/-!
# Regular C¹ curves admit unit-speed reparametrizations

This file proves the regular-reparametrization target in Layer 0 of the
Hopf--Rinow roadmap. A curve that is `C¹` and regular on a nondegenerate
compact interval has an arclength inverse on its full length interval. The
inverse is monotone, preserves both endpoints, gives unit speed, and preserves
Mathlib's canonical `Manifold.pathELength`.

The consumer-facing corollary rescales the arclength interval to `[0, 1]`,
where the resulting curve has constant speed equal to its total length.

## References

* Peter Petersen, *Riemannian Geometry* (3rd ed., 2016), Chapter 5, §5.3,
  Proposition `prop:pet-ch5-arclength-reparametrization`, formalized by
  `regularCurve_arclengthReparametrization` (with the supporting
  `contDiffAt_curveSpeedSq`) in
  `formalized-sources/Petersen/PetersenLib/Ch05/ArclengthReparametrization.lean`
  in `frenzymath/Poincare-Conjecture`, revision
  `e6bc8cb66a83e50afa2b4507db664c9370bd4ac4`. That source supplies the
  arclength/inverse and unit-speed architecture; its smooth squared-speed and
  private curve-length APIs are replaced here by the `C¹` and Mathlib APIs.
* The do Carmo formalization in `frenzymath/Poincare-Conjecture`,
  `DoCarmoLib/Riemannian/Manifold/DoCarmoCh3SegmentReparam.lean`, declarations
  `reparam`, `reparam_mem_Ioo`, and `hasDerivAt_reparam`, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`. This Apache-2.0 source supplies
  the domain-side open-window and inverse/segment architecture only: it has no
  regular arclength-reparametrization theorem, so that target is an explicit
  source gap rather than a copied declaration.
* Both cited formal source files are from the Apache-2.0-licensed
  `frenzymath/Poincare-Conjecture` repository; this module is an adaptation
  under that license.
-/

public section

open Bundle Filter Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti.Manifold

noncomputable section

/-- The ordinary inverse of a globally injective function agrees locally with
the inverse supplied by the one-dimensional inverse function theorem. -/
private theorem hasDerivAt_invFun_of_hasStrictDerivAt
    {phi : ℝ → ℝ} {d t : ℝ} (hphi : HasStrictDerivAt phi d t)
    (hd : d ≠ 0) (hinj : Function.Injective phi) :
    HasDerivAt (Function.invFun phi) d⁻¹ (phi t) ∧
      Set.range phi ∈ 𝓝 (phi t) := by
  let zeta : ℝ → ℝ := hphi.localInverse phi _ t hd
  have hzeta : HasStrictDerivAt zeta d⁻¹ (phi t) :=
    hphi.to_localInverse hd
  have heq : Function.invFun phi =ᶠ[𝓝 (phi t)] zeta := by
    filter_upwards [hphi.eventually_right_inverse hd] with s hs
    apply hinj
    exact (Function.invFun_eq ⟨zeta s, hs⟩).trans hs.symm
  refine ⟨hzeta.hasDerivAt.congr_of_eventuallyEq heq, ?_⟩
  rw [← hphi.map_nhds_eq hd]
  exact mem_map.mpr (Eventually.of_forall fun x ↦ ⟨x, rfl⟩)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A regular `C¹` curve on `[a, b]` admits a `C¹` unit-speed
reparametrization on its arclength interval `[0, L]`.

The length `L`, both endpoint identities, monotonicity of the inverse, the two
inverse identities, and the canonical `pathELength` characterizations are all
part of the public conclusion. -/
theorem exists_unit_speed_reparametrization_of_regular {gamma : ℝ → M}
    {a b : ℝ} (hab : a < b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hreg : ∀ t ∈ Icc a b, riemannianSpeed I gamma t ≠ 0) :
    ∃ L : ℝ, ∃ psi : ℝ → ℝ,
      L = ∫ t in a..b, riemannianSpeed I gamma t ∧
      0 < L ∧
      MapsTo psi (Icc 0 L) (Icc a b) ∧
      MonotoneOn psi (Icc 0 L) ∧
      psi 0 = a ∧
      psi L = b ∧
      (∀ t ∈ Icc a b,
        psi (∫ s in a..t, riemannianSpeed I gamma s) = t) ∧
      (∀ s ∈ Icc 0 L,
        ∫ t in a..psi s, riemannianSpeed I gamma t = s) ∧
      ContDiffOn ℝ 1 psi (Icc 0 L) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, riemannianSpeed I (gamma ∘ psi) s = 1) ∧
      (gamma ∘ psi) 0 = gamma a ∧
      (gamma ∘ psi) L = gamma b ∧
      pathELength I gamma a b = ENNReal.ofReal L ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
        pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s)) ∧
      pathELength I (gamma ∘ psi) 0 L = pathELength I gamma a b := by
  have hmdiff : ∀ t ∈ Icc a b, MDiffAt gamma t := by
    intro t ht
    by_contra hnot
    apply hreg t ht
    rw [riemannianSpeed_eq_zero]
    simp [mfderiv_zero_of_not_mdifferentiableAt hnot]
  have hspeed_cont : ContinuousOn (riemannianSpeed I gamma) (Icc a b) :=
    continuousOn_riemannianSpeed I hgamma hmdiff
      (uniqueDiffOn_Icc hab).uniqueMDiffOn
  let p : ℝ → Icc a b := projIcc a b hab.le
  let v : ℝ → ℝ :=
    (Icc a b).domRestrict (riemannianSpeed I gamma) ∘ p
  have hv_cont : Continuous v := by
    have hp : Continuous p := continuous_projIcc
    exact hspeed_cont.domRestrict.comp hp
  have hv_eq : ∀ t ∈ Icc a b, v t = riemannianSpeed I gamma t := by
    intro t ht
    simp only [v, p, Function.comp_apply, Set.domRestrict_apply,
      projIcc_of_mem hab.le ht]
  have hv_pos : ∀ t, 0 < v t := by
    intro t
    have hne : riemannianSpeed I gamma (p t) ≠ 0 := hreg _ (p t).property
    simpa only [v, Function.comp_apply, Set.domRestrict_apply] using
      lt_of_le_of_ne (riemannianSpeed_nonneg I gamma (p t)) hne.symm
  let phi : ℝ → ℝ := fun t ↦ ∫ s in a..t, v s
  have hphi_strict : ∀ t, HasStrictDerivAt phi (v t) t := by
    intro t
    simpa only [phi] using hv_cont.integral_hasStrictDerivAt a t
  have hphi_add : ∀ s t, phi t = phi s + ∫ r in s..t, v r := by
    intro s t
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hv_cont.intervalIntegrable a s) (hv_cont.intervalIntegrable s t)
    simpa only [phi] using hadd.symm
  have hphi_mono : StrictMono phi := by
    intro s t hst
    have hpos : 0 < ∫ r in s..t, v r :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (hv_cont.intervalIntegrable s t) (fun r _ ↦ hv_pos r) hst
    rw [hphi_add s t]
    linarith
  have hphi_cont : Continuous phi :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hphi_strict t).hasDerivAt.continuousAt
  have hphi_inj : Function.Injective phi := hphi_mono.injective
  let psi : ℝ → ℝ := Function.invFun phi
  have hleft : ∀ t, psi (phi t) = t :=
    Function.leftInverse_invFun hphi_inj
  let W : Set ℝ := Set.range phi
  have hpsi_deriv_local : ∀ t,
      HasDerivAt psi (v t)⁻¹ (phi t) ∧ W ∈ 𝓝 (phi t) := by
    intro t
    simpa only [psi, W] using hasDerivAt_invFun_of_hasStrictDerivAt
      (hphi_strict t) (hv_pos t).ne' hphi_inj
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro s ⟨t, rfl⟩
    exact (hpsi_deriv_local t).2
  have hright : ∀ s ∈ W, phi (psi s) = s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
  have hpsi_hasDeriv : ∀ s ∈ W, HasDerivAt psi (v (psi s))⁻¹ s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
    exact (hpsi_deriv_local t).1
  have hpsi_diff : DifferentiableOn ℝ psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).differentiableAt.differentiableWithinAt
  have hpsi_cont : ContinuousOn psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).continuousAt.continuousWithinAt
  have hpsi_deriv_eq : EqOn (deriv psi) (fun s ↦ (v (psi s))⁻¹) W :=
    fun s hs ↦ (hpsi_hasDeriv s hs).deriv
  have hpsi_C1 : ContDiffOn ℝ 1 psi W := by
    rw [contDiffOn_one_iff_derivWithin hW_open.uniqueDiffOn]
    refine ⟨hpsi_diff, ?_⟩
    have hc : ContinuousOn (fun s ↦ (v (psi s))⁻¹) W :=
      (hv_cont.comp_continuousOn hpsi_cont).inv₀ fun s _ ↦ (hv_pos (psi s)).ne'
    refine hc.congr fun s hs ↦ ?_
    rw [derivWithin_of_isOpen hW_open hs, hpsi_deriv_eq hs]
  let L : ℝ := ∫ t in a..b, riemannianSpeed I gamma t
  have hL_def : L = ∫ t in a..b, riemannianSpeed I gamma t := rfl
  have hphi_eq : ∀ t ∈ Icc a b,
      phi t = ∫ s in a..t, riemannianSpeed I gamma s := by
    intro t ht
    rw [show phi t = ∫ s in a..t, v s from rfl]
    refine intervalIntegral.integral_congr fun r hr ↦ hv_eq r ?_
    rw [uIcc_of_le ht.1] at hr
    exact ⟨hr.1, hr.2.trans ht.2⟩
  have hphi_a : phi a = 0 := by simp only [phi, intervalIntegral.integral_same]
  have hphi_b : phi b = L := by
    rw [hphi_eq b (right_mem_Icc.mpr hab.le), hL_def]
  have hL_pos : 0 < L := by
    have hlt := hphi_mono hab
    rwa [hphi_a, hphi_b] at hlt
  have himage : phi '' Icc a b = Icc 0 L := by
    rw [hphi_cont.continuousOn.image_Icc_of_monotoneOn hab.le
      (hphi_mono.monotone.monotoneOn (Icc a b)), hphi_a, hphi_b]
  have hIccW : Icc 0 L ⊆ W := by
    rw [← himage]
    rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩
  have hmaps : MapsTo psi (Icc 0 L) (Icc a b) := by
    intro s hs
    rw [← himage] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hleft t]
    exact ht
  have hpsi_mono : MonotoneOn psi (Icc 0 L) := by
    intro x hx y hy hxy
    rw [← himage] at hx hy
    obtain ⟨tx, htx, rfl⟩ := hx
    obtain ⟨ty, hty, rfl⟩ := hy
    rw [hleft tx, hleft ty]
    by_contra hnot
    exact (not_lt_of_ge hxy) (hphi_mono (lt_of_not_ge hnot))
  have hpsi_zero : psi 0 = a := by rw [← hphi_a, hleft a]
  have hpsi_L : psi L = b := by rw [← hphi_b, hleft b]
  have hleft_Icc : ∀ t ∈ Icc a b,
      psi (∫ s in a..t, riemannianSpeed I gamma s) = t := by
    intro t ht
    rw [← hphi_eq t ht, hleft t]
  have hright_Icc : ∀ s ∈ Icc 0 L,
      ∫ t in a..psi s, riemannianSpeed I gamma t = s := by
    intro s hs
    rw [← hphi_eq (psi s) (hmaps hs)]
    exact hright s (hIccW hs)
  have hpsi_C1_Icc : ContDiffOn ℝ 1 psi (Icc 0 L) := hpsi_C1.mono hIccW
  have hcomp_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) :=
    hgamma.comp hpsi_C1_Icc.contMDiffOn hmaps
  have hunitSpeed : ∀ s ∈ Icc 0 L,
      riemannianSpeed I (gamma ∘ psi) s = 1 := by
    intro s hs
    have hsW : s ∈ W := hIccW hs
    have hpsi_deriv := hpsi_hasDeriv s hsW
    rw [riemannianSpeed_comp I gamma psi s (hmdiff _ (hmaps hs))
      hpsi_deriv.differentiableAt, hpsi_deriv.deriv, hv_eq _ (hmaps hs)]
    have hpos : 0 < riemannianSpeed I gamma (psi s) := by
      exact lt_of_le_of_ne (riemannianSpeed_nonneg I gamma (psi s))
        (hreg _ (hmaps hs)).symm
    rw [abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  have horiginalLength : pathELength I gamma a b = ENNReal.ofReal L := by
    rw [pathELength_eq_ofReal_integral_riemannianSpeed I hab.le
      hspeed_cont.integrableOn_Icc]
  have hunitLength : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s) := by
    intro s hs t ht hst
    have hpsi_st : psi s ≤ psi t := hpsi_mono hs ht hst
    have htarget : Icc (psi s) (psi t) ⊆ Icc a b :=
      Icc_subset_Icc (hmaps hs).1 (hmaps ht).2
    have hcomp := pathELength_comp_of_monotoneOn (I := I) hst
      (hpsi_mono.mono (Icc_subset_Icc hs.1 ht.2))
      ((hpsi_C1_Icc.differentiableOn (by norm_num)).mono
        (Icc_subset_Icc hs.1 ht.2))
      ((hgamma.mdifferentiableOn (by norm_num)).mono htarget)
    have hint : MeasureTheory.IntegrableOn (riemannianSpeed I gamma)
        (Icc (psi s) (psi t)) :=
      (hspeed_cont.mono htarget).integrableOn_Icc
    rw [hcomp, pathELength_eq_ofReal_integral_riemannianSpeed I hpsi_st hint]
    congr 1
    have hadd := hphi_add (psi s) (psi t)
    rw [hright s (hIccW hs), hright t (hIccW ht)] at hadd
    calc
      ∫ r in psi s..psi t, riemannianSpeed I gamma r =
          ∫ r in psi s..psi t, v r := by
        refine intervalIntegral.integral_congr fun r hr ↦ (hv_eq r ?_).symm
        rw [uIcc_of_le hpsi_st] at hr
        exact htarget hr
      _ = t - s := by linarith
  have htotalLength :
      pathELength I (gamma ∘ psi) 0 L = pathELength I gamma a b := by
    have hlen := hunitLength 0 (left_mem_Icc.mpr hL_pos.le) L
      (right_mem_Icc.mpr hL_pos.le) hL_pos.le
    calc
      pathELength I (gamma ∘ psi) 0 L = ENNReal.ofReal L := by simpa using hlen
      _ = pathELength I gamma a b := horiginalLength.symm
  refine ⟨L, psi, hL_def, hL_pos, hmaps, hpsi_mono, hpsi_zero, hpsi_L,
    hleft_Icc, hright_Icc, hpsi_C1_Icc, hcomp_C1, hunitSpeed, ?_, ?_,
    horiginalLength, hunitLength, htotalLength⟩
  · simp only [Function.comp_apply, hpsi_zero]
  · simp only [Function.comp_apply, hpsi_L]

/-- A regular `C¹` curve on `[a, b]` admits a constant-speed
reparametrization on `[0, 1]`; its speed is its total length `L`. -/
theorem exists_constant_speed_reparametrization_of_regular {gamma : ℝ → M}
    {a b : ℝ} (hab : a < b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hreg : ∀ t ∈ Icc a b, riemannianSpeed I gamma t ≠ 0) :
    ∃ L : ℝ, ∃ theta : ℝ → ℝ,
      L = ∫ t in a..b, riemannianSpeed I gamma t ∧
      0 < L ∧
      MapsTo theta (Icc 0 1) (Icc a b) ∧
      MonotoneOn theta (Icc 0 1) ∧
      theta 0 = a ∧
      theta 1 = b ∧
      ContDiffOn ℝ 1 theta (Icc 0 1) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ theta) (Icc 0 1) ∧
      (∀ t ∈ Icc 0 1, riemannianSpeed I (gamma ∘ theta) t = L) ∧
      pathELength I (gamma ∘ theta) 0 1 = ENNReal.ofReal L ∧
      pathELength I (gamma ∘ theta) 0 1 = pathELength I gamma a b := by
  obtain ⟨L, psi, hL, hL_pos, hpsi_maps, hpsi_mono, hpsi_zero, hpsi_L,
    _, _, hpsi_C1, hunit_C1, hunit, _, _, horiginalLength, _, htotalLength⟩ :=
    exists_unit_speed_reparametrization_of_regular hab hgamma hreg
  let scale : ℝ → ℝ := fun t ↦ L * t
  let theta : ℝ → ℝ := psi ∘ scale
  have hscale_maps : MapsTo scale (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL_pos.le ht.1,
      (mul_le_mul_of_nonneg_left ht.2 hL_pos.le).trans_eq (mul_one L)⟩
  have htheta_maps : MapsTo theta (Icc 0 1) (Icc a b) :=
    hpsi_maps.comp hscale_maps
  have hscale_mono : MonotoneOn scale (Icc 0 1) := by
    intro s _ t _ hst
    exact mul_le_mul_of_nonneg_left hst hL_pos.le
  have htheta_mono : MonotoneOn theta (Icc 0 1) := by
    intro s hs t ht hst
    exact hpsi_mono (hscale_maps hs) (hscale_maps ht)
      (hscale_mono hs ht hst)
  have hscale_C1 : ContDiff ℝ 1 scale := by
    fun_prop
  have htheta_C1 : ContDiffOn ℝ 1 theta (Icc 0 1) := by
    simpa only [theta] using hpsi_C1.comp hscale_C1.contDiffOn hscale_maps
  have hcomp_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (gamma ∘ theta) (Icc 0 1) := by
    have hcomp := hunit_C1.comp hscale_C1.contDiffOn.contMDiffOn hscale_maps
    simpa only [theta, Function.comp_assoc] using hcomp
  have hscale_hasDeriv : ∀ t, HasDerivAt scale L t := by
    intro t
    simpa only [scale, id_eq, mul_one] using (hasDerivAt_id t).const_mul L
  have hunit_mdiff : ∀ t ∈ Icc 0 L, MDiffAt (gamma ∘ psi) t := by
    intro t ht
    by_contra hnot
    have hzero : riemannianSpeed I (gamma ∘ psi) t = 0 := by
      rw [riemannianSpeed_eq_zero]
      simp [mfderiv_zero_of_not_mdifferentiableAt hnot]
    rw [hunit t ht] at hzero
    norm_num at hzero
  have hconstant : ∀ t ∈ Icc 0 1,
      riemannianSpeed I (gamma ∘ theta) t = L := by
    intro t ht
    have hchain := riemannianSpeed_comp I (gamma ∘ psi) scale t
      (hunit_mdiff _ (hscale_maps ht)) (hscale_hasDeriv t).differentiableAt
    rw [(hscale_hasDeriv t).deriv, abs_of_pos hL_pos, hunit _ (hscale_maps ht)] at hchain
    simpa only [theta, Function.comp_assoc, mul_one] using hchain
  have hconstantLength :
      pathELength I (gamma ∘ theta) 0 1 = ENNReal.ofReal L := by
    have hunit_md : MDiff[Icc (scale 0) (scale 1)] (gamma ∘ psi) := by
      simpa only [scale, mul_zero, mul_one] using
        hunit_C1.mdifferentiableOn (by norm_num)
    have hcomp := pathELength_comp_of_monotoneOn (I := I) zero_le_one
      hscale_mono (hscale_C1.contDiffOn.differentiableOn (by norm_num))
      hunit_md
    calc
      pathELength I (gamma ∘ theta) 0 1 =
          pathELength I ((gamma ∘ psi) ∘ scale) 0 1 := by
        simp only [theta, Function.comp_assoc]
      _ = pathELength I (gamma ∘ psi) (scale 0) (scale 1) := hcomp
      _ = pathELength I (gamma ∘ psi) 0 L := by
        simp only [scale, mul_zero, mul_one]
      _ = pathELength I gamma a b := htotalLength
      _ = ENNReal.ofReal L := horiginalLength
  have htheta_zero : theta 0 = a := by simp only [theta, scale, Function.comp_apply, mul_zero,
    hpsi_zero]
  have htheta_one : theta 1 = b := by simp only [theta, scale, Function.comp_apply, mul_one,
    hpsi_L]
  refine ⟨L, theta, hL, hL_pos, htheta_maps, htheta_mono, htheta_zero,
    htheta_one, htheta_C1, hcomp_C1, hconstant, hconstantLength, ?_⟩
  exact hconstantLength.trans horiginalLength.symm

end

end TauCeti.Manifold
