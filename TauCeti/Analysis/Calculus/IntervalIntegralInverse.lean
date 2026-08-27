/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Inverses of primitives of positive functions

The primitive of a continuous positive real function is strictly increasing, and its inverse is
continuously differentiable on the interval between the primitive's endpoint values. This is the
parameter-side inverse result used by the regular Riemannian reparametrization theorem.

The result supplies the interval-integral and inverse-function prerequisite for Layer 0 of the
[Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md).
-/

public section

open Filter Set

namespace TauCeti

noncomputable section

/-- The primitive of a continuous, everywhere positive real function has a
`C¹` inverse on the interval between the primitive's endpoint values.

The conclusion records the inverse's construction, the primitive's strict
monotonicity and interval image, both inverse identities, the endpoint values,
and the derivative of the inverse. -/
theorem exists_contDiffOn_intervalIntegral_inverse_of_pos {v : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hv_cont : Continuous v) (hv_pos : ∀ t, 0 < v t) :
    ∃ L : ℝ, ∃ psi : ℝ → ℝ,
      L = ∫ t in a..b, v t ∧
      psi = Function.invFun (fun t ↦ ∫ s in a..t, v s) ∧
      0 < L ∧
      StrictMono (fun t ↦ ∫ s in a..t, v s) ∧
      (fun t ↦ ∫ s in a..t, v s) '' Icc a b = Icc 0 L ∧
      MapsTo psi (Icc 0 L) (Icc a b) ∧
      MonotoneOn psi (Icc 0 L) ∧
      psi 0 = a ∧
      psi L = b ∧
      (∀ t ∈ Icc a b, psi (∫ s in a..t, v s) = t) ∧
      (∀ s ∈ Icc 0 L, ∫ t in a..psi s, v t = s) ∧
      ContDiffOn ℝ 1 psi (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, HasDerivAt psi (v (psi s))⁻¹ s) := by
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
  have hphi_open : IsOpenMap phi :=
    isOpenMap_of_hasStrictDerivAt hphi_strict (fun t ↦ (hv_pos t).ne')
  have hpsi_deriv_local : ∀ t, HasDerivAt psi (v t)⁻¹ (phi t) := by
    intro t
    have hstrict : HasStrictDerivAt (Function.invFun phi) (v t)⁻¹ (phi t) :=
      (hphi_strict t).to_local_left_inverse (hv_pos t).ne'
        (Filter.Eventually.of_forall (Function.leftInverse_invFun hphi_inj))
    simpa only [psi] using hstrict.hasDerivAt
  have hW_open : IsOpen W := by
    simpa only [W] using hphi_open.isOpen_range
  have hright : ∀ s ∈ W, phi (psi s) = s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
  have hpsi_hasDeriv : ∀ s ∈ W, HasDerivAt psi (v (psi s))⁻¹ s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
    exact hpsi_deriv_local t
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
  let L : ℝ := ∫ t in a..b, v t
  have hphi_a : phi a = 0 := by
    simp only [phi, intervalIntegral.integral_same]
  have hphi_b : phi b = L := by
    simp only [phi, L]
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
  have hpsi_zero : psi 0 = a := by
    rw [← hphi_a, hleft a]
  have hpsi_L : psi L = b := by
    rw [← hphi_b, hleft b]
  have hleft_Icc : ∀ t ∈ Icc a b, psi (∫ s in a..t, v s) = t := by
    intro t _
    simpa only [phi] using hleft t
  have hright_Icc : ∀ s ∈ Icc 0 L, ∫ t in a..psi s, v t = s := by
    intro s hs
    simpa only [phi] using hright s (hIccW hs)
  refine ⟨L, psi, ?_, ?_, hL_pos, ?_, ?_, hmaps, hpsi_mono,
    hpsi_zero, hpsi_L, hleft_Icc, hright_Icc, hpsi_C1.mono hIccW, ?_⟩
  · simp only [L]
  · simp only [psi, phi]
  · simpa only [phi] using hphi_mono
  · simpa only [phi] using himage
  · exact fun s hs ↦ hpsi_hasDeriv s (hIccW hs)

end

end TauCeti
