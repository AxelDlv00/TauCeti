/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Probability.DeFinetti

/-!
# Worked examples: the de Finetti public API

This file imports **only** `TauCeti.Probability.DeFinetti`, and nothing is declared; the import is
not public, so this adds no second route to the API.

The first half is an export check: each example is a bare reference to a name Layer 7 advertises,
so the file elaborates exactly when the curated facade exports everything it promises. A failure
there means an export went missing, not that a proof broke — a summit can be proved, and its module
built, while the facade never re-exports it, leaving the name unreachable for a caller who imports
only the facade.

The second half *uses* the de Finetti correspondence rather than naming it: the mixing law of a
two-point mixture of i.i.d. laws is computed in both directions from the bundled affinity lemmas
and the point-mass identification, and a process whose path law happens to be an i.i.d. law is
shown to have a point mass as its de Finetti measure. These check that the correspondence API
composes — that a caller can build the bundled convex combinations and get from an equation
between path laws to an equation between mixing laws without leaving the facade.

## One advertised name does not exist

Layer 7 spells one endpoint `exchangeable_of_mixedIID`; the repository proves it canonically as
`MixedIID.exchangeable`, which is checked below under that name. No alias is introduced.

`deFinetti_empiricalMeasure` is not currently exported. Unlike the topology-free fixed-set endpoint
below, its weak-convergence statement requires an explicitly chosen compatible Polish topology,
which `[StandardBorelSpace α]` alone does not select.

Every other advertised name is checked below.

## The mathematical worked examples live elsewhere

The roadmap's worked-example list is discharged with the objects each concerns, not here: the
conditionally i.i.d. coin-flip construction in `Exchangeability/ConditionallyIID/CoinFlips.lean`,
the constant-witness characterisation of i.i.d. in `ConditionallyIID/Const.lean`, and the
stationary but non-exchangeable 3-cycle in `Exchangeability/ThreeCycle.lean`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 7** (public API and examples), whose
  suggested home for this file is `TauCeti/Examples/Probability/DeFinetti.lean`.
-/

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

/-! ### Export checks -/

-- The process predicates.
example := @Exchangeable
example := @FullyExchangeable
example := @Contractable
example := @MixedIIDWith
example := @MixedIID
example := @ConditionallyIIDWith
example := @ConditionallyIID

-- Relations between them.
example := @exchangeable_iff_fullyExchangeable
example := @contractable_of_exchangeable
example := @MixedIID.exchangeable
example := @mixedIIDWith_of_conditionallyIIDWith
example := @mixedIID_of_conditionallyIID

-- The summits: unsuffixed is the martingale route, the suffixed ones name theirs.
example := @conditionallyIID_of_contractable
example := @conditionallyIID_of_exchangeable
example := @deFinetti
example := @deFinetti_equivalence
example := @deFinetti_RyllNardzewski_equivalence
example := @mixedIID_of_contractable
example := @deFinetti_viaL2
example := @deFinetti_viaKoopman

-- Representation, disintegration and uniqueness.
example := @ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw
example := @deFinetti_mixture
example := @mixedIID_mixingLaw_unique
example := @conditionallyIID_ae_unique
example := @exchangeable_extreme_iff_iid

-- Empirical-frequency convergence. These two are promised by separate facade imports:
-- `ConditionallyIID.StrongLaw` for the conditional statement, `DeFinetti.EmpiricalMeasure` for the
-- de Finetti endpoint. Neither is re-exported by the other.
example := @ConditionallyIIDWith.tendsto_average_ae
example := @deFinetti_tendsto_empiricalMeasure_apply

/-! ### Using the correspondence -/

section Correspondence

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

/-- The correspondence carries a two-point mixing law to the corresponding two-point mixture of
i.i.d. laws. The mixing law is built with `ProbabilityMeasure.convexCombo`, not assumed. -/
example (P Q : ProbabilityMeasure α) {a b : ℝ≥0∞} (hab : a + b = 1) :
    ((deFinettiEquiv (TauCeti.MeasureTheory.ProbabilityMeasure.convexCombo hab
          ⟨Measure.dirac P, inferInstance⟩ ⟨Measure.dirac Q, inferInstance⟩) :
        ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
      = a • (Measure.infinitePi fun _ : ℕ => (P : Measure α))
        + b • (Measure.infinitePi fun _ : ℕ => (Q : Measure α)) :=
  (congrArg (fun r : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))} =>
      ((r : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)))
    (deFinettiEquiv_convexCombo hab _ _)).trans (by
      rw [exchangeableLawConvexCombo_toMeasure, deFinettiEquiv_dirac, deFinettiEquiv_dirac])

/-- Conversely, an exchangeable law that mixes two i.i.d. laws has the corresponding two-point
mixing law. This is the direction that uses de Finetti's theorem. -/
example (P Q : ProbabilityMeasure α) {a b : ℝ≥0∞} (hab : a + b = 1)
    {ρ₁ ρ₂ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}}
    (hρ₁ : ((ρ₁ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
      = Measure.infinitePi fun _ : ℕ => (P : Measure α))
    (hρ₂ : ((ρ₂ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
      = Measure.infinitePi fun _ : ℕ => (Q : Measure α)) :
    ((deFinettiEquiv.symm (exchangeableLawConvexCombo hab ρ₁ ρ₂) :
        ProbabilityMeasure (ProbabilityMeasure α)) : Measure (ProbabilityMeasure α))
      = a • Measure.dirac P + b • Measure.dirac Q := by
  rw [deFinettiEquiv_symm_convexCombo,
    TauCeti.MeasureTheory.ProbabilityMeasure.toMeasure_convexCombo,
    deFinettiEquiv_symm_eq_dirac P hρ₁, deFinettiEquiv_symm_eq_dirac Q hρ₂]

/-- An exchangeable process whose path law happens to be the i.i.d. law `P^{⊗ℕ}` has the point mass
at `P` as its de Finetti measure. -/
example {Ω : Type*} [MeasurableSpace Ω] [Nonempty α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n))
    (P : ProbabilityMeasure α)
    (hpath : pathLaw μ X = Measure.infinitePi fun _ : ℕ => (P : Measure α)) :
    (deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) :
        Measure (ProbabilityMeasure α)) = Measure.dirac P :=
  congrArg ProbabilityMeasure.toMeasure
    (eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi (π := ⟨Measure.dirac P, inferInstance⟩)
      hX hX_meas
      (by rw [hpath, ← deFinettiBarycenter_dirac P, deFinettiBarycenter_def]; rfl)).symm

end Correspondence

end Probability

end TauCeti
