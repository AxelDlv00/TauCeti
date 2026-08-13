/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant properties on a preconnected set

A predicate that is locally constant along a preconnected set takes the same value everywhere on
it. Mathlib's `IsLocallyConstant.apply_eq_of_preconnectedSpace` says this for a locally constant
function on a preconnected *space*; the statement below is the relative form, for a predicate on a
preconnected subset `s` of an ambient space, with local constancy expressed by the `𝓝[s]`
neighbourhood filter rather than by passing to the subtype.

## Main declarations

* `TauCeti.eq_of_isPreconnected_of_eventually_iff`: a predicate whose truth value is locally
  constant along a preconnected set is constant along it.
-/

public section

namespace TauCeti

open Filter Topology

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A property that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`. -/
theorem eq_of_isPreconnected_of_eventually_iff (hs : IsPreconnected s) {P : X → Prop}
    (hP : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, (P u ↔ P t)) {a b : X} (ha : a ∈ s) (hb : b ∈ s) (hPa : P a) :
    P b := by
  have hlc : IsLocallyConstant fun x : s => P x.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t, ht⟩
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.Eventually.comap ((hP t ht).mono fun _ hu => propext hu) _
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  rw [hlc.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨a, ha⟩]
  exact hPa

end TauCeti
