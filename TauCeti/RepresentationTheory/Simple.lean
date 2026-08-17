/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# Simple objects of `Rep k G` and `FDRep k G`

Two notions of "irreducible representation" coexist. `Representation.IsIrreducible ρ` says that the
lattice of subrepresentations of `ρ` has exactly two elements, and it is the notion in which the
representation-theoretic arguments of this repository are phrased.
`CategoryTheory.Simple X` says that every monomorphism into the object `X` is either zero or an
isomorphism, and it is the notion in which the categorical machinery is phrased -- Schur's lemma
`FDRep.finrank_hom_simple_simple`, the characters of simple objects, semisimple categories. Neither
Mathlib nor this repository related the two, and several files here say so and stop at the
`Representation` level. This file supplies the dictionary, and the type of isomorphism classes of
simple objects that a categorical classification statement is valued in.

Over `Rep k G` the dictionary is bookkeeping. `Rep k G` is equivalent to the category of
`k[G]`-modules (`Rep.equivalenceModuleMonoidAlgebra`), an equivalence transports simplicity in both
directions, and a module is a simple object exactly when it is a simple module
(`simple_iff_isSimpleModule`).

`FDRep k G` is not known to be equivalent to a module category, so it needs an argument in each
direction. One is formal: the forgetful functor to `Rep k G` is faithful, preserves zero morphisms
and monomorphisms, and reflects isomorphisms, and such a functor reflects simplicity
(`CategoryTheory.Functor.simple_of_simple_obj`). The other uses finite-dimensionality, and is where
the restriction to `FDRep` earns its keep: a subrepresentation of a finite-dimensional
representation is again finite-dimensional, so it is again an object of `FDRep k G`, and its
inclusion is a monomorphism which is nonzero exactly when the subrepresentation is nonzero and an
isomorphism exactly when the subrepresentation is everything. Simplicity of the object therefore
says precisely that the lattice of subrepresentations is `{⊥, ⊤}` with `⊥ ≠ ⊤`.

The isomorphism classes of simple objects of `FDRep k G` are a *type*: unlike the isomorphism
classes of abstract simple modules, which range over every universe, the objects of `FDRep k G` are
a type already, so quotienting them by isomorphism needs no device.
`TauCeti.SimpleFDRepClasses` is that quotient, in the shape of
`TauCeti.SimpleSubmoduleClasses`, and `TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`
compares the two over a semisimple group algebra: a categorical classification and a module-level
classification of the same group are two readings of one bijection.

## Main results

* `TauCeti.Rep.simple_iff_isIrreducible`: an object of `Rep k G` is simple exactly when the
  representation it carries is irreducible.
* `TauCeti.FDRep.simple_iff_isIrreducible`: the same for `FDRep k G`.
* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`: over a semisimple group algebra, the
  isomorphism class of the `k[G]`-module a simple object carries.
-/

public section

open CategoryTheory

namespace TauCeti

open scoped MonoidAlgebra

universe u v w

/-- **An object of `Rep k G` is simple exactly when the representation it carries is
irreducible.** Both sides say that the `k[G]`-module the object carries is simple: the left-hand
side across `Rep.equivalenceModuleMonoidAlgebra`, the right-hand side across
`Representation.irreducible_iff_isSimpleModule_asModule`. -/
theorem Rep.simple_iff_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) : Simple A ↔ _root_.Representation.IsIrreducible A.ρ := by
  rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule,
    ← simple_iff_isSimpleModule (R := k[G]) (M := A.ρ.asModule)]
  exact (simple_obj_iff (Rep.toModuleMonoidAlgebra (k := k) (G := G)) A).symm

section FDRep

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The inclusion of a subrepresentation of a finite-dimensional representation, as a morphism of
`FDRep k G`: the monomorphism whose behaviour witnesses simplicity of the object. -/
private noncomputable def subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    FDRep.of W.toRepresentation ⟶ X :=
  (forget₂ (FDRep k G) (Rep k G)).preimage (Rep.ofHom W.subtype)

private theorem map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    (forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W) = Rep.ofHom W.subtype :=
  (forget₂ (FDRep k G) (Rep k G)).map_preimage _

private theorem mono_map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    Mono ((forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W)) := by
  rw [map_subInclusion]
  exact (Rep.mono_iff_injective _).mpr Subtype.val_injective

private instance (X : FDRep k G) (W : Subrepresentation X.ρ) : Mono (subInclusion X W) :=
  (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (mono_map_subInclusion X W)

/-- The inclusion of a subrepresentation is the zero morphism exactly when the subrepresentation is
zero. -/
private theorem subInclusion_eq_zero_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    subInclusion X W = 0 ↔ W = ⊥ := by
  rw [← (forget₂ (FDRep k G) (Rep k G)).map_eq_zero_iff, map_subInclusion]
  constructor
  · intro h
    refine Subrepresentation.toSubmodule_injective ?_
    rw [Subrepresentation.toSubmodule_bot, Submodule.eq_bot_iff]
    intro x hx
    exact congrArg (fun f => (Rep.Hom.hom f) (⟨x, hx⟩ : W.toSubmodule)) h
  · rintro rfl
    ext x
    exact (Submodule.mem_bot k).mp x.2

/-- The inclusion of a subrepresentation is an isomorphism exactly when the subrepresentation is
everything. -/
private theorem isIso_subInclusion_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    IsIso (subInclusion X W) ↔ W = ⊤ := by
  constructor
  · intro h
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W)) := inferInstance
    rw [map_subInclusion] at hepi
    have hrange : W.toSubmodule.subtype.range = ⊤ :=
      LinearMap.range_eq_top.mpr ((Rep.epi_iff_surjective _).mp hepi)
    rw [Submodule.range_subtype] at hrange
    exact Subrepresentation.toSubmodule_injective
      (hrange.trans Subrepresentation.toSubmodule_top.symm)
  · rintro rfl
    have hmono := mono_map_subInclusion X (⊤ : Subrepresentation X.ρ)
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map
        (subInclusion X (⊤ : Subrepresentation X.ρ))) := by
      rw [map_subInclusion]
      exact (Rep.epi_iff_surjective _).mpr fun y => ⟨⟨y, trivial⟩, rfl⟩
    have : IsIso ((forget₂ (FDRep k G) (Rep k G)).map
        (subInclusion X (⊤ : Subrepresentation X.ρ))) := isIso_of_mono_of_epi _
    exact isIso_of_reflects_iso _ (forget₂ (FDRep k G) (Rep k G))

/-- **An object of `FDRep k G` is simple exactly when the representation it carries is
irreducible.** -/
theorem FDRep.simple_iff_isIrreducible (X : FDRep k G) :
    Simple X ↔ _root_.Representation.IsIrreducible X.ρ := by
  constructor
  · intro _
    -- A subrepresentation is everything exactly when it is nonzero: this is simplicity of `X`,
    -- read through the inclusion of the subrepresentation.
    have key : ∀ W : Subrepresentation X.ρ, W = ⊤ ↔ ¬W = ⊥ := fun W => by
      rw [← isIso_subInclusion_iff, ← subInclusion_eq_zero_iff]
      exact Simple.mono_isIso_iff_nonzero _
    have hbot : (⊥ : Subrepresentation X.ρ) ≠ ⊤ := fun h => (key ⊥).mp h rfl
    have : Nontrivial (Subrepresentation X.ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
    exact ⟨fun W => (em (W = ⊥)).imp id (key W).mpr⟩
  · intro _
    have : Simple ((forget₂ (FDRep k G) (Rep k G)).obj X) :=
      (Rep.simple_iff_isIrreducible _).mpr ‹_›
    exact Functor.simple_of_simple_obj (forget₂ (FDRep k G) (Rep k G)) X

instance FDRep.simple_of_isIrreducible (X : FDRep k G)
    [_root_.Representation.IsIrreducible X.ρ] : Simple X :=
  (FDRep.simple_iff_isIrreducible X).mpr ‹_›

instance FDRep.isIrreducible_of_simple (X : FDRep k G) [Simple X] :
    _root_.Representation.IsIrreducible X.ρ :=
  (FDRep.simple_iff_isIrreducible X).mp ‹_›

end FDRep

section Classes

variable (k : Type u) (G : Type v) [Field k] [Monoid G]

/-- **The isomorphism classes of simple objects of `FDRep k G`.**

That this is a quotient of the simple objects by isomorphism is an implementation detail: build a
class with `TauCeti.SimpleFDRepClasses.mk`, compare classes with
`TauCeti.SimpleFDRepClasses.mk_eq_mk_iff`, and eliminate with `TauCeti.SimpleFDRepClasses.lift`
into `Sort` or `TauCeti.SimpleFDRepClasses.ind` into `Prop`. -/
def SimpleFDRepClasses :=
  Quot fun X Y : {X : FDRep k G // Simple X} => Nonempty (X.1 ≅ Y.1)

namespace SimpleFDRepClasses

variable {k G}

/-- The isomorphism class of a simple object of `FDRep k G`. -/
def mk (X : FDRep k G) [Simple X] : SimpleFDRepClasses k G := Quot.mk _ ⟨X, ‹_›⟩

theorem mk_eq_mk_iff {X Y : FDRep k G} [Simple X] [Simple Y] :
    mk X = mk Y ↔ Nonempty (X ≅ Y) :=
  Quot.eq.trans <| Equivalence.eqvGen_iff
    ⟨fun _ => ⟨.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

/-- Every isomorphism class is the class of a simple object: the eliminator into `Prop`. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClasses k G → Prop}
    (mk : ∀ (X : FDRep k G) (_ : Simple X), motive (.mk X)) (c : SimpleFDRepClasses k G) :
    motive c :=
  Quot.ind (fun X => mk X.1 X.2) c

/-- **The eliminator into `Sort`.** To define data on the isomorphism classes of simple objects of
`FDRep k G` it suffices to give a value on each simple object and to check that isomorphic simple
objects get the same value; the value on a class is then read off by
`TauCeti.SimpleFDRepClasses.lift_mk`. -/
def lift {α : Sort*} (f : ∀ (X : FDRep k G) [Simple X], α)
    (hf : ∀ (X Y : FDRep k G) [Simple X] [Simple Y], Nonempty (X ≅ Y) → f X = f Y)
    (c : SimpleFDRepClasses k G) : α :=
  Quot.lift (fun X => @f X.1 X.2) (fun X Y h => @hf X.1 Y.1 X.2 Y.2 h) c

/-- The defining equation of `TauCeti.SimpleFDRepClasses.lift`. -/
@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (X : FDRep k G) [Simple X], α} {hf} (X : FDRep k G)
    [Simple X] : lift f hf (mk X) = f X := (rfl)

/-- **The isomorphism class of the `k[G]`-module a simple object of `FDRep k G` carries.** Over a
semisimple group algebra this compares the categorical classification with the module-level one of
`TauCeti.SimpleSubmoduleClasses`. -/
noncomputable def toSimpleSubmoduleClasses [IsSemisimpleRing k[G]] :
    SimpleFDRepClasses k G → SimpleSubmoduleClasses k[G] k[G] :=
  lift (fun X _ => simpleModuleClass k[G] (_root_.Representation.asModule X.ρ)) fun _ _ _ _ h =>
    simpleModuleClass_eq_iff.mpr
      (Representation.nonempty_equiv_iff.mp (nonempty_fdRepIso_iff.mp h))

@[simp]
theorem toSimpleSubmoduleClasses_mk [IsSemisimpleRing k[G]] (X : FDRep k G) [Simple X] :
    toSimpleSubmoduleClasses (mk X) = simpleModuleClass k[G] (_root_.Representation.asModule X.ρ) :=
  (rfl)

end SimpleFDRepClasses

end Classes

end TauCeti
