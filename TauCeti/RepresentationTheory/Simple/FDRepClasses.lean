/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# The isomorphism classes of simple objects of `FDRep k G`

A classification of representations is a bijection onto *isomorphism classes*, so it needs a type
of them. For abstract simple modules there is none, since they range over every universe, and
`TauCeti.SimpleSubmoduleClasses` exists to stand in for one: it is the isomorphism classes of
simple *submodules* of a fixed module, which over a semisimple ring realizes every isomorphism
class of simple modules. The objects of `FDRep k G` need no such device, because they already form
a type; quotienting them by isomorphism is a plain `Quot`.

`TauCeti.SimpleFDRepClasses` is that quotient, deliberately shaped after
`TauCeti.SimpleSubmoduleClasses` -- `mk`, `mk_eq_mk_iff`, `ind`, `lift`, `lift_mk` -- so that the
two are used the same way, and with the same discipline: the quotient is an implementation detail
and nothing downstream unfolds it.

`TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses` compares the two over a semisimple group
algebra, sending a simple object to the isomorphism class of the `k[G]`-module it carries. It is
what makes a categorical classification and a module-level classification of the same group two
readings of one bijection rather than two unrelated bijections; see
`TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses` for the symmetric group.

## Main results

* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`: over a semisimple group algebra, the
  isomorphism class of the `k[G]`-module a simple object carries.
-/

public section

open CategoryTheory

namespace TauCeti

open scoped MonoidAlgebra

universe u v

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

end TauCeti
