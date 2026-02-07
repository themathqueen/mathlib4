/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Type synonym for linear map convolutive ring and intrinsic star

This files provides the type synonym `ConvRing` which we will use in later files
to put the convolutive product on linear maps instance and the intrinsic star instance.
This is to insure that we only have one multiplication, one unit, and one star.

This is given for any type `A` so that we can have `ConvRing (A →ₗ[R] B)` as well as
`ConvRing (A →L[R] B)`.
-/

@[expose] public section

/-- A type synonym for the convolutive product of linear maps and intrinsic star.

The instances for the convolutive product and intrinsic star are only available with this type.

Use `ConvRing.linearEquiv` to coerce into this type. -/
structure ConvRing A where
  /-- Converts an element of `A` to `ConvRing A`. -/
  ofRing ::
  /-- Converts an element of `ConvRing A` back to `A`. -/
  toRing : A

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `ofRing x` being printed as `{ toRing := x }` by `delabStructureInstance`. -/
@[app_delab ConvRing.ofRing]
meta def ConvRing.delabOfRing : Delab := delabApp

namespace ConvRing
variable {R A : Type*}

@[simp] lemma toRing_ofRing (x : A) : toRing (ofRing x) = x := rfl
@[simp] lemma ofRing_toRing (x : ConvRing A) : ofRing (toRing x) = x := rfl

lemma toRing_surjective : Function.Surjective (@toRing A) :=
  Function.RightInverse.surjective toRing_ofRing

lemma ofRing_surjective : Function.Surjective (@ofRing A) :=
  Function.RightInverse.surjective ofRing_toRing

lemma toRing_injective : Function.Injective (@toRing A) :=
  Function.LeftInverse.injective ofRing_toRing

lemma ofRing_injective : Function.Injective (@ofRing A) :=
  Function.LeftInverse.injective toRing_ofRing

lemma toRing_bijective : Function.Bijective (@toRing A) := ⟨toRing_injective, toRing_surjective⟩
lemma ofRing_bijective : Function.Bijective (@ofRing A) := ⟨ofRing_injective, ofRing_surjective⟩

instance : Coe (ConvRing A) A where coe := toRing
instance {B C} [CoeFun A (fun _ ↦ B → C)] : CoeFun (ConvRing A) (fun _ ↦ B → C) where
  coe f := ⇑(f : A)

@[ext] protected theorem ext {x y : ConvRing A}
    (h : x.toRing = y.toRing) : x = y := toRing_injective h

variable (A) in
/-- `WithLp.ofLp` and `WithLp.toLp` as an equivalence. -/
protected def equiv : ConvRing A ≃ A where
  toFun := toRing
  invFun := ofRing
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma equiv_apply (x : ConvRing A) : ConvRing.equiv A x = x.toRing := rfl
@[simp] lemma symm_equiv_apply (x : A) : (ConvRing.equiv A).symm x = ofRing x := rfl

instance [Nontrivial A] : Nontrivial (ConvRing A) := (ConvRing.equiv A).nontrivial
instance [Unique A] : Unique (ConvRing A) := (ConvRing.equiv A).unique
instance [DecidableEq A] : DecidableEq (ConvRing A) := (ConvRing.equiv A).decidableEq
instance [AddCommMonoid A] : AddCommMonoid (ConvRing A) := (ConvRing.equiv A).addCommMonoid
instance [AddCommGroup A] : AddCommGroup (ConvRing A) := (ConvRing.equiv A).addCommGroup
@[to_additive] instance [SMul R A] : SMul R (ConvRing A) := (ConvRing.equiv A).smul R
@[to_additive] instance [Monoid R] [MulAction R A] : MulAction R (ConvRing A) :=
  fast_instance% (ConvRing.equiv A).mulAction R
instance [Monoid R] [AddCommMonoid A] [DistribMulAction R A] : DistribMulAction R (ConvRing A) :=
  fast_instance% (ConvRing.equiv A).distribMulAction R
instance [Semiring R] [AddCommMonoid A] [Module R A] : Module R (ConvRing A) :=
  fast_instance% (ConvRing.equiv A).module R

section AddCommGroup
variable [AddCommGroup A]

@[simp] lemma toRing_sub (x y : A) : ofRing (x - y) = ofRing x - ofRing y := rfl
@[simp] lemma ofRing_sub (x y : ConvRing A) : toRing (x - y) = toRing x - toRing y := rfl

@[simp] lemma toRing_neg (x : ConvRing A) : toRing (-x) = -toRing x := rfl
@[simp] lemma ofRing_neg (x : A) : ofRing (-x) = -ofRing x := rfl

end AddCommGroup

@[simp] lemma toRing_smul [SMul R A] (c : R) (x : ConvRing A) : toRing (c • x) = c • toRing x := rfl
@[simp] lemma ofRing_smul [SMul R A] (c : R) (x : A) : ofRing (c • x) = c • ofRing x := rfl

variable [AddCommMonoid A]

@[simp] lemma toRing_zero : toRing (0 : ConvRing A) = 0 := rfl
@[simp] lemma ofRing_zero : ofRing (0 : A) = 0 := rfl

@[simp] lemma toRing_add (x y : ConvRing A) : toRing (x + y) = toRing x + toRing y := rfl
@[simp] lemma ofRing_add (x y : A) : ofRing (x + y) = ofRing x + ofRing y := rfl

@[simp] lemma toRing_eq_zero {x : ConvRing A} : toRing x = 0 ↔ x = 0 := toRing_injective.eq_iff
@[simp] lemma ofRing_eq_zero {x : A} : ofRing x = 0 ↔ x = 0 := ofRing_injective.eq_iff

variable (A) in
@[simps!] protected def addEquiv : ConvRing A ≃+ A where
  __ := ConvRing.equiv A
  map_add' := by simp

@[simp] theorem toEquiv_addEquiv : (ConvRing.addEquiv A).toEquiv = ConvRing.equiv A := rfl

variable (R A) in
/-- The linear equivalence between `ConvRing A` and `A`. -/
protected def linearEquiv [Semiring R] [Module R A] : ConvRing A ≃ₗ[R] A where
  __ := ConvRing.addEquiv A
  map_smul' := by simp

@[simp] lemma linearEquiv_apply [Semiring R] [Module R A]
    (a : ConvRing A) : ConvRing.linearEquiv R A a = toRing a := rfl
@[simp] lemma symm_linearEquiv_apply [Semiring R] [Module R A]
    (a : A) : (ConvRing.linearEquiv R A).symm a = ofRing a := rfl

@[simp] lemma toAddEquiv_linearEquiv [Semiring R] [Module R A] :
    (ConvRing.linearEquiv R A).toAddEquiv = ConvRing.addEquiv A := rfl

instance [Semiring R] [Module R A] [Module.Finite R A] :
    Module.Finite R (ConvRing A) := Module.Finite.equiv (ConvRing.linearEquiv R A).symm

@[simp] lemma toRing_sum {ι : Type*} (s : Finset ι) (f : ι → ConvRing A) :
    (∑ i ∈ s, f i).toRing = ∑ i ∈ s, (f i).toRing := map_sum (ConvRing.addEquiv _) _ _

@[simp] lemma ofRing_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    ofRing (∑ i ∈ s, f i) = ∑ i ∈ s, ofRing (f i) := map_sum (ConvRing.addEquiv _).symm _ _

@[simp] lemma toRing_listSum (l : List (ConvRing A)) :
    l.sum.toRing = (l.map toRing).sum := map_list_sum (ConvRing.addEquiv _) _

@[simp] lemma ofRing_listSum (l : List A) :
    ofRing l.sum = (l.map ofRing).sum := map_list_sum (ConvRing.addEquiv _).symm _

@[simp] lemma toRing_multisetSum (s : Multiset (ConvRing A)) :
    s.sum.toRing = (s.map toRing).sum := map_multiset_sum (ConvRing.addEquiv _) _

@[simp] lemma ofRing_multisetSum (s : Multiset A) :
    ofRing s.sum = (s.map ofRing).sum := map_multiset_sum (ConvRing.addEquiv _).symm _

section LinearMapComp
variable {B C : Type*} [Semiring R] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] (f : ConvRing (B →ₗ[R] C)) (g : ConvRing (A →ₗ[R] B))

/-- The composition of linear maps as elements in `ConvRing`. -/
protected def comp : ConvRing (A →ₗ[R] C) := ofRing (f.toRing ∘ₗ g.toRing)

lemma comp_def : f.comp g = ofRing (f.toRing ∘ₗ g.toRing) := rfl
@[simp] lemma comp_apply (x : A) : f.comp g x = f.toRing (g.toRing x) := rfl

end LinearMapComp

end ConvRing
