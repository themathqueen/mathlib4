/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

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

Use `toConvRing.linearEquiv` to coerce into this type. -/
-- def ConvRing (A : Type*) := A
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

lemma toRing_bijective : Function.Bijective (@toRing A) :=
  ⟨toRing_injective, toRing_surjective⟩

lemma ofRing_bijective : Function.Bijective (@ofRing A) :=
  ⟨ofRing_injective, ofRing_surjective⟩

instance [Add A] : Add (ConvRing A) where add x y := .ofRing (x.toRing + y.toRing)
lemma add_def [Add A] (x y : ConvRing A) : x + y = .ofRing (x.toRing + y.toRing) := rfl

instance [Zero A] : Zero (ConvRing A) where zero := .ofRing 0
lemma zero_def [Zero A] : (0 : ConvRing A) = .ofRing 0 := rfl

instance [SMul R A] : SMul R (ConvRing A) where smul n a := .ofRing (n • a.toRing)
lemma smul_def [SMul R A] (n : R) (a : ConvRing A) :
    n • a = .ofRing (n • a.toRing) := rfl

instance [Neg A] : Neg (ConvRing A) where neg x := .ofRing (-x.toRing)
lemma neg_def [Neg A] (a : ConvRing A) : -a = .ofRing (-a.toRing) := rfl

attribute [local simp] ConvRing.add_def ConvRing.zero_def ConvRing.smul_def ConvRing.neg_def

instance [AddCommMonoid A] : AddCommMonoid (ConvRing A) where
  add_assoc := by simp [add_assoc]
  zero_add := by simp
  add_zero := by simp
  add_comm := by simp [add_comm]
  nsmul n a := n • a
  nsmul_zero := by simp
  nsmul_succ := by simp [add_smul]

instance [AddCommGroup A] : AddCommGroup (ConvRing A) where
  neg_add_cancel := by simp
  zsmul n a := n • a
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_smul]
  zsmul_neg' := by simp [add_smul]

instance [AddCommMonoid A] [Semiring R] [Module R A] : Module R (ConvRing A) where
  mul_smul := by simp [mul_smul]
  one_smul := by simp
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

variable (R A) in
def linearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : ConvRing A ≃ₗ[R] A where
  toFun x := toRing x
  invFun x := ofRing x
  map_add' := by simp
  map_smul' := by simp

@[simp] lemma linearEquiv_apply [Semiring R] [AddCommMonoid A] [Module R A]
    (a : ConvRing A) : linearEquiv R A a = toRing a := rfl
@[simp] lemma symm_linearEquiv_apply [Semiring R] [AddCommMonoid A] [Module R A]
    (a : A) : (linearEquiv R A).symm a = ofRing a := rfl

variable {B} [Semiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]

instance : Coe (ConvRing (A →ₗ[R] B)) (A →ₗ[R] B) where coe := toRing
instance : CoeFun (ConvRing (A →ₗ[R] B)) (fun _ ↦ A → B) where coe f := ⇑(f : A →ₗ[R] B)

@[ext] protected theorem ext {x y : ConvRing (A →ₗ[R] B)}
    (h : ∀ i, x i = y i) : x = y := toRing_injective <| LinearMap.ext h

end ConvRing
