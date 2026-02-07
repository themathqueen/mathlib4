/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Notation.ConvRing
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Convolution product on linear maps from a coalgebra to an algebra

This file constructs the ring structure on linear maps `C → A` where `C` is a coalgebra and `A` an
algebra, where multiplication is given by `(f * g)(x) = ∑ f x₍₁₎ * g x₍₂₎` in Sweedler notation or
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.

## Implementation notes

Note that in the case `C = A` this convolution product conflicts with the (unfortunately global!)
group instance on `Module.End R A` with multiplication defined as composition.
As a result, the convolution product is scoped to `ConvolutionProduct`.
-/

@[expose] public section

suppress_compilation

open Coalgebra TensorProduct ConvRing
open scoped RingTheory.LinearMap

variable {R A B C : Type*} [CommSemiring R]

namespace LinearMap
section NonUnitalNonAssocSemiring
variable
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- Convolution product on linear maps from a coalgebra to an algebra. -/
instance convMul : Mul (ConvRing (C →ₗ[R] A)) where
  mul f g := ofRing (mul' R A ∘ₗ map f.toRing g.toRing ∘ₗ comul)

lemma convMul_def (f g : ConvRing (C →ₗ[R] A)) :
    f * g = ofRing (mul' R A ∘ₗ map f.toRing g.toRing ∘ₗ comul) := rfl

@[simp]
lemma convMul_apply (f g : ConvRing (C →ₗ[R] A)) (c : C) :
    (f * g) c = mul' R A (.map f.toRing g.toRing (comul c)) := rfl

lemma _root_.Coalgebra.Repr.convMul_apply {a : C} (𝓡 : Coalgebra.Repr R a)
    (f g : ConvRing (C →ₗ[R] A)) : (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [convMul_def, ← 𝓡.eq]

/-- Non-unital and non-associative convolution semiring structure on linear maps from a
coalgebra to a non-unital non-associative algebra. -/
instance convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (ConvRing (C →ₗ[R] A)) where
  left_distrib f g h := by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp

@[simp] lemma toSpanSingleton_convMul_toSpanSingleton (x y : A) :
    ofRing (toSpanSingleton R A x) * ofRing (toSpanSingleton R A y) =
      ofRing (toSpanSingleton R A (x * y)) := by ext; simp

theorem _root_.TensorProduct.map_convMul_map {D : Type*} [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R B] [NonUnitalNonAssocSemiring D] [Module R D] [SMulCommClass R D D]
    [IsScalarTower R D D] {f h : ConvRing (C →ₗ[R] A)} {g k : ConvRing (B →ₗ[R] D)} :
    ofRing (f.toRing ⊗ₘ g.toRing) * ofRing (h.toRing ⊗ₘ k.toRing) =
      ofRing ((f * h).toRing ⊗ₘ (g * k).toRing) := by
  simp_rw [convMul_def, comul_def, mul'_tensor, comp_assoc, AlgebraTensorModule.map_eq,
    ← comp_assoc _ _ (tensorTensorTensorComm R _ _ _ _).toLinearMap]
  nth_rw 2 [← comp_assoc, comp_assoc]
  simp [AlgebraTensorModule.tensorTensorTensorComm_eq, ← tensorTensorTensorComm_comp_map,
    ← comp_assoc, map_comp]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- Non-unital and non-associative convolution ring structure on linear maps from a
coalgebra to a non-unital and non-associative algebra. -/
instance convNonUnitalNonAssocRing : NonUnitalNonAssocRing (ConvRing (C →ₗ[R] A)) where

end NonUnitalNonAssocRing

section NonUnitalSemiring
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

lemma nonUnitalAlgHom_comp_convMul_distrib
    [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    (h : A →ₙₐ[R] B) (f g : ConvRing (C →ₗ[R] A)) :
    (h : A →ₗ[R] B).comp (f * g).toRing =
      (ofRing ((h : A →ₗ[R] B).comp f.toRing) * ofRing ((h : A →ₗ[R] B).comp g.toRing)).toRing := by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']

lemma convMul_comp_coalgHom_distrib [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
    (f g : ConvRing (C →ₗ[R] A)) (h : B →ₗc[R] C) :
    (f * g).toRing.comp h.toLinearMap =
      (ofRing (f.toRing.comp h.toLinearMap) * ofRing (g.toRing.comp h.toLinearMap)).toRing := by
  simp [convMul_def, map_comp, comp_assoc]

/-- Non-unital convolution semiring structure on linear maps from a coalgebra to a
non-unital algebra. -/
instance convNonUnitalSemiring : NonUnitalSemiring (ConvRing (C →ₗ[R] A)) where
  mul_assoc f g h := calc
    _ = ofRing ((μ ∘ₗ rTensor _ μ) ∘ₗ (((f.toRing ⊗ₘ g.toRing) ⊗ₘ h.toRing) ∘ₗ
        (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ) := by
      ext; simp [comp_assoc, coassoc_symm, convMul_def]
    _ = ofRing ((μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm) ∘ₗ
        (f.toRing ⊗ₘ (g.toRing ⊗ₘ h.toRing)) ∘ₗ lTensor C δ ∘ₗ δ) := by
      simp only [map_map_comp_assoc_symm_eq, comp_assoc]
    _ = ofRing ((μ ∘ₗ .lTensor _ μ) ∘ₗ (f.toRing ⊗ₘ (g.toRing ⊗ₘ h.toRing)) ∘ₗ
        (lTensor C δ ∘ₗ δ)) := by
      congr 2
      ext
      simp [mul_assoc]
    _ = ofRing (μ ∘ₗ (f.toRing ⊗ₘ μ ∘ₗ (g.toRing ⊗ₘ h.toRing) ∘ₗ δ) ∘ₗ δ) := by ext; simp

end NonUnitalSemiring

section NonUnitalRing
variable [NonUnitalRing A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [Coalgebra R C]

/-- Non-unital convolution ring structure on linear maps from a coalgebra to a
non-unital algebra. -/
instance convNonUnitalRing : NonUnitalRing (ConvRing (C →ₗ[R] A)) where

end NonUnitalRing

section Semiring
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [AddCommMonoid C] [Module R C]

section CoalgebraStruct
variable [CoalgebraStruct R C]

lemma algHom_comp_convMul_distrib (h : A →ₐ B) (f g : ConvRing (C →ₗ[R] A)) :
    h.toLinearMap.comp (f * g).toRing =
      (ofRing (h.toLinearMap.comp f.toRing) * ofRing (h.toLinearMap.comp g.toRing)).toRing := by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

end CoalgebraStruct

variable [Coalgebra R C]

/-- Convolution unit on linear maps from a coalgebra to an algebra. -/
instance convOne : One (ConvRing (C →ₗ[R] A)) where one := ofRing (Algebra.linearMap R A ∘ₗ counit)

lemma convOne_def : (1 : ConvRing (C →ₗ[R] A)) = ofRing (Algebra.linearMap R A ∘ₗ counit) := rfl

@[simp] lemma convOne_apply (c : C) :
    (1 : ConvRing (C →ₗ[R] A)) c = algebraMap R A (counit (R := R) c) := rfl

/-- Convolution semiring structure on linear maps from a coalgebra to an algebra. -/
instance convSemiring : Semiring (ConvRing (C →ₗ[R] A)) where
  one_mul f := by ext; simp [convOne_def, ← map_comp_rTensor]
  mul_one f := by ext; simp [convOne_def, ← map_comp_lTensor]

end Semiring

section CommSemiring
variable [CommSemiring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

/-- Commutative convolution semiring structure on linear maps from a cocommutative coalgebra to an
algebra. -/
instance convCommSemiring : CommSemiring (ConvRing (C →ₗ[R] A)) where
  mul_comm f g := by ext x; rw [convMul_apply, ← comm_comul R x, map_comm, mul'_comm, convMul_apply]

end CommSemiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

/-- Convolution ring structure on linear maps from a coalgebra to an algebra. -/
instance convRing : Ring (ConvRing (C →ₗ[R] A)) where

end Ring

section CommRing
variable [CommRing A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C] [IsCocomm R C]

/-- Commutative convolution ring structure on linear maps from a cocommutative coalgebra to an
algebra. -/
instance convCommRing : CommRing (ConvRing (C →ₗ[R] A)) where

end CommRing
end LinearMap
