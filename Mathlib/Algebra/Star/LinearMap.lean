/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Notation.ConvRing
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Intrinsic star operation on `E →ₗ[R] F`

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

**Note** that in the case of when `E = F` for a finite-dimensional Hilbert space, this `star`
is mathematically distinct from the global instance on `E →ₗ[𝕜] E` where
`star := LinearMap.adjoint`.
For that reason, the intrinsic star operation is scoped to `IntrinsicStar`.
-/

@[expose] public section

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

open ConvRing

namespace LinearMap

/-- The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`. -/
instance intrinsicStar : Star (ConvRing (E →ₗ[R] F)) where
  star f := ofRing <|
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }

@[simp] theorem intrinsicStar_apply (f : ConvRing (E →ₗ[R] F)) (x : E) :
    (star f) x = star (f (star x)) := rfl

/-- The involutive intrinsic star structure on linear maps. -/
instance intrinsicInvolutiveStar : InvolutiveStar (ConvRing (E →ₗ[R] F)) where
  star_involutive x := by ext; simp

/-- The intrinsic star additive monoid structure on linear maps. -/
instance intrinsicStarAddMonoid : StarAddMonoid (ConvRing (E →ₗ[R] F)) where
  star_add x y := by ext; simp

/-- A linear map is self-adjoint (with respect to the intrinsic star) iff it is star-preserving. -/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : ConvRing (E →ₗ[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, ConvRing.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
   star_eq_iff_star_eq, eq_comm]

@[deprecated (since := "2025-12-09")]
alias isSelfAdjoint_iff_map_star := IntrinsicStar.isSelfAdjoint_iff_map_star

/-- A star-preserving linear map is self-adjoint (with respect to the intrinsic star). -/
@[simp]
protected theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} :
    IsSelfAdjoint (ofRing (f : E →ₗ[R] F) : ConvRing (E →ₗ[R] F)) :=
  IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

@[deprecated (since := "2025-12-09")]
alias _root_.StarHomClass.isSelfAdjoint := _root_.IntrinsicStar.StarHomClass.isSelfAdjoint

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp (f : ConvRing (E →ₗ[R] F)) (g : ConvRing (G →ₗ[R] E)) :
    star (f.comp g) = (star f).comp (star g) := by ext; simp

@[simp] theorem intrinsicStar_id :
    star (ofRing (LinearMap.id (R := R) (M := E))) = ofRing LinearMap.id := by ext; simp
@[simp] theorem intrinsicStar_zero : star (0 : ConvRing (E →ₗ[R] F)) = 0 := by ext; simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mulLeft (x : E) :
    star (ofRing (mulLeft R x)) = ofRing (mulRight R (star x)) := by ext; simp

theorem intrinsicStar_mulRight (x : E) :
    star (ofRing (mulRight R x)) = ofRing (mulLeft R (star x)) := by
  rw [star_eq_iff_star_eq, intrinsicStar_mulLeft, star_star]

theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (ofRing (mul' R' E)) = ofRing (mul' R' E ∘ₗ TensorProduct.comm R' E E) :=
  ConvRing.ext <| TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
instance intrinsicStarModule : StarModule R (ConvRing (E →ₗ[R] F)) where
  star_smul _ _ := by ext; simp

section CommSemiring
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

theorem _root_.TensorProduct.intrinsicStar_map
    (f : ConvRing (E →ₗ[R] F)) (g : ConvRing (G →ₗ[R] H)) :
    star (ofRing (TensorProduct.map f.toRing g.toRing)) =
      ofRing (TensorProduct.map (star f).toRing (star g).toRing) :=
  ConvRing.ext <| TensorProduct.ext' fun _ _ ↦ by simp

theorem intrinsicStar_lTensor (f : ConvRing (F →ₗ[R] G)) :
    star (ofRing (lTensor E f.toRing)) = ofRing (lTensor E (star f).toRing) := by ext; simp

theorem intrinsicStar_rTensor (f : ConvRing (E →ₗ[R] F)) :
    star (ofRing (rTensor G f.toRing)) = ofRing (rTensor G (star f).toRing) := by ext; simp

theorem intrinsicStar_eq_comp (f : ConvRing (E →ₗ[R] F)) :
    star f =
      ofRing ((starLinearEquiv R).toLinearMap ∘ₛₗ f.toRing ∘ₛₗ (starLinearEquiv R).toLinearMap) :=
  rfl

theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := ConvRing (E →ₗ[R] F)) =
      (ConvRing.linearEquiv R _).trans
      (((starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans
        (ConvRing.linearEquiv R _).symm) := rfl

end CommSemiring

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

@[simp] theorem intrinsicStar_toSpanSingleton (a : E) :
    star (ofRing (toSpanSingleton S E a)) = ofRing (toSpanSingleton S E (star a)) := by ext; simp

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : ConvRing (E →ₗ[S] S)) (x : F) :
    star (ofRing (f.toRing.smulRight x)) = ofRing ((star f).toRing.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

end LinearMap

section matrix
variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

namespace LinearMap

theorem toMatrix'_intrinsicStar (f : ConvRing ((m → R) →ₗ[R] (n → R))) :
    (star f).toRing.toMatrix' = f.toRing.toMatrix'.map star := by
  ext; simp

/-- A linear map `f : (m → R) →ₗ (n → R)` is self-adjoint (with respect to the intrinsic star)
iff its corresponding matrix `f.toMatrix'` has all self-adjoint elements.
So star-preserving maps correspond to their matrices containing only self-adjoint elements. -/
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : ConvRing ((m → R) →ₗ[R] (n → R))) :
    IsSelfAdjoint f ↔ ∀ i j, IsSelfAdjoint (f.toRing.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    ConvRing.ext_iff]

end LinearMap

namespace Matrix

theorem intrinsicStar_toLin' (A : Matrix n m R) :
    star (ofRing A.toLin') = ofRing (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, ConvRing.ext_iff]

/-- Given a matrix `A`, `A.toLin'` is self-adjoint (with respect to the intrinsic star)
iff all its elements are self-adjoint. -/
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint (ofRing A.toLin') ↔ ∀ i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

end Matrix
end matrix

namespace Module.End

/-- Intrinsic star operation for `(End R E)ˣ`. -/
instance Units.intrinsicStar : Star (ConvRing (End R E)ˣ) where
  star f := ofRing <| by
    refine ⟨(star (ofRing ↑f.toRing : ConvRing (End R E))).toRing,
      (star (ofRing ↑(f.toRing⁻¹ : (End R E)ˣ))).toRing, ?_, ?_⟩
    all_goals
      rw [← ofRing_injective.eq_iff, mul_eq_comp, ← comp_def, ← LinearMap.intrinsicStar_comp]
      simp [comp_def, ← mul_eq_comp, one_eq_id]

theorem IsUnit.intrinsicStar {f : ConvRing (End R E)} (hf : IsUnit f.toRing) :
    IsUnit (star f).toRing := by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (ofRing (u : End R E))).toRing := (star (ofRing u)).toRing.isUnit
  simpa [hu] using this

open Module.End in
@[simp] theorem isUnit_intrinsicStar_iff {f : ConvRing (End R E)} :
    IsUnit (star f).toRing ↔ IsUnit f.toRing :=
  ⟨fun h ↦ star_star f ▸ h.intrinsicStar, fun h ↦ h.intrinsicStar⟩

section eigenspace
variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

open LinearMap

theorem mem_eigenspace_intrinsicStar_iff (f : ConvRing (End R V)) (α : R) (x : V) :
    x ∈ (star f).toRing.eigenspace α ↔ star x ∈ f.toRing.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]
theorem spectrum_intrinsicStar (f : ConvRing (End R V)) :
    spectrum R (star f).toRing = star (spectrum R f.toRing) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

end eigenspace
end Module.End
