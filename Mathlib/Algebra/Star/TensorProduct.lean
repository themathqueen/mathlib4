/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The star structure on tensor products

This file defines the `Star` structure on tensor products. This also
defines the `StarAddMonoid` and `StarModule` instances for tensor products.
-/

namespace TensorProduct
variable {R A B : Type*}
  [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]
  [AddCommMonoid B] [StarAddMonoid B] [Module R B] [StarModule R B]

open scoped TensorProduct

instance : Star (A ⊗[R] B) where
  star x := congr (starLinearEquiv R) (starLinearEquiv R) x

@[simp]
theorem star_tmul (x : A) (y : B) : star (x ⊗ₜ[R] y) = star x ⊗ₜ[R] star y := rfl

noncomputable instance : InvolutiveStar (A ⊗[R] B) where
  star_involutive x := by
    simp_rw [star]
    rw [congr_congr]
    convert congr($congr_refl_refl x) <;> ext <;> simp

noncomputable instance : StarAddMonoid (A ⊗[R] B) where
  star_add := LinearMap.map_add _

instance : StarModule R (A ⊗[R] B) where
  star_smul := LinearMap.map_smulₛₗ _

theorem _root_.starLinearEquiv_tensor :
    starLinearEquiv R (A := A ⊗[R] B) = congr (starLinearEquiv R) (starLinearEquiv R) := rfl

end TensorProduct
