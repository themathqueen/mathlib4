/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Nat.Fib.Basic

/-!

# Fibonacci numbers extended onto the integers

This file defines the Fibonacci sequence on the integers.

Definition of the sequence: `F₀ = 0`, `F₁ = 1`, and `Fₙ₊₂ = Fₙ₊₁ + Fₙ`
(same as the natural number version `Nat.fib`, but here `n` is an integer).

-/

namespace Int

/-- The Fibonacci sequence for integers. This satisfies `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`.

This is an extension of `Nat.fib`. -/
@[pp_nodot]
def fib (n : ℤ) : ℤ :=
  if 0 ≤ n then n.toNat.fib else
  if Even n then -(-n).toNat.fib else (-n).toNat.fib

@[simp] theorem fib_natCast (n : ℕ) : Int.fib n = Nat.fib n := rfl
@[simp] theorem fib_zero : Int.fib 0 = 0 := rfl
@[simp] theorem fib_one : Int.fib 1 = 1 := rfl
@[simp] theorem fib_two : Int.fib 2 = 1 := rfl
@[simp] theorem fib_neg_one : Int.fib (-1) = 1 := rfl
@[simp] theorem fib_neg_two : Int.fib (-2) = -1 := rfl

theorem fib_neg_natCast (n : ℕ) : Int.fib (-n) = (-1) ^ (n + 1) * n.fib := by
  simp only [fib, Int.neg_nonneg, natCast_nonpos_iff, toNat_neg_natCast, Nat.fib_zero,
    neg_neg, toNat_natCast, reduceNeg]
  split_ifs with hn h
  · simp [hn]
  · obtain ⟨a, rfl⟩ : Even n := by grind
    simp [← two_mul, Odd.neg_one_pow (Exists.intro a rfl)]
  · obtain ⟨a, rfl⟩ : Odd n := by grind
    simp [add_assoc, ← two_mul, ← mul_add_one]

theorem fib_add_two (n : ℤ) :
    fib (n + 2) = fib n + fib (n + 1) := by
  rcases n with (n | n)
  · dsimp
    rw [show (n : ℤ) + 2 = (n + 2 : ℕ) by rfl, fib_natCast, Nat.fib_add_two]
    rfl
  · rw [show negSucc n = -((n + 1 : ℕ) : ℤ) by rfl, fib_neg_natCast]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_natCast]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : ℤ)) := by grind
      _ = _ := by
        have : -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add]
          simp

theorem fib_eq_fib_add_two_sub_fib_add_one (n : ℤ) :
    fib n = fib (n + 2) - fib (n + 1) := by
  simp only [fib_add_two, add_sub_cancel_right]

theorem fib_add_one (n : ℤ) :
    fib (n + 1) = fib (n + 2) - fib n := by
  simp only [fib_add_two, add_sub_cancel_left]

@[simp] theorem fib_eq_zero {n : ℤ} :
    fib n = 0 ↔ n = 0 := by
  rcases n with (n | n)
  · simp
  · rw [show (negSucc n) = -((n + 1 : ℕ) : ℤ) by rfl, fib_neg_natCast]
    have : -1 + -(n : ℤ) = 0 ↔ (n : ℤ) = -1 := by grind
    simp [this]

theorem fib_natCast_add_natCast (m n : ℕ) :
    fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1) := by
  if hm : m = 0 then simp [hm] else
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  simp_rw [← natCast_add, ← natCast_add_one, add_assoc, add_comm,
    fib_natCast, ← add_assoc, Nat.fib_add]
  simp [add_comm]

-- TODO: `fib_natCast_sub_natCast`, `fib_add`, ...

end Int
