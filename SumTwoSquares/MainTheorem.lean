import Mathlib

open Nat

example (p : ℕ) (h : p ≡ 0 [MOD 2]) : ∃ n : ℕ, p = 2 * n := by
have hdiv: 2 ∣ p := Nat.modEq_zero_iff_dvd.1 h
rcases hdiv with ⟨n, hn⟩
use n

theorem p_not_2_is_odd (p : ℕ) (hP : Nat.Prime p) : p = 2 ↔ p ≡ 0 [MOD 2] := by
constructor
· intro h
  rw[h]
  norm_num
· intro h
  have hdiv : 2 ∣ p := Nat.modEq_zero_iff_dvd.1 h
  have h1 : 2∣ p → 2=1 ∨ 2= p := Nat.Prime.eq_one_or_self_of_dvd hP 2
  apply h1 at hdiv
  obtain h2 | h2 := hdiv
  · exfalso
    linarith
  · symm at h2
    exact h2


theorem residues_mod_n (a n : ℕ) (hn : n > 0) : ∃ m: ℕ, m < n ∧ a ≡ m [MOD n] := by
  use (a%n)
  constructor
  · apply Nat.mod_lt
    exact hn
  · rw[Nat.ModEq.comm]
    exact Nat.mod_modEq a n

theorem nums_le_2 (m : ℕ) (hm : m < 2) : m = 0 ∨ m = 1 := by
  cases m with
  | zero =>
      left; rfl
  | succ m =>
      have hm' : Nat.succ m < Nat.succ 1 := by
        simpa using hm
      have hm_less_than_1 : m < 1 := Nat.lt_of_succ_lt_succ hm'
      have m_equals_0 : m = 0 := by
        cases m with
        | zero => rfl
        | succ m => linarith
      right
      rw[m_equals_0]

theorem nums_le_4 (m : ℕ) (hm : m < 4) : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
  cases m with
  | zero =>
      left; rfl
  | succ m =>
      have hm' : Nat.succ m < Nat.succ 3 := by
        simpa using hm
      have hm_less_than_3 : m<3 := Nat.lt_of_succ_lt_succ hm'
      cases m with
      | zero =>
          right; left; rfl
      | succ m =>
          have hm'' : Nat.succ m < Nat.succ 2 := by
            simpa using hm_less_than_3
          have hm_less_than_2 : m < 2 := Nat.lt_of_succ_lt_succ hm''
          have h01 : m = 0 ∨ m = 1 := nums_le_2 m hm_less_than_2
          cases h01 with
          | inl h => right; right; left; rw[h]
          | inr h => right; right; right; rw[h]



example (m n : ℕ) (h : m + 1 < n + 1) : m < n := by
  simpa [Nat.succ_eq_add_one] using h


theorem odd_prime_1_or_3_mod_4 (p: ℕ ) (hP : Nat.Prime p) : p=2 ∨ p≡ 1 [MOD 4] ∨ p≡ 3 [MOD 4] := by
  by_cases h : (p=2)
  left
  exact h
  right
  have hodd : p % 2 = 1 := by
    by_contra h1


theorem squares_mod_4 (a:ℕ) : a^2 ≡ 0 [MOD 4] ∨ a^2 ≡ 1 [MOD 4] := by
rcases Nat.mod_four


theorem prime_sum_two_squares (p: ℕ ) [Fact p.Prime] : (∃ a b :ℤ, p = a^2 + b^2) ↔ p=2 ∨ p≡ 1 [MOD 4]  /- ↔ p splits in ℤ[i] -/  := by
constructor
intro hp
rcases hp with ⟨a,b,h1⟩
by_cases hP: (p=2)
  left
  exact h1
