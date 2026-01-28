import Mathlib

open Nat
open GaussianInt


--This lemma proves that for any natural number a and n>0, there is some representative of
-- a modulo n in the interval [0, n-1]
lemma residues_mod_n (a n : ℕ) (hn : n > 0) : ∃ m: ℕ, m < n ∧ a ≡ m [MOD n] := by
  use (a%n)
  constructor
  · apply Nat.mod_lt
    exact hn
  · rw[Nat.ModEq.comm]
    exact Nat.mod_modEq a n

--This lemma proves that the only natural numbers less than two are 0 and 1
lemma nums_le_2 (m : ℕ) (hm : m < 2) : m = 0 ∨ m = 1 := by
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

--This lemma proves that the only natural numbers less than 4 are 0,1,2, and 3
lemma nums_lt_4 (m : ℕ) (hm : m < 4) : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by
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

--This lemma proves that every prime is either 2,
--congruent to 1 modulo 4, or congruent to 3 modulo 4
lemma odd_prime_1_or_3_mod_4 (p : ℕ) [hp : Fact (Nat.Prime p)]
  : p=2 ∨ p≡ 1 [MOD 4] ∨ p≡ 3 [MOD 4] := by
  -- We break into cases based on whether p = 2 or p ≠ 2, the former case being trivial
  by_cases h : (p=2)
  · left
    exact h
  right
  · have hp4 : ∃ m : ℕ, m < 4 ∧ p ≡ m [MOD 4] := residues_mod_n p 4 (by norm_num)
    rcases hp4 with ⟨m, hm, heq⟩
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := nums_lt_4 m hm
    --Here we break into cases based on the possible residues of m modulo 4, where
    -- m is the representative of p modulo 4 in [0,3]
    cases hm4 with
    | inl h0 =>
        --We prove here that a prime cannot be congruent to 0 modulo 4 because otherwise 4 divides
        --it, and yet 4 is not prime
        exfalso
        rw[h0] at heq
        have hdiv: 4 ∣ p := Nat.modEq_zero_iff_dvd.1 heq
        have h4ne1 : 4 ≠ 1 := by norm_num
        have hpis4equiv : 4 ∣ p ↔ p=4 := by
          exact Nat.Prime.dvd_iff_eq (Fact.out : Nat.Prime p) h4ne1
        have h4notprime : ¬ Nat.Prime 4 := by norm_num
        apply h4notprime
        rw[hpis4equiv] at hdiv
        rw[← hdiv]
        exact (Fact.out : Nat.Prime p)
    | inr h123 =>
        cases h123 with
        | inl h1 =>
            --This case, p ≡ 1 [MOD 4] is trivial
            left
            rw[h1] at heq
            exact heq
        | inr h23 =>
            cases h23 with
            | inl h2 =>
                --Here we prove that a prime not 2 cannot be congruent to 2 modulo 4 by reducing
                --the assumption p ≡ 2 [MOD 4] to p ≡ 0 [MOD 2] and then deriving that p = 2
                exfalso
                rw[h2] at heq
                have h2div4 : 2 ∣ 4 := by norm_num
                have h2divpiff : 2 ∣ p ↔ 2 ∣ 2 := by exact Nat.ModEq.dvd_iff heq h2div4
                apply h
                have h2notprime : 2 ≠ 1 := by norm_num
                have h2divpiffpis2 : 2 ∣ p ↔ p=2 := by
                  exact Nat.Prime.dvd_iff_eq (Fact.out : Nat.Prime p) h2notprime
                rw[← h2divpiffpis2]
                rw[h2divpiff]
            | inr h3 =>
                --Again, this case p ≡ 3 [MOD 4] is trivial
                right
                rw[h3] at heq
                exact heq




--This lemma classifies 0 and 1 being the only possible residues of a square modulo 4
lemma squares_mod_4 (a : ℕ) : a^2 ≡ 0 [MOD 4] ∨ a^2 ≡ 1 [MOD 4] := by
  have hp4 : ∃ m : ℕ, m < 4 ∧ a ≡ m [MOD 4] := residues_mod_n a 4 (by norm_num)
  rcases hp4 with ⟨m, hm, heq⟩
  have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := nums_lt_4 m hm
  have hpow : a^2 ≡ m^2 [MOD 4] := by exact Nat.ModEq.pow 2 heq
  --Here we just break into cases based on which number in [0,3] represents a modulo 4
  cases hm4 with
  | inl h0 =>
      rw[h0] at hpow
      left
      exact hpow
  | inr h123 =>
      cases h123 with
      | inl h1 =>
          rw[h1] at hpow
          right
          exact hpow
      | inr h23 =>
          cases h23 with
          | inl h2 =>
              rw[h2] at hpow
              left
              exact hpow
          | inr h3 =>
              rw[h3] at hpow
              right
              exact hpow

--This lemma classifies 0,1, and 2 as the only possible residues of the sum of two squares
--modulo 4. This is just by a simple case division with the above lemma
lemma sum_of_squares_mod_4 (a b : ℕ) :
    a^2 + b^2 ≡ 0 [MOD 4] ∨ a^2 + b^2 ≡ 1 [MOD 4] ∨
    a^2 + b^2 ≡ 2 [MOD 4] := by
  have ha : a^2 ≡ 0 [MOD 4] ∨ a^2 ≡ 1 [MOD 4] := squares_mod_4 a
  have hb : b^2 ≡ 0 [MOD 4] ∨ b^2 ≡ 1 [MOD 4] := squares_mod_4 b
  cases ha with
  | inl ha0 =>
      cases hb with
      | inl hb0 =>
          left
          have hsum : a^2 + b^2 ≡ 0 + 0 [MOD 4] := by exact Nat.ModEq.add ha0 hb0
          rw[zero_add] at hsum
          exact hsum
      | inr hb1 =>
          right
          left
          have hsum : a^2 + b^2 ≡ 0 + 1 [MOD 4] := by exact Nat.ModEq.add ha0 hb1
          rw[zero_add] at hsum
          exact hsum
  | inr ha1 =>
      cases hb with
      | inl hb0 =>
          right
          left
          have hsum : a^2 + b^2 ≡ 1 + 0 [MOD 4] := by exact Nat.ModEq.add ha1 hb0
          rw[add_zero] at hsum
          exact hsum
      | inr hb1 =>
          right
          right
          have hsum : a^2 + b^2 ≡ 1 + 1 [MOD 4] := by exact Nat.ModEq.add ha1 hb1
          exact hsum

--This theorem gives a classification for when an integer can be written as the sum of two
--integer squares in terms of the Gaussian integers
theorem sum_two_int_squares_iff_gaussian_norm (n : ℕ) :
  (∃ a b : ℤ , n = a^2 + b^2) ↔
  (∃ z : GaussianInt, n = Zsqrtd.norm z) := by
  constructor
  · --For the forward direction the idea is to use z = a+bi
    intro h
    rcases h with ⟨a,b,hab⟩
    use ((⟨(a : ℤ), (b : ℤ)⟩) : GaussianInt)
    rw[hab]
    rw[Zsqrtd.norm_def]
    simp
    simp[pow_two]
  · --For the backward direction, if n = z.norm and z = a+bi, then a^2+b^2 = n by definition
    intro h
    rcases h with ⟨z, hz⟩
    use z.re, z.im
    rw[hz]
    rw[Zsqrtd.norm_def]
    simp
    simp[pow_two]

--This lemma says that for a nonnegative integer n, casting n as a natural number and then back
--to an integer does not change the value of n
lemma to_nat_to_int_ge_0 (n : ℤ) (hn : 0 ≤ n) : Int.ofNat n.toNat = n := by
  simp only [Int.ofNat_eq_natCast, Int.ofNat_toNat, sup_eq_left]
  exact hn


--This lemma states that for an integer n and natural numbers a and b,
--if n=a^2+b^2 as integers, then
-- n = a^2 + b^2 as natural numbers.
lemma sum_of_squares_to_nat (n : ℕ) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Int.ofNat n = a^2 + b^2 → n = a.toNat^2 + b.toNat^2 := by
  intro h
  have myh : (Int.ofNat n).toNat = (a^2+b^2).toNat := by
    rw[h]
  have hnge0 : n ≥ 0 := by
    exact Nat.zero_le n
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at myh
  rw[myh]
  have ha2 : 0 ≤ a^2 := Int.sq_nonnneg a
  have hb2 : 0 ≤ b^2 := Int.sq_nonnneg b
  have ha2b2 : (a^2+b^2).toNat = (a^2).toNat + (b^2).toNat := Int.toNat_add ha2 hb2
  rw[ha2b2]
  rw[Int.toNat_pow_of_nonneg ha 2, Int.toNat_pow_of_nonneg hb 2]


--This lemma proves that a natural number can be written as the sum of two integer squares
--iff it can be written as the sum of two natural number squares
lemma sum_two_squares_Z_iff_N (n : ℕ) :
  (∃ a b : ℤ, n = a^2 + b^2) ↔
  (∃ c d : ℕ, n = c^2 + d^2) := by
  constructor
  · --The idea is to consider whether a and b are negative or not, and negate them accordingly
     -- and cast the result as a natural number. The reverse direction is easy
    intro h
    rcases h with ⟨a,b,hab⟩
    by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · use a.toNat, b.toNat
        apply sum_of_squares_to_nat n a b ha hb
        exact hab
      · use a.toNat, (-b).toNat
        simp only [not_le] at hb
        have hnb_pos : 0 ≤ -b := by
          simp only [Int.neg_nonneg]
          exact Int.le_of_lt hb
        apply sum_of_squares_to_nat n a (-b) ha hnb_pos
        simp only [Int.ofNat_eq_natCast, even_two, Even.neg_pow]
        exact hab
    · by_cases hb : 0 ≤ b
      · use (-a).toNat, b.toNat
        simp only [not_le] at ha
        have hna_pos : 0 ≤ -a := by
          simp only [Int.neg_nonneg]
          exact Int.le_of_lt ha
        apply sum_of_squares_to_nat n (-a) b hna_pos hb
        simp only [Int.ofNat_eq_natCast, even_two, Even.neg_pow]
        exact hab
      · use (-a).toNat, (-b).toNat
        simp only [not_le] at ha
        simp only [not_le] at hb
        have hna_pos : 0 ≤ -a := by
          simp only [Int.neg_nonneg]
          exact Int.le_of_lt ha
        have hnb_pos : 0 ≤ -b := by
          simp only [Int.neg_nonneg]
          exact Int.le_of_lt hb
        apply sum_of_squares_to_nat n (-a) (-b) hna_pos hnb_pos
        simp only [Int.ofNat_eq_natCast, even_two, Even.neg_pow]
        exact hab
  · intro h
    rcases h with ⟨c,d,hcd⟩
    use Int.ofNat c, Int.ofNat d
    rw[hcd]
    exact ToInt.add_congr rfl rfl

--We prove that for a Gaussian integer z and an integer n, n (viewed as an integer)
--is the norm of z iff n is the norm of z (viewed as a natural number)
lemma gaussian_norms_are_nat (z : GaussianInt) (n : ℕ)
    : n = Zsqrtd.norm z ↔ n = (Zsqrtd.norm z).toNat := by
  constructor
  · intro h
    rw[← h]
    exact Eq.symm (Int.toNat_natCast n)
  · intro h
    rw[h]
    have myh : 0 ≤ Zsqrtd.norm z := GaussianInt.norm_nonneg z
    have h' : ↑(Zsqrtd.norm z).toNat = Int.ofNat (Zsqrtd.norm z).toNat := by rfl
    rw[h']
    rw[to_nat_to_int_ge_0 (Zsqrtd.norm z) myh]

--We combine our above lemmas with our theorem to get the result without any mathematical depth
lemma sum_two_nat_squares_iff_gaussian_norm (n : ℕ) :
  (∃ a b : ℕ, n = a^2 + b^2) ↔
  (∃ z : GaussianInt, n = (Zsqrtd.norm z).toNat) := by
  constructor
  · intro h
    have h' :
     (∃ a b : ℕ, n = a^2 + b^2) → (∃ c d : ℤ, n = c^2 + d^2) := (sum_two_squares_Z_iff_N n).mpr
    apply h' at h
    apply (sum_two_int_squares_iff_gaussian_norm n).mp at h
    rcases h with ⟨z, hz⟩
    use z
    rw[← gaussian_norms_are_nat z n]
    exact hz
  · intro h
    rcases h with ⟨z, hz⟩
    rw[← gaussian_norms_are_nat z n] at hz
    have myh : (∃ z : GaussianInt, n = z.norm) → ∃ a b : ℤ, n = a^2 + b^2
    := (sum_two_int_squares_iff_gaussian_norm n).mpr
    have myh' : ∃ a b : ℤ, n = a^2 + b^2 := by
      apply myh
      use z
    apply (sum_two_squares_Z_iff_N n).mp
    exact myh'



-- This lemma's syntax was partially guided with AI assistance
-- Here we lift a root of the polynomial X^2+1 over  𝔽_p to a root of the polynomial
-- X^2+1 over ℤ modulo p. The idea is just to use any lift of a root in 𝔽_p
lemma lift_y2_plus_1 (p : ℕ) [Fact (Nat.Prime p)]
  (y : ZMod p) (hy : y ^ 2 + 1 = 0) :
  ∃ x : ℕ, p ∣ x^2 + 1 := by
    refine ⟨y.val, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (y.val^2+1) p).mp
    simp only [cast_add, cast_pow, ZMod.natCast_val, ZMod.cast_id', id_eq, cast_one]
    exact hy

-- This lemma's syntax was partially guided with AI assistance
-- We prove that if p = 1+ 4* t, then p/2 = 2*t, which is, in particular, even
lemma half_of_one_add_four_mul
  (p t : ℕ) (ht : p = 1 + 4 * t) :
  p / 2 = 2 * t := by
  subst ht
  calc
    (1 + 4 * t) / 2
        = (1 + 2 * (2 * t)) / 2 := by ring_nf
    _   = 1 / 2 + 2 * t := by
          have h0less2 : 0 < 2 := by norm_num
          simpa using Nat.add_mul_div_left 1 (2 * t) h0less2
    _   = 2 * t := by simp



--Here we show that for any prime congruent to 1 modulo 4, p must divide x^2+1 for some number x
theorem primes_w_neg1_square (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 1 [MOD 4])
 : ∃ x : ℕ, p ∣ x^2+1 := by
  have hn1 : (-1 : ZMod p) ≠ (0 : ZMod p) := by
    norm_num
  --This assumption, that -1 is a square modulo p iff (-1)^(p/2) = 1 is easy to prove with the
  --exact sequence of abelian groups 0 → 𝔽_p^* → 𝔽_p^* → {± 1} → 0, where the second
  -- arrow is just the map x↦x^2 and the third is x ↦ x^(p/2) (recalling p/2 = (p-1)/2).
  --Alternitively, one can prove the primitive root theorem, that the multiplicative group
  --of 𝔽_p is cyclic, and prove the claim directly from this.
  --However, since it's in MathLib, I see no need to reprove this
  have h1 : (-1 : ZMod p)^(p/2) = 1 → IsSquare (-1 : ZMod p) := by
    exact (ZMod.euler_criterion p hn1).mpr
  have h1lep : 1 ≤ p := by exact NeZero.one_le
  have eucl_alg : ∃ t : ℕ, p = 1 + 4*t := by
    apply (Nat.modEq_iff_exists_eq_add h1lep).mp
    apply Nat.ModEq.symm
    exact hpmod4
  rcases eucl_alg with ⟨t, ht⟩
  have hpover2 : p / 2 = 2 * t := half_of_one_add_four_mul p t ht
  --We prove that -1 is a square modulo p by using h1 to prove instead that (-1)^(p/2) =1, which is
  -- an easy computation by our lemma that tells us p/2 = 2*t for some t
  have h2 : IsSquare (-1 : ZMod p) := by
    apply h1
    rw[hpover2]
    norm_num
  rcases h2 with ⟨y, hy⟩
  symm at hy
  rw[Eq.symm (pow_two y)] at hy
  have myh : y^2+1 = 0 := by
    rw[hy]
    norm_num
  --Finally, we lift our constructedroot of y^2+1=0 in 𝔽_p to an integer root modulo p
  exact lift_y2_plus_1 p y myh

--We do not need this result to prove our classification of when primes can be written
--as the sum of two squares, only for later results
theorem primes_wo_neg1_square (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 3 [MOD 4])
  : ¬ IsSquare (-1 : ZMod p) := by
  have hn1 : (-1 : ZMod p) ≠ (0 : ZMod p) := by
    norm_num
  have hprime2 : Nat.Prime 2 := by exact prime_two
  have hpm2implpis2 (n : ℕ ): n ∣ 2 → n = 1 ∨ n = 2 := by
    by_cases h : n = 1
    · intro hyp
      left
      exact h
    · intro hyp
      right
      symm
      rw[← Nat.Prime.dvd_iff_eq hprime2 h]
      exact hyp
  have h2lep : 2 ≤ p := (Nat.Prime.two_le (by
  exact (Fact.out : Nat.Prime p)))
  have h2nep : p ≠ 2 := by
    by_contra c
    rw[c] at hpmod4
    cases hpmod4
  --We need this inequality to get a lift to the natural numbers of p = 3+4*t.
  --The logic is just to use case division repeatedly and the result that 2 ≤ p
  have h3lep : 3 ≤ p := by
    cases p with
    | zero =>
        simp at h2lep
    | succ p =>
      cases p with
      | zero =>
        simp at h2lep
      | succ p =>
        have : (Nat.succ (Nat.succ p)) ≠ 2 := by
          simpa using h2nep
        cases p with
        | zero =>
            cases this rfl
        | succ p =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le p)))
  have eucl_alg : ∃ t : ℕ, p = 3 + 4*t := by
    apply (Nat.modEq_iff_exists_eq_add h3lep).mp
    apply Nat.ModEq.symm
    exact hpmod4
  rcases eucl_alg with ⟨t, ht⟩
  --Here we use the forwards direction of the criterion -1 is a square modulo p
  -- iff (-1)^(p/2) = 1 in ZMod p
  have h1 : IsSquare (-1 : ZMod p) → (-1 : ZMod p)^(p/2) = 1 := by
    exact (ZMod.euler_criterion p hn1).mp
  --We assume for a contradiction that -1 is a square modulo p
  by_contra c
  apply h1 at c
  have hpover2 : p/2 = 1 + 2*t := by
    rw[ht]
    --This tactic will turn our goal (3+4*t)/2 = 1+2*t into two two subgoals,
    --(1 + 2 * t) * 2 ≤ 3 + 4 * t first and 3 + 4 * t < (1 + 2 * t + 1) * 2 second.
    --These goals are just by simplifying each expression
    refine Nat.div_eq_of_lt_le ?_ ?_
    · have : (1+2*t)*2 = 2 + 4* t := by
        rw[add_mul 1 (2*t) 2]
        norm_num
        rw[mul_comm, ← mul_assoc]
        simp
      rw[this]
      have : 3 + 4*t = 1 + (2+4*t) := by
        have : 3 = 1 + 2 := by norm_num
        rw[this, add_assoc]
      rw[this]
      exact Nat.le_add_left (2 + 4 * t) 1
    · have : 1 + 2*t + 1 = 2 +2* t := by
        rw[add_comm, ← add_assoc]
      rw[this]
      have : (2+2*t)*2 = 2*2 + (2*t)*2 := Nat.add_mul 2 (2 * t) 2
      simp only [reduceMul] at this
      have hyp: 2*t*2 = 4*t := by
        rw[mul_comm, ← mul_assoc]
        simp only [reduceMul]
      rw[hyp] at this
      rw[this]
      have : 4 = 1+3 := by norm_num
      nth_rewrite 2[this]
      rw[add_assoc]
      exact lt_one_add (3 + 4 * t)
  rw[hpover2] at c
  have : (-1 : ZMod p)^(1 + 2 * t) = (-1 : ZMod p)^1 * (-1)^(2*t) := pow_add (-1) 1 (2 * t)
  rw[this] at c
  simp only [pow_one, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_one] at c
  have h2 : (2 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => x + 1) c
    simp only [neg_add_cancel] at this
    symm
    have h2isoneplusone : (1 : ZMod p)+1=2 := by norm_num
    rw[h2isoneplusone] at this
    exact this
  have hpdiv2 : p ∣ 2 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).mp
    exact h2
  apply hpm2implpis2 at hpdiv2
  --To show ¬(p = 1 ∨ p = 2) is easy by our assumption that p ≡ 3 [MOD 4]
  cases hpdiv2 with
  | inl h =>
    rw[h] at hpmod4
    cases hpmod4
  | inr h =>
    rw[h] at hpmod4
    cases hpmod4



--Simple transfer of the symbol ≡ to the symbol %
lemma mod4_rw (n : ℕ) (hn : n ≡ 1 [MOD 4]) : n%4=1 := by
  exact Eq.symm (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (ModEq.symm hn))) n))


--The lemmas here are all just helper lemmas for the result on primes being the sum of two squares
lemma contra_via_unit_irreducible (p : ℤ) (hirr : Irreducible p) :
    ¬ (p ∣ 1) := by
  intro h
  have hpunit : IsUnit (p : ℤ) := by
    rcases h with ⟨d, hd⟩
    refine ⟨⟨(p : ℤ), d, ?_, ?_⟩, rfl⟩
    · symm at hd
      exact hd
    · rw[Int.mul_comm] at hd
      symm
      exact hd
  exact (hirr.not_isUnit hpunit)

-- This theorem was partially guided with AI assistance
lemma contra_via_prime_div_1
(p : ℕ) [Fact (Nat.Prime p)] (hdiv : (p : ℤ) ∣ 1) : False := by
  have hprime : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hnotdiv1 : ¬ (p : ℤ) ∣ 1 := contra_via_unit_irreducible (p : ℤ) (hprime.irreducible)
  exact hnotdiv1 hdiv

lemma contra_via_unit_irreducible_neg_1 (p : ℤ) (hirr : Irreducible p) :
  ¬ (p ∣ -1) := by
intro h
have hpunit : IsUnit (p : ℤ) := by
  rcases h with ⟨d, hd⟩
  refine ⟨⟨(p : ℤ), (-d), ?_, ?_⟩, rfl⟩
  · simp only [mul_neg]
    rw[← hd]
    norm_num
  · simp only [neg_mul]
    rw[mul_comm]
    rw[← hd]
    norm_num
exact (hirr.not_isUnit hpunit)


lemma contra_via_prime_div_neg_1
(p : ℕ) [Fact (Nat.Prime p)] (hdiv : (p : ℤ) ∣ -1) : False := by
have hprime : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
have hnotdiv1 : ¬ (p : ℤ) ∣ -1 := contra_via_unit_irreducible_neg_1 (p : ℤ) (hprime.irreducible)
exact hnotdiv1 hdiv

--Here is the first major result--a prime can be written as the sum of two squares iff it is 2
--or 1 modulo 4
theorem prime_sum_two_squares (p : ℕ) [Fact (Nat.Prime p)] :
 (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ p = 2 ∨ p ≡ 1 [MOD 4] := by
  --We break into proving each direction of the claim
  constructor
  · intro h
    rcases h with ⟨a,b,hab⟩
    have hpmod4 :
    p = 2 ∨ p ≡ 1 [MOD 4] ∨ p ≡ 3 [MOD 4] := odd_prime_1_or_3_mod_4 p
    --Here we do case division on p = 2 ∨ p ≡ 1 [MOD 4] ∨ p ≡ 3 [MOD 4]
    cases hpmod4 with
    | inl h2 => left; exact h2
    | inr h1or3 =>
        cases h1or3 with
        | inl h1 => right; exact h1
        | inr h3 =>
            --Here is the only mathematical depth in this direction: if p ≡ 3 [MOD 4],
            --then p is not the sum of two squares. This is easy by our previous result
            --that says sums of two squares are 0,1, or 2 modulo 4
            exfalso
            have hsum3 : 3 ≡ a^2 + b^2 [MOD 4] := by
              rw[hab] at h3
              apply Nat.ModEq.symm at h3
              exact h3
            have hsum012 :
            a^2 + b^2 ≡ 0 [MOD 4]
            ∨ a^2 + b^2 ≡ 1 [MOD 4]
            ∨ a^2 + b^2 ≡ 2 [MOD 4] := sum_of_squares_mod_4 a b
            cases hsum012 with
            | inl h0 =>
                have h3equiv0 : 3 ≡ 0 [MOD 4] := by exact Nat.ModEq.trans hsum3 h0
                have myh : ¬ 3 ≡ 0 [MOD 4] := by norm_num
                apply myh
                exact h3equiv0
            | inr h1or2 =>
                cases h1or2 with
                | inl h1 =>
                    have h3equiv1 : 3 ≡ 1 [MOD 4] := by exact Nat.ModEq.trans hsum3 h1
                    have myh : ¬ 3 ≡ 1 [MOD 4] := by norm_num
                    apply myh
                    exact h3equiv1
                | inr h2 =>
                    have h3equiv2 : 3 ≡ 2 [MOD 4] := by exact Nat.ModEq.trans hsum3 h2
                    have myh : ¬ 3 ≡ 2 [MOD 4] := by norm_num
                    apply myh
                    exact h3equiv2
  · intro h
    --We must now show that if p=2 or p ≡ 1 [MOD 4], then p is the sum of two squares
    -- The case p=2 is trivial. If p ≡ 1 [MOD 4], we know from earlier work that
    -- p ∣ x^2 + 1. The key insight is that x^2+1 = (x+i)(x-i). We can show that
    -- p as a Gaussian integer does not divide either factor, so p cannot be prime.
    -- We use the fact that irreducible implies prime for UFD's to conclude that p
    -- is not irreducible as a Gaussian integer, so there exist non-units a b such that
    -- p = a * b. Thus p^2 = p.norm = (a*b).norm = a.norm * b.norm.
    --We use the equivalence of being a unit with having norm 1 to see that neither a.norm
    -- nor b.norm can be equal to 1. In particular, it follows that a.norm = p as desired by our
    --equivalent classification of when integers can be written as the sum of two squares
    obtain h2 | h1mod4 := h
    · use 1, 1
      norm_num
      exact h2
    · apply (sum_two_nat_squares_iff_gaussian_norm p).mpr
      have pdivx2plus1 : ∃ x : ℕ, p ∣ x^2 + 1 := primes_w_neg1_square p h1mod4
      rcases pdivx2plus1 with ⟨x, hx⟩
      have div_gaussian_int: ↑p ∣ ((x ^ 2 + 1 : ℕ) : GaussianInt) := by
        simpa using cast_dvd_cast hx
      let y : GaussianInt := { re := (x : ℤ), im := (1 : ℤ) }
      have hre_y : y.re = (x : ℤ) := by simp [y]
      have him_y : y.im = (1 : ℤ) := by simp [y]
      have hre_star_y : (star y).re = (x : ℤ) := by simp [y, star]
      have him_star_y : (star y).im = (-1 : ℤ) := by simp [y, star]
      have newrw : ((x ^ 2 + 1 : ℕ) : GaussianInt) = (y.norm : GaussianInt) := by
        simp [y, Zsqrtd.norm_def, pow_two]
      rw[newrw] at div_gaussian_int
      have newnewrw : (y.norm : GaussianInt) = y * star y := by
        exact Zsqrtd.norm_eq_mul_conj y
      rw[newnewrw] at div_gaussian_int
      have h1 : ¬ ↑p ∣ y := by
        by_contra hdiv
        have hdiv_re_im : (p : ℤ) ∣ y.re ∧ (p : ℤ) ∣ y.im := by
          apply (Zsqrtd.intCast_dvd p y).mp at hdiv
          exact hdiv
        rw[hre_y, him_y] at hdiv_re_im
        have myh : (p : ℤ) ∣ (1 : ℤ) := hdiv_re_im.2
        exact contra_via_prime_div_1 p myh
      have h2 : ¬ ↑p ∣ star y := by
        by_contra hdiv
        have hdiv_re_im : (p : ℤ) ∣ (star y).re ∧ (p : ℤ) ∣ (star y).im := by
          apply (Zsqrtd.intCast_dvd p (star y)).mp at hdiv
          exact hdiv
        rw[hre_star_y, him_star_y] at hdiv_re_im
        have myh : (p : ℤ) ∣ (-1 : ℤ) := hdiv_re_im.2
        exact contra_via_prime_div_neg_1 p myh
      have not_prime_p : ¬ _root_.Prime (p : GaussianInt) := by
        intro hpPrime
        rcases hpPrime with ⟨hp_ne_one, hp_mul⟩
        have : (p : GaussianInt) ∣ y ∨ (p : GaussianInt) ∣ star y := by
          apply hp_mul.2
          exact div_gaussian_int
        cases this with
        | inl hdiv_y =>
            exact h1 hdiv_y
        | inr hdiv_star_y =>
            exact h2 hdiv_star_y
      have not_irred_p : ¬ Irreducible (p : GaussianInt) := by
        intro hirr
        apply _root_.irreducible_iff_prime.mp at hirr
        exact not_prime_p hirr
      rw[irreducible_iff] at not_irred_p
      have hnormp2 : (p : GaussianInt).norm = p^2 := by
          rw[Zsqrtd.norm_natCast p]
          ring
      have not_unit_p : ¬ IsUnit (p : GaussianInt) := by
        intro hunit
        have hnorm1 : (p : GaussianInt).norm.natAbs = 1 := by
          apply Zsqrtd.norm_eq_one_iff.mpr
          exact hunit
        rw[hnormp2] at hnorm1
        simp only [Int.natAbs_pow, Int.natAbs_natCast, IsMulTorsionFree.pow_eq_one_iff,
          OfNat.ofNat_ne_zero, or_false] at hnorm1
        cases (Fact.out : Nat.Prime p).ne_one hnorm1
      have not_forall_ab :
      ¬(∀ a b : GaussianInt, (p : GaussianInt) = a * b → IsUnit a ∨ IsUnit b) := by
        intro hforall
        apply not_irred_p
        constructor
        · exact not_unit_p
        · exact hforall
      have not_forall_eq :
      ∃ a b : GaussianInt, ¬ ((p : GaussianInt) = a * b → IsUnit a ∨ IsUnit b):= by
        simpa [not_forall] using not_forall_ab
      rcases not_forall_eq with ⟨a,b,hab⟩
      rw[Classical.not_imp, not_or] at hab
      have habnorm : a.norm * b.norm = p ^ 2 := by
        rw[← Zsqrtd.norm_mul a b]
        rw[← hnormp2]
        rw[hab.1]
      use a
      have hnormage0 : 0≤ a.norm := GaussianInt.norm_nonneg a
      have hnormbge0 : 0≤ b.norm := GaussianInt.norm_nonneg b
      have hnormane1 : a.norm ≠ 1 := by
        have idk : -1 ≤ 0 := by norm_num
        by_contra h
        apply (hab.2).1
        apply (Zsqrtd.norm_eq_one_iff' idk a).mp
        exact h
      have hnormbne1 : b.norm ≠ 1 := by
        have idk : -1 ≤ 0 := by norm_num
        by_contra h
        apply (hab.2).2
        apply (Zsqrtd.norm_eq_one_iff' idk b).mp
        exact h
      have convert_to_Nat_not_1 (n : ℤ) : n ≠ 1 → n.toNat ≠ (1 : ℕ) := by
        intro hn_ne1 hn_toNat
        have hn_eq1 : n = 1 := by
          cases n with
          | ofNat k =>
              have hk : k = 1 := by simpa using hn_toNat
              simp [hk]
          | negSucc k =>
              have : False := by
                simp at hn_toNat
              exact False.elim this
        exact hn_ne1 hn_eq1
      apply convert_to_Nat_not_1 a.norm at hnormane1
      apply convert_to_Nat_not_1 b.norm at hnormbne1
      have to_Z_square_back (n : ℕ) : ((n : ℤ)^2).toNat = n^2 := by
        exact Nat.add_zero (NatPow.pow n 2)
      --appologies for naming conventions from this point forward in this proof--it was some time
      -- between 3 and 6 a.m. after having spent the entire day working on this proof and I had
      -- very little remaining brain function. However, now I think they're funny so I don't care
      -- to update the names now
      have sumthin : (Zsqrtd.norm a * Zsqrtd.norm b).toNat = ((p: ℤ) ^ 2).toNat := by
        rw[habnorm]
      rw[to_Z_square_back p] at sumthin
      have somethink (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
        exact Int.toNat_mul ha hb
      have idk : p ^ 2 = (a.norm).toNat * (b.norm).toNat := by
        rw[← sumthin]
        rw [somethink (a.norm) (b.norm) hnormage0 hnormbge0]
      have final_prop :
      (a.norm).toNat * (b.norm).toNat = p^2 → (a.norm).toNat = p ∧ (b.norm).toNat = p := by
        exact (Nat.Prime.mul_eq_prime_sq_iff (Fact.out : Nat.Prime p) hnormane1 hnormbne1).mp
      symm at idk
      apply final_prop at idk
      symm
      exact idk.left

/-- This function counts the total number of prime divisors of n congruent to 3 mod 4, counting
multiplicities. This is used to do induction later on. -/
def countPrimeFactorsMod4Eq3 (n : ℕ) : ℕ :=
  ∑ p ∈ (n.primeFactors).filter (fun p => p % 4 = 3),
    n.factorization p


--This is a key ingredient in the proof of the forward direction of the main theorem, allowing us to
--do strong induction on countPrimeFactorsMod4Eq3, because we can divide n by p^2 if there is any
--prime factor congruent to 3 modulo 4 dividing n, apply the inductive hypothesis to n/p^2, and
--translate the conclusion back to n
theorem sum_two_squares_descent
(n p a b : ℕ) [Fact (Nat.Prime p)] (hdiv : p ∣ n) (hp : p ≡ 3 [MOD 4]) (hab : n = a ^ 2 + b ^ 2) :
p ^ 2 ∣ n ∧ p ∣ a ∧ p ∣ b := by
  --First we translate the hypotheses to 𝔽_p where we can do algebra
  have hn0: n ≡ 0 [MOD p] := modEq_zero_iff_dvd.mpr hdiv
  rw [hab] at hn0
  have ha2b20modp: (a : ZMod p)^2 + (b : ZMod p)^2 = 0 := by
    rw[← ZMod.natCast_eq_natCast_iff (a^2+b^2) 0 p] at hn0
    simpa only [cast_add, cast_pow, cast_zero] using hn0
  --Now that a^2+b^2 = 0 in 𝔽_p, we will do a case division on a = 0 in 𝔽_p, with the first case
  --giving the conclusion easily, and the second resulting in a contradiction
  by_cases ha0 : (a : ZMod p) = 0
  · rw[ha0] at ha2b20modp
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      pow_eq_zero_iff] at ha2b20modp
    have hpdiva : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp ha0
    have hpdivb : p ∣ b := (ZMod.natCast_eq_zero_iff b p).mp ha2b20modp
    have harewrite : ∃ c : ℕ, a = p * c := Stream'.mem_iff_exists_get_eq.mp hpdiva
    have hbrewrite : ∃ d : ℕ, b = p * d := Stream'.mem_iff_exists_get_eq.mp hpdivb
    rcases harewrite with ⟨c, hc⟩
    rcases hbrewrite with ⟨d, hd⟩
    rw[hd, hc] at hab
    have hyp1: (p*c)^2 = p^2 * c^2 := Nat.mul_pow p c 2
    have hyp2: (p*d)^2 = p^2 * d^2 :=  Nat.mul_pow p d 2
    have hyp3 : p^2*c^2 + p^2*d^2 = p^2*(c^2 + d^2) :=
      Eq.symm (Nat.mul_add (p ^ 2) (c ^ 2) (d ^ 2))
    rw[hyp1, hyp2, hyp3] at hab
    constructor
    · exact Dvd.intro (c ^ 2 + d ^ 2) (id (Eq.symm hab))
    · constructor
      · exact hpdiva
      · exact hpdivb
  · exfalso
    --Essentially, the contradiction will arrive by multiplying by a^-2 and simplifying,
    --to conclude that -1 is a square modulo p, but p ≡ 3 [MOD 4], which contradicts our
    --previous results
    have haainv : (a : ZMod p) * ((a : ZMod p)⁻¹) = 1 := by
      simpa only using (mul_inv_cancel₀ (a := (a : ZMod p)) ha0)
    have hintroainv: ((a : ZMod p)⁻¹)^2 * ((a : ZMod p)^2 + (b : ZMod p)^2) = 0 := by
      simp only [inv_pow, _root_.mul_eq_zero, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff]
      right
      exact ha2b20modp
    rw[mul_add (((a : ZMod p)⁻¹)^2) ((a : ZMod p)^2) ((b : ZMod p)^2)] at hintroainv
    have : (((a : ZMod p)⁻¹)^2) = ((a : ZMod p)^2)⁻¹ := by
      simpa only using (inv_pow (a : ZMod p) 2)
    nth_rewrite 1 [this] at hintroainv
    have hsq_ne0 : ((a : ZMod p)^2) ≠ 0 := by
      exact pow_ne_zero 2 ha0
    have : ((a : ZMod p)^2)⁻¹ * ((a : ZMod p)^2) = 1 := by
      simpa only using (inv_mul_cancel₀ (a := ((a : ZMod p)^2)) hsq_ne0)
    rw[this] at hintroainv
    have : (a : ZMod p)⁻¹ ^ 2 * (b : ZMod p) ^ 2
      = ((a : ZMod p)⁻¹ * (b : ZMod p))^2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_pow ((a : ZMod p)⁻¹) (b : ZMod p) 2).symm
    rw[this] at hintroainv
    have hnewgoal : (-1 : ZMod p) + (1 + ((↑a)⁻¹ * ↑b) ^ 2) = -1 := add_eq_left.mpr hintroainv
    simp only [neg_add_cancel_left] at hnewgoal
    have hissquareneg1 : IsSquare (-1 : ZMod p) := by
      refine (isSquare_iff_exists_mul_self (-1)).mpr ?_
      use ((↑a)⁻¹ * ↑b)
      symm
      have : (a : ZMod p)⁻¹ * ↑b * ((↑a)⁻¹ * ↑b) = ((↑a)⁻¹ * ↑b)^2 := by
        simp [pow_two, mul_left_comm, mul_comm]
      rw[this]
      exact hnewgoal
    have : ¬ IsSquare (-1 : ZMod p) := primes_wo_neg1_square p hp
    tauto


--This lemma just tells us what the prime factorization of n is in terms of the prime factorization
-- of n/p^2
lemma factorization_after_div_by_p2
(n p m : ℕ) (hp : Nat.Prime p) (hnpm : n = p ^ 2 * m) (hnn0 : n ≠ 0) :
(m.factorization p )+2= n.factorization p ∧ (∀ q ≠ p, m.factorization q = n.factorization q) := by
  have hpn0 : p ≠ 0 := Nat.Prime.ne_zero hp
  have hp2n0 : p^2 ≠ 0 := by exact pow_ne_zero 2 hpn0
  have hmn0 : m ≠ 0 := by
    by_contra c
    rw[hnpm,c ] at hnn0
    have : p^2 * 0 = 0 := Nat.mul_zero (p ^ 2)
    rw[this] at hnn0
    apply hnn0
    rfl
  have hfactorizationrw: (n.factorization = m.factorization + 2 • p.factorization) := by
    rw[hnpm]
    rw[Nat.factorization_mul hp2n0 hmn0, factorization_pow, add_comm]
  have hrwat2 (q : ℕ) :
  (m.factorization + 2 • p.factorization) q = m.factorization q + 2 • p.factorization q :=
  Nat.add_zero ((m.factorization q).add ((2 • p.factorization) q))
  --Now we break into the cases for our goal, computing the multiplicity of p as a prime factor and
  --that of all other primes
  constructor
  · rw[← hfactorizationrw] at hrwat2
    rw[hrwat2]
    have : p.factorization p = 1 := Prime.factorization_self hp
    rw[this]
    simp only [smul_eq_mul, mul_one]
  · intro q hq
    rw[hfactorizationrw, hrwat2]
    have : p.factorization q = 0 := by
      by_cases h : q = 1
      · rw[h]
        exact factorization_one_right p
      · have : ¬ q ∣ p := by
          rw[Nat.Prime.dvd_iff_eq]
          · tauto
          · exact hp
          · exact h
        exact factorization_eq_zero_of_not_dvd this
    rw[this]
    simp only [nsmul_zero, add_zero]




/-- The forward direction of our main theorem. We use this definition simply for
ease of notation. -/
def P (n : ℕ) : Prop :=
  (∃ a b : ℕ, n = a^2 + b^2) →
    ∀ p, Nat.Prime p →  (p ≡ 3 [MOD 4] → Even (n.factorization p))


--Here we just prove that the sum of a function f over a Finset s is equal to the sum over s\p plus
-- f p for any p in s. Only used in the below argument
lemma sum_split (α β : Type) [DecidableEq α] [AddCommMonoid β]
(s : Finset α) (f : α → β) {p : α} (hp : p ∈ s) :
        (∑ q ∈  s, f q) = f p + ∑ q ∈  s.erase p, f q := by
      have hs : insert p (s.erase p) = s := by
        simp only [Finset.insert_erase hp]
      have hpnot : p ∉ s.erase p := by simp
      calc
        (∑ q ∈  s, f q)
            = ∑ q ∈  insert p (s.erase p), f q := by simp only [hs]
        _   = f p + ∑ q ∈  s.erase p, f q := by
              simp only [hpnot, not_false_eq_true, Finset.sum_insert]


theorem Pn_for_all_n :
    ∀ n, P n := by
  have H : ∀ k, ∀ n, countPrimeFactorsMod4Eq3 n = k → P n := by
    intro k
    --By having k in the definition of H, it allows us to do strong induction on this variable,
    --even though k is always just countPrimeFactorsMod4Eq3 n by assumption. The strong induction is
    --necessary, because our descent argument will reduce the countPrimeFactors... n by 2, so a
    --direct induction argument will not work.
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro n hk
      rw[countPrimeFactorsMod4Eq3] at hk
      rw[P]
      intro hab p hp hpmod4
      --We need to do a case division on whether n.factorization p = 0, i.e., p actually divides n,
      -- because our descent step requires the assumption p ∣ n. Fortunately for us, the case
      --n.factorization p = 0 is as easy as it gets
      by_cases hfactor : n.factorization p = 0
      · rw[hfactor]
        exact even_iff.mpr rfl
      · have hpinfactors : p ∈ n.primeFactors := by
          by_contra c
          have : n.factorization p = 0 := Finsupp.notMem_support_iff.mp c
          rw[this] at hfactor
          tauto
        have hpmod4' : p%4 = 3 := by
          exact
            Eq.symm
              (Nat.add_right_cancel
                (congrFun (congrArg HAdd.hAdd (id (ModEq.symm hpmod4))) n))
        have hpprime : Nat.Prime p := (irreducible_iff_nat_prime p).mp hp
        have hpprime' : Fact (Nat.Prime p) := ⟨hpprime⟩
        have hpdivn : p ∣ n := dvd_of_mem_primeFactors hpinfactors
        rcases hab with ⟨a,b,hab⟩
        --Here we apply the descent argument
        have hdesc : p ^ 2 ∣ n ∧ p ∣ a ∧ p ∣ b :=
          sum_two_squares_descent n p a b hpdivn hpmod4 hab
        rcases hdesc.1 with ⟨m, hm⟩
        --Here we must do a case division on n=0, since n=0 makes n.factorization behave strangely.
        --Luckily n=0 makes n.factorzation = 0, so our claims are easy
        by_cases hnn0 : n = 0
        · rw[hnn0]
          rw[Nat.factorization_zero]
          simp only [Finsupp.coe_zero, Pi.zero_apply, Even.zero]
        · have hnfactortomfactor : n.factorization p = (m.factorization p) + 2 := by
            symm
            exact (factorization_after_div_by_p2 n p m hpprime hm hnn0).1
          rw[hnfactortomfactor]
          have heveniffevenplus2 (n : ℕ) : Even n ↔ Even (n+2) := by
            constructor
            · intro h
              have h1 : n % 2 = 0 := even_iff.mp h
              have h2 : (n+2)%2 = (n%2 + 2%2) % 2 := add_mod n 2 2
              refine even_iff.mpr ?_
              rw[h2]
              rw[h1]
            · intro h
              have h1 : (n+2) % 2 = 0 := even_iff.mp h
              have h2 : (n+2)%2 = (n%2 + 2%2) % 2 := add_mod n 2 2
              refine even_iff.mpr ?_
              rw[h1] at h2
              simp only [mod_self, add_zero, dvd_refl, mod_mod_of_dvd] at h2
              symm
              exact h2
          rw[← heveniffevenplus2]
          --It is good to remember that our goal is
          -- (countPrimeFactorsMod4Eq3 m) + 2 = countPrimeFactorsMod4Eq3 n,
          --since I would often forget what I was trying to prove in this section.
          --Once we prove this, then we will be able to show that
          -- countPrimeFactorsMod4Eq3 m < countPrimeFactorsMod4Eq3 n, so the
          -- inductive hypothesis will apply to m, and life will be good
          have : (countPrimeFactorsMod4Eq3 m) + 2 = countPrimeFactorsMod4Eq3 n := by
            repeat rw[countPrimeFactorsMod4Eq3]
            have hpS : p ∈ n.primeFactors.filter (fun q => q % 4 = 3) := by
              apply Finset.mem_filter.2
              refine ⟨hpinfactors, ?_⟩
              exact hpmod4'
            have hsplit :
                (∑ q ∈ n.primeFactors.filter (fun q => q % 4 = 3), n.factorization q)
                  =
                n.factorization p
                  + ∑ q ∈ (n.primeFactors.filter (fun q => q % 4 = 3)).erase p,
                      n.factorization q := by
              simpa using
                (sum_split ℕ ℕ
                  (s := n.primeFactors.filter (fun q => q % 4 = 3))
                  (f := fun q => n.factorization q)
                  (p := p)
                  hpS)
            rw[hsplit]
            --Unfortunately, we must break into cases as to whether p ∣ m because
            -- it changes whether m.primeFactors.erase p makes sense. The good news
            --is that the proof is highly similar in both cases
            --I remark now that I don't believe it was necessary to do this case division, since I
            --Lean interprets erasing a nonmember as doing nothing.
            --However, since this proof works, I will stick with it
            by_cases hpinfactors' : p ∈ m.primeFactors
            · have hpS' : p ∈ m.primeFactors.filter (fun q => q % 4 = 3) := by
                apply Finset.mem_filter.2
                refine ⟨hpinfactors', ?_⟩
                exact hpmod4'
              have hsplit' :
                  (∑ q ∈ m.primeFactors.filter (fun q => q % 4 = 3), m.factorization q)
                    =
                  m.factorization p
                    + ∑ q ∈ (m.primeFactors.filter (fun q => q % 4 = 3)).erase p,
                        m.factorization q := by
                simpa using
                  (sum_split ℕ ℕ
                    (s := m.primeFactors.filter (fun q => q % 4 = 3))
                    (f := fun q => m.factorization q)
                    (p := p)
                    hpS')
              rw[hsplit']
              rw[hnfactortomfactor]
              nth_rewrite 4 [add_comm]
              nth_rewrite 2 [add_assoc]
              nth_rewrite 3 [add_comm]
              simp only [Nat.add_right_cancel_iff, Nat.add_left_cancel_iff]
              --This result allows us to prove that the index sets are the same
              --and that the functions m.factorization and n.factorization agree
              --pointwise on the index sets.
              --The first goal is showing the sets are the same.
              --The second goal is showing that the functions agree pointwise
              --on the index set
              refine Finset.sum_congr ?_ ?_
              · rw[hm]
                apply Finset.ext
                intro q
                have hp2mne0 : p^2 * m ≠ 0 := by
                  rw[← hm]
                  exact hnn0
                constructor
                · intro hq
                  have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
                  have hq_memF :
                      q ∈ m.primeFactors.filter (fun r => r % 4 = 3) :=
                    Finset.mem_of_mem_erase hq
                  have hq_mem : q ∈ m.primeFactors :=
                    (Finset.mem_filter.mp hq_memF).1
                  have hq_mod : q % 4 = 3 :=
                    (Finset.mem_filter.mp hq_memF).2
                  have hq_mem' : q ∈ (p^2 * m).primeFactors := by
                    refine mem_primeFactors.mpr ?_
                    constructor
                    · exact prime_of_mem_primeFactors hq_mem
                    · constructor
                      · have : q ∣ m := dvd_of_mem_primeFactors hq_mem
                        exact Nat.dvd_mul_left_of_dvd this (p ^ 2)
                      · exact hp2mne0
                  apply Finset.mem_erase.mpr
                  constructor
                  · exact hq_ne
                  · apply Finset.mem_filter.mpr
                    constructor
                    · assumption
                    · assumption
                · intro hq
                  have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
                  have hq_memF :
                      q ∈ (p^2 * m).primeFactors.filter (fun r => r % 4 = 3) :=
                    Finset.mem_of_mem_erase hq
                  have hq_mem : q ∈ (p^2 * m).primeFactors :=
                    (Finset.mem_filter.mp hq_memF).1
                  have hq_mod : q % 4 = 3 :=
                    (Finset.mem_filter.mp hq_memF).2
                  have h1 : q ∣ p^2 * m := dvd_of_mem_primeFactors hq_mem
                  have hqprime : Nat.Prime q := prime_of_mem_primeFactors hq_mem
                  have hq_mem' : q ∈ m.primeFactors := by
                    refine mem_primeFactors.mpr ?_
                    constructor
                    · exact prime_of_mem_primeFactors hq_mem
                    · constructor
                      · have : q ∣ m := by
                          have h2 : q ∣ p^2 ∨ q ∣ m := by
                            rw[← Nat.Prime.dvd_mul]
                            · exact h1
                            · exact hqprime
                          cases h2 with
                          | inl h =>
                            exfalso
                            have : q ∣ p := Nat.Prime.dvd_of_dvd_pow hqprime h
                            have : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp this
                            rw[this] at hq_ne
                            tauto
                          | inr h =>
                            exact h
                        exact this
                      · by_contra c
                        rw[c] at hp2mne0
                        simp only [mul_zero, ne_eq, not_true_eq_false] at hp2mne0
                  apply Finset.mem_erase.mpr
                  constructor
                  · exact hq_ne
                  · apply Finset.mem_filter.mpr
                    constructor
                    · assumption
                    · assumption
              · --Here we show the functions m.factorization and n.factorization both agree
                --pointwise on the index set
                intro q hq
                have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
                exact (factorization_after_div_by_p2 n p m hpprime hm hnn0).2 q hq_ne
            · --Now we get the assumption instead that p does not divide m. This only changes
              --the proof slightly
              have h1 : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hpinfactors'
              have h2 : n.factorization p = 2 := by
                rw[hnfactortomfactor]
                rw[h1]
              rw[h2]
              rw[add_comm]
              simp only [Nat.add_left_cancel_iff]
              refine Finset.sum_congr ?_ ?_
              · --The goal in this branch again is showing the two index sets agree
                rw[hm]
                apply Finset.ext
                intro q
                have hp2mne0 : p^2 * m ≠ 0 := by
                  rw[← hm]
                  exact hnn0
                constructor
                · intro hq
                  have hq_ne : q ≠ p := by
                    by_contra c
                    have hyp1 : q ∈ m.primeFactors := Finset.mem_of_mem_filter q hq
                    have hyp2 : m.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hyp1
                    rw[c, h1] at hyp2
                    tauto
                  have hq_mem : q ∈ m.primeFactors :=
                    (Finset.mem_filter.mp hq).1
                  have hq_mod : q % 4 = 3 :=
                    (Finset.mem_filter.mp hq).2
                  have hq_mem' : q ∈ (p^2 * m).primeFactors := by
                    refine mem_primeFactors.mpr ?_
                    constructor
                    · exact prime_of_mem_primeFactors hq_mem
                    · constructor
                      · have : q ∣ m := dvd_of_mem_primeFactors hq_mem
                        exact Nat.dvd_mul_left_of_dvd this (p ^ 2)
                      · exact hp2mne0
                  apply Finset.mem_erase.mpr
                  constructor
                  · exact hq_ne
                  · apply Finset.mem_filter.mpr
                    constructor
                    · assumption
                    · assumption
                · intro hq
                  have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
                  have hq_memF :
                      q ∈ (p^2 * m).primeFactors.filter (fun r => r % 4 = 3) :=
                    Finset.mem_of_mem_erase hq
                  have hq_mem : q ∈ (p^2 * m).primeFactors :=
                    (Finset.mem_filter.mp hq_memF).1
                  have hq_mod : q % 4 = 3 :=
                    (Finset.mem_filter.mp hq_memF).2
                  have h1 : q ∣ p^2 * m := dvd_of_mem_primeFactors hq_mem
                  have hqprime : Nat.Prime q := prime_of_mem_primeFactors hq_mem
                  have hq_mem' : q ∈ m.primeFactors := by
                    refine mem_primeFactors.mpr ?_
                    constructor
                    · exact prime_of_mem_primeFactors hq_mem
                    · constructor
                      · have : q ∣ m := by
                          have h2 : q ∣ p^2 ∨ q ∣ m := by
                            rw[← Nat.Prime.dvd_mul]
                            · exact h1
                            · exact hqprime
                          cases h2 with
                          | inl h =>
                            exfalso
                            have : q ∣ p := Nat.Prime.dvd_of_dvd_pow hqprime h
                            have : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp this
                            rw[this] at hq_ne
                            tauto
                          | inr h =>
                            exact h
                        exact this
                      · by_contra c
                        rw[c] at hp2mne0
                        simp only [mul_zero, ne_eq, not_true_eq_false] at hp2mne0
                  apply Finset.mem_filter.mpr
                  constructor
                  · assumption
                  · assumption
              · --Now we are showing just that m.factorization = n.factorization on the index sets
                intro q hq
                have hq_ne : q ≠ p := Finset.ne_of_mem_erase hq
                exact (factorization_after_div_by_p2 n p m hpprime hm hnn0).2 q hq_ne
          --Now the heavylifting is over, we will just apply the induction hypothesis to m shortly
          have h' : P m := by
            --applying the induction hypothesis forces us to prove that each of its
             --hypotheses are met which is not too hard. The only one with some difficulty
             --is the first, that m is the sum of two squres, but we just use our conclusions
             --from the descent argument to get the needed values.
            apply IH (countPrimeFactorsMod4Eq3 m)
            · rw[← countPrimeFactorsMod4Eq3] at hk
              rw[← hk]
              rw[← this]
              simp only [lt_add_iff_pos_right, ofNat_pos]
            · rfl
          --In applying P m, it remains just to show the hypotheses of P m are met
          apply h'
          · rcases hdesc.2.1 with ⟨c, hc⟩
            rcases hdesc.2.2 with ⟨d, hd⟩
            use c, d
            rw[hm, hc, hd] at hab
            have h1 : (p * c) ^2 = p^2 * c^2 := Nat.mul_pow p c 2
            have h2 : (p * d) ^2 = p^2 * d^2 := Nat.mul_pow p d 2
            rw[h1, h2] at hab
            have h3 : p^2 * c^2 + p^2 * d^2 = p^2 * (c^2 + d^2) :=
              Eq.symm (Nat.mul_add (p ^ 2) (c ^ 2) (d ^ 2))
            rw[h3] at hab
            simp only [mul_eq_mul_left_iff, Nat.pow_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, and_true] at hab
            cases hab with
            | inl h => exact h
            | inr h =>
              exfalso
              rw[h] at hpmod4
              cases hpmod4
          · exact hp
          · exact modEq_modulus_add_iff.mp hpmod4
  intro n
  specialize H (countPrimeFactorsMod4Eq3 n) n
  apply H
  rfl


--These lemmas will just be used to define a choice function, selecting a witness for
--each such prime
lemma primes1or2mod4norm (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p = 2 ∨ p ≡ 1 [MOD 4])
: ∃ z : GaussianInt, p = (z.norm).toNat := by
      rw[← sum_two_nat_squares_iff_gaussian_norm, prime_sum_two_squares]
      assumption
lemma allnatnorm (p : ℕ) :
 ∃ z : GaussianInt, p^2 = (z.norm).toNat := by
  use p
  have hpnorm: (p : GaussianInt).norm = (p : ℤ)^2 := by
    rw[Zsqrtd.norm_natCast]
    have : (p : ℤ) * (p : ℤ) = ((p*p) : ℤ) := Int.mul_comm ↑p ↑p
    rw[this]
    have hyp (p : ℤ ): p  * p = p^2 := by exact Eq.symm (pow_two p)
    rw[hyp]
  rw[hpnorm]
  exact Eq.symm (Nat.add_zero (NatPow.pow p 2))

lemma prime_not_3_mod_4_iff_2_or_1_mod_4 (p : ℕ) [Fact (Nat.Prime p)] :
 ¬ p ≡ 3 [MOD 4] ↔ p = 2 ∨ p ≡ 1 [MOD 4] := by
  constructor
  · contrapose!
    intro h'
    have : p = 2 ∨ p ≡ 1 [MOD 4] ∨ p ≡ 3 [MOD 4] := odd_prime_1_or_3_mod_4 p
    cases this with
    | inl h => exfalso; apply h'.1; exact h
    | inr h =>
      cases h with
      | inl h => exfalso; apply h'.2;exact h
      | inr h => exact h
  · intro h'
    cases h' with
    | inl h =>
        rw[h]
        norm_num
    | inr h =>
      by_contra c
      have : 1 ≡ 3 [MOD 4] := ModEq.trans (id (ModEq.symm h)) c
      cases this


/-- This function selects a witness in the Gaussian integers to z.norm = p if p = 2 or
p ≡ 1 [MOD 4], selects a witness to z.norm = p^2 for all other primes, and sends
nonprimes to 0. -/
noncomputable def NtoGaussian (n : ℕ) : GaussianInt := by
  classical
  by_cases hn : Nat.Prime n
  · letI : Fact (Nat.Prime n) := ⟨hn⟩
    by_cases hgood : n = 2 ∨ n ≡ 1 [MOD 4]
    · exact Classical.choose (primes1or2mod4norm (p := n) (hpmod4 := hgood))
    · exact Classical.choose (allnatnorm (p := n))
  · exact 0

--This lemma just proves the defining property of our choice of witness
lemma NtoGaussian_spec_good (n : ℕ) (hn : Nat.Prime n)
    (hgood : n = 2 ∨ n ≡ 1 [MOD 4]) :
    n = ((NtoGaussian n).norm).toNat := by
  classical
  haveI : Fact (Nat.Prime n) := ⟨hn⟩
  simpa [NtoGaussian, hn, hgood] using
    (Classical.choose_spec (primes1or2mod4norm (p := n) (hpmod4 := hgood)))



--This lemma just proves the defining property of our choice of witness
lemma NtoGaussian_spec_bad (n : ℕ) (hn : Nat.Prime n)
    (hbad : ¬( n = 2 ∨  n ≡ 1 [MOD 4])) :
    n^2 = ((NtoGaussian n).norm).toNat := by
  classical
  haveI : Fact (Nat.Prime n) := ⟨hn⟩
  simpa [NtoGaussian, hn, hbad] using
    (Classical.choose_spec (allnatnorm (p := n)))

--This lemma is needed for a simplification in the backwards direction of
--the theorem
lemma gaussian_norm_pow (x : GaussianInt) (k : ℕ) :
    Zsqrtd.norm (x ^ k) = (Zsqrtd.norm x) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp [pow_succ, ih, Zsqrtd.norm_mul, mul_comm]



theorem sum_two_squares_iff (n : ℕ) :
  (∃ a b : ℕ, n = a^2 + b^2) ↔
  (∀ p ∈ n.primeFactors, p ≡ 3 [MOD 4] → Even (n.factorization p)) := by
  constructor
  · --The forward direction in just housekeeping due to our previous theorem Pn_for_all_n
    have : P n := by
      apply Pn_for_all_n
    rw[P] at this
    intro h1
    apply this at h1
    intro p hp hpmod4
    apply h1
    · exact prime_of_mem_primeFactors hp
    · exact hpmod4
  · intro hevenfactors
    --Again we must do case division on n=0 because some results need nonzero assumptions
    by_cases hn : n = 0
    · use 0, 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      exact hn
    · rw[sum_two_nat_squares_iff_gaussian_norm]
      --We have now translated the goal into a question about norms of Gaussian integers.
      --The idea is simple now: if p is 3 mod 4, since (NToGaussian p).norm = p^2, but
      -- p divides n with even multiplicity, then p^2 divides n with some multiplicity r.
      --We just take the product of all such (NToGaussian p)^r.
      -- If p is not 3 mod 4, then we know (NToGaussian p).norm = p, so if p divides n with
      -- multiplicity r, we just take this (NToGaussian p)^r and again take the product over
      -- all such p. The function g below formalizes this idea, so we can set
      -- z = ∏ p ∈ n.primeFactors, g p
      let g : ℕ → GaussianInt := fun p =>
        if ¬ (p = 2 ∨ p ≡ 1 [MOD 4]) then
          (NtoGaussian p) ^ (n.factorization p / 2)
        else
          (NtoGaussian p) ^ (n.factorization p)
      let z : GaussianInt :=
        ∏ p ∈  n.primeFactors, g p
      use z
      --The proof of hnorm_prod was written with the help of AI
      -- We just want to distribute the norm over the product using the
      -- fact that the norm distributes over binary products
      have hnorm_prod (t : Finset ℕ) :
        Zsqrtd.norm (∏ p ∈ t, g p) = ∏ p ∈ t, Zsqrtd.norm (g p) := by
        classical
        refine Finset.induction_on t ?base ?step
        · simp
        · intro a s ha hs
          simp only [Int.reduceNeg, ha, not_false_eq_true, Finset.prod_insert, Zsqrtd.norm_mul, hs]
      --Due to our earlier lemma gaussian_norms_are_nat, the proposition
      --hnZ (equality of integers) is equivalent to our goal (equality of natural numbers)
      have hnZ : (n : ℤ) = z.norm := by
        --Here we prove the fact that n = ∏ p_i ^ e_i, its prime factorization
        have hn_fac' : (∏ p ∈ n.primeFactors, p ^ (n.factorization p)) = n := by
          simpa [Finsupp.prod] using
            (Nat.factorization_prod_pow_eq_self (n := n) hn)
        have hn_facZ :
            (n : ℤ) =
              (∏ p ∈ n.primeFactors, (p : ℤ) ^ (n.factorization p)) := by
          have := congrArg (fun t : ℕ => (t : ℤ)) hn_fac'.symm
          simpa using this
        --Now we use hn_facZ and the transitivity of = to rewrite or goal
        refine hn_facZ.trans ?_
        --Next, we compute the norm of z using the fact that norms distribute over products
        --and z was defined by a product
        have hz_norm :
        z.norm = ∏ p ∈ n.primeFactors, (g p).norm := by
          simpa [z] using (hnorm_prod (t := n.primeFactors))
        rw [hz_norm]
        have hg_norm (p : ℕ) :
        (g p).norm =
          if ¬ (p = 2 ∨ p ≡ 1 [MOD 4]) then
            (Zsqrtd.norm (NtoGaussian p)) ^ (n.factorization p / 2)
          else
            (Zsqrtd.norm (NtoGaussian p)) ^ (n.factorization p) := by
          by_cases hgood : (p = 2 ∨ p ≡ 1 [MOD 4])
          · simp only [g, hgood]
            simp only [Int.reduceNeg, not_true_eq_false, ↓reduceIte]
            rw[gaussian_norm_pow]
          · simp only [g, hgood]
            simp only [Int.reduceNeg, not_false_eq_true, ↓reduceIte]
            rw[gaussian_norm_pow]
        --We use this theorem to reduce our goal to that of showing
        --p ^ n.factorization p = Zsqrtd.norm (g p) for each prime factor p
        refine (Finset.prod_congr rfl ?_)
        intro p hp
        rw[hg_norm]
        --We must break into cases based on if p is 3 mod 4 or not, because
        --since p is prime, this is the only condition in which the definition
        -- of NtoGaussian depends
        by_cases hgood : (p = 2 ∨ p ≡ 1 [MOD 4])
        · have hpPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
          haveI : Fact (Nat.Prime p) := ⟨hpPrime⟩
          have hNat : p = (Zsqrtd.norm (NtoGaussian p)).toNat :=
            NtoGaussian_spec_good (n := p) hpPrime hgood
          have hnn : 0 ≤ Zsqrtd.norm (NtoGaussian p) :=
            GaussianInt.norm_nonneg (NtoGaussian p)
          have hZ : (p : ℤ) = Zsqrtd.norm (NtoGaussian p) := by
            have : p = (Zsqrtd.norm (NtoGaussian p)).toNat := NtoGaussian_spec_good p hpPrime hgood
            exact (gaussian_norms_are_nat (NtoGaussian p) p).mpr hNat
          simp [hgood, hZ]
        · have hpPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
          haveI : Fact (Nat.Prime p) := ⟨hpPrime⟩
          have hNat : p^2 = (Zsqrtd.norm (NtoGaussian p)).toNat :=
            NtoGaussian_spec_bad (n := p) hpPrime hgood
          have hnn : 0 ≤ Zsqrtd.norm (NtoGaussian p) := GaussianInt.norm_nonneg (NtoGaussian p)
          have hZ2 : ((p : ℤ) ^ 2) = Zsqrtd.norm (NtoGaussian p) := by
            have : p^2 ≠ 0 →
            p^2 = (Zsqrtd.norm (NtoGaussian p)).toNat →
            (p^2 : ℤ ) = (Zsqrtd.norm (NtoGaussian p)).toNat := by
              exact (fun a a_1 ↦
                Eq.symm
                  ((fun {a b} ↦ Int.neg_inj.mp)
                    (congrArg Neg.neg (congrArg Nat.cast (id (Eq.symm hNat))))))
            have hp2ne0 : p^2 ≠ 0 := by
              exact Ne.symm (NeZero.ne' (p ^ 2))
            apply this at hp2ne0
            apply hp2ne0 at hNat
            have : (((Zsqrtd.norm (NtoGaussian p)).toNat) : ℤ) = (Zsqrtd.norm (NtoGaussian p)) := by
              exact
              (gaussian_norms_are_nat (NtoGaussian p) (Zsqrtd.norm (NtoGaussian p)).toNat).mpr rfl
            rw[this] at hNat
            exact hNat
          --Convert not 2 or congruent to 1 mod 4 to congruent to 3 mod 4
          have hpmod3 : p ≡ 3 [MOD 4] := by
            by_contra c
            rw[prime_not_3_mod_4_iff_2_or_1_mod_4] at c
            apply hgood
            exact c
          -- use this conversion to get an even condition on the multiplicity
          have heven : Even (n.factorization p) := hevenfactors p hp hpmod3
          -- Use the even condition to obtain that 2 divides n.factorization,
          -- hence 2*(n.factorization p / 2) = n.factorization p
          have hdiv2 : 2 ∣ n.factorization p :=
            even_iff_two_dvd.mp (hevenfactors p hp hpmod3)
          have hmul : 2 * (n.factorization p / 2) = n.factorization p :=
            Nat.mul_div_cancel' hdiv2
          have : ((p : ℤ) ^ 2) ^ (n.factorization p / 2) = (p : ℤ) ^ n.factorization p := by
            calc
              ((p : ℤ) ^ 2) ^ (n.factorization p / 2)
                  = (p : ℤ) ^ (2 * (n.factorization p / 2)) := by
                      simp [pow_mul]
              _   = (p : ℤ) ^ n.factorization p := by
                      simp [hmul]
          simp [hgood, hZ2, this.symm]
      exact (gaussian_norms_are_nat z n).mp hnZ
