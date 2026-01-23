import Mathlib

open Nat
open GaussianInt


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


theorem odd_prime_1_or_3_mod_4 (p : ℕ) [hp : Fact (Nat.Prime p)]
  : p=2 ∨ p≡ 1 [MOD 4] ∨ p≡ 3 [MOD 4] := by
  by_cases h : (p=2)
  · left
    exact h
  right
  · have hp4 : ∃ m : ℕ, m < 4 ∧ p ≡ m [MOD 4] := residues_mod_n p 4 (by norm_num)
    rcases hp4 with ⟨m, hm, heq⟩
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := nums_le_4 m hm
    cases hm4 with
    | inl h0 =>
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
            left
            rw[h1] at heq
            exact heq
        | inr h23 =>
            cases h23 with
            | inl h2 =>
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
                right
                rw[h3] at heq
                exact heq





theorem squares_mod_4 (a : ℕ) : a^2 ≡ 0 [MOD 4] ∨ a^2 ≡ 1 [MOD 4] := by
  have hp4 : ∃ m : ℕ, m < 4 ∧ a ≡ m [MOD 4] := residues_mod_n a 4 (by norm_num)
  rcases hp4 with ⟨m, hm, heq⟩
  have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := nums_le_4 m hm
  have hpow : a^2 ≡ m^2 [MOD 4] := by exact Nat.ModEq.pow 2 heq
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

theorem sum_of_squares_mod_4 (a b : ℕ) :
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

theorem sum_two_int_squares_iff_gaussian_norm (n : ℕ) :
  (∃ a b : ℤ , n = a^2 + b^2) ↔
  (∃ z : GaussianInt, n = Zsqrtd.norm z) := by
  constructor
  · intro h
    rcases h with ⟨a,b,hab⟩
    use ((⟨(a : ℤ), (b : ℤ)⟩) : GaussianInt)
    rw[hab]
    rw[Zsqrtd.norm_def]
    simp
    simp[pow_two]
  · intro h
    rcases h with ⟨z, hz⟩
    use z.re, z.im
    rw[hz]
    rw[Zsqrtd.norm_def]
    simp
    simp[pow_two]

theorem to_nat_to_int_ge_0 (n : ℤ) (hn : 0 ≤ n) : Int.ofNat n.toNat = n := by
  simp only [Int.ofNat_eq_natCast, Int.ofNat_toNat, sup_eq_left]
  exact hn



theorem sum_of_squares_to_nat (n : ℕ) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
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


theorem sum_two_squares_Z_iff_N (n : ℕ) :
  (∃ a b : ℤ, n = a^2 + b^2) ↔
  (∃ c d : ℕ, n = c^2 + d^2) := by
  constructor
  · intro h
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

theorem gaussian_norms_are_nat (z : GaussianInt) (n : ℕ)
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


theorem sum_two_nat_squares_iff_gaussian_norm (n : ℕ) :
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

theorem divison_comm_w_val_up_to_p (p : ℕ) [Fact (Nat.Prime p)] (a b : ZMod p)
  : (a + b).val = 0 ↔ p ∣ a.val + b.val := by
  constructor
  · intro h
    apply (ZMod.val_eq_zero (a+b)).mp at h
    have haisnegb : a = -b := by
      exact eq_neg_of_add_eq_zero_left h
    rw[haisnegb]
    have h1: ↑((-b).val + b.val) = (0 : ZMod p)  ↔ p ∣ (-b).val + b.val := by
      exact ZMod.natCast_eq_zero_iff ((-b).val + b.val) p
    apply h1.mp
    simp
  · intro h
    apply (ZMod.natCast_eq_zero_iff (a.val + b.val) p).mpr at h
    simp only [cast_add, ZMod.natCast_val, ZMod.cast_id', id_eq] at h
    rw[h]
    norm_num


-- This theorem was partially guided with AI assistance
theorem lift_y2_plus_1 (p : ℕ) [Fact (Nat.Prime p)]
  (y : ZMod p) (hy : y ^ 2 + 1 = 0) :
  ∃ x : ℕ, p ∣ x^2 + 1 := by
    refine ⟨y.val, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (y.val^2+1) p).mp
    simp only [cast_add, cast_pow, ZMod.natCast_val, ZMod.cast_id', id_eq, cast_one]
    exact hy

-- This theorem was partially guided with AI assistance
theorem half_of_one_add_four_mul
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




theorem primes_w_neg1_square (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 1 [MOD 4])
 : ∃ x : ℕ, p ∣ x^2+1 := by
  have hn1 : (-1 : ZMod p) ≠ (0 : ZMod p) := by
    norm_num
  have h1 : (-1 : ZMod p)^(p/2) = 1 → IsSquare (-1 : ZMod p) := by
    exact (ZMod.euler_criterion p hn1).mpr
  have h1lep : 1 ≤ p := by exact NeZero.one_le
  have eucl_alg : ∃ t : ℕ, p = 1 + 4*t := by
    apply (Nat.modEq_iff_exists_eq_add h1lep).mp
    apply Nat.ModEq.symm
    exact hpmod4
  rcases eucl_alg with ⟨t, ht⟩
  have hpover2 : p / 2 = 2 * t := half_of_one_add_four_mul p t ht
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
  exact lift_y2_plus_1 p y myh



theorem mod4_rw (n : ℕ) (hn : n ≡ 1 [MOD 4]) : n%4=1 := by
  exact Eq.symm (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (ModEq.symm hn))) n))


theorem primes_one_mod_four_reducible (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 1 [MOD 4])
 : ¬ Irreducible (p : GaussianInt) := by
  have irred_iff_prime : Irreducible (p : GaussianInt) ↔ _root_.Prime (p : GaussianInt) := by
    exact _root_.irreducible_iff_prime
  rw[irred_iff_prime]
  by_contra h
  have pmod43 : p%4 = 3 := mod_four_eq_three_of_nat_prime_of_prime p h
  have pmod41 : p%4 = 1 := mod4_rw p hpmod4
  rw[pmod43] at pmod41
  tauto


theorem contra_via_unit_irreducible (p : ℤ) (hirr : Irreducible p) :
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
theorem contra_via_prime_div_1
(p : ℕ) [Fact (Nat.Prime p)] (hdiv : (p : ℤ) ∣ 1) : False := by
  have hprime : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hnotdiv1 : ¬ (p : ℤ) ∣ 1 := contra_via_unit_irreducible (p : ℤ) (hprime.irreducible)
  exact hnotdiv1 hdiv

theorem contra_via_unit_irreducible_neg_1 (p : ℤ) (hirr : Irreducible p) :
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


theorem contra_via_prime_div_neg_1
(p : ℕ) [Fact (Nat.Prime p)] (hdiv : (p : ℤ) ∣ -1) : False := by
have hprime : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
have hnotdiv1 : ¬ (p : ℤ) ∣ -1 := contra_via_unit_irreducible_neg_1 (p : ℤ) (hprime.irreducible)
exact hnotdiv1 hdiv

theorem prime_sum_two_squares (p : ℕ) [Fact (Nat.Prime p)] :
 (∃ a b : ℕ, p = a^2 + b^2) ↔ p=2 ∨ p≡ 1 [MOD 4] := by
  constructor
  · intro h
    rcases h with ⟨a,b,hab⟩
    have hpmod4 :
    p = 2 ∨ p ≡ 1 [MOD 4] ∨ p ≡ 3 [MOD 4] := odd_prime_1_or_3_mod_4 p
    cases hpmod4 with
    | inl h2 => left; exact h2
    | inr h1or3 =>
        cases h1or3 with
        | inl h1 => right; exact h1
        | inr h3 =>
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

theorem toNat_is_1_iff_is_1 (n : ℤ) : n.toNat = 1 ↔ n = 1 := by
  constructor
  · contrapose!
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
  · intro h
    rw[h]
    norm_num

--Written with AI assistance
theorem toNat_is_m_iff_is_m (n : ℤ) (m : ℕ) (hmpos : m ≠ 0) :
  n.toNat = m ↔ n = m := by
constructor
· intro h
  have hn0 : 0 ≤ n := by
    by_contra hn0
    have hnle : n ≤ 0 := le_of_not_ge hn0
    have ht : n.toNat = 0 := Int.toNat_of_nonpos hnle
    have : m = 0 := by simpa [h] using ht
    exact hmpos this
  have hof : (Int.ofNat n.toNat) = n :=
    to_nat_to_int_ge_0 n hn0
  have : (Int.ofNat m) = n := by
    simpa [h] using hof
  simpa using this.symm
· intro h
  simp [h]





theorem unit_iff_norm_1_nat (z : GaussianInt) : (z.norm).toNat = 1 ↔ IsUnit z := by
  constructor
  · intro h
    have norm_int_is_1 : Zsqrtd.norm z = 1 := by
      rw[(toNat_is_1_iff_is_1 z.norm).mp]
      assumption
    have hminus1le0 : -1 ≤ 0 := by norm_num
    rw[← Zsqrtd.norm_eq_one_iff' hminus1le0]
    exact norm_int_is_1
  · intro h
    have hminus1le0 : -1 ≤ 0 := by norm_num
    rw[toNat_is_1_iff_is_1 z.norm]
    rw[Zsqrtd.norm_eq_one_iff' hminus1le0]
    exact h


theorem prod_Nat_is_p2
 (a b p : ℕ) [Fact (Nat.Prime p)] (heq : a * b = p ^ 2)
 : (a = p ∧ b = p) ∨ a=1 ∨ b = 1 := by
  by_cases ha : a=1
  · right
    left
    exact ha
  · by_cases hb : b=1
    · right
      right
      exact hb
    · left
      apply (Nat.Prime.mul_eq_prime_sq_iff (Fact.out : Nat.Prime p) ha hb).mp
      exact heq

theorem eq_Nat_impl_eq_Int (a : ℤ) (b : ℕ) (ha : 0 ≤ a) (heq : a.toNat = b) : a = ↑b := by
  by_cases h : b = 0
  · rw[h]at heq
    have thm1 (n : ℤ) (hn : 0 ≤ n) : n.toNat = 0 →  n = 0 := by
      intro hyp
      have thm2 (n : ℤ) : n.toNat = 0 → (n.toNat : ℤ) = 0 := by
        exact fun a ↦ (fun {n} ↦ Int.ofNat_eq_zero.mpr) a
      apply (thm2 n) at hyp
      have : Int.ofNat n.toNat = ↑ n.toNat := by exact Int.ofNat_eq_natCast n.toNat
      symm at this
      rw[this] at hyp
      rw [to_nat_to_int_ge_0 n hn] at hyp
      exact hyp
    rw[h]
    simp only [CharP.cast_eq_zero]
    apply thm1 a ha
    exact heq
  · rw [toNat_is_m_iff_is_m a b h] at heq
    exact heq



theorem Nat_prime_product_impl_unit
(p : ℕ) [Fact (Nat.Prime p)] (a b : GaussianInt) (hprod : p = a * b)
: (a.norm = p ∧ b.norm = p) ∨ IsUnit a ∨ IsUnit b := by
    have hnormp2 : (p : GaussianInt).norm = p^2 := by
          rw[Zsqrtd.norm_natCast p]
          ring
    have habnorm : a.norm * b.norm = p ^ 2 := by
        rw[← Zsqrtd.norm_mul a b]
        rw[← hnormp2]
        rw[hprod]
    have sumthin : (Zsqrtd.norm a * Zsqrtd.norm b).toNat = ((p: ℤ) ^ 2).toNat := by
      rw[habnorm]
    have to_Z_square_back (n : ℕ) : ((n : ℤ)^2).toNat = n^2 := by
        exact Nat.add_zero (NatPow.pow n 2)
    rw[to_Z_square_back p] at sumthin
    have somethink (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
      exact Int.toNat_mul ha hb
    have hnormage0 : 0≤ a.norm := GaussianInt.norm_nonneg a
    have hnormbge0 : 0≤ b.norm := GaussianInt.norm_nonneg b
    have convert_to_Nat_not_1 (n : ℤ) : n ≠ 1 → n.toNat ≠ (1 : ℕ) := by
      contrapose!
      exact (toNat_is_1_iff_is_1 n).mp
    have hminus1le0 : -1 ≤ 0 := by norm_num
    rw[← unit_iff_norm_1_nat a]
    rw[← unit_iff_norm_1_nat b]
    rw[somethink a.norm b.norm hnormage0 hnormbge0] at sumthin
    have good_fact :
     ((a.norm).toNat = p ∧ (b.norm).toNat = p) ∨ (a.norm).toNat = 1 ∨ (b.norm).toNat = 1
     := prod_Nat_is_p2 (a.norm).toNat (b.norm).toNat p sumthin
    cases good_fact with
    | inl h =>
        left
        constructor
        · exact eq_Nat_impl_eq_Int a.norm p hnormage0 h.1
        · exact eq_Nat_impl_eq_Int b.norm p hnormbge0 h.2
    | inr h =>
        cases h with
        | inl h' =>
            right
            left
            exact h'
        | inr h' =>
            right
            right
            exact h'


theorem Nat_prime_not_pm1 (p : ℕ) [pFact : Fact (Nat.Prime p)] : p ≠ 1 ∧ (p : ℤ) ≠ -1 := by
  constructor
  · by_contra c
    have hp : Nat.Prime p := pFact.out
    rw[c] at hp
    exact prime_one_false hp
  · exact Ne.symm (not_eq_of_beq_eq_false rfl)


theorem p_mod_4_is_3_is_prime
(p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 3 [MOD 4]) : _root_.Prime (p : GaussianInt) := by
  have pnot1mod4not2 : p ≠ 2 ∧ ¬ p ≡ 1 [MOD 4] := by
    constructor
    · by_contra hp2
      rw[hp2] at hpmod4
      norm_num at hpmod4
    · by_contra hp1
      symm at hp1
      have : 1 ≡ 3 [MOD 4] := by
        exact ModEq.trans hp1 hpmod4
      norm_num at this
  have hexistz : ¬ ∃ z : GaussianInt, p = (Zsqrtd.norm z).toNat := by
    by_contra myhp
    apply (sum_two_nat_squares_iff_gaussian_norm p).mpr at myhp
    apply (prime_sum_two_squares p).mp at myhp
    tauto
  have irred_iff_prime : Irreducible (p : GaussianInt) ↔ _root_.Prime (p : GaussianInt) := by
    exact _root_.irreducible_iff_prime
  apply (irred_iff_prime).mp
  have hm1le0 : -1 ≤ 0 := by norm_num
  rw[irreducible_iff]
  constructor
  · rw[← Zsqrtd.norm_eq_one_iff' hm1le0]
    have : ((p : GaussianInt).norm) = (p : ℤ)^2 := by
      rw[Zsqrtd.norm_natCast p]
      ring
    rw[this]
    norm_num
    constructor
    · exact (Nat_prime_not_pm1 p).1
    · exact (Nat_prime_not_pm1 p).2
  · intro a b hab
    have newcases: (a.norm = p ∧ b.norm = p) ∨ IsUnit a ∨ IsUnit b := by
      exact Nat_prime_product_impl_unit p a b hab
    cases newcases with
    | inl h =>
        exfalso
        have existz : ∃ z : GaussianInt, p =z.norm := by
          use a
          symm
          exact h.1
        have p_sum_two_int_square : ∃ c d : ℤ, p = c^2 + d^2 := by
          rw[sum_two_int_squares_iff_gaussian_norm p]
          exact existz
        have p_sum_two_nat_square : ∃ m n : ℕ, p = m^2 + n^2 := by
          exact (sum_two_squares_Z_iff_N p).mp p_sum_two_int_square
        rw[prime_sum_two_squares p] at p_sum_two_nat_square
        cases p_sum_two_nat_square with
        | inl h' => rw[h'] at hpmod4; norm_num at hpmod4
        | inr h' =>
            have h1 : 1 ≡ p [MOD 4] := h'.symm
            have h1 : 1 ≡ 3 [MOD 4] := by exact ModEq.trans h1 hpmod4
            norm_num at h1
    | inr h => exact h

theorem exists_sqfree_mul_sq (n : ℕ) :
    ∃ d m : ℕ, n = d * m^2 ∧ Squarefree d := by
  rcases Nat.sq_mul_squarefree n with ⟨d, m, h, hd⟩
  refine ⟨d, m, ?_, hd⟩
  have : n = m^2 * d := by
    simpa using h.symm
  simpa [mul_comm] using this

--Written with AI assistance
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  (Nat.sq_mul_squarefree n).choose

--Written with AI assistance
theorem exists_b_sq_mul_squarefreePart (n : ℕ) :
    ∃ b : ℕ, n = b^2 * squarefreePart n := by
  refine ⟨(Nat.sq_mul_squarefree n).choose_spec.choose, ?_⟩
  have h :
      ((Nat.sq_mul_squarefree n).choose_spec.choose)^2 * squarefreePart n = n :=
    (Nat.sq_mul_squarefree n).choose_spec.choose_spec.left
  exact h.symm

--Written with AI assistance
theorem squarefree_squarefreePart (n : ℕ) : Squarefree (squarefreePart n) := by
  rcases (Nat.sq_mul_squarefree n).choose_spec with ⟨b, hb⟩
  exact hb.2

/-
Show two elements are associate iff they have equal norm.
Then show that every Gaussian prime is associated
to either 1+i, a+bi with a^2+b^2=p, p ≡ 1 [MOD 4], or p with p ≡ 3 [MOD 4].
Show p ∣ z.norm ↔ ∃ a Gaussian prime q s.t. q ∣ ↑ p and q ∣ z.
Use this to show that if p ∣ z.norm, then either p=2 or p≡ 1 [MOD 4] and some Gaussian prime
dividing p divides z, or p ≡ 3 [MOD 4] and ↑p ∣ z.
Now apply this to the inductive hypothesis in the final theorem to show that we may cancel
-/

/-
Step 1 : Show that 2 ∣ z.norm ↔ 1+i ∣ z
Step 2 : Show that n = 2 * m, Odd m, ∃ a b, n = a^2 + b^2 ↔ ∃ c d, m = c^2 + d^2
Step 3 : Show that n = 2^r * m, Odd m, ∃ a b, n = a^2 + b^2 ↔ ∃ c d, m = c^2 + d^2 by induction on r
Step 4 : Show that n = a^2 + b^2 →  Even (countPrimeFactorsMod4Eq3 n).
Step 5 : Show that

-/




example (z : GaussianInt) (h : z ≠ 0) :
  ∃ f : Multiset GaussianInt, (∀ p ∈ f, Prime p) ∧ Associated f.prod z := by
    exact UniqueFactorizationMonoid.exists_prime_factors z h


theorem odd_part_decomp {n : ℕ} (hn : n ≠ 0) :
    ∃ r m : ℕ, n = 2^r * m ∧ Odd m := by
  rcases Nat.exists_eq_two_pow_mul_odd (n := n) hn with ⟨r, m, hmOdd, hnm⟩
  exact ⟨r, m, hnm, hmOdd⟩

def countPrimeFactorsMod4Eq3 (n : ℕ) : ℕ :=
  ∑ p ∈  ((Nat.factorization n).support).filter (fun p => p % 4 = 3),
    Nat.factorization n p



theorem even_countPrimeFactorsMod4Eq3_of_modEq_one (m : ℕ)
  (hm : m ≡ 1 [MOD 4]) :
  Even (countPrimeFactorsMod4Eq3 m) := by
  have hm0 : m ≠ 0 := by
    intro h0
    simp only [h0] at hm
    cases hm
  apply (Nat.even_iff).mpr
  set S : Finset ℕ := (Nat.factorization m).support with hS
  have hprod : (∏ p ∈  S, p ^ (Nat.factorization m p)) = m := by
    simpa [S, hS] using (Nat.factorization_prod_pow_eq_self hm0)
  have hmZ4 : (m : ZMod 4) = 1 := by
    apply (ZMod.natCast_eq_natCast_iff m 1 4).mpr
    exact hm
  have hm2 : m ≡ 1 [MOD 2] := hm.of_dvd (by decide : (2 : ℕ) ∣ 4)
  have hOdd : Odd m := (Nat.odd_iff).2 hm2
  have h2notdvd : ¬ (2 ∣ m) := by
    exact hOdd.not_two_dvd_nat
  have hmem_dvd : ∀ {p : ℕ}, p ∈ S → p ∣ m := by
    rw[hS]
    exact fun {p} a ↦ dvd_of_mem_primeFactors a
  have h2notinS : 2 ∉ S := by
    by_contra c
    specialize hmem_dvd c
    tauto
  --The syntax of the below proposition was created with AI assistance
  have hprodZ4 :
    (∏ p ∈ S, (p : ZMod 4) ^ (Nat.factorization m p)) = (m : ZMod 4) := by
      simpa using (congrArg (fun t : ℕ => (t : ZMod 4)) hprod)
  have hprodEq1 : (∏ p ∈  S, (p : ZMod 4) ^ (Nat.factorization m p)) = (1 : ZMod 4) := by
    simpa [hprodZ4] using hmZ4
  have hpinS_imp_Prime_p : ∀ {p : ℕ}, p ∈ S → Nat.Prime p := by
    rw[hS]
    exact fun {p} a ↦ prime_of_mem_primeFactors a
  set g : ℕ → ZMod 4 := fun p => (p : ZMod 4) ^ (Nat.factorization m p)
  have prod_split :
    (∏ p ∈ S.filter (fun p => p % 4 = 1), g p)
      * (∏ p ∈ S.filter (fun p => ¬ p % 4 = 1), g p)
      = (∏ p ∈  S, g p) := by
    simpa [g] using
      (Finset.prod_filter_mul_prod_filter_not (s := S) (f := g) (p := fun p => p % 4 = 1))
  let T : Finset ℕ := S.filter (fun p => p % 4 = 3)
  have filter_not1_eq_filter_3 :
    S.filter (fun p => ¬ p % 4 = 1) = S.filter (fun p => p % 4 = 3) := by
    apply Finset.filter_congr
    intro p hp
    -- hp : p ∈ S
    have hpprime : Nat.Prime p := hpinS_imp_Prime_p hp
    have hpne2 : p ≠ 2 := by
      intro h
      exact h2notinS (by simpa [h] using hp)
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
      haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
      have p2or1mod4or3mod4 : p = 2 ∨ p ≡ 1 [MOD 4] ∨ p ≡ 3 [MOD 4] := odd_prime_1_or_3_mod_4 p
      cases p2or1mod4or3mod4 with
      | inl h => tauto
      | inr h =>
        cases h with
        | inl h1 =>
          left
          have : p%4 = 1%4 := h1
          simp [this]
        | inr h3 =>
          right
          have : p%4 = 3%4 := h3
          simp [this]
    constructor
    · intro hnot1
      cases hmod with
      | inl h1 => exact (False.elim (hnot1 h1))
      | inr h3 => exact h3
    · intro h3 h1
      exact by cases (by simp [h3] at h1 : (3:ℕ)=1)
  rw[filter_not1_eq_filter_3] at prod_split
  have prod_over_1_mod_4 : (∏ p ∈ S with p % 4 = 1, g p) = 1 := by
    have hgp1: ∀ p ∈ S, p % 4 = (1 : ℕ) →  g p = (1 : ZMod 4) := by
      intro p hp hmod4
      have hpmod4is1: (p : ZMod 4) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff p 1 4).mpr
        have h1m4 : 1 = 1%4 := eq_of_beq_eq_true rfl
        rw[h1m4] at hmod4
        exact hmod4
      simp only [g]
      rw[hpmod4is1]
      norm_num
    --The syntax in this simplification was written with the help of AI
    have : (∏ p ∈ S.filter (fun p => p % 4 = 1), g p) = 1 := by
      refine Finset.prod_eq_one ?_
      intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.1 hp).1
      have hpmod : p % 4 = 1 := (Finset.mem_filter.1 hp).2
      simpa using hgp1 p hpS hpmod
    exact this
  rw[prod_over_1_mod_4] at prod_split
  simp only [one_mul] at prod_split
  symm at prod_split
  have prod_over_3_mod_4 : (∏ p ∈ S with p%4 = 3, g p) = (-1)^(countPrimeFactorsMod4Eq3 m) := by
    have hgp3 : ∀ p ∈ S, p % 4 = 3 → g p = (-1)^(m.factorization p) := by
      intro p hp hpmod4
      simp only [g]
      have hred :(p : ZMod 4) = -1 := by
        have h3m4 : 3 = 3%4 := eq_of_beq_eq_true rfl
        rw[h3m4] at hpmod4
        have h3 : p ≡ 3 [MOD 4] := hpmod4
        have hred': (p : ZMod 4) = (3: ZMod 4) := (ZMod.natCast_eq_natCast_iff p 3 4).mpr h3
        have h3isneg1 : (3 : ZMod 4) = (-1 : ZMod 4) := by rfl
        rw[h3isneg1] at hred'
        exact hred'
      rw[hred]
    --The syntax of this proposition was generated by AI
    have hrewrite :
    (∏ p ∈  S.filter (fun p => p % 4 = 3), (g p : ZMod 4))
      =
    (∏ p ∈  S.filter (fun p => p % 4 = 3), ((-1 : ZMod 4) ^ Nat.factorization m p)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rcases Finset.mem_filter.1 hp with ⟨hpS, hpmod⟩
      simpa using hgp3 p hpS hpmod
    have :
    (∏ p ∈  S.filter (fun p => p % 4 = 3), ((-1 : ZMod 4) ^ Nat.factorization m p))
      =
    ((-1 : ZMod 4) ^
      (∑ p ∈  S.filter (fun p => p % 4 = 3), Nat.factorization m p)) := by
      simpa using
    (Finset.prod_pow_eq_pow_sum (s := S.filter (fun p => p % 4 = 3))
      (a := (-1 : ZMod 4)) (f := fun p => Nat.factorization m p))
    rw[this] at hrewrite
    rw[hrewrite]
    have : ∑ p ∈ S with p%4 = 3, m.factorization p = countPrimeFactorsMod4Eq3 m := by
      simp only [countPrimeFactorsMod4Eq3, Nat.support_factorization]
      rw[hS]
      exact Finset.sum_sdiff_eq_sum_sdiff_iff.mp rfl
    rw[this]
  rw[prod_over_3_mod_4] at prod_split
  have hanother_rewrite: ∏ p ∈ S, g p = (m : ZMod 4) := by
    simp only [g]
    nth_rewrite 2[← Nat.factorization_prod_pow_eq_self hm0]
    simp only [cast_finsuppProd, cast_pow]
    rfl
  rw[hanother_rewrite] at prod_split
  rw[hmZ4] at prod_split
  have h_mod_4_pow (k : ℕ) : k%2 ≠ 0 → (-1 : ZMod 4)^k ≠ 1 := by
      intro h
      have hkmod2: (k % 2) = 1 := by
        exact mod_two_ne_zero.mp h
      have heuclk: k = k%2 + k/2 * 2 := Eq.symm (mod_add_div' k 2)
      rw[hkmod2] at heuclk
      rw[heuclk]
      have h_dist_pows: (-1 : ZMod 4)^(1 + k/2 * 2) = (-1)^1 * (-1)^(k/2 * 2) := by
        exact pow_add (-1) 1 (k / 2 * 2)
      rw[h_dist_pows]
      have h_exp_simp : (-1 : ZMod 4)^(k/2 * 2) = ((-1)^2)^(k/2) := by
        exact pow_mul' (-1) (k / 2) 2
      rw[h_exp_simp]
      simp
      tauto
  by_contra c
  apply (h_mod_4_pow (countPrimeFactorsMod4Eq3 m)) at c
  tauto



theorem two_div_znorm (z : GaussianInt) : 2 ∣ z.norm ↔ ((⟨1, 1⟩) : GaussianInt) ∣ z := by
  sorry

theorem cancel_two_if_znorm (m : ℕ)
  : (∃ x : GaussianInt, 2* m = x.norm) ↔ (∃ y : GaussianInt, m = y.norm) := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    have htwodiv : 2 ∣ x.norm := Dvd.intro (↑m) hx
    apply (two_div_znorm x).mp at htwodiv
    have hy : ∃ y : GaussianInt, x = ((⟨1, 1⟩) : GaussianInt) * y := by
      rcases htwodiv with ⟨y, hy⟩
      use y
    rcases hy with ⟨y, h⟩
    use y
    rw[h] at hx
    have norm_dist:
    ((⟨1,1⟩ : GaussianInt) * y).norm = (⟨1,1⟩ : GaussianInt).norm * y.norm
    := Zsqrtd.norm_mul { re := 1, im := 1 } y
    rw[norm_dist] at hx
    have hone_plus_i_norm : (⟨1,1⟩ : GaussianInt).norm = 2 := by exact Int.neg_inj.mp rfl
    rw[hone_plus_i_norm] at hx
    have h2not0 : (2: ℤ) ≠ 0 := by norm_num
    have (n m : ℤ): 2*n = 2*m → n = m := by
      intro h
      apply mul_left_cancel₀ h2not0 h
    apply this at hx
    exact hx
  · intro h
    rcases h with ⟨y, hy⟩
    rw[hy]
    use (⟨1,1⟩: GaussianInt) * y
    have norm_dist:
    ((⟨1,1⟩ : GaussianInt) * y).norm = (⟨1,1⟩ : GaussianInt).norm * y.norm
    := Zsqrtd.norm_mul { re := 1, im := 1 } y
    rw[norm_dist]
    have hone_plus_i_norm : (⟨1,1⟩ : GaussianInt).norm = 2 := by exact Int.neg_inj.mp rfl
    rw[hone_plus_i_norm]



theorem cancel_pow_two_if_znorm (m r : ℕ)
  : (∃ x : GaussianInt, (2 : ℤ)^r * (m : ℤ) = x.norm ) ↔ (∃ y : GaussianInt, m = y.norm) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have halg : (2 : ℤ) ^(r+1) * (↑ m) = 2* (2^r * ↑ m) := by ring_nf
      constructor
      · intro h
        rcases h with ⟨x, hx⟩
        rw[halg] at hx
        have : ∃ y : GaussianInt, 2^r * (m : ℤ) = y.norm := by
          apply (cancel_two_if_znorm (2^r * m)).mp
          use x
          exact hx
        apply ih.mp
        exact this
      · intro h
        rcases h with ⟨y, hy⟩
        use (⟨1,1⟩ : GaussianInt)^(r+1) * y
        have hone_plus_i_norm : (⟨1,1⟩ : GaussianInt).norm = 2 := by exact Int.neg_inj.mp rfl
        have hpowers_comm_w_norm (n : ℕ) (z : GaussianInt): (z^n).norm = (z.norm)^n := by
          induction n with
          | zero => simp
          | succ n ih =>
            have dist_pow_GI: z^(n+1) = z * z^n := by ring
            rw[dist_pow_GI, Zsqrtd.norm_mul z (z^n)]
            rw[ih]
            have dist_pow_Z (a : ℤ) (n : ℕ) : a * a^n = a^(n+1) := Eq.symm (Int.pow_succ' a n)
            rw[dist_pow_Z (z.norm) n]
        rw[Zsqrtd.norm_mul (({ re := 1, im := 1})^(r+1)) y,
        hy, hpowers_comm_w_norm (r+1), hone_plus_i_norm]




theorem even_primes_mod_4_if_sum_two_squares (n a b : ℕ) (hn : n ≠ 0) (heq : n = a ^ 2 + b ^ 2)
  : Even (countPrimeFactorsMod4Eq3 n) := by
  rcases odd_part_decomp hn with ⟨r,m, hrm⟩
  have h1 : ∃ c d : ℕ, 2^r * m = c^2 + d^2 := by
    rw[← hrm.1]
    use a,b
  rcases h1 with ⟨c,d, hcd⟩
  have hcdZ : (2 : ℤ) ^ r * (m : ℤ) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    exact_mod_cast hcd
  have h2 : ∃ z : GaussianInt, 2^r * m = z.norm := by
    use (⟨c,d⟩ : GaussianInt)
    have h3 : (⟨c,d⟩ : GaussianInt).norm = c*c- (-1)* d*d := Int.neg_inj.mp rfl
    simp only [Int.reduceNeg, neg_mul, one_mul, sub_neg_eq_add] at h3
    have h4 : (c : ℤ) * c + d*d = (c : ℤ)^2 + d^2 := by
      simp[pow_two]
    rw[h4] at h3
    rw[h3]
    have : (c : ℤ)^2 + (d : ℤ)^2 = ((c^2+d^2) : ℤ) := by exact (Int.add_left_inj (↑d ^ 2)).mpr rfl
    rw[this]
    simpa using hcdZ
  rw[cancel_pow_two_if_znorm m r] at h2
  rw[← sum_two_int_squares_iff_gaussian_norm m] at h2
  rw[sum_two_squares_Z_iff_N m] at h2
  rcases h2 with ⟨s,t,hst⟩
  have h3 : m ≡ 0 [MOD 4] ∨ m ≡ 1 [MOD 4] ∨ m ≡ 2 [MOD 4] := by
    rw[hst]
    exact sum_of_squares_mod_4 s t
  have h4 : ¬ m ≡ 0 [MOD 4] ∧ ¬ m ≡ 2 [MOD 4] := by
    have myh1 : m%2 =1 := by
      have : m%2 = 1 := by
        apply (odd_iff).mp
        exact hrm.2
      exact this
    rw[Nat.odd_mod_four_iff] at myh1
    cases myh1 with
    | inl h =>
      constructor
      · by_contra
        have hyp1 : m%4 = 0%4 := Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd this) n)
        have hyp2 : m % 4 = 1 % 4 :=  Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd h) n)
        rw[hyp2] at hyp1
        cases hyp1
      · by_contra
        have hyp1 : m%4 = 2%4 := Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd this) n)
        have hyp2 : m % 4 = 1 % 4 :=  Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd h) n)
        rw[hyp2] at hyp1
        cases hyp1
    | inr h =>
      constructor
      · by_contra
        have hyp1 : m%4 = 0%4
        := by exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd this) n)
        have hyp2 : m % 4 = 3 % 4 :=  Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd h) n)
        rw[hyp2] at hyp1
        cases hyp1
      · by_contra
        have hyp1 : m%4 = 2%4 := Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd this) n)
        have hyp2 : m % 4 = 3 % 4 :=  Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd h) n)
        rw[hyp2] at hyp1
        cases hyp1
  have h5 : m ≡ 1 [MOD 4] := by tauto
  have h6 : Even (countPrimeFactorsMod4Eq3 m)  := even_countPrimeFactorsMod4Eq3_of_modEq_one m h5
  have equal_countPrimeFactorsMod4Eq3
  : countPrimeFactorsMod4Eq3 m = countPrimeFactorsMod4Eq3 n := by
    rw[hrm.1]
    simp only [countPrimeFactorsMod4Eq3, Nat.support_factorization]
    have h2m_coprime : Coprime (2^r) m := by
      have hm2 : m ≡ 1 [MOD 2] := h5.of_dvd (by decide : (2 : ℕ) ∣ 4)
      have hOdd : Odd m := (Nat.odd_iff).2 hm2
      have h2 : ¬ (2 ∣ m) := hOdd.not_two_dvd_nat
      have hcop2 : Nat.Coprime 2 m := by
        exact (Nat.prime_two.coprime_iff_not_dvd).2 h2
      simpa using hcop2.pow_left r
    symm
    have h2prime : Nat.Prime 2 := prime_two
    refine Finset.sum_congr ?hs ?hg
    · ext p
      simp only [Finset.mem_filter, mem_primeFactors, ne_eq, _root_.mul_eq_zero, Nat.pow_eq_zero,
        OfNat.ofNat_ne_zero, false_and, false_or, and_congr_left_iff, and_congr_right_iff]
      intro hpmod4 hprimep hmne0
      constructor
      · intro hdiv
        have hdivcases : p ∣ 2^r ∨ p ∣ m := by exact Nat.Prime.dvd_or_dvd hprimep hdiv
        cases hdivcases with
        | inl h =>
          have hp2 : p ∣ 2 := hprimep.dvd_of_dvd_pow h
          have hpne1 : p ≠ 1 :=  Nat.Prime.ne_one hprimep
          have : p = 2 := (Nat.prime_dvd_prime_iff_eq hprimep h2prime).mp hp2
          rw[this] at hpmod4
          cases hpmod4
        | inr h =>
          exact h
      · intro hdivm
        exact Nat.dvd_mul_left_of_dvd hdivm (2 ^ r)
    · intro p hp
      have : (2^r * m).factorization p = (2^r).factorization p + m.factorization p
      := factorization_mul_apply_of_coprime h2m_coprime
      rw[this]
      have : (2^r).factorization = r • ((2).factorization) := by exact Nat.factorization_pow 2 r
      rw[this]
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.add_eq_right, _root_.mul_eq_zero]
      right
      have : p ≠ 2 := by
        by_contra c
        rw[c] at hp
        have hmod : 2% 4 = 3 := (Finset.mem_filter.mp hp).2
        cases hmod
      have hprimep : Nat.Prime p := by
        have : p ∈ m.primeFactors := (Finset.mem_filter.1 hp).1
        exact (Nat.mem_primeFactors.mp this).1
      have hpnot1 : p ≠ 1 := Nat.Prime.ne_one hprimep
      refine factorization_eq_zero_of_not_dvd ?_
      by_contra c
      rw[Nat.Prime.dvd_iff_eq h2prime hpnot1] at c
      tauto
  rw[equal_countPrimeFactorsMod4Eq3] at h6
  exact h6


theorem sum_split (α β : Type) [DecidableEq α] [AddCommMonoid β]
(s : Finset α) (f : α → β) {p : α} (hp : p ∈ s) :
        (∑ q ∈  s, f q) = f p + ∑ q ∈  s.erase p, f q := by
      have hs : insert p (s.erase p) = s := by
        simp only [Finset.insert_erase hp]  -- insert p (erase p s) = s

      -- now use sum_insert
      have hpnot : p ∉ s.erase p := by simp
      calc
        (∑ q ∈  s, f q)
            = ∑ q ∈  insert p (s.erase p), f q := by simp only [hs]
        _   = f p + ∑ q ∈  s.erase p, f q := by
              simp only [hpnot, not_false_eq_true, Finset.sum_insert]

#check Finset.even_sum

theorem even_other_prime_factors_impl_even
(p n a b : ℕ) (hdiv : p ∈ n.primeFactors) (hp : p ≡ 3 [MOD 4]) (hsumsq : n = a ^ 2 + b ^ 2)
: (∀ q ∈ n.primeFactors,
((q ≠ p ∧ q ≡ 3 [MOD 4]) → Even (n.factorization q))) → Even (n.factorization p) := by
  by_cases hn0 : n = 0
  · intro h
    rw[hn0]
    simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, Even.zero]
  · have heventotalfactors : Even (countPrimeFactorsMod4Eq3 n) := by
      exact even_primes_mod_4_if_sum_two_squares n a b hn0 hsumsq
    intro hotherfactorseven
    simp only [countPrimeFactorsMod4Eq3, Nat.support_factorization] at heventotalfactors
    have hpS : p ∈ n.primeFactors.filter (fun q => q % 4 = 3) := by
      apply Finset.mem_filter.2
      refine ⟨hdiv, ?_⟩
      simpa [Nat.ModEq] using hp
    have hsplit :
    (∑ q ∈ n.primeFactors.filter (fun q => q % 4 = 3), n.factorization q)
      =
    n.factorization p
      + ∑ q ∈ (n.primeFactors.filter (fun q => q % 4 = 3)).erase p, n.factorization q := by
      simpa using
        (sum_split ℕ ℕ
          (s := n.primeFactors.filter (fun q => q % 4 = 3))
          (f := fun q => n.factorization q)
          (p := p)
          hpS)
    rw[hsplit] at heventotalfactors
    have hconvertmod2 :
    (n.factorization p + ∑ q ∈ {q ∈ n.primeFactors | q % 4 = 3}.erase p, n.factorization q ) % 2 =0
    := even_iff.mp heventotalfactors
    have hdistrmod2 (a b : ℕ) (hab : (a+b)%2 = 0): a%2 = b%2 := by
      have : (a + b ) % 2 = (a % 2 + b % 2) % 2 := add_mod a b 2
      rw[this] at hab
      by_cases h : a%2 = 0
      · rw[h] at hab
        simp only [zero_add, dvd_refl, mod_mod_of_dvd] at hab
        rw[h, ← hab]
      · have h' : a % 2 = 1 :=  mod_two_ne_zero.mp h
        rw[h'] at hab
        simp only [add_mod_mod] at hab
        rw[ h']
        have hdistr : (1+b) % 2 = (1 % 2 + b % 2) % 2 := add_mod 1 b 2
        by_contra c
        have : b % 2 = 0 := mod_two_ne_one.mp fun a ↦ c (id (Eq.symm a))
        rw[hdistr] at hab
        rw[this] at hab
        simp only [mod_succ, add_zero, one_ne_zero] at hab
    apply hdistrmod2 (n.factorization p) at hconvertmod2
    set T : Finset ℕ := ({q ∈ n.primeFactors | q % 4 = 3}).erase p with hT
    have : (∑ q ∈ {q ∈ n.primeFactors | q % 4 = 3}.erase p, n.factorization q) % 2 =0 := by
      have hterm : ∀ q ∈ T, (n.factorization q) % 2 = 0 := by
        intro q hq
        have : Even (n.factorization q) → (n.factorization q) % 2 = 0
        := fun a ↦(fun {n} ↦ even_iff.mp) a
        apply this
        apply hotherfactorseven
        · have hq' : q ∈ ({q ∈ n.primeFactors | q % 4 = 3}).erase p := by
            simpa [hT] using hq
          have hq_in_filter : q ∈ {q ∈ n.primeFactors | q % 4 = 3} := Finset.mem_of_mem_erase hq
          exact Finset.mem_of_mem_filter q hq_in_filter
        · constructor
          · have hq' : q ∈ ({q ∈ n.primeFactors | q % 4 = 3}).erase p := by
              simpa [hT] using hq
            exact Finset.ne_of_mem_erase hq
          · have hq' : q ∈ ({q ∈ n.primeFactors | q % 4 = 3}).erase p := by
              simpa [hT] using hq
            exact (Finset.mem_filter.1 ((Finset.mem_erase.1 hq').2)).2
      have : (∑ q ∈  T, n.factorization q) % 2
      = (∑ q ∈  T, (n.factorization q % 2)) % 2 := by
        exact Finset.sum_nat_mod T 2 ⇑n.factorization
      rw[ ← hT]
      rw[this]
      --How to formalize this lemma was assisted by AI
      have hsum0 : (∑ q ∈  T, n.factorization q % 2) = 0 := by
        calc
          (∑ q ∈  T, n.factorization q % 2)
              = ∑ q ∈  T, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro q hq
                  simpa using (hterm q hq)
          _   = 0 := by simp
      rw[hsum0]
    rw[← hT] at this
    rw[this] at hconvertmod2
    exact even_iff.mpr hconvertmod2






--The idea of how to set up the induction with the correct scope of s is due to ChatGPT
theorem nat_sum_two_square (n : ℕ) :
    (∃ a b : ℕ, n = a^2 + b^2) ↔
      (∀ p ∈ n.primeFactors, p ≡ 3 [MOD 4] → Even (n.factorization p)) := by
  let P : Finset ℕ → Prop :=
    fun s =>
      ∀ n : ℕ, n.primeFactors = s →
        ((∃ a b : ℕ, n = a^2 + b^2) ↔
          (∀ p ∈ n.primeFactors, p ≡ 3 [MOD 4] → Even (n.factorization p)))

  have hP : P n.primeFactors := by
    classical
    refine Finset.induction_on (s := n.primeFactors) ?base ?step
    · intro n hn
      have hn01 : n = 0 ∨ n = 1 := by
        simpa only [primeFactors_eq_empty] using hn
      cases hn01 with
      | inl h =>
          constructor
          · intro hred
            repeat rw[hn]
            intro p hp
            exfalso
            exact (List.mem_nil_iff p).mp hp
          · intro hred
            use 0, 0
            linarith

      | inr h =>
          constructor
          · intro hred
            intro p hp
            rw[hn] at hp
            exfalso
            exact (List.mem_nil_iff p).mp hp
          · intro hred
            use 1 , 0
            linarith





    · intro q s hqnotmem ih
      intro n hn
      have hqprime : Nat.Prime q := by
        have hpmem : q ∈ n.primeFactors := by
          rw[hn]
          exact Finset.mem_insert_self q s
        exact prime_of_mem_primeFactors hpmem
      have hmeminsert (p : ℕ) : p ∈ insert q s ↔  p = q ∨ p ∈ s:= Finset.mem_insert

      constructor
      · /-Sketch: define m to be the product of all the primes in s raised to their valuations;
        equivalently m = n/q^r where r is the q-adic valuation of n.
        By the inductive hypothesis, for each p in m.primeFactors, p≡3 [MOD 4], 2 ∣ m.factorization p
        Then we prove that for all primes p ≠ q, m.factorization p = n.factorization p
        Then we split into cases based on p = q or p ≠ q, the latter case done by rw
        We suppose for a contradiction that 2 ∣ n.factorization q
        We write m = x.norm for some x : GaussianInt
        Now we show n/q = (x*q^(r/2)).norm (Note : we use the fact that r/2 = (r-1)/2))
        We write q^r as (q^(r/2)).norm
        Then (x * q^(r/2)).norm =
        Using a theorem to be proved, that x.norm = y.norm ↔ ∃ u, IsUnit u, y = u * x, we conclude
        from z.norm = n = ()

        -/
        intro h1
        rcases h1 with ⟨a,b,hnab⟩
        rw[hn]
        intro p hp
        rw[hmeminsert p] at hp
        cases hp with
        | inl h =>
          intro h1mod4






  -- finally apply hP to your original n (this last line is usually `exact (hP n rfl)` if you’re not inlined)
  exact hP n rfl
