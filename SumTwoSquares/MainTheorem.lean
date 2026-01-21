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



theorem p_mod_4_is_3_is_prime (p : ℕ) [Fact (Nat.Prime p)] (hpmod4 : p ≡ 3 [MOD 4]) : _root_.Prime (p : GaussianInt) := by
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


--The idea of how to set up the induction with the correct scope of s is due to ChatGPT
theorem nat_sum_two_square (n : ℕ) :
    (∃ a b : ℕ, n = a^2 + b^2) ↔
      (∀ p ∈ n.primeFactors, p ≡ 3 [MOD 4] → 2 ∣ n.factorization p) := by
  let P : Finset ℕ → Prop :=
    fun s =>
      ∀ n : ℕ, n.primeFactors = s →
        ((∃ a b : ℕ, n = a^2 + b^2) ↔
          (∀ p ∈ n.primeFactors, p ≡ 3 [MOD 4] → 2 ∣ n.factorization p))

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
      have hpprime : Nat.Prime q := by
        have hpmem : q ∈ n.primeFactors := by
          rw[hn]
          exact Finset.mem_insert_self q s
        exact prime_of_mem_primeFactors hpmem
      have hmeminsert (p : ℕ) : p ∈ insert q s ↔  p = q ∨ p ∈ s:= Finset.mem_insert


      constructor
      · intro h1
        rcases h1 with ⟨a,b,hnab⟩
        rw[hn]
        intro p hp
        rw[hmeminsert p] at hp
        cases hp with
        | inl h =>
          intro h1mod4






  -- finally apply hP to your original n (this last line is usually `exact (hP n rfl)` if you’re not inlined)
  exact hP n rfl
