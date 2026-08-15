import FormalConjectures.OEIS.«211417»

/-!
# OEIS A211417: active Formal Conjectures targets

This file targets the five mathematically substantive `research open` declarations in
`FormalConjectures.OEIS.211417`.  The vacuous current statement `general_divisibility` is
deliberately excluded.

All four divisibility targets are now proved. The product theorem is derived from the three
atomic statements. Only the independent supercongruence target remains open in this file.
-/

namespace OeisA211417Proof

/-
## Shared p-adic kernel

The following lemmas adapt the Landau-function part of the existing Formal Conjectures proof of
`(30n-1) ∣ a(n)`.  They are the common input for all three atomic targets.
-/

/-- The local contribution of a prime power `d` to the valuation of `a(x)`. -/
def landauTerm (x d : ℕ) : ℤ :=
  (↑((30 * x) / d) : ℤ) + ↑(x / d) - ↑((15 * x) / d) -
    ↑((10 * x) / d) - ↑((6 * x) / d)

private lemma mul_div_decompose (c n d : ℕ) :
    c * n / d = c * (n / d) + c * (n % d) / d := by
  exact d.eq_zero_or_pos.elim (by simp_all)
    (by rw [← d.mul_add_div ·, mul_left_comm, ← mul_add, Nat.div_add_mod])

private lemma div_half (s d : ℕ) : (15 * s) / d = ((30 * s) / d) / 2 := by
  exact (2).mul_div_mul_right _ _ (by decide) ▸ Nat.mul_right_comm _ _ _ ▸
    (Nat.div_div_eq_div_mul _ _ _).symm

private lemma div_third (s d : ℕ) : (10 * s) / d = ((30 * s) / d) / 3 := by
  exact (3).mul_div_mul_right _ _ (by decide) ▸ Nat.mul_right_comm _ _ _ ▸
    (Nat.div_div_eq_div_mul _ _ _).symm

private lemma div_fifth (s d : ℕ) : (6 * s) / d = ((30 * s) / d) / 5 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.mul_div_mul_right _ _ (by decide : 0 < 5),
    Nat.mul_right_comm]

private lemma small_floor_sum (k : ℕ) (hk : k ≤ 29) :
    k / 2 + k / 3 + k / 5 ≤ k := by
  classical decide +revert

private lemma scaled_remainder_le (n d : ℕ) (hd : d > 0) :
    30 * (n % d) / d ≤ 29 := by
  exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul
    (by push_cast [Nat.mul_lt_mul_left _, mul_comm d, n.mod_lt hd]))

/-- Every prime-power contribution to the A211417 factorial ratio is nonnegative. -/
theorem landauTerm_nonneg (x d : ℕ) : 0 ≤ landauTerm x d := by
  by_cases hd : d = 0
  · subst hd
    simp [landauTerm]
  · have hd_pos : d > 0 := Nat.pos_of_ne_zero hd
    have h1 : 15 * x / d = 15 * (x / d) + 15 * (x % d) / d :=
      mul_div_decompose 15 x d
    have h2 : 10 * x / d = 10 * (x / d) + 10 * (x % d) / d :=
      mul_div_decompose 10 x d
    have h3 : 6 * x / d = 6 * (x / d) + 6 * (x % d) / d :=
      mul_div_decompose 6 x d
    have h4 : 30 * x / d = 30 * (x / d) + 30 * (x % d) / d :=
      mul_div_decompose 30 x d
    have h5 : 15 * (x % d) / d = (30 * (x % d) / d) / 2 := div_half (x % d) d
    have h6 : 10 * (x % d) / d = (30 * (x % d) / d) / 3 := div_third (x % d) d
    have h7 : 6 * (x % d) / d = (30 * (x % d) / d) / 5 := div_fifth (x % d) d
    have h8 : 30 * (x % d) / d ≤ 29 := scaled_remainder_le x d hd_pos
    have h9 := small_floor_sum (30 * (x % d) / d) h8
    unfold landauTerm
    zify at *
    omega

/-- The Landau contribution depends only on `x mod d`. -/
theorem landauTerm_eq_mod (x d : ℕ) :
    landauTerm x d = landauTerm (x % d) d := by
  by_cases hd : d = 0
  · subst hd
    simp [landauTerm]
  · have hr : x % d < d := Nat.mod_lt x (Nat.pos_of_ne_zero hd)
    have hrdiv : x % d / d = 0 := Nat.div_eq_of_lt hr
    rw [landauTerm, landauTerm, mul_div_decompose 30 x d,
      mul_div_decompose 15 x d, mul_div_decompose 10 x d,
      mul_div_decompose 6 x d, hrdiv]
    push_cast
    ring

private lemma mod_eq_div_two_of_dvd_two_mul_add_one
    (n d : ℕ) (hdOdd : Odd d) (hdiv : d ∣ 2 * n + 1) :
    n % d = d / 2 := by
  obtain ⟨c, hc⟩ := hdiv
  have hprodOdd : Odd (d * c) := by
    rw [← hc]
    exact odd_two_mul_add_one n
  have hcOdd : Odd c := Nat.Odd.of_mul_right hprodOdd
  obtain ⟨q, hq⟩ := odd_iff_exists_bit1.mp hcOdd
  have hdform : 2 * (d / 2) + 1 = d := Nat.two_mul_div_two_add_one_of_odd hdOdd
  have heq : d * (2 * q + 1) = 2 * (q * d + d / 2) + 1 := by
    calc
      d * (2 * q + 1) = 2 * (q * d) + d := by ring
      _ = 2 * (q * d + d / 2) + 1 := by omega
  rw [hq] at hc
  have hnform : n = q * d + d / 2 := by omega
  have hdpos : 0 < d := by omega
  have hr : d / 2 < d := Nat.div_lt_self hdpos (by decide)
  rw [hnform]
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr]

/--
For every odd `d ≥ 9`, a divisor `d ∣ 2n+1` contributes exactly one to the valuation
of the factorial ratio.  The excluded values `3`, `5`, and `7` are precisely the exceptional
prime powers for the first atomic target.
-/
theorem landauTerm_eq_one_of_dvd_two_mul_add_one
    (n d : ℕ) (hdOdd : Odd d) (hd9 : 9 ≤ d) (hdiv : d ∣ 2 * n + 1) :
    landauTerm n d = 1 := by
  rw [landauTerm_eq_mod, mod_eq_div_two_of_dvd_two_mul_add_one n d hdOdd hdiv]
  by_cases hd17 : 17 ≤ d
  · let r := d / 2
    have hdform : 2 * r + 1 = d := Nat.two_mul_div_two_add_one_of_odd hdOdd
    have hr8 : 8 ≤ r := by omega
    have hrlt : r < d := by omega
    have h30 : 30 * r / d = 14 :=
      (14).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 7 :=
      (7).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 4 :=
      (4).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 2 :=
      (2).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hrlt
    norm_num [landauTerm, r, h30, h15, h10, h6, hrdiv]
  · have hdlt : d < 17 := by omega
    interval_cases d <;> norm_num [landauTerm] at *

private lemma padic_factorial_sum (p n : ℕ) [Fact p.Prime] :
    padicValNat p (Nat.factorial n) =
      ∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i := by
  apply padicValNat_factorial (Nat.succ_le_succ (p.log_le_self n))

/-- Legendre's formula expresses the numerator-minus-denominator valuation as Landau terms. -/
theorem valuation_gap_eq_sum (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
      ((padicValNat p (15 * n).factorial : ℤ) +
        (padicValNat p (10 * n).factorial : ℤ) +
        (padicValNat p (6 * n).factorial : ℤ)) =
      ∑ j ∈ Finset.Ico 1 (30 * n + 1), landauTerm n (p ^ j) := by
  delta landauTerm
  push_cast [Fact.mk hp, sub_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  repeat
    rw_mod_cast [match Fact.mk hp with
      | fact => padicValNat_factorial
          (Nat.succ_le_succ ((p.log_le_self _).trans (by valid : _ ≤ 30 * n)))]

/-- The full `5`-primary part of `2n+1` divides the indicated binomial coefficient. -/
theorem five_primary_dvd_choose (n : ℕ) :
    5 ^ padicValNat 5 (2 * n + 1) ∣ (5 * n).choose (2 * n) := by
  let q := 5 ^ padicValNat 5 (2 * n + 1)
  have hq : q ∣ 2 * n + 1 := pow_padicValNat_dvd
  have hmn : Nat.Coprime (2 * n + 1) n := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.coprime_add_mul_left_left 1 n 2).2 (Nat.coprime_one_left n)
  have hqn : Nat.Coprime q n := hmn.coprime_dvd_left hq
  have h53 : Nat.Coprime 5 3 := by norm_num
  have hq3 : Nat.Coprime q 3 := h53.pow_left _
  have hcop : Nat.Coprime q (3 * n) := hq3.mul_right hqn
  have hprod : q ∣ (5 * n).choose (2 * n) * (3 * n) := by
    rw [← show 5 * n - 2 * n = 3 * n by omega,
      ← Nat.choose_succ_right_eq (5 * n) (2 * n)]
    exact hq.mul_left ((5 * n).choose (2 * n + 1))
  rw [Nat.mul_comm] at hprod
  exact hcop.dvd_of_dvd_mul_left hprod

/-- At `p = 5`, the valuation gap of the A211417 factorial ratio is a binomial valuation. -/
theorem five_valuation_gap_eq_choose (n : ℕ) :
    (padicValNat 5 (30 * n).factorial : ℤ) +
        (padicValNat 5 n.factorial : ℤ) -
      ((padicValNat 5 (15 * n).factorial : ℤ) +
        (padicValNat 5 (10 * n).factorial : ℤ) +
        (padicValNat 5 (6 * n).factorial : ℤ)) =
      (padicValNat 5 ((5 * n).choose (2 * n)) : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h30 : padicValNat 5 (30 * n).factorial =
      padicValNat 5 (6 * n).factorial + 6 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 5) (6 * n))
  have h15 : padicValNat 5 (15 * n).factorial =
      padicValNat 5 (3 * n).factorial + 3 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 5) (3 * n))
  have h10 : padicValNat 5 (10 * n).factorial =
      padicValNat 5 (2 * n).factorial + 2 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 5) (2 * n))
  have h5 : padicValNat 5 (5 * n).factorial =
      padicValNat 5 n.factorial + n := by
    simpa using padicValNat_factorial_mul (p := 5) n
  have hchoose_ne : (5 * n).choose (2 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hfac : (5 * n).choose (2 * n) * (2 * n).factorial * (3 * n).factorial =
      (5 * n).factorial := by
    simpa [show 5 * n - 2 * n = 3 * n by omega] using
      (Nat.choose_mul_factorial_mul_factorial (show 2 * n ≤ 5 * n by omega))
  have hvleft := padicValNat.mul (p := 5) hchoose_ne (Nat.factorial_ne_zero (2 * n))
  have hvprod := padicValNat.mul (p := 5)
    (Nat.mul_ne_zero hchoose_ne (Nat.factorial_ne_zero (2 * n)))
    (Nat.factorial_ne_zero (3 * n))
  have hchoose :
      padicValNat 5 ((5 * n).choose (2 * n)) +
          padicValNat 5 (2 * n).factorial + padicValNat 5 (3 * n).factorial =
        padicValNat 5 (5 * n).factorial := by
    rw [hfac] at hvprod
    rw [hvleft] at hvprod
    omega
  have h30z : (padicValNat 5 (30 * n).factorial : ℤ) =
      (padicValNat 5 (6 * n).factorial : ℤ) + 6 * n := by exact_mod_cast h30
  have h15z : (padicValNat 5 (15 * n).factorial : ℤ) =
      (padicValNat 5 (3 * n).factorial : ℤ) + 3 * n := by exact_mod_cast h15
  have h10z : (padicValNat 5 (10 * n).factorial : ℤ) =
      (padicValNat 5 (2 * n).factorial : ℤ) + 2 * n := by exact_mod_cast h10
  have h5z : (padicValNat 5 (5 * n).factorial : ℤ) =
      (padicValNat 5 n.factorial : ℤ) + n := by exact_mod_cast h5
  have hchoosez :
      (padicValNat 5 ((5 * n).choose (2 * n)) : ℤ) +
          padicValNat 5 (2 * n).factorial + padicValNat 5 (3 * n).factorial =
        padicValNat 5 (5 * n).factorial := by exact_mod_cast hchoose
  omega

/-- The `5`-adic valuation required by `(2n+1) ∣ 7a(n)` is fully accounted for. -/
theorem five_primary_le_valuation_gap (n : ℕ) :
    (padicValNat 5 (2 * n + 1) : ℤ) ≤
      (padicValNat 5 (30 * n).factorial : ℤ) +
        (padicValNat 5 n.factorial : ℤ) -
        ((padicValNat 5 (15 * n).factorial : ℤ) +
          (padicValNat 5 (10 * n).factorial : ℤ) +
          (padicValNat 5 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : padicValNat 5 (2 * n + 1) ≤
      padicValNat 5 ((5 * n).choose (2 * n)) :=
    (padicValNat_dvd_iff_le (Nat.choose_ne_zero (by omega))).mp
      (five_primary_dvd_choose n)
  rw [five_valuation_gap_eq_choose]
  exact_mod_cast hle

/-- The valuation of `2n+1` as a finite sum of prime-power divisibility indicators. -/
theorem two_mul_add_one_valuation_indicator (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (2 * n + 1) : ℤ) =
      ∑ j ∈ Finset.Ico 1 (30 * n + 1),
        if p ^ j ∣ 2 * n + 1 then (1 : ℤ) else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hval_lt : padicValNat p (2 * n + 1) < 2 * n + 1 := by
      rw [← Nat.factorization_def (2 * n + 1) hp]
      exact Nat.factorization_lt p (by omega)
    have hval_bound : padicValNat p (2 * n + 1) ≤ 30 * n :=
      hval_lt.le.trans (by omega)
    norm_num [padicValNat_dvd_iff_le (by omega : 2 * n + 1 ≠ 0), Fact.mk hp,
      ← Nat.factorization_def _, ← Finset.mem_Icc,
      hp.pow_dvd_iff_le_factorization (by omega : 2 * n + 1 ≠ 0), hnpos]
    exact (((congr_arg _) (Finset.ext (by
      simp_all [·.lt_succ] <;> omega))).trans
      ((1).card_Icc (padicValNat p (2 * n + 1)))).symm

/-- Away from `2`, `3`, `5`, and `7`, every required prime-power indicator is pointwise paid. -/
theorem generic_primary_le_valuation_gap
    (n p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (padicValNat p (2 * n + 1) : ℤ) ≤
      (padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ)) := by
  rw [two_mul_add_one_valuation_indicator n p hp, valuation_gap_eq_sum n p hp]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  by_cases hd : p ^ j ∣ 2 * n + 1
  · have hp11 : 11 ≤ p := by
      by_contra h
      have hple : p ≤ 10 := by omega
      interval_cases p <;> norm_num at hp
      all_goals omega
    have hodd : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
    have hpow : p ≤ p ^ j := by simpa using Nat.pow_le_pow_right hp.pos hj1
    have hd9 : 9 ≤ p ^ j := by omega
    have heq := landauTerm_eq_one_of_dvd_two_mul_add_one n (p ^ j) hodd hd9 hd
    simpa [hd, heq]
  · simpa [hd] using landauTerm_nonneg n (p ^ j)

/-- At `p = 7`, the external factor `7` pays for the sole exceptional level `j = 1`. -/
theorem seven_primary_le_one_add_valuation_gap (n : ℕ) :
    (padicValNat 7 (2 * n + 1) : ℤ) ≤ 1 +
      ((padicValNat 7 (30 * n).factorial : ℤ) +
        (padicValNat 7 n.factorial : ℤ) -
        ((padicValNat 7 (15 * n).factorial : ℤ) +
          (padicValNat 7 (10 * n).factorial : ℤ) +
          (padicValNat 7 (6 * n).factorial : ℤ))) := by
  rw [two_mul_add_one_valuation_indicator n 7 (by norm_num),
    valuation_gap_eq_sum n 7 (by norm_num)]
  let S := Finset.Ico 1 (30 * n + 1)
  have hpoint : ∀ j ∈ S,
      (if 7 ^ j ∣ 2 * n + 1 then (1 : ℤ) else 0) ≤
        (if j = 1 then (1 : ℤ) else 0) + landauTerm n (7 ^ j) := by
    intro j hj
    by_cases hjone : j = 1
    · subst j
      have hnonneg := landauTerm_nonneg n 7
      by_cases hd : 7 ∣ 2 * n + 1 <;> simp [hd] <;> omega
    · have hj2 : 2 ≤ j := by
        have := (Finset.mem_Ico.mp hj).1
        omega
      by_cases hd : 7 ^ j ∣ 2 * n + 1
      · have hodd : Odd (7 ^ j) := (by norm_num : Odd 7).pow
        have hpow : 7 ^ 2 ≤ 7 ^ j := Nat.pow_le_pow_right (by decide) hj2
        have hd9 : 9 ≤ 7 ^ j := by norm_num at hpow ⊢; omega
        have heq := landauTerm_eq_one_of_dvd_two_mul_add_one n (7 ^ j) hodd hd9 hd
        simp [hjone, hd, heq]
      · simpa [hjone, hd] using landauTerm_nonneg n (7 ^ j)
  have hsum := Finset.sum_le_sum hpoint
  have hbad : (∑ j ∈ S, if j = 1 then (1 : ℤ) else 0) ≤ 1 := by
    classical
    simp only [Finset.sum_ite_eq']
    split <;> simp
  rw [Finset.sum_add_distrib] at hsum
  dsimp [S] at hsum hbad
  omega

/-
## The exceptional `p = 3` carry

When `e = v₃(2n+1)`, the levels `2, …, e` each contribute one.  The lemmas below
construct one further level above `e` whose Landau contribution is exactly one.
-/

private lemma scaled_affine_div (s A r d : ℕ) (hs : 0 < s) (hr : r < s) :
    (s * A + r) / (s * d) = A / d := by
  rw [← Nat.div_div_eq_div_mul]
  have hrdiv : r / s = 0 := Nat.div_eq_of_lt hr
  rw [show s * A + r = r + s * A by omega,
    Nat.add_mul_div_left _ _ hs, hrdiv, zero_add]

private lemma shifted_landau_of_large_scale
    (s q d : ℕ) (hs15 : 15 ≤ s) (hsOdd : Odd s) :
    landauTerm (s * q + s / 2) (s * d) =
      (↑((30 * q + 14) / d) : ℤ) + ↑(q / d) -
        ↑((15 * q + 7) / d) - ↑((10 * q + 4) / d) -
        ↑((6 * q + 2) / d) := by
  have hspos : 0 < s := by omega
  have hsform : 2 * (s / 2) + 1 = s := Nat.two_mul_div_two_add_one_of_odd hsOdd
  have hhalf : s / 2 < s := Nat.div_lt_self hspos (by decide)
  have h15half : (s - 15) / 2 = s / 2 - 7 := by omega
  have h30eq : 30 * (s * q + s / 2) = s * (30 * q + 14) + (s - 15) := by
    ring_nf
    omega
  have h15eq : 15 * (s * q + s / 2) =
      s * (15 * q + 7) + (s - 15) / 2 := by
    ring_nf
    omega
  have h10eq : 10 * (s * q + s / 2) = s * (10 * q + 4) + (s - 5) := by
    ring_nf
    omega
  have h6eq : 6 * (s * q + s / 2) = s * (6 * q + 2) + (s - 3) := by
    ring_nf
    omega
  have h30r : s - 15 < s := by omega
  have h15r : (s - 15) / 2 < s := by omega
  have h10r : s - 5 < s := by omega
  have h6r : s - 3 < s := by omega
  rw [landauTerm, h30eq, h15eq, h10eq, h6eq,
    scaled_affine_div s (30 * q + 14) (s - 15) d hspos h30r,
    scaled_affine_div s (15 * q + 7) ((s - 15) / 2) d hspos h15r,
    scaled_affine_div s (10 * q + 4) (s - 5) d hspos h10r,
    scaled_affine_div s (6 * q + 2) (s - 3) d hspos h6r,
    scaled_affine_div s q (s / 2) d hspos hhalf]

private lemma shifted_landau_nine (q d : ℕ) :
    landauTerm (9 * q + 4) (9 * d) =
      (↑((30 * q + 13) / d) : ℤ) + ↑(q / d) -
        ↑((15 * q + 6) / d) - ↑((10 * q + 4) / d) -
        ↑((6 * q + 2) / d) := by
  rw [landauTerm,
    show 30 * (9 * q + 4) = 9 * (30 * q + 13) + 3 by ring,
    show 15 * (9 * q + 4) = 9 * (15 * q + 6) + 6 by ring,
    show 10 * (9 * q + 4) = 9 * (10 * q + 4) + 4 by ring,
    show 6 * (9 * q + 4) = 9 * (6 * q + 2) + 6 by ring,
    scaled_affine_div 9 (30 * q + 13) 3 d (by norm_num) (by norm_num),
    scaled_affine_div 9 (15 * q + 6) 6 d (by norm_num) (by norm_num),
    scaled_affine_div 9 (10 * q + 4) 4 d (by norm_num) (by norm_num),
    scaled_affine_div 9 (6 * q + 2) 6 d (by norm_num) (by norm_num),
    scaled_affine_div 9 q 4 d (by norm_num) (by norm_num)]

private lemma three_landau_extra_e_one (q : ℕ) :
    landauTerm (3 * q + 1) (3 ^ (1 + 1)) = 1 := by
  have h30 : 30 * (3 * q + 1) / 9 = 10 * q + 3 := by
    rw [show 30 * (3 * q + 1) = 9 * (10 * q + 3) + 3 by ring,
      scaled_affine_div 9 (10 * q + 3) 3 1 (by norm_num) (by norm_num)]
    simp
  have hn : (3 * q + 1) / 9 = q / 3 := by
    rw [scaled_affine_div 3 q 1 3 (by norm_num) (by norm_num)]
  have h15 : 15 * (3 * q + 1) / 9 = 5 * q + 1 := by
    rw [show 15 * (3 * q + 1) = 9 * (5 * q + 1) + 6 by ring,
      scaled_affine_div 9 (5 * q + 1) 6 1 (by norm_num) (by norm_num)]
    simp
  have h10 : 10 * (3 * q + 1) / 9 = 3 * q + 1 + q / 3 := by
    rw [show 10 * (3 * q + 1) = 3 * (10 * q + 3) + 1 by ring,
      scaled_affine_div 3 (10 * q + 3) 1 3 (by norm_num) (by norm_num)]
    rw [show 10 * q + 3 = q + 3 * (3 * q + 1) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    omega
  have h6 : 6 * (3 * q + 1) / 9 = 2 * q := by
    rw [show 6 * (3 * q + 1) = 9 * (2 * q) + 6 by ring,
      scaled_affine_div 9 (2 * q) 6 1 (by norm_num) (by norm_num)]
    simp
  rw [show 3 ^ (1 + 1) = 9 by norm_num, landauTerm, h30, hn, h15, h10, h6]
  push_cast
  ring

private lemma shifted_fourteen_eq_one
    (q d : ℕ) (hlo : 9 * q < d) (hhi : d ≤ 27 * q) :
    (30 * q + 14) / d + q / d -
      ((15 * q + 7) / d + (10 * q + 4) / d + (6 * q + 2) / d) = 1 := by
  have hd : 0 < d := by omega
  have hqdiv : q / d = 0 := Nat.div_eq_of_lt (by omega)
  let A := (15 * q + 7) / d
  let B := (10 * q + 4) / d
  let C := (6 * q + 2) / d
  let G := (30 * q + 14) / d
  have hAlo : A * d ≤ 15 * q + 7 := Nat.div_mul_le_self _ _
  have hAhi : 15 * q + 7 < A * d + d := Nat.lt_div_mul_add hd
  have hBlo : B * d ≤ 10 * q + 4 := Nat.div_mul_le_self _ _
  have hBhi : 10 * q + 4 < B * d + d := Nat.lt_div_mul_add hd
  have hClo : C * d ≤ 6 * q + 2 := Nat.div_mul_le_self _ _
  have hChi : 6 * q + 2 < C * d + d := Nat.lt_div_mul_add hd
  have hGlo : G * d ≤ 30 * q + 14 := Nat.div_mul_le_self _ _
  have hGhi : 30 * q + 14 < G * d + d := Nat.lt_div_mul_add hd
  have hA : A ≤ 2 := by
    have : 15 * q + 7 < 3 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hB : B ≤ 1 := by
    have : 10 * q + 4 < 2 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hC : C = 0 := by
    apply Nat.div_eq_of_lt
    omega
  have hGlo1 : 1 ≤ G := by
    apply (Nat.le_div_iff_mul_le hd).2
    omega
  have hG : G ≤ 4 := by
    have : 30 * q + 14 < 5 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  change G + q / d - (A + B + C) = 1
  rw [hqdiv, hC]
  interval_cases A <;> interval_cases B <;> interval_cases G <;> omega

private lemma shifted_thirteen_eq_one
    (q d : ℕ) (hlo : 9 * q < d) (hhi : d ≤ 27 * q) :
    (30 * q + 13) / d + q / d -
      ((15 * q + 6) / d + (10 * q + 4) / d + (6 * q + 2) / d) = 1 := by
  have hd : 0 < d := by omega
  have hqdiv : q / d = 0 := Nat.div_eq_of_lt (by omega)
  let A := (15 * q + 6) / d
  let B := (10 * q + 4) / d
  let C := (6 * q + 2) / d
  let G := (30 * q + 13) / d
  have hAlo : A * d ≤ 15 * q + 6 := Nat.div_mul_le_self _ _
  have hAhi : 15 * q + 6 < A * d + d := Nat.lt_div_mul_add hd
  have hBlo : B * d ≤ 10 * q + 4 := Nat.div_mul_le_self _ _
  have hBhi : 10 * q + 4 < B * d + d := Nat.lt_div_mul_add hd
  have hClo : C * d ≤ 6 * q + 2 := Nat.div_mul_le_self _ _
  have hChi : 6 * q + 2 < C * d + d := Nat.lt_div_mul_add hd
  have hGlo : G * d ≤ 30 * q + 13 := Nat.div_mul_le_self _ _
  have hGhi : 30 * q + 13 < G * d + d := Nat.lt_div_mul_add hd
  have hA : A ≤ 2 := by
    have : 15 * q + 6 < 3 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hB : B ≤ 1 := by
    have : 10 * q + 4 < 2 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hC : C = 0 := by
    apply Nat.div_eq_of_lt
    omega
  have hGlo1 : 1 ≤ G := by
    apply (Nat.le_div_iff_mul_le hd).2
    omega
  have hG : G ≤ 4 := by
    have : 30 * q + 13 < 5 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  change G + q / d - (A + B + C) = 1
  rw [hqdiv, hC]
  interval_cases A <;> interval_cases B <;> interval_cases G <;> omega

/-- A prime-power level above `e` supplies the one contribution missing at `3¹`. -/
theorem three_extra_landau_term (n e : ℕ) (he : 0 < e)
    (hdiv : 3 ^ e ∣ 2 * n + 1) :
    ∃ t : ℕ, 0 < t ∧ e + t ≤ 30 * n ∧
      landauTerm n (3 ^ (e + t)) = 1 := by
  let s := 3 ^ e
  let q := n / s
  have hsOdd : Odd s := (by norm_num : Odd 3).pow
  have hspos : 0 < s := pow_pos (by norm_num) _
  have hmod : n % s = s / 2 :=
    mod_eq_div_two_of_dvd_two_mul_add_one n s hsOdd hdiv
  have hrep : n = s * q + s / 2 := by
    dsimp [q]
    rw [← hmod]
    simpa [Nat.mul_comm] using (Nat.div_add_mod' n s).symm
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hone : 2 * n + 1 = 1 := by omega
    rw [hone] at hdiv
    have hsle : s ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    have h3le : 3 ≤ s := by
      dsimp [s]
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) he
      norm_num at this ⊢
      exact this
    omega
  have he_lt : e < 2 * n + 1 := by
    have hpowle : 3 ^ e ≤ 2 * n + 1 := Nat.le_of_dvd (by omega) hdiv
    have helt : e < 3 ^ e := Nat.lt_pow_self (by norm_num)
    omega
  by_cases he1 : e = 1
  · subst e
    refine ⟨1, by norm_num, by omega, ?_⟩
    norm_num [s] at hrep
    simpa [hrep] using three_landau_extra_e_one q
  by_cases hq0 : q = 0
  · have hrep0 : n = s * 0 + s / 2 := by simpa [hq0] using hrep
    refine ⟨1, by norm_num, by omega, ?_⟩
    by_cases he2 : e = 2
    · subst e
      norm_num [s] at hrep0
      rw [hrep0, show 3 ^ (2 + 1) = 9 * 3 by norm_num,
        shifted_landau_nine 0 3]
      norm_num
    · have he3 : 3 ≤ e := by omega
      have hs15 : 15 ≤ s := by
        have : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he3
        norm_num [s] at this ⊢
        omega
      rw [hrep0, show 3 ^ (e + 1) = s * 3 by simp [s, pow_add]]
      simpa using shifted_landau_of_large_scale s 0 3 hs15 hsOdd
  · let l := Nat.log 3 q
    let d := 3 ^ (l + 3)
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hq_lt : q < 3 ^ (l + 1) := by
      simpa [l] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) q
    have hpow_le : 3 ^ l ≤ q := by
      simpa [l] using Nat.pow_log_le_self 3 hq0
    have hlo : 9 * q < d := by
      have hmul : 9 * q < 9 * 3 ^ (l + 1) := by omega
      calc
        9 * q < 9 * 3 ^ (l + 1) := hmul
        _ = 3 ^ (l + 3) := by simp [pow_add]; ring
        _ = d := rfl
    have hhi : d ≤ 27 * q := by
      simpa [d, pow_add, mul_comm, mul_left_comm, mul_assoc] using
        Nat.mul_le_mul_left 27 hpow_le
    have hlq : l ≤ q := Nat.log_le_self 3 q
    have hqn : q ≤ n := by
      dsimp [q]
      exact Nat.div_le_self n s
    refine ⟨l + 3, by omega, by omega, ?_⟩
    have hpow : 3 ^ (e + (l + 3)) = s * d := by simp [s, d, pow_add]
    by_cases he2 : e = 2
    · subst e
      norm_num [s] at hrep hpow
      rw [hrep, hpow, shifted_landau_nine q d]
      have hnat := shifted_thirteen_eq_one q d hlo hhi
      have heq : (30 * q + 13) / d + q / d =
          (15 * q + 6) / d + (10 * q + 4) / d + (6 * q + 2) / d + 1 := by
        omega
      have heqz : (↑((30 * q + 13) / d) : ℤ) + ↑(q / d) =
          ↑((15 * q + 6) / d) + ↑((10 * q + 4) / d) +
            ↑((6 * q + 2) / d) + 1 := by exact_mod_cast heq
      omega
    · have he3 : 3 ≤ e := by omega
      have hs15 : 15 ≤ s := by
        have : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he3
        norm_num [s] at this ⊢
        omega
      rw [hrep, hpow, shifted_landau_of_large_scale s q d hs15 hsOdd]
      have hnat := shifted_fourteen_eq_one q d hlo hhi
      have heq : (30 * q + 14) / d + q / d =
          (15 * q + 7) / d + (10 * q + 4) / d + (6 * q + 2) / d + 1 := by
        omega
      have heqz : (↑((30 * q + 14) / d) : ℤ) + ↑(q / d) =
          ↑((15 * q + 7) / d) + ↑((10 * q + 4) / d) +
            ↑((6 * q + 2) / d) + 1 := by exact_mod_cast heq
      omega

/-- The factorial-ratio valuation gap is nonnegative at every prime. -/
theorem valuation_gap_nonneg (n p : ℕ) (hp : p.Prime) :
    0 ≤ (padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ)) := by
  rw [valuation_gap_eq_sum n p hp]
  apply Finset.sum_nonneg
  intro j hj
  exact landauTerm_nonneg n (p ^ j)

/-- The complete exceptional `3`-primary estimate for `(2n+1) ∣ 7a(n)`. -/
theorem three_primary_le_valuation_gap (n : ℕ) :
    (padicValNat 3 (2 * n + 1) : ℤ) ≤
      (padicValNat 3 (30 * n).factorial : ℤ) +
        (padicValNat 3 n.factorial : ℤ) -
        ((padicValNat 3 (15 * n).factorial : ℤ) +
          (padicValNat 3 (10 * n).factorial : ℤ) +
          (padicValNat 3 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e := padicValNat 3 (2 * n + 1)
  by_cases he0 : e = 0
  · rw [show padicValNat 3 (2 * n + 1) = 0 by exact he0, Nat.cast_zero]
    exact valuation_gap_nonneg n 3 (by norm_num)
  · have he : 0 < e := Nat.pos_of_ne_zero he0
    have hediv : 3 ^ e ∣ 2 * n + 1 := by
      dsimp [e]
      exact pow_padicValNat_dvd
    obtain ⟨t, ht, hJbound, hextra⟩ := three_extra_landau_term n e he hediv
    let J := e + t
    let S := Finset.Ico 1 (30 * n + 1)
    have hJpos : 1 ≤ J := by dsimp [J]; omega
    have hJmem : J ∈ S := by
      rw [Finset.mem_Ico]
      dsimp [J, S] at *
      omega
    have hnpos : 0 < n := by omega
    have h1mem : 1 ∈ S := by
      rw [Finset.mem_Ico]
      omega
    have hJgt : e < J := by dsimp [J]; omega
    have hextraJ : landauTerm n (3 ^ J) = 1 := by
      simpa [J] using hextra
    rw [two_mul_add_one_valuation_indicator n 3 (by norm_num),
      valuation_gap_eq_sum n 3 (by norm_num)]
    have hpoint : ∀ j ∈ S,
        (if 3 ^ j ∣ 2 * n + 1 then (1 : ℤ) else 0) +
            (if j = J then (1 : ℤ) else 0) ≤
          (if j = 1 then (1 : ℤ) else 0) + landauTerm n (3 ^ j) := by
      intro j hj
      by_cases hjone : j = 1
      · subst j
        have hJne : 1 ≠ J := by omega
        have hdiv1 : 3 ^ 1 ∣ 2 * n + 1 :=
          (pow_dvd_pow 3 (by omega : 1 ≤ e)).trans hediv
        have hdiv3 : 3 ∣ 2 * n + 1 := by simpa using hdiv1
        have hnonneg := landauTerm_nonneg n 3
        simp [hJne, hdiv3]
        omega
      · by_cases hjJ : j = J
        · subst j
          have hnot : ¬3 ^ J ∣ 2 * n + 1 := by
            intro hd
            have hv : J ≤ padicValNat 3 (2 * n + 1) :=
              (padicValNat_dvd_iff_le (by omega : 2 * n + 1 ≠ 0)).mp hd
            dsimp [e] at hJgt
            omega
          simp [hjone, hnot, hextraJ]
        · by_cases hd : 3 ^ j ∣ 2 * n + 1
          · have hj2 : 2 ≤ j := by
              have := (Finset.mem_Ico.mp hj).1
              omega
            have hodd : Odd (3 ^ j) := (by norm_num : Odd 3).pow
            have hpow : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
            have hd9 : 9 ≤ 3 ^ j := by norm_num at hpow ⊢; exact hpow
            have heq := landauTerm_eq_one_of_dvd_two_mul_add_one
              n (3 ^ j) hodd hd9 hd
            simp [hjone, hjJ, hd, heq]
          · simpa [hjone, hjJ, hd] using landauTerm_nonneg n (3 ^ j)
    have hsum := Finset.sum_le_sum hpoint
    have hJsum : (∑ j ∈ S, if j = J then (1 : ℤ) else 0) = 1 := by
      classical
      simp [hJmem]
    have h1sum : (∑ j ∈ S, if j = 1 then (1 : ℤ) else 0) = 1 := by
      classical
      simp [h1mem]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    dsimp [S] at hsum ⊢
    dsimp [S] at hJsum h1sum
    omega

/-- All non-`3` prime cases for the first atomic target. -/
theorem primary_le_with_seven_of_ne_three
    (n p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (padicValNat p (2 * n + 1) : ℤ) ≤ (padicValNat p 7 : ℤ) +
      ((padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ))) := by
  by_cases hp2 : p = 2
  · subst p
    have hm : padicValNat 2 (2 * n + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega)
    have h7 : padicValNat 2 7 = 0 := by norm_num
    rw [hm, h7, Nat.cast_zero, zero_add]
    exact valuation_gap_nonneg n 2 (by norm_num)
  · by_cases hp5 : p = 5
    · subst p
      have h7 : padicValNat 5 7 = 0 := by norm_num
      rw [h7, Nat.cast_zero, zero_add]
      exact five_primary_le_valuation_gap n
    · by_cases hp7 : p = 7
      · subst p
        have h7 : padicValNat 7 7 = 1 := by norm_num
        rw [h7, Nat.cast_one]
        exact seven_primary_le_one_add_valuation_gap n
      · have hnot : ¬p ∣ 7 := by
          intro hd
          have : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
          exact hp7 this
        have h7 : padicValNat p 7 = 0 := padicValNat.eq_zero_of_not_dvd hnot
        rw [h7, Nat.cast_zero, zero_add]
        exact generic_primary_le_valuation_gap n p hp hp2 hp3 hp5 hp7

/-- The primewise estimate for every prime, including the exceptional `p = 3` case. -/
theorem primary_le_with_seven (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (2 * n + 1) : ℤ) ≤ (padicValNat p 7 : ℤ) +
      ((padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ))) := by
  by_cases hp3 : p = 3
  · subst p
    have h7 : padicValNat 3 7 = 0 := by norm_num
    rw [h7, Nat.cast_zero, zero_add]
    exact three_primary_le_valuation_gap n
  · exact primary_le_with_seven_of_ne_three n p hp hp3

/-- Numerator of the factorial ratio, named for the divisibility bridge. -/
def factorialNumerator (n : ℕ) : ℕ := (30 * n).factorial * n.factorial

/-- Denominator of the factorial ratio, named for the divisibility bridge. -/
def factorialDenominator (n : ℕ) : ℕ :=
  (15 * n).factorial * (10 * n).factorial * (6 * n).factorial

/-- Landau nonnegativity implies that the defining factorial ratio is integral. -/
theorem factorial_denominator_dvd_numerator (n : ℕ) :
    factorialDenominator n ∣ factorialNumerator n := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  have hN0 : factorialNumerator n ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hD0 : factorialDenominator n ≠ 0 := by
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)
  have hkD : k ≤ padicValNat p (factorialDenominator n) :=
    (padicValNat_dvd_iff_le hD0).mp hpk
  have hvN : padicValNat p (factorialNumerator n) =
      padicValNat p (30 * n).factorial + padicValNat p n.factorial := by
    rw [factorialNumerator,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hvD : padicValNat p (factorialDenominator n) =
      padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
        padicValNat p (6 * n).factorial := by
    rw [factorialDenominator,
      padicValNat.mul
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hgap := valuation_gap_nonneg n p hp
  have hkN : k ≤ padicValNat p (factorialNumerator n) := by
    rw [hvN]
    rw [hvD] at hkD
    have hkDz : (k : ℤ) ≤
        (padicValNat p (15 * n).factorial : ℤ) +
          padicValNat p (10 * n).factorial + padicValNat p (6 * n).factorial := by
      exact_mod_cast hkD
    have hkNz : (k : ℤ) ≤
        (padicValNat p (30 * n).factorial : ℤ) + padicValNat p n.factorial := by
      omega
    exact_mod_cast hkNz
  exact (padicValNat_dvd_iff_le hN0).mpr hkN

/-- Natural-number form of the first exact FC target. -/
theorem seven_mul_a_dvd_two_mul_add_one_nat (n : ℕ) :
    (2 * n + 1) ∣ 7 * OeisA211417.a n := by
  have hDN : factorialDenominator n ∣ factorialNumerator n :=
    factorial_denominator_dvd_numerator n
  have haeq : OeisA211417.a n = factorialNumerator n / factorialDenominator n := rfl
  have hN0 : factorialNumerator n ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hD0 : factorialDenominator n ≠ 0 := by
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)
  have ha0 : OeisA211417.a n ≠ 0 := by
    intro ha
    have hcancel := Nat.mul_div_cancel' hDN
    rw [← haeq, ha, mul_zero] at hcancel
    exact hN0 hcancel.symm
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  have hM0 : 2 * n + 1 ≠ 0 := by omega
  have hkM : k ≤ padicValNat p (2 * n + 1) :=
    (padicValNat_dvd_iff_le hM0).mp hpk
  have hvN : padicValNat p (factorialNumerator n) =
      padicValNat p (30 * n).factorial + padicValNat p n.factorial := by
    rw [factorialNumerator,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hvD : padicValNat p (factorialDenominator n) =
      padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
        padicValNat p (6 * n).factorial := by
    rw [factorialDenominator,
      padicValNat.mul
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hvA : padicValNat p (OeisA211417.a n) =
      padicValNat p (factorialNumerator n) - padicValNat p (factorialDenominator n) := by
    rw [haeq]
    exact padicValNat.div_of_dvd hDN
  have hv7A : padicValNat p (7 * OeisA211417.a n) =
      padicValNat p 7 + padicValNat p (OeisA211417.a n) :=
    padicValNat.mul (by norm_num) ha0
  have hprimary := primary_le_with_seven n p hp
  have hk : k ≤ padicValNat p (7 * OeisA211417.a n) := by
    rw [hv7A, hvA, hvN, hvD]
    have hvDN : padicValNat p (factorialDenominator n) ≤
        padicValNat p (factorialNumerator n) :=
      (padicValNat_dvd_iff_le hN0).mp
        ((pow_padicValNat_dvd (p := p) (n := factorialDenominator n)).trans hDN)
    rw [hvN, hvD] at hvDN
    have hkMz : (k : ℤ) ≤ (padicValNat p (2 * n + 1) : ℤ) := by
      exact_mod_cast hkM
    have hsubcast :
        (↑((padicValNat p (30 * n).factorial + padicValNat p n.factorial) -
          (padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
            padicValNat p (6 * n).factorial)) : ℤ) =
          (padicValNat p (30 * n).factorial : ℤ) + padicValNat p n.factorial -
            ((padicValNat p (15 * n).factorial : ℤ) +
              padicValNat p (10 * n).factorial + padicValNat p (6 * n).factorial) := by
      rw [Nat.cast_sub hvDN]
      push_cast
      rfl
    have hkz : (k : ℤ) ≤
        ((padicValNat p 7 +
          ((padicValNat p (30 * n).factorial + padicValNat p n.factorial) -
            (padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
              padicValNat p (6 * n).factorial)) : ℕ) : ℤ) := by
      calc
        (k : ℤ) ≤ (padicValNat p (2 * n + 1) : ℤ) := hkMz
        _ ≤ (padicValNat p 7 : ℤ) +
            ((padicValNat p (30 * n).factorial : ℤ) + padicValNat p n.factorial -
              ((padicValNat p (15 * n).factorial : ℤ) +
                padicValNat p (10 * n).factorial + padicValNat p (6 * n).factorial)) :=
          hprimary
        _ = _ := by rw [Nat.cast_add, hsubcast]
    exact_mod_cast hkz
  exact (padicValNat_dvd_iff_le (Nat.mul_ne_zero (by norm_num) ha0)).mpr hk

/-- Exact FC target: `(2n + 1) ∣ 7 a(n)`. -/
theorem seven_mul_a_dvd_two_mul_add_one_target (n : ℕ) :
    (2 * (n : ℤ) + 1) ∣ 7 * (OeisA211417.a n : ℤ) := by
  exact_mod_cast seven_mul_a_dvd_two_mul_add_one_nat n

lemma five_primary_three_dvd_choose (n : ℕ) :
    5 ^ padicValNat 5 (3 * n + 1) ∣ (5 * n).choose (2 * n) := by
  let q := 5 ^ padicValNat 5 (3 * n + 1)
  have hq : q ∣ 3 * n + 1 := pow_padicValNat_dvd
  have hmn : Nat.Coprime (3 * n + 1) n := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.coprime_add_mul_left_left 1 n 3).2 (Nat.coprime_one_left n)
  have hqn : Nat.Coprime q n := hmn.coprime_dvd_left hq
  have h52 : Nat.Coprime 5 2 := by norm_num
  have hq2 : Nat.Coprime q 2 := h52.pow_left _
  have hcop : Nat.Coprime q (2 * n) := hq2.mul_right hqn
  have hprod : q ∣ (5 * n).choose (3 * n) * (2 * n) := by
    rw [← show 5 * n - 3 * n = 2 * n by omega,
      ← Nat.choose_succ_right_eq (5 * n) (3 * n)]
    exact hq.mul_left ((5 * n).choose (3 * n + 1))
  rw [Nat.mul_comm] at hprod
  have hd : q ∣ (5 * n).choose (3 * n) := hcop.dvd_of_dvd_mul_left hprod
  rw [← Nat.choose_symm (show 2 * n ≤ 5 * n by omega)]
  simpa [show 5 * n - 2 * n = 3 * n by omega] using hd

lemma two_primary_three_dvd_choose (n : ℕ) :
    2 ^ padicValNat 2 (3 * n + 1) ∣ (8 * n).choose (3 * n) := by
  let q := 2 ^ padicValNat 2 (3 * n + 1)
  have hq : q ∣ 3 * n + 1 := pow_padicValNat_dvd
  have hmn : Nat.Coprime (3 * n + 1) n := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.coprime_add_mul_left_left 1 n 3).2 (Nat.coprime_one_left n)
  have hqn : Nat.Coprime q n := hmn.coprime_dvd_left hq
  have h25 : Nat.Coprime 2 5 := by norm_num
  have hq5 : Nat.Coprime q 5 := h25.pow_left _
  have hcop : Nat.Coprime q (5 * n) := hq5.mul_right hqn
  have hprod : q ∣ (8 * n).choose (3 * n) * (5 * n) := by
    rw [← show 8 * n - 3 * n = 5 * n by omega,
      ← Nat.choose_succ_right_eq (8 * n) (3 * n)]
    exact hq.mul_left ((8 * n).choose (3 * n + 1))
  rw [Nat.mul_comm] at hprod
  exact hcop.dvd_of_dvd_mul_left hprod

lemma two_valuation_gap_eq_choose (n : ℕ) :
    (padicValNat 2 (30 * n).factorial : ℤ) +
        (padicValNat 2 n.factorial : ℤ) -
      ((padicValNat 2 (15 * n).factorial : ℤ) +
        (padicValNat 2 (10 * n).factorial : ℤ) +
        (padicValNat 2 (6 * n).factorial : ℤ)) =
      (padicValNat 2 ((8 * n).choose (3 * n)) : ℤ) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h30 : padicValNat 2 (30 * n).factorial =
      padicValNat 2 (15 * n).factorial + 15 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 2) (15 * n))
  have h10 : padicValNat 2 (10 * n).factorial =
      padicValNat 2 (5 * n).factorial + 5 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 2) (5 * n))
  have h6 : padicValNat 2 (6 * n).factorial =
      padicValNat 2 (3 * n).factorial + 3 * n := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (padicValNat_factorial_mul (p := 2) (3 * n))
  have h2 : padicValNat 2 (2 * n).factorial =
      padicValNat 2 n.factorial + n := by
    simpa using padicValNat_factorial_mul (p := 2) n
  have h4 : padicValNat 2 (4 * n).factorial =
      padicValNat 2 (2 * n).factorial + 2 * n := by
    convert padicValNat_factorial_mul (p := 2) (2 * n) using 1 <;> ring
  have h8 : padicValNat 2 (8 * n).factorial =
      padicValNat 2 (4 * n).factorial + 4 * n := by
    convert padicValNat_factorial_mul (p := 2) (4 * n) using 1 <;> ring
  have hchoose_ne : (8 * n).choose (3 * n) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hfac : (8 * n).choose (3 * n) * (3 * n).factorial * (5 * n).factorial =
      (8 * n).factorial := by
    simpa [show 8 * n - 3 * n = 5 * n by omega] using
      (Nat.choose_mul_factorial_mul_factorial (show 3 * n ≤ 8 * n by omega))
  have hvleft := padicValNat.mul (p := 2) hchoose_ne (Nat.factorial_ne_zero (3 * n))
  have hvprod := padicValNat.mul (p := 2)
    (Nat.mul_ne_zero hchoose_ne (Nat.factorial_ne_zero (3 * n)))
    (Nat.factorial_ne_zero (5 * n))
  have hchoose : padicValNat 2 ((8 * n).choose (3 * n)) +
      padicValNat 2 (3 * n).factorial + padicValNat 2 (5 * n).factorial =
        padicValNat 2 (8 * n).factorial := by
    rw [hfac] at hvprod
    rw [hvleft] at hvprod
    omega
  have h30z : (padicValNat 2 (30 * n).factorial : ℤ) =
      (padicValNat 2 (15 * n).factorial : ℤ) + 15 * n := by exact_mod_cast h30
  have h10z : (padicValNat 2 (10 * n).factorial : ℤ) =
      (padicValNat 2 (5 * n).factorial : ℤ) + 5 * n := by exact_mod_cast h10
  have h6z : (padicValNat 2 (6 * n).factorial : ℤ) =
      (padicValNat 2 (3 * n).factorial : ℤ) + 3 * n := by exact_mod_cast h6
  have h2z : (padicValNat 2 (2 * n).factorial : ℤ) =
      (padicValNat 2 n.factorial : ℤ) + n := by exact_mod_cast h2
  have h4z : (padicValNat 2 (4 * n).factorial : ℤ) =
      (padicValNat 2 (2 * n).factorial : ℤ) + 2 * n := by exact_mod_cast h4
  have h8z : (padicValNat 2 (8 * n).factorial : ℤ) =
      (padicValNat 2 (4 * n).factorial : ℤ) + 4 * n := by exact_mod_cast h8
  have hchoosez : (padicValNat 2 ((8 * n).choose (3 * n)) : ℤ) +
      padicValNat 2 (3 * n).factorial + padicValNat 2 (5 * n).factorial =
        padicValNat 2 (8 * n).factorial := by exact_mod_cast hchoose
  omega

lemma two_primary_three_le_valuation_gap (n : ℕ) :
    (padicValNat 2 (3 * n + 1) : ℤ) ≤
      (padicValNat 2 (30 * n).factorial : ℤ) +
        (padicValNat 2 n.factorial : ℤ) -
        ((padicValNat 2 (15 * n).factorial : ℤ) +
          (padicValNat 2 (10 * n).factorial : ℤ) +
          (padicValNat 2 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hle : padicValNat 2 (3 * n + 1) ≤
      padicValNat 2 ((8 * n).choose (3 * n)) :=
    (padicValNat_dvd_iff_le (Nat.choose_ne_zero (by omega))).mp
      (two_primary_three_dvd_choose n)
  rw [two_valuation_gap_eq_choose]
  exact_mod_cast hle

lemma five_primary_three_le_valuation_gap (n : ℕ) :
    (padicValNat 5 (3 * n + 1) : ℤ) ≤
      (padicValNat 5 (30 * n).factorial : ℤ) +
        (padicValNat 5 n.factorial : ℤ) -
        ((padicValNat 5 (15 * n).factorial : ℤ) +
          (padicValNat 5 (10 * n).factorial : ℤ) +
          (padicValNat 5 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : padicValNat 5 (3 * n + 1) ≤
      padicValNat 5 ((5 * n).choose (2 * n)) :=
    (padicValNat_dvd_iff_le (Nat.choose_ne_zero (by omega))).mp
      (five_primary_three_dvd_choose n)
  rw [five_valuation_gap_eq_choose]
  exact_mod_cast hle

lemma landauTerm_eq_one_of_dvd_three_mul_add_one
    (n d : ℕ) (hdOdd : Odd d) (hd7 : 7 ≤ d) (hdiv : d ∣ 3 * n + 1) :
    landauTerm n d = 1 := by
  rw [landauTerm_eq_mod]
  let r := n % d
  change landauTerm r d = 1
  have hdpos : 0 < d := by omega
  have hr : r < d := Nat.mod_lt n hdpos
  have hmod0 : (3 * n + 1) % d = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hrmod : (3 * r + 1) % d = 0 := by
    dsimp [r]
    simpa [Nat.add_mod, Nat.mul_mod] using hmod0
  have hdr : d ∣ 3 * r + 1 := Nat.dvd_of_mod_eq_zero hrmod
  obtain ⟨c, hc⟩ := hdr
  have hcpos : 0 < c := by
    by_contra hz
    have : c = 0 := by omega
    subst c
    simp at hc
  have hclt : c < 3 := by
    nlinarith
  have hcases : c = 1 ∨ c = 2 := by omega
  rcases hcases with rfl | rfl
  · by_cases hd31 : 31 ≤ d
    · have h30 : 30 * r / d = 9 := (9).div_eq_of_lt_le (by omega) (by omega)
      have h15 : 15 * r / d = 4 := (4).div_eq_of_lt_le (by omega) (by omega)
      have h10 : 10 * r / d = 3 := (3).div_eq_of_lt_le (by omega) (by omega)
      have h6 : 6 * r / d = 1 := (1).div_eq_of_lt_le (by omega) (by omega)
      have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
      norm_num [landauTerm, h30, h15, h10, h6, hrdiv]
    · have hdlt : d < 31 := by omega
      interval_cases d <;> interval_cases r <;> norm_num [landauTerm] at *
  · obtain ⟨u, hu⟩ := odd_iff_exists_bit1.mp hdOdd
    have hd11 : 11 ≤ d := by omega
    have h30 : 30 * r / d = 19 := (19).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 9 := (9).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 6 := (6).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 3 := (3).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
    norm_num [landauTerm, h30, h15, h10, h6, hrdiv]

lemma three_mul_add_one_valuation_indicator (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (3 * n + 1) : ℤ) =
      ∑ j ∈ Finset.Ico 1 (30 * n + 1),
        if p ^ j ∣ 3 * n + 1 then (1 : ℤ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hval_lt : padicValNat p (3 * n + 1) < 3 * n + 1 := by
      rw [← Nat.factorization_def (3 * n + 1) hp]
      exact Nat.factorization_lt p (by omega)
    have hval_bound : padicValNat p (3 * n + 1) ≤ 30 * n :=
      hval_lt.le.trans (by omega)
    norm_num [padicValNat_dvd_iff_le (by omega : 3 * n + 1 ≠ 0), Fact.mk hp,
      ← Nat.factorization_def _, ← Finset.mem_Icc,
      hp.pow_dvd_iff_le_factorization (by omega : 3 * n + 1 ≠ 0), hnpos]
    exact (((congr_arg _) (Finset.ext (by
      simp_all [·.lt_succ] <;> omega))).trans
      ((1).card_Icc (padicValNat p (3 * n + 1)))).symm

lemma three_mul_add_one_primary_le_valuation_gap (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (3 * n + 1) : ℤ) ≤
      (padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ)) := by
  by_cases hp2 : p = 2
  · subst p
    exact two_primary_three_le_valuation_gap n
  · by_cases hp3 : p = 3
    · subst p
      have hm : padicValNat 3 (3 * n + 1) = 0 :=
        padicValNat.eq_zero_of_not_dvd (by omega)
      rw [hm, Nat.cast_zero]
      exact valuation_gap_nonneg n 3 (by norm_num)
    · by_cases hp5 : p = 5
      · subst p
        exact five_primary_three_le_valuation_gap n
      · rw [three_mul_add_one_valuation_indicator n p hp,
          valuation_gap_eq_sum n p hp]
        apply Finset.sum_le_sum
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
        by_cases hd : p ^ j ∣ 3 * n + 1
        · have hp7 : 7 ≤ p := by
            by_contra h
            have hple : p ≤ 6 := by omega
            interval_cases p <;> norm_num at hp
            all_goals omega
          have hodd : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
          have hpow : p ≤ p ^ j := by simpa using Nat.pow_le_pow_right hp.pos hj1
          have hd7 : 7 ≤ p ^ j := by omega
          have heq := landauTerm_eq_one_of_dvd_three_mul_add_one
            n (p ^ j) hodd hd7 hd
          simpa [hd, heq]
        · simpa [hd] using landauTerm_nonneg n (p ^ j)

lemma linear_dvd_a_of_primary
    (c n : ℕ)
    (hprimary : ∀ p : ℕ, p.Prime →
      (padicValNat p (c * n + 1) : ℤ) ≤
        (padicValNat p (30 * n).factorial : ℤ) +
          (padicValNat p n.factorial : ℤ) -
          ((padicValNat p (15 * n).factorial : ℤ) +
            (padicValNat p (10 * n).factorial : ℤ) +
            (padicValNat p (6 * n).factorial : ℤ))) :
    c * n + 1 ∣ OeisA211417.a n := by
  have hDN : factorialDenominator n ∣ factorialNumerator n :=
    factorial_denominator_dvd_numerator n
  have haeq : OeisA211417.a n = factorialNumerator n / factorialDenominator n := rfl
  have hN0 : factorialNumerator n ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have ha0 : OeisA211417.a n ≠ 0 := by
    intro ha
    have hcancel := Nat.mul_div_cancel' hDN
    rw [← haeq, ha, mul_zero] at hcancel
    exact hN0 hcancel.symm
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  letI : Fact p.Prime := ⟨hp⟩
  have hM0 : c * n + 1 ≠ 0 := by omega
  have hkM : k ≤ padicValNat p (c * n + 1) :=
    (padicValNat_dvd_iff_le hM0).mp hpk
  have hvN : padicValNat p (factorialNumerator n) =
      padicValNat p (30 * n).factorial + padicValNat p n.factorial := by
    rw [factorialNumerator,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hvD : padicValNat p (factorialDenominator n) =
      padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
        padicValNat p (6 * n).factorial := by
    rw [factorialDenominator,
      padicValNat.mul
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hvA : padicValNat p (OeisA211417.a n) =
      padicValNat p (factorialNumerator n) - padicValNat p (factorialDenominator n) := by
    rw [haeq]
    exact padicValNat.div_of_dvd hDN
  apply (padicValNat_dvd_iff_le ha0).mpr
  rw [hvA, hvN, hvD]
  have hvDN : padicValNat p (factorialDenominator n) ≤
      padicValNat p (factorialNumerator n) :=
    (padicValNat_dvd_iff_le hN0).mp
      ((pow_padicValNat_dvd (p := p) (n := factorialDenominator n)).trans hDN)
  rw [hvN, hvD] at hvDN
  have hkMz : (k : ℤ) ≤ (padicValNat p (c * n + 1) : ℤ) := by exact_mod_cast hkM
  have hsubcast :
      (↑((padicValNat p (30 * n).factorial + padicValNat p n.factorial) -
        (padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
          padicValNat p (6 * n).factorial)) : ℤ) =
        (padicValNat p (30 * n).factorial : ℤ) + padicValNat p n.factorial -
          ((padicValNat p (15 * n).factorial : ℤ) +
            padicValNat p (10 * n).factorial + padicValNat p (6 * n).factorial) := by
    rw [Nat.cast_sub hvDN]
    push_cast
    rfl
  have hkz : (k : ℤ) ≤
      (↑((padicValNat p (30 * n).factorial + padicValNat p n.factorial) -
        (padicValNat p (15 * n).factorial + padicValNat p (10 * n).factorial +
          padicValNat p (6 * n).factorial)) : ℤ) := by
    calc
      (k : ℤ) ≤ (padicValNat p (c * n + 1) : ℤ) := hkMz
      _ ≤ _ := hprimary p hp
      _ = _ := hsubcast.symm
  exact_mod_cast hkz

lemma a_dvd_three_mul_add_one_nat (n : ℕ) :
    3 * n + 1 ∣ OeisA211417.a n :=
  linear_dvd_a_of_primary 3 n (three_mul_add_one_primary_le_valuation_gap n)

/-- Exact FC target: `(3n + 1) ∣ a(n)`. -/
theorem a_dvd_three_mul_add_one_target (n : ℕ) :
    (3 * (n : ℤ) + 1) ∣ (OeisA211417.a n : ℤ) := by
  exact_mod_cast a_dvd_three_mul_add_one_nat n

lemma landauTerm_eq_one_of_scale_window
    (n d : ℕ) (hn : 0 < n) (hlo : 9 * n < d) (hhi : d ≤ 27 * n) :
    landauTerm n d = 1 := by
  have hd : 0 < d := by omega
  have hndiv : n / d = 0 := Nat.div_eq_of_lt (by omega)
  let A := 15 * n / d
  let B := 10 * n / d
  let C := 6 * n / d
  let G := 30 * n / d
  have hAlo : A * d ≤ 15 * n := Nat.div_mul_le_self _ _
  have hAhi : 15 * n < A * d + d := Nat.lt_div_mul_add hd
  have hBlo : B * d ≤ 10 * n := Nat.div_mul_le_self _ _
  have hBhi : 10 * n < B * d + d := Nat.lt_div_mul_add hd
  have hClo : C * d ≤ 6 * n := Nat.div_mul_le_self _ _
  have hChi : 6 * n < C * d + d := Nat.lt_div_mul_add hd
  have hGlo : G * d ≤ 30 * n := Nat.div_mul_le_self _ _
  have hGhi : 30 * n < G * d + d := Nat.lt_div_mul_add hd
  have hA : A ≤ 1 := by
    have : 15 * n < 2 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hB : B ≤ 1 := by
    have : 10 * n < 2 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  have hC : C = 0 := Nat.div_eq_of_lt (by omega)
  have hGlo1 : 1 ≤ G := (Nat.le_div_iff_mul_le hd).2 (by omega)
  have hG : G ≤ 3 := by
    have : 30 * n < 4 * d := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 this)
  change (G : ℤ) + (↑(n / d) : ℤ) - A - B - C = 1
  rw [hndiv, hC]
  interval_cases A <;> interval_cases B <;> interval_cases G <;> omega

lemma landauTerm_eq_one_of_dvd_five_mul_add_one
    (n d : ℕ) (hd7 : 7 ≤ d) (hdiv : d ∣ 5 * n + 1) :
    landauTerm n d = 1 := by
  rw [landauTerm_eq_mod]
  let r := n % d
  change landauTerm r d = 1
  have hdpos : 0 < d := by omega
  have hr : r < d := Nat.mod_lt n hdpos
  have hmod0 : (5 * n + 1) % d = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hrmod : (5 * r + 1) % d = 0 := by
    dsimp [r]
    simpa [Nat.add_mod, Nat.mul_mod] using hmod0
  have hdr : d ∣ 5 * r + 1 := Nat.dvd_of_mod_eq_zero hrmod
  obtain ⟨c, hc⟩ := hdr
  have hcpos : 0 < c := by
    by_contra hz
    have : c = 0 := by omega
    subst c
    simp at hc
  have hclt : c < 5 := by nlinarith
  have hcases : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have h30 : 30 * r / d = 5 := (5).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 2 := (2).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 1 := (1).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 1 := (1).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
    norm_num [landauTerm, h30, h15, h10, h6, hrdiv]
  · have h30 : 30 * r / d = 11 := (11).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 5 := (5).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 3 := (3).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 2 := (2).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
    norm_num [landauTerm, h30, h15, h10, h6, hrdiv]
  · have h30 : 30 * r / d = 17 := (17).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 8 := (8).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 5 := (5).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 3 := (3).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
    norm_num [landauTerm, h30, h15, h10, h6, hrdiv]
  · have h30 : 30 * r / d = 23 := (23).div_eq_of_lt_le (by omega) (by omega)
    have h15 : 15 * r / d = 11 := (11).div_eq_of_lt_le (by omega) (by omega)
    have h10 : 10 * r / d = 7 := (7).div_eq_of_lt_le (by omega) (by omega)
    have h6 : 6 * r / d = 4 := (4).div_eq_of_lt_le (by omega) (by omega)
    have hrdiv : r / d = 0 := Nat.div_eq_of_lt hr
    norm_num [landauTerm, h30, h15, h10, h6, hrdiv]

lemma five_mul_add_one_valuation_indicator (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (5 * n + 1) : ℤ) =
      ∑ j ∈ Finset.Ico 1 (30 * n + 1),
        if p ^ j ∣ 5 * n + 1 then (1 : ℤ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hval_lt : padicValNat p (5 * n + 1) < 5 * n + 1 := by
      rw [← Nat.factorization_def (5 * n + 1) hp]
      exact Nat.factorization_lt p (by omega)
    have hval_bound : padicValNat p (5 * n + 1) ≤ 30 * n :=
      hval_lt.le.trans (by omega)
    norm_num [padicValNat_dvd_iff_le (by omega : 5 * n + 1 ≠ 0), Fact.mk hp,
      ← Nat.factorization_def _, ← Finset.mem_Icc,
      hp.pow_dvd_iff_le_factorization (by omega : 5 * n + 1 ≠ 0), hnpos]
    exact (((congr_arg _) (Finset.ext (by
      simp_all [·.lt_succ] <;> omega))).trans
      ((1).card_Icc (padicValNat p (5 * n + 1)))).symm

lemma two_primary_five_dvd_choose (n : ℕ) :
    2 ^ padicValNat 2 (5 * n + 1) ∣ (8 * n).choose (3 * n) := by
  let q := 2 ^ padicValNat 2 (5 * n + 1)
  have hq : q ∣ 5 * n + 1 := pow_padicValNat_dvd
  have hmn : Nat.Coprime (5 * n + 1) n := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.coprime_add_mul_left_left 1 n 5).2 (Nat.coprime_one_left n)
  have hqn : Nat.Coprime q n := hmn.coprime_dvd_left hq
  have h23 : Nat.Coprime 2 3 := by norm_num
  have hq3 : Nat.Coprime q 3 := h23.pow_left _
  have hcop : Nat.Coprime q (3 * n) := hq3.mul_right hqn
  have hprod : q ∣ (8 * n).choose (5 * n) * (3 * n) := by
    rw [← show 8 * n - 5 * n = 3 * n by omega,
      ← Nat.choose_succ_right_eq (8 * n) (5 * n)]
    exact hq.mul_left ((8 * n).choose (5 * n + 1))
  rw [Nat.mul_comm] at hprod
  have hd : q ∣ (8 * n).choose (5 * n) := hcop.dvd_of_dvd_mul_left hprod
  rw [← Nat.choose_symm (show 3 * n ≤ 8 * n by omega)]
  simpa [show 8 * n - 3 * n = 5 * n by omega] using hd

lemma two_primary_five_le_valuation_gap (n : ℕ) :
    (padicValNat 2 (5 * n + 1) : ℤ) ≤
      (padicValNat 2 (30 * n).factorial : ℤ) +
        (padicValNat 2 n.factorial : ℤ) -
        ((padicValNat 2 (15 * n).factorial : ℤ) +
          (padicValNat 2 (10 * n).factorial : ℤ) +
          (padicValNat 2 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hle : padicValNat 2 (5 * n + 1) ≤
      padicValNat 2 ((8 * n).choose (3 * n)) :=
    (padicValNat_dvd_iff_le (Nat.choose_ne_zero (by omega))).mp
      (two_primary_five_dvd_choose n)
  rw [two_valuation_gap_eq_choose]
  exact_mod_cast hle

lemma three_primary_five_le_valuation_gap (n : ℕ) :
    (padicValNat 3 (5 * n + 1) : ℤ) ≤
      (padicValNat 3 (30 * n).factorial : ℤ) +
        (padicValNat 3 n.factorial : ℤ) -
        ((padicValNat 3 (15 * n).factorial : ℤ) +
          (padicValNat 3 (10 * n).factorial : ℤ) +
          (padicValNat 3 (6 * n).factorial : ℤ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e := padicValNat 3 (5 * n + 1)
  by_cases he0 : e = 0
  · rw [show padicValNat 3 (5 * n + 1) = 0 by exact he0, Nat.cast_zero]
    exact valuation_gap_nonneg n 3 (by norm_num)
  · have he : 0 < e := Nat.pos_of_ne_zero he0
    have hediv : 3 ^ e ∣ 5 * n + 1 := by
      dsimp [e]
      exact pow_padicValNat_dvd
    have hnpos : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      norm_num at hediv
      omega
    let J := Nat.log 3 n + 3
    have hpow_le : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by omega)
    have hlo : 9 * n < 3 ^ J := by
      have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) n
      calc
        9 * n < 9 * 3 ^ (Nat.log 3 n + 1) := by omega
        _ = 3 ^ J := by simp [J, pow_add]; ring
    have hhi : 3 ^ J ≤ 27 * n := by
      simpa [J, pow_add, mul_comm, mul_left_comm, mul_assoc] using
        Nat.mul_le_mul_left 27 hpow_le
    have hJbound : J ≤ 30 * n := by
      have := Nat.log_le_self 3 n
      dsimp [J]
      omega
    have hMlt : 5 * n + 1 < 3 ^ J := by omega
    have hJgt : e < J := by
      by_contra h
      have hJe : J ≤ e := by omega
      have hpowmono : 3 ^ J ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hJe
      have hepow : 3 ^ e ≤ 5 * n + 1 := Nat.le_of_dvd (by omega) hediv
      omega
    have hextra : landauTerm n (3 ^ J) = 1 :=
      landauTerm_eq_one_of_scale_window n (3 ^ J) hnpos hlo hhi
    let S := Finset.Ico 1 (30 * n + 1)
    have hJmem : J ∈ S := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have h1mem : 1 ∈ S := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    rw [five_mul_add_one_valuation_indicator n 3 (by norm_num),
      valuation_gap_eq_sum n 3 (by norm_num)]
    have hpoint : ∀ j ∈ S,
        (if 3 ^ j ∣ 5 * n + 1 then (1 : ℤ) else 0) +
            (if j = J then (1 : ℤ) else 0) ≤
          (if j = 1 then (1 : ℤ) else 0) + landauTerm n (3 ^ j) := by
      intro j hj
      by_cases hjone : j = 1
      · subst j
        have hJne : 1 ≠ J := by omega
        have hdiv1 : 3 ^ 1 ∣ 5 * n + 1 :=
          (pow_dvd_pow 3 (by omega : 1 ≤ e)).trans hediv
        have hdiv3 : 3 ∣ 5 * n + 1 := by simpa using hdiv1
        have hnonneg := landauTerm_nonneg n 3
        simp [hJne, hdiv3]
        omega
      · by_cases hjJ : j = J
        · subst j
          have hnot : ¬3 ^ J ∣ 5 * n + 1 := by
            intro hd
            have hle := Nat.le_of_dvd (by omega : 0 < 5 * n + 1) hd
            omega
          simp [hjone, hnot, hextra]
        · by_cases hd : 3 ^ j ∣ 5 * n + 1
          · have hj2 : 2 ≤ j := by
              have := (Finset.mem_Ico.mp hj).1
              omega
            have hpow : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
            have hd7 : 7 ≤ 3 ^ j := by norm_num at hpow ⊢; omega
            have heq := landauTerm_eq_one_of_dvd_five_mul_add_one
              n (3 ^ j) hd7 hd
            simp [hjone, hjJ, hd, heq]
          · simpa [hjone, hjJ, hd] using landauTerm_nonneg n (3 ^ j)
    have hsum := Finset.sum_le_sum hpoint
    have hJsum : (∑ j ∈ S, if j = J then (1 : ℤ) else 0) = 1 := by
      classical
      simp [hJmem]
    have h1sum : (∑ j ∈ S, if j = 1 then (1 : ℤ) else 0) = 1 := by
      classical
      simp [h1mem]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    dsimp [S] at hsum ⊢
    dsimp [S] at hJsum h1sum
    omega

lemma five_mul_add_one_primary_le_valuation_gap (n p : ℕ) (hp : p.Prime) :
    (padicValNat p (5 * n + 1) : ℤ) ≤
      (padicValNat p (30 * n).factorial : ℤ) +
        (padicValNat p n.factorial : ℤ) -
        ((padicValNat p (15 * n).factorial : ℤ) +
          (padicValNat p (10 * n).factorial : ℤ) +
          (padicValNat p (6 * n).factorial : ℤ)) := by
  by_cases hp2 : p = 2
  · subst p
    exact two_primary_five_le_valuation_gap n
  · by_cases hp3 : p = 3
    · subst p
      exact three_primary_five_le_valuation_gap n
    · by_cases hp5 : p = 5
      · subst p
        have hm : padicValNat 5 (5 * n + 1) = 0 :=
          padicValNat.eq_zero_of_not_dvd (by omega)
        rw [hm, Nat.cast_zero]
        exact valuation_gap_nonneg n 5 (by norm_num)
      · rw [five_mul_add_one_valuation_indicator n p hp,
          valuation_gap_eq_sum n p hp]
        apply Finset.sum_le_sum
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
        by_cases hd : p ^ j ∣ 5 * n + 1
        · have hp7 : 7 ≤ p := by
            by_contra h
            have hple : p ≤ 6 := by omega
            interval_cases p <;> norm_num at hp
            all_goals omega
          have hpow : p ≤ p ^ j := by simpa using Nat.pow_le_pow_right hp.pos hj1
          have hd7 : 7 ≤ p ^ j := by omega
          have heq := landauTerm_eq_one_of_dvd_five_mul_add_one
            n (p ^ j) hd7 hd
          simpa [hd, heq]
        · simpa [hd] using landauTerm_nonneg n (p ^ j)

lemma a_dvd_five_mul_add_one_nat (n : ℕ) :
    5 * n + 1 ∣ OeisA211417.a n :=
  linear_dvd_a_of_primary 5 n (five_mul_add_one_primary_le_valuation_gap n)

/-- Exact FC target: `(5n + 1) ∣ a(n)`. -/
theorem a_dvd_five_mul_add_one_target (n : ℕ) :
    (5 * (n : ℤ) + 1) ∣ (OeisA211417.a n : ℤ) := by
  exact_mod_cast a_dvd_five_mul_add_one_nat n

private lemma mul_dvd_gcd_mul_of_dvd_of_dvd
    (a b u : ℕ) (ha : a ∣ u) (hb : b ∣ u) :
    a * b ∣ Nat.gcd a b * u := by
  obtain ⟨t, rfl⟩ := Nat.lcm_dvd ha hb
  refine ⟨t, ?_⟩
  rw [← Nat.mul_assoc, Nat.gcd_mul_lcm]

/--
The FC product target follows formally from the three atomic divisibility targets.

The constant `42 = 7 * 6` is sufficient because
`gcd(2n+1, 3n+1) = 1`, `gcd(2n+1, 5n+1) ∣ 3`, and
`gcd(3n+1, 5n+1) ∣ 2`.
-/
theorem forty_two_mul_a_dvd_product_from_atomic
    (n A : ℕ)
    (h2 : 2 * n + 1 ∣ 7 * A)
    (h3 : 3 * n + 1 ∣ A)
    (h5 : 5 * n + 1 ∣ A) :
    (2 * n + 1) * (3 * n + 1) * (5 * n + 1) ∣ 42 * A := by
  let x := 2 * n + 1
  let y := 3 * n + 1
  let z := 5 * n + 1
  have hxy_coprime : Nat.Coprime x y := by
    dsimp [x, y]
    have hxn : Nat.Coprime (2 * n + 1) n := by
      simpa [Nat.add_comm, Nat.mul_comm] using
        (Nat.coprime_add_mul_left_left 1 n 2).2 (Nat.coprime_one_left n)
    simpa [show 3 * n + 1 = n + (2 * n + 1) by omega] using
      (Nat.coprime_add_self_right (m := 2 * n + 1) (n := n)).2 hxn
  have hxz : Nat.gcd x z ∣ 3 := by
    dsimp [x, z]
    let d := Nat.gcd (2 * n + 1) (5 * n + 1)
    have hx : d ∣ 5 * (2 * n + 1) := (Nat.gcd_dvd_left _ _).mul_left 5
    have hz : d ∣ 2 * (5 * n + 1) := (Nat.gcd_dvd_right _ _).mul_left 2
    have heq : 3 + 2 * (5 * n + 1) = 5 * (2 * n + 1) := by omega
    change d ∣ 3
    apply (Nat.dvd_add_iff_left hz).mpr
    rwa [heq]
  have hyz : Nat.gcd y z ∣ 2 := by
    dsimp [y, z]
    let d := Nat.gcd (3 * n + 1) (5 * n + 1)
    have hy : d ∣ 5 * (3 * n + 1) := (Nat.gcd_dvd_left _ _).mul_left 5
    have hz : d ∣ 3 * (5 * n + 1) := (Nat.gcd_dvd_right _ _).mul_left 3
    have heq : 2 + 3 * (5 * n + 1) = 5 * (3 * n + 1) := by omega
    change d ∣ 2
    apply (Nat.dvd_add_iff_left hz).mpr
    rwa [heq]
  have hxy : x * y ∣ 7 * A :=
    hxy_coprime.mul_dvd_of_dvd_of_dvd (by simpa [x] using h2)
      (by simpa [y] using h3.mul_left 7)
  have hg : Nat.gcd (x * y) z ∣ 6 := by
    have hsplit : Nat.gcd (x * y) z ∣ Nat.gcd x z * Nat.gcd y z := by
      rw [Nat.gcd_comm (x * y) z, Nat.gcd_comm x z, Nat.gcd_comm y z]
      exact gcd_mul_dvd_mul_gcd z x y
    exact hsplit.trans (by simpa using Nat.mul_dvd_mul hxz hyz)
  have hxyz : (x * y) * z ∣ Nat.gcd (x * y) z * (7 * A) :=
    mul_dvd_gcd_mul_of_dvd_of_dvd (x * y) z (7 * A) hxy
      (by simpa [z] using h5.mul_left 7)
  have hscale : Nat.gcd (x * y) z * (7 * A) ∣ 42 * A := by
    convert Nat.mul_dvd_mul hg (dvd_refl (7 * A)) using 1 <;> ring
  simpa [x, y, z] using hxyz.trans hscale

/-- Exact FC product target, derived from the three atomic targets above. -/
theorem forty_two_mul_a_dvd_product_target (n : ℕ) :
    ((2 * (n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (5 * (n : ℤ) + 1)) ∣
      42 * (OeisA211417.a n : ℤ) := by
  have h2 : 2 * n + 1 ∣ 7 * OeisA211417.a n := by
    exact_mod_cast seven_mul_a_dvd_two_mul_add_one_target n
  have h3 : 3 * n + 1 ∣ OeisA211417.a n := by
    exact_mod_cast a_dvd_three_mul_add_one_target n
  have h5 : 5 * n + 1 ∣ OeisA211417.a n := by
    exact_mod_cast a_dvd_five_mul_add_one_target n
  exact_mod_cast
    forty_two_mul_a_dvd_product_from_atomic n (OeisA211417.a n) h2 h3 h5

/-- Exact FC supercongruence target. -/
theorem supercongruence_target
    (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣
      ((OeisA211417.a (p ^ k) : ℤ) -
        (OeisA211417.a (p ^ (k - 1)) : ℤ)) := by
  -- Planned route: Jacobsthal--Kazandzidis for three binomial coefficients, then cancellation.
  sorry

#check OeisA211417.seven_mul_a_dvd_two_mul_add_one
#check OeisA211417.a_dvd_three_mul_add_one
#check OeisA211417.a_dvd_five_mul_add_one
#check OeisA211417.forty_two_mul_a_dvd_product
#check OeisA211417.supercongruence

#print axioms landauTerm_nonneg
#print axioms valuation_gap_eq_sum
#print axioms landauTerm_eq_one_of_dvd_two_mul_add_one
#print axioms three_extra_landau_term
#print axioms three_primary_le_valuation_gap
#print axioms forty_two_mul_a_dvd_product_from_atomic
#print axioms supercongruence_target

/-
## SOLVED TARGET AUDIT

These deliberately thin aliases collect the four completed exact Formal Conjectures targets in
one place.  Their statements can be compared directly with the imported FC declarations above.
The `#print axioms` commands immediately following them must not report `sorryAx`.
-/

theorem target_seven_mul_a_dvd_two_mul_add_one_target (n : ℕ) :
    (2 * (n : ℤ) + 1) ∣ 7 * (OeisA211417.a n : ℤ) :=
  seven_mul_a_dvd_two_mul_add_one_target n

theorem target_a_dvd_three_mul_add_one_target (n : ℕ) :
    (3 * (n : ℤ) + 1) ∣ (OeisA211417.a n : ℤ) :=
  a_dvd_three_mul_add_one_target n

theorem target_a_dvd_five_mul_add_one_target (n : ℕ) :
    (5 * (n : ℤ) + 1) ∣ (OeisA211417.a n : ℤ) :=
  a_dvd_five_mul_add_one_target n

theorem target_forty_two_mul_a_dvd_product_target (n : ℕ) :
    ((2 * (n : ℤ) + 1) * (3 * (n : ℤ) + 1) * (5 * (n : ℤ) + 1)) ∣
      42 * (OeisA211417.a n : ℤ) :=
  forty_two_mul_a_dvd_product_target n

#check target_seven_mul_a_dvd_two_mul_add_one_target
#check target_a_dvd_three_mul_add_one_target
#check target_a_dvd_five_mul_add_one_target
#check target_forty_two_mul_a_dvd_product_target

#print axioms target_seven_mul_a_dvd_two_mul_add_one_target
#print axioms target_a_dvd_three_mul_add_one_target
#print axioms target_a_dvd_five_mul_add_one_target
#print axioms target_forty_two_mul_a_dvd_product_target

end OeisA211417Proof
