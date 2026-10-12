import Mathlib

/-!
# JSP-000301 — Golomb's counterexample (Erdős Problem 365, first yes/no subquestion)

Problem (as scoped by the official JSP-000301 record, review note of
2026-09-13): If two consecutive positive integers are powerful, must at
least one be a perfect square?

Answer: No. Golomb (1970): 12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2 are
consecutive powerful numbers, and neither is a perfect square.

Mathematical source: S. W. Golomb, "Powerful numbers",
Amer. Math. Monthly 77(8) (1970), 848-852. DOI: 10.2307/2317020.
This file formalizes only that scoped yes/no question, not the separate
counting question in the full Erdős Problem 365.
-/

/-- A positive integer `n` is *powerful* if every prime divisor of `n`
satisfies `p ^ 2 ∣ n` (equivalently, every prime exponent in `n` is at
least two; see `powerful_iff_factorization`). -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- The divisibility definition of `Powerful` agrees with the
factorization definition: every prime occurs with exponent at least 2. -/
theorem powerful_iff_factorization {n : ℕ} (hn : n ≠ 0) :
    Powerful n ↔ ∀ p : ℕ, Nat.Prime p → p ∣ n → 2 ≤ n.factorization p := by
  constructor
  · intro h p hp hdvd
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hn]
    exact h p hp hdvd
  · intro h p hp hdvd
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn]
    exact h p hp hdvd

/-- Any prime divisor of `12167 = 23 ^ 3` equals `23`. -/
private lemma prime_dvd_12167 {p : ℕ} (hp : Nat.Prime p) (h : p ∣ 12167) : p = 23 := by
  have hfac : (12167 : ℕ) = 23 ^ 3 := by norm_num
  rw [hfac] at h
  have h1 : p ∣ 23 := hp.dvd_of_dvd_pow h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 23)).mp h1 with h2 | h2
  · exact absurd h2 hp.ne_one
  · exact h2

/-- Any prime divisor of `12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2` is `2`, `3` or `13`. -/
private lemma prime_dvd_12168 {p : ℕ} (hp : Nat.Prime p) (h : p ∣ 12168) :
    p = 2 ∨ p = 3 ∨ p = 13 := by
  have hfac : (12168 : ℕ) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  rw [hfac] at h
  rcases (hp.dvd_mul).mp h with h | h
  · rcases (hp.dvd_mul).mp h with h | h
    · left
      have h1 : p ∣ 2 := hp.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h1 with h2 | h2
      · exact absurd h2 hp.ne_one
      · exact h2
    · right; left
      have h1 : p ∣ 3 := hp.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h1 with h2 | h2
      · exact absurd h2 hp.ne_one
      · exact h2
  · right; right
    have h1 : p ∣ 13 := hp.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp h1 with h2 | h2
    · exact absurd h2 hp.ne_one
    · exact h2

theorem powerful_12167 : Powerful 12167 := by
  intro p hp h
  rw [prime_dvd_12167 hp h]
  exact ⟨23, by norm_num⟩

theorem powerful_12168 : Powerful 12168 := by
  intro p hp h
  rcases prime_dvd_12168 hp h with rfl | rfl | rfl
  · exact ⟨3042, by norm_num⟩
  · exact ⟨1352, by norm_num⟩
  · exact ⟨72, by norm_num⟩

/-- A natural number strictly between the consecutive squares `110 ^ 2`
and `111 ^ 2` is not a square. -/
private lemma not_square_of_between {n : ℕ} (h1 : 110 ^ 2 < n) (h2 : n < 111 ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hk2 : k * k = n := hk.symm
  have hkb : k ≤ 110 ∨ 111 ≤ k := by omega
  rcases hkb with hb | hb
  · have hle : k * k ≤ 110 * 110 := Nat.mul_le_mul hb hb
    omega
  · have hle : 111 * 111 ≤ k * k := Nat.mul_le_mul hb hb
    omega

theorem not_square_12167 : ¬ IsSquare 12167 :=
  not_square_of_between (by norm_num) (by norm_num)

theorem not_square_12168 : ¬ IsSquare 12168 :=
  not_square_of_between (by norm_num) (by norm_num)

/-- Golomb's counterexample, in existential form: there is a positive
integer `n` such that `n` and `n + 1` are both powerful and neither is
a perfect square. -/
theorem golomb_counterexample :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, by norm_num, powerful_12167, powerful_12168,
   not_square_12167, not_square_12168⟩

/-- The direct negation of the problem's universal assertion: it is not
the case that for every pair of consecutive positive powerful integers,
at least one of them is a perfect square. -/
theorem answer_no :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  have hcon := h 12167 (by norm_num) powerful_12167 powerful_12168
  rcases hcon with hs | hs
  · exact not_square_12167 hs
  · exact not_square_12168 hs
