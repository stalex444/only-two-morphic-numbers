/-
PdtMorphic — the Aarts–Fokkink–Kruijtzer classification of morphic numbers.

Aarts, Fokkink, Kruijtzer, "Morphic numbers", Nieuw Arch. Wisk. (5) 2
(2001) 56–58: a real number p > 1 is MORPHIC if there are natural numbers
k, l ≥ 1 with p + 1 = p ^ k and p - 1 = p ^ (-l) — the golden ratio's two
scale properties, abstracted.  THE THEOREM (p. 58): there exist only two
morphic numbers, the divine proportion φ (k, l = 2, 1) and the plastic
number ρ of Dom Hans van der Laan, the real root of x³ = x + 1
(k, l = 3, 4, via x⁵ - x⁴ - 1 = (x³ - x - 1)(x² - x + 1)).

Proof route (AFK's, with one substitution): a morphic number is a common
root of X^k - X - 1 and X^(l+1) - X^l - 1.  Selmer (Math. Scand. 4 (1956)
287–302; in Mathlib as `Polynomial.X_pow_sub_X_sub_one_irreducible`)
makes the first trinomial the minimal polynomial of p over ℤ, hence a
divisor of the second.  Where AFK cite Tverberg (Math. Scand. 8 (1960)
121–126), this file derives the needed instance from Mathlib's Ljunggren
unit-trinomial machinery (Ljunggren, Math. Scand. 8 (1960) 65–70,
formalized by T. Browning): the mirror dichotomy extracted from
`IsUnitTrinomial.irreducible_of_coprime` forces the cofactor q to be
mirror-fixed, whence q ∣ X² - X + 1, and the forced factorization
(X^k - X - 1)(X² - X + 1) = X^(k+2) - X^(k+1) - 1 pins k = 3, p = ρ;
the cofactor q = 1 gives k = 2, p = φ.
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.Algebra.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Order.IntermediateValue

namespace PDT
namespace Morphic

open Polynomial

/-- AFK 2001, p. 57: a real number `p > 1` is *morphic* if there are natural
numbers `k, l ≥ 1` with `p + 1 = p ^ k` and `p - 1 = p ^ (-l)`.  The second
equation is rendered zpow-free as `p ^ l * (p - 1) = 1`; the positivity
conjuncts transcribe the paper's "natural numbers" (they are in fact
removable: `l = 0` would force `p = 2`, killed by `2 ^ k = 3`). -/
def IsMorphic (p : ℝ) : Prop :=
  1 < p ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = p + 1 ∧ p ^ l * (p - 1) = 1

/-! ### The plastic number -/

/-- The cubic `x³ = x + 1` has a real root above `1` (IVT on `[1, 2]`). -/
theorem exists_plastic : ∃ x : ℝ, 1 < x ∧ x ^ 3 = x + 1 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨x, hmem, hx⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hc
    (show (0:ℝ) ∈ Set.Icc ((1:ℝ) ^ 3 - 1 - 1) ((2:ℝ) ^ 3 - 2 - 1) by norm_num)
  simp only at hx
  refine ⟨x, ?_, by linarith⟩
  rcases lt_or_eq_of_le hmem.1 with h | h
  · exact h
  · rw [← h] at hx; norm_num at hx

/-- The plastic number ρ: the real root of `x³ = x + 1` in `(1, ∞)`
(unique there, by `eq_plasticNumber_of_cubic`). -/
noncomputable def plasticNumber : ℝ := Classical.choose exists_plastic

theorem one_lt_plasticNumber : 1 < plasticNumber :=
  (Classical.choose_spec exists_plastic).1

theorem plasticNumber_cubic : plasticNumber ^ 3 = plasticNumber + 1 :=
  (Classical.choose_spec exists_plastic).2

/-- Uniqueness of the plastic number on `(1, ∞)`. -/
theorem eq_plasticNumber_of_cubic {x : ℝ} (h1 : 1 < x) (h3 : x ^ 3 = x + 1) :
    x = plasticNumber := by
  have hr1 := one_lt_plasticNumber
  have hr3 := plasticNumber_cubic
  have key : (x - plasticNumber) *
      (x ^ 2 + x * plasticNumber + plasticNumber ^ 2 - 1) = 0 := by
    linear_combination h3 - hr3
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · nlinarith

/-- Uniqueness of the golden ratio on `(1, ∞)`. -/
theorem eq_goldenRatio_of_sq {x : ℝ} (h1 : 1 < x) (h2 : x ^ 2 = x + 1) :
    x = Real.goldenRatio := by
  have h5 : ((2 * x - 1) ^ 2 : ℝ) = 5 := by linear_combination 4 * h2
  have hpos : (0:ℝ) ≤ 2 * x - 1 := by linarith
  have hsqrt : Real.sqrt 5 = 2 * x - 1 := by
    rw [show (5:ℝ) = (2 * x - 1) ^ 2 from h5.symm, Real.sqrt_sq hpos]
  show x = (1 + Real.sqrt 5) / 2
  rw [hsqrt]; ring

/-! ### The two witnesses -/

/-- The golden ratio is morphic, with `(k, l) = (2, 1)`. -/
theorem goldenRatio_morphic : IsMorphic Real.goldenRatio := by
  refine ⟨Real.one_lt_goldenRatio, 2, 1, by norm_num, by norm_num,
    Real.goldenRatio_sq, ?_⟩
  linear_combination Real.goldenRatio_sq

/-- The plastic number is morphic, with `(k, l) = (3, 4)`: the second
witness `ρ⁴(ρ - 1) = 1` is AFK's identity
`x⁵ - x⁴ - 1 = (x³ - x - 1)(x² - x + 1)` applied at ρ. -/
theorem plasticNumber_morphic : IsMorphic plasticNumber := by
  refine ⟨one_lt_plasticNumber, 3, 4, by norm_num, by norm_num,
    plasticNumber_cubic, ?_⟩
  linear_combination (plasticNumber ^ 2 - plasticNumber + 1) * plasticNumber_cubic

/-! ### The Ljunggren mirror dichotomy

Extracted from the proof of
`Polynomial.IsUnitTrinomial.irreducible_of_coprime` (T. Browning's
formalization of Ljunggren's method, Math. Scand. 8 (1960) 65–70): if a
unit trinomial `p` and any `q` satisfy `p * p.mirror = q * q.mirror`,
then `q` is `±p` or `±p.mirror`.  The aux-named public lemma
`IsUnitTrinomial.irreducible_aux3` used below is Mathlib's own. -/

theorem mirror_dichotomy {p q : ℤ[X]} (hp : p.IsUnitTrinomial)
    (hpq : p * p.mirror = q * q.mirror) :
    q = p ∨ q = -p ∨ q = p.mirror ∨ q = -p.mirror := by
  have hq : IsUnitTrinomial q := (isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ←
      trinomial_natTrailingDegree hkm hmn u.ne_zero, ← hp, ← natTrailingDegree_mul_mirror, hpq,
      natTrailingDegree_mul_mirror, hq, trinomial_natTrailingDegree hkm' hmn' x.ne_zero]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ← trinomial_natDegree hkm hmn w.ne_zero, ←
      hp, ← natDegree_mul_mirror, hpq, natDegree_mul_mirror, hq,
      trinomial_natDegree hkm' hmn' z.ne_zero]
  subst hk
  subst hn
  rcases eq_or_eq_neg_of_sq_eq_sq (y : ℤ) (v : ℤ)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · rw [h1] at hq
    rcases IsUnitTrinomial.irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rw [h1] at hq
    rw [trinomial_def] at hp
    rw [← neg_inj, neg_add, neg_add, ← neg_mul, ← neg_mul, ← neg_mul, ← C_neg, ← C_neg, ← C_neg]
      at hp
    rw [← neg_mul_neg, ← mirror_neg] at hpq
    rcases IsUnitTrinomial.irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with
      (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))

/-! ### Trinomial bookkeeping for the two families

`A = X^k - X - 1` (the Selmer trinomial) and `B = X^(j+2) - X^(j+1) - 1`
(the AFK trinomial, `l = j + 1`). -/

theorem selmer_trinomial (k : ℕ) :
    (X ^ k - X - 1 : ℤ[X]) = trinomial 0 1 k (-1) (-1) 1 := by
  simp only [trinomial, C_neg, C_1]; ring1

theorem afk_trinomial (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]) = trinomial 0 (j + 1) (j + 2) (-1) (-1) 1 := by
  simp only [trinomial, C_neg, C_1]; ring1

theorem selmer_monic {k : ℕ} (hk : 1 < k) : (X ^ k - X - 1 : ℤ[X]).Monic := by
  rw [selmer_trinomial k]; exact trinomial_monic zero_lt_one hk

theorem afk_monic (j : ℕ) : (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).Monic := by
  rw [afk_trinomial j]; exact trinomial_monic (by omega) (by omega)

theorem selmer_natDegree {k : ℕ} (hk : 1 < k) :
    (X ^ k - X - 1 : ℤ[X]).natDegree = k := by
  rw [selmer_trinomial k]; exact trinomial_natDegree zero_lt_one hk one_ne_zero

theorem afk_natDegree (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).natDegree = j + 2 := by
  rw [afk_trinomial j]; exact trinomial_natDegree (by omega) (by omega) one_ne_zero

theorem afk_isUnitTrinomial (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).IsUnitTrinomial := by
  rw [afk_trinomial j]
  exact ⟨0, j + 1, j + 2, by omega, by omega, -1, -1, 1, rfl⟩

theorem selmer_mirror {k : ℕ} (hk : 1 < k) :
    (X ^ k - X - 1 : ℤ[X]).mirror = 1 - X ^ (k - 1) - X ^ k := by
  rw [selmer_trinomial k,
    trinomial_mirror zero_lt_one hk (by norm_num) (by norm_num)]
  have he : k - 1 + 0 = k - 1 := by omega
  rw [he]
  simp only [trinomial, C_neg, C_1]; ring1

theorem afk_mirror (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).mirror = 1 - X - X ^ (j + 2) := by
  rw [afk_trinomial j,
    trinomial_mirror (by omega) (by omega) (by norm_num) (by norm_num)]
  have he : j + 2 - (j + 1) + 0 = 1 := by omega
  rw [he]
  simp only [trinomial, C_neg, C_1, pow_one]; ring1

theorem selmer_eval_one (k : ℕ) : (X ^ k - X - 1 : ℤ[X]).eval 1 = -1 := by simp

theorem afk_eval_one (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).eval 1 = -1 := by simp

theorem selmer_eval_zero {k : ℕ} (hk : 1 < k) :
    (X ^ k - X - 1 : ℤ[X]).eval 0 = -1 := by
  simp [zero_pow (by omega : k ≠ 0)]

theorem selmer_mirror_eval_zero {k : ℕ} (hk : 1 < k) :
    (X ^ k - X - 1 : ℤ[X]).mirror.eval 0 = 1 := by
  rw [selmer_mirror hk]
  simp [zero_pow (by omega : k ≠ 0), zero_pow (by omega : k - 1 ≠ 0)]

theorem afk_coeff_zero (j : ℕ) :
    (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).coeff 0 = -1 := by
  rw [afk_trinomial j]
  exact trinomial_trailing_coeff' (by omega) (by omega)

/-! ### Selmer's theorem pins the minimal polynomial -/

/-- `X^k - X - 1` is the minimal polynomial over ℤ of any real root
(Selmer 1956, via Mathlib's `X_pow_sub_X_sub_one_irreducible`). -/
theorem minpoly_eq_selmer {p : ℝ} {k : ℕ} (hk : 1 < k) (hpk : p ^ k = p + 1) :
    minpoly ℤ p = X ^ k - X - 1 := by
  have haev : aeval p (X ^ k - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hpk]; ring1
  have hint : IsIntegral ℤ p := ⟨_, selmer_monic hk, haev⟩
  obtain ⟨e, he⟩ := minpoly.isIntegrallyClosed_dvd hint haev
  rcases (X_pow_sub_X_sub_one_irreducible
      (by omega : k ≠ 1)).isUnit_or_isUnit he with h | h
  · exact absurd h (minpoly.not_isUnit ℤ p)
  · exact eq_of_monic_of_associated (minpoly.monic hint) (selmer_monic hk)
      ⟨h.unit, by rw [IsUnit.unit_spec]; exact he.symm⟩

/-- The Selmer trinomial of a morphic number divides its AFK trinomial. -/
theorem selmer_dvd_afk {p : ℝ} {k j : ℕ} (hk : 1 < k) (hpk : p ^ k = p + 1)
    (hpl : p ^ (j + 1) * (p - 1) = 1) :
    (X ^ k - X - 1 : ℤ[X]) ∣ X ^ (j + 2) - X ^ (j + 1) - 1 := by
  have haev : aeval p (X ^ k - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hpk]; ring1
  have haevB : aeval p (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hpl
  rw [← minpoly_eq_selmer hk hpk]
  exact minpoly.isIntegrallyClosed_dvd ⟨_, selmer_monic hk, haev⟩ haevB

/-! ### The cofactor is mirror-fixed -/

/-- If a unit trinomial `B` factors as `A * q`, and `A` is barred from
`±`-mirror-symmetry by its evaluations at `0` and `1`, then the cofactor
`q` is mirror-fixed.  This is the Tverberg-instance step, run through the
Ljunggren dichotomy. -/
theorem cofactor_mirror_fixed {A B q : ℤ[X]} (hB : B.IsUnitTrinomial)
    (hfac : B = A * q) (hA0 : A ≠ 0)
    (hA1 : A.eval 1 = -1) (hB1 : B.eval 1 = -1)
    (hAz : A.eval 0 = -1) (hAmz : A.mirror.eval 0 = 1) :
    q.mirror = q := by
  have hBne : B ≠ 0 := hB.ne_zero
  have hqne : q ≠ 0 := fun h => hBne (by rw [hfac, h, mul_zero])
  have hqmne : q.mirror ≠ 0 := fun h => hqne (mirror_eq_zero.mp h)
  have hBm : B.mirror = A.mirror * q.mirror := by rw [hfac, mirror_mul_of_domain]
  have hkey : B * B.mirror = (A * q.mirror) * (A * q.mirror).mirror := by
    rw [mirror_mul_of_domain, mirror_mirror, hBm, hfac]; ring1
  rcases mirror_dichotomy hB hkey with h | h | h | h
  · -- `A * q.mirror = B = A * q`
    exact mul_left_cancel₀ hA0 (h.trans hfac)
  · -- `A * q.mirror = -B` would force `q.eval 1 = 0`, against `B.eval 1 = -1`
    have h2 : q.mirror = -q :=
      mul_left_cancel₀ hA0 (h.trans (by rw [hfac]; ring1))
    have he1 := congrArg (eval 1) h2
    rw [mirror_eval_one, eval_neg] at he1
    have hq1 : q.eval 1 = 0 := by linarith
    have hzero : B.eval 1 = 0 := by rw [hfac, eval_mul, hq1, mul_zero]
    rw [hB1] at hzero; norm_num at hzero
  · -- `A * q.mirror = B.mirror` would force `A = A.mirror`
    have h3 : A = A.mirror := mul_right_cancel₀ hqmne (h.trans hBm)
    have h4 := congrArg (eval 0) h3
    rw [hAz, hAmz] at h4; norm_num at h4
  · -- `A * q.mirror = -B.mirror` would force `A = -A.mirror`
    have h3 : A = -A.mirror :=
      mul_right_cancel₀ hqmne (h.trans (by rw [hBm]; ring1))
    have h4 := congrArg (eval 1) h3
    rw [hA1, eval_neg, mirror_eval_one, hA1] at h4
    norm_num at h4

/-! ### The mirror-fixed cofactor divides `X² - X + 1` -/

theorem quad_trinomial : (X ^ 2 - X + 1 : ℤ[X]) = trinomial 0 1 2 1 (-1) 1 := by
  simp only [trinomial, C_neg, C_1]; ring1

theorem quad_monic : (X ^ 2 - X + 1 : ℤ[X]).Monic := by
  rw [quad_trinomial]; exact trinomial_monic zero_lt_one one_lt_two

theorem quad_natDegree : (X ^ 2 - X + 1 : ℤ[X]).natDegree = 2 := by
  rw [quad_trinomial]; exact trinomial_natDegree zero_lt_one one_lt_two one_ne_zero

/-- The arithmetic heart of the Tverberg instance: a common divisor of the
AFK trinomial and its mirror, coprime to `X`, divides `X² - X + 1`.
(AFK reach the same quadratic through the primitive sixth roots of unity;
here it falls out of two ring identities.) -/
theorem cofactor_dvd_quadratic {j : ℕ} {q : ℤ[X]}
    (hdvdB : q ∣ (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]))
    (hdvdBm : q ∣ (1 - X - X ^ (j + 2) : ℤ[X]))
    (hunit : IsUnit (q.coeff 0)) :
    q ∣ (X ^ 2 - X + 1 : ℤ[X]) := by
  have h1 : q ∣ (X * (X ^ j + 1) : ℤ[X]) := by
    have hsum := dvd_add hdvdB hdvdBm
    have he : (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]) + (1 - X - X ^ (j + 2))
        = -(X * (X ^ j + 1)) := by ring1
    rw [he] at hsum
    exact dvd_neg.mp hsum
  have hco : IsCoprime q (X : ℤ[X]) := by
    rcases Int.isUnit_iff.mp hunit with hc | hc
    · refine ⟨1, -q.divX, ?_⟩
      have hx := X_mul_divX_add q
      rw [hc, C_1] at hx
      linear_combination -hx
    · refine ⟨-1, q.divX, ?_⟩
      have hx := X_mul_divX_add q
      rw [hc, C_neg, C_1] at hx
      linear_combination hx
  have h2 : q ∣ (X ^ j + 1 : ℤ[X]) := hco.dvd_of_dvd_mul_left h1
  have h3 : q ∣ ((X - 1) * (X * (X ^ j + 1)) : ℤ[X]) := (h2.mul_left X).mul_left _
  have he2 : ((X - 1) * (X * (X ^ j + 1)) : ℤ[X])
      = (X ^ (j + 2) - X ^ (j + 1) - 1) + (X ^ 2 - X + 1) := by ring1
  rw [he2] at h3
  exact (dvd_add_right hdvdB).mp h3

/-- A monic divisor of `X² - X + 1` over ℤ is `1` or `X² - X + 1`:
degree 1 is impossible because `a² + a + 1 = 0` has no integer solution. -/
theorem monic_dvd_quadratic {q : ℤ[X]} (hm : q.Monic)
    (hdvd : q ∣ (X ^ 2 - X + 1 : ℤ[X])) : q = 1 ∨ q = X ^ 2 - X + 1 := by
  obtain ⟨r, hr⟩ := hdvd
  have hrm : r.Monic := hm.of_mul_monic_left (hr ▸ quad_monic)
  have hdeg : q.natDegree + r.natDegree = 2 := by
    have hd := congrArg natDegree hr
    rw [quad_natDegree, Monic.natDegree_mul hm hrm] at hd
    omega
  have hcase : q.natDegree = 0 ∨ q.natDegree = 1 ∨ q.natDegree = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · exact Or.inl (hm.natDegree_eq_zero.mp h0)
  · exfalso
    have hqa : q = X + C (q.coeff 0) := hm.eq_X_add_C h1
    set a : ℤ := q.coeff 0 with ha
    have heval := congrArg (eval (-a)) hr
    have hqe : q.eval (-a) = 0 := by
      rw [hqa]; simp
    rw [eval_mul, hqe, zero_mul] at heval
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one] at heval
    nlinarith [sq_nonneg (2 * a + 1), heval]
  · have hr0 : r.natDegree = 0 := by omega
    have hr1 : r = 1 := hrm.natDegree_eq_zero.mp hr0
    rw [hr1, mul_one] at hr
    exact Or.inr hr.symm

/-! ### The forced factorizations -/

/-- Cofactor `1`: `B = A` forces `(k, l) = (2, 1)`. -/
theorem endgame_one {k j : ℕ} (hk : 1 < k)
    (h : (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]) = X ^ k - X - 1) :
    k = 2 ∧ j = 0 := by
  have hdeg : j + 2 = k := by
    have hd := congrArg natDegree h
    rwa [afk_natDegree j, selmer_natDegree hk] at hd
  have hX : (X : ℤ[X]) ^ (j + 1) = X ^ 1 := by
    rw [← hdeg] at h
    linear_combination -h
  have hj := congrArg natDegree hX
  rw [natDegree_X_pow, natDegree_X_pow] at hj
  omega

/-- Cofactor `X² - X + 1`: the forced factorization
`(X^k - X - 1)(X² - X + 1) = X^(k+2) - X^(k+1) - 1` expands to
`X^k = X³`, AFK's "by direct computation": `(k, l) = (3, 4)`. -/
theorem endgame_quadratic {k j : ℕ} (hk : 1 < k)
    (h : (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X])
      = (X ^ k - X - 1) * (X ^ 2 - X + 1)) :
    k = 3 ∧ j = 3 := by
  have hdeg : j + 2 = k + 2 := by
    have hd := congrArg natDegree h
    rwa [afk_natDegree j, Monic.natDegree_mul (selmer_monic hk) quad_monic,
      selmer_natDegree hk, quad_natDegree] at hd
  have hjk : j = k := by omega
  have hX : (X : ℤ[X]) ^ k = X ^ 3 := by
    rw [hjk] at h
    linear_combination -h
  have hk3 := congrArg natDegree hX
  rw [natDegree_X_pow, natDegree_X_pow] at hk3
  omega

/-! ### The classification -/

/-- **Aarts–Fokkink–Kruijtzer 2001, Theorem (p. 58)**: there exist only two
morphic numbers — the divine proportion and the plastic number. -/
theorem morphic_iff (p : ℝ) :
    IsMorphic p ↔ p = Real.goldenRatio ∨ p = plasticNumber := by
  constructor
  · rintro ⟨hp1, k, l, hk0, hl0, hpk, hpl⟩
    have hk : 1 < k := by
      by_contra hcon
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hpk
      linarith
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    obtain ⟨q, hq⟩ := selmer_dvd_afk hk hpk hpl
    have hqmonic : q.Monic := (selmer_monic hk).of_mul_monic_left (hq ▸ afk_monic j)
    have hmf : q.mirror = q :=
      cofactor_mirror_fixed (afk_isUnitTrinomial j) hq (selmer_monic hk).ne_zero
        (selmer_eval_one k) (afk_eval_one j) (selmer_eval_zero hk)
        (selmer_mirror_eval_zero hk)
    have hdvdB : q ∣ (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]) :=
      ⟨X ^ k - X - 1, by rw [hq]; ring1⟩
    have hdvdBm : q ∣ (1 - X - X ^ (j + 2) : ℤ[X]) := by
      rw [← afk_mirror j]
      have hqm : q.mirror ∣ (X ^ (j + 2) - X ^ (j + 1) - 1 : ℤ[X]).mirror := by
        rw [hq, mirror_mul_of_domain]
        exact Dvd.intro_left _ rfl
      rwa [hmf] at hqm
    have hcu : IsUnit (q.coeff 0) := by
      have hc := congrArg (fun r : ℤ[X] => r.coeff 0) hq
      simp only [mul_coeff_zero] at hc
      rw [afk_coeff_zero j] at hc
      exact IsUnit.of_mul_eq_one (-(X ^ k - X - 1 : ℤ[X]).coeff 0)
        (by linear_combination hc)
    rcases monic_dvd_quadratic hqmonic
        (cofactor_dvd_quadratic hdvdB hdvdBm hcu) with h1 | h1
    · rw [h1, mul_one] at hq
      obtain ⟨hk2, -⟩ := endgame_one hk hq
      subst hk2
      exact Or.inl (eq_goldenRatio_of_sq hp1 hpk)
    · rw [h1] at hq
      obtain ⟨hk3, -⟩ := endgame_quadratic hk hq
      subst hk3
      exact Or.inr (eq_plasticNumber_of_cubic hp1 hpk)
  · rintro (rfl | rfl)
    · exact goldenRatio_morphic
    · exact plasticNumber_morphic

end Morphic
end PDT

/-! ### Axiom audit — expected: propext, Classical.choice, Quot.sound only -/

#print axioms PDT.Morphic.morphic_iff
#print axioms PDT.Morphic.goldenRatio_morphic
#print axioms PDT.Morphic.plasticNumber_morphic
#print axioms PDT.Morphic.plasticNumber_cubic
#print axioms PDT.Morphic.one_lt_plasticNumber
