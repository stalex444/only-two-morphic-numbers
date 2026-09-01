/-
PdtFamilyBoundaries — general-n boundaries of the golden family x^n = x + 1.

For each n ≥ 2 the Selmer trinomial X^n − X − 1 (irreducible for every
n ≥ 2: Selmer, Math. Scand. 4 (1956) 287–302, in Mathlib as
`Polynomial.X_pow_sub_X_sub_one_irreducible_rat`) has a unique real root
r_n > 1, strictly decreasing in n: r_2 = φ (golden ratio), r_3 = ρ
(plastic number), r_4, r_5, …  This module proves the family-level
boundary statements:

* `family_root_exists_unique` / `family_root_strict_anti` — existence,
  uniqueness, and strict decrease of r_n.
* `family_morphic_boundary` — r_n is morphic (Aarts–Fokkink–Kruijtzer
  2001) iff n ≤ 3.
* `no_unit_circle_root` — X^n − X − 1 has no complex root of modulus 1,
  for any n (|z| = |z+1| = 1 forces z² + z + 1 = 0, so z³ = 1, and every
  residue of n mod 3 is impossible).
* `family_le_mahlerMeasure` — r_n ≤ M(X^n − X − 1), by the monic
  root-product (Jensen) form of the Mahler measure.
* `family_measure_eq_iff_pisot` — M(X^n − X − 1) = r_n iff every complex
  root other than r_n lies strictly inside the unit circle: the
  measure-language form of "r_n is a Pisot number", exact because the
  family never has unimodular roots (Selmer irreducibility + the circle
  exclusion above).
* `siegel_conditional_closure` — IF the plastic number is the smallest
  Pisot number (Siegel, Duke Math. J. 11 (1944) 597–602 — entering ONLY
  as the explicit hypothesis `siegel`, not proved here), THEN
  r_n < M(X^n − X − 1) for every n ≥ 4.
* `Q_lt_psi` — the quartic root lies strictly below ψ (ψ⁴ = ψ³ + 1), the
  Mahler measure of the n = 4 member.

Siegel's minimality theorem is the only classical input that appears as a
hypothesis; every other statement is kernel-checked unconditionally.
-/
import PdtMorphic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Ring.GeomSum

namespace PDT
namespace FamilyBoundaries

open Polynomial Morphic ComplexConjugate

/-! ### Order helper: `x ↦ x^n − x` is strictly increasing on `[1, ∞)` -/

lemma pow_sub_self_strictMono {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 1 ≤ x)
    (hxy : x < y) : x ^ n - x < y ^ n - y := by
  have hy : 1 ≤ y := le_of_lt (lt_of_le_of_lt hx hxy)
  have hgeom := geom_sum₂_mul y x n
  have hterm : ∀ i ∈ Finset.range n, (1 : ℝ) ≤ y ^ i * x ^ (n - 1 - i) := by
    intro i _
    have h1 : (1 : ℝ) ≤ y ^ i := one_le_pow₀ hy
    have h2 : (1 : ℝ) ≤ x ^ (n - 1 - i) := one_le_pow₀ hx
    nlinarith
  have hsum : (n : ℝ) ≤ ∑ i ∈ Finset.range n, y ^ i * x ^ (n - 1 - i) := by
    have h := Finset.sum_le_sum hterm
    simpa using h
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < y - x := sub_pos.mpr hxy
  have hkey : 2 * (y - x) ≤
      (∑ i ∈ Finset.range n, y ^ i * x ^ (n - 1 - i)) * (y - x) :=
    mul_le_mul_of_nonneg_right (le_trans h2n hsum) (le_of_lt hpos)
  linarith [hkey, hgeom]

/-! ### The family root r_n: existence, uniqueness, strict decrease -/

/-- `x^n = x + 1` has a real root above `1` (IVT on `[1, 2]`). -/
theorem family_root_exists {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : ℝ, 1 < x ∧ x ^ n = x + 1 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ n - y - 1) (Set.Icc 1 2) := by fun_prop
  have h4 : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn
  have hmem : (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ n - 1 - 1) ((2 : ℝ) ^ n - 2 - 1) := by
    rw [Set.mem_Icc]
    refine ⟨by norm_num, by linarith⟩
  obtain ⟨x, hmemx, hx⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hc hmem
  simp only at hx
  refine ⟨x, ?_, by linarith⟩
  rcases lt_or_eq_of_le hmemx.1 with h | h
  · exact h
  · rw [← h] at hx; norm_num at hx

/-- **Existence and uniqueness of the family root**: for every `n ≥ 2`
there is exactly one real `r > 1` with `r^n = r + 1`. -/
theorem family_root_exists_unique {n : ℕ} (hn : 2 ≤ n) :
    ∃! r : ℝ, 1 < r ∧ r ^ n = r + 1 := by
  obtain ⟨r, hr1, hrn⟩ := family_root_exists hn
  refine ⟨r, ⟨hr1, hrn⟩, ?_⟩
  rintro s ⟨hs1, hsn⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono := pow_sub_self_strictMono hn hs1.le h
    linarith
  · have hmono := pow_sub_self_strictMono hn hr1.le h
    linarith

/-- **Strict decrease of the family root**: the root of `x^(n+1) = x + 1`
lies strictly below the root of `x^n = x + 1`. -/
theorem family_root_strict_anti {n : ℕ} (hn : 2 ≤ n) {r s : ℝ} (hr1 : 1 < r)
    (hr : r ^ n = r + 1) (hs1 : 1 < s) (hs : s ^ (n + 1) = s + 1) : s < r := by
  have hlt : s ^ n < s ^ (n + 1) := pow_lt_pow_right₀ hs1 (Nat.lt_succ_self n)
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt2
  · rw [heq] at hr
    linarith
  · have hmono := pow_sub_self_strictMono hn hr1.le hlt2
    linarith

/-! ### Numerical brackets -/

lemma golden_lb : (3 / 2 : ℝ) < Real.goldenRatio := by
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_sq
  by_contra hc
  push Not at hc
  nlinarith

lemma plastic_lb : (132 / 100 : ℝ) < plasticNumber := by
  have h1 := one_lt_plasticNumber
  have h3 := plasticNumber_cubic
  by_contra hc
  push Not at hc
  have h2 : plasticNumber ^ 2 ≤ (132 / 100) * plasticNumber := by nlinarith
  have h4 : plasticNumber ^ 3 ≤ (132 / 100) * plasticNumber ^ 2 := by
    nlinarith [sq_nonneg plasticNumber]
  linarith

/-- Descent: for `n ≥ 4` the family root drops below `1.23` (from
`q^4 ≤ q^n = q + 1`). -/
lemma family_descent {n : ℕ} (hn : 4 ≤ n) {q : ℝ} (hq1 : 1 < q)
    (hq : q ^ n = q + 1) : q < 123 / 100 := by
  have h4 : q ^ 4 ≤ q + 1 := by
    calc q ^ 4 ≤ q ^ n := pow_le_pow_right₀ hq1.le hn
    _ = q + 1 := hq
  by_contra hc
  push Not at hc
  have h7 : (123 / 100 : ℝ) * q ≤ q ^ 2 := by nlinarith
  have h6 : (123 / 100 : ℝ) * q ^ 2 ≤ q ^ 3 := by nlinarith
  have h5 : (123 / 100 : ℝ) * q ^ 3 ≤ q ^ 4 := by nlinarith
  linarith

/-- For `n ≥ 4` the family root lies strictly below the plastic number. -/
lemma family_lt_plastic {n : ℕ} (hn : 4 ≤ n) {q : ℝ} (hq1 : 1 < q)
    (hq : q ^ n = q + 1) : q < plasticNumber :=
  lt_trans (family_descent hn hq1 hq) (lt_trans (by norm_num) plastic_lb)

/-! ### The morphic boundary -/

/-- **The morphic boundary of the golden family**: for `n ≥ 2` and real
`q > 1` with `q^n = q + 1`, `q` is morphic (Aarts–Fokkink–Kruijtzer 2001)
iff `n ≤ 3`.  Forward: the AFK classification forces `q ∈ {φ, ρ}`, but
for `n ≥ 4` descent gives `q < 1.23 < min (φ, ρ)`.  Reverse: `n = 2, 3`
are the golden and plastic witnesses via uniqueness of the root. -/
theorem family_morphic_boundary {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq1 : 1 < q)
    (hq : q ^ n = q + 1) : IsMorphic q ↔ n ≤ 3 := by
  constructor
  · intro hm
    by_contra hcon
    push Not at hcon
    have hn4 : 4 ≤ n := hcon
    have hlt := family_descent hn4 hq1 hq
    rcases (morphic_iff q).mp hm with rfl | rfl
    · linarith [golden_lb]
    · linarith [plastic_lb]
  · intro h3
    interval_cases n
    · exact (morphic_iff q).mpr (Or.inl (eq_goldenRatio_of_sq hq1 hq))
    · exact (morphic_iff q).mpr (Or.inr (eq_plasticNumber_of_cubic hq1 hq))

/-! ### No roots on the unit circle (the ω-argument) -/

/-- **Circle exclusion for the whole family**: `X^n − X − 1` has no
complex root of modulus 1, for any `n`.  From `|z| = |z + 1| = 1` the
conjugate identities force `z² + z + 1 = 0` (so `z` is a primitive cube
root of unity and `z³ = 1`), and each residue of `n` mod 3 makes
`z^n = z + 1` impossible. -/
theorem no_unit_circle_root (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    z ^ n ≠ z + 1 := by
  intro heq
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1 : ‖z + 1‖ = 1 := by
    rw [← heq, norm_pow, hz, one_pow]
  have hns : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hns1 : Complex.normSq (z + 1) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz1]; norm_num
  have h1 : z * conj z = 1 := by
    rw [Complex.mul_conj, hns, Complex.ofReal_one]
  have h2 : (z + 1) * (conj z + 1) = 1 := by
    have hc : conj (z + 1) = conj z + 1 := by simp
    rw [← hc, Complex.mul_conj, hns1, Complex.ofReal_one]
  have hcz : conj z = -z - 1 := by linear_combination h2 - h1
  have hquad : z ^ 2 + z + 1 = 0 := by linear_combination z * hcz - h1
  have hcube : z ^ 3 = 1 := by linear_combination (z - 1) * hquad
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hcube, one_pow, mul_one]
    have h3 : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [pow_zero, pow_one, or_true, true_or]
  rcases key with hk | hk | hk
  · rw [hk] at heq
    exact hz0 (by linear_combination -heq)
  · rw [hk] at heq
    simp at heq
  · rw [hk] at heq
    have hzm : z = -1 := by linear_combination (hquad - heq) / 2
    rw [hzm] at hquad
    norm_num at hquad

/-! ### Mahler-measure bookkeeping for the family -/

lemma selmer_map_C (n : ℕ) :
    (X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ) = (X ^ n - X - 1 : ℂ[X]) := by
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]

lemma selmer_monic_C {n : ℕ} (hn : 2 ≤ n) : (X ^ n - X - 1 : ℂ[X]).Monic := by
  have h := (selmer_monic (show 1 < n by omega)).map (algebraMap ℤ ℂ)
  rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one] at h

lemma selmer_mem_roots {n : ℕ} (hn : 2 ≤ n) {z : ℂ} :
    z ∈ (X ^ n - X - 1 : ℂ[X]).roots ↔ z ^ n = z + 1 := by
  rw [mem_roots (selmer_monic_C hn).ne_zero, IsRoot.def]
  simp only [eval_sub, eval_pow, eval_X, eval_one]
  rw [sub_sub, sub_eq_zero]

/-- Selmer irreducibility over ℚ makes the complex roots simple. -/
lemma selmer_roots_nodup {n : ℕ} (hn : 2 ≤ n) :
    (X ^ n - X - 1 : ℂ[X]).roots.Nodup := by
  have hirr : Irreducible (X ^ n - X - 1 : ℚ[X]) :=
    X_pow_sub_X_sub_one_irreducible_rat (show n ≠ 1 by omega)
  have hsep : ((X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).Separable :=
    hirr.separable.map
  rw [selmer_map_C n] at hsep
  exact nodup_roots hsep

/-! ### The general-n Mahler lower bound -/

/-- **The family root bounds the Mahler measure from below**: for `n ≥ 2`
and real `q > 1` with `q^n = q + 1`,
`q ≤ M(X^n − X − 1)` — by the monic root-product form: the measure is the
product of `max 1 ‖·‖` over all roots, one of which is `q`. -/
theorem family_le_mahlerMeasure {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq1 : 1 < q)
    (hq : q ^ n = q + 1) :
    q ≤ ((X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure := by
  rw [selmer_map_C n]
  have hqC : (q : ℂ) ^ n = (q : ℂ) + 1 := by exact_mod_cast hq
  have hroot : (q : ℂ) ∈ (X ^ n - X - 1 : ℂ[X]).roots := (selmer_mem_roots hn).mpr hqC
  have hsplit := Multiset.prod_map_erase (f := fun a : ℂ => max 1 ‖a‖) hroot
  have hrest : (1 : ℝ) ≤
      (((X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ)).map (fun a => max 1 ‖a‖)).prod := by
    refine Multiset.one_le_prod ?_
    intro x hx
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hx
    exact le_max_left _ _
  have hnorm : max 1 ‖(q : ℂ)‖ = q := by
    rw [Complex.norm_of_nonneg (by linarith)]
    exact max_eq_right hq1.le
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, (selmer_monic_C hn).leadingCoeff,
    norm_one, one_mul, ← hsplit, hnorm]
  exact le_mul_of_one_le_right (by linarith) hrest

/-! ### The measure-equality ⟺ Pisot equivalence -/

/-- **Measure equality is exactly the Pisot condition**: for `n ≥ 2` and
real `q > 1` with `q^n = q + 1`, `M(X^n − X − 1) = q` iff every complex
root other than `q` lies strictly inside the unit circle.  The forward
direction needs `no_unit_circle_root` (a modulus-1 root would be
invisible to the measure); the reverse uses Selmer irreducibility for
simple roots.  This theorem is the honest form of "the Mahler-measure
boundary restates the Pisot boundary". -/
theorem family_measure_eq_iff_pisot {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq1 : 1 < q)
    (hq : q ^ n = q + 1) :
    ((X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = q ↔
      ∀ z : ℂ, z ^ n = z + 1 → z ≠ (q : ℂ) → ‖z‖ < 1 := by
  rw [selmer_map_C n]
  have hnodup := selmer_roots_nodup hn
  have hqC : (q : ℂ) ^ n = (q : ℂ) + 1 := by exact_mod_cast hq
  have hroot : (q : ℂ) ∈ (X ^ n - X - 1 : ℂ[X]).roots := (selmer_mem_roots hn).mpr hqC
  have hsplit := Multiset.prod_map_erase (f := fun a : ℂ => max 1 ‖a‖) hroot
  have hnorm : max 1 ‖(q : ℂ)‖ = q := by
    rw [Complex.norm_of_nonneg (by linarith)]
    exact max_eq_right hq1.le
  have hM : (X ^ n - X - 1 : ℂ[X]).mahlerMeasure
      = q * (((X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ)).map
        (fun a => max 1 ‖a‖)).prod := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, (selmer_monic_C hn).leadingCoeff,
      norm_one, one_mul, ← hsplit, hnorm]
  rw [hM]
  constructor
  · intro hMq z hzn hzq
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · exact no_unit_circle_root n z heq.symm hzn
    have hzroot : z ∈ (X ^ n - X - 1 : ℂ[X]).roots := (selmer_mem_roots hn).mpr hzn
    have hzerase : z ∈ (X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ) :=
      hnodup.mem_erase_iff.mpr ⟨hzq, hzroot⟩
    have hsplit2 := Multiset.prod_map_erase (f := fun a : ℂ => max 1 ‖a‖) hzerase
    have hrest : (1 : ℝ) ≤ ((((X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ)).erase z).map
        (fun a => max 1 ‖a‖)).prod := by
      refine Multiset.one_le_prod ?_
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hx
      exact le_max_left _ _
    have hz1 : (1 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le hlt (le_max_right _ _)
    have hE : (1 : ℝ) < (((X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ)).map
        (fun a => max 1 ‖a‖)).prod := by
      rw [← hsplit2]
      nlinarith [hrest, hz1]
    nlinarith [hMq, hE, hq1]
  · intro hall
    have hone : (((X ^ n - X - 1 : ℂ[X]).roots.erase (q : ℂ)).map
        (fun a => max 1 ‖a‖)).prod = 1 := by
      refine Multiset.prod_eq_one ?_
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨haq, haroot⟩ := hnodup.mem_erase_iff.mp ha
      exact max_eq_left (hall a ((selmer_mem_roots hn).mp haroot) haq).le
    rw [hone, mul_one]

/-! ### The Siegel-conditional strict excess -/

/-- **Siegel-conditional closure**: IF the plastic number is the smallest
Pisot number — Siegel's 1944 theorem, taken here as the explicit
hypothesis `siegel`, with "Pisot" spelled inline: a real algebraic
integer `x > 1` all of whose other complex conjugates (roots of
`minpoly ℤ x`) have modulus `< 1` — THEN for every `n ≥ 4` the family
root lies strictly below the Mahler measure: `r_n < M(X^n − X − 1)`.
Kernel-held pieces: the Jensen lower bound, the measure⟺Pisot
equivalence, Selmer's minimal-polynomial identification, and the descent
`r_n < ρ` for `n ≥ 4`.  Siegel's theorem itself is NOT proved here. -/
theorem siegel_conditional_closure
    (siegel : ∀ x : ℝ, 1 < x → IsIntegral ℤ x →
      (∀ z : ℂ, aeval z (minpoly ℤ x) = 0 → z ≠ (x : ℂ) → ‖z‖ < 1) →
      plasticNumber ≤ x) :
    ∀ n : ℕ, 4 ≤ n → ∀ q : ℝ, 1 < q → q ^ n = q + 1 →
      q < ((X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure := by
  intro n hn q hq1 hq
  have hn2 : 2 ≤ n := by omega
  have hle := family_le_mahlerMeasure hn2 hq1 hq
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hM : ((X ^ n - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = q := h.symm
    have hall := (family_measure_eq_iff_pisot hn2 hq1 hq).mp hM
    have haev : (aeval q) (X ^ n - X - 1 : ℤ[X]) = 0 := by
      simp only [map_sub, map_pow, aeval_X, map_one]
      rw [hq]; ring1
    have hint : IsIntegral ℤ q := ⟨_, selmer_monic (show 1 < n by omega), haev⟩
    have hmin : minpoly ℤ q = X ^ n - X - 1 :=
      minpoly_eq_selmer (show 1 < n by omega) hq
    have hple : plasticNumber ≤ q := by
      refine siegel q hq1 hint ?_
      intro z hzaev hzq
      rw [hmin] at hzaev
      have hzn : z ^ n = z + 1 := by
        simp only [map_sub, map_pow, aeval_X, map_one] at hzaev
        linear_combination hzaev
      exact hall z hzn hzq
    have hlt := family_lt_plastic hn hq1 hq
    linarith

/-! ### The quartic root sits below ψ -/

/-- The quartic family root (`q⁴ = q + 1`) lies strictly below `ψ`
(`ψ⁴ = ψ³ + 1`), the Mahler measure of the `n = 4` member: brackets
`q < 1.23 < 1.29 < ψ`. -/
theorem Q_lt_psi {q psi : ℝ} (hq1 : 1 < q) (hq : q ^ 4 = q + 1)
    (hpsi1 : 1 < psi) (hpsi : psi ^ 4 = psi ^ 3 + 1) : q < psi := by
  have hqb : q < 123 / 100 := family_descent (le_refl 4) hq1 hq
  have hpb : (129 / 100 : ℝ) < psi := by
    by_contra hc
    push Not at hc
    have h2 : psi ^ 2 ≤ (129 / 100) * psi := by nlinarith
    have h3 : psi ^ 3 ≤ (129 / 100) * psi ^ 2 := by nlinarith [sq_nonneg psi]
    have h4 : psi ^ 4 ≤ (129 / 100) * psi ^ 3 := by
      nlinarith [sq_nonneg psi, mul_pos (mul_pos (lt_trans one_pos hpsi1)
        (lt_trans one_pos hpsi1)) (lt_trans one_pos hpsi1)]
    linarith
  linarith

end FamilyBoundaries
end PDT

/-! ### Axiom audit — expected: propext, Classical.choice, Quot.sound only -/

#print axioms PDT.FamilyBoundaries.family_root_exists_unique
#print axioms PDT.FamilyBoundaries.family_root_strict_anti
#print axioms PDT.FamilyBoundaries.family_morphic_boundary
#print axioms PDT.FamilyBoundaries.no_unit_circle_root
#print axioms PDT.FamilyBoundaries.family_le_mahlerMeasure
#print axioms PDT.FamilyBoundaries.family_measure_eq_iff_pisot
#print axioms PDT.FamilyBoundaries.siegel_conditional_closure
#print axioms PDT.FamilyBoundaries.Q_lt_psi
