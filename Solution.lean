/-
Solution: proofs of the challenge statements, transferred from the
PdtMorphic development (definition, plastic number with cubic and
uniqueness, the mirror dichotomy, the cofactor analysis in ℤ[X], and
the classification).
-/
import PdtMorphic

namespace MorphicNumbers

/-- **The Aarts–Fokkink–Kruijtzer classification** (2001, Theorem, p. 58):
there exist only two morphic numbers — the divine proportion and the
plastic number. -/
theorem morphic_iff (p rho : ℝ) (hrho1 : 1 < rho) (hrho3 : rho ^ 3 = rho + 1) :
    (1 < p ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = p + 1 ∧ p ^ l * (p - 1) = 1)
      ↔ p = Real.goldenRatio ∨ p = rho := by
  have hr : rho = PDT.Morphic.plasticNumber :=
    PDT.Morphic.eq_plasticNumber_of_cubic hrho1 hrho3
  subst hr
  exact PDT.Morphic.morphic_iff p

/-- **The golden ratio is morphic**, with `(k, l) = (2, 1)`. Routine
consequence of `Real.goldenRatio_sq`; readability surface only. -/
theorem goldenRatio_morphic :
    1 < Real.goldenRatio ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      Real.goldenRatio ^ k = Real.goldenRatio + 1 ∧
      Real.goldenRatio ^ l * (Real.goldenRatio - 1) = 1 :=
  PDT.Morphic.goldenRatio_morphic

/-- **The plastic number is morphic**, with `(k, l) = (3, 4)` via AFK's
identity `x⁵ − x⁴ − 1 = (x³ − x − 1)(x² − x + 1)`. Routine consequence
of the defining cubic; readability surface only. -/
theorem plasticNumber_morphic (rho : ℝ) (hrho1 : 1 < rho)
    (hrho3 : rho ^ 3 = rho + 1) :
    1 < rho ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      rho ^ k = rho + 1 ∧ rho ^ l * (rho - 1) = 1 := by
  have hr : rho = PDT.Morphic.plasticNumber :=
    PDT.Morphic.eq_plasticNumber_of_cubic hrho1 hrho3
  subst hr
  exact PDT.Morphic.plasticNumber_morphic

theorem plastic_exists : ∃ x : ℝ, 1 < x ∧ x ^ 3 = x + 1 :=
  PDT.Morphic.exists_plastic

end MorphicNumbers

/-! ### Axiom audit — every build prints the audit for the compared theorems -/

#print axioms MorphicNumbers.morphic_iff
#print axioms MorphicNumbers.goldenRatio_morphic
#print axioms MorphicNumbers.plasticNumber_morphic
#print axioms MorphicNumbers.plastic_exists
