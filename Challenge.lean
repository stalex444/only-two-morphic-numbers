import Mathlib

/-!
# Only two morphic numbers

The Aarts–Fokkink–Kruijtzer classification (Nieuw Archief voor Wiskunde
(5) 2 (2001) 56–58; open access at
nieuwarchief.nl/serie5/pdf/naw5-2001-02-1-056.pdf): a real number
`p > 1` is **morphic** if there are natural numbers `k, l ≥ 1` with

  `p + 1 = p ^ k`   and   `p − 1 = p ^ (−l)`

— the golden ratio's two scale properties — the paper's Figure 1
caption calls them superposition and juxtaposition — abstracted. THE THEOREM (p. 58): there exist only two
morphic numbers — the divine proportion `φ` (with `k, l = 2, 1`) and the
plastic number `ρ`, the real root of `x³ = x + 1`, with `k, l = 3, 4`
via the identity `x⁵ − x⁴ − 1 = (x³ − x − 1)(x² − x + 1)`.

The plastic number was introduced by Dom Hans van der Laan (Le Nombre
Plastique, Brill 1960) as the ideal ratio for spatial objects; the same
discovery was made independently by Gérard Cordonnier (Padovan 1994,
p. 96). That `φ` and `ρ` are the ONLY numbers with both scale
properties was conjectured in Kruijtzer's book Ruimte en Getal (1998)
and proved by Aarts, Fokkink, and Kruijtzer in 2001. The proof runs
through the irreducibility theory of trinomials: Selmer's theorem
(Math. Scand. 4 (1956) 287–302) makes `X^k − X − 1` the minimal
polynomial of `p`, hence a divisor of `X^(l+1) − X^l − 1`, and a lemma
AFK derive from Tverberg's theorem (Math. Scand. 8 (1960) 121–126)
forces the cofactor to be `1` or `X² − X + 1`; comparing coefficients
pins `(k, l) = (2, 1)` or `(3, 4)`.

## The compared statements

1. `morphic_iff` — THE theorem, the full classification: for every real
   `p`, the morphic property (spelled inline) holds iff
   `p = Real.goldenRatio` or `p = ρ`, where ρ is pinned hypothesis-style
   as a real in `(1, ∞)` with `ρ³ = ρ + 1` (it is unique there; the proof module carries the uniqueness lemma
(used by the solution)). The negative half (no third morphic number) and both witnesses are
carried by this iff, and the existence of the cubic's root by the
compared `plastic_exists`.
2. `goldenRatio_morphic` — the golden ratio is morphic, `(k, l) = (2, 1)`.
   A routine consequence of `Real.goldenRatio_sq`, stated separately for
   readability only — not a headline.
3. `plasticNumber_morphic` — the plastic number is morphic,
4. `plastic_exists` — the cubic's root exists,
   `(k, l) = (3, 4)` via AFK's displayed identity. Routine consequence
   of the cubic; readability surface only — not a headline.

Hypotheses are inline: the morphic property is spelled out in full in
each statement (`p − 1 = p ^ (−l)` rendered zpow-free as
`p ^ l * (p − 1) = 1`; the conjuncts `0 < k`, `0 < l` transcribe the
paper's "natural numbers" — they are in fact removable (`k = 0` would force `1 = p + 1`, against
`1 < p`; `l = 0` would force `p = 2`, killed by `2 ^ k = 3`)), and the plastic number
enters only through its defining property `1 < ρ ∧ ρ³ = ρ + 1`. The
statements use only Mathlib vocabulary — `Real.goldenRatio` and real
arithmetic — with no custom definitions.

## Proof route, stated honestly

Selmer's theorem is consumed from Mathlib
(`Polynomial.X_pow_sub_X_sub_one_irreducible`, T. Browning's
formalization). Where AFK cite Tverberg's general theorem, the solution
derives the needed instance from Mathlib's Ljunggren unit-trinomial
machinery (Ljunggren, Math. Scand. 8 (1960) 65–70 — same lineage, both
Math. Scand. 8 (1960)): the mirror dichotomy extracted from
`IsUnitTrinomial.irreducible_of_coprime` forces the cofactor to be
mirror-fixed. The remaining cofactor analysis then runs wholly in
`ℤ[X]` by a divisibility argument, where the paper argues through
complex roots of modulus 1 (a divergence in proof route, not in
statement; disclosed in `formalization.yaml`, with the two points the
paper leaves implicit — separability of the trinomial and the
power-of-the-quadratic point — handled explicitly by the formal
argument).

## Relation to the registered sibling entry

The registered entry PALOMAR-2026-08-31-000004
(stalex444/mahler-measure-minima) characterizes `x² − x − 1` and
`x³ − x − 1` as the degree-2 and degree-3 Mahler-measure minimizers —
the extremality side of the same pair of numbers. This entry
characterizes their roots by the superposition/juxtaposition functional
equations — the functional-equation side. Two independent literature
theorems, different audiences, no shared statements.

Prior art, stated honestly: per the 2026-09-01 sweep (Mathlib at the
pin and at master, the AFP entry index, Sequencelib, set.mm, arXiv, and
repository search), the entry is not aware of a prior formalization of
the morphic-number classification, of the plastic number, or of the
Padovan/Perrin sequences in any surveyed prover ecosystem. Mathlib's
`GoldenRatio` file (φ and its quadratic) and `Selmer` file (the
trinomial irreducibility) are consumed as infrastructure; neither
contains a morphic characterization.

Sources (full bibliography with identifiers in `formalization.yaml`):
J. Aarts, R. Fokkink, G. Kruijtzer, "Morphic numbers", Nieuw Arch.
Wisk. (5) 2 (2001) 56–58. E. S. Selmer, Math. Scand. 4 (1956) 287–302.
H. Tverberg, Math. Scand. 8 (1960) 121–126. W. Ljunggren, Math. Scand.
8 (1960) 65–70. H. van der Laan, Le Nombre Plastique, Brill, Leiden
1960. R. Padovan, Dom Hans van der Laan: Modern Primitive, Architectura
& Natura 1994. G. Kruijtzer, Ruimte en Getal, Architectura & Natura
1998.
-/

namespace MorphicNumbers

/-- **The cubic root exists.** There is a real number above 1 with
x³ = x + 1 — the existence half of the classification, so that the
compared surface carries "there EXIST only two morphic numbers" in
full: this statement supplies the root, `morphic_iff` pins every
morphic number to it or to the golden ratio, and the two witness
theorems confirm both qualify. -/
theorem plastic_exists : ∃ x : ℝ, 1 < x ∧ x ^ 3 = x + 1 := by
  sorry

/-- **The Aarts–Fokkink–Kruijtzer classification** (2001, Theorem, p. 58):
there exist only two morphic numbers — the divine proportion and the
plastic number. For every real `p`: `p` is morphic (`1 < p`, and there
are `k, l ≥ 1` with `p ^ k = p + 1` and `p − 1 = p ^ (−l)`, the latter
rendered zpow-free as `p ^ l * (p − 1) = 1`) if and only if `p` is the
golden ratio or the plastic number ρ — pinned hypothesis-style as a real
in `(1, ∞)` with `ρ³ = ρ + 1` (the unique such real; uniqueness is carried by the proof module). The forward direction is the negative
half (no third morphic number, via Selmer's theorem and the
Tverberg-instance cofactor analysis); the reverse direction carries both
witnesses. -/
theorem morphic_iff (p rho : ℝ) (hrho1 : 1 < rho) (hrho3 : rho ^ 3 = rho + 1) :
    (1 < p ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = p + 1 ∧ p ^ l * (p - 1) = 1)
      ↔ p = Real.goldenRatio ∨ p = rho := by
  sorry

/-- **The golden ratio is morphic**, with `(k, l) = (2, 1)`: both scale
properties `φ² = φ + 1` and `φ − 1 = φ⁻¹` hold. ROUTINE CONSEQUENCE of
`Real.goldenRatio_sq` (two `linear_combination`-length steps); stated as
a separate compared corollary for readability of the surface only —
never a headline. -/
theorem goldenRatio_morphic :
    1 < Real.goldenRatio ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      Real.goldenRatio ^ k = Real.goldenRatio + 1 ∧
      Real.goldenRatio ^ l * (Real.goldenRatio - 1) = 1 := by
  sorry

/-- **The plastic number is morphic**, with `(k, l) = (3, 4)`: `ρ³ = ρ + 1`
and `ρ − 1 = ρ⁻⁴`, the second witness via AFK's displayed identity
`x⁵ − x⁴ − 1 = (x³ − x − 1)(x² − x + 1)` applied at ρ. ROUTINE
CONSEQUENCE of the defining cubic (one `linear_combination` from it);
stated as a separate compared corollary for readability of the surface
only — never a headline. -/
theorem plasticNumber_morphic (rho : ℝ) (hrho1 : 1 < rho)
    (hrho3 : rho ^ 3 = rho + 1) :
    1 < rho ∧ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      rho ^ k = rho + 1 ∧ rho ^ l * (rho - 1) = 1 := by
  sorry

end MorphicNumbers
