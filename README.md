# Only two morphic numbers

Kernel-checked proof, in Lean 4 + Mathlib, of the
**Aarts–Fokkink–Kruijtzer classification** (Nieuw Archief voor
Wiskunde (5) 2 (2001) 56–58;
[open access](https://www.nieuwarchief.nl/serie5/pdf/naw5-2001-02-1-056.pdf)):
a real number `p > 1` is **morphic** if there are natural numbers
`k, l ≥ 1` with

```
p + 1 = p^k    and    p − 1 = p^(−l)
```

— the golden ratio's two scale properties, abstracted — and **there
exist only two morphic numbers**: the divine proportion `φ`
(`k, l = 2, 1`) and the plastic number `ρ`, the real root of
`x³ = x + 1` (`k, l = 3, 4`, via
`x⁵ − x⁴ − 1 = (x³ − x − 1)(x² − x + 1)`).

## The compared statements

- `morphic_iff` — THE theorem: for every real `p`, the morphic
  property (spelled inline, zpow-free) holds iff `p = Real.goldenRatio`
  or `p = ρ`, with ρ pinned hypothesis-style as a real in `(1, ∞)` with
  `ρ³ = ρ + 1`. The forward direction is the negative half; the reverse
  direction carries both witnesses.
- `goldenRatio_morphic`, `plasticNumber_morphic` — the two witnesses as
  separate compared corollaries, explicitly labeled **routine
  consequences** (readability surface, never headlines).

## The story

The plastic number was introduced by Dom Hans van der Laan (Le Nombre
Plastique, Brill 1960) as the ideal ratio for spatial objects; the same
discovery was made independently by Gérard Cordonnier (Padovan, Dom
Hans van der Laan: Modern Primitive, 1994). That `φ` and `ρ` are the
ONLY numbers with both scale properties was conjectured in Kruijtzer's
Ruimte en Getal (1998) and proved by Aarts, Fokkink, and Kruijtzer in
2001, through trinomial irreducibility: Selmer's theorem (Math. Scand.
4 (1956)) makes `X^k − X − 1` the minimal polynomial of a morphic
number, hence a divisor of `X^(l+1) − X^l − 1`; a lemma AFK derive from
Tverberg's theorem (Math. Scand. 8 (1960)) forces the cofactor to be
`1` or `X² − X + 1`; comparing coefficients pins `(k, l) = (2, 1)` or
`(3, 4)`.

**Proof-route note, stated honestly**: Selmer's theorem is consumed
from Mathlib (`Polynomial.X_pow_sub_X_sub_one_irreducible`). Where AFK
cite Tverberg's general theorem, the proof here derives the needed
instance from Mathlib's Ljunggren unit-trinomial machinery (Ljunggren,
Math. Scand. 8 (1960) 65–70 — the same lineage), and the cofactor
analysis then runs wholly in `ℤ[X]` by a divisibility argument where
the paper argues through complex zeros of modulus 1 — a simplification
with identical statement, disclosed in `formalization.yaml` together
with the two points the paper leaves implicit (the power-of-the-
quadratic point and separability), which this route discharges
explicitly.

## Prior art

Per the 2026-09-01 sweep (Mathlib at the pin and at master, the AFP
entry index, Sequencelib, set.mm, arXiv, repository search), the entry
is not aware of a prior formalization of the morphic-number
classification, of the plastic number, or of the Padovan/Perrin
sequences in any surveyed prover ecosystem. Mathlib's `GoldenRatio`
and `Selmer` files are consumed as infrastructure; neither contains a
morphic characterization.

The results address the design-mathematics community around van der
Laan's plastic number, the trinomial-irreducibility lineage of Selmer,
Tverberg, and Ljunggren, and the formalization community — the mirror dichotomy extracted here is theory Mathlib's own unit-trinomial
analysis file lists as wanted.

## Layout and build

`Challenge.lean` states the four results with placeholder proofs;
`Solution.lean` proves them by transfer from the proof module
`PdtMorphic` (definition, plastic number with cubic and uniqueness,
mirror dichotomy, the `ℤ[X]` cofactor analysis, the classification);
`comparator.json` is the machine comparison surface;
`formalization.yaml` carries sources, classification, and disclosure.

```
lake exe cache get
lake build
```

(pinned toolchain and Mathlib; a green build is the kernel
verification — the four placeholder `sorry` warnings in
`Challenge.lean` are the only expected diagnostics, and
`Solution.lean` prints the axiom audit for all four compared
theorems: `propext`, `Classical.choice`, `Quot.sound`.)

## Provenance

This repository is the complete, self-contained proof development for
this entry — nothing is imported from any parent project, and the
proof module `PdtMorphic` is native to this repository. It belongs to
the larger kernel-verified project
[stalex444/pdt-lean](https://github.com/stalex444/pdt-lean) (pinned
reference revision
[`d66ffbe`](https://github.com/stalex444/pdt-lean/tree/d66ffbe813e48636aa636ffcd80070b81cbf10da)),
which shares the plastic-number conventions. The registered sibling
entry PALOMAR-2026-08-31-000004
([stalex444/mahler-measure-minima](https://github.com/stalex444/mahler-measure-minima/tree/ca3df22))
characterizes `x² − x − 1` and `x³ − x − 1` as the degree-2 and
degree-3 Mahler-measure minimizers — the extremality side of the same
pair of numbers; this entry characterizes their roots by the
functional equations. Complementary, with no shared statements.
