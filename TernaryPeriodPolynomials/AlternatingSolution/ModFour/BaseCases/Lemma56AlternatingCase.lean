module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.JPieceAlt
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.JPieceAltEval
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LiftIndependence
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases10
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases11
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases12
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22c
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22d
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd1
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd5
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd6
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.POdd7
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd0
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd1
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd2
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd3
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd4
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd5
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd6
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QOdd7

@[expose] public section



/-!
Alternating-case assembly for `modFour_beta_triangular`'s second conjunct: given `r : Fin 8 → Poly2` and any
alternating integral lift `v` of `expandOdd r` with half-norm `g`, shows
`piOperator (reduceTwo g) = expandOdd r + expandOdd (uOperator r)`.

Mirrors `Lemma56SymmetricCase.lean` exactly: eight `jpiece_alt_j (r j)` witnesses (in place of
`jpiece_j`), folded via `lemma_5_5_clause3`, with alternating-ness combined via `isAlternating_add`
(in place of `IsSymmetric.add`) and transported via `lemma_5_5_clause2`'s `Or.inr` branch (in
place of `Or.inl`).

The only *mathematical* difference from the symmetric case: each `jpiece_alt_j (r j)`'s
closed-form `piOperator`-value carries an extra leading `evalR0 (r j) * oddGenerator j` term,
traced to the `WD j` contribution baked into `baseAlt_zero_half_pi` (see `JPieceAltEval.lean`'s
docstring). Summed over `j`, these assemble uniformly into the extra `expandOdd r` summand that
is absent from the symmetric case's conclusion. The remaining `delta_p`/`delta_q` part of each
piece is *identical in shape* to the symmetric case (same `jpiece_sym`/`jpiece_alt` machinery,
symmetry-agnostic) and assembles into `expandOdd (uOperator r)` by the same closing
`simp [uOperator, ...]; ring` step, including the same `j = 4 ↝ 3` cross term absorbed into
`uOperator`'s own definition.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem evalR0_X2' : evalR0 (X 2) = d7 ^ 2 := by
  show bind₁ ![d4, d6, d7 ^ 2] (X 2) = d7 ^ 2
  simp

theorem lemma_5_6_alternating_case (r : Fin 8 → MvPolynomial (Fin 3) (ZMod 2))
    (v g : MvPolynomial (Fin 3) ℤ)
    (hred : reduceTwo v = expandOdd r) (hg : threeTermNorm v = C 2 * g)
    (halt : IsAlternating v) :
    piOperator (reduceTwo g) = expandOdd r + expandOdd (uOperator r) := by
  obtain ⟨v0, g0, hv0alt, hv0red, hv0g, hv0pi⟩ := jpiece_alt_0 (r 0)
  obtain ⟨v1, g1, hv1alt, hv1red, hv1g, hv1pi⟩ := jpiece_alt_1 (r 1)
  obtain ⟨v2, g2, hv2alt, hv2red, hv2g, hv2pi⟩ := jpiece_alt_2 (r 2)
  obtain ⟨v3, g3, hv3alt, hv3red, hv3g, hv3pi⟩ := jpiece_alt_3 (r 3)
  obtain ⟨v4, g4, hv4alt, hv4red, hv4g, hv4pi⟩ := jpiece_alt_4 (r 4)
  obtain ⟨v5, g5, hv5alt, hv5red, hv5g, hv5pi⟩ := jpiece_alt_5 (r 5)
  obtain ⟨v6, g6, hv6alt, hv6red, hv6g, hv6pi⟩ := jpiece_alt_6 (r 6)
  obtain ⟨v7, g7, hv7alt, hv7red, hv7g, hv7pi⟩ := jpiece_alt_7 (r 7)
  have h01 := lemma_5_5_clause3 _ _ _ _ hv0g hv1g
  have h012 := lemma_5_5_clause3 _ _ _ _ h01.1 hv2g
  have h0123 := lemma_5_5_clause3 _ _ _ _ h012.1 hv3g
  have h01234 := lemma_5_5_clause3 _ _ _ _ h0123.1 hv4g
  have h012345 := lemma_5_5_clause3 _ _ _ _ h01234.1 hv5g
  have h0123456 := lemma_5_5_clause3 _ _ _ _ h012345.1 hv6g
  have h01234567 := lemma_5_5_clause3 _ _ _ _ h0123456.1 hv7g
  have hvstar_alt : IsAlternating (v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7) :=
    isAlternating_add
      (isAlternating_add
        (isAlternating_add
          (isAlternating_add
            (isAlternating_add
              (isAlternating_add
                (isAlternating_add hv0alt hv1alt) hv2alt) hv3alt) hv4alt) hv5alt) hv6alt) hv7alt
  have hvstar_red : reduceTwo (v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7) = expandOdd r := by
    show reduceTwo (v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7) = ∑ j, evalR0 (r j) * oddGenerator j
    rw [Fin.sum_univ_eight]
    simp only [map_add, hv0red, hv1red, hv2red, hv3red, hv4red, hv5red, hv6red, hv7red]
  have htransport := lemma_5_5_clause2 v (v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7) g
    (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7) (Or.inr ⟨halt, hvstar_alt⟩)
    (hred.trans hvstar_red.symm) hg h01234567.1
  rw [htransport, h01234567.2, h0123456.2, h012345.2, h01234.2, h0123.2, h012.2, h01.2,
    hv0pi, hv1pi, hv2pi, hv3pi, hv4pi, hv5pi, hv6pi, hv7pi]
  show _ = (∑ j, evalR0 (r j) * oddGenerator j) + ∑ j, evalR0 (uOperator r j) * oddGenerator j
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp [uOperator, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four,
    map_add, map_mul, map_zero, evalR0_X2', zero_mul,
    delta_p_odd0_eq_probe, delta_p_odd1_eq_probe, delta_p_odd2_eq_probe, delta_p_odd3_eq_probe,
    delta_p_odd4_eq_probe, delta_p_odd5_eq_probe, delta_p_odd6_eq_probe, delta_p_odd7_eq_probe,
    delta_q_odd0_eq_probe, delta_q_odd1_eq_probe, delta_q_odd2_eq_probe, delta_q_odd3_eq_probe,
    delta_q_odd4_eq_probe, delta_q_odd5_eq_probe, delta_q_odd6_eq_probe, delta_q_odd7_eq_probe]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
