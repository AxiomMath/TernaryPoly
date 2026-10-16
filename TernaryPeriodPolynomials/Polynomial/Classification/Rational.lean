module

public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates.Defs
public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates.Sectors
public import TernaryPeriodPolynomials.Polynomial.Reduction
public import TernaryPeriodPolynomials.SymmetricSolution.BernoulliTodd
public import TernaryPeriodPolynomials.ArithmeticCohomology.SupportTheorem
public import TernaryPeriodPolynomials.SymmetricSolution.ObstructionVanishing
public import TernaryPeriodPolynomials.AlternatingSolution.OddDegreeVanishing
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.AlternatingBridge

@[expose] public section



/-!
# The pairwise decomposition over `ℚ`

A rational solution of the cyclic and three-term relations is a sum of polynomials in two of the
variables (`rational_pairwise`). By the sector splitting of `TernaryPoly.Reduction` it suffices to
treat the symmetric and the alternating homogeneous sectors: the symmetric scalar obstruction
vanishes by Proposition 4.2 (`symmetric_obstruction_vanishes`, through the boundary comparison of
Appendix C), and odd-degree alternating solutions vanish by Theorem 5.2
(`alternating_odd_degree_solution_eq_zero`).
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.Classification

/-- The symmetric scalar obstruction vanishes on every rational symmetric homogeneous solution
(from Proposition 4.2, `symmetric_obstruction_vanishes`). -/
theorem scalar_zero : TernaryPoly.ScalarGates.ScalarZero := by
  intro n f hn hf hrel hs
  have hj := TernaryPeriodPolynomials.symmetric_obstruction_vanishes n hn
    (⟨MvPolynomial.map (algebraMap ℚ ℂ) f, hf.map (algebraMap ℚ ℂ)⟩ :
      GeneralEisenstein.HomogeneousPoly n)
    (TernaryPeriodPolynomials.mapped_symmetricSolution hf hrel hs)
  have hmap : MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.symmetricTodd f) = 0 :=
    (TernaryPeriodPolynomials.map_symmetricTodd hf).trans hj
  have hz : TernaryPoly.symmetricTodd f = 0 :=
    MvPolynomial.map_injective (algebraMap ℚ ℂ)
      (FaithfulSMul.algebraMap_injective ℚ ℂ) (hmap.trans (map_zero _).symm)
  simp only [TernaryPoly.symmetricScalar, hz, map_zero, Polynomial.coeff_zero]

/-- The ordinary-sector reference pairwise fact (`support_principle`). -/
theorem hordinary : TernaryPoly.ScalarGates.SectorReferencePairwise :=
  TernaryPoly.ScalarGates.sectorReferencePairwise_of_ordinary
    TernaryPeriodPolynomials.support_principle

/-- Odd-degree alternating sector: `C f = f`, `S f = -f` makes `f` fully alternating
(`TernaryPeriodPolynomials.Argument.ModFourMain.isAlternating_iff`), and the new route's
`alternating_odd_degree_solution_eq_zero` kills every odd-degree alternating solution outright, so it is in
particular `Pairwise`. -/
theorem odd_alternating_pairwise {n : ℕ} {f : TernaryPoly.TernaryPolynomial}
    (ho : Odd n) (hf : f.IsHomogeneous n) (hrel : TernaryPoly.PeriodRelations f)
    (hs : TernaryPoly.S f = -f) : TernaryPoly.Pairwise f := by
  have halt : TernaryPeriodPolynomials.Argument.IsAlternating f :=
    (TernaryPeriodPolynomials.Argument.ModFourMain.isAlternating_iff f).mpr ⟨hrel.1, hs⟩
  have hN : TernaryPeriodPolynomials.Argument.threeTermNorm f = 0 := hrel.2
  have hz : f = 0 :=
    TernaryPeriodPolynomials.alternating_odd_degree_solution_eq_zero f hf ho halt hN
  simpa only [hz] using TernaryPoly.pairwise_zero

/-- Full alternating sector (`S f = -f`), any positive degree: even case via
`TernaryPoly.ScalarGates.even_alternating_pairwise` (ordinary route only), odd case via
`odd_alternating_pairwise`. -/
theorem alternating_pairwise {n : ℕ} {f : TernaryPoly.TernaryPolynomial} (hn : 0 < n)
    (hf : f.IsHomogeneous n) (hrel : TernaryPoly.PeriodRelations f)
    (hs : TernaryPoly.S f = -f) : TernaryPoly.Pairwise f := by
  rcases Nat.even_or_odd n with he | ho
  · exact TernaryPoly.ScalarGates.even_alternating_pairwise hordinary hn he hf hrel hs
  · exact odd_alternating_pairwise ho hf hrel hs

/-- The full `ℚ`-level pairwise decomposition: replaces
`TernaryPoly.Paper.OriginalSupportBridge.rational_solution_pairwise`. -/
theorem rational_pairwise {f : TernaryPoly.TernaryPolynomial}
    (hf : TernaryPoly.PeriodRelations f) : TernaryPoly.Pairwise f :=
  TernaryPoly.pairwise_of_positive_homogeneous_sectors
    (fun _n _f hn hf hrel hs =>
      TernaryPoly.ScalarGates.symmetric_pairwise scalar_zero hordinary hn hf
        hrel hs)
    (fun _n _f hn hf hrel hs => alternating_pairwise hn hf hrel hs) hf

end TernaryPeriodPolynomials.Argument.Classification
