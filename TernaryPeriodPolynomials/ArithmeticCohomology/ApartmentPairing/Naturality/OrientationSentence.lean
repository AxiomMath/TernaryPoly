module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33GeoNormalized
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Tree

@[expose] public section


/-!
# Lemma 3.3: the paper's orientation sentence and the averaged standard top-cell generator

Formalized by Claude Sonnet 5.5.

Paper: "We orient the flat and the averaged standard top-cell
generator so that their local intersection number is `+1`."  `paper_orientation_sentence` states it exactly (orientation signs of the flat and
of the generator, local intersection number `orientedIntersection`) and proves it from the geometric local data of `Geometric/GeoMain.lean`
(normal-space degree `-1` of `T₀`, cross-product constant `1`, planar degree `+1` of the flat) and the oriented cell model: `avgGenT0_eq` shows
that the average over the stabilizer of the orientation-character-weighted translates of `[T₀]` is `[T₀]`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence Finsupp
open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized
open TernaryPeriodPolynomials.Argument.Lemma33.Geometric
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical

theorem cellSign_sq (g : GeneralEisenstein.IntegralGL3) (T : Finset TernaryPeriodPolynomials.FreeResolution.Line) :
    cellSign g T * cellSign g T = 1 := by
  unfold cellSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro z _
  induction z using Sym2.ind with
  | h a b => simpa using pairSign_sq g a b

/-- **The averaged standard top-cell generator is the standard top-cell generator.**  In the oriented cell resolution (cells with the
orientation character `cellSign`, the signed permutation character of the standard cell) every element `g` of the stabilizer of the
standard top cell `T₀` acts on its generator by `g · [T₀] = cellSign g T₀ · [T₀]`; hence the average of the translates over any finite
set `S` of stabilizer elements, weighted by the orientation character, is the generator itself (for the full stabilizer, the 48 signed
permutation matrices, this is the "averaged standard top-cell generator" of the paper). -/
theorem avgGenT0_eq (S : Finset GeneralEisenstein.IntegralGL3) (hS : S.Nonempty)
    (hfix : ∀ g ∈ S, glGraded 3 g T0g = T0g) :
    (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g (single T0g (1 : ℚ)) =
      single T0g (1 : ℚ) := by
  have h : ∀ g ∈ S, cellSign g T0g.1.val • twistLin 3 g (single T0g (1 : ℚ)) = single T0g (1 : ℚ) := by
    intro g hg
    rw [twistLin_single, hfix g hg, Finsupp.smul_single, smul_eq_mul, mul_one, cellSign_sq]
  rw [Finset.sum_congr rfl h, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hS.card_pos.ne'), one_smul]

/-- The local intersection number at the identity of the flat oriented by `s` (so `s • flatClass`, `s = 1` the flat whose boundary is the
coordinate apartment) with the standard top-cell generator oriented by `r` (the generator `r • T₀`): linear in each orientation; for
`s = 1` it is the geometric local intersection number `geoLocalIntersection r = -r` (normal-space degree of `r • T₀`
against the positive normal orientation, times the cross-product constant `1`, times the positive planar degree of the flat). -/
def orientedIntersection (s r : ℚ) : ℚ := s * Geometric.geoLocalIntersection r

/-- **The paper's sentence, "We orient the flat and the averaged standard top-cell generator so that their local
intersection number is `+1`", proved in the following exact form.**

1. there are orientations (signs) of the flat and of the generator with local intersection number `+1`; the solutions are exactly the pairs
   of opposite signs (`s · r = -1`);
2. the flat's orientation is the one for which its boundary is the coordinate apartment (`δ [flat] = [apartment]`, `s = 1`), and then the
   generator is forced to be `-T₀` (`r = -1`);
3. in this normalization the diagram of Lemma 3.3 reads the top-cell coefficient literally: if `j_* c` is the class of a cellular top cycle
   `z`, then `⟨PD_∂ c, ∂a⟩ = coeff_{(-T₀)}(z)`;
4. the averaged generator is the standard generator: the orientation-character-weighted average of the translates of `[T₀]` over any finite
   set of elements fixing the standard cell (the signed permutations) is `[T₀]` (`avgGenT0_eq`).

The geometric constants (cell degree `-1`, cross-product constant `1`, planar flat degree `+1`) are the ones established in
`Geometric/GeoMain.lean`; the library's rational orientation scale `d₅` enters only as the single global factor documented there. -/
theorem paper_orientation_sentence :
    (∃ s r : ℚ, (s = 1 ∨ s = -1) ∧ (r = 1 ∨ r = -1) ∧ orientedIntersection s r = 1) ∧
    (∀ s r : ℚ, orientedIntersection s r = 1 ↔ s * r = -1) ∧
    OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
      OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass ∧
    (∀ r : ℚ, orientedIntersection 1 r = 1 ↔ r = -1) ∧
    (∀ (W : Rep.{0} ℚ principalSix) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
        (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c = cellGroupHomologyMap W 3 (cellClass W z hz) →
          flatBoundaryPairing W (PDboundaryGeo W c) = (coeffAtGen (-1) W).hom z) ∧
    (∀ (S : Finset GeneralEisenstein.IntegralGL3), S.Nonempty → (∀ g ∈ S, glGraded 3 g T0g = T0g) →
        (S.card : ℚ)⁻¹ • ∑ g ∈ S, cellSign g T0g.1.val • twistLin 3 g (single T0g (1 : ℚ)) =
          single T0g (1 : ℚ)) := by
  have hI : ∀ s r : ℚ, orientedIntersection s r = - (s * r) := fun s r => by
    unfold orientedIntersection
    rw [Geometric.geoLocalIntersection_eq]; ring
  refine ⟨⟨1, -1, Or.inl rfl, Or.inr rfl, by rw [hI]; norm_num⟩, fun s r => ?_, delta_flatClass, fun r => ?_,
    fun W c z hz h => Geometric.geoDiagram_literal_reversed W c z hz h, fun S hS hf => avgGenT0_eq S hS hf⟩
  · rw [hI]; constructor <;> intro h <;> linarith
  · rw [hI]; constructor <;> intro h <;> linarith

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
