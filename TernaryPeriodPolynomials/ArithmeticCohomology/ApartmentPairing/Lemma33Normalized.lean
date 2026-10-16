module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Natural
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.CapNatural

@[expose] public section


/-!
# Lemma 3.3 (`lem:apartment-boundary-pairing`) with the paper's normalization, literally

Formalized by Claude Sonnet 5.5.

Paper: "the boundary of the flat represents the
coordinate apartment.  We orient the flat and the averaged standard top-cell generator so that their local intersection number
is `+1`.  With this normalization, the next lemma compares evaluation of a boundary class with its boundary intersection
pairing."  Lemma 3.3: the diagram `j_* ≫ (z ↦ φ(F_z)) = PD_∂ ≫ (ω ↦ ⟨ω, ∂a_φ⟩)` commutes, and
`λ(F_{j_*c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩`.

## Reading of the normalization (form N1)

The normalization is a CHOICE of orientations; it is not a numerical claim about the library's fixed conventions.  The flat is
kept (`∂ flatClass` is the coordinate apartment, `Lemma33Geometric.flat_boundary_class`), and the standard top-cell generator `T₀`
is rescaled to `r • T₀`; the coefficient of a cellular cycle against it is `coeffAtGen r`.  The local intersection number of the
flat with `r • T₀`, `localIntersection r`, is computed from local data (the normal local degree `degπ` of the chain `r • T₀` at
the identity, times the bridge constant `pairingConstant = d₅ / lamPos`), and "intersection with the flat reads the top-cell
coefficient" is the theorem `readsCoefficient_localIntersection`.  `lemma_3_3_normalized` chooses `r` with local intersection
number `+1` (unique), and then the diagram of Lemma 3.3 commutes with the right arrow equal to the top-cell coefficient (through
the cellular iso `cellGroupHomologyMap`), with no normalization hypothesis.

## Library normalization artifact (recorded, not hidden)

The sign of `r` is the paper's free choice.  Its absolute value is forced by the library: local homology of `ℝⁿ` is read in
the library's rational generator (a `LinearEquiv.ofFinrankEq`-chosen isomorphism), `d₅` is the rational degree of the integral
staircase product cell against it, and `normScalar = -(d₅)⁻¹`.  `normScalar` is a sign exactly when `d₅` is
(`integral_normalization_of_unit_degree`); that `|d₅| = 1` is NOT provable from the library.

Everything here is an EVALUATOR-WEIGHT / SCALE statement about the library's choice-normalized
rational generators: `localIntersection r` is the weight with which the top evaluator reads the coefficient against `r • T₀`; it
is NOT invariant under rescaling the five-dimensional generator, hence it is not a geometric intersection number, and
`normScalar = -(d₅)⁻¹` is a scale artifact of the library (no claim `|d₅| = 1`).  The geometric statement, in which only the sign of
`T₀` is free, is `Proofs/Lemma33/Geometric/GeoMain.lean` and `Exports/Lemma33GeoNormalized.lean`.
-/

open CategoryTheory HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SingularLocalHomology

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma33Normalized

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized
open TernaryPoly.OrdinaryTopBoundaryComparison
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

/-- **Lemma 3.3 in the paper's normalization.**  There is a unique generator scale `r` (the standard top-cell generator is
`r • T₀`) such that the flat, whose boundary is the coordinate apartment, has local intersection number `+1` with it, and for
every coefficient system `W`:

* the diagram `j_* ≫ (z ↦ φ(F_z)) = PD_∂ ≫ (ω ↦ ⟨ω, ∂a⟩)` commutes (`eq:apartment-boundary-diagram`);
* the right arrow, on every cellular top cycle `z`, is literally the coefficient of `z` against the generator;
* for every boundary class `c`, `j_* c` is the class of a cellular top cycle `z` and `⟨PD_∂ c, ∂a⟩` is its coefficient;
* `λ(F_{j_* c}(ℓ)) = ⟨PD_∂ c, ∂a⟩` for every `λ ∈ W*` (`eq:apartment-boundary-evaluation`). -/
theorem lemma_3_3_normalized :
    ∃ r : ℚ, r ≠ 0 ∧ localIntersection r = 1 ∧ ReadsCoefficient r 1 ∧
      (∀ r' : ℚ, localIntersection r' = 1 → r' = r) ∧
      (∃ κ : ℚ, FlatIntersectionBridge κ ∧ r * (κ * LocalDegree.dT0) = 1) ∧
      OrdinaryTopBoundaryComparison.upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
        OrdinaryTopBoundaryComparison.identityApartmentBoundaryClass ∧
      ∀ W : Rep.{0} ℚ principalSix,
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupApartmentEvaluation W =
          PDboundary W ≫ flatBoundaryPairing W ∧
        (∀ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
          groupApartmentEvaluation W (cellGroupHomologyMap W 3 (cellClass W z hz)) = (coeffAtGen r W).hom z) ∧
        (∀ c : (SingularLocalHomology.boundaryLocalChains W).homology 3,
          ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
            SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
                cellGroupHomologyMap W 3 (cellClass W z hz) ∧
              flatBoundaryPairing W (PDboundary W c) = (coeffAtGen r W).hom z) ∧
        (∀ (lam : W →ₗ[ℚ] ℚ) (c : (SingularLocalHomology.boundaryLocalChains W).homology 3),
          lam (groupApartmentEvaluation W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c)) =
            lam (flatBoundaryPairing W (PDboundary W c))) :=
  ⟨normScalar, normScalar_ne_zero, localIntersection_normScalar, (readsCoefficient_one_iff _).mpr rfl,
    fun r' h => (localIntersection_eq_one_iff r').mp h,
    ⟨pairingConstant, flatIntersectionBridge_pairingConstant,
      by rw [pairingConstant_mul_dT0, normScalar_mul_neg_d5]⟩, delta_flatClass,
    fun W => ⟨Statements.Lemma33Diagram.diagram_commutes W, eval_eq_coeffAtT0Norm W,
      diagram_literal_exists W, Statements.Lemma33Diagram.evaluation_apply W⟩⟩

/-- The normalized generator's coefficient is `(-d₅)` times the library's coefficient at `T₀`. -/
theorem normalized_coefficient (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    (coeffAtGen normScalar W).hom z = (-d5) • (coeffAtT0 W).hom z :=
  coeffAtT0Norm_apply W z

/-- The library's own generator `T₀` has evaluator weight `-d₅` (a choice-normalized rational; not a geometric intersection number). -/
theorem library_local_intersection : localIntersection 1 = -d5 := by
  rw [localIntersection_eq, one_mul]

/-- `normScalar` is a sign exactly when `d₅` is: a unit degree (the integral normalization of the local generator) makes the
normalizing rescaling an orientation reversal. -/
theorem integral_normalization_of_unit_degree (h : d5 = 1 ∨ d5 = -1) : normScalar = -1 ∨ normScalar = 1 := by
  unfold normScalar
  rcases h with h | h
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

/-- **Scale artifact, conditional on `d₅ = 1`** (a hypothesis the library cannot discharge; for the geometric version see
`Statements.Lemma33GeoNormalized`).  In the orientation of `M` with `d₅ = 1`, the
library's generator `T₀` has local intersection number `-1` with the flat, not `+1`; the reversed generator `(-1) • T₀` (the
sign choice of the paper) has `+1`, and reversing the flat instead gives the same reading.  -/
theorem library_sign_difference (hd : d5 = 1) :
    localIntersection 1 = -1 ∧ ReadsCoefficient 1 (-1) ∧ ¬ ReadsCoefficient 1 1 ∧
      localIntersection (-1) = 1 ∧ ReadsCoefficient (-1) 1 ∧ normScalar = -1 ∧
      ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
        groupFlatEvaluation ((-1 : ℚ) • flatClass) W (cellGroupHomologyMap W 3 (cellClass W z hz)) =
          (coeffAtT0 W).hom z := by
  have hs : normScalar = -1 := by
    unfold normScalar
    rw [hd]
    norm_num
  have h1 : localIntersection 1 = -1 := by rw [library_local_intersection, hd]
  have h2 : localIntersection (-1) = 1 := by
    rw [localIntersection_eq, hd]
    norm_num
  refine ⟨h1, ?_, ?_, h2, ?_, hs, ?_⟩
  · rw [← h1]
    exact readsCoefficient_localIntersection one_ne_zero
  · intro h
    rw [readsCoefficient_iff_localIntersection one_ne_zero, h1] at h
    norm_num at h
  · have := readsCoefficient_localIntersection (r := -1) (by norm_num)
    rwa [h2] at this
  · intro W z hz
    rw [flat_scaling_reading one_ne_zero (-1) W z hz, library_local_intersection, hd, coeffAtGen_apply]
    norm_num

/-- **`eq:apartment-boundary-evaluation` for the induced coefficient system** `M = restrictedCoefficients n e` (the
level-six restriction of the full residue-covector system `E_{n,e}`) and any functional `λ` of it, e.g.
`φ_λ(F) = λ(F(ℓ))`: `λ(F_{j_* c}(ℓ)) = ⟨PD_∂ c, ∂a_{φ_λ}⟩`, and on cellular top cycles the evaluator is the coefficient against
the normalized generator.  (Passage to a finite-index subgroup: `Statements.AppendixLemmas.apartment_boundary_transfer`.) -/
theorem lemma_3_3_normalized_induced (n : ℕ) (e : ℤ)
    (lam : SymmetricSpaceBoundaryFull.restrictedCoefficients n e →ₗ[ℚ] ℚ)
    (c : (SingularLocalHomology.boundaryLocalChains (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)).homology 3) :
    lam (groupApartmentEvaluation (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)
        (SymmetricSpaceBoundaryDuality.boundaryToGroup (SymmetricSpaceBoundaryFull.restrictedCoefficients n e) 3 c)) =
      lam (flatBoundaryPairing (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)
        (PDboundary (SymmetricSpaceBoundaryFull.restrictedCoefficients n e) c)) ∧
    ∀ (z : (cellCoinv (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)).X 3)
      (hz : ((cellCoinv (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)).d 3 2).hom z = 0),
      groupApartmentEvaluation (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)
          (cellGroupHomologyMap (SymmetricSpaceBoundaryFull.restrictedCoefficients n e) 3
            (cellClass (SymmetricSpaceBoundaryFull.restrictedCoefficients n e) z hz)) =
        (coeffAtGen normScalar (SymmetricSpaceBoundaryFull.restrictedCoefficients n e)).hom z :=
  ⟨Statements.Lemma33Diagram.evaluation_apply _ lam c, eval_eq_coeffAtT0Norm _⟩

/-- **Naturality of the diagram in the coefficient system** (compatibility with change of coefficients, in particular with
induction): for every morphism `φ : V ⟶ W` of `Γ(6)`-coefficients, the maps `j_*`, the top evaluator, boundary Poincaré
duality `PD_∂`, the bottom arrow and the composite `c ↦ ⟨PD_∂ c, ∂a⟩` all commute with `φ`. -/
theorem diagram_natural {V W : Rep.{0} ℚ principalSix} (φ : V ⟶ W) :
    (homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 ≫
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 =
      SymmetricSpaceBoundaryDuality.boundaryToGroup V 3 ≫ groupHomology.map (MonoidHom.id _) φ 3) ∧
    (∀ x : groupHomology V 3, groupApartmentEvaluation W ((groupHomology.map (MonoidHom.id principalSix) φ 3).hom x) =
      φ.hom (groupApartmentEvaluation V x)) ∧
    (∀ ω, flatBoundaryPairing W
        (homologyMap (TernaryPeriodPolynomials.Argument.CoefficientNaturality.coefHomPost
          SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1 ω) = φ.hom (flatBoundaryPairing V ω)) ∧
    (∀ c : (SingularLocalHomology.boundaryLocalChains V).homology 3,
      flatBoundaryPairing W
        (PDboundary W ((homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3).hom c)) =
      φ.hom (flatBoundaryPairing V (PDboundary V c))) ∧
    (homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 ≫ PDboundary W =
      PDboundary V ≫ homologyMap (TernaryPeriodPolynomials.Argument.CoefficientNaturality.coefHomPost
        SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1) :=
  ⟨boundaryToGroup_natural φ, groupApartmentEvaluation_natural φ, flatBoundaryPairing_natural φ, pairing_natural φ,
    PDboundary_natural φ⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma33Normalized
