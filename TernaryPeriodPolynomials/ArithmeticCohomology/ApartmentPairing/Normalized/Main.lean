module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.LocalDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.EvaluatorNonzero

@[expose] public section


/-!
# Lemma 3.3 in the paper's normalization (form N1): the normalized top-cell generator

Formalized by Claude Sonnet 5.5.

Paper: "the boundary of the flat represents the coordinate apartment.  We orient the flat and the averaged
standard top-cell generator so that their local intersection number is `+1`."  The flat is kept (so `∂a` is the coordinate
apartment, `delta_flatClass`) and the standard top-cell generator `T₀` is rescaled to `r • T₀`; the coefficient of a cellular
cycle against the generator `r • T₀` is `r⁻¹ • coeffAtT0` (`coeffAtGen`).

* The **local intersection number** of the flat with the generator `r • T₀` is computed from local data
  (`localIntersection r = pairingConstant * localDegreeGen r`): the three-dimensional normal local degree `degπ` of the chain
  `r • T₀` at the identity (`localDegreeGen_eq : = r * dT0`, the flat meets `T₀` at the identity
  transversally) times `pairingConstant = d₅ / lamPos`, the constant of the global bridge converting the sum of local degrees
  into the Poincaré--Lefschetz pairing with the flat.  Only the product is independent of the choice of the generator of local
  homology (rescaling it by `ρ` multiplies `dT0` by `ρ⁻¹` and `pairingConstant` by `ρ`).
* `ReadsCoefficient r n`: "intersection with the flat reads the top-cell coefficient": the top evaluator of every cellular top
  cycle is `n` times its coefficient against `r • T₀`.  `readsCoefficient_localIntersection` PROVES that the number `n` is the
  local intersection number (from the bridge and the local degree), `readsCoefficient_iff` that it is unique.
* The normalized generator has scale `normScalar = -(d₅)⁻¹`: `localIntersection r = 1 ↔ r = normScalar`
  (`localIntersection_eq_one_iff`), and then the diagram of Lemma 3.3 reads the coefficient LITERALLY
  (`diagram_literal`).

Everything here is an EVALUATOR-WEIGHT / SCALE statement about the library's choice-normalized
rational generators: `localIntersection r` is the weight with which the top evaluator reads the coefficient against `r • T₀`; it
is NOT invariant under rescaling the five-dimensional generator, hence it is not a geometric intersection number, and
`normScalar = -(d₅)⁻¹` is a scale artifact of the library (no claim `|d₅| = 1`).  The geometric statement, in which only the sign of
`T₀` is free, is `Proofs/Lemma33/Geometric/GeoMain.lean` and `Exports/Lemma33GeoNormalized.lean`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction

namespace TernaryPeriodPolynomials.Argument.Lemma33.Normalized

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPoly.OrdinaryTopBoundaryComparison
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section

/-- The coefficient of a cellular top chain against the rescaled generator `r • T₀`. -/
def coeffAtGen (r : ℚ) (W : Rep.{0} ℚ principalSix) : (cellCoinv W).X 3 ⟶ ModuleCat.of ℚ W :=
  r⁻¹ • coeffAtT0 W

theorem coeffAtGen_apply (r : ℚ) (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    (coeffAtGen r W).hom z = r⁻¹ • (coeffAtT0 W).hom z := rfl

/-- The coefficient against the normalized generator `normScalar • T₀`. -/
def coeffAtT0Norm (W : Rep.{0} ℚ principalSix) : (cellCoinv W).X 3 ⟶ ModuleCat.of ℚ W :=
  coeffAtGen normScalar W

theorem d5_ne_zero' : d5 ≠ 0 := by
  obtain ⟨-, -, -, -, -, hd, -⟩ := Statements.Lemma33Geometric.apartment_constant_values
  exact hd

theorem normScalar_ne_zero : normScalar ≠ 0 := by
  have := d5_ne_zero'
  unfold normScalar
  simpa using this

theorem normScalar_mul_neg_d5 : normScalar * (-d5) = 1 := by
  have := d5_ne_zero'
  unfold normScalar
  field_simp

theorem normScalar_inv : normScalar⁻¹ = -d5 := by
  unfold normScalar
  rw [inv_neg, inv_inv]

theorem coeffAtT0Norm_apply (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    (coeffAtT0Norm W).hom z = (-d5) • (coeffAtT0 W).hom z := by
  unfold coeffAtT0Norm
  rw [coeffAtGen_apply, normScalar_inv]

/-- **Intersection with the flat reads the top-cell coefficient** against the generator `r • T₀` with weight `n`: the
top evaluator of the class of every cellular top cycle is `n` times its coefficient against `r • T₀`. -/
def ReadsCoefficient (r n : ℚ) : Prop :=
  ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
    groupApartmentEvaluation W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      n • (coeffAtGen r W).hom z

/-- Some cellular top cycle (for the coefficient system `ordinaryCyclesRep`) has non-zero top-cell coefficient. -/
theorem exists_coeff_ne_zero :
    ∃ (z : (cellCoinv SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).X 3)
      (_ : ((cellCoinv SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).d 3 2).hom z = 0),
      (coeffAtT0 SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).hom z ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ (z : (cellCoinv SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).X 3)
      (_ : ((cellCoinv SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).d 3 2).hom z = 0),
      (coeffAtT0 SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep).hom z = 0 := by
    intro z hz
    by_contra hne
    exact hcon ⟨z, hz, hne⟩
  apply groupApartmentEvaluation_ne_zero
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := cellGroupHomologyMap_surjective _ x
  obtain ⟨z, hz, rfl⟩ := exists_cellClass _ y
  rw [Statements.Lemma33Geometric.apartment_evaluation_eq_neg_d5_coefficient _ z hz, hcon' z hz, smul_zero]
  rfl

/-- **Characterization of the weights**: the top evaluator reads the coefficient against `r • T₀` with weight `n` iff
`-d₅ = n r⁻¹`.  In particular the weight is unique. -/
theorem readsCoefficient_iff (r n : ℚ) : ReadsCoefficient r n ↔ -d5 = n * r⁻¹ := by
  constructor
  · intro h
    obtain ⟨z, hz, hne⟩ := exists_coeff_ne_zero
    have e := h _ z hz
    rw [Statements.Lemma33Geometric.apartment_evaluation_eq_neg_d5_coefficient _ z hz, coeffAtGen_apply,
      smul_smul] at e
    exact smul_left_injective ℚ hne e
  · intro h W z hz
    rw [Statements.Lemma33Geometric.apartment_evaluation_eq_neg_d5_coefficient W z hz, coeffAtGen_apply,
      smul_smul, h]

theorem readsCoefficient_unique {r n n' : ℚ} (h : ReadsCoefficient r n) (h' : ReadsCoefficient r n') (hr : r ≠ 0) :
    n = n' := by
  rw [readsCoefficient_iff] at h h'
  have := h.symm.trans h'
  exact mul_right_cancel₀ (inv_ne_zero hr) this

/-! ### The local intersection number computed from the local data -/

/-- The constant `d₅ / lamPos` of the global bridge: pairing = `pairingConstant` × (sum of local degrees). -/
def pairingConstant : ℚ := d5 / Orient.lamPos

theorem pairingConstant_spec : FlatIntersectionBridge pairingConstant ∧ pairingConstant * LocalDegree.dT0 = -d5 := by
  obtain ⟨κ, -, hB, hκ, hneg, -, hl, -⟩ := Statements.Lemma33Geometric.apartment_constant_values
  have : κ = pairingConstant := by
    unfold pairingConstant
    field_simp
    exact hκ
  exact ⟨this ▸ hB, this ▸ hneg⟩

theorem flatIntersectionBridge_pairingConstant : FlatIntersectionBridge pairingConstant :=
  pairingConstant_spec.1

theorem pairingConstant_mul_dT0 : pairingConstant * LocalDegree.dT0 = -d5 :=
  pairingConstant_spec.2

/-- **The evaluator weight of the flat against the top-cell generator `r • T₀`** (named `localIntersection` historically; a scale
statement, not a geometric intersection number), computed from the local data: the
pairing constant times the normal local degree at the identity of the chain `r • T₀`. -/
def localIntersection (r : ℚ) : ℚ := pairingConstant * localDegreeGen r

theorem localIntersection_eq (r : ℚ) : localIntersection r = r * (-d5) := by
  unfold localIntersection
  rw [localDegreeGen_eq, ← pairingConstant_mul_dT0]
  ring

/-- **Intersection with the flat reads the top-cell coefficient**, proved from the bridge and the local
degree: for a non-zero generator scale `r`, the weight is exactly the local intersection number. -/
theorem readsCoefficient_localIntersection {r : ℚ} (hr : r ≠ 0) : ReadsCoefficient r (localIntersection r) := by
  rw [readsCoefficient_iff, localIntersection_eq]
  field_simp

/-- The weights in `ReadsCoefficient r n` are exactly the local intersection numbers. -/
theorem readsCoefficient_iff_localIntersection {r : ℚ} (hr : r ≠ 0) (n : ℚ) :
    ReadsCoefficient r n ↔ n = localIntersection r :=
  ⟨fun h => readsCoefficient_unique h (readsCoefficient_localIntersection hr) hr,
    fun h => h ▸ readsCoefficient_localIntersection hr⟩

/-- **The normalization**: the generator scale `r` has local intersection number `+1` with the flat iff `r = normScalar`. -/
theorem localIntersection_eq_one_iff (r : ℚ) : localIntersection r = 1 ↔ r = normScalar := by
  rw [localIntersection_eq]
  have := d5_ne_zero'
  unfold normScalar
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

theorem localIntersection_normScalar : localIntersection normScalar = 1 :=
  (localIntersection_eq_one_iff _).mpr rfl

/-- Reading with weight `+1` characterizes the normalized generator. -/
theorem readsCoefficient_one_iff (r : ℚ) : ReadsCoefficient r 1 ↔ r = normScalar := by
  rw [readsCoefficient_iff]
  have := d5_ne_zero'
  unfold normScalar
  constructor
  · intro h
    have hr : r ≠ 0 := by
      rintro rfl
      simp at h
      exact this h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    simp

/-- **With the normalized generator the top evaluator is literally the top-cell coefficient.** -/
theorem eval_eq_coeffAtT0Norm (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    groupApartmentEvaluation W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = (coeffAtT0Norm W).hom z := by
  have h := (readsCoefficient_one_iff normScalar).mpr rfl W z hz
  rw [one_smul] at h
  exact h

/-! ### The diagram -/

/-- **The literal diagram**: if `j_* c` is the class of the cellular top cycle `z`, then `⟨PD_∂ c, ∂a⟩ = coeff_{T₀'} z`,
the coefficient against the normalized generator, with NO normalization hypothesis. -/
theorem diagram_literal (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3)
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (h : SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
      cellGroupHomologyMap W 3 (cellClass W z hz)) :
    flatBoundaryPairing W (PDboundary W c) = (coeffAtT0Norm W).hom z := by
  rw [← Statements.Lemma33Diagram.diagram_apply, h]
  exact eval_eq_coeffAtT0Norm W z hz

/-- Every boundary class `c` has a cellular top cycle `z` with `j_* c = [z]` and `⟨PD_∂ c, ∂a⟩ = coeff_{T₀'} z`. -/
theorem diagram_literal_exists (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    ∃ (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
      SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c =
          cellGroupHomologyMap W 3 (cellClass W z hz) ∧
        flatBoundaryPairing W (PDboundary W c) = (coeffAtT0Norm W).hom z := by
  obtain ⟨y, hy⟩ := cellGroupHomologyMap_surjective W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c)
  obtain ⟨z, hz, rfl⟩ := exists_cellClass W y
  exact ⟨z, hz, hy.symm, diagram_literal W c z hz hy.symm⟩

/-! ### Rescaling or reversing the flat instead of the generator (form N2) -/

/-- Rescaling the flat by `s` rescales the weight: `s • flatClass` reads the coefficient against `r • T₀` with weight
`s * localIntersection r`. -/
theorem flat_scaling_reading {r : ℚ} (hr : r ≠ 0) (s : ℚ) (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0) :
    groupFlatEvaluation (s • flatClass) W ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      (s * localIntersection r) • (coeffAtGen r W).hom z := by
  rw [groupFlatEvaluation_smul, groupFlatEvaluation_flatClass, readsCoefficient_localIntersection hr W z hz,
    smul_smul]

/-- The diagram for any multiple of the flat commutes (linearity in the flat). -/
theorem diagram_commutes_smul (s : ℚ) (W : Rep.{0} ℚ principalSix) :
    SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 ≫ groupFlatEvaluation (s • flatClass) W =
      PDboundary W ≫ flatBoundaryPairingFor (s • flatClass) W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change groupFlatEvaluation (s • flatClass) W (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 c) =
    flatBoundaryPairingFor (s • flatClass) W (PDboundary W c)
  rw [groupFlatEvaluation_smul, flatBoundaryPairingFor_smul, groupFlatEvaluation_flatClass]
  congr 1
  exact Statements.Lemma33Diagram.diagram_apply W c

end

end TernaryPeriodPolynomials.Argument.Lemma33.Normalized
