module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Diagram

@[expose] public section


/-!
# Lemma 3.3 in the paper's normalization: oriented flats and their intersection functionals

Formalized by Claude Sonnet 5.5.

Paper: "We orient the flat and the averaged
standard top-cell generator so that their local intersection number is `+1`."  The orientation of the flat is a choice, so
the intersection functional `z ↦ φ(F_z)` and the bottom arrow `ω ↦ ⟨ω, ∂a_φ⟩` must be formed from the CHOSEN oriented
flat class, not from a fixed library convention.

* `groupFlatEvaluation a W`: the intersection of `H₃(Γ(6); W)` with an arbitrary relative class `a` (an oriented flat), i.e. the
  capped class paired with `a`.  For `a = flatClass` it is `groupApartmentEvaluation W`
  (`groupFlatEvaluation_flatClass`).
* `flatBoundaryPairingFor a W`: the bottom arrow `ω ↦ ⟨ω, ∂a⟩` for the oriented flat `a`.
* The normalizing scalar `normScalar = -(d5)⁻¹`.  The primary normalization (form N1) keeps the flat (so `∂a` stays the
  coordinate apartment) and rescales the standard top-cell generator; the intersection functionals of a
  rescaled flat `s • flatClass` (form N2) are linear in `s` and are used only to compare conventions.

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

noncomputable section

/-- **Intersection with an oriented flat**: `z ↦ φ_a(F_z)`, the pairing of the capped class of `z` with the relative class `a`. -/
def groupFlatEvaluation (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix) :
    groupHomology W 3 ⟶ ModuleCat.of ℚ W :=
  (SingularLocalHomology.bordifiedGroupLocalHomologyIso W 3).hom ≫ (relativeHomCapIso W).inv ≫
    homologyEvaluation upstairsRelativeChains W 2 ≫
    ModuleCat.ofHom
      { toFun := fun f => f.hom a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

/-- **The bottom arrow `ω ↦ ⟨ω, ∂a⟩`** of the diagram for the oriented flat `a`. -/
def flatBoundaryPairingFor (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix) :
    (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1 ⟶
      ModuleCat.of ℚ W :=
  homologyEvaluation SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1 ≫
    ModuleCat.ofHom
      { toFun := fun f => f.hom (upstairsRelativeSequence_shortExact.δ 2 1 rfl a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

theorem groupFlatEvaluation_apply (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix)
    (x : groupHomology W 3) :
    groupFlatEvaluation a W x =
      (homologyEvaluation upstairsRelativeChains W 2
        ((relativeHomCapIso W).inv ((SingularLocalHomology.bordifiedGroupLocalHomologyIso W 3).hom x))).hom a :=
  rfl

theorem flatBoundaryPairingFor_apply (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix)
    (ω : (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1) :
    flatBoundaryPairingFor a W ω =
      (homologyEvaluation SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W 1 ω).hom
        (upstairsRelativeSequence_shortExact.δ 2 1 rfl a) :=
  rfl

/-- The library's bottom arrow is the pairing for the library's flat class. -/
theorem flatBoundaryPairingFor_flatClass (W : Rep.{0} ℚ principalSix) :
    flatBoundaryPairingFor flatClass W = Statements.Lemma33Diagram.flatBoundaryPairing W :=
  rfl

/-- The intersection with the library's flat class is the library's top evaluator. -/
theorem groupFlatEvaluation_flatClass (W : Rep.{0} ℚ principalSix) :
    groupFlatEvaluation flatClass W = groupApartmentEvaluation W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have h := Statements.Lemma33Geometric.flat_intersection_reads_evaluation W
    ((relativeHomCapIso W).inv ((SingularLocalHomology.bordifiedGroupLocalHomologyIso W 3).hom y))
  rw [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] at h
  exact h.symm

/-- Intersection is linear in the oriented flat. -/
theorem groupFlatEvaluation_smul (s : ℚ) (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix)
    (x : groupHomology W 3) :
    groupFlatEvaluation (s • a) W x = s • groupFlatEvaluation a W x := by
  rw [groupFlatEvaluation_apply, groupFlatEvaluation_apply]
  exact map_smul _ s a

/-- The boundary pairing is linear in the oriented flat. -/
theorem flatBoundaryPairingFor_smul (s : ℚ) (a : upstairsRelativeChains.homology 2) (W : Rep.{0} ℚ principalSix)
    (ω : (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1) :
    flatBoundaryPairingFor (s • a) W ω = s • flatBoundaryPairingFor a W ω := by
  rw [flatBoundaryPairingFor_apply, flatBoundaryPairingFor_apply]
  have h : upstairsRelativeSequence_shortExact.δ 2 1 rfl (s • a) =
      s • upstairsRelativeSequence_shortExact.δ 2 1 rfl a :=
    map_smul (upstairsRelativeSequence_shortExact.δ 2 1 rfl).hom s a
  rw [h]
  exact map_smul _ s _

/-- **The normalizing scalar** `-(d₅)⁻¹`.  Rescaling the standard top-cell generator `T₀` to `normScalar • T₀`
makes its local intersection number with the flat `+1` (`Normalized/Main.lean`, `readsCoefficient_one_iff`); it is also the
unique multiple `s • flatClass` of the flat with this property (reversal/rescaling of the flat, `flat_scaling_reading`).
If the integral orientation of `M` makes `d₅ = ±1` it is the sign `∓1`; the library cannot decide `|d₅| = 1`. -/
def normScalar : ℚ := -(d5)⁻¹

end

end TernaryPeriodPolynomials.Argument.Lemma33.Normalized
