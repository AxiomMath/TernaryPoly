module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.StabCd
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ProdVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CornerEval

@[expose] public section


/-!
# The 4-cocycles of the line and plane complexes of `Γ(6)` are coboundaries (`H⁴ = 0`)

Formalized by Claude Sonnet 5.5.

The cup product `z ∪ z'` of two line (plane) 2-cocycles is a 4-cocycle of the complex of the labels `Line` (`Plane`) of `Γ(6)` with trivial coefficients, and its
cohomology class lives in `∏_{orbits} H⁴(Stab ℓ; ℚ) = 0` (`cdLe_three_stab_line`), so it has a primitive `γ`
(`exists_line_primitive`, `exists_plane_primitive`): the hypothesis of the corner evaluation `LineDatum.conePair_eq_corner`.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- A 4-cocycle of the permutation complex of a set of labels whose stabilizers have cohomological dimension `≤ 3` is a coboundary. -/
theorem exists_primitive_of_cdLe {Z : Type} [MulAction Γ6 Z]
    (hcd : ∀ z : Z, CdLe ℚ ↥(MulAction.stabilizer Γ6 z) 3)
    (ψ : (prodComplex Γ6 RationalGL3 Z).X 4 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hψ : (prodComplex Γ6 RationalGL3 Z).d 5 4 ≫ ψ = 0) :
    ∃ γ : (prodComplex Γ6 RationalGL3 Z).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      (prodComplex Γ6 RationalGL3 Z).d 4 3 ≫ γ = ψ := by
  have hz : IsZero ((homCochains (prodComplex Γ6 RationalGL3 Z) (𝟙_ (Rep.{0} ℚ Γ6))).homology 4) :=
    isZero_homCochains_prod (Γ := Γ6) (V := RationalGL3) (Z := Z) (1 : RationalGL3) vertexAction_free' _ 4
      (fun o => hcd o.out ℚ 4 (by norm_num))
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ 4).2 hz
  rw [HomologicalComplex.exactAt_iff' _ 3 4 5 (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel 3 4 from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 4 5 from rfl)), ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨γ, hγ⟩ := hex ψ hψ
  exact ⟨γ, hγ⟩

/-- **Every line 4-cocycle is a coboundary.** -/
theorem exists_line_primitive
    (ψ : (prodComplex Γ6 RationalGL3 Line).X 4 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hψ : (prodComplex Γ6 RationalGL3 Line).d 5 4 ≫ ψ = 0) :
    ∃ γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ = ψ :=
  exists_primitive_of_cdLe (fun ℓ => cdLe_three_stab_line ℓ) ψ hψ

/-- **Every plane 4-cocycle is a coboundary.** -/
theorem exists_plane_primitive
    (ψ : (prodComplex Γ6 RationalGL3 Plane).X 4 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hψ : (prodComplex Γ6 RationalGL3 Plane).d 5 4 ≫ ψ = 0) :
    ∃ γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ = ψ :=
  exists_primitive_of_cdLe (fun P => cdLe_three_stab_plane P) ψ hψ

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
