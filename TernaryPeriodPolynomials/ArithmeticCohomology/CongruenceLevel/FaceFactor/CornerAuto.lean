module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupCocycle

@[expose] public section


/-!
# Corner evaluation of the cone pairing of two line (plane) data, with the primitive supplied by `H⁴ = 0`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, Lemma C.2.

`LineDatum.conePair_exists_corner`, `PlaneDatum.conePair_exists_corner`: for ARBITRARY coefficient modules `W, W'` of `Γ(6)`, every pairing `π` and every coinvariant cycle `v` of the
cone, there is a primitive `γ` of the cup product `z ∪ z'` (it exists because the line and plane groups of `Γ(6)` have cohomological dimension `≤ 3`) such that the
cone pairing of the two lifts is the evaluation on the corner chain `pA 3 v` of the flag 3-cochain `w ∪ (z'|flags) - γ|flags` (resp. its plane analogue).
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

theorem LineDatum.conePair_exists_corner (d : LineDatum W) (e : LineDatum W') (hv : IsCoinvCycle v) :
    ∃ γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
        (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π ∧
      conePair π v d.cone e.cone =
        (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) ≫ π) -
          flagLineHom.hom.f 3 ≫ γ).hom ((modelPush.pA 3).hom v) := by
  obtain ⟨γ, hγ⟩ := exists_line_primitive ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (cup_cocycle (nerveDiagSystem Γ6 RationalGL3 Line) d.z d.hz e.z e.hz π)
  exact ⟨γ, hγ, LineDatum.conePair_eq_corner π v d e hv γ hγ⟩

theorem PlaneDatum.conePair_exists_corner (d : PlaneDatum W) (e : PlaneDatum W') (hv : IsCoinvCycle v) :
    ∃ γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6),
      (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
        (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π ∧
      conePair π v d.cone e.cone =
        (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ d.z) ⊗ₘ (-e.w)) ≫ π) +
          flagPlaneHom.hom.f 3 ≫ γ).hom ((modelPush.pA 3).hom v) := by
  obtain ⟨γ, hγ⟩ := exists_plane_primitive ((nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (cup_cocycle (nerveDiagSystem Γ6 RationalGL3 Plane) d.z d.hz e.z e.hz π)
  exact ⟨γ, hγ, PlaneDatum.conePair_eq_corner π v d e hv γ hγ⟩

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
