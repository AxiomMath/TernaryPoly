module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FamAct

@[expose] public section


/-!
# The face components of the cone pairing of the lifts of mixed classes

Formalized by Claude Sonnet 5.5.

For lifts `d`, `e` of mixed classes of a line face, `lineFacePairM` is the sum of two terms: the *base term* `⟨w ⌣ flagLine^* e.z, ω_A⟩` on the flag component `ω_A = pA 3 Ω` of the Stokes cycle
(it involves the flag primitives and the restriction of the line cocycles to the complete flags), and the *line term* `⟨d.z ⌣ e.z, ω_L⟩` on the line component `ω_L = pL 3 Ω`.  For planes the line term
is replaced by the plane term on `ω_P = pP 3 Ω` and the corner term pairs `flagPlane^* d.z` with `-e.w`.  This is the cone-level expression that the algebraic factorisation (fibre pairing times base pairing)
has to identify.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Coords

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ Rep.trivial ℚ Γ6 ℂ) (v : coneR.X 4)

/-- **The complex cone pairing of two line cones in coordinates**: base term on the flag component and line term on the line component. -/
theorem conePairC_lineCone_eq (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W)
    (w' : A.X 1 ⟶ W') (z' : (prodComplex Γ6 RationalGL3 Line).X 2 ⟶ W') :
    conePairC π v (lineCone w z) (lineCone w' z') =
      ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (w ⊗ₘ (flagLineHom.hom.f 2 ≫ z')) ≫ π).hom
        ((modelPush.pA 3).hom v) +
      ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (z ⊗ₘ z') ≫ π).hom ((modelPush.pL 3).hom v) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_rat_functional
  intro r
  rw [map_sub, map_add, rHom_conePairC, conePair_lineCone_eq (π ≫ rHom r) v w z w' z']
  exact sub_self _

/-- … for two plane cones. -/
theorem conePairC_planeCone_eq (w : A.X 1 ⟶ W) (z : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W)
    (w' : A.X 1 ⟶ W') (z' : (prodComplex Γ6 RationalGL3 Plane).X 2 ⟶ W') :
    conePairC π v (planeCone w z) (planeCone w' z') =
      ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ z) ⊗ₘ (-w')) ≫ π).hom
        ((modelPush.pA 3).hom v) +
      ((nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (z ⊗ₘ z') ≫ π).hom ((modelPush.pP 3).hom v) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_rat_functional
  intro r
  rw [map_sub, map_add, rHom_conePairC, conePair_planeCone_eq (π ≫ rHom r) v w z w' z']
  exact sub_self _

end Coords

section Lifts

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The line face pairing of lifts of mixed classes, in coordinates**: the base term on the flag component `pA 3 Ω` plus the line term on the line component `pL 3 Ω` of the Stokes cycle. -/
theorem lineFacePairM_coords (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
    (hdc : d.coord (lineFacesEquivOrbits i) = lineTau ρ i x) (hec : e.coord (lineFacesEquivOrbits i) = lineTauD ρ i y) :
    lineFacePairM ρ i x y =
      ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫
          (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) ≫ evalC (MonoidHom.id Γ6) (rep6 ρ)).hom
        ((modelPush.pA 3).hom stokesCycle) +
      ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ evalC (MonoidHom.id Γ6) (rep6 ρ)).hom
        ((modelPush.pL 3).hom stokesCycle) := by
  rw [lineFace_pair_eq_cone ρ i x y d e hd he hdc hec]
  exact conePairC_lineCone_eq (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle d.w d.z e.w e.z

/-- … for the plane face: the corner term pairs `flagPlane^* d.z` with `-e.w`. -/
theorem planeFacePairM_coords (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual)))
    (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
    (hd : d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (he : e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
    (hdc : d.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
        (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x))
    (hec : e.coord (planeFacesEquivOrbits i) =
      faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
        (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
        (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
        (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)) :
    planeFacePairM ρ i x y =
      ((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫
          ((flagPlaneHom.hom.f 2 ≫ d.z) ⊗ₘ (-e.w)) ≫ evalC (MonoidHom.id Γ6) (rep6 ρ)).hom
        ((modelPush.pA 3).hom stokesCycle) +
      ((nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ evalC (MonoidHom.id Γ6) (rep6 ρ)).hom
        ((modelPush.pP 3).hom stokesCycle) := by
  rw [planeFace_pair_eq_cone ρ i x y d e hd he hdc hec]
  exact conePairC_planeCone_eq (evalC (MonoidHom.id Γ6) (rep6 ρ)) stokesCycle d.w d.z e.w e.z

end Lifts

end TernaryPeriodPolynomials.Argument.GammaNStokes
