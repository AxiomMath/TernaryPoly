module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ConeDecomp

@[expose] public section


/-!
# One family of universal flag-orbit functionals for the line pairing, the plane pairing and the vanishing on global cocycles

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`exists_cone_functionals`: for a coinvariant cycle `v` of the cone there is ONE family `φ_o` of functionals on `H³(Stab o.out; ℚ)` such that
(1) the cone pairing of any two line data (with any primitive `γ`) is `∑_o φ_o (faceCoord_o [lineFlagCochain …])`; (2) the same for plane data;
(3) `∑_o φ_o (faceCoord_o [flagLine^* ξ]) = 0` for every 3-cocycle `ξ` of the line complex; (4) the same for the plane complex.
(3) and (4) show that the local value `φ_o (faceCoord_o [θ])` of the corner functional is NOT intrinsic to the pair of classes: changing the primitive `γ` by a global cocycle `ξ` changes the
individual terms, and only their sum is invariant.  So the factorisation `φ_o = c_o · λ_o` must be combined with the sum-zero relations among the restrictions `H³(Q) → ⊕_F H³(B_F)`.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

theorem flagLine_cocycle (ξ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hξ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ ξ = 0) :
    ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (flagLineHom.hom.f 3 ≫ ξ) = 0 := by
  have hcomm : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagLineHom.hom.f 3 =
      flagLineHom.hom.f 4 ≫ (prodComplex Γ6 RationalGL3 Line).d 4 3 := (flagLineHom.hom.comm 4 3).symm
  change (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagLineHom.hom.f 3 ≫ ξ = 0
  rw [← Category.assoc, hcomm, Category.assoc, hξ, comp_zero]

theorem flagPlane_cocycle (ξ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hξ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ ξ = 0) :
    ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (flagPlaneHom.hom.f 3 ≫ ξ) = 0 := by
  have hcomm : (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagPlaneHom.hom.f 3 =
      flagPlaneHom.hom.f 4 ≫ (prodComplex Γ6 RationalGL3 Plane).d 4 3 := (flagPlaneHom.hom.comm 4 3).symm
  change (prodComplex Γ6 RationalGL3 Flag).d 4 3 ≫ flagPlaneHom.hom.f 3 ≫ ξ = 0
  rw [← Category.assoc, hcomm, Category.assoc, hξ, comp_zero]

theorem exists_cone_functionals (v : coneR.X 4) (hv : IsCoinvCycle v) :
    ∃ φ : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 →ₗ[ℚ] ℚ,
      (∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : LineDatum W) (e : LineDatum W')
        (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
        (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
          (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π),
        conePair π v d.cone e.cone = ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (lineFlagCochain π d.w e.z γ) (lineFlagCochain_cocycle π d e γ hγ)))) ∧
      (∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : PlaneDatum W) (e : PlaneDatum W')
        (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
        (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
          (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π),
        conePair π v d.cone e.cone = ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (planeFlagCochain π d.z e.w γ) (planeFlagCochain_cocycle π d e γ hγ)))) ∧
      (∀ (ξ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (hξ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ ξ = 0),
        ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (flagLineHom.hom.f 3 ≫ ξ) (flagLine_cocycle ξ hξ))) = 0) ∧
      (∀ (ξ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (hξ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ ξ = 0),
        ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (flagPlaneHom.hom.f 3 ≫ ξ) (flagPlane_cocycle ξ hξ))) = 0) := by
  obtain ⟨φ, hφ⟩ := corner_functional_decomp ((modelPush.pA 3).hom v) (fun ψ => modelPush.corner_cycle hv ψ)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro W W' π d e γ hγ
    rw [LineDatum.conePair_eq_corner π v d e hv γ hγ]
    exact hφ _ (lineFlagCochain_cocycle π d e γ hγ)
  · intro W W' π d e γ hγ
    rw [PlaneDatum.conePair_eq_corner π v d e hv γ hγ]
    exact hφ _ (planeFlagCochain_cocycle π d e γ hγ)
  · intro ξ hξ
    exact (hφ _ (flagLine_cocycle ξ hξ)).symm.trans (corner_eval_indep_line v hv ξ hξ)
  · intro ξ hξ
    exact (hφ _ (flagPlane_cocycle ξ hξ)).symm.trans (corner_eval_indep_plane v hv ξ hξ)

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
