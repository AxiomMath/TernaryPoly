module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Local
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.LocalPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Decomp
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CornerEval

@[expose] public section


/-!
# The cone pairing of two line (plane) data is a sum over the flag orbits of universal functionals of explicit classes

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`LineDatum.conePair_decomp` / `PlaneDatum.conePair_decomp`: for a coinvariant cycle `v` of the cone there are functionals `φ_o` on `H³(Stab o.out; ℚ)` (one for each orbit `o` of complete flags of `Γ(6)`), depending
only on `v`, such that for ALL coefficient modules, pairings `π`, line (plane) data `d`, `e` and primitives `γ` of `d.z ∪ e.z`, the cone pairing is `∑_o φ_o (faceCoord_o [lineFlagCochain π d.w e.z γ])`
(resp. the plane analogue).  Combined with `lineFlag_faceCoord` this exhibits the cone pairing as the sum over the flag orbits of a universal functional on the class of the explicit cup cocycle
`w̄ ⌣ z̄' - γ̄` of the flag stabilizer; nothing about the coefficients enters `φ_o`.  The remaining content of the face factorisation is the evaluation of `φ_o` (the one-dimensionality and
evaluation functional on `H³` of the flag group) and of the sum on mixed classes.
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

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

theorem lineFlagCochain_cocycle (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (lineFlagCochain π d.w e.z γ) = 0 :=
  lineFlagCochain_d π d e γ hγ

theorem planeFlagCochain_cocycle (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    ((homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))).d (2 + 1) (2 + 1 + 1)).hom
      (planeFlagCochain π d.z e.w γ) = 0 :=
  planeFlagCochain_d π d e γ hγ

/-- **The cone pairing of two line data is a sum over the flag orbits of universal functionals applied to the flag classes.**  The functionals `φ_o` depend only on the coinvariant cycle `v`
(not on the coefficient modules `W`, `W'`, the pairing `π`, the data, or the primitive `γ`). -/
theorem LineDatum.conePair_decomp (v : coneR.X 4) (hv : IsCoinvCycle v) :
    ∃ φ : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 →ₗ[ℚ] ℚ,
      ∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : LineDatum W) (e : LineDatum W')
        (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
        (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
          (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π),
        conePair π v d.cone e.cone = ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (lineFlagCochain π d.w e.z γ) (lineFlagCochain_cocycle π d e γ hγ))) := by
  obtain ⟨φ, hφ⟩ := corner_functional_decomp ((modelPush.pA 3).hom v) (fun ψ => modelPush.corner_cycle hv ψ)
  refine ⟨φ, fun π d e γ hγ => ?_⟩
  rw [LineDatum.conePair_eq_corner π v d e hv γ hγ]
  exact hφ _ (lineFlagCochain_cocycle π d e γ hγ)

/-- **The same for two plane data.** -/
theorem PlaneDatum.conePair_decomp (v : coneR.X 4) (hv : IsCoinvCycle v) :
    ∃ φ : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 →ₗ[ℚ] ℚ,
      ∀ {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : PlaneDatum W) (e : PlaneDatum W')
        (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
        (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
          (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π),
        conePair π v d.cone e.cone = ∑ o, φ o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (planeFlagCochain π d.z e.w γ) (planeFlagCochain_cocycle π d e γ hγ))) := by
  obtain ⟨φ, hφ⟩ := corner_functional_decomp ((modelPush.pA 3).hom v) (fun ψ => modelPush.corner_cycle hv ψ)
  refine ⟨φ, fun π d e γ hγ => ?_⟩
  rw [PlaneDatum.conePair_eq_corner π v d e hv γ hγ]
  exact hφ _ (planeFlagCochain_cocycle π d e γ hγ)

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
