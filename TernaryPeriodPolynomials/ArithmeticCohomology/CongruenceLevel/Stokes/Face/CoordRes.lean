module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Lifts

@[expose] public section


/-!
# Restriction naturality of the Shapiro coordinates along the incidence maps, in all degrees

Formalized by Claude Sonnet 5.5.

For an equivariant map `α : Z → Z'` of label sets, labels `z ∈ Z` and subgroups `S' ≤ S` with `S'` fixing `z` and `S` fixing `α z`, the Shapiro coordinate of the pullback along `α` at `z` for `S'` is the
restriction `H^n(S, W) → H^n(S', W)` of the coordinate at `α z` for `S` (`faceCoord_pullback_res`).  For `Γ(6)` and the incidence maps of complete flags to lines and to planes:
`faceCoord_flagLine`, `faceCoord_flagPlane`: `coord_F ∘ H^n(flagLine^*) = res^{Stab ℓ}_{Stab F} ∘ coord_ℓ` for every flag `F` with line `ℓ` (plane) and every degree `n`.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.EquivariantSingularSmall

section Generic

variable {Γ : Type} [Group Γ] {V Z Z' : Type} [MulAction Γ V] [MulAction Γ Z] [MulAction Γ Z']

/-- **Restriction naturality of the Shapiro coordinate along an equivariant map of label sets** (every degree). -/
theorem faceCoord_pullback_res (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z)
    (S S' : Subgroup Γ) (h : S' ≤ S) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z)
    (hz' : ∀ g : S', g • z = z) (hS : ∀ g : S, g • α z = α z) (n : ℕ) :
    HomologicalComplex.homologyMap (homPullback (prodMapHom Γ V Z α hα) W) n ≫
        faceCoord S' W v₀ z hz' n =
      faceCoord S W v₀ (α z) hS n ≫
        groupCohomology.map (Subgroup.inclusion h) (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W))) n := by
  have hS' : ∀ g : S', g • α z = α z := fun g => hS ⟨g.1, h g.2⟩
  rw [faceCoord_eq_homologyMap_stabCoord, faceCoord_eq_homologyMap_stabCoord]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, stabCoord_pullback α hα S' W v₀ z hz' hS',
    stabCoord_sub S S' h W v₀ (α z) hS hS']
  erw [HomologicalComplex.homologyMap_comp]
  rw [Category.assoc, Category.assoc]
  refine congrArg (fun t => HomologicalComplex.homologyMap (stabCoord S W v₀ (α z) hS) n ≫ t) ?_
  exact barChainMap_homology (A := Rep.res S.subtype W) (B := Rep.res S'.subtype W) (Subgroup.inclusion h)
    (𝟙 (Rep.res (Subgroup.inclusion h) (Rep.res S.subtype W))) n

end Generic

section Flags

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable (W : Rep.{0} ℚ Γ6) (F : Flag) (n : ℕ)

/-- **Restriction naturality along `flagLine`**: for every complete flag `F` with line `ℓ = flagLine F`,
`coord_F ∘ H^n(flagLine^*) = res^{Stab ℓ}_{Stab F} ∘ coord_ℓ`. -/
theorem faceCoord_flagLine :
    HomologicalComplex.homologyMap (homPullback flagLineHom.hom W) n ≫
        faceCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) F (fun g => g.2) n =
      faceCoord (MulAction.stabilizer Γ6 (flagLineOf F)) W (1 : RationalGL3) (flagLineOf F) (fun g => g.2) n ≫
        groupCohomology.map (Subgroup.inclusion (stab_flag_le_stab_pt flagLineOf
          TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant F))
          (𝟙 (Rep.res (Subgroup.inclusion (stab_flag_le_stab_pt flagLineOf
            TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant F))
            (Rep.res (MulAction.stabilizer Γ6 (flagLineOf F)).subtype W))) n :=
  faceCoord_pullback_res flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant
    (MulAction.stabilizer Γ6 (flagLineOf F)) (MulAction.stabilizer Γ6 F)
    (stab_flag_le_stab_pt flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant F)
    W (1 : RationalGL3) F (fun g => g.2)
    (fun g => g.2) n

/-- … along `flagPlane`. -/
theorem faceCoord_flagPlane :
    HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom W) n ≫
        faceCoord (MulAction.stabilizer Γ6 F) W (1 : RationalGL3) F (fun g => g.2) n =
      faceCoord (MulAction.stabilizer Γ6 (flagPlaneOf F)) W (1 : RationalGL3) (flagPlaneOf F) (fun g => g.2) n ≫
        groupCohomology.map (Subgroup.inclusion (stab_flag_le_stab_pt flagPlaneOf
          TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F))
          (𝟙 (Rep.res (Subgroup.inclusion (stab_flag_le_stab_pt flagPlaneOf
            TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F))
            (Rep.res (MulAction.stabilizer Γ6 (flagPlaneOf F)).subtype W))) n :=
  faceCoord_pullback_res flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant
    (MulAction.stabilizer Γ6 (flagPlaneOf F)) (MulAction.stabilizer Γ6 F)
    (stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant F)
    W (1 : RationalGL3) F (fun g => g.2)
    (fun g => g.2) n

end Flags

end TernaryPeriodPolynomials.Argument.GammaNStokes
