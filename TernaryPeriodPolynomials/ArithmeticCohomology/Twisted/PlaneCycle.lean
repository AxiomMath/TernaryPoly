module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge

@[expose] public section


/-!
# Cocycle-level formulas for the twisted identity-plane edge

The twisted binary edge sends a relative two-cocycle `z` of the identity-plane stabilizer to the
one-cocycle `m ↦ (n+1)⁻¹ (X₀ · π(z(s(m), u(m e₁)) - z(u(e₁), s(m))) + X₁ · π(…))` of
`GL₂(ℤ)` with values in `Sym^{n+1} ⊗ det⁰`; this is literally the formula of the untwisted edge, only
the module structure on the target differs.  This file records the formula, the criterion for a
relative class to vanish in terms of a binary potential, and the ambient (homogeneous cochain)
version of the edge.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The `GL₂(ℤ)`-one-cocycle of the twisted edge attached to a relative two-cocycle. -/
def identityPlaneBinaryEdgeCycleT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (identityPlaneRadicalCoordinateIsoT n χ hχ).hom).hom.comp
      (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ))

/-- The radical one-cocycle attached to a relative two-cocycle and a Levi element, as a cocycle of the
upper radical lattice representation. -/
def identityPlaneRadicalEdgeCycleT (n : ℕ) (χ : RankOneCharacter)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) : groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  cocycleToUpperT n χ (splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle)

theorem identityPlaneBinaryEdgeCycleT_apply (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneBinaryEdgeCycleT n χ hχ cycle matrix =
      upperRadicalCocycleCoordinate n (identityPlaneRadicalEdgeCycleT n χ cycle matrix) := by
  have equality := groupCohomology.mapCocycles₁_comp_i_apply
    (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ)) (identityPlaneRadicalCoordinateIsoT n χ hχ).hom
    (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle)
  have value := congrFun equality matrix
  change identityPlaneBinaryEdgeCycleT n χ hχ cycle matrix =
    identityPlaneRadicalH1CoordinateT n χ
      (groupCohomology.H1π (Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
        (splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle)) at value
  exact value.trans (identityPlaneRadicalH1CoordinateT_apply n χ _)

theorem identityPlaneBinaryEdgeCycleT_H1 (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (identityPlaneBinaryEdgeCycleT n χ hχ cycle) =
      identityPlaneBinaryEdgeT n χ hχ
        (relativeTwoCocycleClass identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ) cycle) := by
  rw [identityPlaneBinaryEdgeT_apply]
  change groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
      (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
        (identityPlaneRadicalCoordinateIsoT n χ hχ).hom
        (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle)) =
    groupCohomology.map (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
      (identityPlaneRadicalCoordinateIsoT n χ hχ).hom 1
      (groupCohomology.H1π
        (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRepT n χ))
        (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle))
  exact (groupCohomology.H1π_comp_map_apply
    (A := splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRepT n χ))
    (B := arithmeticBinaryRep (n + 1) 0) (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (identityPlaneRadicalCoordinateIsoT n χ hχ).hom
    (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRepT n χ) cycle)).symm

theorem identityPlaneSplitEdgeCycleT_apply (n : ℕ) (χ : RankOneCharacter)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    identityPlaneRadicalEdgeCycleT n χ cycle matrix radical =
      cycle.val (identityPlaneLeviSection matrix,
          identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radical)) -
        cycle.val (identityPlaneRadicalInclusion radical, identityPlaneLeviSection matrix) :=
  (splitEdgeCycle_apply identityPlaneSplitting (identityPlaneCoefficientRepT n χ) matrix cycle radical).trans
    (congrArg (fun input : RadicalLattice =>
      cycle.val (identityPlaneLeviSection matrix, identityPlaneRadicalInclusion input) -
        cycle.val (identityPlaneRadicalInclusion radical, identityPlaneLeviSection matrix))
      (identityPlaneSplitting_inverse_action matrix radical))

/-- **The cocycle-level formula of the twisted edge.** -/
theorem identityPlaneBinaryEdgeCycleT_value (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycleT n χ hχ cycle matrix).val = (n + 1 : ℂ)⁻¹ •
      (MvPolynomial.X 0 * binaryPolynomialRestrict
        (cycle.val (identityPlaneLeviSection matrix,
            identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radicalLatticeFirst)) -
          cycle.val (identityPlaneRadicalInclusion radicalLatticeFirst, identityPlaneLeviSection matrix)).val +
       MvPolynomial.X 1 * binaryPolynomialRestrict
        (cycle.val (identityPlaneLeviSection matrix,
            identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radicalLatticeSecond)) -
          cycle.val (identityPlaneRadicalInclusion radicalLatticeSecond, identityPlaneLeviSection matrix)).val) := by
  rw [identityPlaneBinaryEdgeCycleT_apply]
  have formula := upperRadicalCocycleCoordinate_value (identityPlaneRadicalEdgeCycleT n χ cycle matrix)
  have first := congrArg (fun polynomial : HomogeneousPoly n => binaryPolynomialRestrict polynomial.val)
    (identityPlaneSplitEdgeCycleT_apply n χ cycle matrix radicalLatticeFirst)
  have second := congrArg (fun polynomial : HomogeneousPoly n => binaryPolynomialRestrict polynomial.val)
    (identityPlaneSplitEdgeCycleT_apply n χ cycle matrix radicalLatticeSecond)
  rw [first, second] at formula
  exact formula

theorem identityPlaneFullBinaryEdgeT_relative (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) :
    identityPlaneFullBinaryEdgeT n χ hχ positive odd
        (groupCohomology.H2π (identityPlaneCoefficientRepT n χ) cycle.val) =
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (identityPlaneBinaryEdgeCycleT n χ hχ cycle) := by
  rw [identityPlaneBinaryEdgeCycleT_H1]
  rfl

/-- The vanishing of a relative class is an ordinary binary-polynomial coboundary on integral `GL₂`
with values in `Sym^{n+1} ⊗ det⁰`. -/
theorem identityPlaneRelativeH2_zero_iff_binaryPotentialT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRepT n χ)) :
    groupCohomology.H2π (identityPlaneCoefficientRepT n χ) cycle.val = 0 ↔
      ∃ potential : Binary.HomogeneousPoly (n + 1), ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        identityPlaneBinaryEdgeCycleT n χ hχ cycle matrix =
          Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
            potential - potential := by
  rw [← identityPlaneFullBinaryEdgeT_zero_iff n χ hχ positive odd,
    identityPlaneFullBinaryEdgeT_relative, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    exact ⟨potential, fun matrix => (congrFun equality matrix).symm⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, funext (fun matrix => (equality matrix).symm)⟩

/-! ### The ambient edge -/

/-- **The ambient twisted edge**, on homogeneous cocycles of the identity-plane stabilizer with values
in the ambient representation `rationalCoefficientComponent n χ`. -/
def identityPlaneAmbientBinaryEdgeT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n) :
    cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ) →ₗ[ℂ]
        groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  (identityPlaneFullBinaryEdgeT n χ hχ positive odd).comp
    ((groupCohomology.H2π (identityPlaneCoefficientRepT n χ)).hom.comp
      (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ)))

theorem identityPlaneAmbientBinaryEdgeT_apply (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ)) :
    identityPlaneAmbientBinaryEdgeT n χ hχ positive odd cycle =
      identityPlaneFullBinaryEdgeT n χ hχ positive odd
        (groupCohomology.H2π (identityPlaneCoefficientRepT n χ)
          (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
            (rationalCoefficientComponent n χ) cycle)) := rfl

/-- Detection: the ambient twisted edge of a homogeneous cocycle vanishes iff the cocycle is a
homogeneous coboundary. -/
theorem identityPlaneAmbientBinaryEdgeT_zero_iff (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ)) :
    identityPlaneAmbientBinaryEdgeT n χ hχ positive odd cycle = 0 ↔
      ∃ primitive, differentialOne (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) primitive = cycle.val :=
  (identityPlaneFullBinaryEdgeT_zero_iff n χ hχ positive odd
    (groupCohomology.H2π (identityPlaneCoefficientRepT n χ)
      (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent n χ) cycle))).trans
    (ambientCocycle_H2_zero_iff (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n χ) cycle)

end TernaryPeriodPolynomials.Twisted
