module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralDual
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.ConstantTerms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

/-!
# The model's dual constant-term existence statement for the literal contragredient `E*`

Formalized by Claude Sonnet 5.5.

`FacePairingFull/Dual/ConstantTerms.dual_constant_terms_pointwise` proves, in the rational cocycle model with the dual
coefficient system `dualRep ρ = ρ ∘ dualInvolution`, that every inner line class `η` of `E*` is the line coordinate of a global cocycle whose plane
coordinate is inner.  `dual_constant_terms_pointwise_literal` transports this along `thetaModelEquiv` (`Θ` on cocycles, flag cocycles and edge
cochains: `inner_theta`, `inner_theta_inv`, `restriction_theta`) to the literal contragredient `ρ^∨` on `Module.Dual ℂ (HomogeneousPoly n)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (n : ℕ)

/-- Inner (zero flag restriction) classes transport along `Θ`. -/
theorem inner_theta (side : Side)
    (z : cocycles rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) side))
    (u : cochains rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) Edges) 1)
    (hu : ∀ x e, z.val.val x (endpoint side e) =
      (differentialOne rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) Edges) u).val x e) :
    InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual side
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual side)
        (thetaXCocycles n (Flags side) z)) := by
  refine ⟨thetaXCocycles n (Flags side) z, rfl, thetaXCochains n Edges 1 u, fun x e => ?_⟩
  have e1 : differentialOne rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual Edges)
      (thetaXCochains n Edges 1 u) =
      thetaXCochains n Edges 2 (differentialOne rationalLevel
        (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) Edges) u) :=
    (coeffCochains_differentialOne rationalLevel _ _ _ _ _).symm
  rw [e1]
  exact congrArg (thetaModel n) (hu x e)

/-- `Θ⁻¹` on cochains with values in functions on `X`. -/
def thetaXInvCochains (X : Type) [MulAction RationalGL3 X] (k : ℕ) :
    cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X) k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X) k :=
  coeffCochains rationalLevel _ _ (thetaFunInv n X) (thetaFunInv_intertwines n X) k

/-- Inner classes transport back along `Θ⁻¹`. -/
theorem inner_theta_inv (side : Side)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual side))
    (u : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual Edges) 1)
    (hu : ∀ x e, z.val.val x (endpoint side e) =
      (differentialOne rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual Edges) u).val x e) :
    InnerBoundaryRep (dualRep (rationalCoefficientComponent n trivialCharacter)) side
      (classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) side)
        (thetaXInvCocycles n (Flags side) z)) := by
  refine ⟨thetaXInvCocycles n (Flags side) z, rfl, thetaXInvCochains n Edges 1 u, fun x e => ?_⟩
  have e1 : differentialOne rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) Edges)
      (thetaXInvCochains n Edges 1 u) =
      thetaXInvCochains n Edges 2 (differentialOne rationalLevel
        (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual Edges) u) :=
    (coeffCochains_differentialOne rationalLevel _ _ _ _ _).symm
  rw [e1]
  exact congrArg (thetaModelEquiv n).symm (hu x e)

theorem restriction_theta (side : Side)
    (c : cocycles rationalLevel (dualRep (rationalCoefficientComponent n trivialCharacter))) :
    restrictionCocycleRep (rationalCoefficientComponent n trivialCharacter).dual side (thetaCocycles n c) =
      thetaXCocycles n (Flags side) (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) side c) :=
  rfl

/-- **The dual constant-term existence statement for the literal `E*`** (model `dual_constant_terms_pointwise` transported along `Θ`):
every inner line class `η` of `E*` is the line coordinate of a global cocycle of `E*` whose plane coordinate is inner. -/
theorem dual_constant_terms_pointwise_literal (hn : 4 ≤ n)
    (η : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line)
    (hη : InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .line η) :
    ∃ c'' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual,
      InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .plane
        (globalCoordinatesRep (rationalCoefficientComponent n trivialCharacter).dual c'').1 ∧
      (globalCoordinatesRep (rationalCoefficientComponent n trivialCharacter).dual c'').2 = η := by
  obtain ⟨z', hz', u', hu'⟩ := hη
  have hmodel := dual_constant_terms_pointwise n hn
    (classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .line)
      (thetaXInvCocycles n (Flags .line) z'))
    (inner_theta_inv n .line z' u' hu')
  obtain ⟨c', hc1, hc2⟩ := hmodel
  refine ⟨thetaCocycles n c', ?_, ?_⟩
  · obtain ⟨z0, hz0, u0, hu0⟩ := hc1
    have h := inner_theta n .plane z0 u0 hu0
    have hz0' : classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane) z0 =
        classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane)
          (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane c') := hz0
    have hcl : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)
          (thetaXCocycles n (Flags .plane) z0) =
        classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)
          (thetaXCocycles n (Flags .plane) (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane c')) :=
      classOf_coeff rationalLevel _ _ (thetaFun n (Flags .plane)) (thetaFun_intertwines n (Flags .plane)) hz0'
    have e3 : (globalCoordinatesRep (rationalCoefficientComponent n trivialCharacter).dual (thetaCocycles n c')).1 =
        classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)
          (thetaXCocycles n (Flags .plane) (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane c')) := rfl
    rw [e3, ← hcl]
    exact h
  · have e4 : (globalCoordinatesRep (rationalCoefficientComponent n trivialCharacter).dual (thetaCocycles n c')).2 =
        classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)
          (thetaXCocycles n (Flags .line) (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line c')) := rfl
    have hc2' : classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .line)
        (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line c') =
        classOf rationalLevel (flagRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) .line)
          (thetaXInvCocycles n (Flags .line) z') := hc2
    have hcl : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)
          (thetaXCocycles n (Flags .line) (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line c')) =
        classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)
          (thetaXCocycles n (Flags .line) (thetaXInvCocycles n (Flags .line) z')) :=
      classOf_coeff rationalLevel _ _ (thetaFun n (Flags .line)) (thetaFun_intertwines n (Flags .line)) hc2'
    have e5 : thetaXCocycles n (Flags .line) (thetaXInvCocycles n (Flags .line) z') = z' := by
      apply Subtype.ext
      apply Subtype.ext
      funext x F
      exact congrFun (thetaFun_thetaFunInv n (Flags .line) (z'.val.val x)) F
    rw [e4]
    refine hcl.trans ?_
    rw [e5]
    exact hz'

end TernaryPeriodPolynomials.Argument.EisensteinDual
