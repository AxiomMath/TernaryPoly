module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GraphReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FlagShapiro
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Basic

@[expose] public section


/-!
# `RestrictionFormula` from the vanishing of the defect at integral flags

The defect cochain `defectCochain` (restriction of the global Eisenstein cocycle minus the
evaluated source of the side) is a coboundary as soon as, at every integral flag representative
`g`, its `g`-component is the differential of a one-cochain equivariant for the flag stabilizer
`rationalLevel ⊓ stabilizer`. This file assembles the restriction formula from that local
statement (Shapiro assembly `exists_primitive_of_stabilizers`, integral representatives of flags).

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

/-- The defect cochain is the differential of an equivariant one-cochain as soon as this holds
componentwise at integral flag representatives. -/
theorem defectCochain_exact_of_integral_flags (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (hrep : ∀ x : Flags side, ∃ g : IntegralGL3,
      (QuotientGroup.mk (integralRational g) :
        Flags side) = x)
    (hflag : ∀ g : IntegralGL3,
      ∃ P : cochains (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) : Flags side))
        (rationalCoefficientComponent n D.chi) 1,
      ∀ y : Fin 3 → RationalGL3,
        (differentialOne (rationalLevel ⊓ MulAction.stabilizer RationalGL3
          (QuotientGroup.mk (integralRational g) : Flags side)) (rationalCoefficientComponent n D.chi) P).val y =
        (defectCochain large D hol c side).val y
          (QuotientGroup.mk (integralRational g))) :
    ∃ P : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) 1,
      ∀ y, (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) P).val y =
        (defectCochain large D hol c side).val y := by
  apply exists_primitive_of_stabilizers (rationalCoefficientComponent n D.chi) (Flags side)
    rationalLevel (defectCochain large D hol c side)
  intro x
  obtain ⟨g, rfl⟩ := hrep x
  exact hflag g

/-- Equality of the stratum class of the restriction of the global Eisenstein cocycle and of the
evaluated source of the side, from exactness of the defect cochain. -/
theorem stratum_class_eq_of_exact (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (hexact : ∃ P : cochains rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) 1,
      ∀ y, (differentialOne rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) side) P).val y =
        (defectCochain large D hol c side).val y) :
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
        (restrictionCocycle n D.chi side
          (EndpointEisensteinCocycle.globalCocycle D hol large c)) =
      SourceSpace.sourceClass D side (sideSource large D hol c side) := by
  obtain ⟨P, hP⟩ := hexact
  change classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
      (restrictionCocycle n D.chi side
        (EndpointEisensteinCocycle.globalCocycle D hol large c)) =
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)
      (SourceSpace.evaluatedSource D side (sideSource large D hol c side))
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨P, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext y
  exact hP y

/-- **The restriction formula from exactness of the defect on both strata.** -/
theorem restrictionFormula_of_exact (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (hexact : ∀ (c : SourceSpace.sourceCocycles D .plane) (side : Side),
      ∃ P : cochains rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) side) 1,
        ∀ y, (differentialOne rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) side) P).val y =
          (defectCochain large D hol c side).val y) :
    GraphReduction.RestrictionFormula large D hol := by
  intro c
  exact Prod.ext (stratum_class_eq_of_exact large D hol c .plane (hexact c .plane))
    (stratum_class_eq_of_exact large D hol c .line (hexact c .line))

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
