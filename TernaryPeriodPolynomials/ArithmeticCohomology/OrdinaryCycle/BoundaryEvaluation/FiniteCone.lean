module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteBars
public import TernaryPeriodPolynomials.Building.Reference.CoefficientMatrices

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex SymmetricSpaceBoundaryFull OrdinaryParabolicGroups
open ReferenceCoefficientMatrices

/-- The literal coordinate transposition (01), in the full plane stabilizer. -/
def finitePlaneSwap : P := ⟨s, (mem_P s).mpr ⟨rfl,rfl⟩⟩

/-- The literal coordinate transposition (12), in the full line stabilizer. -/
def finiteLineSwap : Q := ⟨s*c, (mem_Q (s*c)).mpr (by constructor <;> decide +kernel)⟩

theorem finitePlaneSwap_inv : (finitePlaneSwap.val)⁻¹ = s := s_inv_eq_self

theorem finiteLineSwap_inv : (finiteLineSwap.val)⁻¹ = s*c := by
  apply Units.ext
  decide +kernel

theorem finiteLineSwap_cinv : (finiteLineSwap.val)⁻¹ * c⁻¹ = s := by
  rw [finiteLineSwap_inv, mul_assoc, mul_inv_cancel, mul_one]

theorem finiteLineSwap_c : (finiteLineSwap.val)⁻¹ * c = s*c⁻¹ := by
  rw [finiteLineSwap_inv, mul_assoc, ← pow_two, ← c_inv_eq_sq]

/-- The complete six flag-corner chains, with literal induction coordinates and orientation. -/
def finiteApartmentCorner : (inducedBarComplex B).X 0 :=
  (inducedZero B 1 - inducedZero B s) +
    (inducedZero B c⁻¹ - inducedZero B (s*c⁻¹)) +
    (inducedZero B c - inducedZero B (s*c))

/-- Three actual line-stabilizer bars fill the line image of the hexagon. -/
def finiteApartmentLine : (inducedBarComplex Q).X 1 :=
  inducedOne Q 1 finiteLineSwap + inducedOne Q c⁻¹ finiteLineSwap + inducedOne Q c finiteLineSwap

/-- Three actual plane-stabilizer bars fill the plane image of the hexagon. -/
def finiteApartmentPlane : (inducedBarComplex P).X 1 :=
  inducedOne P 1 finitePlaneSwap + inducedOne P c⁻¹ finitePlaneSwap + inducedOne P c finitePlaneSwap

/-- The line bars have exactly minus the complete corner's line boundary. -/
theorem finiteApartmentLine_boundary :
    ((inducedBarComplex Q).d 1 0).hom finiteApartmentLine =
      -(canonicalLineArrow.f 0).hom finiteApartmentCorner := by
  simp only [finiteApartmentLine, map_add, inducedOne_boundary, finiteLineSwap_inv,
    mul_one, mul_assoc, mul_inv_cancel, ← pow_two, ← c_inv_eq_sq]
  simp only [finiteApartmentCorner, map_add, map_sub]
  change _ = -((inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B 1) -
    (inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B s) +
    ((inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B c⁻¹) -
      (inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B (s*c⁻¹))) +
    ((inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B c) -
      (inducedBarMap B Q fullB_le_Q).f 0 (inducedZero B (s*c))))
  rw [inducedZero_map, inducedZero_map, inducedZero_map, inducedZero_map,
    inducedZero_map, inducedZero_map]
  abel

/-- The plane bars have exactly minus the complete corner's plane boundary. -/
theorem finiteApartmentPlane_boundary :
    ((inducedBarComplex P).d 1 0).hom finiteApartmentPlane =
      -(canonicalPlaneArrow.f 0).hom finiteApartmentCorner := by
  simp only [finiteApartmentPlane, map_add, inducedOne_boundary, finitePlaneSwap_inv, mul_one]
  simp only [finiteApartmentCorner, map_add, map_sub]
  change _ = -((inducedBarMap B P fullB_le_P).f 0 (inducedZero B 1) -
    (inducedBarMap B P fullB_le_P).f 0 (inducedZero B s) +
    ((inducedBarMap B P fullB_le_P).f 0 (inducedZero B c⁻¹) -
      (inducedBarMap B P fullB_le_P).f 0 (inducedZero B (s*c⁻¹))) +
    ((inducedBarMap B P fullB_le_P).f 0 (inducedZero B c) -
      (inducedBarMap B P fullB_le_P).f 0 (inducedZero B (s*c))))
  rw [inducedZero_map, inducedZero_map, inducedZero_map, inducedZero_map,
    inducedZero_map, inducedZero_map]
  abel

/-- The explicit finite canonical cone chain, negated for the genuine MV-edge convention. -/
def finiteApartmentChain : canonicalFaceCone.X 1 :=
  -((signedCornerInclusion canonicalLineArrow canonicalPlaneArrow 0).hom finiteApartmentCorner +
    (signedLineInclusion canonicalLineArrow canonicalPlaneArrow 1).hom finiteApartmentLine -
    (signedPlaneInclusion canonicalLineArrow canonicalPlaneArrow 1).hom finiteApartmentPlane)

/-- The twelve-term finite canonical chain is an actual degree-one cycle. -/
theorem finiteApartmentChain_boundary : canonicalFaceCone.d 1 0 finiteApartmentChain = 0 := by
  have hc := congrArg (fun f => f.hom finiteApartmentCorner)
    (signedCornerInclusion_d_zero canonicalLineArrow canonicalPlaneArrow)
  have hl := congrArg (fun f => f.hom finiteApartmentLine)
    (signedLineInclusion_d canonicalLineArrow canonicalPlaneArrow 1 0)
  have hp := congrArg (fun f => f.hom finiteApartmentPlane)
    (signedPlaneInclusion_d canonicalLineArrow canonicalPlaneArrow 1 0)
  change canonicalFaceCone.d 1 0 ((signedCornerInclusion _ _ 0).hom finiteApartmentCorner) =
    (signedLineInclusion _ _ 0).hom ((canonicalLineArrow.f 0).hom finiteApartmentCorner) -
    (signedPlaneInclusion _ _ 0).hom ((canonicalPlaneArrow.f 0).hom finiteApartmentCorner) at hc
  change canonicalFaceCone.d 1 0 ((signedLineInclusion _ _ 1).hom finiteApartmentLine) =
    (signedLineInclusion _ _ 0).hom (((inducedBarComplex Q).d 1 0).hom finiteApartmentLine) at hl
  change canonicalFaceCone.d 1 0 ((signedPlaneInclusion _ _ 1).hom finiteApartmentPlane) =
    (signedPlaneInclusion _ _ 0).hom (((inducedBarComplex P).d 1 0).hom finiteApartmentPlane) at hp
  rw [finiteApartmentLine_boundary, map_neg] at hl
  rw [finiteApartmentPlane_boundary, map_neg] at hp
  erw [finiteApartmentChain, map_neg, map_sub, map_add, hc, hl, hp]
  have hzero (x y : canonicalFaceCone.X 0) : -((x-y)+(-x)-(-y)) = 0 := by abel
  exact hzero _ _

end TernaryPoly.OrdinaryBoundaryActualEvaluation
