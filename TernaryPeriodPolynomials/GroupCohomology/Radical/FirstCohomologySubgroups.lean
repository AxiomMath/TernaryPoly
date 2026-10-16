module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLine
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlane
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineComparison
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlaneComparison
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologySubgroups

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.RadicalFirstCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RadicalTopCohomology RelativeStabilizerParameters

/-- Parameterization identifies genuine first cohomology of the lattice and the actual plane radical. -/
def planeParameterH1Iso (n : ℕ) :
    groupCohomology (planeRep n) 1 ≅ groupCohomology (planeSubgroupRep n) 1 :=
  groupCohomology.mapIso planeParamEquiv (LinearEquiv.refl ℚ (H n)) (fun _ => rfl) 1

def lineParameterH1Iso (n : ℕ) :
    groupCohomology (lineRep n) 1 ≅ groupCohomology (lineSubgroupRep n) 1 :=
  groupCohomology.mapIso lineParamEquiv (LinearEquiv.refl ℚ (H n)) (fun _ => rfl) 1

/-- Actual inverse conjugation and coefficient action on plane-radical first cohomology. -/
def planeSubgroupH1Action (n : ℕ) (M : GL2) :
    groupCohomology (planeSubgroupRep n) 1 ⟶ groupCohomology (planeSubgroupRep n) 1 :=
  groupCohomology.map (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) 1

def lineSubgroupH1Action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    groupCohomology (lineSubgroupRep n) 1 ⟶ groupCohomology (lineSubgroupRep n) 1 :=
  groupCohomology.map (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) 1

@[reassoc] theorem planeParameterH1Iso_action (n : ℕ) (M : GL2) :
    (planeParameterH1Iso n).inv ≫ planeH1Action n M =
      planeSubgroupH1Action n M ≫ (planeParameterH1Iso n).inv :=
  planeParameterCohomology_natural n 1 M

@[reassoc] theorem lineParameterH1Iso_action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    (lineParameterH1Iso n).inv ≫ lineH1Action n ε =
      lineSubgroupH1Action n ε ≫ (lineParameterH1Iso n).inv :=
  lineParameterCohomology_natural n 1 ε

/-- The actual integral plane-radical H¹ comparison with the closed derivative-pair quotient. -/
def planeSubgroupH1DerivativeQuotientIso (n : ℕ) :
    groupCohomology (planeSubgroupRep n) 1 ≅ planeDerivativeQuotient n :=
  (planeParameterH1Iso n).symm ≪≫ planeH1DerivativeQuotientIso n

def lineSubgroupH1DerivativeQuotientIso (n : ℕ) :
    groupCohomology (lineSubgroupRep n) 1 ≅ lineDerivativeQuotient n :=
  (lineParameterH1Iso n).symm ≪≫ lineH1DerivativeQuotientIso n

/-- The actual plane Levi central sign is minus identity in even degree. -/
theorem planeSubgroupH1_sign (n : ℕ) (hn : Even n) :
    planeSubgroupH1Action n (-1)= -𝟙 (groupCohomology (planeSubgroupRep n) 1) := by
  apply (cancel_mono (planeParameterH1Iso n).inv).mp
  rw [←planeParameterH1Iso_action,planeH1_sign n hn]
  simp

/-- The actual independent line diagonal sign is minus identity in every degree. -/
theorem lineSubgroupH1_sign (n : ℕ) :
    lineSubgroupH1Action n (-1,1)= -𝟙 (groupCohomology (lineSubgroupRep n) 1) := by
  apply (cancel_mono (lineParameterH1Iso n).inv).mp
  rw [←lineParameterH1Iso_action,lineH1_sign]
  simp

/-- The actual plane comparison intertwines the specified central action and minus identity. -/
theorem planeSubgroupH1DerivativeQuotientIso_sign (n : ℕ) (hn : Even n)
    (v : groupCohomology (planeSubgroupRep n) 1) :
    (planeSubgroupH1DerivativeQuotientIso n).hom (planeSubgroupH1Action n (-1) v)=
      -(planeSubgroupH1DerivativeQuotientIso n).hom v := by
  rw [planeSubgroupH1_sign n hn]
  change (planeSubgroupH1DerivativeQuotientIso n).hom (-v)=_
  rw [map_neg]

theorem lineSubgroupH1DerivativeQuotientIso_sign (n : ℕ)
    (v : groupCohomology (lineSubgroupRep n) 1) :
    (lineSubgroupH1DerivativeQuotientIso n).hom (lineSubgroupH1Action n (-1,1) v)=
      -(lineSubgroupH1DerivativeQuotientIso n).hom v := by
  rw [lineSubgroupH1_sign]
  change (lineSubgroupH1DerivativeQuotientIso n).hom (-v)=_
  rw [map_neg]

end TernaryPoly.RadicalFirstCohomology
