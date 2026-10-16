module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesIncidence
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Consumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open OrdinaryIncidence SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction SymmetricSpaceRationalGluing
open IntegralGL3Congruence

/-- Rational action transports the actual line label by the literal rational subspace action. -/
theorem lineFace_action_iff (a : RationalGL) (L : Line) (x : Glued) :
    leftAction a x∈lineFace (OrdinaryFullAction.lineAction a L) ↔ x∈lineFace L := by
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  rw [leftAction_chart,lineFace_chart_iff,lineFace_chart_iff]
  change (p.2.1.val=0 ∧ OrdinaryFullAction.lineAction (a*g) standardLine=
    OrdinaryFullAction.lineAction a L) ↔ _
  rw [lineAction_mul]
  exact and_congr_right (fun _ => (OrdinaryFullAction.lineAction a).injective.eq_iff)

theorem planeFace_action_iff (a : RationalGL) (P : Plane) (x : Glued) :
    leftAction a x∈planeFace (OrdinaryFullAction.planeAction a P) ↔ x∈planeFace P := by
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  rw [leftAction_chart,planeFace_chart_iff,planeFace_chart_iff]
  change (p.2.2.val=0 ∧ OrdinaryFullAction.planeAction (a*g) standardPlane=
    OrdinaryFullAction.planeAction a P) ↔ _
  rw [planeAction_mul]
  exact and_congr_right (fun _ => (OrdinaryFullAction.planeAction a).injective.eq_iff)

theorem lineFace_image (a : RationalGL) (L : Line) :
    leftAction a '' lineFace L=lineFace (OrdinaryFullAction.lineAction a L) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (lineFace_action_iff a L x).mpr hx
  · intro hy
    have he : leftAction a (leftAction a⁻¹ y)=y := by
      rw [←leftAction_mul,mul_inv_cancel,leftAction_one]
    exact ⟨leftAction a⁻¹ y,(lineFace_action_iff a L _).mp (he.symm ▸ hy),he⟩

theorem planeFace_image (a : RationalGL) (P : Plane) :
    leftAction a '' planeFace P=planeFace (OrdinaryFullAction.planeAction a P) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (planeFace_action_iff a P x).mpr hx
  · intro hy
    have he : leftAction a (leftAction a⁻¹ y)=y := by
      rw [←leftAction_mul,mul_inv_cancel,leftAction_one]
    exact ⟨leftAction a⁻¹ y,(planeFace_action_iff a P _).mp (he.symm ▸ hy),he⟩

/-- Integral action uses exactly the scalar-extended integral matrix on rational labels. -/
theorem integral_lineFace_image (a : ModThreeGoodAction.IntegralGL) (L : Line) :
    integralAction a '' lineFace L=lineFace
      (OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a) L) :=
  lineFace_image (integralRational a) L

theorem integral_planeFace_image (a : ModThreeGoodAction.IntegralGL) (P : Plane) :
    integralAction a '' planeFace P=planeFace
      (OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a) P) :=
  planeFace_image (integralRational a) P

/-- On K, the transported label is exactly the existing ordinary-incidence action. -/
theorem K_lineFace_image (a : GoodBuilding.K) (L : Line) :
    integralAction a.val '' lineFace L=lineFace (OrdinaryIncidence.lineAction a L) :=
  integral_lineFace_image a.val L

theorem K_planeFace_image (a : GoodBuilding.K) (P : Plane) :
    integralAction a.val '' planeFace P=planeFace (OrdinaryIncidence.planeAction a P) :=
  integral_planeFace_image a.val P

theorem principalSix_lineFace_image (a : principalSix) (L : Line) :
    (fun x : Glued => a • x) '' lineFace L=lineFace
      (OrdinaryFullAction.lineAction (OrdinaryFullAction.integral a.val) L) :=
  integral_lineFace_image a.val L

theorem principalSix_planeFace_image (a : principalSix) (P : Plane) :
    (fun x : Glued => a • x) '' planeFace P=planeFace
      (OrdinaryFullAction.planeAction (OrdinaryFullAction.integral a.val) P) :=
  integral_planeFace_image a.val P

end TernaryPoly.SymmetricSpaceBoundaryFaces
