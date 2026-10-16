module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.CochainHomology
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullTransfer

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex SymmetricSpaceBoundaryFullTransfer

variable {G : Type} [Group G] (H : Subgroup G)
  (C : ChainComplex (Rep.{0} ℚ G) ℕ) (W : Rep.{0} ℚ G) (n : ℕ)
  (a : C.X n ⟶ W) (ha : C.d (n+1) n ≫ a = 0)

include ha in
/-- Restriction keeps an actual cocycle's boundary-annihilation identity. -/
theorem restrictedCochain_boundary :
    (restrictedComplex H C).d (n+1) n ≫ (Rep.resFunctor H.subtype).map a = 0 := by
  change (Rep.resFunctor H.subtype).map (C.d (n+1) n) ≫ (Rep.resFunctor H.subtype).map a = 0
  rw [← Functor.map_comp, ha, Functor.map_zero]

/-- Evaluate a literal full-level cochain on the actual restricted chain complex. -/
def restrictedEvaluation : (restrictedComplex H C).homology n ⟶ Rep.res H.subtype W :=
  evaluationOfCochain (restrictedComplex H C) (Rep.res H.subtype W) n
    ((Rep.resFunctor H.subtype).map a) (restrictedCochain_boundary H C W n a ha)

/-- Restricted evaluation is literally the original cochain on each represented cycle. -/
theorem restrictedEvaluation_projection :
    (restrictedComplex H C).homologyπ n ≫ restrictedEvaluation H C W n a ha =
      (restrictedComplex H C).iCycles n ≫ (Rep.resFunctor H.subtype).map a :=
  evaluationOfCochain_projection _ _ _ _ _

/-- Literal full-level cochain compatibility remains exact after restriction and homology evaluation. -/
theorem restrictedEvaluation_natural {D : ChainComplex (Rep.{0} ℚ G) ℕ} (f : C ⟶ D)
    (b : D.X n ⟶ W) (hb : D.d (n+1) n ≫ b = 0) (hab : f.f n ≫ b = a) :
    homologyMap (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
      restrictedEvaluation H D W n b hb = restrictedEvaluation H C W n a ha := by
  apply evaluationOfCochain_natural
  change (Rep.resFunctor H.subtype).map (f.f n) ≫ (Rep.resFunctor H.subtype).map b = _
  rw [← Functor.map_comp, hab]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
