module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsDual

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory
open SingularLocalCap SingularLocalCap.Homology
variable (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)

/-- A dual coboundary evaluates to zero on every actual chain homology class. -/
theorem evaluateCycles_boundary (φ : (dual S V).X₁) :
    evaluateCycles S V ((dual S V).moduleCatToCycles φ) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨c,rfl⟩ := SingularLocalCompactCap.Algebra.cycleClass_surjective S z
  change evaluateCycle S V _ (cycleClass S c) = 0
  rw [evaluateCycle_cycleClass]
  change φ (S.g c.val) = 0
  rw [c.property, map_zero]

/-- Canonical evaluation on dual cycles annihilates the actual dual boundary submodule. -/
theorem dual_boundaries_le_evaluation_kernel :
    Boundaries (dual S V) ≤ LinearMap.ker (evaluateCycles S V) := by
  rintro c ⟨φ,rfl⟩
  exact evaluateCycles_boundary S V φ

/-- The canonical rational universal-coefficient evaluation map on actual homology objects. -/
def evaluation : (dual S V).homology →ₗ[ℚ] (S.homology →ₗ[ℚ] V) :=
  ((Boundaries (dual S V)).liftQ (evaluateCycles S V)
    (dual_boundaries_le_evaluation_kernel S V)).comp (dual S V).moduleCatHomologyIso.hom.hom

/-- Universal evaluation on actual homology classes is literal cocycle application to an actual cycle. -/
theorem evaluation_cycleClasses (φ : Cycles (dual S V)) (c : Cycles S) :
    evaluation S V (cycleClass (dual S V) φ) (cycleClass S c) = φ.val c.val := by
  have h := congrArg (fun f => f ((Boundaries (dual S V)).mkQ φ))
    (dual S V).moduleCatHomologyIso.inv_hom_id
  change (dual S V).moduleCatHomologyIso.hom
    ((dual S V).moduleCatHomologyIso.inv ((Boundaries (dual S V)).mkQ φ)) =
      (Boundaries (dual S V)).mkQ φ at h
  change ((Boundaries (dual S V)).liftQ (evaluateCycles S V) (dual_boundaries_le_evaluation_kernel S V)
    ((dual S V).moduleCatHomologyIso.hom
      ((dual S V).moduleCatHomologyIso.inv ((Boundaries (dual S V)).mkQ φ)))) (cycleClass S c) = _
  rw [h]
  exact evaluateCycle_cycleClass S V φ c

end TernaryPoly.RationalHomologyCoefficients
