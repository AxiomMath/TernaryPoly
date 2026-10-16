module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Jets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.FixedSpace

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspUniformJets

theorem hilbertJet_continuous {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (order : ℕ) :
    Continuous (fun pair : AdelicGL × (Fin 1 → RealGL3) =>
      AdelicJets.rightJet order
        (fun argument => (CuspLift.vector data side parameter function induced argument).val)
        pair.1 pair.2) :=
  AdelicJets.rightJet_continuous _ (CuspLift.real_smooth data side parameter function induced)
    (fun level argument => congrArg Subtype.val
      (CuspLift.finite_invariant data side parameter function induced argument level)) order

theorem hilbertJets_bounded {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function)
    (adelicSet : Set AdelicGL) (adelicCompact : IsCompact adelicSet)
    (realSet : Set (Fin 1 → RealGL3)) (realCompact : IsCompact realSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ argument ∈ adelicSet, ∀ real ∈ realSet, ∀ derivative ≤ order,
      ‖AdelicJets.rightJet derivative
        (fun argument => (CuspLift.vector data side parameter function induced argument).val)
        argument real‖ ≤ bound :=
  AdelicJets.finite_rightJets_bounded _ (CuspLift.real_smooth data side parameter function induced)
    (fun level argument => congrArg Subtype.val
      (CuspLift.finite_invariant data side parameter function induced argument level))
    adelicSet adelicCompact realSet realCompact order

def projectedLift {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function) :
    AdelicGL → CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal :=
  fun argument => (CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal).orthogonalProjectionOnto
    (CuspLift.vector data .plane parameter function induced argument).val

theorem projectedLift_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      projectedLift data parameter function induced (argument * atInfinity (real 0))) := by
  let projection :=
    (CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal).orthogonalProjectionOnto.restrictScalars ℝ
  exact projection.contDiff.comp_contDiffOn
    (CuspLift.real_smooth data .plane parameter function induced argument)

theorem projectedLift_finite_invariant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (level : finiteLevel) (argument : AdelicGL) :
    projectedLift data parameter function induced (argument * atFinite level.val) =
      projectedLift data parameter function induced argument := by
  unfold projectedLift
  rw [CuspLift.finite_invariant]

theorem projectedLift_eq_compactRealLift {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    (fun real : Fin 1 → RealGL3 =>
      projectedLift data parameter function induced (compact * atInfinity (real 0))) =
        CuspFixedSpace.compactRealLift data parameter function induced compact membership := by
  funext real
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (CuspFixedSpace.compactRealLift data parameter function induced compact membership real)

/-- One bound controls all compact base arguments, real parameters, and derivatives
up to the prescribed finite order, in the common fixed-level Hilbert space. -/
theorem fixedJets_bounded {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (realSet : Set (Fin 1 → RealGL3)) (realCompact : IsCompact realSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compact, ∀ membership : inMaximalCompact compact,
      ∀ real ∈ realSet, ∀ derivative ≤ order,
        ‖SmoothJets.jet derivative
          (CuspFixedSpace.compactRealLift data parameter function induced compact membership) real‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := AdelicJets.finite_rightJets_bounded
    (projectedLift data parameter function induced) (projectedLift_smooth data parameter function induced)
    (projectedLift_finite_invariant data parameter function induced)
    {compact | inMaximalCompact compact} MaximalCompact.isCompact realSet realCompact order
  refine ⟨bound, nonnegative, ?_⟩
  intro compact membership real realMembership derivative atMost
  have estimate := bounded compact membership real realMembership derivative atMost
  unfold AdelicJets.rightJet at estimate
  rw [projectedLift_eq_compactRealLift data parameter function induced compact membership] at estimate
  exact estimate

theorem flat_fixedLift_eq_cohomologicalPoint {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (compact : AdelicGL) (membership : inMaximalCompact compact)
    (real : Fin 1 → RealGL3)
    (orthogonal : (real 0).val.transpose * (real 0).val = 1) :
    CuspFixedSpace.compactRealLift data parameter (extension parameter) (flat.1 parameter)
        compact membership real =
      CuspFixedSpace.compactRealLift data cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compact membership real := by
  apply Subtype.ext
  change (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
      (compact * atInfinity (real 0))).val =
    (CuspLift.vector data .plane cohomologicalPoint (extension cohomologicalPoint)
      (flat.1 cohomologicalPoint) (compact * atInfinity (real 0))).val
  exact congrArg Subtype.val (CuspLift.flat_vector data extension flat parameter
    (compact * atInfinity (real 0))
    (RealTranslations.compact_mul compact (atInfinity (real 0)) membership
      (RealTranslations.compact_atInfinity (real 0) orthogonal)))

theorem flat_fixedLift_norm_bounded {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter compact,
      ∀ membership : inMaximalCompact compact, ∀ real : Fin 1 → RealGL3,
      (real 0).val.transpose * (real 0).val = 1 →
      ‖(CuspFixedSpace.compactRealLift data parameter (extension parameter)
          (flat.1 parameter) compact membership real).val‖ ≤ bound := by
  obtain ⟨endpointBound, bounded⟩ := CuspLift.bounded data .plane cohomologicalPoint
    (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  refine ⟨max endpointBound 0, le_max_right _ _, ?_⟩
  intro parameter compact membership real orthogonal
  rw [flat_fixedLift_eq_cohomologicalPoint data extension flat parameter compact membership
    real orthogonal]
  exact (bounded (compact * atInfinity (real 0))
    (RealTranslations.compact_mul compact (atInfinity (real 0)) membership
      (RealTranslations.compact_atInfinity (real 0) orthogonal))).trans (le_max_left _ _)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CuspUniformJets
