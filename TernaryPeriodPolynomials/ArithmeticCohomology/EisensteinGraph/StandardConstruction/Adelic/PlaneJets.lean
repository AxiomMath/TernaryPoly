module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PlaneJets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Jets

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicPlaneJets

def leftJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (function : AdelicGL → E) (argument : AdelicGL) (binary : Fin 1 → BinaryRealGL) :=
  SmoothJets.jet order (fun elements : Fin 1 → BinaryRealGL =>
    function (atInfinity (planeLevi (elements 0) 1) * argument)) binary

theorem finite_local_formula {E : Type} (function : AdelicGL → E)
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (reference : FiniteGL) (argument : AdelicGL)
    (membership : reference⁻¹ * finiteGroup argument ∈ finiteLevel) (real : RealGL3) :
    function (atInfinity real * argument) =
      function (atFinite reference * atInfinity (real * realGroup argument)) := by
  let unit : finiteLevel := ⟨reference⁻¹ * finiteGroup argument, membership⟩
  calc
    _ = function (atInfinity real * ((atFinite reference * atInfinity (realGroup argument)) *
        atFinite unit.val)) :=
      congrArg (fun value => function (atInfinity real * value))
        (InducedContinuity.split_right argument reference)
    _ = function ((atFinite reference * atInfinity (real * realGroup argument)) * atFinite unit.val) := by
      rw [RealTranslations.atInfinity_mul, ← mul_assoc, ← mul_assoc,
        ← RealTranslations.atFinite_atInfinity_commute reference real, mul_assoc (atFinite reference)]
    _ = _ := invariant unit _

theorem leftJet_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument) (order : ℕ) :
    Continuous (fun pair : AdelicGL × (Fin 1 → BinaryRealGL) =>
      leftJet order function pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  intro pair
  have localContinuous : Continuous (fun other : AdelicGL × (Fin 1 → BinaryRealGL) =>
      SmoothJets.jet order (fun elements : Fin 1 → BinaryRealGL =>
        function (atFinite (finiteGroup pair.1) *
          atInfinity (planeLevi (elements 0) 1 * realGroup other.1))) other.2) := by
    have translation := PlaneJets.jet_plane_continuous
      (fun elements : Fin 1 → RealGL3 =>
        function (atFinite (finiteGroup pair.1) * atInfinity (elements 0)))
      (smooth (atFinite (finiteGroup pair.1))) order
    exact translation.comp
      (f := fun other : AdelicGL × (Fin 1 → BinaryRealGL) =>
        ((fun _ : Fin 1 => realGroup other.1), other.2))
      ((continuous_pi (fun _ : Fin 1 =>
        InducedContinuity.realGroup_continuous.comp continuous_fst)).prodMk continuous_snd)
  have near : ∀ᶠ other : AdelicGL × (Fin 1 → BinaryRealGL) in 𝓝 pair,
      (finiteGroup pair.1)⁻¹ * finiteGroup other.1 ∈ finiteLevel :=
    (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul (InducedContinuity.finiteGroup_continuous.comp continuous_fst))).mem_nhds
        (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with other membership
  unfold leftJet
  congr 1
  funext elements
  exact finite_local_formula function invariant (finiteGroup pair.1) other.1 membership
    (planeLevi (elements 0) 1)

theorem finite_leftJets_bounded {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (adelicSet : Set AdelicGL) (adelicCompact : IsCompact adelicSet)
    (binarySet : Set (Fin 1 → BinaryRealGL)) (binaryCompact : IsCompact binarySet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ argument ∈ adelicSet, ∀ binary ∈ binarySet,
      ∀ derivative ≤ order, ‖leftJet derivative function argument binary‖ ≤ bound := by
  have continuous : Continuous (fun pair : AdelicGL × (Fin 1 → BinaryRealGL) =>
      ∑ derivative ∈ Finset.range (order + 1), ‖leftJet derivative function pair.1 pair.2‖) := by
    apply continuous_finsetSum
    intro derivative _
    exact (leftJet_continuous function smooth invariant derivative).norm
  obtain ⟨bound, bounded⟩ :=
    (adelicCompact.prod binaryCompact).exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro argument argumentMem binary binaryMem derivative atMost
  have estimate := bounded (argument, binary) ⟨argumentMem, binaryMem⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at estimate
  have single : ‖leftJet derivative function argument binary‖ ≤
      ∑ index ∈ Finset.range (order + 1), ‖leftJet index function argument binary‖ :=
    Finset.single_le_sum (s := Finset.range (order + 1)) (a := derivative)
      (f := fun index => ‖leftJet index function argument binary‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  exact single.trans (estimate.trans (le_max_left _ _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicPlaneJets
