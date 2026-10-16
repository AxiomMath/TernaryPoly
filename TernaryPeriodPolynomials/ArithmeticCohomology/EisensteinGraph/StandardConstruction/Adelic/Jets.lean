module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TranslatedJets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicJets

def rightJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (function : AdelicGL → E) (argument : AdelicGL) (real : Fin 1 → RealGL3) :=
  SmoothJets.jet order (fun elements : Fin 1 → RealGL3 =>
    function (argument * atInfinity (elements 0))) real

theorem finite_local_formula {E : Type} (function : AdelicGL → E)
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (reference : FiniteGL) (argument : AdelicGL)
    (membership : reference⁻¹ * finiteGroup argument ∈ finiteLevel) (real : RealGL3) :
    function (argument * atInfinity real) =
      function (atFinite reference * atInfinity (realGroup argument * real)) := by
  let unit : finiteLevel := ⟨reference⁻¹ * finiteGroup argument, membership⟩
  calc
    _ = function ((atFinite reference * atInfinity (realGroup argument) *
        atFinite unit.val) * atInfinity real) :=
      congrArg (fun value => function (value * atInfinity real))
        (InducedContinuity.split_right argument reference)
    _ = function ((atFinite reference * atInfinity (realGroup argument) *
        atInfinity real) * atFinite unit.val) := by
      rw [mul_assoc (atFinite reference * atInfinity (realGroup argument)),
        RealTranslations.atFinite_atInfinity_commute unit.val real, ← mul_assoc]
    _ = _ := by
      rw [invariant, RealTranslations.atInfinity_mul, mul_assoc]

theorem rightJet_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (reference : FiniteGL) (argument : AdelicGL)
    (membership : reference⁻¹ * finiteGroup argument ∈ finiteLevel)
    (order : ℕ) (real : Fin 1 → RealGL3) :
    rightJet order function argument real =
      SmoothJets.jet order (fun elements : Fin 1 → RealGL3 =>
        function (atFinite reference * atInfinity (realGroup argument * elements 0))) real := by
  have equality : (fun elements : Fin 1 → RealGL3 => function (argument * atInfinity (elements 0))) =
      (fun elements : Fin 1 → RealGL3 =>
        function (atFinite reference * atInfinity (realGroup argument * elements 0))) :=
    funext (fun elements => finite_local_formula function invariant reference argument membership (elements 0))
  unfold rightJet
  rw [equality]

theorem rightJet_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument) (order : ℕ) :
    Continuous (fun pair : AdelicGL × (Fin 1 → RealGL3) =>
      rightJet order function pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  intro pair
  have localContinuous : Continuous (fun other : AdelicGL × (Fin 1 → RealGL3) =>
      SmoothJets.jet order (fun elements : Fin 1 → RealGL3 =>
        function (atFinite (finiteGroup pair.1) *
          atInfinity (realGroup other.1 * elements 0))) other.2) := by
    have translation := TranslatedJets.jet_mul_left_continuous
      (fun elements : Fin 1 → RealGL3 =>
        function (atFinite (finiteGroup pair.1) * atInfinity (elements 0)))
      (smooth (atFinite (finiteGroup pair.1))) order
    exact translation.comp
      (f := fun other : AdelicGL × (Fin 1 → RealGL3) =>
        ((fun _ : Fin 1 => realGroup other.1), other.2))
      ((continuous_pi (fun _ : Fin 1 =>
        InducedContinuity.realGroup_continuous.comp continuous_fst)).prodMk continuous_snd)
  have near : ∀ᶠ other : AdelicGL × (Fin 1 → RealGL3) in 𝓝 pair,
      (finiteGroup pair.1)⁻¹ * finiteGroup other.1 ∈ finiteLevel :=
    (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul (InducedContinuity.finiteGroup_continuous.comp continuous_fst))).mem_nhds
        (by simp)
  apply localContinuous.continuousAt.congr_of_eventuallyEq
  filter_upwards [near] with other membership
  exact rightJet_local function invariant (finiteGroup pair.1) other.1 membership order other.2

/-- Compact adelic base arguments and compact real arguments admit one derivative bound. -/
theorem finite_rightJets_bounded {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun elements : Fin 1 → RealGL3 =>
      function (argument * atInfinity (elements 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (adelicSet : Set AdelicGL) (adelicCompact : IsCompact adelicSet)
    (realSet : Set (Fin 1 → RealGL3)) (realCompact : IsCompact realSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ argument ∈ adelicSet, ∀ real ∈ realSet,
      ∀ derivative ≤ order, ‖rightJet derivative function argument real‖ ≤ bound := by
  have continuous : Continuous (fun pair : AdelicGL × (Fin 1 → RealGL3) =>
      ∑ derivative ∈ Finset.range (order + 1), ‖rightJet derivative function pair.1 pair.2‖) := by
    apply continuous_finsetSum
    intro derivative _
    exact (rightJet_continuous function smooth invariant derivative).norm
  obtain ⟨bound, bounded⟩ :=
    (adelicCompact.prod realCompact).exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro argument argumentMem real realMem derivative atMost
  have estimate := bounded (argument, real) ⟨argumentMem, realMem⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at estimate
  have single : ‖rightJet derivative function argument real‖ ≤
      ∑ index ∈ Finset.range (order + 1), ‖rightJet index function argument real‖ :=
    Finset.single_le_sum (s := Finset.range (order + 1)) (a := derivative)
      (f := fun index => ‖rightJet index function argument real‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  exact single.trans (estimate.trans (le_max_left _ _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicJets
