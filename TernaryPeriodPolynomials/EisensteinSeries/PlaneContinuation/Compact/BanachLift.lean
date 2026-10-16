module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.ProfileCutoff
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactBanachLift

open scoped Classical

variable {Index Domain Target : Type} {Sources : Index → Type}
variable [Fintype Index]
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain] [FiniteDimensional ℝ Domain]
variable [NormedAddCommGroup Target] [NormedSpace ℂ Target]
variable [∀ index, NormedAddCommGroup (Sources index)] [∀ index, NormedSpace ℂ (Sources index)]

def sumMap (maps : ∀ index, Sources index →L[ℂ] Target) : (∀ index, Sources index) →L[ℂ] Target :=
  ∑ index, (maps index).comp (ContinuousLinearMap.proj index)

theorem sumMap_apply (maps : ∀ index, Sources index →L[ℂ] Target) (value : ∀ index, Sources index) :
    sumMap maps value = ∑ index, maps index (value index) := by
  simp only [sumMap, _root_.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

variable [NormedSpace ℝ Target] [IsScalarTower ℝ ℂ Target]
variable [∀ index, NormedSpace ℝ (Sources index)] [∀ index, IsScalarTower ℝ ℂ (Sources index)]
variable [∀ index, CompleteSpace (Sources index)]

theorem exists_supported_test (maps : ∀ index, Sources index →L[ℂ] Target) (profile : Domain → Target)
    (domains : Index → Set Domain) (openness : ∀ index, IsOpen (domains index))
    (lifts : ∀ index, Domain → Sources index)
    (analytic : ∀ index, AnalyticOnNhd ℝ (lifts index) (domains index))
    (values : ∀ index, ∀ point ∈ domains index, maps index (lifts index point) = profile point)
    (cutoff : Domain → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (covered : tsupport cutoff ⊆ ⋃ index, domains index) :
    ∃ test : SchwartzMap Domain (∀ index, Sources index), tsupport (fun point => test point) ⊆ tsupport cutoff ∧
      ∀ point, sumMap maps (test point) = cutoff point • profile point := by
  obtain ⟨partition, subordinate⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ Domain) (isClosed_tsupport cutoff) domains openness covered
  let localCutoff : Index → Domain → ℝ := fun index point => cutoff point * partition index point
  have localSmooth (index : Index) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localCutoff index) :=
    smooth.mul (partition index).contMDiff.contDiff
  have localSupported (index : Index) : tsupport (localCutoff index) ⊆ domains index :=
    tsupport_mul_subset_right.trans (subordinate index)
  let lift : Domain → (∀ index, Sources index) := fun point index => localCutoff index point • lifts index point
  have liftSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) lift := by
    apply contDiff_pi.mpr
    intro index
    exact RealProfileCutoff.smul_contDiff_of_support (localCutoff index) (lifts index) _ (localSmooth index)
      (fun point membership => (analytic index point (localSupported index membership)).contDiffAt)
  have expression : lift = fun point => cutoff point • (fun index => partition index point • lifts index point) := by
    funext point index
    exact mul_smul _ _ _
  have liftSupported : tsupport lift ⊆ tsupport cutoff := by
    rw [expression]
    exact tsupport_smul_subset_left _ _
  have liftCompact : HasCompactSupport lift := compact.of_isClosed_subset (isClosed_tsupport lift) liftSupported
  refine ⟨liftCompact.toSchwartzMap liftSmooth, liftSupported, ?_⟩
  intro point
  rw [sumMap_apply]
  change (∑ index, maps index (localCutoff index point • lifts index point)) = _
  have termEquality (index : Index) : maps index (localCutoff index point • lifts index point) =
      localCutoff index point • profile point := by
    rw [LinearMapClass.map_smul_of_tower]
    by_cases membership : point ∈ domains index
    · rw [values index point membership]
    · have zeroCutoff : localCutoff index point = 0 :=
        image_eq_zero_of_notMem_tsupport (fun supported => membership (localSupported index supported))
      rw [zeroCutoff, zero_smul, zero_smul]
  simp_rw [termEquality]
  rw [← Finset.sum_smul]
  by_cases nonzero : cutoff point = 0
  · simp only [localCutoff, nonzero, zero_mul, Finset.sum_const_zero, zero_smul]
  · have partitionSum : ∑ index, partition index point = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using partition.sum_eq_one (subset_tsupport _ nonzero)
    change (∑ index, cutoff point * partition index point) • profile point = _
    rw [← Finset.mul_sum, partitionSum, mul_one]

theorem exists_test (maps : ∀ index, Sources index →L[ℂ] Target) (profile : Domain → Target)
    (domains : Index → Set Domain) (openness : ∀ index, IsOpen (domains index))
    (lifts : ∀ index, Domain → Sources index)
    (analytic : ∀ index, AnalyticOnNhd ℝ (lifts index) (domains index))
    (values : ∀ index, ∀ point ∈ domains index, maps index (lifts index point) = profile point)
    (cutoff : Domain → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (covered : tsupport cutoff ⊆ ⋃ index, domains index) :
    ∃ test : SchwartzMap Domain (∀ index, Sources index),
      ∀ point, sumMap maps (test point) = cutoff point • profile point := by
  obtain ⟨test, _, equality⟩ := exists_supported_test maps profile domains openness lifts analytic values cutoff smooth compact covered
  exact ⟨test, equality⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactBanachLift
