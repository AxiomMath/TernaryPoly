module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CochainSupBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicDecomposition

@[expose] public section


/-!
# Parabolic scaling of source cochain cusp vectors

At the cohomological point the plane modulus exponent vanishes, so moving the real argument of a
source-cochain cusp vector by a real plane-parabolic element `p` with `GL₂` block `B` multiplies
its cusp sup norm by `|det B|^{(n+3)/2}`. With the compact-set bound of `CochainSupBounds` this gives,
for vertices in a compact set and arguments `p k` with `k` in a compact set, the bound
`|det B|^{(n+3)/2} C` with one constant `C`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

/-- The determinant of the upper-left `GL₂` block of a real matrix. -/
def upperBlockDet (p : RealGL3) : ℝ := p.val 0 0 * p.val 1 1 - p.val 0 1 * p.val 1 0

/-- **Parabolic scaling of the cusp sup norm.** -/
theorem cochainCuspVector_parabolic (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    (vertices : Fin 3 → RealGL3) {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (k : RealGL3) :
    CuspSupNorm.cuspSupNorm (cochainCuspVector data source cocycle m vertices (p * k)) =
      |upperBlockDet p| ^ (((n : ℝ) + 3) / 2) *
        CuspSupNorm.cuspSupNorm (cochainCuspVector data source cocycle m vertices k) := by
  obtain ⟨a, b, s, B, hdec⟩ := SphericalDetection.Helpers.planeParabolic_exists_decomposition ⟨p, hp⟩
  change p = _ at hdec
  have hf := cocycle.1 vertices m
  have hsplit : atInfinity (p * k) =
      planeUnipotent ((a, 0) : Adeles) ((b, 0) : Adeles) *
        (planeLevi 1 (realAdeleUnit s) * (planeLevi (atInfinity B) 1 * atInfinity k)) := by
    rw [hdec, EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_planeUnipotent,
      EisensteinRegularization.Helpers.atInfinity_planeLevi,
      EisensteinRegularization.Helpers.atInfinity_planeLevi]
    have h1 : atInfinity (1 : BinaryRealGL) = 1 := by
      apply Units.ext
      refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;> by_cases hij : i = j <;>
        simp [atInfinity, combineGL, pairMatrix, hij]
    have h2 : realAdeleUnit (1 : ℝˣ) = 1 := by
      apply Units.ext; rfl
    rw [h1, h2]
    simp only [mul_assoc]
  unfold cochainCuspVector
  rw [hsplit, planeCuspVector_unipotent, planeCuspVector_scalar,
    CuspSupNorm.cuspSupNorm_smul, planeCuspVector_binaryLevi,
    CuspSupNorm.cuspSupNorm_smul, CuspSupNorm.cuspSupNorm_translate]
  have hscalar : ‖data.chi.toMonoidHom (realAdeleUnit s) *
      normPower (realAdeleUnit s) (-2 * inductionExponent .plane cohomologicalPoint)‖ = 1 := by
    rw [ArchimedeanConstant.plane_exponent_cohomological, mul_zero,
      SphericalDetection.Helpers.normPower_zero_exponent, mul_one, data.chi.unitary]
  have hblock : upperBlockDet p = B.val.det := by
    rw [upperBlockDet, hdec]
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.det_fin_two]
  have hBpos : 0 < |B.val.det| := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero B)
  have hlevi : ‖normPower (GeneralLinearGroup.det (atInfinity B))
      (binaryInductionExponent n .plane cohomologicalPoint)‖ = |B.val.det| ^ (((n : ℝ) + 3) / 2) := by
    rw [Helpers.norm_normPower,
      EisensteinRegularization.Helpers.det_atInfinity_binary,
      EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
    have hexp : (binaryInductionExponent n .plane cohomologicalPoint).re = ((n : ℝ) + 3) / 2 := by
      simp only [binaryInductionExponent, ArchimedeanConstant.plane_exponent_cohomological, add_zero]
      simp
    rw [hexp]
    change Real.exp (((n : ℝ) + 3) / 2 * Real.log |B.val.det|) = _
    rw [mul_comm, ← Real.rpow_def_of_pos hBpos]
  rw [hscalar, one_mul, hlevi, hblock]

/-- **Uniform parabolic decay on compact vertex sets.** -/
theorem cochainCuspVector_parabolic_bound (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    {K : Set (Fin 3 → RealGL3)} (hK : IsCompact K) {L : Set RealGL3} (hL : IsCompact L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ p ∈ planeParabolic ℝ, ∀ k ∈ L,
      CuspSupNorm.cuspSupNorm (cochainCuspVector data source cocycle m x (p * k)) ≤
        |upperBlockDet p| ^ (((n : ℝ) + 3) / 2) * C := by
  let join : (Fin 3 → RealGL3) × RealGL3 → (Fin 4 → RealGL3) := fun pair => Fin.snoc pair.1 pair.2
  have joinContinuous : Continuous join := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have e : (fun pair : (Fin 3 → RealGL3) × RealGL3 => join pair (Fin.last 3)) = Prod.snd := by
        funext pair
        exact Fin.snoc_last (α := fun _ => RealGL3) pair.2 pair.1
      rw [e]
      exact continuous_snd
    · have e : (fun pair : (Fin 3 → RealGL3) × RealGL3 => join pair j.castSucc) = fun pair => pair.1 j := by
        funext pair
        simp [join]
      rw [e]
      exact (continuous_apply j).comp continuous_fst
  obtain ⟨C, hC0, hC⟩ := cochainCuspVector_bounded data source cocycle m ((hK.prod hL).image joinContinuous)
  refine ⟨C, hC0, fun x hx p hp k hk => ?_⟩
  rw [cochainCuspVector_parabolic data source cocycle m x hp k]
  have bound := hC (join (x, k)) ⟨(x, k), ⟨hx, hk⟩, rfl⟩
  simp only [join, Fin.snoc_castSucc, Fin.snoc_last] at bound
  exact mul_le_mul_of_nonneg_left bound (Real.rpow_nonneg (abs_nonneg _) _)

end TernaryPeriodPolynomials.AnalyticClasses
