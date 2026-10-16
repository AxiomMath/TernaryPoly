module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.Three
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.LineFactorization

@[expose] public section


/-!
# R-e: The bad-plane and good-line weights

`badPlaneWeight` (indicator of `P(ℚ₃)K₁` at `3`) and `goodLineWeight` (indicator of `L(ℚ₃)g₀K₁`), with their finite-part, level and parabolic invariance.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem inLocalThreeLevel_inv {x : LocalThreeGL} (h : InLocalThreeLevel x) : InLocalThreeLevel x⁻¹ := by
  obtain ⟨k, hrow, rfl⟩ := h
  refine ⟨k⁻¹, ?_, by rw [map_inv]⟩
  conv_lhs => rw [← hrow]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.vecMul_one]

/-- The set `P(ℚ₃) K₁` of local matrices, `K₁` the last-row congruence subgroup. -/
def badPlaneSet (g : LocalThreeGL) : Prop :=
  ∃ (p : planeParabolic ℚ_[3]) (k : LocalThreeGL), InLocalThreeLevel k ∧ g = p.val * k

/-- The set `L(ℚ₃) g₀ K₁` of local matrices. -/
def goodLineSet (g : LocalThreeGL) : Prop :=
  ∃ (p : lineParabolic ℚ_[3]) (k : LocalThreeGL), InLocalThreeLevel k ∧ g = p.val * localGoodLine * k

theorem badPlaneSet_mul_level {g c : LocalThreeGL} (hg : badPlaneSet g) (hc : InLocalThreeLevel c) :
    badPlaneSet (g * c) := by
  obtain ⟨p, k, hk, rfl⟩ := hg
  exact ⟨p, k * c, InLocalThreeLevel_mul hk hc, by rw [mul_assoc]⟩

theorem badPlaneSet_mul_level_iff {g c : LocalThreeGL} (hc : InLocalThreeLevel c) :
    badPlaneSet (g * c) ↔ badPlaneSet g := by
  refine ⟨fun h => ?_, fun h => badPlaneSet_mul_level h hc⟩
  have := badPlaneSet_mul_level h (inLocalThreeLevel_inv hc)
  rwa [mul_inv_cancel_right] at this

theorem badPlaneSet_parabolic_mul {g : LocalThreeGL} (q : planeParabolic ℚ_[3]) (hg : badPlaneSet g) :
    badPlaneSet (q.val * g) := by
  obtain ⟨p, k, hk, rfl⟩ := hg
  exact ⟨q * p, k, hk, by rw [Subgroup.coe_mul, mul_assoc]⟩

theorem badPlaneSet_parabolic_mul_iff {g : LocalThreeGL} (q : planeParabolic ℚ_[3]) :
    badPlaneSet (q.val * g) ↔ badPlaneSet g := by
  refine ⟨fun h => ?_, badPlaneSet_parabolic_mul q⟩
  have := badPlaneSet_parabolic_mul q⁻¹ h
  rwa [Subgroup.coe_inv, inv_mul_cancel_left] at this

theorem goodLineSet_mul_level_iff {g c : LocalThreeGL} (hc : InLocalThreeLevel c) :
    goodLineSet (g * c) ↔ goodLineSet g := by
  have forward : ∀ {g c : LocalThreeGL}, goodLineSet g → InLocalThreeLevel c → goodLineSet (g * c) := by
    intro g c hg hc
    obtain ⟨p, k, hk, rfl⟩ := hg
    exact ⟨p, k * c, InLocalThreeLevel_mul hk hc, by rw [mul_assoc]⟩
  refine ⟨fun h => ?_, fun h => forward h hc⟩
  have := forward h (inLocalThreeLevel_inv hc)
  rwa [mul_inv_cancel_right] at this

theorem goodLineSet_parabolic_mul_iff {g : LocalThreeGL} (q : lineParabolic ℚ_[3]) :
    goodLineSet (q.val * g) ↔ goodLineSet g := by
  have forward : ∀ (q : lineParabolic ℚ_[3]) {g : LocalThreeGL}, goodLineSet g → goodLineSet (q.val * g) := by
    intro q g hg
    obtain ⟨p, k, hk, rfl⟩ := hg
    exact ⟨q * p, k, hk, by simp only [Subgroup.coe_mul, mul_assoc]⟩
  refine ⟨fun h => ?_, forward q⟩
  have := forward q⁻¹ h
  rwa [Subgroup.coe_inv, inv_mul_cancel_left] at this

open Classical in
/-- The finite weight of the bad-plane section: the indicator of `P(ℚ₃) K₁` at `3`. -/
def badPlaneWeight (g : AdelicGL) : ℂ := if badPlaneSet (adelicThreeGroup g) then 1 else 0

open Classical in
/-- The finite weight of the good-line component: the indicator of `L(ℚ₃) g₀ K₁` at `3`. -/
def goodLineWeight (g : AdelicGL) : ℂ := if goodLineSet (adelicThreeGroup g) then 1 else 0

theorem adelicThreeGroup_mem_plane (p : AdelicGL) (hp : p ∈ planeParabolic Adeles) :
    adelicThreeGroup p ∈ planeParabolic ℚ_[3] := by
  have first := generalLinearGroup_map_plane (RingHom.snd ℝ FiniteAdeles) ⟨p, hp⟩
  exact generalLinearGroup_map_plane finiteThree ⟨_, first⟩

theorem adelicThreeGroup_mem_line (p : AdelicGL) (hp : p ∈ lineParabolic Adeles) :
    adelicThreeGroup p ∈ lineParabolic ℚ_[3] := by
  have first := generalLinearGroup_map_line (RingHom.snd ℝ FiniteAdeles) hp
  exact generalLinearGroup_map_line finiteThree first

theorem badPlaneWeight_finite (g g' : AdelicGL) (h : finiteGroup g = finiteGroup g') :
    badPlaneWeight g = badPlaneWeight g' := by
  unfold badPlaneWeight
  have : adelicThreeGroup g = adelicThreeGroup g' := by
    change GeneralLinearGroup.map finiteThree (finiteGroup g) = GeneralLinearGroup.map finiteThree (finiteGroup g')
    rw [h]
  rw [this]

open Classical in
theorem badPlaneWeight_level (k : finiteLevel) (g : AdelicGL) :
    badPlaneWeight (g * atFinite k.val) = badPlaneWeight g := by
  unfold badPlaneWeight
  rw [map_mul]
  exact if_congr (badPlaneSet_mul_level_iff (finiteLevel_atThree k)) rfl rfl

open Classical in
theorem badPlaneWeight_parabolic (p : AdelicGL) (hp : p ∈ planeParabolic Adeles) (g : AdelicGL) :
    badPlaneWeight (p * g) = badPlaneWeight g := by
  unfold badPlaneWeight
  rw [map_mul]
  exact if_congr (badPlaneSet_parabolic_mul_iff ⟨_, adelicThreeGroup_mem_plane p hp⟩) rfl rfl

theorem goodLineWeight_finite (g g' : AdelicGL) (h : finiteGroup g = finiteGroup g') :
    goodLineWeight g = goodLineWeight g' := by
  unfold goodLineWeight
  have : adelicThreeGroup g = adelicThreeGroup g' := by
    change GeneralLinearGroup.map finiteThree (finiteGroup g) = GeneralLinearGroup.map finiteThree (finiteGroup g')
    rw [h]
  rw [this]

open Classical in
theorem goodLineWeight_level (k : finiteLevel) (g : AdelicGL) :
    goodLineWeight (g * atFinite k.val) = goodLineWeight g := by
  unfold goodLineWeight
  rw [map_mul]
  exact if_congr (goodLineSet_mul_level_iff (finiteLevel_atThree k)) rfl rfl

open Classical in
theorem goodLineWeight_parabolic (p : AdelicGL) (hp : p ∈ lineParabolic Adeles) (g : AdelicGL) :
    goodLineWeight (p * g) = goodLineWeight g := by
  unfold goodLineWeight
  rw [map_mul]
  exact if_congr (goodLineSet_parabolic_mul_iff ⟨_, adelicThreeGroup_mem_line p hp⟩) rfl rfl

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
