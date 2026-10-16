module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliers
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicInvariance

@[expose] public section


/-!
# The flat family of a plane section is `Ξ^{s - s₀} f`

For a function `logXi` satisfying `HeightLaw`, and a plane-induced section `f` at the cohomological
point, `s ↦ Ξ^{s - s₀} f` is a flat family (`xiFlat_isFlat`). By uniqueness of flat extensions
(`FlatUniqueness.linearFlatExtension_unique`), it is `SectionSpace.linearFlatExtension f`
(`linearFlatExtension_eq_xi`). Consequently, for the twisted section `Φ_z = ρ_h^z · R(h) f`
(`SectionMultipliers.twist`), the flat family of `Φ_{s - s₀}` at the parameter `s` is the right
translate by `h` of the flat family of `f` (`flat_twist_diagonal`) — the diagonal identity used in
`RightEquivariance.DiagonalDatum`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersFlat

/-- The power `Ξ^z` times a function. -/
def xiPower (logXi : AdelicGL → ℝ) (z : ℂ) (f : AdelicGL → ℂ) : AdelicGL → ℂ :=
  fun y => Complex.exp (z * (logXi y : ℂ)) * f y

/-- The candidate flat family `s ↦ Ξ^{s - s₀} f`. -/
def xiFlat (logXi : AdelicGL → ℝ) (f : AdelicGL → ℂ) : ℂ → AdelicGL → ℂ :=
  fun parameter => xiPower logXi (parameter - cohomologicalPoint) f

theorem normPower_shift (unit : Adelesˣ) (z c : ℂ) :
    normPower unit (-(c + z / 3)) * normPower unit (z / 3) = normPower unit (-c) := by
  unfold normPower
  rw [← Complex.exp_add]
  congr 1
  ring

theorem exp_levi_factor {logXi : AdelicGL → ℝ} (law : HeightLaw logXi) (z : ℂ)
    (binary : BinaryAdelicGL) (unit : Adelesˣ) (y : AdelicGL) :
    Complex.exp (z * (logXi (planeLevi binary unit * y) : ℂ)) =
      Complex.exp (z * (logXi y : ℂ)) * normPower (GeneralLinearGroup.det binary) (z / 3) *
        normPower unit (-2 * z / 3) := by
  rw [law.levi]
  unfold normPower
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem inductionShift (z : ℂ) :
    inductionExponent .plane (cohomologicalPoint + z) =
      inductionExponent .plane cohomologicalPoint + z / 3 := by
  simp only [inductionExponent]
  ring

theorem binaryShift (degree : ℕ) (z : ℂ) :
    binaryInductionExponent degree .plane (cohomologicalPoint + z) =
      binaryInductionExponent degree .plane cohomologicalPoint + z / 3 := by
  simp only [binaryInductionExponent, inductionExponent]
  ring

/-- `Ξ^z f` is plane-induced at the parameter `s₀ + z` when `f` is plane-induced at `s₀`. -/
theorem isInduced_xiPower {degree : ℕ} (data : InducingData degree) {logXi : AdelicGL → ℝ}
    (law : HeightLaw logXi) (f : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint f) (z : ℂ) :
    IsInduced data .plane (cohomologicalPoint + z) (xiPower logXi z f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    exact (smooth_cexp_mul z _ (law.smooth g)).mul (induced.1 g)
  · intro level g
    change Complex.exp (z * (logXi (g * atFinite level.val) : ℂ)) * f (g * atFinite level.val) =
      Complex.exp (z * (logXi g : ℂ)) * f g
    rw [law.rightCompact g _ (SmoothNormPower.finiteLevel_compact level), induced.2.1 level g]
  · intro a
    obtain ⟨vectors, vectorsSmooth, realizes⟩ := induced.2.2.1 a
    refine ⟨fun x => Complex.exp (z * (logXi (a * atInfinity (x (Fin.last 0))) : ℂ)) • vectors x,
      ?_, ?_⟩
    · have scalarSmooth : Smooth (fun x : Fin (0 + 1) → RealGL3 =>
          Complex.exp (z * (logXi (a * atInfinity (x (Fin.last 0))) : ℂ))) :=
        smooth_cexp_mul z _ (law.smooth a)
      show Smooth (fun x : Fin (0 + 1) → RealGL3 =>
        Complex.exp (z * (logXi (a * atInfinity (x (Fin.last 0))) : ℂ)) • (vectors x).val)
      exact ContDiffOn.smul scalarSmooth vectorsSmooth
    · intro x binary
      have realization := realizes x binary
      have shift := normPower_shift (GeneralLinearGroup.det binary) z
        (binaryInductionExponent degree .plane cohomologicalPoint)
      simp only [binaryLevi] at realization ⊢
      change data.cusp.realize (Complex.exp (z * (logXi (a * atInfinity (x (Fin.last 0))) : ℂ)) •
        vectors x) binary = _
      rw [map_smul, Pi.smul_apply, smul_eq_mul, realization, binaryShift]
      simp only [xiPower]
      rw [exp_levi_factor law z binary 1, ParabolicInvariance.normPower_one]
      linear_combination
        (-(Complex.exp (z * (logXi (a * atInfinity (x (Fin.last 0))) : ℂ)) *
          f (planeLevi binary 1 * (a * atInfinity (x (Fin.last 0)))))) * shift
  · refine ⟨?_, ?_, ?_⟩
    · intro first second g
      change Complex.exp (z * (logXi (planeUnipotent first second * g) : ℂ)) *
        f (planeUnipotent first second * g) = Complex.exp (z * (logXi g : ℂ)) * f g
      rw [law.radical, induced.2.2.2.1 first second g]
    · intro unit g
      change Complex.exp (z * (logXi (planeLevi 1 unit * g) : ℂ)) * f (planeLevi 1 unit * g) =
        _ * (Complex.exp (z * (logXi g : ℂ)) * f g)
      rw [exp_levi_factor law z 1 unit g, induced.2.2.2.2.1 unit g, inductionShift]
      have determinantOne : GeneralLinearGroup.det (1 : BinaryAdelicGL) = 1 := map_one _
      have split : -2 * (inductionExponent .plane cohomologicalPoint + z / 3) =
          -2 * inductionExponent .plane cohomologicalPoint + (-2 * z / 3) := by ring
      rw [determinantOne, ParabolicInvariance.normPower_one, split, NormPower.normPower_add]
      ring
    · intro g
      have member := (cuspFunctions data.cusp).smul_mem (Complex.exp (z * (logXi g : ℂ)))
        (induced.2.2.2.2.2 g)
      convert member using 1
      funext binary
      simp only [Pi.smul_apply, smul_eq_mul, xiPower]
      have shift := normPower_shift (GeneralLinearGroup.det binary) z
        (((degree : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint)
      have exponent : -(((degree : ℂ) + 3) / 2 + (inductionExponent .plane cohomologicalPoint + z / 3)) =
          -((((degree : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint) + z / 3) := by
        ring
      rw [exp_levi_factor law z binary 1 g, inductionShift, exponent,
        ParabolicInvariance.normPower_one]
      linear_combination (Complex.exp (z * (logXi g : ℂ)) * f (planeLevi binary 1 * g)) * shift

/-- `s ↦ Ξ^{s - s₀} f` is a flat family. -/
theorem xiFlat_isFlat {degree : ℕ} (data : InducingData degree) {logXi : AdelicGL → ℝ}
    (law : HeightLaw logXi) (f : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint f) :
    IsFlatSection data (xiFlat logXi f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro parameter
    have member := isInduced_xiPower data law f induced (parameter - cohomologicalPoint)
    have reparametrize : cohomologicalPoint + (parameter - cohomologicalPoint) = parameter := by
      ring
    rw [reparametrize] at member
    exact member
  · intro g parameter
    change AnalyticAt ℂ (fun z => Complex.exp ((z - cohomologicalPoint) * (logXi g : ℂ)) * f g)
      parameter
    exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_const).cexp).mul analyticAt_const
  · intro parameter binary compact membership
    have zeroLog : logXi compact = 0 := by
      have rightInvariance := law.rightCompact 1 compact membership
      rwa [one_mul, law.one] at rightInvariance
    have shift := normPower_shift (GeneralLinearGroup.det binary) (parameter - cohomologicalPoint)
      (binaryInductionExponent degree .plane cohomologicalPoint)
    have exponent : binaryInductionExponent degree .plane parameter =
        binaryInductionExponent degree .plane cohomologicalPoint +
          (parameter - cohomologicalPoint) / 3 := by
      simp only [binaryInductionExponent, inductionExponent]
      ring
    change normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane parameter) *
        (Complex.exp ((parameter - cohomologicalPoint) * (logXi (planeLevi binary 1 * compact) : ℂ)) *
          f (planeLevi binary 1 * compact)) =
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane cohomologicalPoint) *
        (Complex.exp ((cohomologicalPoint - cohomologicalPoint) *
          (logXi (planeLevi binary 1 * compact) : ℂ)) * f (planeLevi binary 1 * compact))
    rw [exp_levi_factor law (parameter - cohomologicalPoint) binary 1 compact, exponent, zeroLog,
      ParabolicInvariance.normPower_one]
    simp only [sub_self, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one]
    linear_combination (f (planeLevi binary 1 * compact)) * shift

/-- The flat extension of a plane section is `Ξ^{s - s₀} f`. -/
theorem linearFlatExtension_eq_xi {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : HeightLaw logXi)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (parameter : ℂ) (argument : AdelicGL) :
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).val parameter argument =
      Complex.exp ((parameter - cohomologicalPoint) * (logXi argument : ℂ)) *
        sectionValue.val argument := by
  have flat := xiFlat_isFlat data law sectionValue.val sectionValue.property
  have endpoint : (⟨xiFlat logXi sectionValue.val, flat⟩ : EisensteinValue.flatFamilies data).val
      cohomologicalPoint = sectionValue.val := by
    funext argument
    simp [xiFlat, xiPower]
  have unique := FlatUniqueness.linearFlatExtension_unique data holomorphic sectionValue
    ⟨xiFlat logXi sectionValue.val, flat⟩ endpoint
  exact congrArg (fun extension : EisensteinValue.flatFamilies data =>
    extension.val parameter argument) unique

/-- The flat family of the twisted section `Φ_{s - s₀}` at the parameter `s` is the right
translate by `h` of the flat family of `f`. -/
theorem flat_twist_diagonal {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : HeightLaw logXi)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (parameter : ℂ) (argument : AdelicGL) :
    (SectionSpace.linearFlatExtension data holomorphic
      ⟨twist logXi real (parameter - cohomologicalPoint) sectionValue.val,
        isInduced_twist data cohomologicalPoint law real (parameter - cohomologicalPoint)
          sectionValue.val sectionValue.property⟩).val parameter argument =
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).val parameter
      (argument * atInfinity real) := by
  rw [linearFlatExtension_eq_xi data holomorphic law, linearFlatExtension_eq_xi data holomorphic law]
  simp only [twist, heightMultiplier]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliersFlat
