module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfilePackages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileInterpolation

section Assembly

variable {KeyType : Type} [Fintype KeyType] {degree : ℕ} (data : InducingData degree)
variable (families : KeyType → RealFamily data) (boxes : KeyType → Boxes)

abbrev Index := (key : KeyType) × (boxes key).indices

def test : ℂ → Rectangular Adeles → data.cusp.smooth :=
  FiniteGodementFamilies.test data (Finset.univ : Finset (Index boxes))
    (fun index => (families index.1).family) (fun index => (families index.1).tests)
    (fun index => FiniteLatticeMeasure.rationalScale (boxes index.1).scale)
    (fun index => index.2.val.out) (fun index => (boxes index.1).coefficients index.2.val)

def continuation : ℂ → AdelicGL → ℂ :=
  FiniteGodementFamilies.continuation data (Finset.univ : Finset (Index boxes))
    (fun index => (families index.1).family) (fun index => (families index.1).tests)
    (fun index => FiniteLatticeMeasure.rationalScale (boxes index.1).scale)
    (fun index => index.2.val.out) (fun index => (boxes index.1).coefficients index.2.val)

theorem continues :
    IsEisensteinContinuation
      (fun parameter point => VectorGodement.sectionFunction data (test data families boxes parameter) parameter point)
      (continuation data families boxes) :=
  FiniteGodementFamilies.isEisensteinContinuation data Finset.univ _ _ _ _ _
    (fun index => (families index.1).continuous) (fun index => (families index.1).holomorphic)
    (fun index => (families index.1).bounded)

theorem test_integrable (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    MeasureTheory.Integrable (VectorGodement.integrand data (test data families boxes parameter) parameter point)
      BinaryHaar.measure :=
  FiniteGodementFamilies.test_integrable data Finset.univ _ _ _ _ _
    (fun index => (families index.1).continuous) parameter point halfPlane

theorem test_eq (parameter : ℂ) (value : Rectangular Adeles) :
    test data families boxes parameter value =
      ∑ key, (boxes key).test (finite value) •
        ((families key).family ((families key).tests parameter (archimedean value))).val := by
  unfold test FiniteGodementFamilies.test
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro key _
  simp only [liftTest, BanachAdelicTheta.tensorTest, map_smul, Submodule.coe_smul, smul_smul]
  let vector : data.cusp.smooth := ((families key).family ((families key).tests parameter (archimedean value))).val
  let coefficient := fun coset => (boxes key).coefficients coset *
    RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale (boxes key).scale) coset.out (finite value)
  have sumEquality := Finset.sum_smul (s := (Finset.univ : Finset (boxes key).indices))
    (f := fun coset => coefficient coset.val) (x := vector)
  exact sumEquality.symm.trans (congrArg (fun scalar : ℂ => scalar • vector)
    (Finset.sum_coe_sort (boxes key).indices coefficient))

end Assembly

theorem finite_adelicFrame (point : IntegralFiniteGL) (value : Rectangular ℝ) :
    finite (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
      embedding (CompactFiniteFrames.frame point) := by
  apply Matrix.ext
  intro row column
  exact congrArg Prod.snd (adelicFrame_apply point value row column)

theorem archimedean_adelicFrame (point : IntegralFiniteGL) (value : Rectangular ℝ) :
    archimedean (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
      coordinateEquiv value := by
  apply congrArg coordinateEquiv
  apply Matrix.ext
  intro row column
  exact congrArg Prod.fst (adelicFrame_apply point value row column)

theorem exists_integrable_interpolation {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      (∀ (parameter : ℂ) (point : AdelicGL), (1 - (degree : ℝ)) / 2 < parameter.re →
        MeasureTheory.Integrable (VectorGodement.integrand data (test parameter) parameter point) BinaryHaar.measure) ∧
      ∀ parameter (point : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
        test parameter (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
          cutoff value • profile (flat.1 parameter)
            (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) := by
  choose families image using fun key : Key flat =>
    exists_realFamily flat (representative flat key) cutoff smooth compact supported
  choose boxes boxValue using fun key : Key flat => exists_boxes flat key
  refine ⟨test data families boxes, continuation data families boxes, continues data families boxes,
    test_integrable data families boxes, ?_⟩
  intro parameter point value fullRank
  rw [test_eq, finite_adelicFrame, archimedean_adelicFrame]
  simp only [boxValue, image, LinearEquiv.symm_apply_apply]
  let selected : Key flat := ⟨profileKey flat point, ⟨point, rfl⟩⟩
  rw [Finset.sum_eq_single selected]
  · have keyEquality := congrFun (congrFun (representative_key flat selected) parameter) ⟨value, fullRank⟩
    change profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding
      (representative flat selected)) value) =
        profile (flat.1 parameter) (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) at keyEquality
    simp only [selected, ite_true, one_smul, keyEquality]
  · intro key _ different
    have unequal : profileKey flat point ≠ key.val := by
      intro equality
      exact different (Subtype.ext equality.symm)
    simp only [ite_eq_right unequal, zero_smul]
  · simp

theorem exists_interpolation {degree : ℕ} {data : InducingData degree} {sectionFunction : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data sectionFunction)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ test : ℂ → Rectangular Adeles → data.cusp.smooth, ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data (test parameter) parameter point) continuation ∧
      ∀ parameter (point : IntegralFiniteGL) (value : Rectangular ℝ), FullRank value →
        test parameter (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) =
          cutoff value • profile (flat.1 parameter)
            (adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) value) := by
  obtain ⟨test, continuation, continues, _, interpolation⟩ :=
    exists_integrable_interpolation flat cutoff smooth compact supported
  exact ⟨test, continuation, continues, interpolation⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfileInterpolation
