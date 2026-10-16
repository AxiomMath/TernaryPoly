module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MaximalCompact
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Translations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealTranslations

theorem atInfinity_mul (first second : RealGL3) :
    atInfinity (first * second) = atInfinity first * atInfinity second := by
  apply InducedContinuity.adelic_ext
  · simp only [map_mul, InducedContinuity.realGroup_atInfinity]
  · simp only [map_mul, InducedContinuity.finiteGroup_atInfinity, one_mul]

theorem atFinite_atInfinity_commute (finite : FiniteGL) (real : RealGL3) :
    atFinite finite * atInfinity real = atInfinity real * atFinite finite := by
  apply InducedContinuity.adelic_ext
  · simp only [map_mul, InducedContinuity.realGroup_atFinite,
      InducedContinuity.realGroup_atInfinity, one_mul, mul_one]
  · simp only [map_mul, InducedContinuity.finiteGroup_atFinite,
      InducedContinuity.finiteGroup_atInfinity, one_mul, mul_one]

theorem compact_atInfinity (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) :
    inMaximalCompact (atInfinity real) := by
  constructor
  · simpa only [InducedContinuity.realGroup_atInfinity] using orthogonal
  · rw [InducedContinuity.finiteGroup_atInfinity]
    exact ⟨1, map_one _⟩

theorem compact_mul (first second : AdelicGL)
    (firstCompact : inMaximalCompact first) (secondCompact : inMaximalCompact second) :
    inMaximalCompact (first * second) := by
  constructor
  · rw [map_mul]
    change ((realGroup first).val * (realGroup second).val).transpose *
      ((realGroup first).val * (realGroup second).val) = 1
    rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc (realGroup first).val.transpose,
      firstCompact.1, one_mul, secondCompact.1]
  · obtain ⟨firstIntegral, firstEquality⟩ := firstCompact.2
    obtain ⟨secondIntegral, secondEquality⟩ := secondCompact.2
    refine ⟨firstIntegral * secondIntegral, ?_⟩
    rw [map_mul, map_mul, firstEquality, secondEquality]

theorem smoothCuspLift_right_real {degree arity : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (smoothLift : HasSmoothCuspLift data side parameter function) (real : RealGL3) :
    HasSmoothCuspLift data side parameter
      (fun vertices argument => function vertices (argument * atInfinity real)) := by
  classical
  intro argument
  obtain ⟨lift, smooth, equality⟩ := smoothLift argument
  let right : Fin (arity + 1) → RealGL3 := fun index => if index = Fin.last arity then real else 1
  refine ⟨fun elements => lift (fun index => elements index * right index),
    SmoothTranslations.smooth_mul_right _ smooth right, ?_⟩
  intro elements binary
  simpa only [right, Fin.castSucc_ne_last, ite_false, mul_one, ite_true, atInfinity_mul, mul_assoc]
    using equality (fun index => elements index * right index) binary

theorem induced_right_real {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) (real : RealGL3) :
    IsInduced data side parameter (fun argument => function (argument * atInfinity real)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro argument
    simpa only [atInfinity_mul, mul_assoc] using
      SmoothTranslations.smooth_mul_right _ (induced.1 argument) (fun _ => real)
  · intro level argument
    dsimp only
    rw [mul_assoc, atFinite_atInfinity_commute, ← mul_assoc, induced.2.1 level]
  · exact smoothCuspLift_right_real data side parameter _ induced.2.2.1 real
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro first second argument
        simpa only [mul_assoc] using induced.2.2.2.1 first second (argument * atInfinity real)
      · intro unit argument
        simpa only [mul_assoc] using induced.2.2.2.2.1 unit (argument * atInfinity real)
      · intro argument
        simpa only [mul_assoc] using induced.2.2.2.2.2 (argument * atInfinity real)
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro first second argument
        simpa only [mul_assoc] using induced.2.2.2.1 first second (argument * atInfinity real)
      · intro unit argument
        simpa only [mul_assoc] using induced.2.2.2.2.1 unit (argument * atInfinity real)
      · intro argument
        simpa only [mul_assoc] using induced.2.2.2.2.2 (argument * atInfinity real)

def sectionRightReal {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (real : RealGL3) :
    Module.End ℂ (SectionSpace.inducedSections data side parameter) where
  toFun sectionValue := ⟨fun argument => sectionValue.val (argument * atInfinity real),
    induced_right_real data side parameter sectionValue.val sectionValue.property real⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flat_right_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) :
    IsFlatSection data (fun parameter argument => extension parameter (argument * atInfinity real)) := by
  refine ⟨fun parameter => induced_right_real data .plane parameter _ (flat.1 parameter) real,
    fun argument parameter => flat.2.1 (argument * atInfinity real) parameter, ?_⟩
  intro parameter binary compact membership
  simpa only [mul_assoc] using flat.2.2 parameter binary (compact * atInfinity real)
    (compact_mul compact (atInfinity real) membership (compact_atInfinity real orthogonal))

def flatRightCompact {degree : ℕ} (data : InducingData degree) (real : RealGL3)
    (orthogonal : real.val.transpose * real.val = 1) :
    Module.End ℂ (EisensteinValue.flatFamilies data) where
  toFun extension := ⟨fun parameter argument => extension.val parameter (argument * atInfinity real),
    flat_right_compact data extension.val extension.property real orthogonal⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealTranslations
