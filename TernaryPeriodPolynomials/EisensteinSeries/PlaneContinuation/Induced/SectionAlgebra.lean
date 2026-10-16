module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FrameProfile

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra

theorem smooth_add {m k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {first second : (Fin k → GeneralLinearGroup (Fin m) ℝ) → E}
    (firstSmooth : Smooth first) (secondSmooth : Smooth second) : Smooth (first + second) :=
  firstSmooth.add secondSmooth

theorem smooth_smul {m k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {function : (Fin k → GeneralLinearGroup (Fin m) ℝ) → E}
    (smooth : Smooth function) (coefficient : ℂ) : Smooth (coefficient • function) :=
  smooth.const_smul coefficient

theorem lift_zero {degree k : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ) :
    HasSmoothCuspLift data side parameter (0 : (Fin k → RealGL3) → AdelicGL → ℂ) := by
  intro point
  refine ⟨0, contDiffOn_const, ?_⟩
  intro matrices binary
  simp

theorem lift_add {degree k : ℕ} {data : InducingData degree} {side : Side} {parameter : ℂ}
    {first second : (Fin k → RealGL3) → AdelicGL → ℂ}
    (firstLift : HasSmoothCuspLift data side parameter first)
    (secondLift : HasSmoothCuspLift data side parameter second) :
    HasSmoothCuspLift data side parameter (first + second) := by
  intro point
  obtain ⟨left, leftSmooth, leftValue⟩ := firstLift point
  obtain ⟨right, rightSmooth, rightValue⟩ := secondLift point
  refine ⟨left + right, leftSmooth.add rightSmooth, ?_⟩
  intro matrices binary
  simp only [Pi.add_apply, map_add, leftValue, rightValue, mul_add]

theorem lift_smul {degree k : ℕ} {data : InducingData degree} {side : Side} {parameter : ℂ}
    {function : (Fin k → RealGL3) → AdelicGL → ℂ}
    (lift : HasSmoothCuspLift data side parameter function) (coefficient : ℂ) :
    HasSmoothCuspLift data side parameter (coefficient • function) := by
  intro point
  obtain ⟨vector, smooth, value⟩ := lift point
  refine ⟨coefficient • vector, smooth.const_smul coefficient, ?_⟩
  intro matrices binary
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, value]
  ring

theorem induced_zero {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    IsInduced data .plane parameter 0 := by
  refine ⟨fun _ => contDiffOn_const, fun _ _ => rfl, lift_zero data .plane parameter,
    fun _ _ _ => rfl, ?_, ?_⟩
  · intro scalar point
    simp
  · intro point
    convert (cuspFunctions data.cusp).zero_mem using 1
    ext binary
    simp

theorem induced_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) :
    IsInduced data .plane parameter (first + second) := by
  refine ⟨fun point => (firstInduced.1 point).add (secondInduced.1 point), ?_,
    lift_add firstInduced.2.2.1 secondInduced.2.2.1, ?_, ?_, ?_⟩
  · intro level point
    simp only [Pi.add_apply, firstInduced.2.1, secondInduced.2.1]
  · intro a b point
    simp only [Pi.add_apply, firstInduced.2.2.2.1, secondInduced.2.2.2.1]
  · intro scalar point
    simp only [Pi.add_apply, firstInduced.2.2.2.2.1, secondInduced.2.2.2.2.1, mul_add]
  · intro point
    convert (cuspFunctions data.cusp).add_mem
      (firstInduced.2.2.2.2.2 point) (secondInduced.2.2.2.2.2 point) using 1
    ext binary
    simp only [Pi.add_apply, mul_add]

theorem induced_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function) (coefficient : ℂ) :
    IsInduced data .plane parameter (coefficient • function) := by
  refine ⟨fun point => (induced.1 point).const_smul coefficient, ?_,
    lift_smul induced.2.2.1 coefficient, ?_, ?_, ?_⟩
  · intro level point
    simp only [Pi.smul_apply, induced.2.1]
  · intro a b point
    simp only [Pi.smul_apply, induced.2.2.2.1]
  · intro scalar point
    simp only [Pi.smul_apply, smul_eq_mul, induced.2.2.2.2.1]
    ring
  · intro point
    convert (cuspFunctions data.cusp).smul_mem coefficient (induced.2.2.2.2.2 point) using 1
    ext binary
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

def inducedSpace {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    Submodule ℂ (AdelicGL → ℂ) where
  carrier := {function | IsInduced data .plane parameter function}
  zero_mem' := induced_zero data parameter
  add_mem' := induced_add
  smul_mem' := fun coefficient _ induced => induced_smul induced coefficient

theorem flat_zero {degree : ℕ} (data : InducingData degree) : IsFlatSection data 0 := by
  refine ⟨induced_zero data, fun _ _ => analyticAt_const, ?_⟩
  intro parameter binary point compact
  simp

theorem flat_add {degree : ℕ} {data : InducingData degree} {first second : ℂ → AdelicGL → ℂ}
    (firstFlat : IsFlatSection data first) (secondFlat : IsFlatSection data second) :
    IsFlatSection data (first + second) := by
  refine ⟨fun parameter => induced_add (firstFlat.1 parameter) (secondFlat.1 parameter),
    fun point parameter => (firstFlat.2.1 point parameter).add (secondFlat.2.1 point parameter), ?_⟩
  intro parameter binary point compact
  simp only [Pi.add_apply, mul_add, firstFlat.2.2 parameter binary point compact,
    secondFlat.2.2 parameter binary point compact]

theorem flat_smul {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (coefficient : ℂ) :
    IsFlatSection data (coefficient • function) := by
  refine ⟨fun parameter => induced_smul (flat.1 parameter) coefficient,
    fun point parameter => analyticAt_const.mul (flat.2.1 point parameter), ?_⟩
  intro parameter binary point compact
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ coefficient,
    flat.2.2 parameter binary point compact]

def flatSpace {degree : ℕ} (data : InducingData degree) : Submodule ℂ (ℂ → AdelicGL → ℂ) where
  carrier := {function | IsFlatSection data function}
  zero_mem' := flat_zero data
  add_mem' := flat_add
  smul_mem' := fun coefficient _ flat => flat_smul flat coefficient

theorem cuspVector_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (point : AdelicGL) :
    planeCuspVector (induced_add firstInduced secondInduced) point =
      planeCuspVector firstInduced point + planeCuspVector secondInduced point := by
  apply data.cusp.injective
  funext binary
  simp only [map_add, Pi.add_apply, realize_planeCuspVector, mul_add]

theorem cuspVector_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (coefficient : ℂ) (point : AdelicGL) :
    planeCuspVector (induced_smul induced coefficient) point = coefficient • planeCuspVector induced point := by
  apply data.cusp.injective
  funext binary
  simp only [map_smul, Pi.smul_apply, realize_planeCuspVector, smul_eq_mul]
  ring

theorem profile_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (value : Rectangular Adeles) :
    profile (induced_add firstInduced secondInduced) value =
      profile firstInduced value + profile secondInduced value := by
  unfold profile
  split_ifs
  · simp only [normalized]
    rw [cuspVector_add firstInduced secondInduced, smul_add]
  · simp

theorem profile_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (coefficient : ℂ) (value : Rectangular Adeles) :
    profile (induced_smul induced coefficient) value = coefficient • profile induced value := by
  unfold profile
  split_ifs
  · simp only [normalized]
    rw [cuspVector_smul induced coefficient, smul_comm _ coefficient]
  · simp

def profileLinear {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (value : Rectangular Adeles) :
    inducedSpace data parameter →ₗ[ℂ] data.cusp.smooth where
  toFun := fun function => profile function.property value
  map_add' := fun first second => profile_add first.property second.property value
  map_smul' := fun coefficient function => profile_smul function.property coefficient value

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
