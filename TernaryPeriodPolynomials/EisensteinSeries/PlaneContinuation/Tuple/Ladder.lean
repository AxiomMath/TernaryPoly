module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ModeRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdmissibleRealAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleModeRestriction
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleLadder

def toSmooth {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Space data index →ₗ[ℂ] SmoothTupleOperator.Space data :=
  LinearMap.pi (fun key => (fixedMode data.cusp finiteCongruence index).subtype.comp (LinearMap.proj key))

def raising {degree : ℕ} (data : InducingData degree) : Module.End ℂ (SmoothTupleOperator.Space data) :=
  LinearMap.pi (fun key => (LieOperators.raising data.cusp).comp (LinearMap.proj key))

def lowering {degree : ℕ} (data : InducingData degree) : Module.End ℂ (SmoothTupleOperator.Space data) :=
  LinearMap.pi (fun key => (LieOperators.lowering data.cusp).comp (LinearMap.proj key))

theorem raising_mem {degree : ℕ} (data : InducingData degree) (value : SmoothTupleOperator.Space data)
    (membership : (fun key => (value key).val) ∈ ProfileTuples.admissible data) :
    (fun key => (raising data value key).val) ∈ ProfileTuples.admissible data := by
  have result := (ProfileTuples.admissible data).sub_mem
    (AdmissibleRealAction.directional_mem data value membership LieOperators.diagonalMatrix)
    ((ProfileTuples.admissible data).smul_mem Complex.I
      (AdmissibleRealAction.directional_mem data value membership LieOperators.symmetricMatrix))
  exact result

theorem lowering_mem {degree : ℕ} (data : InducingData degree) (value : SmoothTupleOperator.Space data)
    (membership : (fun key => (value key).val) ∈ ProfileTuples.admissible data) :
    (fun key => (lowering data value key).val) ∈ ProfileTuples.admissible data := by
  have result := (ProfileTuples.admissible data).add_mem
    (AdmissibleRealAction.directional_mem data value membership LieOperators.diagonalMatrix)
    ((ProfileTuples.admissible data).smul_mem Complex.I
      (AdmissibleRealAction.directional_mem data value membership LieOperators.symmetricMatrix))
  exact result

def modeRaising {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Space data index →ₗ[ℂ] Space data (index + 2) :=
  LinearMap.pi (fun key => (LadderAdmissibility.raisingMap data.cusp finiteCongruence index).comp (LinearMap.proj key))

def modeLowering {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    Space data index →ₗ[ℂ] Space data (index - 2) :=
  LinearMap.pi (fun key => (LadderAdmissibility.loweringMap data.cusp finiteCongruence index).comp (LinearMap.proj key))

theorem modeRaising_mem {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data index)
    (membership : value ∈ admissible data index) : modeRaising data index value ∈ admissible data (index + 2) :=
  raising_mem data (toSmooth data index value) membership

theorem modeLowering_mem {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data index)
    (membership : value ∈ admissible data index) : modeLowering data index value ∈ admissible data (index - 2) :=
  lowering_mem data (toSmooth data index value) membership

def admissibleRaising {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    admissible data index →ₗ[ℂ] admissible data (index + 2) :=
  (modeRaising data index).restrict (modeRaising_mem data index)

def admissibleLowering {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    admissible data index →ₗ[ℂ] admissible data (index - 2) :=
  (modeLowering data index).restrict (modeLowering_mem data index)

theorem raising_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) (scalar : ℂ)
    (casimir : ∀ vector : data.cusp.smooth, LieCasimir.casimir data.cusp vector = scalar • vector)
    (nonzero : scalar - (index : ℂ) * (index + 2) ≠ 0) : Function.Injective (modeRaising data index) := by
  intro first second equality
  funext key
  exact LadderAdmissibility.raisingMap_injective data.cusp finiteCongruence index scalar casimir nonzero (congrFun equality key)

theorem lowering_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) (scalar : ℂ)
    (casimir : ∀ vector : data.cusp.smooth, LieCasimir.casimir data.cusp vector = scalar • vector)
    (nonzero : scalar - (index : ℂ) * (index - 2) ≠ 0) : Function.Injective (modeLowering data index) := by
  intro first second equality
  funext key
  exact LadderAdmissibility.loweringMap_injective data.cusp finiteCongruence index scalar casimir nonzero (congrFun equality key)

theorem admissibleRaising_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) (scalar : ℂ)
    (casimir : ∀ vector : data.cusp.smooth, LieCasimir.casimir data.cusp vector = scalar • vector)
    (nonzero : scalar - (index : ℂ) * (index + 2) ≠ 0) : Function.Injective (admissibleRaising data index) := by
  intro first second equality
  exact Subtype.ext (raising_injective data index scalar casimir nonzero (congrArg Subtype.val equality))

theorem admissibleLowering_injective {degree : ℕ} (data : InducingData degree) (index : ℤ) (scalar : ℂ)
    (casimir : ∀ vector : data.cusp.smooth, LieCasimir.casimir data.cusp vector = scalar • vector)
    (nonzero : scalar - (index : ℂ) * (index - 2) ≠ 0) : Function.Injective (admissibleLowering data index) := by
  intro first second equality
  exact Subtype.ext (lowering_injective data index scalar casimir nonzero (congrArg Subtype.val equality))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleLadder
