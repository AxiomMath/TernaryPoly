module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# The arithmetic period cocycle of an Eichler cocycle

For an Eichler input `I`, the Eichler cocycle `α = I.eichlerCocycle` is a `GL₂(ℝ)`-cocycle with values
in cusp functions that are right `GL₂(Ẑ)`-invariant.  By left rationality of cusp functions and
finite-level invariance, `α h (atInfinity γ) = α h 1` for every `γ ∈ GL₂(ℤ)`
(`EichlerInput.eichlerCocycle_atInfinity_integral`).  Hence the evaluation `γ ↦ α (γ_∞) 1` is a
one-cocycle of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) (-1)`
(`EichlerInput.arithmeticPeriodCocycle`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

/-- The arithmetic action of `GL₂(ℤ)` on binary forms of degree `n + 1` with determinant twist `-1`,
with values in the forms (rather than in the carrier of the representation). -/
abbrev periodAct (n : ℕ) (γ : GeneralLinearGroup (Fin 2) ℤ) (q : Binary.HomogeneousPoly (n + 1)) :
    Binary.HomogeneousPoly (n + 1) :=
  (arithmeticBinaryRep (n + 1) (-1)).ρ γ q

/-- The coefficient action of an integral matrix, through its real image, is the arithmetic binary
representation of weight `n + 1` and determinant twist `-1`. -/
theorem binaryCoefficient_map_int (n : ℕ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (q : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) q = periodAct n γ q := by
  have matrices : GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) =
        GeneralLinearGroup.map (Int.castRingHom ℂ) γ := by
    apply Units.ext
    funext row column
    simp [GeneralLinearGroup.map_apply]
  change Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)) q =
    Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) q
  rw [matrices]

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (I : EichlerInput σ n)

/-- **Rationality of the Eichler cocycle.**  By left automorphy under `GL₂(ℚ)` and right
`GL₂(Ẑ)`-invariance, the Eichler cocycle takes the same value at `γ_∞` and at `1` for every
`γ ∈ GL₂(ℤ)`. -/
theorem eichlerCocycle_atInfinity_integral (stages : AnalyticScalar.ContinuousStages σ)
    (h : BinaryRealGL) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    I.eichlerCocycle h (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)) =
      I.eichlerCocycle h 1 := by
  have member : I.eichlerCocycle h ∈ cuspidalTensorValues σ (Binary.HomogeneousPoly (n + 1)) :=
    (cuspidalTensorValues_binary_iff σ n _).mpr (I.eichlerCocycle_binaryValues stages h)
  have fixed : (⟨I.eichlerCocycle h, member⟩ :
      cuspidalTensorValues σ (Binary.HomogeneousPoly (n + 1))) ∈
        cuspidalTensorFiniteLevel σ (Binary.HomogeneousPoly (n + 1)) := by
    intro matrix argument
    exact I.eichlerCocycle_finiteLevel stages matrix h argument
  exact cuspidalTensorFiniteLevel_integralReal σ ⟨I.eichlerCocycle h, member⟩ fixed γ

/-- The twisted action of an integral matrix on the Eichler cocycle, evaluated at the identity. -/
theorem binaryCohomologicalAction_eichlerCocycle_one (stages : AnalyticScalar.ContinuousStages σ)
    (g h : GeneralLinearGroup (Fin 2) ℤ) :
    binaryCohomologicalAction n (GeneralLinearGroup.map (Int.castRingHom ℝ) g)
        (I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) h)) 1 =
      periodAct n g (I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) h) 1) := by
  unfold binaryCohomologicalAction
  rw [normPower_binaryIntegralReal g, one_smul, one_mul,
    I.eichlerCocycle_atInfinity_integral stages, binaryCoefficient_map_int]

/-- **The arithmetic period cocycle**: `γ ↦ α (γ_∞) 1` is a one-cocycle of `GL₂(ℤ)` with values in
`arithmeticBinaryRep (n + 1) (-1)`. -/
def arithmeticPeriodCocycle (stages : AnalyticScalar.ContinuousStages σ) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) :=
  ⟨fun γ => I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    change I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) (g * h)) 1 =
      periodAct n g (I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) h) 1) +
        I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) g) 1
    have multiplicative := I.eichlerCocycle_mul stages (GeneralLinearGroup.map (Int.castRingHom ℝ) g)
      (GeneralLinearGroup.map (Int.castRingHom ℝ) h) 1
    rw [← map_mul] at multiplicative
    rw [multiplicative, I.binaryCohomologicalAction_eichlerCocycle_one stages g h]
    exact add_comm _ _⟩

theorem arithmeticPeriodCocycle_apply (stages : AnalyticScalar.ContinuousStages σ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) :
    I.arithmeticPeriodCocycle stages γ =
      I.eichlerCocycle (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1 := rfl

end EichlerInput

end TernaryPeriodPolynomials.SourceConstruction

end
