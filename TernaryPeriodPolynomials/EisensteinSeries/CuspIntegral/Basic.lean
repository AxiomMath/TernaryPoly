module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.AdelicReduction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragingSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.Averaging
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Level
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LineStabilizer
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeBasic

@[expose] public section


/-!
# Adelic lifts of `Γ₁(3)` cusp forms: vocabulary

Monoid-hom packaging of the three embeddings into `GL₂(𝔸)` (rational, real, finite), the level
group `K'` (second row `≡ (0, 1)` mod `3`), and the classical weight-`k` function `liftReal f`
on `GL₂(ℝ)`, normalised so that `|liftReal f r| = (Im (r • i))^(k/2) |f (r • i)|`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.CuspIntegral

/-- Integral points of `GL₂` over the integral adeles. -/
abbrev IntegralBinaryGL := GeneralLinearGroup (Fin 2) IntegralAdeles

/-- The rational embedding `GL₂(ℚ) → GL₂(𝔸)`. -/
def ratGL : BinaryRationalGL →* BinaryAdelicGL := GeneralLinearGroup.map rationalAdele

/-- The archimedean embedding `GL₂(ℝ) → GL₂(𝔸)`. -/
def infGL : BinaryRealGL →* BinaryAdelicGL := AveragingSmooth.realInclusion

/-- The finite embedding `GL₂(𝔸_f) → GL₂(𝔸)`. -/
def finGL : BinaryFiniteGL →* BinaryAdelicGL := CompactAveraging.finiteInclusion

/-- The integral embedding `GL₂(Ẑ) → GL₂(𝔸_f)`. -/
def intGL : IntegralBinaryGL →* BinaryFiniteGL := GeneralLinearGroup.map integralEmbedding

/-- Reduction modulo three `GL₂(Ẑ) → GL₂(ℤ/3)`. -/
def redGL : IntegralBinaryGL →* GeneralLinearGroup (Fin 2) (ZMod 3) :=
  GeneralLinearGroup.map integralReduction

/-- The real image of a rational matrix. -/
def realOfRat : BinaryRationalGL →* BinaryRealGL := GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- The finite image of a rational matrix. -/
def finOfRat : BinaryRationalGL →* BinaryFiniteGL :=
  GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)

theorem infGL_apply (r : BinaryRealGL) : infGL r = atInfinity r := rfl

theorem finGL_apply (k : BinaryFiniteGL) : finGL k = atFinite k := rfl

theorem infGL_finGL_comm (r : BinaryRealGL) (k : BinaryFiniteGL) :
    infGL r * finGL k = finGL k * infGL r :=
  (FiniteLevel.atFinite_atInfinity_commute k r).symm

theorem ratGL_decomp (γ : BinaryRationalGL) :
    ratGL γ = infGL (realOfRat γ) * finGL (finOfRat γ) :=
  BinaryAdelicReduction.rational_decomposition γ

/-- The level group `K' ⊆ GL₂(𝔸_f)`: images of integral matrices whose second row is `≡ (0,1)`
modulo three. -/
def levelGroup : Subgroup BinaryFiniteGL :=
  (EisensteinGraph.InnerCuspidalArithmetic.Helpers.binaryRowStabilizer.comap redGL).map intGL

theorem mem_levelGroup_iff (k : BinaryFiniteGL) :
    k ∈ levelGroup ↔ ∃ m : IntegralBinaryGL, intGL m = k ∧
      ![0, 1] ᵥ* (redGL m).val = ![0, 1] := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, rfl, hm⟩
  · rintro ⟨m, rfl, hm⟩
    exact ⟨m, hm, rfl⟩

/-- Image of `κ ∈ SL₂(ℤ)` in `GL₂(R)`. -/
abbrev slGL (R : Type*) [CommRing R] (κ : SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) R :=
  SpecialLinearGroup.mapGL R κ

/-- `Fin`-indexed standard upper unipotent in `GL₂(R)`. -/
abbrev nGL {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R := binaryUnipotent x

/-- The weight-`k` function on `GL₂(ℝ)` attached to a cusp form of `Γ₁(3)`:
`det^{k/2} j(r, i)^{-k} f(r • i)`. For `det r > 0` it is the classical lift. -/
def liftReal {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) (r : BinaryRealGL) : ℂ :=
  ((Real.sqrt |(GeneralLinearGroup.det r : ℝˣ).val| : ℝ) : ℂ) ^ k *
    UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) ^ (-k) * f (r • UpperHalfPlane.I)

/-- Decomposition `g = γ · r · k` of an adele matrix. -/
def IsDecomp (g : BinaryAdelicGL) (γ : BinaryRationalGL) (r : BinaryRealGL)
    (k : BinaryFiniteGL) : Prop :=
  0 < (GeneralLinearGroup.det r : ℝˣ).val ∧ k ∈ levelGroup ∧
    g = ratGL γ * (infGL r * finGL k)

end TernaryPeriodPolynomials.CuspIntegral
