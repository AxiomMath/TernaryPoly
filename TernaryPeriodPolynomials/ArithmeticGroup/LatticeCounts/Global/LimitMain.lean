module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitInduction
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitFinal

@[expose] public section


/-!
# Global limit: the finite-`S` formula (4') from the line step, and the global Euler product

`finiteIdentity_of_lineStep`: if the line step holds at every prime `p ≠ 3` with the local ratio `c_p`, then `FiniteIdentity` holds with `v = F(0,0)`,
and `F(0,0) = normPower(det Z) · vhValueFull(g∞, Z)` (`globalIntegrand_zero`).  `global_integral_euler_of_lineStep` is the resulting
`∫ F = normPower(det Z)(k/2) · vhValueFull · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`; the only input is the line step (the one-place Hecke computation at a general base).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory Filter Topology Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitIntegrable
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitInduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitFinal
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)

open Classical

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMain

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem SEP_empty : SEP (∅ : Finset PIdx) = ∅ := by simp [SEP]

theorem SEP_insert (q : PIdx) (T : Finset PIdx) : SEP (insert q T) = SEP T ∪ {embP q} := by
  unfold SEP
  rw [Finset.map_insert, Finset.insert_eq, Finset.union_comm]

/-- **(4') from the line step.** -/
theorem finiteIdentity_of_lineStep (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL)
    (hint : Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))
    (hline : ∀ p : PIdx, LineStep I Z gInf (embP p) (embP_ne p)
      (globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h p.val.val) p.val)) :
    FiniteIdentity I h Z gInf (globalIntegrand I Z gInf (0, 0)) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    simp only [Uex, SEP_empty, Finset.prod_empty, mul_one]
    exact integral_empty I h hform Z hZ gInf
  | insert q T hq ih =>
    have hqT : embP q ∉ SEP T := by
      intro hm
      obtain ⟨r, hr, hre⟩ := Finset.mem_map.1 hm
      exact hq (embP.injective hre ▸ hr)
    simp only [Uex, SEP_insert]
    rw [integral_union_of_lineStep I h hform (SEP T) (SEP_ne T) (embP q) (embP_ne q) hqT Z hZ gInf hint _ (hline q),
      Finset.prod_insert hq]
    simp only [Uex] at ih
    rw [ih]
    ring

/-- **The value at the origin.** `F(0,0) = normPower(det Z) · vhValueFull(g∞, Z)`. -/
theorem globalIntegrand_zero (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    globalIntegrand I Z gInf (0, 0) =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I) * vhValueFull (-2 * I.halfWeight) h gInf Z := by
  have hz : ((0 : FiniteAwayThree), (0 : FiniteAwayThree)) ∈ UregionS (∅ : Finset FinitePlace) := by
    intro w _
    exact ⟨(OS w).zero_mem, (OS w).zero_mem⟩
  obtain ⟨X, hX, heq⟩ := globalIntegrand_absorb I h hform (∅ : Finset FinitePlace) (fun _ => 1) (fun _ => 1)
    (fun w hw => absurd hw (Finset.notMem_empty w)) (0, 0) (fun w hw => absurd hw (Finset.notMem_empty w))
    (fun w hw => absurd hw (Finset.notMem_empty w))
    (fun w hw => intGL3_LfinGLof_of_mem hz w hw) Z hZ gInf
  have hX1 : X = 1 := by
    apply gl2_ext
    intro w
    rw [hX w]
    simp
  rw [heq, hX1, one_mul]
  simp

/-- **The global integral as the Euler product, from the line step.** For `k = -2 · halfWeight > 6`, `g∞` with `det g∞ ≠ 0`, `Z` integral at every place: `F` is
integrable on `FiniteAwayThree²` and `∫ F = normPower(det Z)(k/2) · vhValueFull(g∞, Z) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)`, given the line step at every prime `≠ 3`. -/
theorem global_integral_euler_of_lineStep (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight)) (hh : IsNormalizedEigenform h)
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (hk : 6 < -2 * I.halfWeight) (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (hline : ∀ p : PIdx, LineStep I Z gInf (embP p) (embP_ne p)
      (globalOuterLocalRatio (-2 * I.halfWeight) (fourierCoeff h p.val.val) p.val)) :
    Integrable (globalIntegrand I Z gInf) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      ∫ z, globalIntegrand I Z gInf z ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) =
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I) * vhValueFull (-2 * I.halfWeight) h gInf Z *
          (LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 2) /
            LSeries (removeEulerCoefficients (fun m => fourierCoeff h m) 3) (((-2 * I.halfWeight : ℤ) : ℂ) - 1)) := by
  have hint := (globalIntegrand_integrable_tendsto I h hform hk gInf hg Z hZ).1
  obtain ⟨-, heq⟩ := global_integral_eq_outer_ratio' I h hh hform hk gInf hg Z hZ _
    (finiteIdentity_of_lineStep I h hform Z hZ gInf hint hline)
  refine ⟨hint, ?_⟩
  rw [heq, globalIntegrand_zero I h hform Z hZ gInf]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitMain
