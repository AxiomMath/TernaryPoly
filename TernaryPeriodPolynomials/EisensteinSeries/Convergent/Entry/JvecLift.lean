module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Analytic
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.OrbitIntegral

@[expose] public section


/-!
# The smooth lift of a boundary integral of the plane seed

`exists_JvecLift`: for positive definite `Γa, Γb`, the Hilbert-space boundary integral
`∫₀¹ K_μ(γ(t), Γb-Γa) • O(τ(γ(t))) dt` of the weighted orbit `O` of a smooth finite-level vector `v` is a smooth vector
`w` whose realization at `β` is the scalar boundary integral of the realized orbit `F β` (`F` = the weighted scalar
realization).  This is `orbitIntegral_exists` for the clamped Gram segment.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory Set MvPolynomial Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The clamped Gram segment. -/
def clampSeg (x y : Mat3) (t : ℝ) : Mat3 := x + (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) • (y - x)

theorem continuous_clampSeg (x y : Mat3) : Continuous (clampSeg x y) := by
  unfold clampSeg
  exact continuous_const.add (((continuous_subtype_val.comp continuous_projIcc)).smul continuous_const)

theorem clampSeg_mem {x y : Mat3} (hx : x.PosDef) (hy : y.PosDef) (t : ℝ) : clampSeg x y t ∈ gramDomain :=
  segment_mem_gramDomain' hx hy (Set.projIcc (0 : ℝ) 1 zero_le_one t).property

theorem clampSeg_eq (x y : Mat3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampSeg x y t = x + t • (y - x) := by
  unfold clampSeg
  rw [Set.projIcc_of_mem zero_le_one ht]

theorem continuous_Kfun_clamp (n : ℕ) (μ : Fin 3 →₀ ℕ) {x y : Mat3} (hx : x.PosDef) (hy : y.PosDef) :
    Continuous (fun t : ℝ => Kfun n μ (clampSeg x y t) (y - x)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have h1 := (analyticAt_Kfun n μ (clampSeg_mem hx hy t) (y - x)).continuousAt
  have h2 : Continuous (fun t : ℝ => (clampSeg x y t, y - x)) := (continuous_clampSeg x y).prodMk continuous_const
  exact ContinuousAt.comp (g := fun p : Mat3 × Mat3 => Kfun n μ p.1 p.2)
    (f := fun t : ℝ => (clampSeg x y t, y - x)) h1 h2.continuousAt

theorem continuous_tau_clamp {x y : Mat3} (hx : x.PosDef) (hy : y.PosDef) :
    Continuous (fun t : ℝ => gramPlaneTau (clampSeg x y t)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact (analyticAt_gramPlaneTau (clampSeg_mem hx hy t)).continuousAt.comp (continuous_clampSeg x y).continuousAt

section Lift

variable (σ : CuspidalRepresentation) (stages : AnalyticScalar.ContinuousStages σ) (hw : ℤ)
  (v : σ.smooth) (fixed : v.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence)

include stages fixed

/-- **The smooth lift of a boundary integral of the plane seed.**  For positive definite `Γa, Γb` the Hilbert-space
boundary integral `∫₀¹ K_μ(γ(t), Γb-Γa) • O(τ(γ(t))) dt` of the weighted orbit of `v` is a smooth vector `w` whose
realization at `β` is the scalar boundary integral of the realized orbit `F β`. -/
theorem exists_JvecLift (n : ℕ) (μ : Fin 3 →₀ ℕ) {Γa Γb : Mat3} (ha : Γa.PosDef) (hb : Γb.PosDef) :
    ∃ w : σ.smooth, w.val = JgenInt (cuspWeightedAffineOrbit σ hw v.val) n μ Γa Γb ∧
      ∀ β, σ.realize w β = JgenInt (cuspScalarWeightedRealization σ hw v β) n μ Γa Γb := by
  obtain ⟨w, h1, h2⟩ := orbitIntegral_exists σ stages hw v fixed
    (fun t => Kfun n μ (clampSeg Γa Γb t) (Γb - Γa)) (fun t => gramPlaneTau (clampSeg Γa Γb t))
    (continuous_Kfun_clamp n μ ha hb) (continuous_tau_clamp ha hb)
    (fun t => gramPlaneTau_im_pos_of_domain (clampSeg_mem ha hb t))
  refine ⟨w, ?_, fun β => ?_⟩
  · rw [h1]
    unfold JgenInt
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [clampSeg_eq Γa Γb ht]
  · rw [h2 β]
    unfold JgenInt
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [clampSeg_eq Γa Γb ht, smul_eq_mul]

end Lift

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
