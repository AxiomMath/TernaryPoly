module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Schwartz
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.SchwartzBounds
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# Twisting a family of Schwartz tests by `exp (z * log)`

Given a holomorphic family `s ↦ tests s` of Schwartz maps supported in one compact set, and a
function `logarithm` that is smooth on an open neighbourhood of that compact set, the pointwise
products `exp (z * logarithm v) • tests s v` are again Schwartz maps, and they stay uniformly
bounded in every Schwartz seminorm as `(s, z)` ranges over a compact set. The proof multiplies by
a smooth compactly supported cutoff equal to `1` on the support, which makes the multiplier a
smooth compactly supported function of `v` whose derivatives are bounded uniformly for `z` in a
compact set, and then applies the Leibniz estimate for iterated derivatives.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.EdgeEisenstein.TwistedTests

open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source]

/-- A smooth compactly supported cutoff equal to `1` on a compact set `K` inside an open set `U`. -/
private lemma exists_cutoff (K : Set RealSpace) (hK : IsCompact K) (U : Set RealSpace)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : RealSpace → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ IsCompact (tsupport χ) ∧
      tsupport χ ⊆ U ∧ ∀ v ∈ K, χ v = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ', -, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := modelWithCornersSelf ℝ RealSpace) (n := (⊤ : ℕ∞)) hVo hK.isClosed hKV
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ := contMDiff_iff_contDiff.mp hχ'
  have hts : tsupport χ = closure V := by rw [tsupport, hsupp]
  refine ⟨χ, hχ, ?_, ?_, fun v hv => (hone v).1 hv⟩
  · rw [hts]; exact hVc
  · rw [hts]; exact hVU

/-- The cutoff-times-exponential multiplier is jointly smooth in the parameter and the point. -/
private lemma smooth_twist (χ : RealSpace → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (logarithm : RealSpace → ℝ) (domain : Set RealSpace) (domainOpen : IsOpen domain)
    (inside : tsupport χ ⊆ domain) (smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) logarithm domain) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun p : ℂ × RealSpace => (χ p.2 : ℂ) * Complex.exp (p.1 * (logarithm p.2 : ℂ))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 ∈ domain
  · have hL : ContDiffAt ℝ (↑(⊤ : ℕ∞)) logarithm p.2 :=
      smooth.contDiffAt (domainOpen.mem_nhds hp)
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : ℂ × RealSpace => (χ q.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd)
    have h2 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℂ × RealSpace => (logarithm q.2 : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (hL.comp p contDiff_snd.contDiffAt)
    have h3 : ContDiffAt ℝ (↑(⊤ : ℕ∞))
        (fun q : ℂ × RealSpace => q.1 * (logarithm q.2 : ℂ)) p :=
      contDiff_fst.contDiffAt.mul h2
    exact h1.contDiffAt.mul (Complex.contDiff_exp.contDiffAt.comp p h3)
  · have hn : p.2 ∉ tsupport χ := fun h => hp (inside h)
    have hmem : (Prod.snd ⁻¹' (tsupport χ)ᶜ : Set (ℂ × RealSpace)) ∈ nhds p :=
      continuous_snd.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hn)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with q hq
    have hq' : q.2 ∉ tsupport χ := hq
    have hzero : χ q.2 = 0 := image_eq_zero_of_notMem_tsupport hq'
    simp [hzero]

/-- Derivatives in the point of a jointly smooth family vanishing off a compact set are bounded
uniformly for the parameter in a compact set. -/
private lemma uniform_derivative_bound (M : ℂ × RealSpace → ℂ)
    (hM : ContDiff ℝ (↑(⊤ : ℕ∞)) M) (T : Set RealSpace) (hT : IsCompact T)
    (vanish : ∀ z v, v ∉ T → M (z, v) = 0) (S : Set ℂ) (hS : IsCompact S) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ v, ‖iteratedFDeriv ℝ i (fun w => M (z, w)) v‖ ≤ C := by
  have hcont : Continuous fun p : ℂ × RealSpace => iteratedFDeriv ℝ i M p :=
    hM.continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨C, hC⟩ := (hS.prod hT).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz v => ?_⟩
  by_cases hv : v ∈ T
  · refine le_trans ?_ (le_max_left C 0)
    refine le_trans ?_ (hC (z, v) ⟨hz, hv⟩)
    have hshift : ContDiff ℝ (↑(⊤ : ℕ∞)) fun u : ℂ × RealSpace => M ((z, 0) + u) :=
      hM.comp (contDiff_const.add contDiff_id)
    have hcomp : (fun w => M (z, w)) =
        (fun u : ℂ × RealSpace => M ((z, 0) + u)) ∘ (ContinuousLinearMap.inr ℝ ℂ RealSpace) := by
      funext w
      simp
    have hj : ‖ContinuousLinearMap.inr ℝ ℂ RealSpace‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [Prod.norm_def]
    have hpt : ((z, (0 : RealSpace)) + ContinuousLinearMap.inr ℝ ℂ RealSpace v) = (z, v) := by
      simp
    rw [hcomp, (ContinuousLinearMap.inr ℝ ℂ RealSpace).iteratedFDeriv_comp_right hshift v
      (mod_cast le_top), iteratedFDeriv_comp_add_left, hpt]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _k : Fin i, ‖ContinuousLinearMap.inr ℝ ℂ RealSpace‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) hj
    calc _ ≤ ‖iteratedFDeriv ℝ i M (z, v)‖ * 1 := by gcongr
      _ = _ := mul_one _
  · have hzero : iteratedFDeriv ℝ i (fun w => M (z, w)) v = 0 := by
      refine image_eq_zero_of_notMem_tsupport
        (f := iteratedFDeriv ℝ i (fun w => M (z, w))) fun h => hv ?_
      have h' := tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i h
      have hsub : Function.support (fun w => M (z, w)) ⊆ T :=
        fun w hw => by_contra fun hwT => hw (vanish z w hwT)
      exact closure_minimal hsub hT.isClosed h'
    rw [hzero, norm_zero]
    exact le_max_right _ _

/-- Twisting a holomorphic family of compactly supported Schwartz tests by `exp (z * log)`
preserves Schwartz-ness and uniform seminorm bounds on compact parameter sets. -/
theorem exists_twist (tests : ℂ → SchwartzMap RealSpace Source)
    (support : Set RealSpace) (supportCompact : IsCompact support)
    (supported : ∀ s, tsupport (fun v => tests s v) ⊆ support)
    (holomorphic : ∀ v, Differentiable ℂ (fun s => tests s v))
    (bounded : ∀ S : Set ℂ, IsCompact S → UniformSchwartzBounds.Bounded (tests '' S))
    (logarithm : RealSpace → ℝ) (domain : Set RealSpace) (domainOpen : IsOpen domain)
    (inside : support ⊆ domain) (smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) logarithm domain) :
    ∃ twisted : ℂ × ℂ → SchwartzMap RealSpace Source,
      (∀ s z v, twisted (s, z) v = Complex.exp (z * (logarithm v : ℂ)) • tests s v) ∧
      (∀ pairs : Set (ℂ × ℂ), IsCompact pairs →
        UniformSchwartzBounds.Bounded (twisted '' pairs)) := by
  have _ := holomorphic
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_cutoff support supportCompact domain domainOpen inside
  obtain ⟨M, hM⟩ : ∃ M : ℂ × RealSpace → ℂ,
      M = fun p => (χ p.2 : ℂ) * Complex.exp (p.1 * (logarithm p.2 : ℂ)) := ⟨_, rfl⟩
  have hMapp : ∀ z v, M (z, v) = (χ v : ℂ) * Complex.exp (z * (logarithm v : ℂ)) := by
    intro z v
    rw [hM]
  have hMsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) M := by
    rw [hM]
    exact smooth_twist χ hχ logarithm domain domainOpen hχU smooth
  have hvanish : ∀ z v, v ∉ tsupport χ → M (z, v) = 0 := by
    intro z v hv
    have hzero : χ v = 0 := image_eq_zero_of_notMem_tsupport hv
    rw [hMapp, hzero]
    simp
  have hmsmooth : ∀ z, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => M (z, v)) := fun z =>
    hMsmooth.comp (contDiff_const.prodMk contDiff_id)
  have hmtemp : ∀ z, Function.HasTemperateGrowth (fun v => M (z, v)) := fun z =>
    HasCompactSupport.hasTemperateGrowth
      (HasCompactSupport.intro hχc fun v hv => hvanish z v hv) (hmsmooth z)
  refine ⟨fun p => SchwartzMap.smulLeftCLM Source (fun v => M (p.2, v)) (tests p.1), ?_, ?_⟩
  · intro s z v
    show SchwartzMap.smulLeftCLM Source (fun v => M (z, v)) (tests s) v = _
    rw [SchwartzMap.smulLeftCLM_apply_apply (hmtemp z)]
    by_cases hv : v ∈ support
    · show M (z, v) • tests s v = _
      rw [hMapp, hχ1 v hv]
      simp
    · have hzero : tests s v = 0 := image_eq_zero_of_notMem_tsupport fun h => hv (supported s h)
      simp [hzero]
  · intro pairs hpairs
    have hS1 : IsCompact (Prod.fst '' pairs) := hpairs.image continuous_fst
    have hS2 : IsCompact (Prod.snd '' pairs) := hpairs.image continuous_snd
    have hb := bounded _ hS1
    intro k n
    choose Cf hCf0 hCf using
      fun i => uniform_derivative_bound M hMsmooth (tsupport χ) hχc hvanish _ hS2 i
    choose B hB0 hB using fun j => hb k j
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * B (n - i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hB0 _)
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * B (n - i), hnonneg, ?_⟩
    rintro _ ⟨⟨s, z⟩, hp, rfl⟩
    have hs : s ∈ Prod.fst '' pairs := ⟨(s, z), hp, rfl⟩
    have hz : z ∈ Prod.snd '' pairs := ⟨(s, z), hp, rfl⟩
    have hfun : ⇑(SchwartzMap.smulLeftCLM Source (fun v => M (z, v)) (tests s)) =
        fun v => M (z, v) • tests s v :=
      funext fun v => SchwartzMap.smulLeftCLM_apply_apply (hmtemp z) (tests s) v
    show SchwartzMap.seminorm ℂ k n
      (SchwartzMap.smulLeftCLM Source (fun v => M (z, v)) (tests s)) ≤ _
    refine SchwartzMap.seminorm_le_bound ℂ k n _ hnonneg fun x => ?_
    rw [hfun]
    have hgs : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => M (z, v)) := hmsmooth z
    have hfs : ContDiff ℝ (↑(⊤ : ℕ∞)) (tests s) := (tests s).smooth ⊤
    have hn : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := mod_cast le_top
    have hder := norm_iteratedFDeriv_smul_le hgs hfs x hn
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun v => M (z, v) • tests s v) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun v => M (z, v)) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (tests s) x‖ :=
          mul_le_mul_of_nonneg_left hder (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun v => M (z, v)) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (tests s) x‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * B (n - i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖iteratedFDeriv ℝ i (fun v => M (z, v)) x‖ ≤ Cf i := hCf i z hz x
          have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (tests s) x‖ ≤ B (n - i) :=
            (SchwartzMap.le_seminorm ℂ k (n - i) (tests s) x).trans
              (hB (n - i) (tests s) ⟨s, hs, rfl⟩)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

end TernaryPeriodPolynomials.EdgeEisenstein.TwistedTests
