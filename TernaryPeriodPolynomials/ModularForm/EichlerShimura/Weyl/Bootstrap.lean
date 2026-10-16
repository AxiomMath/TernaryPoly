module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Weyl.OneStep
public import TernaryPeriodPolynomials.Analysis.Compact.SmoothCutoff

@[expose] public section


/-!
# Bootstrapping: weak solutions are in every `Hk` locally

A locally square integrable weak solution `u` of `P₀ ∂₀ u + P₁ ∂₁ u + Q u = 0` on an open set `U`
(`Q` with smooth coefficients) has `η • u ∈ Hk (tsupport η) k` for every `k` and every smooth
cutoff `η` supported in `U` (`WeakSol.hk`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ESFoundations
namespace Weyl

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace ENNReal

section Closure

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem L2s.zero (K : Set ℂ) : L2s K (fun _ : ℂ => (0 : X)) :=
  ⟨(MemLp.zero : MemLp (0 : ℂ → X) 2 volume), Eventually.of_forall fun _ _ => rfl⟩

omit [CompleteSpace X] in
theorem Hk.zero (K : Set ℂ) (k : ℕ) : Hk K k (fun _ : ℂ => (0 : X)) := by
  induction k with
  | zero => exact L2s.zero K
  | succ k ih =>
    refine ⟨L2s.zero K, fun _ _ => 0, fun j φ hφ => ?_, fun _ => ih⟩
    simp

theorem Hk.sum {K : Set ℂ} (hK : IsCompact K) {k : ℕ} {ι : Type*} (s : Finset ι)
    {w : ι → ℂ → X} (h : ∀ t ∈ s, Hk K k (w t)) : Hk K k (fun z => ∑ t ∈ s, w t z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Hk.zero K k
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Hk.add hK (h a (Finset.mem_insert_self a s))
      (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

theorem Hk.restrict_support {K K' : Set ℂ} (hK : IsCompact K) (hK' : IsCompact K') :
    ∀ {k : ℕ} {w : ℂ → X}, Hk K' k w → (∀ᵐ z, z ∉ K → w z = 0) → Hk K k w := by
  intro k
  induction k with
  | zero => exact fun hw hz => ⟨hw.1, hz⟩
  | succ k ih =>
    intro w hw hz
    obtain ⟨hl, g, hg, hgk⟩ := hw
    refine ⟨⟨hl.1, hz⟩, g, hg, fun j => ih (hgk j) ?_⟩
    exact WD.zero_off hK hz (hg j) ((hgk j).l2s.integrable hK')

end Closure

section Cutoff

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {P : Fin 2 → X →L[ℝ] X}

/-- The weak equation `P u = R` on the open set `U`. -/
def WeakEqOn (U : Set ℂ) (P : Fin 2 → X →L[ℝ] X) (u R : ℂ → X) : Prop :=
  ∀ φ : ℂ → ℝ, IsTest φ → tsupport φ ⊆ U →
    ∑ j, P j (∫ z, fderiv ℝ φ z (dir j) • u z) = - ∫ z, φ z • R z

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
theorem integrable_cutoff_smul [NormedSpace ℝ X] {U : Set ℂ} {u : ℂ → X}
    (hu : LocallyIntegrableOn u U volume) {χ : ℂ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hU : tsupport χ ⊆ U) : Integrable fun z => χ z • u z := by
  have h1 : IntegrableOn u (tsupport χ) volume :=
    (hu.mono_set hU).integrableOn_isCompact hc
  have h2 : IntegrableOn (fun z => χ z • u z) (tsupport χ) volume := by
    obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hc
    exact h1.smul_of_top_right (memLp_top_of_bound hχ.aestronglyMeasurable C
      (Eventually.of_forall fun z => hC z))
  exact (integrableOn_iff_integrable_of_support_subset (fun z hz => subset_tsupport χ
    fun h0 => hz (by simp [h0]))).mp h2

theorem tsupport_fderiv_apply_subset {η : ℂ → ℝ} (e : ℂ) :
    tsupport (fun z => fderiv ℝ η z e) ⊆ tsupport η := by
  refine closure_minimal (fun z hz => ?_) isClosed_closure
  have : fderiv ℝ η z ≠ 0 := fun h0 => hz (by simp [h0])
  exact tsupport_fderiv_subset ℝ (subset_tsupport _ this)

theorem weakEqOn_cutoff {U : Set ℂ} {u R : ℂ → X} (hu : LocallyIntegrableOn u U volume)
    (hR : LocallyIntegrableOn R U volume) (h : WeakEqOn U P u R) {η : ℂ → ℝ} (hη : IsTest η)
    (hηU : tsupport η ⊆ U) :
    WeakEq P (fun z => η z • u z)
      (fun z => η z • R z + ∑ j, fderiv ℝ η z (dir j) • P j (u z)) := by
  intro φ hφ
  have hψ : IsTest fun z => φ z * η z := hφ.mul hη.1
  have hts : tsupport (fun z => φ z * η z) ⊆ U := tsupport_mul_subset_right.trans hηU
  have e := h _ hψ hts
  have hd : ∀ j z, fderiv ℝ (fun z => φ z * η z) z (dir j) =
      fderiv ℝ φ z (dir j) * η z + φ z * fderiv ℝ η z (dir j) := fun j z => by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) z) (hη.1.differentiable (by simp) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have iA : ∀ j, Integrable fun z => (fderiv ℝ φ z (dir j) * η z) • u z := fun j =>
    integrable_cutoff_smul hu ((hφ.fderiv_apply _).mul hη.continuous)
      ((hφ.fderiv_compact _).mul_right) (tsupport_mul_subset_right.trans hηU)
  have iB : ∀ j, Integrable fun z => (φ z * fderiv ℝ η z (dir j)) • u z := fun j =>
    integrable_cutoff_smul hu (hφ.continuous.mul (hη.fderiv_apply _))
      (hφ.2.mul_right) (tsupport_mul_subset_right.trans
        ((tsupport_fderiv_apply_subset (dir j)).trans hηU))
  have iC : Integrable fun z => (φ z * η z) • R z :=
    integrable_cutoff_smul hR (hφ.continuous.mul hη.continuous) hψ.2 hts
  have step : ∀ j, ∫ z, fderiv ℝ (fun z => φ z * η z) z (dir j) • u z =
      (∫ z, fderiv ℝ φ z (dir j) • (η z • u z)) + ∫ z, φ z • (fderiv ℝ η z (dir j) • u z) := by
    intro j
    have : (fun z => fderiv ℝ (fun z => φ z * η z) z (dir j) • u z) = fun z =>
        (fderiv ℝ φ z (dir j) * η z) • u z + (φ z * fderiv ℝ η z (dir j)) • u z := by
      funext z
      rw [hd, add_smul]
    rw [this, integral_add (iA j) (iB j)]
    simp only [smul_smul]
  have hPB : ∀ j, P j (∫ z, φ z • (fderiv ℝ η z (dir j) • u z)) =
      ∫ z, φ z • (fderiv ℝ η z (dir j) • P j (u z)) := fun j => by
    have i : Integrable fun z => φ z • (fderiv ℝ η z (dir j) • u z) := by
      refine (iB j).congr (Eventually.of_forall fun z => ?_)
      simp only [smul_smul]
    rw [← ContinuousLinearMap.integral_comp_comm (P j) i]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [map_smul]
  have iT : ∀ j, Integrable fun z => φ z • (fderiv ℝ η z (dir j) • P j (u z)) := fun j => by
    have i : Integrable fun z => φ z • (fderiv ℝ η z (dir j) • u z) := by
      refine (iB j).congr (Eventually.of_forall fun z => ?_)
      simp only [smul_smul]
    have := (P j).integrable_comp i
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [map_smul]
  have e' : ∑ j, P j (∫ z, fderiv ℝ φ z (dir j) • (η z • u z)) +
      ∑ j, ∫ z, φ z • (fderiv ℝ η z (dir j) • P j (u z)) = - ∫ z, (φ z * η z) • R z := by
    rw [← Finset.sum_add_distrib]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [step j, map_add, hPB j]
  have hI : ∫ z, φ z • (η z • R z + ∑ j, fderiv ℝ η z (dir j) • P j (u z)) =
      (∫ z, (φ z * η z) • R z) + ∑ j, ∫ z, φ z • (fderiv ℝ η z (dir j) • P j (u z)) := by
    have : (fun z => φ z • (η z • R z + ∑ j, fderiv ℝ η z (dir j) • P j (u z))) = fun z =>
        (φ z * η z) • R z + ∑ j, φ z • (fderiv ℝ η z (dir j) • P j (u z)) := by
      funext z
      rw [smul_add, smul_smul, Finset.smul_sum]
    rw [this, integral_add iC (integrable_finsetSum _ fun j _ => iT j), integral_finsetSum _ fun j _ => iT j]
  rw [hI, neg_add']
  exact eq_sub_of_add_eq e'

end Cutoff

theorem contDiff_of_tsupport_subset' {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf x hx).contDiffAt (hU.mem_nhds hx)
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hs ht)))

theorem tsupport_subset_of_zero_off {f : ℂ → ℝ} {K : Set ℂ} (hK : IsClosed K)
    (h : ∀ z, z ∉ K → f z = 0) : tsupport f ⊆ K :=
  closure_minimal (fun z hz => by_contra fun hzK => hz (h z hzK)) hK

section Bootstrap

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {P : Fin 2 → X →L[ℝ] X}

/-- A locally square integrable weak solution of `P u + Q u = 0` on `U`, `Q = ∑ q_s T_s`. -/
structure WeakSol (U : Set ℂ) (P : Fin 2 → X →L[ℝ] X) {ι : Type} [Fintype ι]
    (T : ι → X →L[ℝ] X) (q : ι → ℂ → ℝ) (u : ℂ → X) : Prop where
  isOpen : IsOpen U
  dirac : DiracPair P
  smooth_q : ∀ s, ContDiffOn ℝ ∞ (q s) U
  locL2 : ∀ K : Set ℂ, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K)
  eq : ∀ φ : ℂ → ℝ, IsTest φ → tsupport φ ⊆ U →
    ∑ j, P j (∫ z, fderiv ℝ φ z (dir j) • u z) = ∫ z, φ z • ∑ s, q s z • T s (u z)

namespace WeakSol

variable {U : Set ℂ} {ι : Type} [Fintype ι] {T : ι → X →L[ℝ] X} {q : ι → ℂ → ℝ} {u : ℂ → X}
  (hs : WeakSol U P T q u)
include hs

omit [CompleteSpace X] in
theorem locInt : LocallyIntegrableOn u U volume := by
  rw [locallyIntegrableOn_iff hs.isOpen.isLocallyClosed]
  intro K hKU hK
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact (hs.locL2 K hK hKU).integrable one_le_two

omit [CompleteSpace X] in
theorem l2s_cutoff {η : ℂ → ℝ} (hη : IsTest η) (hηU : tsupport η ⊆ U) :
    L2s (tsupport η) fun z => η z • u z := by
  set K := tsupport η with hK
  have hKc : IsCompact K := hη.2
  have hind : MemLp (K.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hKc.measurableSet).mpr (hs.locL2 K hKc hηU)
  have hz : ∀ z, z ∉ K → η z • u z = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  obtain ⟨C, hC⟩ := hη.continuous.bounded_above_of_compact_support hη.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have e : (fun z => η z • u z) = fun z => η z • K.indicator u z := funext fun z => by
    by_cases hzK : z ∈ K
    · simp [hzK]
    · rw [hz z hzK, indicator_of_notMem hzK, smul_zero]
  rw [e]
  refine ⟨?_, Eventually.of_forall fun z hzK => by simp [indicator_of_notMem hzK]⟩
  refine hind.of_le_mul (c := C) (hη.continuous.aestronglyMeasurable.smul hind.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun z => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (by simpa using hC z) (norm_nonneg _)

omit [CompleteSpace X] in
theorem locInt_Qu : LocallyIntegrableOn (fun z => ∑ s, q s z • T s (u z)) U volume := by
  rw [locallyIntegrableOn_iff hs.isOpen.isLocallyClosed]
  intro K hKU hK
  refine integrable_finsetSum _ fun s _ => ?_
  have hu : IntegrableOn u K volume := (hs.locInt.mono_set hKU).integrableOn_isCompact hK
  have h1 : IntegrableOn (fun z => T s (u z)) K volume := (T s).integrable_comp hu
  exact h1.continuousOn_smul ((hs.smooth_q s).continuousOn.mono hKU) hK

omit [CompleteSpace X] in
theorem locInt_R : LocallyIntegrableOn (fun z => - ∑ s, q s z • T s (u z)) U volume :=
  hs.locInt_Qu.neg

omit [CompleteSpace X] in
theorem weakEqOn : WeakEqOn U P u (fun z => - ∑ s, q s z • T s (u z)) := by
  intro φ hφ hφU
  rw [hs.eq φ hφ hφU]
  simp only [smul_neg, integral_neg, neg_neg]

theorem hk : ∀ (k : ℕ) (η : ℂ → ℝ), IsTest η → tsupport η ⊆ U →
    Hk (tsupport η) k fun z => η z • u z := by
  intro k
  induction k with
  | zero => exact fun η hη hηU => hs.l2s_cutoff hη hηU
  | succ k ih =>
    intro η hη hηU
    have hKc : IsCompact (tsupport η) := hη.2
    obtain ⟨η', hη'd, hη'c, hη'U, hη'1⟩ :=
      TernaryPoly.CompactSmoothCutoff.exists_cutoff hKc hs.isOpen hηU
    have hη' : IsTest η' := ⟨hη'd, hη'c⟩
    have hK'c : IsCompact (tsupport η') := hη'.2
    have hone : ∀ z ∈ tsupport η, η' z = 1 := fun z hz => (hη'1 z hz).self_of_nhds
    have hKK' : tsupport η ⊆ tsupport η' := fun z hz =>
      subset_tsupport η' (by rw [Function.mem_support, hone z hz]; exact one_ne_zero)
    let S : ι ⊕ Fin 2 → X →L[ℝ] X := Sum.elim T P
    let c : ι ⊕ Fin 2 → ℂ → ℝ :=
      Sum.elim (fun s z => -(η z * q s z)) (fun j z => fderiv ℝ η z (dir j))
    have hcz : ∀ t z, z ∉ tsupport η → c t z = 0 := by
      intro t z hz
      rcases t with s | j
      · simp [c, image_eq_zero_of_notMem_tsupport hz]
      · simp [c, fderiv_of_notMem_tsupport ℝ hz]
    have hcd : ∀ t, ContDiff ℝ ∞ (c t) := by
      intro t
      rcases t with s | j
      · refine contDiff_of_tsupport_subset' hs.isOpen ?_ ?_
        · exact (hη.1.contDiffOn.mul (hs.smooth_q s)).neg
        · exact (tsupport_subset_of_zero_off hKc.isClosed (hcz (Sum.inl s))).trans hηU
      · exact (hη.fderiv_test (dir j)).1
    have hsum : ∀ z, (η z • (- ∑ s, q s z • T s (u z)) + ∑ j, fderiv ℝ η z (dir j) • P j (u z)) =
        ∑ t, c t z • S t (u z) := by
      intro z
      rw [Fintype.sum_sum_type]
      simp only [c, S, Sum.elim_inl, Sum.elim_inr, smul_neg, Finset.smul_sum, smul_smul, neg_smul,
        Finset.sum_neg_distrib]
    have hW : WeakEq P (fun z => η z • u z) (fun z => ∑ t, c t z • S t (u z)) := by
      have := weakEqOn_cutoff hs.locInt hs.locInt_R hs.weakEqOn hη hηU
      simpa only [hsum] using this
    have hF : Hk (tsupport η) k fun z => ∑ t, c t z • S t (u z) := by
      have h1 : Hk (tsupport η') k fun z => η' z • u z := ih η' hη' hη'U
      refine Hk.restrict_support hKc hK'c ?_ (Eventually.of_forall fun z hz => ?_)
      · have e : (fun z => ∑ t, c t z • S t (u z)) = fun z => ∑ t, c t z • S t (η' z • u z) := by
          funext z
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases hz : z ∈ tsupport η
          · simp [hone z hz]
          · simp [hcz t z hz]
        rw [e]
        exact Hk.sum hK'c _ fun t _ => Hk.smul_smooth hK'c (Hk.clm hK'c (S t) h1) (hcd t)
      · exact Finset.sum_eq_zero fun t _ => by simp [hcz t z hz]
    exact Hk_succ_of_weakEq hs.dirac hKc k (ih η hη hηU) hF hW

end WeakSol

end Bootstrap

end Weyl
end TernaryPeriodPolynomials.Argument.ESFoundations
