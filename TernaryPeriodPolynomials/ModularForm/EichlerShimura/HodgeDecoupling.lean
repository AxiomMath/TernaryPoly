module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeReduce
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymRepSL
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgeGlobal

@[expose] public section


/-!
# Hodge decoupling

Foundation file of the unconditional Eichler--Shimura route.  Let `α dz + β dz̄` be a smooth `Sym^m`-valued one-form on the upper half plane (in
monomial coordinates), equivariant under a subgroup `Γ` of `SL(2, ℤ)`, closed and co-closed for
the Hodge metric `Hmat`, of finite `L²` norm (`fullEnergy` is integrable, the integral over the
partition of unity replacing the integral over a fundamental domain).  Then
`α = f(z) · (zX₁ - X₀)^m` and `β = conj(g(z)) · (z̄X₁ - X₀)^m` with `f`, `g` holomorphic on the
upper half plane, of weight `m + 2` for `Γ` and square integrable (`decoupling`).  The proof
combines the reduction of closed and co-closed to the pair system (`HodgeReduce`), the
transformation law of the frame components (`SymRepSL`) and the vanishing of the middle pairs
(`HodgeGlobal`).

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory Matrix
open scoped ContDiff MatrixGroups
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
open TernaryPeriodPolynomials.Argument.ESFoundations.Global

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Decoupling

variable {m : ℕ} {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}

/-- `j`-th Hodge frame component of a form with monomial coordinates `α`. -/
def comp (m : ℕ) (α : ℂ → Fin (m + 1) → ℂ) (j : Fin (m + 1)) (w : ℂ) : ℂ :=
  (frameT m w *ᵥ α w) j

theorem contDiffOn_comp {α : ℂ → Fin (m + 1) → ℂ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (fun w => α w i) U) (j : Fin (m + 1)) :
    ContDiffOn ℝ ∞ (comp m α j) U := by
  unfold comp
  simp only [Matrix.mulVec, dotProduct]
  refine ContDiffOn.sum fun i _ => ?_
  exact ((contDiffOn_frameT m j i).of_le (by simp)).mul (hα i)

theorem diffV_of_contDiffOn {α : ℂ → Fin (m + 1) → ℂ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (fun w => α w i) U) {z : ℂ} (hz : z ∈ U) : DiffV α z :=
  fun i => ((hα i).differentiableOn (by simp) z hz).differentiableAt (isOpen_U.mem_nhds hz)

theorem differentiableAt_of_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ f z)
    (h : dbar f z = 0) : DifferentiableAt ℂ f z := by
  have hI : fderiv ℝ f z I = I • fderiv ℝ f z 1 := by
    unfold dbar at h
    have h2 : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 := by
      have := mul_eq_zero.mp h
      exact this.resolve_left (by norm_num)
    have : I * fderiv ℝ f z I = -fderiv ℝ f z 1 := by linear_combination h2
    calc fderiv ℝ f z I = (-I) * (I * fderiv ℝ f z I) := by
          rw [← mul_assoc]; simp
      _ = I * fderiv ℝ f z 1 := by rw [this]; ring
  have := (differentiableWithinAt_complex_iff_differentiableWithinAt_real
    (s := Set.univ) (f := f) (x := z) (by simp)).mpr ⟨hd.differentiableWithinAt, by
      simpa [fderivWithin_univ] using hI⟩
  exact differentiableWithinAt_univ.mp this

/-- The full finite-energy density `cutoff · Σ_j y^m κ_j (|a_j|² + |b_j|²)`. -/
def fullEnergy (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ)) (m : ℕ)
    (α β : ℂ → Fin (m + 1) → ℂ) (z : ℂ) : ℝ :=
  if z ∈ U then cutoff Γ R z * ∑ j : Fin (m + 1),
    z.im ^ m * kap m j * (‖comp m α j z‖ ^ 2 + ‖comp m β j z‖ ^ 2) else 0

theorem kap_mul_choose (j : Fin (m + 1)) : kap m j * (m.choose j : ℝ) = 1 := by
  unfold kap
  have : (0 : ℝ) < (m.choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp

theorem single_le_full (α β : ℂ → Fin (m + 1) → ℂ)
    (j : Fin (m + 1)) {z : ℂ} (hz : z ∈ U) :
    cutoff Γ R z * (z.im ^ m * kap m j * (‖comp m α j z‖ ^ 2 + ‖comp m β j z‖ ^ 2)) ≤
      fullEnergy Γ R m α β z := by
  simp only [fullEnergy, hz, ite_true]
  refine mul_le_mul_of_nonneg_left ?_ (cutoff_nonneg Γ R z)
  have hy : 0 < z.im := hz
  refine Finset.single_le_sum (f := fun j : Fin (m + 1) =>
    z.im ^ m * kap m j * (‖comp m α j z‖ ^ 2 + ‖comp m β j z‖ ^ 2)) (fun i _ => ?_)
    (Finset.mem_univ j)
  have : 0 ≤ kap m i := by
    unfold kap; positivity
  positivity

theorem fullEnergy_nonneg (α β : ℂ → Fin (m + 1) → ℂ) (z : ℂ) : 0 ≤ fullEnergy Γ R m α β z := by
  unfold fullEnergy
  split_ifs with hz
  · have hy : 0 < z.im := hz
    refine mul_nonneg (cutoff_nonneg Γ R z) (Finset.sum_nonneg fun i _ => ?_)
    have : 0 ≤ kap m i := by
      unfold kap; positivity
    positivity
  · exact le_rfl

theorem aestronglyMeasurable_ite_U {f : ℂ → ℝ} (hf : ContinuousOn f U) :
    AEStronglyMeasurable (fun z => if z ∈ U then f z else 0) volume := by
  have : (fun z => if z ∈ U then f z else 0) = U.indicator f := by
    funext z; simp [Set.indicator]
  rw [this, aestronglyMeasurable_indicator_iff isOpen_U.measurableSet]
  exact hf.aestronglyMeasurable isOpen_U.measurableSet

theorem continuousOn_energy_term (hR : IsCover Γ R) {α : ℂ → Fin (m + 1) → ℂ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (fun w => α w i) U) (j : Fin (m + 1)) (c : ℝ) :
    ContinuousOn (fun z => cutoff Γ R z * (z.im ^ m * c * ‖comp m α j z‖ ^ 2)) U := by
  have h1 : ContinuousOn (cutoff Γ R) U := (contDiffOn_cutoff Γ R hR).continuousOn
  have h2 : ContinuousOn (fun z => ‖comp m α j z‖ ^ 2) U :=
    ((contDiffOn_comp hα j).continuousOn.norm).pow 2
  have h3 : ContinuousOn (fun z : ℂ => z.im ^ m * c) U :=
    ((Complex.continuous_im.pow m).mul continuous_const).continuousOn
  exact h1.mul (h3.mul h2)

/-- A single component of `α` has integrable weighted energy. -/
theorem integrable_comp_energy (hR : IsCover Γ R) {α β : ℂ → Fin (m + 1) → ℂ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (fun w => α w i) U)
    (hE : Integrable (fullEnergy Γ R m α β)) (j : Fin (m + 1)) :
    Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖comp m α j z‖ ^ 2) else 0) := by
  have hmeas := aestronglyMeasurable_ite_U (continuousOn_energy_term hR hα j 1)
  refine Integrable.mono' (hE.const_mul (m.choose j : ℝ)) (by simpa using hmeas)
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ U
  · simp only [hz, ite_true, Real.norm_eq_abs]
    have hy : 0 < z.im := hz
    have hs := single_le_full (Γ := Γ) (R := R) α β j hz
    have hk := kap_mul_choose j
    have hc : 0 ≤ cutoff Γ R z * (z.im ^ m * ‖comp m α j z‖ ^ 2) := by
      have := cutoff_nonneg Γ R z; positivity
    rw [abs_of_nonneg hc]
    have hch : (0 : ℝ) ≤ m.choose j := by positivity
    have hnb : 0 ≤ cutoff Γ R z * (z.im ^ m * kap m j * ‖comp m β j z‖ ^ 2) := by
      have := cutoff_nonneg Γ R z
      have : 0 ≤ kap m j := by unfold kap; positivity
      positivity
    calc cutoff Γ R z * (z.im ^ m * ‖comp m α j z‖ ^ 2)
        = (m.choose j : ℝ) * (cutoff Γ R z * (z.im ^ m * kap m j * ‖comp m α j z‖ ^ 2)) := by
          calc _ = (kap m j * (m.choose j : ℝ)) *
                (cutoff Γ R z * (z.im ^ m * ‖comp m α j z‖ ^ 2)) := by rw [hk, one_mul]
            _ = _ := by ring
      _ ≤ (m.choose j : ℝ) * fullEnergy Γ R m α β z := by
          refine mul_le_mul_of_nonneg_left ?_ hch
          refine le_trans ?_ hs
          nlinarith [hnb]
  · simp only [hz, ite_false, norm_zero]
    have := fullEnergy_nonneg (Γ := Γ) (R := R) α β z
    positivity

theorem fullEnergy_comm (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ))
    (α β : ℂ → Fin (m + 1) → ℂ) : fullEnergy Γ R m α β = fullEnergy Γ R m β α := by
  funext z
  unfold fullEnergy
  split_ifs with hz
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · rfl

/-- **The decoupling of a harmonic `L²` form into holomorphic and antiholomorphic parts.** -/
theorem decoupling (hR : IsCover Γ R) {α β : ℂ → Fin (m + 1) → ℂ}
    (hα : ∀ i, ContDiffOn ℝ ∞ (fun w => α w i) U) (hβ : ∀ i, ContDiffOn ℝ ∞ (fun w => β w i) U)
    (hC : ∀ z ∈ U, dbarV α z = dzV β z)
    (hCC : ∀ z ∈ U, dbarV (fun w => Hmat m w *ᵥ α w) z + dzV (fun w => Hmat m w *ᵥ β w) z = 0)
    (hAeq : ∀ γ ∈ Γ, ∀ z ∈ U, α (mob γ z) = den γ z ^ 2 • (symRep m γ *ᵥ α z))
    (hBeq : ∀ γ ∈ Γ, ∀ z ∈ U,
      β (mob γ z) = starRingEnd ℂ (den γ z ^ 2) • (symRep m γ *ᵥ β z))
    (hE : Integrable (fullEnergy Γ R m α β)) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g U ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, f (mob γ z) = den γ z ^ (m + 2) * f z) ∧
      (∀ γ ∈ Γ, ∀ z ∈ U, g (mob γ z) = den γ z ^ (m + 2) * g z) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖f z‖ ^ 2) else 0) ∧
      Integrable (fun z => if z ∈ U then cutoff Γ R z * (z.im ^ m * ‖g z‖ ^ 2) else 0) ∧
      ∀ z ∈ U, α z = f z • (fun i => frameE m z i (Fin.last m)) ∧
        β z = starRingEnd ℂ (g z) • (fun i => frameE m z i 0) := by
  have hcomp_law : ∀ (φ : ℂ → Fin (m + 1) → ℂ) (s : ℂ → ℂ) (j : Fin (m + 1)) (γ : SL(2, ℤ)),
      (∀ z ∈ U, φ (mob γ z) = s z • (symRep m γ *ᵥ φ z)) → ∀ z ∈ U,
      comp m φ j (mob γ z) = s z * (den γ z ^ (j : ℕ) *
        (starRingEnd ℂ (den γ z)) ^ (m - (j : ℕ))) * comp m φ j z := by
    intro φ s j γ h z hz
    have := frame_component_law m γ hz (s z) φ (h z hz) j
    simpa [comp, den, conj_den] using this
  have lawA : ∀ (j : Fin (m + 1)) (γ : SL(2, ℤ)), γ ∈ Γ → ∀ z ∈ U,
      comp m α j (mob γ z) = den γ z ^ 2 * (den γ z ^ (j : ℕ) *
        (starRingEnd ℂ (den γ z)) ^ (m - (j : ℕ))) * comp m α j z :=
    fun j γ hγ z hz => hcomp_law α (fun z => den γ z ^ 2) j γ (fun z hz => hAeq γ hγ z hz) z hz
  have lawB : ∀ (j : Fin (m + 1)) (γ : SL(2, ℤ)), γ ∈ Γ → ∀ z ∈ U,
      comp m β j (mob γ z) = starRingEnd ℂ (den γ z ^ 2) * (den γ z ^ (j : ℕ) *
        (starRingEnd ℂ (den γ z)) ^ (m - (j : ℕ))) * comp m β j z :=
    fun j γ hγ z hz => hcomp_law β (fun z => starRingEnd ℂ (den γ z ^ 2)) j γ
      (fun z hz => hBeq γ hγ z hz) z hz
  have hca := contDiffOn_comp hα
  have hcb := contDiffOn_comp hβ
  have hEβ : Integrable (fullEnergy Γ R m β α) volume := by rwa [fullEnergy_comm]
  have hvan : ∀ k (hk : k < m), (∀ z ∈ U, comp m α ⟨k, by omega⟩ z = 0) ∧
      (∀ z ∈ U, comp m β ⟨k + 1, by omega⟩ z = 0) := by
    intro k hk
    obtain ⟨r, hr⟩ : ∃ r, m = k + 1 + r := ⟨m - k - 1, by omega⟩
    have hpair := fun (z : ℂ) (hz : z ∈ U) => pair_system m (show 0 < z.im from hz)
      (diffV_of_contDiffOn hα hz) (diffV_of_contDiffOn hβ hz) (hC z hz) (hCC z hz) hk
    have hen : Integrable (energyDen Γ R m (comp m α ⟨k, by omega⟩)
        (comp m β ⟨k + 1, by omega⟩)) volume := by
      refine ((integrable_comp_energy hR hα hE ⟨k, by omega⟩).add
        (integrable_comp_energy hR hβ hEβ ⟨k + 1, by omega⟩)).congr
        (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ U
      · simp [energyDen, hz]; ring
      · simp [energyDen, hz]
    exact ⟨fun z hz => (middle_pair_vanish hR hr (hca ⟨k, by omega⟩) (hcb ⟨k + 1, by omega⟩)
        (fun z hz => (hpair z hz).1) (fun z hz => (hpair z hz).2)
        (fun γ hγ z hz => by simpa using lawA ⟨k, by omega⟩ γ hγ z hz)
        (fun γ hγ z hz => by simpa using lawB ⟨k + 1, by omega⟩ γ hγ z hz) hen z hz).1,
      fun z hz => (middle_pair_vanish hR hr (hca ⟨k, by omega⟩) (hcb ⟨k + 1, by omega⟩)
        (fun z hz => (hpair z hz).1) (fun z hz => (hpair z hz).2)
        (fun γ hγ z hz => by simpa using lawA ⟨k, by omega⟩ γ hγ z hz)
        (fun γ hγ z hz => by simpa using lawB ⟨k + 1, by omega⟩ γ hγ z hz) hen z hz).2⟩
  have hαz : ∀ j : Fin (m + 1), j ≠ Fin.last m → ∀ z ∈ U, comp m α j z = 0 := by
    intro j hj z hz
    have hk : (j : ℕ) < m := by
      have := j.2
      have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext (by simpa using h))
      omega
    have := (hvan j hk).1 z hz
    simpa using this
  have hβz : ∀ j : Fin (m + 1), j ≠ 0 → ∀ z ∈ U, comp m β j z = 0 := by
    intro j hj z hz
    have hjpos : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exact absurd (Fin.ext (by simpa using h)) hj
      · exact h
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
    have hkm : k < m := by have := j.2; omega
    have := (hvan k hkm).2 z hz
    have e : (⟨k + 1, by omega⟩ : Fin (m + 1)) = j := Fin.ext hk.symm
    rwa [e] at this
  have hrep : ∀ (φ : ℂ → Fin (m + 1) → ℂ) (l : Fin (m + 1)),
      (∀ j, j ≠ l → ∀ z ∈ U, comp m φ j z = 0) →
      ∀ z ∈ U, φ z = comp m φ l z • (fun i => frameE m z i l) := by
    intro φ l hl z hz
    have h1 : φ z = frameE m z *ᵥ (frameT m z *ᵥ φ z) := by
      rw [Matrix.mulVec_mulVec, frameE_mul_frameT m z hz, Matrix.one_mulVec]
    have h2 : frameT m z *ᵥ φ z = Pi.single l (comp m φ l z) := by
      funext j
      by_cases hj : j = l
      · subst hj; simp [comp]
      · simp only [Pi.single_apply, hj, ite_false]
        exact hl j hj z hz
    rw [h1, h2]
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  refine ⟨comp m α (Fin.last m), fun w => starRingEnd ℂ (comp m β 0 w), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (differentiableAt_of_dbar_eq_zero
      (((hca _).differentiableOn (by simp) z hz).differentiableAt (isOpen_U.mem_nhds hz))
      (top_holo m (show 0 < z.im from hz) (diffV_of_contDiffOn hα hz) (diffV_of_contDiffOn hβ hz)
        (hC z hz) (hCC z hz))).differentiableWithinAt
  · intro z hz
    have hd : DifferentiableAt ℝ (comp m β 0) z :=
      ((hcb 0).differentiableOn (by simp) z hz).differentiableAt (isOpen_U.mem_nhds hz)
    have hdb : dbar (fun w => starRingEnd ℂ (comp m β 0 w)) z = 0 := by
      rw [dbar_conj hd]
      have := bottom_antiholo m (show 0 < z.im from hz) (diffV_of_contDiffOn hα hz)
        (diffV_of_contDiffOn hβ hz) (hC z hz) (hCC z hz)
      have h0 : dz (comp m β 0) z = 0 := this
      rw [h0]; simp
    have hd2 : DifferentiableAt ℝ (fun w => starRingEnd ℂ (comp m β 0 w)) z :=
      (Complex.conjCLE.differentiableAt).comp z hd
    exact (differentiableAt_of_dbar_eq_zero hd2 hdb).differentiableWithinAt
  · intro γ hγ z hz
    rw [lawA (Fin.last m) γ hγ z hz]
    simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
    ring
  · intro γ hγ z hz
    show starRingEnd ℂ (comp m β 0 (mob γ z)) = _
    rw [lawB 0 γ hγ z hz]
    simp only [Fin.val_zero, pow_zero, one_mul, Nat.sub_zero, map_mul, map_pow, Complex.conj_conj]
    ring
  · exact integrable_comp_energy hR hα hE (Fin.last m)
  · refine (integrable_comp_energy hR hβ hEβ 0).congr (Filter.Eventually.of_forall fun z => ?_)
    simp
  · intro z hz
    refine ⟨hrep α (Fin.last m) hαz z hz, ?_⟩
    have := hrep β 0 hβz z hz
    rw [this]
    simp

end TernaryPeriodPolynomials.Argument.ESFoundations.Decoupling
