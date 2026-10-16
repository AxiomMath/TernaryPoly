module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.CutoffSmooth
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Commutator
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Plateau

@[expose] public section


/-! # General coercivity, Tier B: invariant smooth cutoffs from Lipschitz cutoffs

A `Γ`-invariant Lipschitz function of the covering space supported over a compact subset `Q` of the
orbit space is replaced by a smooth `Γ`-invariant function (an `InvMult`) with the same support
condition, equal to `1` where the original is `1`, and with invariant gradient at most a universal
multiple of the Lipschitz constant: smooth approximation with the sharp Riemannian slope, averaged
over `Γ` with a cutoff partition and composed with a fixed plateau.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceTraceMetric
  TernaryPoly.SymmetricSpaceRiemannian
  Set Metric Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL}

/-- A global bound for the derivative of the fixed plateau. -/
def plateauSlope : ℝ := Classical.choose exists_cutoffPlateau_derivative_bound

theorem plateauSlope_pos : 0 < plateauSlope :=
  (Classical.choose_spec exists_cutoffPlateau_derivative_bound).1

theorem norm_fderiv_plateau_le (t : ℝ) : ‖fderiv ℝ cutoffPlateau t‖ ≤ plateauSlope :=
  (Classical.choose_spec exists_cutoffPlateau_derivative_bound).2 t

theorem exists_small_delta {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ a * δ ≤ 1 / 16 ∧ b * δ ≤ L := by
  refine ⟨min (1 / 8) (min (1 / (16 * (a + 1))) (L / (b + 1))), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  · set δ := min (1 / 8) (min (1 / (16 * (a + 1))) (L / (b + 1)))
    have h1 : δ ≤ 1 / (16 * (a + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : δ * (16 * (a + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at h1
      exact h1
    have h3 : 0 ≤ δ := le_min (by norm_num) (le_min (by positivity) (by positivity))
    nlinarith
  · set δ := min (1 / 8) (min (1 / (16 * (a + 1))) (L / (b + 1)))
    have h1 : δ ≤ L / (b + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : δ * (b + 1) ≤ L := by
      rw [le_div_iff₀ (by positivity)] at h1
      exact h1
    have h3 : 0 ≤ δ := le_min (by norm_num) (le_min (by positivity) (by positivity))
    nlinarith

theorem chart_symm_action (γ : Γ) {y : Coordinates} (hy : y ∈ positiveCoordinates) :
    coordinateChart.symm (coordinateAction (γ : RealGL) y) = γ • coordinateChart.symm y := by
  rw [coordinateAction_eq_chart _ hy]
  exact coordinateChart.left_inv (by simp)

attribute [local instance] spaceMetricSpace in
/-- **Invariantisation of a Lipschitz cutoff.**  A `Γ`-invariant `L`-Lipschitz function of the covering
space whose support lies over a compact set `Q` of the orbit space is replaced by a smooth
`Γ`-invariant function with the same support condition, equal to `1` where the original is `1`, and
whose invariant gradient is at most `3 · plateauSlope · L`. -/
theorem exists_invMult (h : Admissible Γ) {Q : Set (OrbitSpace Γ)} (hQ : IsCompact Q)
    {L : ℝ} (hL : 0 < L) {m : Space → ℝ} (hm : ∀ S T, |m S - m T| ≤ L * dist S T)
    (hinv : ∀ (γ : Γ) (S : Space), m (γ • S) = m S) (hQm : ∀ S, m S ≠ 0 → proj Γ S ∈ Q) :
    ∃ c : InvMult Γ, c.Slope (3 * plateauSlope * L) ∧
      (∀ x ∈ positiveCoordinates, c.toFun x ≠ 0 → coordProj Γ x ∈ Q) ∧
      (∀ x ∈ positiveCoordinates, m (coordinateChart.symm x) = 1 → c.toFun x = 1) := by
  obtain ⟨φ, hφ⟩ := h.exists_cutoff hQ
  have hKc : IsCompact (tsupport φ) := hφ.compactSupport
  obtain ⟨Nn, hNn⟩ := h.exists_overlap_bound hKc hφ.tsupport_subset
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_fderiv_bound hKc hφ.tsupport_subset hφ.smooth
  obtain ⟨C, hC⟩ := hφ.compactSupport.exists_bound_of_continuous hφ.smooth.continuous
  have hP0 : ∀ y, φ y ≤ |C| := fun y =>
    (le_abs_self (φ y)).trans ((Real.norm_eq_abs (φ y) ▸ hC y).trans (le_abs_self C))
  obtain ⟨δ, hδ, hδ8, hδP, hδΛ⟩ := exists_small_delta (a := Nn * |C|) (b := Nn * Λ)
    (by positivity) (by positivity) hL
  have hmInv : ∀ γ : Γ, ∀ y ∈ positiveCoordinates,
      m (coordinateChart.symm (coordinateAction (γ : RealGL) y)) = m (coordinateChart.symm y) :=
    fun γ y hy => by rw [chart_symm_action γ hy]; exact hinv γ _
  obtain ⟨g, hg, hgm, hgd⟩ := exists_smooth_slope hKc hφ.tsupport_subset hL.le hm hδ
  have hcs : HasCompactSupport (fun y => φ y * g y) := hφ.compactSupport.mul_right
  have hts : tsupport (fun y => φ y * g y) ⊆ positiveCoordinates :=
    tsupport_mul_subset_left.trans hφ.tsupport_subset
  have hc0 : ContDiffOn ℝ ∞ (cutoffSum Γ (fun y => φ y * g y)) positiveCoordinates :=
    h.contDiffOn_cutoffSum (hφ.smooth.mul hg) hcs hts
  have hsmall : ∀ x ∈ positiveCoordinates, m (coordinateChart.symm x) = 0 →
      |cutoffSum Γ (fun y => φ y * g y) x| ≤ 1 / 16 := fun x hx hm0 =>
    (abs_cutoffSum_le h hφ hδ.le (m := fun x => m (coordinateChart.symm x)) hmInv hgm hP0 hNn hx hm0).trans
      (by nlinarith)
  have hβ : ContDiff ℝ ∞ (cutoffPlateau : ℝ → ℝ) := cutoffPlateau.contDiff
  have hplat0 : ∀ t : ℝ, |t| ≤ 1 / 8 → cutoffPlateau t = 0 := fun t ht =>
    cutoffPlateau_zero (by rw [Real.dist_eq, sub_zero]; exact ht)
  have hplat1 : ∀ t : ℝ, |t - 1| ≤ 1 / 8 → cutoffPlateau t = 1 := fun t ht =>
    cutoffPlateau_one (by rw [Real.dist_eq]; exact ht)
  have hder0 : ∀ t : ℝ, |t| < 1 / 8 → fderiv ℝ cutoffPlateau t = 0 := by
    intro t ht
    have hev : (cutoffPlateau : ℝ → ℝ) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show t ∈ Metric.ball (0 : ℝ) (1 / 8) by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht)] with s hs
      exact hplat0 s (by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs; exact hs.le)
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 0
  have hvanish : ∀ x ∈ positiveCoordinates, coordProj Γ x ∉ Q →
      m (coordinateChart.symm x) = 0 := fun x _ hxQ => by
    by_contra hne
    exact hxQ (hQm _ hne)
  refine ⟨⟨fun x => cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) x), ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hβ.comp_contDiffOn hc0
  · intro γ x hx
    show cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) (coordinateAction (γ : RealGL) x)) =
      cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) x)
    rw [cutoffSum_action γ hx]
  · intro x
    exact cutoffPlateau.nonneg
  · intro x
    exact cutoffPlateau.le_one
  · intro x hx v
    have hdiff0 : DifferentiableAt ℝ (cutoffSum Γ (fun y => φ y * g y)) x :=
      ((hc0 x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
    have hchain : fderiv ℝ (fun y => cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) y)) x v =
        fderiv ℝ cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) x)
          (fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v) := by
      have := fderiv_comp x (hβ.differentiable (by simp) _) hdiff0
      exact congrArg (fun L => L v) this
    show |fderiv ℝ (fun y => cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) y)) x v| ≤ _
    rw [hchain]
    by_cases hxQ : coordProj Γ x ∈ Q
    · have hb := fderiv_cutoffSum_bound hφ hg (m := fun x => m (coordinateChart.symm x)) hmInv hgm hgd hΛ
        hNn hδ.le hΛ0 hx hxQ v
      have h1 : |fderiv ℝ cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) x)
          (fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v)| ≤ plateauSlope *
          |fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v| := by
        have := (fderiv ℝ cutoffPlateau (cutoffSum Γ (fun y => φ y * g y) x)).le_opNorm
          (fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v)
        rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
        exact this.trans (mul_le_mul_of_nonneg_right (norm_fderiv_plateau_le _) (abs_nonneg _))
      have hP0' : 0 ≤ Real.sqrt (coordinatePair x v v) := Real.sqrt_nonneg _
      have h2 : ((1 + δ) * L + Nn * δ * Λ) ≤ 3 * L := by nlinarith
      calc _ ≤ plateauSlope * |fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v| := h1
        _ ≤ plateauSlope * (((1 + δ) * L + Nn * δ * Λ) * Real.sqrt (coordinatePair x v v)) :=
            mul_le_mul_of_nonneg_left hb plateauSlope_pos.le
        _ ≤ plateauSlope * ((3 * L) * Real.sqrt (coordinatePair x v v)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hP0') plateauSlope_pos.le
        _ = _ := by ring
    · have hm0 := hvanish x hx hxQ
      have := hsmall x hx hm0
      rw [hder0 _ (lt_of_le_of_lt this (by norm_num))]
      have : 0 ≤ 3 * plateauSlope * L * Real.sqrt (coordinatePair x v v) :=
        mul_nonneg (mul_nonneg (by linarith [plateauSlope_pos]) hL.le) (Real.sqrt_nonneg _)
      simpa using this
  · intro x hx hne
    by_contra hxQ
    apply hne
    exact hplat0 _ ((hsmall x hx (hvanish x hx hxQ)).trans (by norm_num))
  · intro x hx hm1
    have hxQ : coordProj Γ x ∈ Q := by
      by_contra hxQ
      have := hvanish x hx hxQ
      rw [hm1] at this
      exact one_ne_zero this
    have := abs_cutoffSum_sub_one_le hφ (m := fun x => m (coordinateChart.symm x)) hmInv hgm hx hxQ hm1
    exact hplat1 _ (this.trans hδ8)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
