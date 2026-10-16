module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.OrbitDist
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Calculus.ChartIntegral

@[expose] public section


/-! # General coercivity, Tier B: invariantising a smoothing with a cutoff

For a compactly supported cutoff `φ` adapted to a compact subset `Q` of the orbit space, translates
of `φ` overlap boundedly, and the sum over `Γ` of `φ · g` with `g` a smooth approximation of an
invariant function has an invariant gradient controlled by that of `g` plus an error that is small
with the approximation error.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceTraceMetric
  Set Metric Filter Topology
open scoped ContDiff

variable {Γ : Subgroup RealGL}

/-- The translates of a compact set of the coordinates overlap boundedly. -/
theorem Admissible.exists_overlap_bound (h : Admissible Γ) {K : Set Coordinates}
    (hK : IsCompact K) (hKp : K ⊆ positiveCoordinates) :
    ∃ N : ℕ, ∀ x ∈ positiveCoordinates, ∀ F : Finset Γ,
      (∀ γ ∈ F, coordinateAction (γ : RealGL) x ∈ K) → F.card ≤ N := by
  classical
  have hC : IsCompact (coordinateChart.symm '' K) :=
    hK.image_of_continuousOn (coordinateChart.continuousOn_symm.mono (fun y hy => by
      simpa using hKp hy))
  have hT := h.transporters _ _ hC hC
  refine ⟨hT.toFinset.card, fun x hx F hF => ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | ⟨γ₁, hγ₁⟩
  · simp
  have hmem : ∀ γ ∈ F, γ • coordinateChart.symm x ∈ coordinateChart.symm '' K := by
    intro γ hγ
    refine ⟨coordinateAction (γ : RealGL) x, hF γ hγ, ?_⟩
    rw [coordinateAction_eq_chart (γ : RealGL) hx]
    exact coordinateChart.left_inv (by simp)
  refine Finset.card_le_card_of_injOn (fun γ => γ * γ₁⁻¹) (fun γ hγ => ?_) (fun a _ b _ hab => ?_)
  · rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine ⟨γ • coordinateChart.symm x, ⟨γ₁ • coordinateChart.symm x, hmem γ₁ hγ₁, ?_⟩,
      hmem γ hγ⟩
    show (γ * γ₁⁻¹) • (γ₁ • coordinateChart.symm x) = γ • coordinateChart.symm x
    rw [← mul_smul, inv_mul_cancel_right]
  · exact mul_right_cancel hab

theorem differentiableAt_coordinateAction (g : RealGL) {x : Coordinates}
    (hx : x ∈ positiveCoordinates) : DifferentiableAt ℝ (coordinateAction g) x :=
  (((contDiffOn_coordinateAction g) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)

theorem fderiv_comp_action {f : Coordinates → ℝ} (hf : ContDiff ℝ ∞ f) (g : RealGL)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    fderiv ℝ (fun y => f (coordinateAction g y)) x v =
      fderiv ℝ f (coordinateAction g x) (fderiv ℝ (coordinateAction g) x v) := by
  have := fderiv_comp x (hf.differentiable (by simp) (coordinateAction g x))
    (differentiableAt_coordinateAction g hx)
  exact congrArg (fun L => L v) this

theorem fderiv_term {φ g : Coordinates → ℝ} (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g)
    (γ : RealGL) {x : Coordinates} (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    fderiv ℝ (fun y => φ (coordinateAction γ y) * g (coordinateAction γ y)) x v =
      φ (coordinateAction γ x) * fderiv ℝ g (coordinateAction γ x) (fderiv ℝ (coordinateAction γ) x v) +
        g (coordinateAction γ x) * fderiv ℝ φ (coordinateAction γ x) (fderiv ℝ (coordinateAction γ) x v) := by
  have h1 : DifferentiableAt ℝ (fun y => φ (coordinateAction γ y)) x :=
    (hφ.differentiable (by simp) _).comp x (differentiableAt_coordinateAction γ hx)
  have h2 : DifferentiableAt ℝ (fun y => g (coordinateAction γ y)) x :=
    (hg.differentiable (by simp) _).comp x (differentiableAt_coordinateAction γ hx)
  rw [fderiv_fun_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_comp_action hφ γ hx, fderiv_comp_action hg γ hx]

theorem exists_fderiv_bound {K : Set Coordinates} (hK : IsCompact K)
    (hKp : K ⊆ positiveCoordinates) {φ : Coordinates → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ y ∈ K, ∀ w : Coordinates,
      |fderiv ℝ φ y w| ≤ Λ * Real.sqrt (coordinatePair y w w) := by
  obtain ⟨l, hl, hlow⟩ := exists_pair_lower_bound hK hKp
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_fderiv (by simp)).continuousOn
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  refine ⟨|C| / Real.sqrt l, by positivity, fun y hy w => ?_⟩
  have h1 : Real.sqrt l * ‖w‖ ≤ Real.sqrt (coordinatePair y w w) := by
    calc Real.sqrt l * ‖w‖ = Real.sqrt (l * ‖w‖ ^ 2) := by
          rw [Real.sqrt_mul hl.le, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ _ := Real.sqrt_le_sqrt (hlow y hy w)
  have h2 : |fderiv ℝ φ y w| ≤ |C| * ‖w‖ :=
    (Real.norm_eq_abs _ ▸ (fderiv ℝ φ y).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right ((hC y hy).trans (le_abs_self C)) (norm_nonneg _))
  refine h2.trans ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ hsl]
  calc |C| * ‖w‖ * Real.sqrt l = |C| * (Real.sqrt l * ‖w‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

/-- The derivative of the invariantised smoothing, in the invariant metric. -/
theorem fderiv_cutoffSum_bound {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {g m : Coordinates → ℝ} (hg : ContDiff ℝ ∞ g)
    {L δ Λ : ℝ} {Nn : ℕ}
    (hmInv : ∀ γ : Γ, ∀ y ∈ positiveCoordinates, m (coordinateAction (γ : RealGL) y) = m y)
    (hgm : ∀ y ∈ tsupport φ, |g y - m y| ≤ δ)
    (hgd : ∀ y ∈ tsupport φ, ∀ w : Coordinates,
      |fderiv ℝ g y w| ≤ (1 + δ) * L * Real.sqrt (coordinatePair y w w))
    (hΛ : ∀ y ∈ tsupport φ, ∀ w : Coordinates,
      |fderiv ℝ φ y w| ≤ Λ * Real.sqrt (coordinatePair y w w))
    (hN : ∀ x ∈ positiveCoordinates, ∀ F : Finset Γ,
      (∀ γ ∈ F, coordinateAction (γ : RealGL) x ∈ tsupport φ) → F.card ≤ Nn)
    (hδ : 0 ≤ δ) (hΛ0 : 0 ≤ Λ)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (hxQ : coordProj Γ x ∈ Q) (v : Coordinates) :
    |fderiv ℝ (cutoffSum Γ (fun y => φ y * g y)) x v| ≤
      ((1 + δ) * L + Nn * δ * Λ) * Real.sqrt (coordinatePair x v v) := by
  classical
  obtain ⟨N, hN1, A, hNΩ, hzero, hsum⟩ := hφ.localPartition hx hxQ
  have hloc : cutoffSum Γ (fun y => φ y * g y) =ᶠ[𝓝 x]
      fun y => ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) y) * g (coordinateAction (γ : RealGL) y) := by
    filter_upwards [hN1] with y hy
    unfold cutoffSum
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hnA
    exact hγ (by simp [hzero γ hnA y hy])
  have hdiff : ∀ γ ∈ A, DifferentiableAt ℝ
      (fun y => φ (coordinateAction (γ : RealGL) y) * g (coordinateAction (γ : RealGL) y)) x := by
    intro γ _
    exact ((hφ.smooth.differentiable (by simp) _).comp x (differentiableAt_coordinateAction _ hx)).mul
      ((hg.differentiable (by simp) _).comp x (differentiableAt_coordinateAction _ hx))
  have hdφ : ∀ γ ∈ A, DifferentiableAt ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x := by
    intro γ _
    exact (hφ.smooth.differentiable (by simp) _).comp x (differentiableAt_coordinateAction _ hx)
  -- the sum of the differentials of the translates of the cutoff vanishes
  have hS3 : ∑ γ ∈ A, fderiv ℝ φ (coordinateAction (γ : RealGL) x)
      (fderiv ℝ (coordinateAction (γ : RealGL)) x v) = 0 := by
    have h1 : ∀ γ ∈ A, fderiv ℝ φ (coordinateAction (γ : RealGL) x)
        (fderiv ℝ (coordinateAction (γ : RealGL)) x v) =
        fderiv ℝ (fun y => φ (coordinateAction (γ : RealGL) y)) x v :=
      fun γ _ => (fderiv_comp_action hφ.smooth (γ : RealGL) hx v).symm
    rw [Finset.sum_congr rfl h1, ← sum_apply, ← fderiv_fun_sum hdφ]
    have he : (fun y => ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hN1] with y hy using hsum y hy
    rw [he.fderiv_eq, fderiv_const_apply]
    rfl
  set P := Real.sqrt (coordinatePair x v v) with hP
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hpair : ∀ γ : Γ, coordinatePair (coordinateAction (γ : RealGL) x)
      (fderiv ℝ (coordinateAction (γ : RealGL)) x v) (fderiv ℝ (coordinateAction (γ : RealGL)) x v) =
      coordinatePair x v v := fun γ => coordinatePair_fderiv_invariant _ x hx v v
  -- bounds on the individual terms
  have hb1 : ∀ γ ∈ A, |φ (coordinateAction (γ : RealGL) x) *
      fderiv ℝ g (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v)| ≤
      φ (coordinateAction (γ : RealGL) x) * ((1 + δ) * L * P) := by
    intro γ _
    by_cases hγ : coordinateAction (γ : RealGL) x ∈ tsupport φ
    · rw [abs_mul, abs_of_nonneg (hφ.nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (hφ.nonneg _)
      have := hgd _ hγ (fderiv ℝ (coordinateAction (γ : RealGL)) x v)
      rwa [hpair γ] at this
    · rw [image_eq_zero_of_notMem_tsupport hγ]
      simp
  have hb2 : ∀ γ ∈ A, |(g (coordinateAction (γ : RealGL) x) - m x) *
      fderiv ℝ φ (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v)| ≤
      if coordinateAction (γ : RealGL) x ∈ tsupport φ then δ * (Λ * P) else 0 := by
    intro γ _
    by_cases hγ : coordinateAction (γ : RealGL) x ∈ tsupport φ
    · rw [ite_eq_left hγ, abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) hδ
      · have := hgm _ hγ
        rwa [hmInv γ x hx] at this
      · have := hΛ _ hγ (fderiv ℝ (coordinateAction (γ : RealGL)) x v)
        rwa [hpair γ] at this
    · rw [ite_eq_right hγ, fderiv_of_notMem_tsupport ℝ hγ]
      simp
  have hterm : ∀ γ ∈ A, fderiv ℝ
      (fun y => φ (coordinateAction (γ : RealGL) y) * g (coordinateAction (γ : RealGL) y)) x v =
      φ (coordinateAction (γ : RealGL) x) *
        fderiv ℝ g (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v) +
      (g (coordinateAction (γ : RealGL) x) - m x) *
        fderiv ℝ φ (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v) +
      m x * fderiv ℝ φ (coordinateAction (γ : RealGL) x)
        (fderiv ℝ (coordinateAction (γ : RealGL)) x v) := by
    intro γ _
    rw [fderiv_term hφ.smooth hg (γ : RealGL) hx v]
    ring
  rw [hloc.fderiv_eq, fderiv_fun_sum hdiff, sum_apply,
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hS3, mul_zero, add_zero]
  have hS1 : |∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) *
      fderiv ℝ g (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v)| ≤
      (1 + δ) * L * P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb1).trans ?_)
    rw [← Finset.sum_mul, hsum x (mem_of_mem_nhds hN1), one_mul]
  have hS2 : |∑ γ ∈ A, (g (coordinateAction (γ : RealGL) x) - m x) *
      fderiv ℝ φ (coordinateAction (γ : RealGL) x) (fderiv ℝ (coordinateAction (γ : RealGL)) x v)| ≤
      Nn * δ * Λ * P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb2).trans ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((A.filter fun γ : Γ => coordinateAction (γ : RealGL) x ∈ tsupport φ).card : ℝ) ≤ Nn :=
      Nat.cast_le.mpr (hN x hx _ (fun γ hγ => (Finset.mem_filter.mp hγ).2))
    have : 0 ≤ δ * (Λ * P) := mul_nonneg hδ (mul_nonneg hΛ0 hP0)
    calc _ ≤ (Nn : ℝ) * (δ * (Λ * P)) := mul_le_mul_of_nonneg_right hcard this
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (1 + δ) * L * P + Nn * δ * Λ * P := add_le_add hS1 hS2
    _ = _ := by ring

/-- Away from the lift of `Q`, where the target vanishes, the invariantised smoothing is small. -/
theorem abs_cutoffSum_le (h : Admissible Γ) {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {g m : Coordinates → ℝ} {δ P0 : ℝ} {Nn : ℕ} (hδ : 0 ≤ δ)
    (hmInv : ∀ γ : Γ, ∀ y ∈ positiveCoordinates, m (coordinateAction (γ : RealGL) y) = m y)
    (hgm : ∀ y ∈ tsupport φ, |g y - m y| ≤ δ) (hP0 : ∀ y, φ y ≤ P0)
    (hN : ∀ x ∈ positiveCoordinates, ∀ F : Finset Γ,
      (∀ γ ∈ F, coordinateAction (γ : RealGL) x ∈ tsupport φ) → F.card ≤ Nn)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (hm0 : m x = 0) :
    |cutoffSum Γ (fun y => φ y * g y) x| ≤ Nn * P0 * δ := by
  classical
  have hP00 : 0 ≤ P0 := (hφ.nonneg x).trans (hP0 x)
  have hc : HasCompactSupport (fun y => φ y * g y) := hφ.compactSupport.mul_right
  have hs : tsupport (fun y => φ y * g y) ⊆ positiveCoordinates :=
    (tsupport_mul_subset_left).trans hφ.tsupport_subset
  have hfin := h.cutoffSum_finite hc hs hx
  unfold cutoffSum
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  have hmem : ∀ γ ∈ hfin.toFinset, coordinateAction (γ : RealGL) x ∈ tsupport φ := by
    intro γ hγ
    have := hfin.mem_toFinset.mp hγ
    exact subset_tsupport φ (left_ne_zero_of_mul this)
  have hb : ∀ γ ∈ hfin.toFinset, |φ (coordinateAction (γ : RealGL) x) *
      g (coordinateAction (γ : RealGL) x)| ≤ P0 * δ := by
    intro γ hγ
    have hK := hmem γ hγ
    have h1 : |g (coordinateAction (γ : RealGL) x)| ≤ δ := by
      have := hgm _ hK
      rw [hmInv γ x hx, hm0, sub_zero] at this
      exact this
    rw [abs_mul, abs_of_nonneg (hφ.nonneg _)]
    exact mul_le_mul (hP0 _) h1 (abs_nonneg _) hP00
  have hcard : (hfin.toFinset.card : ℝ) ≤ Nn := Nat.cast_le.mpr (hN x hx _ hmem)
  calc _ ≤ ∑ γ ∈ hfin.toFinset, |φ (coordinateAction (γ : RealGL) x) *
        g (coordinateAction (γ : RealGL) x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _γ ∈ hfin.toFinset, P0 * δ := Finset.sum_le_sum hb
    _ = hfin.toFinset.card * (P0 * δ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Nn * (P0 * δ) := by
        exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hP00 hδ)
    _ = _ := by ring

/-- Over the lift of `Q`, where the target is `1`, the invariantised smoothing is within `δ` of `1`. -/
theorem abs_cutoffSum_sub_one_le {Q : Set (OrbitSpace Γ)} {φ : Coordinates → ℝ}
    (hφ : CutoffData Γ Q φ) {g m : Coordinates → ℝ} {δ : ℝ}
    (hmInv : ∀ γ : Γ, ∀ y ∈ positiveCoordinates, m (coordinateAction (γ : RealGL) y) = m y)
    (hgm : ∀ y ∈ tsupport φ, |g y - m y| ≤ δ)
    {x : Coordinates} (hx : x ∈ positiveCoordinates) (hxQ : coordProj Γ x ∈ Q) (hm1 : m x = 1) :
    |cutoffSum Γ (fun y => φ y * g y) x - 1| ≤ δ := by
  classical
  obtain ⟨N, hN1, A, hNΩ, hzero, hsum⟩ := hφ.localPartition hx hxQ
  have hxN := mem_of_mem_nhds hN1
  have hc : cutoffSum Γ (fun y => φ y * g y) x =
      ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) * g (coordinateAction (γ : RealGL) x) := by
    unfold cutoffSum
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hnA
    exact hγ (by simp [hzero γ hnA x hxN])
  have hone := hsum x hxN
  have e : cutoffSum Γ (fun y => φ y * g y) x - 1 = ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) *
      (g (coordinateAction (γ : RealGL) x) - 1) := by
    have h2 : ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) *
        (g (coordinateAction (γ : RealGL) x) - 1) =
        ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) * g (coordinateAction (γ : RealGL) x) -
          ∑ γ ∈ A, φ (coordinateAction (γ : RealGL) x) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun γ _ => by ring
    rw [h2, hc, hone]
  have hb : ∀ γ ∈ A, |φ (coordinateAction (γ : RealGL) x) *
      (g (coordinateAction (γ : RealGL) x) - 1)| ≤ φ (coordinateAction (γ : RealGL) x) * δ := by
    intro γ _
    by_cases hγ : coordinateAction (γ : RealGL) x ∈ tsupport φ
    · rw [abs_mul, abs_of_nonneg (hφ.nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (hφ.nonneg _)
      have := hgm _ hγ
      rwa [hmInv γ x hx, hm1] at this
    · rw [image_eq_zero_of_notMem_tsupport hγ]
      simp
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb).trans ?_)
  rw [← Finset.sum_mul, hone, one_mul]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
