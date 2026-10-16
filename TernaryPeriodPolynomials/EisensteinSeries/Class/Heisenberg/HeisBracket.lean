module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisLattice

@[expose] public section


/-!
# The Lie bracket relations of the left-invariant fields

Formalized by Claude Sonnet 5.5.

For a smooth function `u : ℝ³ → W` the fields `X₀ = ∂ₓ`, `X₁ = ∂_y + x ∂_z`, `X₂ = ∂_z` satisfy `X₀ X₁ - X₁ X₀ = X₂` and `X₂` commutes with `X₀` and `X₁`
(`Xop_comm01`, `Xop_comm02`, `Xop_comm12`).  These follow from the symmetry of the second Fréchet derivative (`ddir_comm`) and the product rule.
-/

open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Second directional derivatives in terms of the second Fréchet derivative.** -/
theorem ddir_ddir {u : Pt → W} (hu : ContDiff ℝ ∞ u) (v w : Pt) (p : Pt) :
    ddir v (ddir w u) p = fderiv ℝ (fderiv ℝ u) p v w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ u) p :=
    ((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have h := fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ : Pt => w) (x := p) hc
    (differentiableAt_const w)
  have e : (fun q => fderiv ℝ u q w) = fun q => (fderiv ℝ u q) ((fun _ : Pt => w) q) := rfl
  show fderiv ℝ (fun q => fderiv ℝ u q w) p v = _
  rw [e, h]
  simp

/-- **Directional derivatives commute** (symmetry of the second derivative). -/
theorem ddir_comm {u : Pt → W} (hu : ContDiff ℝ ∞ u) (v w : Pt) :
    ddir v (ddir w u) = ddir w (ddir v u) := by
  funext p
  rw [ddir_ddir hu, ddir_ddir hu]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) v w

theorem ddir_fst_smul {g : Pt → W} (hg : ContDiff ℝ ∞ g) (w p : Pt) :
    ddir w (fun q => q.1 • g q) p = w.1 • g p + p.1 • ddir w g p := by
  have hc : DifferentiableAt ℝ (fun q : Pt => q.1) p := differentiableAt_fst
  have hf : DifferentiableAt ℝ g p := (hg.differentiable (by simp)).differentiableAt
  have h := fderiv_smul hc hf
  show fderiv ℝ ((fun q : Pt => q.1) • g) p w = _
  rw [h]
  have hf1 : fderiv ℝ (fun q : Pt => q.1) p = ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).fderiv
  simp [ddir, hf1]
  abel

theorem Xop_comm01 {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) :
    Xop 0 (Xop 1 u) p - Xop 1 (Xop 0 u) p = Xop 2 u p := by
  have h3 : ContDiff ℝ ∞ (ddir e3 u) := by
    exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (ddir e2 u) := by
    exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfs : ContDiff ℝ ∞ (fun q : Pt => q.1 • ddir e3 u q) := contDiff_fst.smul h3
  have e1' : Xop 0 (Xop 1 u) p = ddir e1 (ddir e2 u) p + (e1.1 • ddir e3 u p + p.1 • ddir e1 (ddir e3 u) p) := by
    show ddir e1 (fun q => ddir e2 u q + q.1 • ddir e3 u q) p = _
    have := ddir_add h2 hfs e1
    rw [show (fun q => ddir e2 u q + q.1 • ddir e3 u q) = ddir e2 u + fun q => q.1 • ddir e3 u q from rfl,
      this]
    simp only [Pi.add_apply]
    rw [ddir_fst_smul h3]
  have e2' : Xop 1 (Xop 0 u) p = ddir e2 (ddir e1 u) p + p.1 • ddir e3 (ddir e1 u) p := rfl
  rw [e1', e2', ddir_comm hu e2 e1, ddir_comm hu e3 e1]
  simp [e1, Xop]
  
theorem Xop_comm02 {u : Pt → W} (hu : ContDiff ℝ ∞ u) :
    Xop 0 (Xop 2 u) = Xop 2 (Xop 0 u) := ddir_comm hu e1 e3

theorem Xop_comm12 {u : Pt → W} (hu : ContDiff ℝ ∞ u) (p : Pt) :
    Xop 1 (Xop 2 u) p = Xop 2 (Xop 1 u) p := by
  have h3 : ContDiff ℝ ∞ (ddir e3 u) := by
    exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (ddir e2 u) := by
    exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfs : ContDiff ℝ ∞ (fun q : Pt => q.1 • ddir e3 u q) := contDiff_fst.smul h3
  have e2' : Xop 2 (Xop 1 u) p = ddir e3 (ddir e2 u) p + (e3.1 • ddir e3 u p + p.1 • ddir e3 (ddir e3 u) p) := by
    show ddir e3 (fun q => ddir e2 u q + q.1 • ddir e3 u q) p = _
    have := ddir_add h2 hfs e3
    rw [show (fun q => ddir e2 u q + q.1 • ddir e3 u q) = ddir e2 u + fun q => q.1 • ddir e3 u q from rfl,
      this]
    simp only [Pi.add_apply]
    rw [ddir_fst_smul h3]
  have e1' : Xop 1 (Xop 2 u) p = ddir e2 (ddir e3 u) p + p.1 • ddir e3 (ddir e3 u) p := rfl
  rw [e1', e2', ddir_comm hu e2 e3]
  simp [e3]

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
