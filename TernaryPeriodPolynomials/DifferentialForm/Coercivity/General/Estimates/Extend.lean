module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hilbert
public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedTarget

@[expose] public section


/-! # General coercivity, Tier B: bounded extension of core operators to the completion

A linear map between spaces of compactly supported equivariant forms that is bounded for the `L²`
norms extends to the completions (`hext`), with the same bound.  A uniformly bounded sequence of
operators converging on a dense set converges everywhere (`exists_tendsto_of_dense`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open Filter Topology TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric

/-- A uniformly bounded sequence of operators converging on a dense set converges everywhere. -/
theorem exists_tendsto_of_dense {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : ℕ → E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) {D : Set E} (hD : Dense D)
    (hconv : ∀ x ∈ D, ∃ y, Tendsto (fun j => T j x) atTop (𝓝 y)) (x : E) :
    ∃ y, Tendsto (fun j => T j x) atTop (𝓝 y) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hpos : 0 < ε / (4 * (C + 1)) := by positivity
  obtain ⟨x', hx'D, hx'⟩ := Metric.mem_closure_iff.mp (hD x) _ hpos
  obtain ⟨y, hy⟩ := hconv x' hx'D
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hy.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, fun m hm l hl => ?_⟩
  have h1 : ∀ j, dist (T j x) (T j x') ≤ C * (ε / (4 * (C + 1))) := by
    intro j
    rw [dist_eq_norm, ← map_sub]
    refine ((T j).le_opNorm _).trans ?_
    have : ‖x - x'‖ ≤ ε / (4 * (C + 1)) := by
      rw [← dist_eq_norm]
      exact hx'.le
    exact mul_le_mul (hT j) this (norm_nonneg _) hC
  have h2 := hN m hm l hl
  have h3 : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc dist (T m x) (T l x)
      ≤ dist (T m x) (T m x') + dist (T m x') (T l x') + dist (T l x') (T l x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 2 + ε / 4 := by
        have := h1 m
        have := h1 l
        rw [dist_comm (T l x') (T l x)]
        linarith
    _ = ε := by ring

variable {Γ : Subgroup RealGL} [hΓ : Fact (Admissible Γ)] {n p q : ℕ}

variable (Γ n p q) in
/-- The bounded extension of an `L²`-bounded core operator to the completions. -/
def hext (L : CForm Γ n p →ₗ[ℝ] CForm Γ n q) (C : ℝ)
    (hL : ∀ a, ‖incl Γ n q (L a)‖ ≤ C * ‖incl Γ n p a‖) :
    Hilbert Γ n p →L[ℝ] Hilbert Γ n q :=
  TernaryPoly.CompactPairingCompletion.boundedTargetExtension (quotientVolume Γ)
    (pairingData Γ n p) ((incl Γ n q).comp L) C hL

theorem hext_incl (L : CForm Γ n p →ₗ[ℝ] CForm Γ n q) (C : ℝ)
    (hL : ∀ a, ‖incl Γ n q (L a)‖ ≤ C * ‖incl Γ n p a‖) (a : CForm Γ n p) :
    hext Γ n p q L C hL (incl Γ n p a) = incl Γ n q (L a) :=
  TernaryPoly.CompactPairingCompletion.boundedTargetExtension_inclusion (quotientVolume Γ)
    (pairingData Γ n p) ((incl Γ n q).comp L) C hL a

theorem norm_hext_le (L : CForm Γ n p →ₗ[ℝ] CForm Γ n q) {C : ℝ}
    (hL : ∀ a, ‖incl Γ n q (L a)‖ ≤ C * ‖incl Γ n p a‖) (x : Hilbert Γ n p) :
    ‖hext Γ n p q L C hL x‖ ≤ C * ‖x‖ := by
  have hc : IsClosed {z : Hilbert Γ n p | ‖hext Γ n p q L C hL z‖ ≤ C * ‖z‖} :=
    isClosed_le (continuous_norm.comp (hext Γ n p q L C hL).continuous)
      (continuous_const.mul continuous_norm)
  refine DenseRange.induction_on (incl_dense Γ n p) x
    (p := fun z : Hilbert Γ n p => ‖hext Γ n p q L C hL z‖ ≤ C * ‖z‖) hc ?_
  intro a
  have e : hext Γ n p q L C hL (incl Γ n p a) = incl Γ n q (L a) := hext_incl L C hL a
  exact (congrArg (fun z : Hilbert Γ n q => ‖z‖) e).trans_le (hL a)

theorem opNorm_hext_le (L : CForm Γ n p →ₗ[ℝ] CForm Γ n q) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ a, ‖incl Γ n q (L a)‖ ≤ C * ‖incl Γ n p a‖) : ‖hext Γ n p q L C hL‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_hext_le L hL)

/-- A core identity `⟪ι (L a), ι b⟫ = ⟪ι a, ι (L' b)⟫` persists for the extension in the first slot. -/
theorem inner_hext_incl (L : CForm Γ n p →ₗ[ℝ] CForm Γ n q) {C : ℝ}
    (hL : ∀ a, ‖incl Γ n q (L a)‖ ≤ C * ‖incl Γ n p a‖) (L' : CForm Γ n q → CForm Γ n p)
    (h : ∀ (a : CForm Γ n p) (b : CForm Γ n q),
      inner ℝ (incl Γ n q (L a)) (incl Γ n q b) = inner ℝ (incl Γ n p a) (incl Γ n p (L' b)))
    (x : Hilbert Γ n p) (b : CForm Γ n q) :
    inner ℝ (hext Γ n p q L C hL x) (incl Γ n q b) = inner ℝ x (incl Γ n p (L' b)) := by
  have hc : IsClosed {z : Hilbert Γ n p | inner ℝ (hext Γ n p q L C hL z) (incl Γ n q b) =
      inner ℝ z (incl Γ n p (L' b))} :=
    isClosed_eq ((hext Γ n p q L C hL).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
  refine DenseRange.induction_on (incl_dense Γ n p) x
    (p := fun z : Hilbert Γ n p => inner ℝ (hext Γ n p q L C hL z) (incl Γ n q b) =
      inner ℝ z (incl Γ n p (L' b))) hc ?_
  intro a
  have e : hext Γ n p q L C hL (incl Γ n p a) = incl Γ n q (L a) := hext_incl L C hL a
  exact (congrArg (fun z : Hilbert Γ n q => inner ℝ z (incl Γ n q b)) e).trans (h a b)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
