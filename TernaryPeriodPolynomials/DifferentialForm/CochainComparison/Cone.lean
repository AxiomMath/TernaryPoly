module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Natural

@[expose] public section


/-!
# The Gram cone as an open convex set with the linear action of `SL₃`

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open Set Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The open convex cone of real `3 × 3` matrices with positive definite symmetric part: `xᵀ G x > 0` for `x ≠ 0`. -/
def gramCone : Set Mat3 := {G | ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)}

theorem mem_gramCone_iff {G : Mat3} : G ∈ gramCone ↔ ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x) := Iff.rfl

theorem convex_gramCone : Convex ℝ gramCone := by
  intro G hG H hH a b ha hb hab
  rw [mem_gramCone_iff]
  intro x hx
  have h1 := (mem_gramCone_iff.1 hG) x hx
  have h2 := (mem_gramCone_iff.1 hH) x hx
  have : x ⬝ᵥ ((a • G + b • H) *ᵥ x) = a * (x ⬝ᵥ (G *ᵥ x)) + b * (x ⬝ᵥ (H *ᵥ x)) := by
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
  rw [this]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this
    simpa using h2
  · have := mul_pos ha' h1
    nlinarith [mul_nonneg hb h2.le]

theorem one_mem_gramCone : (1 : Mat3) ∈ gramCone := by
  rw [mem_gramCone_iff]
  intro x hx
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have h1 : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  simpa using lt_of_le_of_ne h0 (Ne.symm h1)

theorem gramCone_eq_sphere : gramCone = {G : Mat3 | ∀ x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1, 0 < x ⬝ᵥ (G *ᵥ x)} := by
  ext G
  rw [mem_gramCone_iff]
  constructor
  · intro h x hx
    refine h x ?_
    intro h0
    simp [h0] at hx
  · intro h x hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have := h _ hy
    have e : (‖x‖⁻¹ • x) ⬝ᵥ (G *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (G *ᵥ x)) := by
      simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this

theorem isOpen_gramCone : IsOpen gramCone := by
  rw [gramCone_eq_sphere]
  have hK : IsCompact (Metric.sphere (0 : Fin 3 → ℝ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin 3 → ℝ) 1) := isCompact_iff_compactSpace.mp hK
  let f : Mat3 × (Metric.sphere (0 : Fin 3 → ℝ) 1) → ℝ := fun p => p.2.1 ⬝ᵥ (p.1 *ᵥ p.2.1)
  have hf : Continuous f := by
    have h1 : Continuous (fun p : Mat3 × (Metric.sphere (0 : Fin 3 → ℝ) 1) => p.1) := continuous_fst
    have h2 : Continuous (fun p : Mat3 × (Metric.sphere (0 : Fin 3 → ℝ) 1) => p.2.1) :=
      continuous_subtype_val.comp continuous_snd
    have e1 : ∀ i j : Fin 3, Continuous (fun p : Mat3 × (Metric.sphere (0 : Fin 3 → ℝ) 1) => p.1 i j) :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp h1)
    have e2 : ∀ i : Fin 3, Continuous (fun p : Mat3 × (Metric.sphere (0 : Fin 3 → ℝ) 1) => p.2.1 i) :=
      fun i => (continuous_apply i).comp h2
    simp only [f, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    continuity
  have hcl : IsClosed (f ⁻¹' Iic 0) := isClosed_Iic.preimage hf
  have hmap := isClosedMap_fst_of_compactSpace (X := Mat3) (Y := Metric.sphere (0 : Fin 3 → ℝ) 1) _ hcl
  convert hmap.isOpen_compl using 1
  ext G
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, mem_preimage, mem_Iic, Prod.exists, exists_and_right,
    exists_eq_right, Subtype.exists, not_exists, not_le, f]


end TernaryPeriodPolynomials.Argument.FormCochainBridge
