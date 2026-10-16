module

public import Mathlib

@[expose] public section


/-!
# Uniform bounds for families in a finite-dimensional space of bounded functions

If a family `k ↦ φ k` of functions on `X`, indexed by a compact space, lies in a
finite-dimensional space of bounded functions and depends continuously on `k` at every point,
then it is uniformly bounded. This is the abstract step of the `K`-finite route to the uniform cusp
bound: right translates of a `K`-finite section span a finite-dimensional space.

Original work (AxiomDeep, Claude Opus 5.5).
-/

namespace TernaryPeriodPolynomials.ArchimedeanConstant

theorem uniform_bound_of_finiteDimensional_span {X K : Type*} [TopologicalSpace K]
    [CompactSpace K] (φ : K → X → ℂ) (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k, φ k ∈ W) (hbdd : ∀ w ∈ W, ∃ C : ℝ, ∀ x, ‖w x‖ ≤ C)
    (hcont : ∀ x, Continuous fun k => φ k x) : ∃ C : ℝ, ∀ k x, ‖φ k x‖ ≤ C := by
  classical
  let bW := Module.finBasis ℂ W
  let ev : X → (W →ₗ[ℂ] ℂ) := fun x => (LinearMap.proj x).comp W.subtype
  have hker : ∀ i, ⨅ x, LinearMap.ker (ev x) ≤ LinearMap.ker (bW.coord i) := by
    intro i w hw
    have hw0 : w = 0 := by
      apply Subtype.ext
      funext x
      have := (Submodule.mem_iInf _).mp hw x
      simpa [ev] using this
    rw [hw0]
    exact (LinearMap.ker (bW.coord i)).zero_mem
  have hspan : ∀ i, bW.coord i ∈ Submodule.span ℂ (Set.range ev) := fun i =>
    FiniteDimensional.mem_span_of_iInf_ker_le_ker (hker i)
  choose c hc using fun i => (Finsupp.mem_span_range_iff_exists_finsupp).mp (hspan i)
  have hcoord : ∀ i k, bW.coord i ⟨φ k, hW k⟩ = ∑ x ∈ (c i).support, c i x * φ k x := by
    intro i k
    rw [← hc i, Finsupp.sum, LinearMap.sum_apply]
    rfl
  have hcc : ∀ i, Continuous fun k => bW.coord i ⟨φ k, hW k⟩ := by
    intro i
    simp_rw [hcoord i]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcont x)
  choose M hM using fun i => isCompact_univ.exists_bound_of_continuousOn (hcc i).continuousOn
  choose C hC using fun i => hbdd (bW i) (bW i).2
  refine ⟨∑ i, max (M i) 0 * max (C i) 0, fun k x => ?_⟩
  have hrepr := bW.sum_repr ⟨φ k, hW k⟩
  have h1 := congrFun (congrArg Subtype.val hrepr) x
  rw [Submodule.coe_sum, Finset.sum_apply] at h1
  have hx : φ k x = ∑ i, bW.repr ⟨φ k, hW k⟩ i * (bW i : X → ℂ) x := by
    calc φ k x = _ := h1.symm
      _ = _ := by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hx]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have hMi := hM i k (Set.mem_univ k)
  rw [Module.Basis.coord_apply] at hMi
  exact mul_le_mul (hMi.trans (le_max_left _ _))
    ((hC i x).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

end TernaryPeriodPolynomials.ArchimedeanConstant
