module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorSolvability
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ComplexProjection

@[expose] public section


/-! Coercivity gives unreduced exactness of an unbounded Hilbert complex. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [NormedSpace ℝ G]
variable [CompleteSpace E] [CompleteSpace F]

/-- Coercivity on the intersection of the two actual domains implies every
cycle is an actual boundary. No reduced cohomology or closed-range hypothesis
is substituted for this conclusion. -/
theorem exact_of_coercive (S : E →ₗ.[ℝ] F) (T : F →ₗ.[ℝ] G)
    (hS : S.IsClosed) (hdS : Dense (S.domain : Set E)) (hT : T.IsClosed)
    (hcomplex : ∀ u : S.domain, S u ∈ kernel T)
    (C : ℝ)
    (hcoercive : ∀ x : T.domain, ∀ hx : (x : F) ∈ S†.domain,
      ‖(x : F)‖ ≤ C * (‖T x‖ + ‖S† ⟨(x : F), hx⟩‖)) :
    (kernel T : Set F) = Set.range S := by
  let K := kernel T
  let : IsClosed (K : Set F) := kernel_isClosed T hT
  apply Set.Subset.antisymm
  · intro z hz
    apply mem_range_of_adjoint_bound S hS hdS z (‖z‖ * C)
    intro y
    obtain ⟨hp, heq⟩ := adjoint_projection S hdS K hcomplex y
    let p : T.domain := ⟨K.starProjection (y : F),
      kernel_le_domain T (K.starProjection_apply_mem _)⟩
    have hp0 : T p = 0 := (coe_mem_kernel T p).mp (K.starProjection_apply_mem _)
    have hb : ‖K.starProjection (y : F)‖ ≤ C * ‖S† y‖ := by
      have h := hcoercive p hp
      simp only [hp0, norm_zero, zero_add] at h
      change ‖K.starProjection (y : F)‖ ≤ C * ‖S† ⟨K.starProjection (y : F), hp⟩‖ at h
      rwa [heq] at h
    rw [inner_projection K z (y : F) hz]
    calc ‖inner ℝ z (K.starProjection (y : F))‖
        ≤ ‖z‖ * ‖K.starProjection (y : F)‖ := norm_inner_le_norm _ _
      _ ≤ ‖z‖ * (C * ‖S† y‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (‖z‖ * C) * ‖S† y‖ := (mul_assoc _ _ _).symm
  · rintro z ⟨u, rfl⟩
    exact hcomplex u

end TernaryPoly.HilbertClosedOperator
