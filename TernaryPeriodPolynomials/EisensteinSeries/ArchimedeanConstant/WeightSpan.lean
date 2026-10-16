module

public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.FiniteRealize
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionCohomology

@[expose] public section


/-!
# The `O(2)`-span of a weight vector

If `v` is a weight vector for the rotations, `π(r_θ) v = θ^w v`, then its reflection `π(J) v` is a
weight vector of the opposite weight. Hence the span of `v` and `π(J) v` contains every
`O(2)`-translate of `v`. Such a vector is `O(2)`-finite, so the finite-dimensional realization lemmas
of `FiniteRealize` apply to it.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.ArchimedeanConstant

variable (σ : CuspidalRepresentation)

/-- The reflection of a weight vector has the opposite weight. -/
theorem reflection_weight (v : σ.H) (w : ℤ)
    (hrot : ∀ θ : Circle, σ.π (atInfinity (binaryRotations θ)) v = (θ : ℂ) ^ w • v)
    (θ : Circle) :
    σ.π (atInfinity (binaryRotations θ)) (σ.π (atInfinity UpperHalfPlane.J) v) =
      ((θ⁻¹ : Circle) : ℂ) ^ w • σ.π (atInfinity UpperHalfPlane.J) v := by
  rw [← Module.End.mul_apply, ← map_mul, ← atInfinity_mul, binaryRotation_mul_reflection,
    atInfinity_mul, map_mul, Module.End.mul_apply, hrot, map_smul]

/-- The two-dimensional span of a weight vector and its reflection. -/
def weightSpan (v : σ.H) : Submodule ℂ σ.H :=
  Submodule.span ℂ {v, σ.π (atInfinity UpperHalfPlane.J) v}

instance (v : σ.H) : FiniteDimensional ℂ (weightSpan σ v) :=
  FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-- **`O(2)`-finiteness.** Rotations and rotations followed by the reflection keep a weight
vector inside `weightSpan`. -/
theorem rotation_mem_weightSpan (v : σ.H) (w : ℤ)
    (hrot : ∀ θ : Circle, σ.π (atInfinity (binaryRotations θ)) v = (θ : ℂ) ^ w • v)
    (θ : Circle) :
    σ.π (atInfinity (binaryRotations θ)) v ∈ weightSpan σ v ∧
      σ.π (atInfinity (binaryRotations θ * UpperHalfPlane.J)) v ∈ weightSpan σ v := by
  constructor
  · rw [hrot]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · rw [atInfinity_mul, map_mul, Module.End.mul_apply, reflection_weight σ v w hrot]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The span of a smooth weight vector consists of smooth vectors. -/
theorem weightSpan_le_smooth (v : σ.H) (hv : v ∈ σ.smooth) : weightSpan σ v ≤ σ.smooth := by
  apply Submodule.span_le.mpr
  intro u hu
  rcases hu with rfl | hu
  · exact hv
  · rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact σ.smooth_stable _ _ hv

end TernaryPeriodPolynomials.ArchimedeanConstant
