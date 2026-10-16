module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransferBounds

@[expose] public section


/-!
# The real good-line transfer is a two-cocycle

The homogeneous canonical cochain of a pointwise binary cocycle is closed on every four-vertex
configuration of real-plane points. Moving the vertices by the good-line argument and integrating
(every face is absolutely integrable for `n ≥ 5`) shows that the real good-line transfer is closed;
with its equivariance it is the homogeneous form of an inhomogeneous two-cocycle of the real
good-line stabilizer.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- **Closedness of the homogeneous canonical cochain**, along any family of plane points. -/
theorem planeHomogeneousCanonical_closed
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (hN : IsBinaryPointCocycle N) {β : Type*} (f : β → RealPlaneGroup) (y : Fin 4 → β) :
    planeHomogeneousCanonical N (fun i => f (![y 1, y 2, y 3] i)) -
        planeHomogeneousCanonical N (fun i => f (![y 0, y 2, y 3] i)) +
        planeHomogeneousCanonical N (fun i => f (![y 0, y 1, y 3] i)) -
        planeHomogeneousCanonical N (fun i => f (![y 0, y 1, y 2] i)) = 0 := by
  unfold planeHomogeneousCanonical
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  set Q : Fin 4 → RealPlaneGroup := fun i => f (y i)
  change planeAmbientRepresentation n (Q 1) (pointCanonical N ((Q 1)⁻¹ * Q 2) ((Q 2)⁻¹ * Q 3)) -
      planeAmbientRepresentation n (Q 0) (pointCanonical N ((Q 0)⁻¹ * Q 2) ((Q 2)⁻¹ * Q 3)) +
      planeAmbientRepresentation n (Q 0) (pointCanonical N ((Q 0)⁻¹ * Q 1) ((Q 1)⁻¹ * Q 3)) -
      planeAmbientRepresentation n (Q 0) (pointCanonical N ((Q 0)⁻¹ * Q 1) ((Q 1)⁻¹ * Q 2)) = 0
  set a := (Q 0)⁻¹ * Q 1
  set b := (Q 1)⁻¹ * Q 2
  set d := (Q 2)⁻¹ * Q 3
  have e := pointCanonical_cocycle hN a b d
  have hQ1 : Q 1 = Q 0 * a := by simp [a]
  have hab : (Q 0)⁻¹ * Q 2 = a * b := by simp [a, b, mul_assoc]
  have hbd : (Q 1)⁻¹ * Q 3 = b * d := by simp [b, d, mul_assoc]
  rw [hab, hbd, hQ1, map_mul, Module.End.mul_apply, ← map_sub, ← map_add, ← map_sub, e, map_zero]

/-- **Pointwise closedness of the transferred integrand.** -/
theorem lineTransferIntegrand_closed
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (hN : IsBinaryPointCocycle N) (x : Fin 4 → LineGroup) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lineTransferIntegrand N ![x 1, x 2, x 3] u h - lineTransferIntegrand N ![x 0, x 2, x 3] u h +
        lineTransferIntegrand N ![x 0, x 1, x 3] u h -
        lineTransferIntegrand N ![x 0, x 1, x 2] u h = 0 := by
  have closed := congrFun (planeHomogeneousCanonical_closed hN
    (fun y => gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix y)) x) h
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at closed
  unfold lineTransferIntegrand
  rw [← map_sub, ← map_add, ← map_sub, closed, map_zero]

/-- **Closedness of the real good-line transfer** (`n ≥ 5`). -/
theorem lineTransfer_closed (large : 5 ≤ n) (N : BinaryPointCocycle n) (x : Fin 4 → LineGroup) :
    faceSum (lineTransfer N.value) x = 0 := by
  funext p
  obtain ⟨h, functional⟩ := p
  have integrable (y : Fin 3 → LineGroup) := lineTransferIntegrand_integrable large N y h functional
  change lineTransfer N.value ![x 1, x 2, x 3] (h, functional) -
      lineTransfer N.value ![x 0, x 2, x 3] (h, functional) +
      lineTransfer N.value ![x 0, x 1, x 3] (h, functional) -
      lineTransfer N.value ![x 0, x 1, x 2] (h, functional) = 0
  unfold lineTransfer
  dsimp only
  rw [← integral_sub (integrable _) (integrable _), ← integral_add _ (integrable _),
    ← integral_sub _ (integrable _)]
  rotate_left
  · exact ((integrable _).sub (integrable _)).add (integrable _)
  · exact (integrable _).sub (integrable _)
  have pointwise (u : ℝ × ℝ) :
      functional (lineTransferIntegrand N.value ![x 1, x 2, x 3] u h) -
          functional (lineTransferIntegrand N.value ![x 0, x 2, x 3] u h) +
          functional (lineTransferIntegrand N.value ![x 0, x 1, x 3] u h) -
          functional (lineTransferIntegrand N.value ![x 0, x 1, x 2] u h) = 0 := by
    rw [← map_sub, ← map_add, ← map_sub, lineTransferIntegrand_closed N.cocycle, map_zero]
  simp only [pointwise, integral_zero]

/-- **The real good-line transfer is a two-cocycle of the real stabilizer** (`n ≥ 5`). -/
theorem lineTransfer_isTwoCocycle (large : 5 ≤ n) (N : BinaryPointCocycle n) :
    IsTwoCocycle (inhomogeneousOfHomogeneous (lineTransfer N.value)) :=
  isTwoCocycle_inhomogeneousOfHomogeneous (fun q x => lineTransfer_smul N.value q x)
    (lineTransfer_closed large N)

end TernaryPeriodPolynomials.AnalyticClasses
