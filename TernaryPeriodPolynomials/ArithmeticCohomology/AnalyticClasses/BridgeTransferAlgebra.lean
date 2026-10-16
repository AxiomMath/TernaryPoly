module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.TransferOrthogonal

@[expose] public section


/-!
# The canonical cochain and the real transfer of a binary coboundary

For a function `κ : GL₂(𝔸) → Sym^{n+1}` let `δκ (A) = A · κ - κ` be its binary coboundary (for the
cohomological action `binaryAmbientRepresentation`) and let `θκ (q) = μ(x_q)(κ)` be the plane
one-cochain built from `μ = realUpperBinaryValue`. The canonical cochain of `δκ` is the plane
coboundary of `θκ`. Homogeneously, the canonical cochain of `δκ` at `(Q₀, Q₁, Q₂)` is the
alternating sum of the canonical cochains of the constant family `κ` at the degenerate simplices
`(Q₁, Q₁, Q₂)`, `(Q₀, Q₀, Q₂)` and `(Q₀, Q₀, Q₁)`, each of which is the homogeneous form of `θκ`.
The real good-line transfer of `θκ` is the one-cochain `bridgeTransfer κ` of the real good-line
stabilizer, and on every configuration whose degenerate faces are integrable the transfer of the
canonical cochain of `δκ` is the coboundary of `bridgeTransfer κ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The canonical cochain of a binary coboundary -/

/-- The binary coboundary `A ↦ A · κ - κ` of a function `κ : GL₂(𝔸) → Sym^{n+1}`. -/
def binaryCoboundary (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun A => binaryAmbientRepresentation n A κ - κ

theorem binaryCoboundary_apply (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (A : BinaryRealGL) (h : BinaryAdelicGL) :
    binaryCoboundary κ A h = binaryAmbientRepresentation n A κ h - κ h := rfl

/-- The plane one-cochain `q ↦ μ(x_q)(κ)` of a function `κ : GL₂(𝔸) → Sym^{n+1}`. -/
def planeBridgeCochain (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (q : RealPlaneGroup) : BinaryAdelicGL → HomogeneousPoly n :=
  fun h => realUpperBinaryValue n q.left (κ h)

/-- The canonical cochain is additive in the binary cochain. -/
theorem pointCanonical_add (N₁ N₂ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p q : RealPlaneGroup) :
    pointCanonical (fun A => N₁ A + N₂ A) p q = pointCanonical N₁ p q + pointCanonical N₂ p q := by
  funext h
  simp only [pointCanonical, Pi.add_apply, map_add]

/-- **The canonical cochain of a binary coboundary is the plane coboundary of `θκ`.** -/
theorem pointCanonical_binaryCoboundary (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (p q : RealPlaneGroup) :
    pointCanonical (binaryCoboundary κ) p q =
      planeAmbientRepresentation n p (planeBridgeCochain κ q) - planeBridgeCochain κ (p * q) +
        planeBridgeCochain κ p := by
  funext h
  have moved := planeCoefficient_canonical p 1 q.left (κ (h * realPlaneBinaryInput p))
  simp only [map_one, mul_one, Module.End.one_apply] at moved
  have first : planeAmbientRepresentation n p (planeBridgeCochain κ q) h =
      (realUpperRadicalRep n).ρ p.left
        (realUpperBinaryValue n (realPlaneRadicalAction p.right q.left)
          (realPlaneCuspidalTwist n p •
            binaryCoefficient n p.right (κ (h * realPlaneBinaryInput p)))) := by
    rw [planeAmbientRepresentation_apply]
    unfold planeBridgeCochain
    rw [moved, map_smul, map_smul]
  have second : planeBridgeCochain κ (p * q) h =
      (realUpperRadicalRep n).ρ p.left
          (realUpperBinaryValue n (realPlaneRadicalAction p.right q.left) (κ h)) +
        realUpperBinaryValue n p.left (κ h) := by
    unfold planeBridgeCochain
    rw [SemidirectProduct.mul_left, realUpperBinaryValue_mul]
  have binary : binaryCoboundary κ p.right h = realPlaneCuspidalTwist n p •
      binaryCoefficient n p.right (κ (h * realPlaneBinaryInput p)) - κ h := rfl
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [first, second]
  unfold pointCanonical planeBridgeCochain
  rw [binary, map_sub, map_sub]
  abel

/-- The canonical cochain of a constant family with first argument `1` is `θκ`. -/
theorem pointCanonical_const_one (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (q : RealPlaneGroup) :
    pointCanonical (fun _ => κ) 1 q = planeBridgeCochain κ q := by
  funext h
  simp [pointCanonical, planeBridgeCochain]

/-- The homogeneous canonical cochain of a constant family at a degenerate simplex. -/
theorem planeHomogeneousCanonical_degenerate (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (P Q : RealPlaneGroup) :
    planeHomogeneousCanonical (fun _ => κ) ![P, P, Q] =
      planeAmbientRepresentation n P (planeBridgeCochain κ (P⁻¹ * Q)) := by
  unfold planeHomogeneousCanonical
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, inv_mul_cancel, pointCanonical_const_one]

/-- **The homogeneous canonical cochain of a binary coboundary** as an alternating sum over
degenerate simplices of the constant family. -/
theorem planeHomogeneousCanonical_binaryCoboundary
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (Q : Fin 3 → RealPlaneGroup) :
    planeHomogeneousCanonical (binaryCoboundary κ) Q =
      planeHomogeneousCanonical (fun _ => κ) ![Q 1, Q 1, Q 2] -
        planeHomogeneousCanonical (fun _ => κ) ![Q 0, Q 0, Q 2] +
        planeHomogeneousCanonical (fun _ => κ) ![Q 0, Q 0, Q 1] := by
  rw [planeHomogeneousCanonical_degenerate, planeHomogeneousCanonical_degenerate,
    planeHomogeneousCanonical_degenerate]
  unfold planeHomogeneousCanonical
  have product : (Q 0)⁻¹ * Q 1 * ((Q 1)⁻¹ * Q 2) = (Q 0)⁻¹ * Q 2 := by group
  rw [pointCanonical_binaryCoboundary, map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel_left, product]

/-- The homogeneous canonical cochain is additive in the binary cochain. -/
theorem planeHomogeneousCanonical_add
    (N₁ N₂ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (Q : Fin 3 → RealPlaneGroup) :
    planeHomogeneousCanonical (fun A => N₁ A + N₂ A) Q =
      planeHomogeneousCanonical N₁ Q + planeHomogeneousCanonical N₂ Q := by
  unfold planeHomogeneousCanonical
  rw [pointCanonical_add, map_add]

/-! ### The transferred integrands -/

/-- The transferred integrand is additive in the binary cochain. -/
theorem lineTransferIntegrand_add
    (N₁ N₂ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (x : Fin 3 → LineGroup) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lineTransferIntegrand (fun A => N₁ A + N₂ A) x u h =
      lineTransferIntegrand N₁ x u h + lineTransferIntegrand N₂ x u h := by
  unfold lineTransferIntegrand
  rw [planeHomogeneousCanonical_add, Pi.add_apply, map_add]

/-- **The transferred integrand of a binary coboundary** as an alternating sum of transferred
integrands of the constant family at degenerate simplices. -/
theorem lineTransferIntegrand_binaryCoboundary
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (x : Fin 3 → LineGroup) (u : ℝ × ℝ)
    (h : BinaryAdelicGL) :
    lineTransferIntegrand (binaryCoboundary κ) x u h =
      lineTransferIntegrand (fun _ => κ) ![x 1, x 1, x 2] u h -
        lineTransferIntegrand (fun _ => κ) ![x 0, x 0, x 2] u h +
        lineTransferIntegrand (fun _ => κ) ![x 0, x 0, x 1] u h := by
  have vertices (y z : LineGroup) :
      (fun i => gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix (![y, y, z] i))) =
        ![gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix y),
          gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix y),
          gsPlaneVertex (standardGoodLineRealArgument u * lineMatrix z)] := by
    funext i
    fin_cases i <;> rfl
  unfold lineTransferIntegrand
  rw [vertices, vertices, vertices, planeHomogeneousCanonical_binaryCoboundary, Pi.add_apply,
    Pi.sub_apply, map_add, map_sub]

/-! ### The transfer of `θκ` -/

/-- **The real good-line transfer of `θκ`**, in inhomogeneous form: at `a`, the integral over the
good-line coordinate `u` of the transferred value of `θκ` at the relative position of `a`. -/
def bridgeTransfer (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (a : LineGroup) :
    LineValues n :=
  fun p => ∫ u : ℝ × ℝ, p.2 (transferScale n u •
    realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
      (planeBridgeCochain κ (relativeVertex u a)
        (p.1 * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right)))
    ∂((volume : Measure ℝ).prod volume)

/-- The transferred integrand of the constant family at the degenerate simplex `(1, 1, a)`. -/
theorem lineTransferIntegrand_degenerate_one (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (a : LineGroup) (u : ℝ × ℝ) (h : BinaryAdelicGL) :
    lineTransferIntegrand (fun _ => κ) ![1, 1, a] u h =
      transferScale n u • realCoefficientComponent n trivialCharacter (gsOrth u)⁻¹
        (planeBridgeCochain κ (relativeVertex u a)
          (h * atInfinity (gsPlaneVertex (standardGoodLineRealArgument u)).right)) := by
  rw [lineTransferIntegrand_eq_relative]
  unfold relativeIntegrand
  rw [relativeVertex_one, inv_one, one_mul, pointCanonical_const_one]

/-- The transfer of `θκ` is the transfer of the constant family at degenerate simplices. -/
theorem bridgeTransfer_eq_lineTransfer (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (a : LineGroup) : bridgeTransfer κ a = lineTransfer (fun _ => κ) ![1, 1, a] := by
  funext p
  unfold bridgeTransfer lineTransfer
  simp only [lineTransferIntegrand_degenerate_one]

/-- Equivariance of the transfer of `θκ`. -/
theorem lineTransfer_degenerate (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (q a : LineGroup) :
    lineTransfer (fun _ => κ) ![q, q, q * a] = q • bridgeTransfer κ a := by
  rw [bridgeTransfer_eq_lineTransfer, ← lineTransfer_smul]
  congr 1
  funext i
  fin_cases i <;> simp

/-! ### The transfer of the canonical cochain of a binary coboundary -/

/-- **The transfer of the canonical cochain of a binary coboundary**, homogeneously: on every
configuration whose degenerate faces are integrable, it is the alternating sum of the degenerate
transfers of the constant family. -/
theorem lineTransfer_binaryCoboundary (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (integrable : ∀ (y z : LineGroup) (h : BinaryAdelicGL)
      (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable (fun u => functional (lineTransferIntegrand (fun _ => κ) ![y, y, z] u h))
        ((volume : Measure ℝ).prod volume))
    (x : Fin 3 → LineGroup) :
    lineTransfer (binaryCoboundary κ) x =
      lineTransfer (fun _ => κ) ![x 1, x 1, x 2] - lineTransfer (fun _ => κ) ![x 0, x 0, x 2] +
        lineTransfer (fun _ => κ) ![x 0, x 0, x 1] := by
  funext p
  obtain ⟨h, functional⟩ := p
  change _ = lineTransfer (fun _ => κ) ![x 1, x 1, x 2] (h, functional) -
      lineTransfer (fun _ => κ) ![x 0, x 0, x 2] (h, functional) +
      lineTransfer (fun _ => κ) ![x 0, x 0, x 1] (h, functional)
  unfold lineTransfer
  dsimp only
  rw [← integral_sub (integrable _ _ h functional) (integrable _ _ h functional),
    ← integral_add _ (integrable _ _ h functional)]
  · congr 1
    funext u
    rw [lineTransferIntegrand_binaryCoboundary, map_add, map_sub]
  · exact (integrable _ _ h functional).sub (integrable _ _ h functional)

/-- **The transfer of the canonical cochain of a binary coboundary is the coboundary of the
transfer of `θκ`.** -/
theorem lineTransferCochain_binaryCoboundary
    (κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (integrable : ∀ (y z : LineGroup) (h : BinaryAdelicGL)
      (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable (fun u => functional (lineTransferIntegrand (fun _ => κ) ![y, y, z] u h))
        ((volume : Measure ℝ).prod volume))
    (a b : LineGroup) :
    lineTransferCochain (binaryCoboundary κ) a b =
      a • bridgeTransfer κ b - bridgeTransfer κ (a * b) + bridgeTransfer κ a := by
  change lineTransfer (binaryCoboundary κ) ![1, a, a * b] = _
  rw [lineTransfer_binaryCoboundary κ integrable]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [lineTransfer_degenerate]
  simp only [bridgeTransfer_eq_lineTransfer]

end TernaryPeriodPolynomials.AnalyticClasses
