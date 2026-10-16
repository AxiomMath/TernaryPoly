module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantPlaneInvariants

@[expose] public section


open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

theorem actualPlaneRelations_eq_ker (n : ℕ) :
    actualPlaneRelations n = LinearMap.ker (planeEval n) := by
  rw [actualPlaneRelations_eq, planeRelations_eq_ker]

theorem actualLineRelations_eq_ker (n : ℕ) :
    actualLineRelations n = LinearMap.ker (lineEval n) := by
  rw [actualLineRelations_eq, lineRelations_eq_ker]

def actualLineScalarEquiv (n : ℕ) : (H n ⧸ actualLineRelations n) ≃ₗ[ℚ] ℚ :=
  (actualLineQuotientEquiv n).trans (unaryScalarEquiv n)

@[simp] theorem actualPlaneQuotientEquiv_mk (n : ℕ) (p : H n) :
    actualPlaneQuotientEquiv n (Submodule.Quotient.mk p) = planeEval n p := rfl

@[simp] theorem actualLineScalarEquiv_mk (n : ℕ) (p : H n) :
    actualLineScalarEquiv n (Submodule.Quotient.mk p) = unaryScalarEquiv n (lineEval n p) := rfl

theorem planeRelations_Levi_stable (n : ℕ) (A : GL2) :
    actualPlaneRelations n ≤ (actualPlaneRelations n).comap
      (PolynomialGLAction.integralAction n 0 (planeElement A 0)) := by
  intro p hp
  change PolynomialGLAction.integralAction n 0 (planeElement A 0) p ∈ actualPlaneRelations n
  rw [actualPlaneRelations_eq_ker] at hp ⊢
  apply Subtype.ext
  rw [planeEval_Levi]
  have he : (planeEval n p : MvPolynomial (Fin 2) ℚ) = 0 := congrArg Subtype.val hp
  rw [he, map_zero]
  rfl

/-- The actual coefficient action descends to the plane coinvariant quotient. -/
def planeQuotientLevi (n : ℕ) (A : GL2) :
    (H n ⧸ actualPlaneRelations n) →ₗ[ℚ] (H n ⧸ actualPlaneRelations n) :=
  (actualPlaneRelations n).mapQ (actualPlaneRelations n)
    (PolynomialGLAction.integralAction n 0 (planeElement A 0)) (planeRelations_Levi_stable n A)

theorem lineRelations_diagonal_stable (n : ℕ) (ε : ℤˣ × ℤˣ) :
    actualLineRelations n ≤ (actualLineRelations n).comap
      (PolynomialGLAction.integralAction n 0 (diagonalHom ε)) := by
  intro p hp
  change PolynomialGLAction.integralAction n 0 (diagonalHom ε) p ∈ actualLineRelations n
  rw [actualLineRelations_eq_ker] at hp ⊢
  apply Subtype.ext
  rw [lineEval_integralAction_diagonal]
  have he : (lineEval n p : MvPolynomial (Fin 1) ℚ) = 0 := congrArg Subtype.val hp
  rw [he, map_zero]
  rfl

def lineQuotientDiagonal (n : ℕ) (ε : ℤˣ × ℤˣ) :
    (H n ⧸ actualLineRelations n) →ₗ[ℚ] (H n ⧸ actualLineRelations n) :=
  (actualLineRelations n).mapQ (actualLineRelations n)
    (PolynomialGLAction.integralAction n 0 (diagonalHom ε)) (lineRelations_diagonal_stable n ε)

/-- The actual quotient equivalence intertwines the descended Levi action. -/
theorem planeQuotientLevi_intertwine (n : ℕ) (A : GL2) (q : H n ⧸ actualPlaneRelations n) :
    (actualPlaneQuotientEquiv n (planeQuotientLevi n A q) : MvPolynomial (Fin 2) ℚ) =
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
      (actualPlaneQuotientEquiv n q) := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (actualPlaneRelations n) q
  simp only [planeQuotientLevi, Submodule.mapQ_apply, actualPlaneQuotientEquiv_mk]
  exact planeEval_Levi n A p

theorem lineQuotientDiagonal_intertwine (n : ℕ) (ε : ℤˣ × ℤˣ)
    (q : H n ⧸ actualLineRelations n) :
    actualLineScalarEquiv n (lineQuotientDiagonal n ε q) =
    unitScalar ε.1⁻¹ ^ n * actualLineScalarEquiv n q := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (actualLineRelations n) q
  simp only [lineQuotientDiagonal, Submodule.mapQ_apply, actualLineScalarEquiv_mk]
  exact lineScalar_integralAction_diagonal n ε p

/-- The determinant-dual-twisted plane quotient has no fixed vectors under its actual Levi. -/
theorem planeQuotient_twisted_fixed_zero (n : ℕ) (q : H n ⧸ actualPlaneRelations n)
    (hq : ∀ A : GL2, planeLeviRootDual A • planeQuotientLevi n A q = q) : q = 0 := by
  apply (actualPlaneQuotientEquiv n).injective
  rw [map_zero]
  apply binary_twisted_Levi_fixed_zero n (actualPlaneQuotientEquiv n q)
  intro A
  have h := congrArg (fun z : H n ⧸ actualPlaneRelations n =>
    (actualPlaneQuotientEquiv n z : MvPolynomial (Fin 2) ℚ)) (hq A)
  simpa only [map_smul, Submodule.coe_smul, planeQuotientLevi_intertwine] using h

/-- The determinant-dual-twisted line quotient has no fixed vectors under its actual diagonal subgroup. -/
theorem lineQuotient_twisted_fixed_zero (n : ℕ) (q : H n ⧸ actualLineRelations n)
    (hq : ∀ ε : ℤˣ × ℤˣ, lineRootDual ε • lineQuotientDiagonal n ε q = q) : q = 0 := by
  apply (actualLineScalarEquiv n).injective
  rw [map_zero]
  have h := congrArg (actualLineScalarEquiv n) (hq (1,-1))
  rw [map_smul, lineQuotientDiagonal_intertwine, lineRootDual_formula] at h
  simp [unitScalar] at h
  linarith

end TernaryPoly.RadicalCoinvariantAlgebra
