module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualFaithful
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Derivative

@[expose] public section


/-!
# General coercivity: the Cartan-twisted coefficients are the dual representation

The dual coefficient system of this development is `Coefficients n` with the representation
`ρ*(g) = ρ(θ g)`, `θ g = (g⁻¹)ᵀ` (and its complexification).  This file shows that this is the
contragredient representation `E*` of `E = Sym^n`: the Fischer isomorphism
`InnerProductSpace.toDual : E ≃ₗᵢ E*` (an isometry for the Fischer norm) intertwines `ρ*(g)` with
the contragredient action `φ ↦ φ ∘ ρ(g)⁻¹`.  The statement is the equivariant form of
`TernaryPoly.PolynomialCoefficientMetric.coefficientSubstitution_dual`, which it uses.  For the
complexification, the dual of `E ⊗ ℂ` is `E* ⊗ ℂ`, and both the representation and the Hermitian
metric are the real/imaginary-part ones of `ComplexCoefficients` (`reImEquiv_complexRho`,
`fischerC_reImEquiv`); the Hermitian extension of the Fischer inner product is `cplxInner`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.SL3PolynomialCoercivity

attribute [local instance 2000] TernaryPoly.PolynomialCoefficientMetric.coefficientTopologicalSpace

/-- The substitution by the transpose of `g` is the Fischer adjoint of the substitution by `g`
(equivariant form of `coefficientSubstitution_dual`). -/
theorem coefficientSubstitution_adjoint (n : ℕ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (p q : Coefficients n) :
    inner ℝ (coefficientSubstitution n A p) q = inner ℝ p (coefficientSubstitution n A.transpose q) := by
  simp only [coefficient_inner, coefficientSubstitution_apply]
  exact realSubstitute_transpose_adjoint A p.val q.val

/-- **The Cartan-twisted representation is the contragredient.**  The Fischer inner product
satisfies `⟨ρ(θ g) p, q⟩ = ⟨p, ρ(g)⁻¹ q⟩`: under `toDual` the twisted action `ρ*(g)` on `E` is the
contragredient action on `E*`. -/
theorem inner_dualRep (n : ℕ) (g : RealGL) (p q : Coefficients n) :
    inner ℝ (realHomogeneousAction n (thetaHom g) p) q =
      inner ℝ p (realHomogeneousAction n g⁻¹ q) := by
  have e1 : realHomogeneousAction n (thetaHom g) p =
      coefficientSubstitution n (g : Matrix (Fin 3) (Fin 3) ℝ).transpose p := rfl
  have e2 : realHomogeneousAction n g⁻¹ q = coefficientSubstitution n (g : Matrix (Fin 3) (Fin 3) ℝ) q := by
    apply Subtype.ext
    change realSubstitute (((g⁻¹)⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) q.val = _
    rw [inv_inv]
    rfl
  rw [e1, e2, coefficientSubstitution_adjoint, Matrix.transpose_transpose]

/-- `toDual` intertwines `ρ*(g)` with the contragredient action `φ ↦ φ ∘ ρ(g)⁻¹`. -/
theorem toDual_dualRep (n : ℕ) (g : RealGL) (p : Coefficients n) :
    InnerProductSpace.toDual ℝ (Coefficients n) (realHomogeneousAction n (thetaHom g) p) =
      (InnerProductSpace.toDual ℝ (Coefficients n) p).comp
        (realHomogeneousAction n g⁻¹).toContinuousLinearMap := by
  ext q
  simpa using inner_dualRep n g p q

/-- The Hermitian extension of the Fischer inner product to `E ⊗ ℂ = ComplexCoefficients n`
(real part of the Hermitian product, `⟨a + ib, a' + ib'⟩ = ⟨a,a'⟩ + ⟨b,b'⟩`). -/
def cplxInner (n : ℕ) : ComplexCoefficients n →ₗ[ℝ] ComplexCoefficients n →ₗ[ℝ] ℝ :=
  cplxBilin n (innerₗ (Coefficients n))

theorem cplxInner_apply (n : ℕ) (p q : ComplexCoefficients n) :
    cplxInner n p q = inner ℝ (reL n p) (reL n q) + inner ℝ (imL n p) (imL n q) := rfl

theorem cplxInner_self (n : ℕ) (p : ComplexCoefficients n) : cplxInner n p p = fischerC p.1 := by
  rw [cplxInner_apply, fischerC_reImEquiv, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rfl

/-- **Complex version of the dictionary.**  The Hermitian extension of the Fischer product
intertwines the complexified twisted action with the inverse action, so `ComplexCoefficients n`
with `ρ_ℂ ∘ θ` is `E_ℂ* = E* ⊗ ℂ` with its Hermitian Fischer metric. -/
theorem cplxInner_dualRep (n : ℕ) (g : RealGL) (p q : ComplexCoefficients n) :
    cplxInner n (complexRepresentation n (thetaHom g) p) q =
      cplxInner n p (complexRepresentation n g⁻¹ q) := by
  rw [cplxInner_apply, cplxInner_apply, reL_complexRep, imL_complexRep, reL_complexRep,
    imL_complexRep, inner_dualRep, inner_dualRep]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
