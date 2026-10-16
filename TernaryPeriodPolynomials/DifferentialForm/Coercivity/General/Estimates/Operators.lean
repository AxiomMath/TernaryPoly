module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Hilbert
public import TernaryPeriodPolynomials.DifferentialForm.MinimalAdjoints
public import TernaryPeriodPolynomials.Analysis.Embedded.AdjointComplex
public import TernaryPeriodPolynomials.Analysis.Embedded.LinearComplex
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.AdjointComplex
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedExtension
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.GraphEnergyExactness

@[expose] public section


/-! # General coercivity, Tier B: the operators `d` and `δ` on the `L²` completions

Core operators, minimal (closure) and maximal (adjoint) extensions and the complex laws, for an
admissible group.  This is the `Γ`-parametric analogue of `PolynomialFormDifferential`,
`PolynomialFormHilbertAdjoint`, `PolynomialFormCodifferentialComplex`,
`PolynomialFormMinimalComplex` and `PolynomialFormMaximalComplex`; all abstract Hilbert-space
statements are the unchanged generic ones of `TernaryPoly.HilbertClosedOperator`.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SmoothLocalDeRham TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceCharts TernaryPoly.PolynomialCoefficientMetric
open scoped LinearPMap


instance instAddCommGroupCForm (Γ : Subgroup RealGL) (n k : ℕ) : AddCommGroup (CForm Γ n k) :=
  Submodule.addCommGroup _

variable {Γ : Subgroup RealGL} {n k : ℕ}

/-! ### Algebraic identities on the cores -/

theorem CForm.d_d (a : CForm Γ n k) : CForm.d Γ n (k + 1) (CForm.d Γ n k a) = 0 :=
  Subtype.ext (SmoothLocalDeRham.d_squared isOpen_positiveCoordinates k
    (a : Form (F := Coefficients n) positiveCoordinates k))

theorem Admissible.delta_delta (h : Admissible Γ) (e : CForm Γ n (k + 2)) :
    CForm.delta Γ n k (CForm.delta Γ n (k + 1) e) = 0 := by
  set z := CForm.delta Γ n k (CForm.delta Γ n (k + 1) e) with hz
  have h1 : l2Form Γ n k z z = 0 := by
    calc l2Form Γ n k z z = l2Form Γ n (k + 1) (CForm.d Γ n k z) (CForm.delta Γ n (k + 1) e) :=
          (h.l2Form_d z (CForm.delta Γ n (k + 1) e)).symm
      _ = l2Form Γ n (k + 2) (CForm.d Γ n (k + 1) (CForm.d Γ n k z)) e :=
          (h.l2Form_d (CForm.d Γ n k z) e).symm
      _ = 0 := by rw [CForm.d_d]; simp
  exact h.eq_zero_of_normSq_eq_zero z h1

/-! ### Core operators in the completion -/

section Core

variable (Γ n k) [hΓ : Fact (Admissible Γ)]

/-- The exterior derivative with domain the embedded compactly supported forms. -/
def opD : Hilbert Γ n k →ₗ.[ℝ] Hilbert Γ n (k + 1) :=
  EmbeddedLinearOperator.operator (incl Γ n k) (incl_injective Γ n k)
    ((incl Γ n (k + 1)).comp (CForm.d Γ n k))

/-- The codifferential with domain the embedded compactly supported forms. -/
def opDelta : Hilbert Γ n (k + 1) →ₗ.[ℝ] Hilbert Γ n k :=
  EmbeddedLinearOperator.operator (incl Γ n (k + 1)) (incl_injective Γ n (k + 1))
    ((incl Γ n k).comp (CForm.delta Γ n k))

theorem opD_domain_dense : Dense ((opD Γ n k).domain : Set (Hilbert Γ n k)) :=
  EmbeddedLinearOperator.domain_dense _ _ _ (incl_dense Γ n k)

theorem opDelta_domain_dense : Dense ((opDelta Γ n k).domain : Set (Hilbert Γ n (k + 1))) :=
  EmbeddedLinearOperator.domain_dense _ _ _ (incl_dense Γ n (k + 1))

theorem opD_incl (a : CForm Γ n k) :
    opD Γ n k ⟨incl Γ n k a, ⟨a, rfl⟩⟩ = incl Γ n (k + 1) (CForm.d Γ n k a) :=
  EmbeddedLinearOperator.operator_apply _ _ _ a

theorem opDelta_incl (b : CForm Γ n (k + 1)) :
    opDelta Γ n k ⟨incl Γ n (k + 1) b, ⟨b, rfl⟩⟩ = incl Γ n k (CForm.delta Γ n k b) :=
  EmbeddedLinearOperator.operator_apply _ _ _ b

/-- Integration by parts on the cores (G1), in the completion. -/
theorem inner_incl_d (a : CForm Γ n k) (b : CForm Γ n (k + 1)) :
    inner ℝ (incl Γ n (k + 1) (CForm.d Γ n k a)) (incl Γ n (k + 1) b) =
      inner ℝ (incl Γ n k a) (incl Γ n k (CForm.delta Γ n k b)) := by
  calc inner ℝ (incl Γ n (k + 1) (CForm.d Γ n k a)) (incl Γ n (k + 1) b)
      = l2Form Γ n (k + 1) (CForm.d Γ n k a) b := inner_incl Γ n (k + 1) _ _
    _ = l2Form Γ n k a (CForm.delta Γ n k b) := hΓ.out.l2Form_d a b
    _ = _ := (inner_incl Γ n k a _).symm

theorem opD_formalAdjoint : (opD Γ n k).IsFormalAdjoint (opDelta Γ n k) :=
  EmbeddedLinearOperator.isFormalAdjoint (incl Γ n k) (incl_injective Γ n k)
    (incl Γ n (k + 1)) (incl_injective Γ n (k + 1)) (CForm.d Γ n k) (CForm.delta Γ n k)
    (inner_incl_d Γ n k)

theorem opD_isClosable : (opD Γ n k).IsClosable :=
  HilbertClosedOperator.isClosable_of_formalAdjoint _ _ (opDelta_domain_dense Γ n k)
    (opD_formalAdjoint Γ n k)

theorem opDelta_isClosable : (opDelta Γ n k).IsClosable :=
  HilbertClosedOperator.isClosable_of_formalAdjoint _ _ (opD_domain_dense Γ n k)
    (opD_formalAdjoint Γ n k).symm

theorem opD_complex (a : (opD Γ n k).domain) :
    opD Γ n k a ∈ HilbertClosedOperator.kernel (opD Γ n (k + 1)) :=
  EmbeddedLinearOperator.complex (incl Γ n k) (incl_injective Γ n k)
    (incl Γ n (k + 1)) (incl_injective Γ n (k + 1)) (incl Γ n (k + 1 + 1))
    (CForm.d Γ n k) (CForm.d Γ n (k + 1)) (fun v => CForm.d_d v) a

theorem opDelta_complex (a : (opDelta Γ n (k + 1)).domain) :
    opDelta Γ n (k + 1) a ∈ HilbertClosedOperator.kernel (opDelta Γ n k) :=
  EmbeddedLinearOperator.complex (incl Γ n (k + 1 + 1)) (incl_injective Γ n (k + 1 + 1))
    (incl Γ n (k + 1)) (incl_injective Γ n (k + 1)) (incl Γ n k)
    (CForm.delta Γ n (k + 1)) (CForm.delta Γ n k) (fun v => hΓ.out.delta_delta v) a

/-! ### Minimal and maximal extensions -/

/-- Closure of the core exterior derivative. -/
def minD : Hilbert Γ n k →ₗ.[ℝ] Hilbert Γ n (k + 1) := (opD Γ n k).closure

/-- Closure of the core codifferential. -/
def minDelta : Hilbert Γ n (k + 1) →ₗ.[ℝ] Hilbert Γ n k := (opDelta Γ n k).closure

/-- The weak exterior derivative, tested against the core codifferential. -/
def maxD : Hilbert Γ n k →ₗ.[ℝ] Hilbert Γ n (k + 1) := (opDelta Γ n k)†

/-- The weak codifferential, tested against the core exterior derivative. -/
def maxDelta : Hilbert Γ n (k + 1) →ₗ.[ℝ] Hilbert Γ n k := (opD Γ n k)†

theorem minD_isClosed : (minD Γ n k).IsClosed := (opD_isClosable Γ n k).closure_isClosed

theorem minDelta_isClosed : (minDelta Γ n k).IsClosed := (opDelta_isClosable Γ n k).closure_isClosed

theorem maxD_isClosed : (maxD Γ n k).IsClosed :=
  LinearPMap.adjoint_isClosed (opDelta_domain_dense Γ n k)

theorem maxDelta_isClosed : (maxDelta Γ n k).IsClosed :=
  LinearPMap.adjoint_isClosed (opD_domain_dense Γ n k)

theorem minD_domain_dense : Dense ((minD Γ n k).domain : Set (Hilbert Γ n k)) :=
  HilbertClosedOperator.closure_dense_domain _ (opD_domain_dense Γ n k)

theorem opD_le_maxD : opD Γ n k ≤ maxD Γ n k :=
  (opD_formalAdjoint Γ n k).symm.le_adjoint (opDelta_domain_dense Γ n k)

theorem opDelta_le_maxDelta : opDelta Γ n k ≤ maxDelta Γ n k :=
  (opD_formalAdjoint Γ n k).le_adjoint (opD_domain_dense Γ n k)

theorem minD_le_maxD : minD Γ n k ≤ maxD Γ n k :=
  HilbertClosedOperator.closure_le _ _ (maxD_isClosed Γ n k) (opD_le_maxD Γ n k)

theorem minDelta_le_maxDelta : minDelta Γ n k ≤ maxDelta Γ n k :=
  HilbertClosedOperator.closure_le _ _ (maxDelta_isClosed Γ n k) (opDelta_le_maxDelta Γ n k)

/-- The minimal exterior derivative and the maximal codifferential are adjoint. -/
theorem minD_adjoint : (minD Γ n k)† = maxDelta Γ n k :=
  HilbertClosedOperator.adjoint_closure _ (opD_domain_dense Γ n k) (opD_isClosable Γ n k)

theorem minDelta_adjoint : (minDelta Γ n k)† = maxD Γ n k :=
  HilbertClosedOperator.adjoint_closure _ (opDelta_domain_dense Γ n k) (opDelta_isClosable Γ n k)

theorem minD_complex (a : (minD Γ n k).domain) :
    minD Γ n k a ∈ HilbertClosedOperator.kernel (minD Γ n (k + 1)) :=
  HilbertClosedOperator.closure_complex _ _ (opD_isClosable Γ n k)
    (opD_isClosable Γ n (k + 1)) (opD_complex Γ n k) a

theorem maxD_complex (a : (maxD Γ n k).domain) :
    maxD Γ n k a ∈ HilbertClosedOperator.kernel (maxD Γ n (k + 1)) :=
  HilbertClosedOperator.adjoint_complex (opDelta Γ n (k + 1)) (opDelta Γ n k)
    (opDelta_domain_dense Γ n (k + 1)) (opDelta_domain_dense Γ n k)
    (opDelta_complex Γ n k) a

theorem maxDelta_complex (a : (maxDelta Γ n (k + 1)).domain) :
    maxDelta Γ n (k + 1) a ∈ HilbertClosedOperator.kernel (maxDelta Γ n k) :=
  HilbertClosedOperator.adjoint_complex (opD Γ n k) (opD Γ n (k + 1))
    (opD_domain_dense Γ n k) (opD_domain_dense Γ n (k + 1)) (opD_complex Γ n k) a

end Core

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
