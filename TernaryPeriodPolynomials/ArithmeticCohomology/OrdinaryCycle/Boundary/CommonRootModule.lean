module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Covectors
public import TernaryPeriodPolynomials.Polynomial.GLAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCommonRoot
open OrdinaryCovectors ModThreeGoodAction PolynomialGLAction

/-- The literal 26-covector homogeneous polynomial coefficient module. -/
abbrev Coefficients (n : ℕ) := NonzeroCovector → HomogeneousPoly n

instance homogeneous_finite (n : ℕ) : FiniteDimensional ℚ (HomogeneousPoly n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℚ n)

instance coefficients_finite (n : ℕ) : FiniteDimensional ℚ (Coefficients n) := inferInstance

/-- Right multiplication of a nonzero residue covector by an actual integral matrix. -/
def rowMove (g : IntegralGL) (r : NonzeroCovector) : NonzeroCovector :=
  ⟨Matrix.vecMul r.val (reduction g).val, by
    intro h
    apply r.property
    have hh := congrArg (fun x => Matrix.vecMul x (reduction g⁻¹).val) h
    simpa only [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.vecMul_one, Matrix.zero_vecMul] using hh⟩

@[simp] theorem rowMove_one (r : NonzeroCovector) : rowMove 1 r = r := by
  apply Subtype.ext
  simp [rowMove]

 theorem rowMove_mul (g h : IntegralGL) (r : NonzeroCovector) :
    rowMove (g*h) r = rowMove h (rowMove g r) := by
  apply Subtype.ext
  simp [rowMove, Matrix.vecMul_vecMul]

/-- The induced coefficient action in the global polynomial trivialization:
`(g • F)(r) = ρ(g)(F(rg))`. In particular `ρ(g)` substitutes `g⁻¹`. -/
def coefficientAction (n : ℕ) (e : ℤ) : Representation ℚ IntegralGL (Coefficients n) where
  toFun g :=
    { toFun := fun F r => integralAction n e g (F (rowMove g r))
      map_add' F H := by funext r; exact map_add _ _ _
      map_smul' q F := by funext r; exact (integralAction n e g).map_smul q _ }
  map_one' := by
    apply LinearMap.ext
    intro F
    funext r
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    funext r
    change integralAction n e (g*h) (F (rowMove (g*h) r)) =
      integralAction n e g (integralAction n e h (F (rowMove h (rowMove g r))))
    rw [map_mul, Module.End.mul_apply, rowMove_mul]

@[simp] theorem coefficientAction_apply (n : ℕ) (e : ℤ) (g : IntegralGL)
    (F : Coefficients n) (r : NonzeroCovector) :
    coefficientAction n e g F r = integralAction n e g (F (rowMove g r)) := rfl

/-- The support-three distinguished covector `(1,1,1)`. -/
def distinguished : NonzeroCovector := nonzeroRow 1

@[simp] theorem distinguished_val : distinguished.val = fixedRow := row_one

/-- Literal evaluation at the distinguished support-three covector. -/
def evaluation (n : ℕ) : Coefficients n →ₗ[ℚ] HomogeneousPoly n :=
  LinearMap.proj distinguished

/-- A residue-fixing matrix acts on the distinguished coefficient by inverse polynomial substitution. -/
theorem evaluation_action (n : ℕ) (e : ℤ) (g : IntegralGL) (hg : g ∈ K)
    (F : Coefficients n) :
    evaluation n (coefficientAction n e g F) = integralAction n e g (evaluation n F) := by
  have hr : rowMove g distinguished = distinguished := by
    apply Subtype.ext
    simpa [rowMove] using hg
  change integralAction n e g (F (rowMove g distinguished)) = _
  rw [hr]
  rfl

end TernaryPoly.OrdinaryBoundaryCommonRoot
