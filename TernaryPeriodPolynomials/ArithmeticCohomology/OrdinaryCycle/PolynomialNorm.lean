module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Norm
public import TernaryPeriodPolynomials.Polynomial.Operators

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryPolynomialNorm
open OrdinaryCovectors OrdinaryCovectorOrbits

/-- Literal simultaneous first-two-coordinate sign change. -/
def D12 : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![-X 0,-X 1,X 2]
/-- Literal third-coordinate sign change. -/
def D3 : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0,X 1,-X 2]

theorem A_comp_D12 : A.comp D12=D12.comp A := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A,D12,AlgHom.comp_apply]
  abel

theorem A_comp_D3 : A.comp D3=D3.comp A := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [A,D3,AlgHom.comp_apply]

theorem A_D12 (f : TernaryPolynomial) : A (D12 f)=D12 (A f) :=
  DFunLike.congr_fun A_comp_D12 f

theorem A_D3 (f : TernaryPolynomial) : A (D3 f)=D3 (A f) :=
  DFunLike.congr_fun A_comp_D3 f

/-- The polynomial norm uses exactly the substitutions, on the indicated fibers. -/
def fiberNorm (F : Covector → TernaryPolynomial) (r : Covector) : TernaryPolynomial :=
  F r+A (F (stepA (stepA r)))+A2 (F (stepA r))

theorem fiberNorm_eq (F : Covector → TernaryPolynomial) (r : Covector) :
    fiberNorm F r=OrdinaryFiberNorm.norm A.toLinearMap F r := by
  simp only [fiberNorm,OrdinaryFiberNorm.norm,AlgHom.toLinearMap_apply,A_A]

/-- The signed-polynomial fiber system has exactly five independent norm checks. -/
theorem all_norms_of_five (F : Covector → TernaryPolynomial)
    (h12 : ∀ r,F (sign12 r)=D12 (F r))
    (h3 : ∀ r,F (sign3 r)= -D3 (F r))
    (hfive : ∀ i,fiberNorm F (representative i)=0) :
    ∀ r : Covector,r≠0 → fiberNorm F r=0 := by
  intro r hr
  rw [fiberNorm_eq]
  apply OrdinaryFiberNorm.all_norms_of_five A.toLinearMap D12.toLinearMap
    (-D3.toLinearMap) F A_A_A h12 h3 A_D12 ?_ ?_ r hr
  · intro f
    change A (-D3 f)= -D3 (A f)
    rw [map_neg,A_D3]
  · intro i
    rw [← fiberNorm_eq]
    exact hfive i

end TernaryPoly.OrdinaryPolynomialNorm
