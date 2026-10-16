module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.PolynomialFiberSystem
public import TernaryPeriodPolynomials.Building.Good.ChainComplex

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFiberComparison
open ModThreeGoodAction OrdinaryCovectors OrdinaryCovectorOrbits
open OrdinaryPolynomialFiberSystem OrdinaryPolynomialNorm OrdinaryFiberPermutations
open OrdinarySignedFibers OrdinarySeedEquivariance

/-- The literal polynomial assigned to any integral frame by its residue fiber. -/
def framePoly (F : Covector → TernaryPolynomial) (g : IntegralGL) : TernaryPolynomial :=
  ReferenceCoefficientMatrices.coefficientAction (-1) g (F (row g))

/-- The same frame value in the actual exact-degree homogeneous coefficient space. -/
def frameValue (n : ℕ) (F : Covector → TernaryPolynomial)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) : PolynomialGLAction.HomogeneousPoly n :=
  PolynomialGLAction.integralAction n (-1) g ⟨F (row g),hF (row g)⟩

@[simp] theorem frameValue_coe (n : ℕ) (F : Covector → TernaryPolynomial)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) :
    (frameValue n F hF g : TernaryPolynomial)=framePoly F g := rfl

@[simp] theorem framePoly_one (F : Covector → TernaryPolynomial) :
    framePoly F 1=F ![1,1,1] := by
  simp only [framePoly,row_one,map_one,Module.End.one_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem framePoly_equivariant (F : Covector → TernaryPolynomial) (k : K) (g : IntegralGL) :
    framePoly F (k.val*g)=
      ReferenceCoefficientMatrices.coefficientAction (-1) k.val (framePoly F g) := by
  rw [framePoly,row_left_K,map_mul,Module.End.mul_apply]
  rfl

theorem frameValue_equivariant (n : ℕ) (F : Covector → TernaryPolynomial)
    (hF : ∀ r,(F r).IsHomogeneous n) (k : K) (g : IntegralGL) :
    frameValue n F hF (k.val*g)=
      GoodChainComplex.coefficientAction n (-1) k (frameValue n F hF g) := by
  apply Subtype.ext
  exact framePoly_equivariant F k g

theorem row_mul_a (g : IntegralGL) :
    row (g*ReferenceCoefficientMatrices.a)=stepA (row g) := by
  rw [row_mul,stepA_matrix]

theorem row_mul_a_sq (g : IntegralGL) :
    OrdinaryCovectors.row (g*ReferenceCoefficientMatrices.a^2)=stepA (stepA (row g)) := by
  rw [pow_two,←mul_assoc,row_mul_a,row_mul_a]

theorem row_mul_c (g : IntegralGL) :
    row (g*ReferenceCoefficientMatrices.c)=cycleRow (cycleRow (row g)) := by
  rw [row_mul]
  funext i
  fin_cases i <;>
    simp [cycleRow,reduction,ReferenceCoefficientMatrices.c,
      ReferenceCoefficientMatrices.cMatrix,GeneralLinearGroup.map_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_three]

theorem row_mul_s (g : IntegralGL) :
    row (g*ReferenceCoefficientMatrices.s)=swapRow (row g) := by
  rw [row_mul]
  funext i
  fin_cases i <;>
    simp [swapRow,reduction,ReferenceCoefficientMatrices.s,
      ReferenceCoefficientMatrices.sMatrix,GeneralLinearGroup.map_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_three]

theorem system_permute {F : Covector → TernaryPolynomial} (h : System F)
    (π : Equiv.Perm (Fin 3)) (r : Covector) :
    F (permuteRow π r)=permutePoly π (F r) := by
  have he : signRow ∅ r=r := by funext i; simp [signRow]
  simpa [he,signPoly_empty] using h.signed ∅ π r

theorem system_cycle {F : Covector → TernaryPolynomial} (h : System F) (r : Covector) :
    F (cycleRow r)=C (F r) := by
  simpa only [permuteRow_cycle,permutePoly_cycle] using system_permute h cyclePerm r

theorem system_swap {F : Covector → TernaryPolynomial} (h : System F) (r : Covector) :
    F (swapRow r)=S (F r) := by
  simpa only [permuteRow_swap,permutePoly_swap] using system_permute h swapPerm r

/-- The residue-fiber equations impose the correct orientation under the integral cyclic frame matrix. -/
theorem framePoly_cyclic {F : Covector → TernaryPolynomial} (h : System F) (g : IntegralGL) :
    framePoly F (g*ReferenceCoefficientMatrices.c)=framePoly F g := by
  rw [framePoly,row_mul_c,map_mul,Module.End.mul_apply,ReferenceCoefficientMatrices.coefficientAction_c,
    system_cycle h,system_cycle h,C_C_C]
  rfl

/-- The coefficient determinant twist supplies the apartment transposition sign. -/
theorem framePoly_swap {F : Covector → TernaryPolynomial} (h : System F) (g : IntegralGL) :
    framePoly F (g*ReferenceCoefficientMatrices.s)= -framePoly F g := by
  rw [framePoly,row_mul_s,map_mul,Module.End.mul_apply,
    ReferenceCoefficientMatrices.coefficientAction_neg_one_s,system_swap h,S_S,map_neg]
  rfl

/-- Every literal integral augmented tetrahedron receives the exact three-term norm relation. -/
theorem framePoly_norm {F : Covector → TernaryPolynomial} (h : System F) (g : IntegralGL) :
    framePoly F g+framePoly F (g*ReferenceCoefficientMatrices.a)+
      framePoly F (g*ReferenceCoefficientMatrices.a^2)=0 := by
  simp only [framePoly,row_mul_a,row_mul_a_sq,map_mul,Module.End.mul_apply,
    ReferenceCoefficientMatrices.coefficientAction_a,ReferenceCoefficientMatrices.coefficientAction_a_sq]
  rw [←map_add,←map_add]
  have hn := h.norm (row g) (row_ne_zero g)
  have he : F (row g)+A2 (F (stepA (row g)))+A (F (stepA (stepA (row g))))=0 := by
    simpa only [fiberNorm,add_assoc,add_comm,add_left_comm] using hn
  rw [he,map_zero]

end TernaryPoly.OrdinaryFiberComparison
