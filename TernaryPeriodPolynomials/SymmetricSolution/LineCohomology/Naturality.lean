module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Levi
public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.LeviAlgebra

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices groupCohomology

def eulerBinaryFirst (n : ℕ) (J : BinaryH (n+1)) : BP :=
  MvPolynomial.C (((n+1 : ℕ) : ℚ)⁻¹) * pderiv 1 (J : BP)

def eulerBinarySecond (n : ℕ) (J : BinaryH (n+1)) : BP :=
  -(MvPolynomial.C (((n+1 : ℕ) : ℚ)⁻¹)) * pderiv 0 (J : BP)

/-- The actual Euler cocycle is the additive integral combination of its two binary values. -/
theorem eulerCocycle_poly (n : ℕ) (J : BinaryH (n+1)) (g : Lattice) :
    (eulerCocycle n J g : Poly) = rename Fin.succ
      (g.toAdd.1 • eulerBinaryFirst n J + g.toAdd.2 • eulerBinarySecond n J) := by
  change g.toAdd.1 • ((eulerPair n J).val 0 : Poly) +
    g.toAdd.2 • ((eulerPair n J).val 1 : Poly) = _
  rw [map_add,map_zsmul,map_zsmul,eulerPair_first,eulerPair_second]
  rfl

/-- The actual normalizer acts on the explicit Euler representative. -/
def transformedEuler (n : ℕ) (t : ℤˣ) (L : GL2) (J : BinaryH (n+1)) :
    cocycles₁ (lineRep n) :=
  mapCocycles₁ (leviLatticeChange t L) (leviCoefficientHom n t L) (eulerCocycle n J)

theorem transformedEuler_poly (n : ℕ) (t : ℤˣ) (L : GL2) (J : BinaryH (n+1))
    (g : Lattice) :
    (transformedEuler n t L J g : Poly) =
      rename Fin.succ
        (((t.val : ℚ) * (L.val.det : ℚ))⁻¹ •
          binaryMatrixSubst (rationalBlock L⁻¹).val
            ((leviLatticeChange t L g).toAdd.1 • eulerBinaryFirst n J +
             (leviLatticeChange t L g).toAdd.2 • eulerBinarySecond n J)) := by
  change (PolynomialGLAction.integralAction n (-1) (lineElement t 0 L)
    (eulerCocycle n J (leviLatticeChange t L g)) : Poly) = _
  rw [lineLevi_action_rename _ _ _ _ _ (eulerCocycle_poly n J _),map_smul]

/-- The two factors of the integral line sign cancel, leaving only the lower determinant. -/
theorem transformedEuler_generator (n : ℕ) (t : ℤˣ) (L : GL2) (J : BinaryH (n+1))
    (j : Fin 2) :
    (transformedEuler n t L J (![first,second] j) : Poly) =
      rename Fin.succ (MvPolynomial.C ((L.val.det : ℚ)⁻¹) *
        (MvPolynomial.C (L.val j 0 : ℚ) *
            binaryMatrixSubst (rationalBlock L⁻¹).val (eulerBinaryFirst n J) +
         MvPolynomial.C (L.val j 1 : ℚ) *
            binaryMatrixSubst (rationalBlock L⁻¹).val (eulerBinarySecond n J))) := by
  rw [transformedEuler_poly]
  congr 1
  rcases Int.units_eq_one_or t with rfl | rfl <;> fin_cases j <;>
    simp [leviLatticeChange,first,second,map_add,
      ← Int.cast_smul_eq_zsmul ℚ,Algebra.smul_def] <;> ring

/-- The complete scalar of the transported Euler representative is inverse binary substitution. -/
theorem cocycleScalar_transformedEuler (n : ℕ) (t : ℤˣ) (L : GL2) (J : BinaryH (n+1)) :
    (cocycleScalar n (transformedEuler n t L J) : BP) =
      binaryMatrixSubst (rationalBlock L⁻¹).val (J : BP) := by
  apply (rename_injective _ (Fin.succ_injective 2))
  rw [cocycleScalar_rename]
  have h0 := transformedEuler_generator n t L J 0
  have h1 := transformedEuler_generator n t L J 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at h0 h1
  rw [h0,h1,ternaryTodd_rename_succ,ternaryTodd_rename_succ]
  have he := binary_radicalEuler_contraction (Nat.succ_pos n) J.property
  change X 1 * eulerBinaryFirst n J - X 0 * eulerBinarySecond n J = (J : BP) at he
  have hi := binary_inverse_contraction (rationalBlock L) (eulerBinaryFirst n J) (eulerBinarySecond n J)
  rw [he] at hi
  have hd : (rationalBlock L).val.det = (L.val.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det _).symm
  rw [hd] at hi
  have hv : (rationalBlock L)⁻¹ = rationalBlock L⁻¹ := (map_inv _ _).symm
  rw [hv] at hi
  have h := congrArg (rename (Fin.succ : Fin 2 → Fin 3)) hi
  simp only [map_mul,map_add,map_sub,rename_C,rename_X] at h
  change _ = _ at h
  convert h using 1
  simp [rationalBlock,GeneralLinearGroup.map_apply]
  ring

/-- Full integral Levi naturality of the complete scalar on every actual lattice H¹ class. -/
theorem latticeH1ScalarEquiv_Levi (n : ℕ) (t : ℤˣ) (L : GL2)
    (x : groupCohomology (lineRep n) 1) :
    (latticeH1ScalarEquiv n (latticeH1LeviAction n t L x) : BP) =
      binaryMatrixSubst (rationalBlock L⁻¹).val (latticeH1ScalarEquiv n x : BP) := by
  conv_lhs => rw [← H1π_eulerCocycle_scalar n x]
  change (latticeH1ScalarEquiv n
    (groupCohomology.map (leviLatticeChange t L) (leviCoefficientHom n t L) 1
      (H1π (lineRep n) (eulerCocycle n (latticeH1ScalarEquiv n x)))) : BP) = _
  rw [H1π_comp_map_apply,latticeH1ScalarEquiv_H1π]
  exact cocycleScalar_transformedEuler n t L (latticeH1ScalarEquiv n x)

/-- Full integral Levi naturality on the actual determinant-minus-one radical subgroup H¹.
The line unit contributes t⁻²=1, so the answer is exactly inverse lower-block substitution. -/
theorem subgroupH1ScalarEquiv_Levi (n : ℕ) (t : ℤˣ) (L : GL2)
    (x : groupCohomology (twistedSubgroupRep n) 1) :
    (subgroupH1ScalarEquiv n (subgroupH1LeviAction n t L x) : BP) =
      binaryMatrixSubst (rationalBlock L⁻¹).val (subgroupH1ScalarEquiv n x : BP) := by
  refine H1_induction_on x ?_
  intro c
  change (subgroupH1ScalarEquiv n
    (groupCohomology.map (leviSubgroupChange t L) (leviSubgroupCoefficientHom n t L) 1
      (H1π (twistedSubgroupRep n) c)) : BP) = _
  rw [H1π_comp_map_apply,subgroupH1ScalarEquiv_H1π,subgroupH1ScalarEquiv_H1π,
    ← levi_cocycles_parameter]
  have h := latticeH1ScalarEquiv_Levi n t L
    (H1π (lineRep n) (mapCocycles₁ lineParamEquiv.toMonoidHom (twistedParameterCoefficient n) c))
  unfold latticeH1LeviAction at h
  rw [H1π_comp_map_apply,latticeH1ScalarEquiv_H1π,latticeH1ScalarEquiv_H1π] at h
  exact h

end TernaryPoly.SymmetricLineCohomology
