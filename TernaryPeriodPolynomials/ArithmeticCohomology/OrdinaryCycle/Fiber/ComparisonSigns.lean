module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.ComparisonFrames
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Frames

@[expose] public section

open Matrix MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFiberComparison
open ModThreeGoodAction OrdinaryCovectors OrdinaryApartmentFrames
open OrdinaryPolynomialFiberSystem OrdinaryFiberPermutations OrdinarySignedFibers

/-- The residue row transforms by exactly the same independent column signs. -/
theorem row_mul_signFrame (g : IntegralGL) (s : Finset (Fin 3)) :
    OrdinaryCovectors.row (g*signFrame s)=signRow s (OrdinaryCovectors.row g) := by
  rw [row_mul]
  funext i
  change Matrix.vecMul (OrdinaryCovectors.row g)
    ((Matrix.diagonal (signEntry s)).map (Int.castRingHom (ZMod 3))) i=_
  rw [Matrix.diagonal_map (map_zero _),Matrix.vecMul_diagonal]
  by_cases hi : i∈s <;> simp [signEntry,signRow,hi]

/-- The determinant of the integral sign matrix is its product-of-signs character. -/
theorem signFrame_det (s : Finset (Fin 3)) :
    (signFrame s).val.det=(-1 : ℤ)^s.card := by
  change (Matrix.diagonal (signEntry s)).det=_
  rw [Matrix.det_diagonal]
  simp [signEntry]

/-- Literal inverse substitution for a sign frame negates exactly its selected variables. -/
theorem substitute_signFrame (s : Finset (Fin 3)) :
    PolynomialGLAction.substitute
      ((ReferenceCoefficientMatrices.rational (signFrame s))⁻¹ : PolynomialGLAction.GL3)=signPoly s := by
  rw [←map_inv,signFrame_inv]
  apply MvPolynomial.algHom_ext
  intro i
  change PolynomialGLAction.substitute
    ((Matrix.diagonal (signEntry s)).map (Int.castRingHom ℚ)) (X i)=signPoly s (X i)
  rw [PolynomialGLAction.substitute_X,Matrix.diagonal_map (map_zero _)]
  simp only [PolynomialGLAction.linearForm,signPoly,bind₁_X_right]
  rw [Finset.sum_eq_single i]
  · by_cases hi : i∈s <;> simp [signEntry,hi]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem signPoly_signPoly (s : Finset (Fin 3)) (p : TernaryPolynomial) :
    signPoly s (signPoly s p)=p := by
  have he : (signPoly s).comp (signPoly s)=AlgHom.id ℚ TernaryPolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i∈s <;> simp [signPoly,hi,AlgHom.comp_apply]
  exact DFunLike.congr_fun he p

theorem coefficientAction_signFrame (s : Finset (Fin 3)) (p : TernaryPolynomial) :
    ReferenceCoefficientMatrices.coefficientAction (-1) (signFrame s) p=
      (-1 : ℚ)^s.card • signPoly s p := by
  change PolynomialGLAction.action (-1) (ReferenceCoefficientMatrices.rational (signFrame s)) p=_
  rw [PolynomialGLAction.action_apply,substitute_signFrame]
  have hd : ((GeneralLinearGroup.det (ReferenceCoefficientMatrices.rational (signFrame s)) : ℚˣ) : ℚ)=
      (-1 : ℚ)^s.card := by
    rw [GeneralLinearGroup.map_det]
    change ((signFrame s).val.det : ℚ)=_
    rw [signFrame_det]
    push_cast
    rfl
  change (((GeneralLinearGroup.det (ReferenceCoefficientMatrices.rational (signFrame s)) : ℚˣ) : ℚ)^(-1 : ℤ)) • _=_
  rw [hd]
  have hx : (-1 : ℚ)^s.card * (-1 : ℚ)^s.card=1 := by rw [←mul_pow]; norm_num
  rw [zpow_neg_one,inv_eq_of_mul_eq_one_right hx]

theorem system_sign {F : Covector → TernaryPolynomial} (h : System F)
    (s : Finset (Fin 3)) (r : Covector) :
    F (signRow s r)=(-1 : ℚ)^s.card • signPoly s (F r) := by
  have he := h.signed s 1 r
  rw [permutePoly_one] at he
  exact he

/-- The determinant twist and the signed fiber character cancel for every column sign. -/
theorem framePoly_signs {F : Covector → TernaryPolynomial} (h : System F)
    (g : IntegralGL) (s : Finset (Fin 3)) : framePoly F (g*signFrame s)=framePoly F g := by
  rw [framePoly,row_mul_signFrame,map_mul,Module.End.mul_apply,coefficientAction_signFrame,
    system_sign h]
  simp only [map_smul,signPoly_signPoly,smul_smul,←mul_pow]
  norm_num
  rfl

/-- The ordinary frame polynomial depends only on its ordered rational column lines. -/
theorem framePoly_eq_of_triangleList {F : Covector → TernaryPolynomial} (hF : System F)
    (g h : IntegralGL) (he : GoodRelativeChains.triangleList g=GoodRelativeChains.triangleList h) :
    framePoly F g=framePoly F h := by
  have hh : AugmentedFrameComplex.augmentedLine g 0=AugmentedFrameComplex.augmentedLine h 0 ∧
      AugmentedFrameComplex.augmentedLine g 1=AugmentedFrameComplex.augmentedLine h 1 ∧
      AugmentedFrameComplex.augmentedLine g 2=AugmentedFrameComplex.augmentedLine h 2 := by
    simpa only [GoodRelativeChains.triangleList,List.cons.injEq,and_true] using he
  obtain ⟨s,rfl⟩ := eq_mul_signFrame_of_column_lines g h (by
    intro j
    fin_cases j
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2)
  exact (framePoly_signs hF g s).symm

theorem frameValue_cyclic (n : ℕ) {F : Covector → TernaryPolynomial} (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) :
    frameValue n F hF (g*ReferenceCoefficientMatrices.c)=frameValue n F hF g := by
  apply Subtype.ext
  exact framePoly_cyclic h g

theorem frameValue_swap (n : ℕ) {F : Covector → TernaryPolynomial} (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) :
    frameValue n F hF (g*ReferenceCoefficientMatrices.s)= -frameValue n F hF g := by
  apply Subtype.ext
  exact framePoly_swap h g

theorem frameValue_norm (n : ℕ) {F : Covector → TernaryPolynomial} (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) :
    frameValue n F hF g+frameValue n F hF (g*ReferenceCoefficientMatrices.a)+
      frameValue n F hF (g*ReferenceCoefficientMatrices.a^2)=0 := by
  apply Subtype.ext
  exact framePoly_norm h g

theorem frameValue_signs (n : ℕ) {F : Covector → TernaryPolynomial} (h : System F)
    (hF : ∀ r,(F r).IsHomogeneous n) (g : IntegralGL) (s : Finset (Fin 3)) :
    frameValue n F hF (g*signFrame s)=frameValue n F hF g := by
  apply Subtype.ext
  exact framePoly_signs h g s

theorem frameValue_eq_of_triangleList (n : ℕ) {F : Covector → TernaryPolynomial} (hF : System F)
    (hh : ∀ r,(F r).IsHomogeneous n) (g h : IntegralGL)
    (he : GoodRelativeChains.triangleList g=GoodRelativeChains.triangleList h) :
    frameValue n F hh g=frameValue n F hh h := by
  apply Subtype.ext
  exact framePoly_eq_of_triangleList hF g h he

end TernaryPoly.OrdinaryFiberComparison
