module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.TranslationPrimitive
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem pderiv_commute_apply (i j : Fin 3) (p : Poly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  ext exponent
  simp only [coeff_pderiv]
  by_cases equal : i = j
  · subst j
    rfl
  · have indices : exponent + Finsupp.single i 1 + Finsupp.single j 1 =
        exponent + Finsupp.single j 1 + Finsupp.single i 1 := by abel
    simp only [indices,Finsupp.add_apply,Finsupp.single_eq_of_ne equal,
      Finsupp.single_eq_of_ne (Ne.symm equal),add_zero]
    ring

theorem radicalPairCoordinate_sub (n : ℕ) (a b a' b' : HomogeneousPoly n) :
    radicalPairCoordinate n (a-a') (b-b') =
      radicalPairCoordinate n a b-radicalPairCoordinate n a' b' := by
  simp only [radicalPairCoordinate,Submodule.coe_sub,bernoulliOperator_sub]
  ring

theorem radicalPairCoordinate_independent (n : ℕ) (a b : HomogeneousPoly n)
    (ha : pderiv 0 a.val = 0) (hb : pderiv 0 b.val = 0) :
    radicalPairCoordinate n a b = X 2*a.val-X 1*b.val := by
  rw [radicalPairCoordinate,bernoulliOperator_eq_of_pderiv_zero n (X 1) a.val ha,
    bernoulliOperator_eq_of_pderiv_zero n (X 2) b.val hb]

theorem binary_coordinate_lift (n : ℕ) (p : HomogeneousPoly (n+1))
    (independent : pderiv 0 p.val = 0) :
    ∃ a b : HomogeneousPoly n, pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧
      radicalPairCoordinate n a b = p.val := by
  let a : HomogeneousPoly n := ⟨((n+1 : ℕ) : ℂ)⁻¹ • pderiv 2 p.val,by
    apply (HomogeneousPoly n).smul_mem
    change (pderiv 2 p.val).IsHomogeneous n
    simpa only [Nat.add_sub_cancel] using pderiv_homogeneous p.val p.property 2⟩
  let b : HomogeneousPoly n := ⟨-(((n+1 : ℕ) : ℂ)⁻¹ • pderiv 1 p.val),by
    apply (HomogeneousPoly n).neg_mem
    apply (HomogeneousPoly n).smul_mem
    change (pderiv 1 p.val).IsHomogeneous n
    simpa only [Nat.add_sub_cancel] using pderiv_homogeneous p.val p.property 1⟩
  have ha : pderiv 0 a.val = 0 := by
    change pderiv 0 (((n+1 : ℕ) : ℂ)⁻¹ • pderiv 2 p.val) = 0
    rw [Derivation.map_smul,pderiv_commute_apply,independent,map_zero,smul_zero]
  have hb : pderiv 0 b.val = 0 := by
    change pderiv 0 (-(((n+1 : ℕ) : ℂ)⁻¹ • pderiv 1 p.val)) = 0
    rw [map_neg,Derivation.map_smul,pderiv_commute_apply,independent,map_zero,smul_zero,neg_zero]
  refine ⟨a,b,ha,hb,?_⟩
  rw [radicalPairCoordinate_independent n a b ha hb]
  have euler := p.property.sum_X_mul_pderiv
  rw [Fin.sum_univ_three,independent,mul_zero,zero_add] at euler
  have nonzero : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have scaled := congrArg (fun q : Poly => ((n+1 : ℕ) : ℂ)⁻¹ • q) euler
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ nonzero,one_smul] at scaled
  change X 2 * (((n+1 : ℕ) : ℂ)⁻¹ • pderiv 2 p.val) -
    X 1 * (-(((n+1 : ℕ) : ℂ)⁻¹ • pderiv 1 p.val)) = p.val
  calc
    _ = ((n+1 : ℕ) : ℂ)⁻¹ • (X 1*pderiv 1 p.val+X 2*pderiv 2 p.val) := by
      simp only [smul_add,mul_smul_comm,mul_neg,sub_neg_eq_add,add_comm]
    _ = p.val := scaled

theorem independent_pair_cocycle (n : ℕ) (a b : HomogeneousPoly n)
    (ha : pderiv 0 a.val = 0) (hb : pderiv 0 b.val = 0) (x y : ℤ × ℤ) :
    (x+y).1 • a+(x+y).2 • b = x.1 • a+x.2 • b+
      rationalCoefficientComponent n trivialCharacter (integralRadicalHom (Multiplicative.ofAdd x))
        (y.1 • a+y.2 • b) := by
  have fixes_a := rationalCoefficient_fixes_independent n a ha (x.1 : ℚ) (x.2 : ℚ)
  have fixes_b := rationalCoefficient_fixes_independent n b hb (x.1 : ℚ) (x.2 : ℚ)
  simp only [Prod.fst_add,Prod.snd_add,add_smul,map_add,map_zsmul]
  change _ = _ + (y.1 • rationalCoefficientComponent n trivialCharacter
    (Adelic.lineUnipotent (x.1 : ℚ) (x.2 : ℚ)) a + y.2 • rationalCoefficientComponent n trivialCharacter
    (Adelic.lineUnipotent (x.1 : ℚ) (x.2 : ℚ)) b)
  rw [fixes_a,fixes_b]
  abel

theorem radical_cocycle_primitive_of_coordinate_zero (n : ℕ) (positive : 0 < n)
    (values : ℤ × ℤ → HomogeneousPoly n)
    (relation : ∀ x y, values (x+y) = values x +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) (values y))
    (coordinate_zero : radicalPairCoordinate n (values (1,0)) (values (0,1)) = 0) :
    ∃ primitive : HomogeneousPoly n, ∀ x,
      values x = primitive-rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x)) primitive := by
  obtain ⟨primitive,first,second⟩ := radical_primitive_of_bernoulli_zero n positive
    (values (1,0)) (values (0,1)) coordinate_zero
  let representation := (rationalCoefficientComponent n trivialCharacter).comp integralRadicalHom
  have equal := integerPair_cocycle_ext representation values
    (fun x => primitive-representation (Multiplicative.ofAdd x) primitive)
    relation (by
      intro x y
      rw [ofAdd_add,map_mul,Module.End.mul_apply,map_sub]
      abel)
    (by simpa [representation,integralRadicalHom] using first)
    (by simpa [representation,integralRadicalHom] using second)
  exact ⟨primitive,fun x => congrFun equal x⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
