module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.CoordinateLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem normalizedBadLine_upper_mixed_primitive (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∃ a b primitive : HomogeneousPoly n,
      pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧ ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c upperTranslation
          (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) +
        rationalCoefficientComponent n trivialCharacter upperTranslation (s • a+(s+t) • b) -
        (s • a+t • b) =
      primitive-rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive := by
  obtain ⟨q,hq,q_difference⟩ := normalizedBadLine_upper_coordinate_primitive n positive f solution c normalized
  obtain ⟨a,b,ha,hb,coordinate⟩ := binary_coordinate_lift n q hq
  let representation := rationalCoefficientComponent n trivialCharacter
  let a' := representation upperTranslation (a+b)-a
  let b' := representation upperTranslation b-b
  have acted_independent (p : HomogeneousPoly n) (hp : pderiv 0 p.val = 0) :
      pderiv 0 (representation upperTranslation p).val = 0 := by
    rw [rationalCoefficient_upperTranslation]
    exact upperTranslationSubstitution_preserves p.val hp
  have hab : pderiv 0 (a+b).val = 0 := by simp only [Submodule.coe_add,map_add,ha,hb,add_zero]
  have ha' : pderiv 0 a'.val = 0 := by
    simp only [a',Submodule.coe_sub,map_sub,acted_independent (a+b) hab,ha,sub_self]
  have hb' : pderiv 0 b'.val = 0 := by
    simp only [b',Submodule.coe_sub,map_sub,acted_independent b hb,hb,sub_self]
  have covariance := radicalPairCoordinate_upperTranslation n positive
    (fun x : ℤ × ℤ => x.1 • a+x.2 • b) (independent_pair_cocycle n a b ha hb)
  simp only [one_smul,zero_smul,add_zero,zero_add] at covariance
  have difference_coordinate : radicalPairCoordinate n a' b' =
      upperTranslationSubstitution q.val-q.val := by
    rw [radicalPairCoordinate_sub,covariance,coordinate]
  let values := fun x : ℤ × ℤ =>
    mixedValue rationalLevel representation c upperTranslation
      (integralRadicalHom (Multiplicative.ofAdd x)) + (x.1 • a'+x.2 • b')
  have values_relation (x y : ℤ × ℤ) : values (x+y) = values x +
      representation (integralRadicalHom (Multiplicative.ofAdd x)) (values y) := by
    dsimp only [values]
    rw [mixedValue_integralRadical_cocycle n c normalized.1
      ⟨upperTranslation,upperTranslation_mem⟩ upperTranslation_normalizes,
      independent_pair_cocycle n a' b' ha' hb']
    simp only [map_add]
    exact add_add_add_comm (G := HomogeneousPoly n) _ _ _ _
  have zero_coordinate : radicalPairCoordinate n (values (1,0)) (values (0,1)) = 0 := by
    have first_value : values (1,0) = mixedValue rationalLevel representation c upperTranslation
        (Adelic.lineUnipotent 1 0)+a' := by simp [values,integralRadicalHom]
    have second_value : values (0,1) = mixedValue rationalLevel representation c upperTranslation
        (Adelic.lineUnipotent 0 1)+b' := by simp [values,integralRadicalHom]
    rw [first_value,second_value,radicalPairCoordinate_add,
      ← mixedBernoulliCoordinate_eq_pair,difference_coordinate,q_difference]
    abel
  obtain ⟨primitive,hprimitive⟩ := radical_cocycle_primitive_of_coordinate_zero n positive
    values values_relation zero_coordinate
  refine ⟨a,b,primitive,ha,hb,?_⟩
  intro s t
  have result := hprimitive (s,t)
  change mixedValue rationalLevel representation c upperTranslation
    (Adelic.lineUnipotent (s : ℚ) (t : ℚ))+(s • a'+t • b') =
    primitive-representation (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive at result
  change mixedValue rationalLevel representation c upperTranslation
    (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) +
      representation upperTranslation (s • a+(s+t) • b) - (s • a+t • b) = _
  rw [← result]
  simp only [a',b',map_add,map_zsmul,smul_add,smul_sub,add_smul]
  abel

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
