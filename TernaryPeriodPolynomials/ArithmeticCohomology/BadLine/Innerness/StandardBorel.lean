module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.UpperPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.FiniteIndexPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def standardBorel : Subgroup RationalGL3 := rationalLevel ⊓ (parabolic .plane ⊓ parabolic .line)

theorem standardBorel_lower (g : standardBorel) :
    g.val.val 1 0 = 0 ∧ g.val.val 2 0 = 0 ∧ g.val.val 2 1 = 0 :=
  ⟨g.property.2.2.1,g.property.2.1.1,g.property.2.1.2⟩

theorem standardBorel_integral (g : standardBorel) :
    ∃ V : IntegralGL3, GeneralLinearGroup.map (Int.castRingHom ℚ) V = g.val := by
  have level := g.property.1
  change g.val ∈ rationalInclusion.range at level
  obtain ⟨V,equal⟩ := MonoidHom.mem_range.mp level
  exact ⟨V.val,equal⟩

theorem standardBorel_integral_lower (g : standardBorel) (V : IntegralGL3)
    (equal : GeneralLinearGroup.map (Int.castRingHom ℚ) V = g.val) :
    V.val 1 0 = 0 ∧ V.val 2 0 = 0 ∧ V.val 2 1 = 0 := by
  have lower := standardBorel_lower g
  rw [← equal] at lower
  change (V.val 1 0 : ℚ) = 0 ∧ (V.val 2 0 : ℚ) = 0 ∧ (V.val 2 1 : ℚ) = 0 at lower
  exact_mod_cast lower

theorem standardBorel_diagonal_sign (g : standardBorel) (i : Fin 3) :
    g.val.val i i = 1 ∨ g.val.val i i = -1 := by
  obtain ⟨V,equal⟩ := standardBorel_integral g
  obtain ⟨h10,h20,h21⟩ := standardBorel_integral_lower g V equal
  have determinant_unit : IsUnit V.val.det := (GeneralLinearGroup.det V).isUnit
  have diagonal_units : IsUnit (V.val 0 0) ∧ IsUnit (V.val 1 1) ∧ IsUnit (V.val 2 2) := by
    simpa [Matrix.det_fin_three,h10,h20,h21,IsUnit.mul_iff,and_assoc] using determinant_unit
  have unit : IsUnit (V.val i i) := by
    fin_cases i
    · exact diagonal_units.1
    · exact diagonal_units.2.1
    · exact diagonal_units.2.2
  have sign := Int.isUnit_iff.mp unit
  rw [← equal]
  change (V.val i i : ℚ) = 1 ∨ (V.val i i : ℚ) = -1
  rcases sign with one | minus
  · left; rw [one]; norm_num
  · right; rw [minus]; norm_num

theorem standardBorel_diagonal_mul (g h : standardBorel) (i : Fin 3) :
    (g*h).val.val i i = g.val.val i i*h.val.val i i := by
  obtain ⟨g10,g20,g21⟩ := standardBorel_lower g
  obtain ⟨h10,h20,h21⟩ := standardBorel_lower h
  change (g.val*h.val).val i i = _
  rw [GeneralLinearGroup.coe_mul]
  fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_three,g10,g20,g21,h10,h20,h21]

theorem standardBorel_unipotent_mem (g : standardBorel) (diagonal : ∀ i, g.val.val i i = 1) :
    g.val ∈ integralUpperGroup := by
  obtain ⟨V,equal⟩ := standardBorel_integral g
  obtain ⟨h10,h20,h21⟩ := standardBorel_integral_lower g V equal
  have diagonalV (i : Fin 3) : V.val i i = 1 := by
    have entry := diagonal i
    rw [← equal] at entry
    change (V.val i i : ℚ) = 1 at entry
    exact_mod_cast entry
  refine ⟨(V.val 0 1,V.val 0 2-V.val 0 1*V.val 1 2,V.val 1 2),?_⟩
  rw [← equal]
  apply Units.ext
  rw [upperElement_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply,h10,h20,h21,diagonalV]

theorem standardBorel_same_diagonal (g h : standardBorel)
    (diagonal : ∀ i, g.val.val i i = h.val.val i i) :
    (g⁻¹*h).val ∈ integralUpperGroup := by
  apply standardBorel_unipotent_mem
  intro i
  rw [standardBorel_diagonal_mul,← diagonal i,← standardBorel_diagonal_mul,inv_mul_cancel]
  change (1 : Matrix (Fin 3) (Fin 3) ℚ) i i = 1
  simp

instance standardBorel_quotient_finite : Finite (standardBorel ⧸ integralUpperGroup.subgroupOf standardBorel) := by
  classical
  let signs := fun q : standardBorel ⧸ integralUpperGroup.subgroupOf standardBorel =>
    fun i : Fin 3 => decide (q.out.val.val i i = 1)
  apply Finite.of_injective signs
  intro q r equal
  have diagonal (i : Fin 3) : q.out.val.val i i = r.out.val.val i i := by
    have at_i := congrFun equal i
    change decide (q.out.val.val i i = 1) = decide (r.out.val.val i i = 1) at at_i
    rcases standardBorel_diagonal_sign q.out i with hq | hq
    · have hr : r.out.val.val i i = 1 := by
        apply of_decide_eq_true
        simpa only [hq,decide_true] using at_i.symm
      exact hq.trans hr.symm
    · rcases standardBorel_diagonal_sign r.out i with hr | hr
      · rw [hq,hr] at at_i
        norm_num at at_i
      · exact hq.trans hr.symm
  have cosets : (QuotientGroup.mk q.out : standardBorel ⧸ integralUpperGroup.subgroupOf standardBorel) =
      QuotientGroup.mk r.out := QuotientGroup.eq.mpr (standardBorel_same_diagonal q.out r.out diagonal)
  simpa only [QuotientGroup.out_eq'] using cosets

theorem normalizedBadLine_standardBorel_primitive (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∃ primitive : cochains standardBorel (rationalCoefficientComponent n trivialCharacter) 1,
      ∀ vertices, (differentialOne standardBorel
        (rationalCoefficientComponent n trivialCharacter) primitive).val vertices = c.val.val vertices := by
  let := Fintype.ofFinite (standardBorel ⧸ integralUpperGroup.subgroupOf standardBorel)
  obtain ⟨primitive,equal⟩ := normalizedBadLine_upperGroup_primitive n positive f solution c normalized
  exact cocycle_primitive_of_finite_index rationalLevel integralUpperGroup standardBorel inf_le_left
    (rationalCoefficientComponent n trivialCharacter) c primitive equal

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
