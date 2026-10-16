module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddBoundary
public import TernaryPeriodPolynomials.Analysis.CoordinateSumQuotient

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The actual corrected symmetric Todd expression is additive. -/
theorem symmetricTodd_add (f g : TernaryPolynomial) :
    symmetricTodd (f+g) = symmetricTodd f+symmetricTodd g := by
  have hframe : symmetricFrame2 (f+g) = symmetricFrame2 f+symmetricFrame2 g := by
    simp only [symmetricFrame2,symmetricFrame1,substitute3,map_add]
    abel
  simp only [symmetricTodd,hframe,symmetricFrame1,substitute3,map_add,ternaryTodd]
  ring

/-- The actual corrected symmetric Todd expression respects subtraction. -/
theorem symmetricTodd_sub (f g : TernaryPolynomial) :
    symmetricTodd (f-g) = symmetricTodd f-symmetricTodd g := by
  have hframe : symmetricFrame2 (f-g) = symmetricFrame2 f-symmetricFrame2 g := by
    simp only [symmetricFrame2,symmetricFrame1,substitute3,map_sub]
    abel
  simp only [symmetricTodd,hframe,symmetricFrame1,substitute3,map_sub,ternaryTodd]
  ring

@[simp] theorem symmetricTodd_zero : symmetricTodd 0 = 0 := by
  simp [symmetricTodd,ternaryTodd,symmetricFrame1,symmetricFrame2,substitute3]

/-- Coordinate-sum division preserves full swap symmetry. -/
theorem symmetric_of_coordinate_sum_pow_mul {f : TernaryPolynomial} (r : ℕ)
    (hs : S ((X 0+X 1+X 2)^r*f) = (X 0+X 1+X 2)^r*f) : S f = f := by
  apply mul_left_cancel₀ (pow_ne_zero r coordinate_sum_ne_zero)
  have hw : S (X 0+X 1+X 2) = (X 0+X 1+X 2 : TernaryPolynomial) := by
    simp [S]
    ring
  simpa only [map_mul,map_pow,hw] using hs

/-- Coordinate-sum division preserves the entire symmetric Todd kernel. -/
theorem symmetricTodd_of_coordinate_sum_pow_mul {f : TernaryPolynomial} (r : ℕ)
    (hJ : symmetricTodd ((X 0+X 1+X 2)^r*f) = 0) : symmetricTodd f = 0 := by
  rw [symmetricTodd_W_pow_mul] at hJ
  have hlin : (X 2-3*X 1 : TernaryPolynomial) ≠ 0 := by
    intro h
    have he := congrArg (bind₁ (![0,0,1] : Fin 3 → TernaryPolynomial)) h
    simp at he
  exact (mul_eq_zero.mp hJ).resolve_left (pow_ne_zero r hlin)

/-- The actual double-plane quotient has lower degree and retains all kernel symmetries. -/
theorem symmetric_normal_quotient_data {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hc : C f = f) (hs : S f = f)
    (hJ : symmetricTodd f = 0) (g : TernaryPolynomial)
    (hg : f = (X 0+X 1+X 2)^2*g) :
    g.IsHomogeneous (n-2) ∧ C g = g ∧ S g = g ∧ symmetricTodd g = 0 ∧
      (g ≠ 0 → 2 ≤ n) := by
  have hWh : ((X 0+X 1+X 2 : TernaryPolynomial)^2).IsHomogeneous 2 := by
    simpa only [one_mul] using coordinate_sum_isHomogeneous.pow 2
  have hW0 := pow_ne_zero 2 coordinate_sum_ne_zero
  have hgh : ((X 0+X 1+X 2)^2*g).IsHomogeneous n := by rwa [← hg]
  refine ⟨isHomogeneous_quotient hWh hW0 hgh,
    cyclic_of_coordinate_sum_pow_mul 2 (by rwa [← hg]),
    symmetric_of_coordinate_sum_pow_mul 2 (by rwa [← hg]),
    symmetricTodd_of_coordinate_sum_pow_mul 2 (by rwa [← hg]),?_⟩
  intro hg0
  have ht := hgh.totalDegree (mul_ne_zero hW0 hg0)
  rw [totalDegree_mul_of_isDomain hW0 hg0,hWh.totalDegree hW0] at ht
  omega

end TernaryPoly
