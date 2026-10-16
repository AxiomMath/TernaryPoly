module

public import TernaryPeriodPolynomials.PeriodPolynomial.ComplexPeriod.Span
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodEquiv

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryComplexPeriod
open SinglePoleCoordinate OrdinaryFullCoefficient OrdinaryResiduePeriod

/-- The field-generic equations agree literally with the original rational period relations. -/
theorem rational_relations_iff (q : MvPolynomial (Fin 2) ℚ) :
    Relations ℚ q ↔ SymmetricBinaryPeriodRelations q := by
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨h0,h1,h2,h3⟩
  · intro h
    exact ⟨h.swap,h.odd_first,h.odd_second,h.period⟩

/-- The original nested homogeneous period subtype and the scalar-extension interface are identical
on their literal polynomial values. -/
def rationalEquiv (d : ℕ) : periodSpace d ≃ₗ[ℚ] space ℚ d where
  toFun q := ⟨q.val.val,q.val.property,(rational_relations_iff _).mpr q.property⟩
  invFun q := ⟨⟨q.val,q.property.1⟩,(rational_relations_iff _).mp q.property.2⟩
  left_inv _q := rfl
  right_inv _q := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual ordinary residue map, in the scalar-extension-ready period coordinates. -/
def actualPeriodEquiv (n : ℕ) : ResidueHom n (-1) ≃ₗ[ℚ] space ℚ (n+1) :=
  (periodEquiv n).trans (rationalEquiv (n+1))

@[simp] theorem actualPeriodEquiv_value (n : ℕ) (F : ResidueHom n (-1)) :
    (actualPeriodEquiv n F).val=(coordinatePeriod n 0 F).val := rfl

/-- The actual liftable subspace transported by the proved literal coordinate equivalence. -/
def actualLiftable (n : ℕ) : Submodule ℚ (space ℚ (n+1)) :=
  (liftableResidueHoms n (-1)).map (actualPeriodEquiv n).toLinearMap

/-- Its whole extreme functional vanishes, with no arithmetic or ES input. -/
theorem actualLiftable_extreme (n : ℕ) (q : space ℚ (n+1)) (hq : q ∈ actualLiftable n) :
    extreme ℚ (n+1) q=0 := by
  obtain ⟨F,hF,rfl⟩ := hq
  change (coordinatePeriod n 0 F).val.coeff (Finsupp.single 0 1+Finsupp.single 1 (n+1-1))=0
  have he : Finsupp.cons 1 (Finsupp.single (0 : Fin 1) n)=
      Finsupp.single 0 1+Finsupp.single 1 (n+1-1) := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.single (0 : Fin 1) n) 0 = _
      simp
  rw [←he]
  exact liftable_coordinate_extreme n F hF 0 _

/-- The actual complex span retains the entire extreme-coefficient zero. -/
theorem actualLiftable_complex_extreme (n : ℕ) :
    ∀ q ∈ complexSpan (n+1) (actualLiftable n),extreme ℂ (n+1) q=0 :=
  complexSpan_extreme (n+1) (actualLiftable n) (actualLiftable_extreme n)

/-- Vanishing of the actual complexified coordinate space kills every actual liftable residue. -/
theorem liftable_residue_zero_of_complexSpan (n : ℕ)
    (h : complexSpan (n+1) (actualLiftable n)=⊥)
    (F : ResidueHom n (-1)) (hF : F ∈ liftableResidueHoms n (-1)) : F=0 := by
  have hz := (complexSpan_eq_bot_iff (n+1) (actualLiftable n)).mp h
  have hm : actualPeriodEquiv n F ∈ actualLiftable n := ⟨F,hF,rfl⟩
  rw [hz] at hm
  apply (actualPeriodEquiv n).injective
  simpa only [map_zero] using (Submodule.mem_bot ℚ).mp hm

end TernaryPoly.BinaryComplexPeriod
