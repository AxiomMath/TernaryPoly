module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SmoothVectors

@[expose] public section


/-!
# The `K∞`-type and level of the weight-`k` compression criterion

The compression criterion of `AbstractIrreducibility` is applied to the subgroup
`typeGroup K` of `GL₂(𝔸)` of adeles with finite part in an open compact subgroup `K` of `GL₂(𝔸_f)`
and archimedean part in `SO(2)`, with the character `c ↦ j(c_∞, i)^k` (the weight `k` character of
`SO(2)` through its action on `i`; it is trivial on the finite part).  `typeCharacter` is only
a function on the subgroup; the type subspace never uses multiplicativity.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Automorphic.TypeData

/-- The special orthogonal group `SO(2)` inside `GL₂(ℝ)`. -/
def so2 : Subgroup BinaryRealGL where
  carrier := {g | g.val.transpose * g.val = 1 ∧ g.val.det = 1}
  mul_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc a.val.transpose,
        ha, Matrix.one_mul, hb]
    · rw [Units.val_mul, Matrix.det_mul, hda, hdb, mul_one]
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro a ⟨ha, hda⟩
    have hco : a.val * a.val.transpose = 1 := mul_eq_one_comm.mp ha
    have hinv : (a⁻¹).val = a.val.transpose := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_right_inv hco
    refine ⟨?_, ?_⟩
    · rw [hinv, Matrix.transpose_transpose, hco]
    · rw [hinv, Matrix.det_transpose, hda]

/-- The subgroup of `GL₂(𝔸)` with finite part in `K` and archimedean part in `SO(2)`. -/
def typeGroup (K : Subgroup BinaryFiniteGL) : Subgroup BinaryAdelicGL :=
  (so2.prod K).comap (realPart.prod finitePart)

/-- The weight-`k` function `c ↦ (c_{21} i + c_{22})^k` of the archimedean part. -/
def typeCharacter (k : ℕ) (K : Subgroup BinaryFiniteGL) : typeGroup K → ℂ :=
  fun c => (((realPart c.val).val 1 0 : ℝ) * Complex.I + ((realPart c.val).val 1 1 : ℝ)) ^ k

theorem mem_typeGroup {K : Subgroup BinaryFiniteGL} {c : BinaryAdelicGL} :
    c ∈ typeGroup K ↔ realPart c ∈ so2 ∧ finitePart c ∈ K := Iff.rfl

end TernaryPeriodPolynomials.Automorphic.TypeData
