module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.LineAct

@[expose] public section


/-!
# The orientation characters of a face and their product

Formalized by Claude Sonnet 5.5.

For the line face `Q` and the stabilizer element `g = [[a, v],[0, A]]` (`a = ±1`, `A ∈ GL₂(ℤ)`), the action `x ↦ g x gᵗ` on the symmetric matrices (the tangent space of the cone over the symmetric space of `SL₃`) is block triangular for the filtration
`T` (base), `w` (radical), `s` (normal direction) with diagonal blocks `A T Aᵗ`, `a A`, `a²` (`line_orientation_factorisation`).  Their determinants are the **base orientation character** `ε_L = det A³ = det A`
(the orientation of the modular curve: `A` reverses it iff `det A = -1`; the library's `cuspConjNat` scales the cup-form pairing by `det A`), the **radical orientation character** `ε_N = a² det A = det A`
(the Koszul pairing scales by the determinant of the Levi action on the radical lattice, `PhiC_pullback`, `radDet_rowAct`) and the positive normal factor `a²`.
Since the action on the five-dimensional symmetric space has trivial orientation character, `det (x ↦ g x gᵗ) = (det g)⁴ = 1`, and
`ε_N · ε_L = 1` is the (trivial) orientation character of the face (`line_characters_multiply`).  The same for the plane face `P` (`plane_*`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section Radical

/-- The row-vector action `r ↦ r A` of an integral `2 × 2` matrix on the radical lattice (the Levi action on the radical of a line face). -/
def rowAct (A : Matrix (Fin 2) (Fin 2) ℤ) : RadicalLattice →* RadicalLattice where
  toFun r := Multiplicative.ofAdd (r.toAdd.1 * A 0 0 + r.toAdd.2 * A 1 0, r.toAdd.1 * A 0 1 + r.toAdd.2 * A 1 1)
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.mk_add_mk]
    ext <;> (simp; try ring)

/-- **The determinant of the Levi action on the radical lattice is `det A`.** -/
theorem radDet_rowAct (A : Matrix (Fin 2) (Fin 2) ℤ) : radDet (rowAct A) = A.det := by
  simp [radDet, rowAct, rl1, rl2, radicalLatticeFirst, radicalLatticeSecond, Matrix.det_fin_two]

/-- The column-vector action `r ↦ B r` of an integral `2 × 2` matrix on the radical lattice (the Levi action on the radical of a plane face, `B = A⁻¹`). -/
def colAct (B : Matrix (Fin 2) (Fin 2) ℤ) : RadicalLattice →* RadicalLattice where
  toFun r := Multiplicative.ofAdd (B 0 0 * r.toAdd.1 + B 0 1 * r.toAdd.2, B 1 0 * r.toAdd.1 + B 1 1 * r.toAdd.2)
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.mk_add_mk]
    ext <;> (simp; try ring)

theorem radDet_colAct (B : Matrix (Fin 2) (Fin 2) ℤ) : radDet (colAct B) = B.det := by
  simp [radDet, colAct, rl1, rl2, radicalLatticeFirst, radicalLatticeSecond, Matrix.det_fin_two]
  try ring

end Radical

section Numbers

theorem det_mul_self_eq_one {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsUnit A.det) : A.det * A.det = 1 := by
  rcases Int.isUnit_iff.1 hA with h | h <;> rw [h] <;> norm_num

/-- The determinant of the inverse of an integral unimodular matrix equals its determinant. -/
theorem det_inverse_eq {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsUnit A.det) (hAB : A * B = 1) : B.det = A.det := by
  have h1 : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have h2 := det_mul_self_eq_one hA
  have : A.det * (B.det - A.det) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hA.ne_zero)
  · linarith

end Numbers

section Line

variable (a : ℤ) (v : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ)

theorem det_lineElt : (lineElt a v A).det = a * A.det := by
  simp [lineElt, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- **Factorisation of the orientation of the cone for a line face**: normal factor `a²`, radical factor `det (a A)`, base factor `det (A T Aᵗ) = det A³`. -/
theorem line_orientation_factorisation :
    (lineActMat a v A).det = a ^ 2 * (a • A).det * (sym2Act A).det := by
  rw [det_lineActMat, det_sym2Act, Matrix.det_smul]
  simp
  ring

/-- **The orientation characters of a line face multiply to the face orientation.**  For `a = ±1`, `A` unimodular: the radical character `det (a A)` and the base character `det (A T Aᵗ)` both equal `det A`; their product is `1`, which is
the orientation character of the face, namely `(det g)⁴ / a² = 1` (the ambient orientation character is trivial, the normal factor is `a² = 1`). -/
theorem line_characters_multiply (ha : a * a = 1) (hA : IsUnit A.det) :
    (a • A).det = A.det ∧ (sym2Act A).det = A.det ∧ (a • A).det * (sym2Act A).det = 1 ∧
      (lineActMat a v A).det = 1 ∧ (lineActMat a v A).det = (lineElt a v A).det ^ 4 := by
  have h2 := det_mul_self_eq_one hA
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact ha
  have h1 : (a • A).det = A.det := by
    rw [Matrix.det_smul, Fintype.card_fin, ha2, one_mul]
  have h3 : (sym2Act A).det = A.det := by
    rw [det_sym2Act]
    calc A.det ^ 3 = A.det * (A.det * A.det) := by ring
      _ = A.det := by rw [h2, mul_one]
  refine ⟨h1, h3, ?_, ?_, ?_⟩
  · rw [h1, h3, h2]
  · rw [line_orientation_factorisation, h1, h3, ha2, one_mul, h2]
  · rw [det_lineActMat, det_lineElt]; ring

end Line

section Plane

variable (a : ℤ) (v : Fin 2 → ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ)

theorem det_planeElt : (planeElt a v A).det = a * A.det := by
  simp [planeElt, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- **Factorisation of the orientation of the cone for a plane face.** -/
theorem plane_orientation_factorisation :
    (planeActMat a v A).det = a ^ 2 * (a • A).det * (sym2Act A).det := by
  rw [det_planeActMat, det_sym2Act, Matrix.det_smul]
  simp
  ring

/-- **The orientation characters of a plane face multiply to the face orientation.** -/
theorem plane_characters_multiply (ha : a * a = 1) (hA : IsUnit A.det) :
    (a • A).det = A.det ∧ (sym2Act A).det = A.det ∧ (a • A).det * (sym2Act A).det = 1 ∧
      (planeActMat a v A).det = 1 ∧ (planeActMat a v A).det = (planeElt a v A).det ^ 4 := by
  have h2 := det_mul_self_eq_one hA
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact ha
  have h1 : (a • A).det = A.det := by
    rw [Matrix.det_smul, Fintype.card_fin, ha2, one_mul]
  have h3 : (sym2Act A).det = A.det := by
    rw [det_sym2Act]
    calc A.det ^ 3 = A.det * (A.det * A.det) := by ring
      _ = A.det := by rw [h2, mul_one]
  refine ⟨h1, h3, ?_, ?_, ?_⟩
  · rw [h1, h3, h2]
  · rw [plane_orientation_factorisation, h1, h3, ha2, one_mul, h2]
  · rw [det_planeActMat, det_planeElt]; ring

end Plane

/-- **The Koszul scaling and the Poincaré-Lefschetz scaling of a Levi element cancel.**  The Levi element `A ∈ GL₂(ℤ)` of a line face acts on the radical lattice with determinant `det A` (`radDet_rowAct`: the Koszul pairing is scaled by it,
`PhiC_pullback`) and reverses the orientation of the modular curve iff `det A = -1` (`cuspConjNat`: the cup-form pairing is scaled by `det A`).  The product of the two scalars is `1`. -/
theorem koszul_times_base_scale {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsUnit A.det) :
    (radDet (rowAct A) : ℤ) * A.det = 1 := by
  rw [radDet_rowAct]; exact det_mul_self_eq_one hA

/-- The same for the plane face (Levi acting on the radical lattice by `A⁻¹`). -/
theorem koszul_times_base_scale_plane {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsUnit A.det) (hAB : A * B = 1) :
    (radDet (colAct B) : ℤ) * A.det = 1 := by
  rw [radDet_colAct, det_inverse_eq hA hAB]; exact det_mul_self_eq_one hA

end TernaryPeriodPolynomials.Argument.FaceDescent
