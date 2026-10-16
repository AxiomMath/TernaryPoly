module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CanonicalTwist
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineConj

@[expose] public section


/-!
# The frame change of a line face as a twisted isomorphism of extensions (arithmetic part)

Formalized by Claude Sonnet 5.5.

For `q ∈ Q(ℚ) ∩ SL₃(ℤ)` with first column `(a, 0, 0)ᵗ` (`a = ±1`) and lower right block `A = botRight q`:
`lineBorel_a_sq` (`a² = 1`, `a · det A = 1`), `phiQ q`: the radical map `r ↦ a · r A` (conjugation `q⁻¹ rad(r) q = rad(φ r)`, `rad_mul_q`) and its determinant `radDet (phiQ q) = det A = a`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section Arith

variable {q : SL(3, ℤ)}

theorem lineBorel_det (hq : q ∈ lineBorel) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (botRight q 0 0 * botRight q 1 1 - botRight q 0 1 * botRight q 1 0) = 1 := by
  obtain ⟨h1, h2⟩ := hq
  have hdet : (q : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := q.2
  rw [Matrix.det_fin_three, h1, h2] at hdet
  simp only [botRight, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination hdet

theorem lineBorel_a_sq (hq : q ∈ lineBorel) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 := by
  have h := lineBorel_det hq
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ h) with h0 | h0 <;> rw [h0] <;> norm_num

theorem lineBorel_detA (hq : q ∈ lineBorel) :
    botRight q 0 0 * botRight q 1 1 - botRight q 0 1 * botRight q 1 0 = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  have h := lineBorel_det hq
  have h2 := lineBorel_a_sq hq
  linear_combination (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * h - (botRight q 0 0 * botRight q 1 1 - botRight q 0 1 * botRight q 1 0) * h2

end Arith


section Phi

/-- The radical map `r ↦ a · r A` of the frame change by `q` (`a` the `(0,0)` entry, `A = botRight q`). -/
def phiQHom (q : SL(3, ℤ)) : RadicalLattice →* RadicalLattice where
  toFun r := Multiplicative.ofAdd ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (r.toAdd.1 * botRight q 0 0 + r.toAdd.2 * botRight q 1 0),
    (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (r.toAdd.1 * botRight q 0 1 + r.toAdd.2 * botRight q 1 1))
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.mk_add_mk, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
    constructor <;> ring

theorem phiQHom_toAdd (q : SL(3, ℤ)) (r : RadicalLattice) :
    (phiQHom q r).toAdd = ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (r.toAdd.1 * botRight q 0 0 + r.toAdd.2 * botRight q 1 0),
      (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (r.toAdd.1 * botRight q 0 1 + r.toAdd.2 * botRight q 1 1)) := rfl

theorem inv_a {q : SL(3, ℤ)} (hq : q ∈ lineBorel) :
    ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  obtain ⟨h1, h2⟩ := hq
  have hm : ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have e := congrFun (congrFun hm 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h1, h2, mul_zero, add_zero, Matrix.one_apply_eq] at e
  have hsq := lineBorel_a_sq (q := q) ⟨h1, h2⟩
  linear_combination ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0) * e - ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * hsq

theorem phiQHom_inv {q : SL(3, ℤ)} (hq : q ∈ lineBorel) (r : RadicalLattice) : phiQHom q⁻¹ (phiQHom q r) = r := by
  apply Multiplicative.toAdd.injective
  have hA := (botRight_inv_mul q hq).1
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e01 e10 e11
  simp only [Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero] at e01 e10
  have ha := inv_a hq
  have hsq := lineBorel_a_sq hq
  rw [phiQHom_toAdd, phiQHom_toAdd]
  rw [ha]
  apply Prod.ext
  · simp only
    linear_combination (r.toAdd.1 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0)) * e00
      + (r.toAdd.2 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0)) * e10
      + r.toAdd.1 * hsq
  · simp only
    linear_combination (r.toAdd.1 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0)) * e01
      + (r.toAdd.2 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0)) * e11
      + r.toAdd.2 * hsq

/-- The radical map `φ_q` as an automorphism of the radical lattice. -/
def phiQ {q : SL(3, ℤ)} (hq : q ∈ lineBorel) : RadicalLattice ≃* RadicalLattice :=
  { phiQHom q with
    invFun := phiQHom q⁻¹
    left_inv := fun r => phiQHom_inv hq r
    right_inv := fun r => by
      have := phiQHom_inv (lineBorel.inv_mem hq) r
      rwa [inv_inv] at this }

theorem phiQ_apply {q : SL(3, ℤ)} (hq : q ∈ lineBorel) (r : RadicalLattice) : phiQ hq r = phiQHom q r := rfl

/-- **The determinant of the radical map is `det A = a`.** -/
theorem radDet_phiQ {q : SL(3, ℤ)} (hq : q ∈ lineBorel) :
    radDet (phiQ hq).toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 := by
  have h := lineBorel_detA hq
  have hsq := lineBorel_a_sq hq
  simp only [radDet, MulEquiv.coe_toMonoidHom, phiQ_apply, phiQHom_toAdd, rl1, rl2, radicalLatticeFirst,
    radicalLatticeSecond, toAdd_ofAdd]
  simp only [zero_mul, add_zero, zero_add, one_mul]
  linear_combination ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0) * h
    + (q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 * hsq

/-- `rad(r) q = q rad(φ r)`: conjugating a radical element of the line group by `q`. -/
theorem rad_mul_q (N : ℕ) {q : SL(3, ℤ)} (hq : q ∈ lineBorel) (r : RadicalLattice) :
    radEltQ N r * q = q * radEltQ N (phiQHom q r) := by
  obtain ⟨h1, h2⟩ := hq
  have hsq := lineBorel_a_sq (q := q) ⟨h1, h2⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, radEltQ, phiQHom_toAdd, botRight, h1, h2] <;>
    first
    | linear_combination (-(N * r.toAdd.1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 1 1 +
        N * r.toAdd.2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1)) * hsq
    | linear_combination (-(N * r.toAdd.1 * (q : Matrix (Fin 3) (Fin 3) ℤ) 1 2 +
        N * r.toAdd.2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2)) * hsq

end Phi

end TernaryPeriodPolynomials.Argument.FrameInvariance
