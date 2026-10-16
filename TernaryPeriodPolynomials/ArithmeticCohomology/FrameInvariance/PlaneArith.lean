module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CanonicalTwist
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Conjugation

@[expose] public section


/-!
# The frame change of a plane face as a twisted isomorphism of extensions (arithmetic part)

Formalized by Claude Sonnet 5.5.

For `q ∈ P(ℚ) ∩ SL₃(ℤ)` with third row `(0, 0, d)` (`d = ±1`) and upper left block `A = topLeft q`: `planeBorel_d_sq` (`d² = 1`, `d · det A = 1`), `phiPQ`: the radical map `w ↦ d · A⁻¹ w` (`rad(w) q = q rad(φ w)`, `rad_mul_qP`)
and its determinant `radDet (phiPQ q) = d`.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

section Arith

variable {q : SL(3, ℤ)}

theorem planeBorel_det (hq : q ∈ planeBorel) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (topLeft q 0 0 * topLeft q 1 1 - topLeft q 0 1 * topLeft q 1 0) = 1 := by
  obtain ⟨h1, h2⟩ := hq
  have hdet : (q : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := q.2
  rw [Matrix.det_fin_three, h1, h2] at hdet
  simp only [topLeft, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination hdet

theorem planeBorel_d_sq (hq : q ∈ planeBorel) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := by
  have h := planeBorel_det hq
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ h) with h0 | h0 <;> rw [h0] <;> norm_num

theorem planeBorel_detA (hq : q ∈ planeBorel) :
    topLeft q 0 0 * topLeft q 1 1 - topLeft q 0 1 * topLeft q 1 0 = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
  have h := planeBorel_det hq
  have h2 := planeBorel_d_sq hq
  linear_combination (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * h - (topLeft q 0 0 * topLeft q 1 1 - topLeft q 0 1 * topLeft q 1 0) * h2

end Arith

section Phi

/-- The radical map `w ↦ d · A⁻¹ w` of the frame change by `q` (`d` the `(2,2)` entry, `A⁻¹ = topLeft q⁻¹`). -/
def phiPQHom (q : SL(3, ℤ)) : RadicalLattice →* RadicalLattice where
  toFun r := Multiplicative.ofAdd ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (topLeft q⁻¹ 0 0 * r.toAdd.1 + topLeft q⁻¹ 0 1 * r.toAdd.2),
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (topLeft q⁻¹ 1 0 * r.toAdd.1 + topLeft q⁻¹ 1 1 * r.toAdd.2))
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.mk_add_mk, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
    constructor <;> ring

theorem phiPQHom_toAdd (q : SL(3, ℤ)) (r : RadicalLattice) :
    (phiPQHom q r).toAdd = ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (topLeft q⁻¹ 0 0 * r.toAdd.1 + topLeft q⁻¹ 0 1 * r.toAdd.2),
      (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (topLeft q⁻¹ 1 0 * r.toAdd.1 + topLeft q⁻¹ 1 1 * r.toAdd.2)) := rfl

theorem inv_d {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
  obtain ⟨k1, k2⟩ := planeBorel.inv_mem hq
  have hm : ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have e := congrFun (congrFun hm 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, k1, k2, zero_mul, zero_add, Matrix.one_apply_eq] at e
  have hsq := planeBorel_d_sq hq
  linear_combination ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) * e - ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * hsq

theorem phiPQHom_inv {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (r : RadicalLattice) : phiPQHom q⁻¹ (phiPQHom q r) = r := by
  apply Multiplicative.toAdd.injective
  have hA := (topLeft_inv_mul q hq).1
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e01 e10 e11
  simp only [Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero] at e01 e10
  have hsq := planeBorel_d_sq hq
  rw [phiPQHom_toAdd, phiPQHom_toAdd, inv_inv, inv_d hq]
  apply Prod.ext
  · simp only
    linear_combination (r.toAdd.1 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2)) * e00
      + (r.toAdd.2 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2)) * e01
      + r.toAdd.1 * hsq
  · simp only
    linear_combination (r.toAdd.1 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2)) * e10
      + (r.toAdd.2 * ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2)) * e11
      + r.toAdd.2 * hsq

/-- The radical map `φ_q` as an automorphism of the radical lattice. -/
def phiPQ {q : SL(3, ℤ)} (hq : q ∈ planeBorel) : RadicalLattice ≃* RadicalLattice :=
  { phiPQHom q with
    invFun := phiPQHom q⁻¹
    left_inv := fun r => phiPQHom_inv hq r
    right_inv := fun r => by
      have := phiPQHom_inv (planeBorel.inv_mem hq) r
      rwa [inv_inv] at this }

theorem phiPQ_apply {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (r : RadicalLattice) : phiPQ hq r = phiPQHom q r := rfl

/-- **The determinant of the radical map is `d`.** -/
theorem radDet_phiPQ {q : SL(3, ℤ)} (hq : q ∈ planeBorel) :
    radDet (phiPQ hq).toMonoidHom = (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 := by
  have h := planeBorel_detA (planeBorel.inv_mem hq)
  rw [inv_d hq] at h
  have hsq := planeBorel_d_sq hq
  simp only [radDet, MulEquiv.coe_toMonoidHom, phiPQ_apply, phiPQHom_toAdd, rl1, rl2, radicalLatticeFirst,
    radicalLatticeSecond, toAdd_ofAdd]
  simp only [add_zero, zero_add, mul_zero, mul_one]
  linear_combination ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) * h
    + (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * hsq

/-- `rad(r) q = q rad(φ r)`: conjugating a radical element of the plane group by `q`. -/
theorem rad_mul_qP (N : ℕ) {q : SL(3, ℤ)} (hq : q ∈ planeBorel) (r : RadicalLattice) :
    radElt N r * q = q * radElt N (phiPQHom q r) := by
  obtain ⟨h1, h2⟩ := hq
  have hq := (⟨h1, h2⟩ : q ∈ planeBorel)
  have hsq := planeBorel_d_sq hq
  have hA := (topLeft_inv_mul q hq).1
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e01 e10 e11
  simp only [Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero] at e01 e10
  simp only [topLeft, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.SpecialLinearGroup.coe_inv] at e00 e01 e10 e11
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, radElt, phiPQHom_toAdd, topLeft, h1, h2] <;>
    first
    | linear_combination (-(N * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * r.toAdd.1)) * e00 +
        (-(N * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * r.toAdd.2)) * e01
    | linear_combination (-(N * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * r.toAdd.1)) * e10 +
        (-(N * (q : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * r.toAdd.2)) * e11

end Phi

end TernaryPeriodPolynomials.Argument.FrameInvariance
