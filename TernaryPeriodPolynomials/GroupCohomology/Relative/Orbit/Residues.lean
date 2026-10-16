module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Completion
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Covectors
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Conjugacy

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeOrbitResidues
open ModThreeGoodAction RelativeOrbitCompletion RelativeStabilizerCoordinates
open RelativeStabilizerConjugacy

abbrev Row := Fin 3 → ZMod 3

def row (g : IntegralGL) : Row := Matrix.vecMul (![0,0,1] : Row) (reduction g).val

theorem row_apply (g : IntegralGL) (j : Fin 3) : row g j = (g.val 2 j : ZMod 3) := by
  simp [row,Matrix.vecMul,dotProduct,Fin.sum_univ_three,reduction,Matrix.GeneralLinearGroup.map_apply]

theorem row_mul (g h : IntegralGL) : row (g*h) = Matrix.vecMul (row g) (reduction h).val := by
  simp only [row,map_mul,Units.val_mul,Matrix.vecMul_vecMul]

theorem row_ne_zero (g : IntegralGL) : row g ≠ 0 := by
  have he : OrdinaryCovectors.row (B*g) = row g := by
    rw [OrdinaryCovectors.row_mul,show OrdinaryCovectors.row B = ![0,0,1] from fixedRow_B]
    rfl
  rw [← he]
  exact OrdinaryCovectors.row_ne_zero _

/-- Goodness of an integral coordinate subspace is detected exactly by its literal column residues. -/
theorem good3_coordinate_iff (g : IntegralGL) (s : Finset (Fin 3)) :
    Good3 (mapSpace g (coordinateSubspace s)) ↔ ∃ j ∈ s, row g j ≠ 0 := by
  classical
  constructor
  · rintro ⟨v,hv,hn⟩
    by_contra h
    have hz : ∀ j ∈ s, row g j = 0 := by simpa only [not_exists,not_and,not_not] using h
    let w : IntegralVector := (g⁻¹).val.mulVec v
    have hw : rationalVector w ∈ coordinateSubspace s := by
      obtain ⟨x,hx,he⟩ := hv
      have hi : rationalVector w = x := by
        rw [show rationalVector w = rationalRepresentation g⁻¹ (rationalVector v) from rationalVector_mulVec _ _,
          ← he]
        exact BadVertexProjection.representation_inverse g x
      rw [hi]
      exact hx
    have hrec : g.val.mulVec w = v := by
      rw [show w = (g⁻¹).val.mulVec v from rfl,Matrix.mulVec_mulVec,← Units.val_mul,
        mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
    apply hn
    have hv2 : (v 2 : ZMod 3) = ∑ j : Fin 3, (g.val 2 j : ZMod 3) * (w j : ZMod 3) := by
      have he := congrFun hrec 2
      change (∑ j : Fin 3, g.val 2 j * w j) = v 2 at he
      have hc := congrArg (fun z : ℤ => (z : ZMod 3)) he.symm
      simpa only [Int.cast_sum,Int.cast_mul] using hc
    rw [hv2]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · rw [← row_apply,hz j hj,zero_mul]
    · have he : w j = 0 := by
        have hwj : (w j : ℚ) = 0 := hw j hj
        exact_mod_cast hwj
      simp only [he,Int.cast_zero,mul_zero]
  · rintro ⟨j,hj,hn⟩
    refine ⟨g.val.mulVec (Pi.single j 1),?_,?_⟩
    · rw [rationalVector_mulVec]
      apply Submodule.mem_map_of_mem
      intro i hi
      have hij : i ≠ j := fun he => hi (he ▸ hj)
      simp [rationalVector,hij]
    · simpa only [Matrix.mulVec_single_one,Matrix.col_apply,← row_apply] using hn

theorem good3_L0_iff (g : IntegralGL) : Good3 (mapSpace g L0) ↔ row g 0 = 1 ∨ row g 0 = 2 := by
  rw [L0,good3_coordinate_iff]
  have h : ∀ a : ZMod 3, a ≠ 0 ↔ a = 1 ∨ a = 2 := by decide +kernel
  simp only [Finset.mem_singleton,exists_eq_left,h]

theorem bad3_L0_iff (g : IntegralGL) : ¬Good3 (mapSpace g L0) ↔ row g 0 = 0 := by
  rw [L0,good3_coordinate_iff]
  simp

theorem bad3_P0_iff (g : IntegralGL) : ¬Good3 (mapSpace g P0) ↔ row g 0 = 0 ∧ row g 1 = 0 := by
  rw [P0,good3_coordinate_iff]
  simp

theorem good3_P1_iff (g : IntegralGL) : Good3 (mapSpace g P1) ↔ row g 0 ≠ 0 ∨ row g 2 ≠ 0 := by
  rw [P1,good3_coordinate_iff]
  simp

end TernaryPoly.RelativeOrbitResidues
