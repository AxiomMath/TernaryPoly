module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeStabilizerConjugacy
open ModThreeGoodAction RelativeStabilizerCoordinates

/-- The integral basis change sending the original covector to the last coordinate. -/
def B : IntegralGL :=
  ⟨![![1,0,0],![0,1,0],![-1,-1,1]],
   ![![1,0,0],![0,1,0],![1,1,1]],by decide +kernel,by decide +kernel⟩

theorem fixedRow_B : Matrix.vecMul fixedRow (reduction B).val = ![0,0,1] := by
  decide +kernel

theorem lastRow_Binv : Matrix.vecMul (![0,0,1] : Fin 3 → ZMod 3) (reduction B⁻¹).val = fixedRow := by
  decide +kernel

theorem conjugate_mem_K_iff (g : IntegralGL) : B*g*B⁻¹ ∈ K ↔ g ∈ K3 := by
  change Matrix.vecMul fixedRow (reduction (B*g*B⁻¹)).val = fixedRow ↔
    Matrix.vecMul (![0,0,1] : Fin 3 → ZMod 3) (reduction g).val = ![0,0,1]
  simp only [map_mul,Units.val_mul,← Matrix.vecMul_vecMul,fixedRow_B]
  constructor
  · intro h
    have he := congrArg (fun row => Matrix.vecMul row (reduction B).val) h
    rw [Matrix.vecMul_vecMul] at he
    have hi : (reduction B⁻¹).val * (reduction B).val = 1 := by
      rw [← Units.val_mul,← map_mul,inv_mul_cancel,map_one,Units.val_one]
    simpa only [hi,Matrix.vecMul_one,fixedRow_B] using he
  · intro h
    rw [h,lastRow_Binv]

/-- The subgroup equivalence uses literal matrix conjugation. -/
def K3EquivK : K3 ≃* K where
  toFun g := ⟨B*g.val*B⁻¹,(conjugate_mem_K_iff g.val).mpr g.property⟩
  invFun g := ⟨B⁻¹*g.val*B,by
    apply (conjugate_mem_K_iff _).mp
    simp [mul_assoc]⟩
  left_inv g := by apply Subtype.ext; simp [mul_assoc]
  right_inv g := by apply Subtype.ext; simp [mul_assoc]
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem K3EquivK_val (g : K3) : (K3EquivK g).val = B*g.val*B⁻¹ := rfl

def changeSpace (L : RationalSubspace) : RationalSubspace :=
  L.map (rationalRepresentation B).toLinearMap

def act3 (g : K3) (L : RationalSubspace) : RationalSubspace :=
  L.map (rationalRepresentation g.val).toLinearMap

/-- The old and new actions are intertwined by the actual rational basis change. -/
theorem changeSpace_act3 (g : K3) (L : RationalSubspace) :
    changeSpace (act3 g L) = act (K3EquivK g) (changeSpace L) := by
  simp only [changeSpace,act3,act,K3EquivK_val,← Submodule.map_comp]
  congr 1
  rw [← Module.End.mul_eq_comp,← LinearEquiv.coe_toLinearMap_mul,← map_mul,← Module.End.mul_eq_comp,← LinearEquiv.coe_toLinearMap_mul,← map_mul]
  simp [mul_assoc]

theorem sum_B_mulVec (v : IntegralVector) :
    (∑ i : Fin 3, ((B.val.mulVec v) i : ZMod 3)) = (v 2 : ZMod 3) := by
  simp [B,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

theorem last_Binv_mulVec (v : IntegralVector) :
    ((B⁻¹).val.mulVec v 2 : ZMod 3) = ∑ i : Fin 3, (v i : ZMod 3) := by
  change ((Matrix.mulVec (![![1,0,0],![0,1,0],![1,1,1]] : Matrix (Fin 3) (Fin 3) ℤ) v) 2 : ZMod 3) = _
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,add_assoc]

/-- Goodness transports with its genuine integral-lattice witness. -/
theorem good_changeSpace_iff (L : RationalSubspace) : Good (changeSpace L) ↔ Good3 L := by
  constructor
  · rintro ⟨v,hv,hn⟩
    refine ⟨(B⁻¹).val.mulVec v,?_,?_⟩
    · rw [rationalVector_mulVec]
      obtain ⟨w,hw,he⟩ := hv
      have hi : rationalRepresentation B⁻¹ (rationalVector v) = w := by
        rw [← he]
        change (rationalRepresentation B⁻¹ * rationalRepresentation B) w = w
        rw [← map_mul,inv_mul_cancel,map_one]
        rfl
      rw [hi]
      exact hw
    · rwa [last_Binv_mulVec]
  · rintro ⟨v,hv,hn⟩
    refine ⟨B.val.mulVec v,?_,?_⟩
    · rw [rationalVector_mulVec]
      exact Submodule.mem_map_of_mem hv
    · rwa [sum_B_mulVec]

/-- In the new coordinates the action preserves goodness exactly. -/
theorem good3_act3_iff (g : K3) (L : RationalSubspace) : Good3 L ↔ Good3 (act3 g L) := by
  rw [← good_changeSpace_iff,← good_changeSpace_iff,changeSpace_act3,good_act_iff]

end TernaryPoly.RelativeStabilizerConjugacy
