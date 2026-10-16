module

public import TernaryPeriodPolynomials.Building.Primitive.BasisExtension
public import Mathlib.Data.Fintype.Card

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryCovectors
open ModThreeGoodAction GoodIntegralNormalization PrimitiveBasisExtension

abbrev Covector := Fin 3 → ZMod 3
abbrev NonzeroCovector := {r : Covector // r≠0}

/-- The exact residue covector of an integral frame. -/
def row (g : IntegralGL) : Covector := Matrix.vecMul fixedRow (reduction g).val

theorem row_mul (g h : IntegralGL) : row (g*h)=Matrix.vecMul (row g) (reduction h).val := by
  simp only [row,map_mul,Units.val_mul,Matrix.vecMul_vecMul]

theorem row_one : row 1=fixedRow := by simp [row]

theorem row_ne_zero (g : IntegralGL) : row g≠0 := by
  intro h
  have he := row_mul g g⁻¹
  rw [mul_inv_cancel,row_one,h,Matrix.zero_vecMul] at he
  have := congrFun he 0
  norm_num [fixedRow] at this

/-- Left multiplication by the actual congruence subgroup fixes precisely this covector. -/
theorem row_left_K (k : K) (g : IntegralGL) : row (k.val*g)=row g := by
  rw [row_mul,show row k.val=fixedRow from k.property]
  rfl

/-- Equality of covectors is exactly membership in the same left-K orbit. -/
theorem row_eq_iff (g h : IntegralGL) : row g=row h ↔ ∃ k : K,k.val*g=h := by
  constructor
  · intro he
    have hk : h*g⁻¹∈K := by
      change row (h*g⁻¹)=fixedRow
      rw [row_mul,← he,← row_mul,mul_inv_cancel,row_one]
    refine ⟨⟨h*g⁻¹,hk⟩,?_⟩
    simp [mul_assoc]
  · rintro ⟨k,rfl⟩
    exact (row_left_K k g).symm

/-- Lift residues by the balanced integers 0,1,-1. -/
def balanced (x : ZMod 3) : ℤ := if x=0 then 0 else if x=1 then 1 else -1

theorem balanced_cast (x : ZMod 3) : (balanced x : ZMod 3)=x := by
  fin_cases x <;> rfl

theorem balanced_isUnit {x : ZMod 3} (hx : x≠0) : IsUnit (balanced x) := by
  simp only [balanced,ite_eq_right hx]
  split <;> simp

/-- Every nonzero balanced covector is a primitive integral row. -/
theorem balanced_primitive (r : NonzeroCovector) : Primitive (fun i => balanced (r.val i)) := by
  obtain ⟨i,hi⟩ : ∃ i,r.val i≠0 := by
    by_contra h
    apply r.property
    funext i
    simpa using not_exists.mp h i
  have hd := content_dvd (fun i => balanced (r.val i)) i
  have hu := balanced_isUnit hi
  have hc : IsUnit ((content (fun i => balanced (r.val i)) : ℕ) : ℤ) :=
    isUnit_of_dvd_unit hd hu
  exact Int.isUnit_iff_natAbs_eq.mp hc

/-- A fixed integral basis change sends the row to the first coordinate. -/
def firstRowFrame : IntegralGL :=
  ⟨!![1,-1,-1;0,1,0;0,0,1],!![1,1,1;0,1,0;0,0,1],by decide +kernel,by decide +kernel⟩

theorem row_firstRowFrame : row firstRowFrame=![1,0,0] := by decide +kernel

/-- Every one of the26 nonzero covectors has an actual integral frame representative. -/
theorem row_surjective (r : NonzeroCovector) : ∃ g : IntegralGL,row g=r.val := by
  let v : IntegralVector := fun i => balanced (r.val i)
  obtain ⟨M,hcol,hdet⟩ := exists_matrix_first_column_det_one v (balanced_primitive r)
  let t : IntegralGL := Matrix.nonsingInvUnit M.transpose (by rw [Matrix.det_transpose,hdet]; exact isUnit_one)
  refine ⟨firstRowFrame*t,?_⟩
  rw [row_mul,row_firstRowFrame]
  funext i
  change (Matrix.vecMul (![1,0,0] : Covector) (reduction t).val) i=r.val i
  have hmi : M i 0=v i := congrFun hcol i
  have hti : t.val 0 i=v i := hmi
  simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_three,reduction,
    Matrix.GeneralLinearGroup.map_apply,hti,v] using balanced_cast (r.val i)

/-- The frame-to-covector map lands in the literal finite26-element set. -/
def nonzeroRow (g : IntegralGL) : NonzeroCovector := ⟨row g,row_ne_zero g⟩

theorem nonzeroRow_surjective : Function.Surjective nonzeroRow := by
  intro r
  obtain ⟨g,hg⟩ := row_surjective r
  exact ⟨g,Subtype.ext hg⟩

theorem card_nonzeroCovector : Fintype.card NonzeroCovector=26 := by
  decide +kernel

end TernaryPoly.OrdinaryCovectors
