module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeStabilizerCoordinates
open ModThreeGoodAction
open scoped BigOperators

/-- The standard-coordinate subspace supported on `s`. -/
def coordinateSubspace (s : Finset (Fin 3)) : RationalSubspace where
  carrier := {v | ∀ i, i ∉ s → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i hi; simp [hv i hi, hw i hi]
  smul_mem' := by intro q v hv i hi; simp [hv i hi]

/-- The actual coordinate line Q e₀. -/
def L0 : RationalSubspace := coordinateSubspace {0}
/-- The actual coordinate plane Q e₀ + Q e₁. -/
def P0 : RationalSubspace := coordinateSubspace {0,1}
/-- The actual coordinate plane Q e₀ + Q e₂. -/
def P1 : RationalSubspace := coordinateSubspace {0,2}

@[simp] theorem mem_L0 (v : Space) : v ∈ L0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  change (∀ i : Fin 3, i ∉ ({0} : Finset (Fin 3)) → v i = 0) ↔ _
  constructor
  · intro h; exact ⟨h 1 (by decide),h 2 (by decide)⟩
  · rintro ⟨h1,h2⟩ i hi; fin_cases i <;> simp_all

@[simp] theorem mem_P0 (v : Space) : v ∈ P0 ↔ v 2 = 0 := by
  change (∀ i : Fin 3, i ∉ ({0,1} : Finset (Fin 3)) → v i = 0) ↔ _
  constructor
  · intro h; exact h 2 (by decide)
  · intro h i hi; fin_cases i <;> simp_all

@[simp] theorem mem_P1 (v : Space) : v ∈ P1 ↔ v 1 = 0 := by
  change (∀ i : Fin 3, i ∉ ({0,2} : Finset (Fin 3)) → v i = 0) ↔ _
  constructor
  · intro h; exact h 1 (by decide)
  · intro h i hi; fin_cases i <;> simp_all

/-- Stabilization under the genuine rational representation. -/
def Stabilizes (g : IntegralGL) (L : RationalSubspace) : Prop :=
  L.map (rationalRepresentation g).toLinearMap = L

theorem stabilizes_iff_map_le (g : IntegralGL) (L : RationalSubspace) :
    Stabilizes g L ↔ L.map (rationalRepresentation g).toLinearMap ≤ L := by
  constructor
  · intro h; exact le_of_eq h
  · intro h
    exact Submodule.eq_of_le_of_finrank_eq h
      ((rationalRepresentation g).submoduleMap L).finrank_eq.symm

theorem stabilizes_coordinate_iff (g : IntegralGL) (s : Finset (Fin 3)) :
    Stabilizes g (coordinateSubspace s) ↔
      ∀ i, i ∉ s → ∀ j ∈ s, g.val i j = 0 := by
  rw [stabilizes_iff_map_le]
  constructor
  · intro h i hi j hj
    have hv : (Pi.single j (1 : ℚ) : Space) ∈ coordinateSubspace s := by
      intro k hk
      have hkj : k ≠ j := by intro he; subst k; exact hk hj
      simp [hkj]
    have hm := h (Submodule.mem_map_of_mem (f := (rationalRepresentation g).toLinearMap) hv)
    have he := hm i hi
    change rationalRepresentation g (Pi.single j 1) i = 0 at he
    rw [rationalRepresentation_apply] at he
    have he' : (g.val i j : ℚ) = 0 := by
      simpa [Matrix.mulVec_single_one,Matrix.GeneralLinearGroup.map_apply] using he
    exact_mod_cast he'
  · intro h v hv
    obtain ⟨w,hw,rfl⟩ := hv
    intro i hi
    rw [LinearEquiv.coe_coe,rationalRepresentation_apply]
    change (∑ j : Fin 3, (g.val i j : ℚ) * w j) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · simp [h i hi j hj]
    · simp [hw j hj]

theorem stabilizes_L0_iff (g : IntegralGL) :
    Stabilizes g L0 ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [L0,stabilizes_coordinate_iff]
  simp only [Finset.mem_singleton]
  constructor
  · intro h; exact ⟨h 1 (by decide) 0 rfl,h 2 (by decide) 0 rfl⟩
  · rintro ⟨h1,h2⟩ i hi j rfl
    fin_cases i <;> simp_all

theorem stabilizes_P0_iff (g : IntegralGL) :
    Stabilizes g P0 ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [P0,stabilizes_coordinate_iff]
  constructor
  · intro h; exact ⟨h 2 (by decide) 0 (by decide),h 2 (by decide) 1 (by decide)⟩
  · rintro ⟨h0,h1⟩ i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all

theorem stabilizes_P1_iff (g : IntegralGL) :
    Stabilizes g P1 ↔ g.val 1 0 = 0 ∧ g.val 1 2 = 0 := by
  rw [P1,stabilizes_coordinate_iff]
  constructor
  · intro h; exact ⟨h 1 (by decide) 0 (by decide),h 1 (by decide) 2 (by decide)⟩
  · rintro ⟨h0,h2⟩ i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all

/-- The exact fixer of the last coordinate covector modulo three. -/
def K3 : Subgroup IntegralGL where
  carrier := {g | Matrix.vecMul (![0,0,1] : Fin 3 → ZMod 3) (reduction g).val = ![0,0,1]}
  one_mem' := by simp
  mul_mem' hg hh := by
    change Matrix.vecMul _ (reduction (_*_)).val = _
    rw [map_mul,Units.val_mul,← Matrix.vecMul_vecMul,hg,hh]
  inv_mem' := by
    intro g hg
    have h := congrArg (fun row => Matrix.vecMul row (reduction g⁻¹).val) hg
    rw [Matrix.vecMul_vecMul] at h
    have he : (reduction g).val * (reduction g⁻¹).val = 1 := by
      rw [← Units.val_mul,← map_mul,mul_inv_cancel,map_one,Units.val_one]
    rw [he,Matrix.vecMul_one] at h
    exact h.symm

theorem mem_K3_iff (g : IntegralGL) : g ∈ K3 ↔
    (g.val 2 0 : ZMod 3) = 0 ∧ (g.val 2 1 : ZMod 3) = 0 ∧
      (g.val 2 2 : ZMod 3) = 1 := by
  change Matrix.vecMul (![0,0,1] : Fin 3 → ZMod 3) (reduction g).val = _ ↔ _
  simp only [funext_iff,Fin.forall_fin_succ,Fin.forall_fin_zero]
  simp [Matrix.vecMul,dotProduct,Fin.sum_univ_three,reduction,Matrix.GeneralLinearGroup.map_apply]

/-- Goodness in the conjugated coordinates uses the integral lattice and last residue. -/
def Good3 (L : RationalSubspace) : Prop :=
  ∃ v : IntegralVector, rationalVector v ∈ L ∧ (v 2 : ZMod 3) ≠ 0

theorem not_good3_L0 : ¬ Good3 L0 := by
  rintro ⟨v,hv,hn⟩
  have he : (v 2 : ℚ) = 0 := ((mem_L0 (rationalVector v)).mp hv).2
  have hz : v 2 = 0 := by exact_mod_cast he
  exact hn (by simp [hz])

theorem not_good3_P0 : ¬ Good3 P0 := by
  rintro ⟨v,hv,hn⟩
  have he : (v 2 : ℚ) = 0 := (mem_P0 (rationalVector v)).mp hv
  have hz : v 2 = 0 := by exact_mod_cast he
  exact hn (by simp [hz])

theorem good3_P1 : Good3 P1 := by
  refine ⟨![0,0,1],?_,?_⟩
  · simp [rationalVector]
  · change (1 : ZMod 3) ≠ 0
    exact one_ne_zero

theorem L0_le_P0 : L0 ≤ P0 := by intro v hv; exact (mem_P0 v).mpr ((mem_L0 v).mp hv).2

theorem L0_le_P1 : L0 ≤ P1 := by intro v hv; exact (mem_P1 v).mpr ((mem_L0 v).mp hv).1

/-- The coordinate line has its literal one-dimensional parametrization. -/
def L0Equiv : L0 ≃ₗ[ℚ] ℚ where
  toFun v := v.val 0
  invFun q := ⟨![q,0,0],by simp⟩
  left_inv v := by
    apply Subtype.ext
    obtain ⟨h1,h2⟩ := (mem_L0 v.val).mp v.property
    ext i; fin_cases i <;> simp [h1,h2]
  right_inv q := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The bad coordinate plane has its literal two-coordinate parametrization. -/
def P0Equiv : P0 ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun v := ![v.val 0,v.val 1]
  invFun q := ⟨![q 0,q 1,0],by simp⟩
  left_inv v := by
    apply Subtype.ext
    have h2 := (mem_P0 v.val).mp v.property
    ext i; fin_cases i <;> simp [h2]
  right_inv q := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

/-- The good coordinate plane has its literal two-coordinate parametrization. -/
def P1Equiv : P1 ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun v := ![v.val 0,v.val 2]
  invFun q := ⟨![q 0,0,q 1],by simp⟩
  left_inv v := by
    apply Subtype.ext
    have h1 := (mem_P1 v.val).mp v.property
    ext i; fin_cases i <;> simp [h1]
  right_inv q := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

theorem finrank_L0 : Module.finrank ℚ L0 = 1 := by
  rw [L0Equiv.finrank_eq]; simp

theorem finrank_P0 : Module.finrank ℚ P0 = 2 := by
  rw [P0Equiv.finrank_eq]; simp

theorem finrank_P1 : Module.finrank ℚ P1 = 2 := by
  rw [P1Equiv.finrank_eq]; simp

end TernaryPoly.RelativeStabilizerCoordinates
