module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Conjugates of the rational upper unitriangular group

For `q ∈ GL₃(ℚ)` let `conjUnitri q = q U(ℚ) q⁻¹`, where `U` is the upper unitriangular
group (the Heisenberg group). For `g, h` in this group, the defect
`g⁻¹ (h g h⁻¹)` of conjugation by `h` is central in `conjUnitri q`: after conjugating by
`q` it is a commutator of unitriangular matrices, whose two super-diagonal entries vanish
because they are additive.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- Upper unitriangular rational matrices. -/
def IsUnitri (v : RationalGL3) : Prop :=
  v.val 0 0 = 1 ∧ v.val 1 1 = 1 ∧ v.val 2 2 = 1 ∧ v.val 1 0 = 0 ∧ v.val 2 0 = 0 ∧ v.val 2 1 = 0

/-- Unitriangular matrices whose two super-diagonal entries vanish (the centre). -/
def IsCentralUnitri (z : RationalGL3) : Prop :=
  IsUnitri z ∧ z.val 0 1 = 0 ∧ z.val 1 2 = 0

theorem unitri_one : IsUnitri 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem unitri_mul {v w : RationalGL3} (hv : IsUnitri v) (hw : IsUnitri w) :
    IsUnitri (v * w) ∧ (v * w).val 0 1 = v.val 0 1 + w.val 0 1 ∧
      (v * w).val 1 2 = v.val 1 2 + w.val 1 2 := by
  obtain ⟨v00, v11, v22, v10, v20, v21⟩ := hv
  obtain ⟨w00, w11, w22, w10, w20, w21⟩ := hw
  simp only [IsUnitri, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    v00, v11, v22, v10, v20, v21, w00, w11, w22, w10, w20, w21]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> ring

theorem unitri_inv {v : RationalGL3} (hv : IsUnitri v) :
    IsUnitri v⁻¹ ∧ (v⁻¹).val 0 1 = -v.val 0 1 ∧ (v⁻¹).val 1 2 = -v.val 1 2 := by
  obtain ⟨v00, v11, v22, v10, v20, v21⟩ := hv
  set w := v⁻¹ with hwdef
  have h : w.val * v.val = 1 := by
    rw [hwdef, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have e : ∀ i j, w.val i 0 * v.val 0 j + w.val i 1 * v.val 1 j + w.val i 2 * v.val 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) i j := fun i j => by
    rw [← h, Matrix.mul_apply, Fin.sum_univ_three]
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e00 := e 0 0
  have e01 := e 0 1
  simp only [v00, v11, v22, v10, v20, v21, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.reduceEq, not_false_eq_true, mul_one, mul_zero, add_zero] at e20 e21 e22 e10 e11 e12 e00 e01
  rw [e20, zero_mul, zero_add] at e21
  rw [e20, e21, zero_mul, zero_mul, zero_add, zero_add] at e22
  rw [e10, zero_mul, zero_add] at e11
  rw [e10, e11, zero_mul, zero_add, one_mul] at e12
  rw [e00, one_mul] at e01
  refine ⟨⟨e00, e11, e22, e10, e20, e21⟩, ?_, ?_⟩
  · linarith
  · linarith

/-- The conjugate `q U(ℚ) q⁻¹` of the upper unitriangular group. -/
def conjUnitri (q : RationalGL3) : Subgroup RationalGL3 where
  carrier := {g | IsUnitri (q⁻¹ * g * q)}
  one_mem' := by
    change IsUnitri (q⁻¹ * 1 * q)
    rw [mul_one, inv_mul_cancel]
    exact unitri_one
  mul_mem' {g h} hg hh := by
    change IsUnitri (q⁻¹ * (g * h) * q)
    have : q⁻¹ * (g * h) * q = (q⁻¹ * g * q) * (q⁻¹ * h * q) := by group
    rw [this]
    exact (unitri_mul hg hh).1
  inv_mem' {g} hg := by
    change IsUnitri (q⁻¹ * g⁻¹ * q)
    have : q⁻¹ * g⁻¹ * q = (q⁻¹ * g * q)⁻¹ := by group
    rw [this]
    exact (unitri_inv hg).1

theorem mem_conjUnitri {q g : RationalGL3} : g ∈ conjUnitri q ↔ IsUnitri (q⁻¹ * g * q) := Iff.rfl

theorem central_comm {z v : RationalGL3} (hz : IsCentralUnitri z) (hv : IsUnitri v) :
    z * v = v * z := by
  obtain ⟨⟨z00, z11, z22, z10, z20, z21⟩, z01, z12⟩ := hz
  obtain ⟨v00, v11, v22, v10, v20, v21⟩ := hv
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (z.val * v.val) i j = (v.val * z.val) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, z00, z11, z22, z10, z20, z21, z01, z12,
      v00, v11, v22, v10, v20, v21]
  ring

theorem commutator_central {v u : RationalGL3} (hv : IsUnitri v) (hu : IsUnitri u) :
    IsCentralUnitri (v⁻¹ * u * v * u⁻¹) := by
  obtain ⟨hvi, hvi01, hvi12⟩ := unitri_inv hv
  obtain ⟨hui, hui01, hui12⟩ := unitri_inv hu
  obtain ⟨h1, h1a, h1b⟩ := unitri_mul hvi hu
  obtain ⟨h2, h2a, h2b⟩ := unitri_mul h1 hv
  obtain ⟨h3, h3a, h3b⟩ := unitri_mul h2 hui
  refine ⟨h3, ?_, ?_⟩
  · rw [h3a, h2a, h1a, hvi01, hui01]; ring
  · rw [h3b, h2b, h1b, hvi12, hui12]; ring

/-- The defect of conjugation by `h` commutes with every element of `conjUnitri q`. -/
theorem conj_defect_comm {q g h x : RationalGL3} (hg : g ∈ conjUnitri q) (hh : h ∈ conjUnitri q)
    (hx : x ∈ conjUnitri q) : g⁻¹ * (h * g * h⁻¹) * x = x * (g⁻¹ * (h * g * h⁻¹)) := by
  have hz := commutator_central hg hh
  have hc := central_comm hz hx
  have e1 : (q⁻¹ * g * q)⁻¹ * (q⁻¹ * h * q) * (q⁻¹ * g * q) * (q⁻¹ * h * q)⁻¹ =
      q⁻¹ * (g⁻¹ * (h * g * h⁻¹)) * q := by group
  rw [e1] at hc
  have e2 : q⁻¹ * (g⁻¹ * (h * g * h⁻¹)) * q * (q⁻¹ * x * q) =
      q⁻¹ * (g⁻¹ * (h * g * h⁻¹) * x) * q := by group
  have e3 : q⁻¹ * x * q * (q⁻¹ * (g⁻¹ * (h * g * h⁻¹)) * q) =
      q⁻¹ * (x * (g⁻¹ * (h * g * h⁻¹))) * q := by group
  rw [e2, e3] at hc
  have := congrArg (fun y => q * y * q⁻¹) hc
  simpa [mul_assoc] using this

end TernaryPeriodPolynomials.FlagExactness
