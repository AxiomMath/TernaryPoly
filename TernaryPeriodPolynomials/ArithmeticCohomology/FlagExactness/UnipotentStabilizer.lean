module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.GroupCohomology

@[expose] public section


/-!
# The unipotent part of a complete-flag stabilizer

The elements `γ` of the arithmetic flag stabilizer `edgeStabilizer q` such that
`q⁻¹ γ q` has unit diagonal form a subgroup. It has finite index, because the diagonal
is multiplicative on the Borel subgroup and takes values in `{±1}³`. Together with
`exists_primitive_of_finiteIndex`, this reduces stabilizer exactness to a Heisenberg
lattice.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem borel_diag_mul {β β' : RationalGL3} (hβ : β ∈ parabolic .plane ⊓ parabolic .line)
    (hβ' : β' ∈ parabolic .plane ⊓ parabolic .line) (i : Fin 3) :
    (β * β').val i i = β.val i i * β'.val i i := by
  obtain ⟨h10, h20, h21⟩ := borel_entries hβ
  obtain ⟨h10', h20', h21'⟩ := borel_entries hβ'
  rw [Matrix.GeneralLinearGroup.coe_mul]
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h10', h20', h21']

theorem conj_mul (q γ δ : RationalGL3) : q⁻¹ * (γ * δ) * q = (q⁻¹ * γ * q) * (q⁻¹ * δ * q) := by
  group

theorem edgeStabilizer_borel (q : RationalGL3) {γ : RationalGL3} (hγ : γ ∈ edgeStabilizer q) :
    q⁻¹ * γ * q ∈ parabolic .plane ⊓ parabolic .line :=
  stabilizer_mem_borel q γ (MulAction.mem_stabilizer_iff.mp hγ.2)

/-- The unipotent part of the arithmetic complete-flag stabilizer. -/
def unipotentStabilizer (q : RationalGL3) : Subgroup RationalGL3 where
  carrier := {γ | γ ∈ edgeStabilizer q ∧ ∀ i, (q⁻¹ * γ * q).val i i = 1}
  one_mem' := by
    refine ⟨(edgeStabilizer q).one_mem, fun i => ?_⟩
    rw [mul_one, inv_mul_cancel]
    simp
  mul_mem' := by
    rintro γ δ ⟨hγ, dγ⟩ ⟨hδ, dδ⟩
    refine ⟨(edgeStabilizer q).mul_mem hγ hδ, fun i => ?_⟩
    rw [conj_mul, borel_diag_mul (edgeStabilizer_borel q hγ) (edgeStabilizer_borel q hδ), dγ, dδ, one_mul]
  inv_mem' := by
    rintro γ ⟨hγ, dγ⟩
    refine ⟨(edgeStabilizer q).inv_mem hγ, fun i => ?_⟩
    have hinv : q⁻¹ * γ⁻¹ * q = (q⁻¹ * γ * q)⁻¹ := by group
    have hprod := borel_diag_mul (edgeStabilizer_borel q hγ)
      (edgeStabilizer_borel q ((edgeStabilizer q).inv_mem hγ)) i
    rw [← conj_mul, mul_inv_cancel] at hprod
    have hone : ((q⁻¹ * 1 * q : RationalGL3)).val i i = 1 := by
      rw [mul_one, inv_mul_cancel]
      simp
    rw [hone, dγ, one_mul] at hprod
    exact hprod.symm

theorem unipotentStabilizer_le (q : RationalGL3) : unipotentStabilizer q ≤ edgeStabilizer q :=
  fun _ h => h.1

/-- The diagonal of the conjugated stabilizer element. -/
def stabilizerDiagonal (q : RationalGL3) (γ : edgeStabilizer q) : Fin 3 → ℚ :=
  fun i => (q⁻¹ * γ.val * q).val i i

theorem stabilizerDiagonal_mul (q : RationalGL3) (γ δ : edgeStabilizer q) (i : Fin 3) :
    stabilizerDiagonal q (γ * δ) i = stabilizerDiagonal q γ i * stabilizerDiagonal q δ i := by
  unfold stabilizerDiagonal
  rw [Subgroup.coe_mul, conj_mul, borel_diag_mul (edgeStabilizer_borel q γ.property)
    (edgeStabilizer_borel q δ.property)]

theorem stabilizerDiagonal_sign (q : RationalGL3) (γ : edgeStabilizer q) (i : Fin 3) :
    stabilizerDiagonal q γ i = 1 ∨ stabilizerDiagonal q γ i = -1 :=
  stabilizer_diag_sign q ⟨γ.val, γ.property.1⟩ (MulAction.mem_stabilizer_iff.mp γ.property.2) i

/-- The unipotent stabilizer has finitely many right cosets in the full stabilizer. -/
theorem unipotentStabilizer_finite (q : RationalGL3) :
    Finite (Quotient (QuotientGroup.rightRel ((unipotentStabilizer q).subgroupOf (edgeStabilizer q)))) := by
  let S : Set (Fin 3 → ℚ) := {d | ∀ i, d i = 1 ∨ d i = -1}
  have hS : S.Finite := by
    have : S ⊆ Set.pi Set.univ (fun _ => ({1, -1} : Set ℚ)) := by
      intro d hd i _
      rcases hd i with h | h <;> simp [h]
    exact (Set.Finite.pi (fun _ => Set.toFinite ({1, -1} : Set ℚ))).subset this
  have : Finite S := hS.to_subtype
  let f : Quotient (QuotientGroup.rightRel ((unipotentStabilizer q).subgroupOf (edgeStabilizer q))) → S :=
    Quotient.lift (fun γ => ⟨stabilizerDiagonal q γ, stabilizerDiagonal_sign q γ⟩) (by
      intro a b hab
      have hmem := QuotientGroup.rightRel_apply.mp hab
      apply Subtype.ext
      funext i
      have hb : b = (b * a⁻¹) * a := by group
      change stabilizerDiagonal q a i = stabilizerDiagonal q b i
      rw [hb, stabilizerDiagonal_mul]
      have : stabilizerDiagonal q (b * a⁻¹) i = 1 := hmem.2 i
      rw [this, one_mul])
  apply Finite.of_injective f
  intro x y hxy
  induction x using Quotient.inductionOn' with
  | h a =>
  induction y using Quotient.inductionOn' with
  | h b =>
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    refine ⟨(edgeStabilizer q).mul_mem b.property ((edgeStabilizer q).inv_mem a.property), fun i => ?_⟩
    have hdiag := congrFun (congrArg Subtype.val hxy) i
    change stabilizerDiagonal q a i = stabilizerDiagonal q b i at hdiag
    have hprod := stabilizerDiagonal_mul q (b * a⁻¹) a i
    rw [inv_mul_cancel_right] at hprod
    have ha : stabilizerDiagonal q a i ≠ 0 := by
      rcases stabilizerDiagonal_sign q a i with h | h <;> rw [h] <;> norm_num
    change stabilizerDiagonal q (b * a⁻¹) i = 1
    rw [← hdiag] at hprod
    field_simp at hprod
    linarith [hprod]

end TernaryPeriodPolynomials.FlagExactness
