module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Corestriction for homogeneous cochains

Let `Γ' ≤ Γ` be a subgroup of finite index, acting on vertices in `G`. If a
`Γ`-equivariant homogeneous 2-cochain has a `Γ'`-equivariant primitive, then it has a
`Γ`-equivariant primitive: average the `Γ'`-primitive over the right cosets
`Γ' \ Γ`. In characteristic zero, vanishing of homogeneous `H²` classes can therefore
be checked on finite-index subgroups, such as the unipotent part of a Borel stabilizer.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The right-coset average of a `Γ'`-equivariant 1-cochain. -/
def cosetAverageValue (Γ Γ' : Subgroup G) (ρ : Representation ℂ G V)
    (P' : cochains Γ' ρ 1) (x : Fin 2 → G) :
    Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ)) → V :=
  Quotient.lift (fun γ : Γ => ρ (γ.val)⁻¹ (P'.val (fun i => γ.val * x i))) (by
    intro a b hab
    have hmem : b * a⁻¹ ∈ Γ'.subgroupOf Γ := QuotientGroup.rightRel_apply.mp hab
    have hb : b.val = (b * a⁻¹).val * a.val := by simp
    change ρ (a.val)⁻¹ (P'.val (fun i => a.val * x i)) = ρ (b.val)⁻¹ (P'.val (fun i => b.val * x i))
    have hequiv := P'.property ⟨(b * a⁻¹).val, hmem⟩ (fun i => a.val * x i)
    have hfun : (fun i => b.val * x i) = (fun i => (b * a⁻¹).val * (a.val * x i)) := by
      funext i
      rw [hb, mul_assoc]
    rw [hfun, hequiv, ← Module.End.mul_apply, ← map_mul]
    congr 2
    rw [hb]
    group)

theorem rightCoset_mul_rel (Γ Γ' : Subgroup G) (γ₀ : Γ) (a b : Γ)
    (hab : QuotientGroup.rightRel (Γ'.subgroupOf Γ) a b) :
    QuotientGroup.rightRel (Γ'.subgroupOf Γ) (a * γ₀) (b * γ₀) := by
  rw [QuotientGroup.rightRel_apply] at hab ⊢
  simpa [mul_assoc] using hab

/-- Right multiplication on right cosets. -/
def rightCosetMul (Γ Γ' : Subgroup G) (γ₀ : Γ) :
    Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ)) ≃
      Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ)) where
  toFun := Quotient.map' (· * γ₀) (fun a b h => rightCoset_mul_rel Γ Γ' γ₀ a b h)
  invFun := Quotient.map' (· * γ₀⁻¹) (fun a b h => rightCoset_mul_rel Γ Γ' γ₀⁻¹ a b h)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

/-- **Corestriction.** A `Γ`-equivariant 2-cochain with a `Γ'`-equivariant primitive has
a `Γ`-equivariant primitive, when `Γ'` has finite index in `Γ`. -/
theorem exists_primitive_of_finiteIndex (Γ Γ' : Subgroup G)
    [Finite (Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ)))]
    (ρ : Representation ℂ G V) (K : cochains Γ ρ 2) (P' : cochains Γ' ρ 1)
    (boundary : ∀ x, (differentialOne Γ' ρ P').val x = K.val x) :
    ∃ P : cochains Γ ρ 1, ∀ x, (differentialOne Γ ρ P).val x = K.val x := by
  classical
  have : Fintype (Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ))) := Fintype.ofFinite _
  set Q := Quotient (QuotientGroup.rightRel (Γ'.subgroupOf Γ))
  have hcard : (Fintype.card Q : ℂ) ≠ 0 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨Quotient.mk'' 1⟩
    exact_mod_cast this.ne'
  let value : (Fin 2 → G) → V := fun x =>
    (Fintype.card Q : ℂ)⁻¹ • ∑ q : Q, cosetAverageValue Γ Γ' ρ P' x q
  have hequiv : ∀ (γ₀ : Γ) x, value (fun i => γ₀.val * x i) = ρ γ₀.val (value x) := by
    intro γ₀ x
    simp only [value, map_smul, map_sum]
    congr 1
    conv_rhs => rw [← (rightCosetMul Γ Γ' γ₀).sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn' with
    | h a =>
      simp only [rightCosetMul, Equiv.coe_fn_mk, Quotient.map'_mk'', cosetAverageValue]
      change ρ (a.val)⁻¹ (P'.val (fun i => a.val * (γ₀.val * x i))) =
        ρ γ₀.val (ρ ((a * γ₀).val)⁻¹ (P'.val (fun i => (a * γ₀).val * x i)))
      have hfun : (fun i => (a * γ₀).val * x i) = (fun i => a.val * (γ₀.val * x i)) := by
        funext i
        simp [mul_assoc]
      rw [hfun, ← Module.End.mul_apply, ← map_mul]
      congr 2
      simp only [Subgroup.coe_mul]
      group
  refine ⟨⟨value, hequiv⟩, fun x => ?_⟩
  change value ![x 1, x 2] - value ![x 0, x 2] + value ![x 0, x 1] = K.val x
  simp only [value]
  rw [← smul_sub, ← smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hterm : ∀ q : Q, cosetAverageValue Γ Γ' ρ P' ![x 1, x 2] q -
      cosetAverageValue Γ Γ' ρ P' ![x 0, x 2] q + cosetAverageValue Γ Γ' ρ P' ![x 0, x 1] q =
        K.val x := by
    intro q
    induction q using Quotient.inductionOn' with
    | h a =>
      simp only [cosetAverageValue, Quotient.lift_mk]
      change ρ (a.val)⁻¹ (P'.val (fun i => a.val * ![x 1, x 2] i)) -
        ρ (a.val)⁻¹ (P'.val (fun i => a.val * ![x 0, x 2] i)) +
        ρ (a.val)⁻¹ (P'.val (fun i => a.val * ![x 0, x 1] i)) = K.val x
      rw [← map_sub, ← map_add]
      have hb := boundary (fun i => a.val * x i)
      change P'.val ![a.val * x 1, a.val * x 2] - P'.val ![a.val * x 0, a.val * x 2] +
        P'.val ![a.val * x 0, a.val * x 1] = K.val (fun i => a.val * x i) at hb
      have h12 : (fun i => a.val * ![x 1, x 2] i) = ![a.val * x 1, a.val * x 2] := by
        funext i; fin_cases i <;> rfl
      have h02 : (fun i => a.val * ![x 0, x 2] i) = ![a.val * x 0, a.val * x 2] := by
        funext i; fin_cases i <;> rfl
      have h01 : (fun i => a.val * ![x 0, x 1] i) = ![a.val * x 0, a.val * x 1] := by
        funext i; fin_cases i <;> rfl
      rw [h12, h02, h01, hb, K.property ⟨a.val, a.property⟩ x, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hcard, one_smul]

end TernaryPeriodPolynomials.FlagExactness
