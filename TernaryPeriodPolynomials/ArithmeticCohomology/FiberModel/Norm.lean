module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Seeds

@[expose] public section


/-!
# The fiber norm relation needs to be checked on five covectors only

For a signed-permutation equivariant function `F : 𝒮 → M`, the norm relation
`F(r) + ρ(A) F(rA) + ρ(A²) F(rA²) = 0` holds for all `r ∈ 𝒮` as soon as it holds for the five
representatives `(0,0,1), (1,1,0), (1,1,1), (1,0,1), (1,0,0)` of the orbits of
`⟨A, D₁₂, D₃⟩` (this is the orbit decomposition `2 + 2 + 4 + 12 + 6 = 26` of the paper).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryCovectorOrbits TernaryPoly.OrdinaryApartmentFrames

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M] {ρ : Representation ℚ IntegralGL M}

/-- The norm matrix `A` of the paper, as an element of `GL₃(ℤ)`. -/
abbrev aG : IntegralGL := ReferenceCoefficientMatrices.a

theorem act_a_val (r : NonzeroCovector) : (act r aG).1 = stepA r.1 := by
  rw [act_val, stepA_matrix]
  rfl

theorem act_a_sq_val (r : NonzeroCovector) : (act r (aG ^ 2)).1 = stepA (stepA r.1) := by
  rw [pow_two, act_mul]
  rw [act_a_val, act_a_val]

theorem act_signFrame_val (r : NonzeroCovector) (s : Finset (Fin 3)) :
    (act r (signFrame s)).1 = fun j => if j ∈ s then -r.1 j else r.1 j := by
  have h := act_signedPerm r s 1
  rw [signedPerm, map_one, mul_one] at h
  rw [h]
  rfl

/-- Extension of a function on `𝒮` by zero to all covectors. -/
def extZero (F : NonzeroCovector → M) (r : Fin 3 → ZMod 3) : M :=
  if h : r = 0 then 0 else F ⟨r, h⟩

omit [Module ℚ M] in
theorem extZero_coe (F : NonzeroCovector → M) (r : NonzeroCovector) : extZero F r.1 = F r := by
  unfold extZero
  rw [dite_eq_right r.2]

theorem IsSignedEquivariant.sign_apply {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F)
    (s : Finset (Fin 3)) (r : NonzeroCovector) :
    F (act r (signFrame s)) = ρ (signFrame s)⁻¹ (F r) := by
  have h := hF.signed s 1 r
  rw [signedPerm, map_one, mul_one] at h
  rw [h, map_one, Units.val_one, one_smul]

theorem a_inv_mul_a_inv : aG⁻¹ * aG⁻¹ = aG := by
  rw [ReferenceCoefficientMatrices.a_inv_eq_sq, ← pow_add, show 2 + 2 = 1 + 3 from rfl, pow_add,
    ReferenceCoefficientMatrices.a_cube, mul_one, pow_one]

theorem rep_ne_zero (i : Fin 5) : representative i ≠ 0 := by
  revert i
  decide

theorem norm_extZero (F : NonzeroCovector → M) (r : NonzeroCovector) :
    OrdinaryFiberNorm.norm (ρ aG⁻¹) (extZero F) r.1 = normExpr ρ F r := by
  unfold OrdinaryFiberNorm.norm normExpr
  have h1 : (act r aG).1 = stepA r.1 := act_a_val r
  have h2 : (act r (aG ^ 2)).1 = stepA (stepA r.1) := act_a_sq_val r
  rw [← h2, ← h1, extZero_coe, extZero_coe, extZero_coe]
  have e1 : ρ aG⁻¹ = ρ (aG ^ 2) := by
    rw [ReferenceCoefficientMatrices.a_inv_eq_sq]
  have e2 : ρ aG⁻¹ (ρ aG⁻¹ (F (act r aG))) = ρ aG (F (act r aG)) := by
    rw [← rho_mul_apply, a_inv_mul_a_inv]
  rw [e2, e1]
  exact add_right_comm _ _ _


theorem extZero_sign {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F)
    (s : Finset (Fin 3)) (f : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hf : ∀ r : NonzeroCovector, f r.1 = (act r (signFrame s)).1) (hf0 : f 0 = 0)
    (r : Fin 3 → ZMod 3) : extZero F (f r) = ρ (signFrame s)⁻¹ (extZero F r) := by
  by_cases hr : r = 0
  · subst hr
    rw [hf0]
    simp [extZero]
  · have h1 : extZero F (f r) = F (act ⟨r, hr⟩ (signFrame s)) := by
      rw [hf ⟨r, hr⟩]
      exact extZero_coe F _
    have h2 : extZero F r = F ⟨r, hr⟩ := extZero_coe F ⟨r, hr⟩
    rw [h1, h2, hF.sign_apply]

theorem sign12_eq (r : NonzeroCovector) : sign12 r.1 = (act r (signFrame {0, 1})).1 := by
  rw [act_signFrame_val]
  funext j
  fin_cases j <;> simp [sign12]

theorem sign3_eq (r : NonzeroCovector) : sign3 r.1 = (act r (signFrame {2})).1 := by
  rw [act_signFrame_val]
  funext j
  fin_cases j <;> simp [sign3]

theorem a_inv_comm_D12 : aG⁻¹ * (signFrame {0, 1})⁻¹ = (signFrame {0, 1})⁻¹ * aG⁻¹ := by
  decide +kernel

theorem a_inv_comm_D3 : aG⁻¹ * (signFrame {2})⁻¹ = (signFrame {2})⁻¹ * aG⁻¹ := by
  decide +kernel

/-- **Five norm equations suffice.** -/
theorem IsSignedEquivariant.norm_of_five {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F)
    (h5 : ∀ i : Fin 5, normExpr ρ F ⟨representative i, rep_ne_zero i⟩ = 0) :
    ∀ r, normExpr ρ F r = 0 := by
  have h12 : ∀ r, extZero F (sign12 r) = ρ (signFrame {0, 1})⁻¹ (extZero F r) :=
    extZero_sign hF _ sign12 sign12_eq (by funext j; fin_cases j <;> simp [sign12])
  have h3 : ∀ r, extZero F (sign3 r) = ρ (signFrame {2})⁻¹ (extZero F r) :=
    extZero_sign hF _ sign3 sign3_eq (by funext j; fin_cases j <;> simp [sign3])
  have hα : ∀ v, ρ aG⁻¹ (ρ aG⁻¹ (ρ aG⁻¹ v)) = v := by
    intro v
    rw [← rho_mul_apply, ← rho_mul_apply]
    have : aG⁻¹ * aG⁻¹ * aG⁻¹ = 1 := by
      rw [a_inv_mul_a_inv]
      exact mul_inv_cancel _
    rw [this, map_one, Module.End.one_apply]
  have hc12 : ∀ v, ρ aG⁻¹ (ρ (signFrame {0, 1})⁻¹ v) = ρ (signFrame {0, 1})⁻¹ (ρ aG⁻¹ v) := by
    intro v
    rw [← rho_mul_apply, ← rho_mul_apply, a_inv_comm_D12]
  have hc3 : ∀ v, ρ aG⁻¹ (ρ (signFrame {2})⁻¹ v) = ρ (signFrame {2})⁻¹ (ρ aG⁻¹ v) := by
    intro v
    rw [← rho_mul_apply, ← rho_mul_apply, a_inv_comm_D3]
  have hfive : ∀ i : Fin 5, OrdinaryFiberNorm.norm (ρ aG⁻¹) (extZero F) (representative i) = 0 :=
    fun i => (norm_extZero F ⟨representative i, rep_ne_zero i⟩).trans (h5 i)
  have key := OrdinaryFiberNorm.all_norms_of_five (ρ aG⁻¹) (ρ (signFrame {0, 1})⁻¹)
    (ρ (signFrame {2})⁻¹) (extZero F) hα h12 h3 hc12 hc3 hfive
  intro r
  exact (norm_extZero F r).symm.trans (key r.1 r.2)

end

end TernaryPeriodPolynomials.Argument.FiberModel
