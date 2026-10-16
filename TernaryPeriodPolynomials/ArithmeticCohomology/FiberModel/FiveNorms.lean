module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Norm

@[expose] public section


/-!
# The five norm equations in terms of the three seeds

For a signed-permutation equivariant `F`, the norm relation at the five representatives
`(0,0,1), (1,1,0), (1,1,1), (1,0,1), (1,0,0)` is, up to an invertible operator `ρ(k)` and a sign, the
corresponding seed relation of Lemma 4.3 (`N₂₃ P = 0`, `N₁₂ Q = 0`, `N₁₂ f = 0`, `eq:mixed1`,
`eq:mixed2`).  Here the relations are written with the twisted action `ρ`; all matrices are explicit
elements of `GL₃(ℤ)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryCovectorOrbits TernaryPoly.OrdinaryApartmentFrames

/-- An element of `GL₃(ℤ)` from an explicit matrix and its inverse. -/
def mkGL (M N : Matrix (Fin 3) (Fin 3) ℤ) (h1 : M * N = 1 := by decide +kernel)
    (h2 : N * M = 1 := by decide +kernel) : IntegralGL := ⟨M, N, h1, h2⟩

/-- A permutation of `Fin 3` from a function and its inverse. -/
def mkPerm (f g : Fin 3 → Fin 3) (h1 : ∀ i, g (f i) = i := by decide)
    (h2 : ∀ i, f (g i) = i := by decide) : Equiv.Perm (Fin 3) := ⟨f, g, h1, h2⟩

/-- `(a,b,c) ↦ (a, b, c + a)`, the substitution of `eq:mixed1` on `Q`. -/
def T1 : IntegralGL := mkGL !![1, 0, 0; 0, 1, 0; 1, 0, 1] !![1, 0, 0; 0, 1, 0; -1, 0, 1]
/-- `(a,b,c) ↦ (a + c, -c, b)`, the substitution of `eq:mixed1` on `f`. -/
def T2 : IntegralGL := mkGL !![1, 0, 1; 0, 0, -1; 0, 1, 0] !![1, 1, 0; 0, 0, 1; 0, -1, 0]
/-- `(a,b,c) ↦ (a, c + a, b)`, the substitution of `eq:mixed2` on `P`. -/
def T3 : IntegralGL := mkGL !![1, 0, 0; 1, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; -1, 1, 0]
/-- `(a,b,c) ↦ (-c, a + c, b)`, the substitution of `eq:mixed2` on `Q`. -/
def T4 : IntegralGL := mkGL !![0, 0, -1; 1, 0, 1; 0, 1, 0] !![1, 1, 0; 0, 0, 1; -1, 0, 0]
/-- `(a,b,c) ↦ (a, c, b)`. -/
def T5 : IntegralGL := mkGL !![1, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 0, 1, 0]
/-- `(a,b,c) ↦ (a, -c, b - c)`, the first substitution of `N₂₃`. -/
def U1 : IntegralGL := mkGL !![1, 0, 0; 0, 0, -1; 0, 1, -1] !![1, 0, 0; 0, -1, 1; 0, -1, 0]
/-- `(a,b,c) ↦ (a, c - b, -b)`, the second substitution of `N₂₃`. -/
def U2 : IntegralGL := mkGL !![1, 0, 0; 0, -1, 1; 0, -1, 0] !![1, 0, 0; 0, 0, -1; 0, 1, -1]
/-- The operator matrix relating the norm at `(0,0,1)` to `N₂₃`. -/
def K0 : IntegralGL := mkGL !![0, 1, 0; 0, 0, 1; 1, 0, 0] !![0, 0, 1; 1, 0, 0; 0, 1, 0]

section

variable {M : Type*} [AddCommGroup M] [Module ℚ M] {ρ : Representation ℚ IntegralGL M}

theorem rho_eq {x y z w : IntegralGL} (h : x * y = z * w) (m : M) :
    ρ x (ρ y m) = ρ z (ρ w m) := by
  rw [← rho_mul_apply, ← rho_mul_apply, h]

theorem IsSignedEquivariant.at_rep {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F)
    {i : Fin 3} {s : Finset (Fin 3)} {π : Equiv.Perm (Fin 3)} {r : NonzeroCovector}
    (h : act (rep i) (signedPerm s π) = r) :
    F r = ((Equiv.Perm.sign π : ℤˣ) : ℤ) • ρ (signedPerm s π)⁻¹ (F (rep i)) := by
  rw [← h]
  exact hF.signed s π (rep i)


/-- The permutation `(0 1 2) ↦ (1, 2, 0)` (as `π j`). -/
def pi0 : Equiv.Perm (Fin 3) := mkPerm ![1, 2, 0] ![2, 0, 1]

theorem norm_rep1 {F : NonzeroCovector → M} :
    normExpr ρ F (rep 1) = F (rep 1) + ρ aG (F (rep 1)) + ρ (aG ^ 2) (F (rep 1)) := by
  have ha : act (rep 1) aG = rep 1 := by
    apply Subtype.ext
    rw [act_val]
    decide +kernel
  have ha2 : act (rep 1) (aG ^ 2) = rep 1 := by
    rw [pow_two, act_mul, ha, ha]
  unfold normExpr
  rw [ha, ha2]

theorem norm_rep2 {F : NonzeroCovector → M} :
    normExpr ρ F (rep 2) = F (rep 2) + ρ aG (F (rep 2)) + ρ (aG ^ 2) (F (rep 2)) := by
  have ha : act (rep 2) aG = rep 2 := by
    apply Subtype.ext
    rw [act_val]
    decide +kernel
  have ha2 : act (rep 2) (aG ^ 2) = rep 2 := by
    rw [pow_two, act_mul, ha, ha]
  unfold normExpr
  rw [ha, ha2]

theorem norm_eq0 {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F) :
    normExpr ρ F ⟨representative 0, rep_ne_zero 0⟩ =
      ρ K0 (F (rep 0) + ρ U1⁻¹ (F (rep 0)) + ρ U2⁻¹ (F (rep 0))) := by
  have h0 : act (rep 0) (signedPerm ∅ pi0) = ⟨representative 0, rep_ne_zero 0⟩ := by
    apply Subtype.ext
    rw [act_signedPerm]
    decide +kernel
  have ha : act (⟨representative 0, rep_ne_zero 0⟩ : NonzeroCovector) aG =
      ⟨representative 0, rep_ne_zero 0⟩ := by
    apply Subtype.ext
    rw [act_val]
    decide +kernel
  have ha2 : act (⟨representative 0, rep_ne_zero 0⟩ : NonzeroCovector) (aG ^ 2) =
      ⟨representative 0, rep_ne_zero 0⟩ := by
    rw [pow_two, act_mul, ha, ha]
  have hs : ((Equiv.Perm.sign pi0 : ℤˣ) : ℤ) = 1 := by decide +kernel
  have e0 : (signedPerm ∅ pi0)⁻¹ = K0 := by decide +kernel
  unfold normExpr
  rw [ha, ha2, hF.at_rep h0, hs, one_smul, e0, map_add, map_add,
    rho_eq (x := aG) (y := K0) (z := K0) (w := U2⁻¹) (by decide +kernel),
    rho_eq (x := aG ^ 2) (y := K0) (z := K0) (w := U1⁻¹) (by decide +kernel)]
  abel


/-- The transposition `(1 2)` as `π j = (0, 2, 1)`. -/
def pi03 : Equiv.Perm (Fin 3) := mkPerm ![0, 2, 1] ![0, 2, 1]

/-- The transposition `(0 1)` as `π j = (1, 0, 2)`. -/
def pi01 : Equiv.Perm (Fin 3) := mkPerm ![1, 0, 2] ![1, 0, 2]

theorem norm_eq3 {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F) :
    normExpr ρ F ⟨representative 3, rep_ne_zero 3⟩ =
      -ρ T3 (ρ T1⁻¹ (F (rep 1)) - F (rep 1) - ρ T2⁻¹ (F (rep 2))) := by
  have h0 : act (rep 1) (signedPerm ∅ pi03) = ⟨representative 3, rep_ne_zero 3⟩ := by
    apply Subtype.ext
    rw [act_signedPerm]
    decide +kernel
  have h1 : act (rep 1) (signedPerm {0} cyclePerm') =
      act (⟨representative 3, rep_ne_zero 3⟩ : NonzeroCovector) aG := by
    apply Subtype.ext
    rw [act_signedPerm, act_val]
    decide +kernel
  have h2 : act (rep 2) (signedPerm {0} 1) =
      act (⟨representative 3, rep_ne_zero 3⟩ : NonzeroCovector) (aG ^ 2) := by
    apply Subtype.ext
    rw [act_signedPerm, pow_two, act_mul, act_val, act_val]
    decide +kernel
  have s0 : ((Equiv.Perm.sign pi03 : ℤˣ) : ℤ) = -1 := by decide +kernel
  have s1 : ((Equiv.Perm.sign cyclePerm' : ℤˣ) : ℤ) = 1 := by
    rw [sign_cycle]
    rfl
  have s2 : ((Equiv.Perm.sign (1 : Equiv.Perm (Fin 3)) : ℤˣ) : ℤ) = 1 := by simp
  have e0 : (signedPerm ∅ pi03)⁻¹ = T3 * T1⁻¹ := by decide +kernel
  have e1 : aG * (signedPerm {0} cyclePerm')⁻¹ = T3 := by decide +kernel
  have e2 : aG ^ 2 * (signedPerm {0} 1)⁻¹ = T3 * T2⁻¹ := by decide +kernel
  unfold normExpr
  rw [hF.at_rep h0, hF.at_rep h1, hF.at_rep h2, s0, s1, s2, one_smul, one_smul,
    ← rho_mul_apply, ← rho_mul_apply, e1, e2, e0]
  rw [rho_mul_apply, rho_mul_apply]
  simp only [map_sub, neg_smul, one_smul]
  abel

theorem norm_eq4 {F : NonzeroCovector → M} (hF : IsSignedEquivariant ρ F) :
    normExpr ρ F ⟨representative 4, rep_ne_zero 4⟩ =
      ρ T3 (ρ T3⁻¹ (F (rep 0)) - ρ T5⁻¹ (F (rep 0)) - ρ T4⁻¹ (F (rep 1))) := by
  have h0 : act (rep 0) (signedPerm ∅ 1) = ⟨representative 4, rep_ne_zero 4⟩ := by
    apply Subtype.ext
    rw [act_signedPerm]
    decide +kernel
  have h1 : act (rep 0) (signedPerm {0} pi01) =
      act (⟨representative 4, rep_ne_zero 4⟩ : NonzeroCovector) aG := by
    apply Subtype.ext
    rw [act_signedPerm, act_val]
    decide +kernel
  have h2 : act (rep 1) (signedPerm {0} 1) =
      act (⟨representative 4, rep_ne_zero 4⟩ : NonzeroCovector) (aG ^ 2) := by
    apply Subtype.ext
    rw [act_signedPerm, pow_two, act_mul, act_val, act_val]
    decide +kernel
  have hQ : Inv ρ (F (rep 1)) ∅ pi01 :=
    hF.hstab 1 ∅ pi01 (by apply Subtype.ext; rw [act_signedPerm]; decide +kernel)
  have s0 : ((Equiv.Perm.sign pi01 : ℤˣ) : ℤ) = -1 := by decide +kernel
  have s2 : ((Equiv.Perm.sign (1 : Equiv.Perm (Fin 3)) : ℤˣ) : ℤ) = 1 := by simp
  have e1 : aG * (signedPerm {0} pi01)⁻¹ = T3 * T5⁻¹ := by decide +kernel
  have e2 : aG ^ 2 * (signedPerm {0} 1)⁻¹ = T3 * T4⁻¹ * (signedPerm ∅ pi01)⁻¹ := by
    decide +kernel
  have e0 : (signedPerm ∅ 1 : IntegralGL)⁻¹ = 1 := by
    rw [signedPerm_empty_one, inv_one]
  have hQ' : ρ (signedPerm ∅ pi01)⁻¹ (F (rep 1)) = -F (rep 1) := by
    have h := hQ
    unfold Inv at h
    rw [h, s0, neg_smul, one_smul]
  unfold normExpr
  rw [hF.at_rep h0, hF.at_rep h1, hF.at_rep h2, s0, s2, one_smul, e0, map_one,
    Module.End.one_apply]
  simp only [map_zsmul]
  rw [← rho_mul_apply, ← rho_mul_apply, e1, e2, rho_mul_apply ρ (T3 * T4⁻¹) (signedPerm ∅ pi01)⁻¹, hQ']
  simp only [map_sub, map_neg, rho_mul_apply, rho_inv_cancel, neg_smul, one_smul]
  abel

end

end TernaryPeriodPolynomials.Argument.FiberModel
