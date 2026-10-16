module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.Defs

@[expose] public section


/-!
# The signed permutation matrices of `GL₃(ℤ)` and the 26 covectors

The signed permutation matrices `signedPerm s π = D_s P_π` multiply as
`signedPerm s π * signedPerm s' π' = signedPerm (s Δ π(s')) (π π')`, act on the covectors
(`r ↦ r ∘ π` with the coordinates in `π(s)` negated), and the three covectors
`(1,0,0)`, `(1,1,0)`, `(1,1,1)` represent the three orbits of the 26 nonzero covectors.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryApartmentFrames

theorem signFrame_mul (s t : Finset (Fin 3)) :
    signFrame s * signFrame t = signFrame (symmDiff s t) := by
  revert s t
  decide +kernel

theorem permFrame_mul_signFrame (π : Equiv.Perm (Fin 3)) (s : Finset (Fin 3)) :
    permFrame π * signFrame s = signFrame (s.image π) * permFrame π := by
  revert π s
  decide +kernel

/-- Product of two signed permutation matrices. -/
theorem signedPerm_mul (s s' : Finset (Fin 3)) (π π' : Equiv.Perm (Fin 3)) :
    signedPerm s π * signedPerm s' π' = signedPerm (symmDiff s (s'.image π)) (π * π') := by
  unfold signedPerm
  calc signFrame s * permFrame π * (signFrame s' * permFrame π')
      = signFrame s * (permFrame π * signFrame s') * permFrame π' := by simp only [mul_assoc]
    _ = signFrame s * (signFrame (s'.image π) * permFrame π) * permFrame π' := by
        rw [permFrame_mul_signFrame]
    _ = (signFrame s * signFrame (s'.image π)) * (permFrame π * permFrame π') := by
        simp only [mul_assoc]
    _ = _ := by rw [signFrame_mul, ← map_mul]

theorem signedPerm_empty_one : signedPerm ∅ 1 = 1 := by
  unfold signedPerm
  rw [signFrame_empty, map_one, mul_one]

/-- Inverse of a signed permutation matrix. -/
theorem signedPerm_inv (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    (signedPerm s π)⁻¹ = signedPerm (s.image ⇑π⁻¹) π⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [signedPerm_mul, mul_inv_cancel, ← signedPerm_empty_one]
  congr 1
  have : (s.image ⇑π⁻¹).image ⇑π = s := by
    ext i
    simp [Finset.mem_image]
  rw [this, symmDiff_self]
  rfl

/-- The action of a signed permutation on a covector: negate the coordinates in `π(s)` and permute. -/
def moveRow (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : Fin 3 → ZMod 3) :
    Fin 3 → ZMod 3 :=
  fun j => if π j ∈ s then -r (π j) else r (π j)

theorem act_signedPerm (r : NonzeroCovector) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    (act r (signedPerm s π)).1 = moveRow s π r.1 := by
  have h : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : Fin 3 → ZMod 3),
      Matrix.vecMul r (mod3 (signedPerm s π).val) = moveRow s π r := by
    decide +kernel
  exact h s π r.1

/-- The three orbit representatives `(1,0,0)`, `(1,1,0)`, `(1,1,1)`. -/
def rep : Fin 3 → NonzeroCovector :=
  ![⟨![1, 0, 0], by decide⟩, ⟨![1, 1, 0], by decide⟩, ⟨![1, 1, 1], by decide⟩]

theorem cover_moveRow : ∀ r : Fin 3 → ZMod 3, r ≠ 0 →
    ∃ i : Fin 3, ∃ s : Finset (Fin 3), ∃ π : Equiv.Perm (Fin 3), moveRow s π (rep i).1 = r := by
  decide +kernel

theorem cover (r : NonzeroCovector) :
    ∃ d : Fin 3 × Finset (Fin 3) × Equiv.Perm (Fin 3), act (rep d.1) (signedPerm d.2.1 d.2.2) = r := by
  obtain ⟨i, s, π, h⟩ := cover_moveRow r.1 r.2
  exact ⟨(i, s, π), Subtype.ext (by rw [act_signedPerm]; exact h)⟩

theorem orbits_disjoint : ∀ (i i' : Fin 3) (s s' : Finset (Fin 3)) (π π' : Equiv.Perm (Fin 3)),
    moveRow s π (rep i).1 = moveRow s' π' (rep i').1 → i = i' := by
  decide +kernel

theorem stab_rep0 : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)),
    moveRow s π (rep 0).1 = (rep 0).1 → s ⊆ {1, 2} ∧ (π = 1 ∨ π = Equiv.swap 1 2) := by
  decide +kernel

theorem stab_rep1 : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)),
    moveRow s π (rep 1).1 = (rep 1).1 → s ⊆ {2} ∧ (π = 1 ∨ π = Equiv.swap 0 1) := by
  decide +kernel

theorem stab_rep2 : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)),
    moveRow s π (rep 2).1 = (rep 2).1 → s = ∅ := by
  decide +kernel

end TernaryPeriodPolynomials.Argument.FiberModel
