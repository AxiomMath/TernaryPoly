module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingComparison

@[expose] public section


/-!
# Invariance of the diagonal pairing under cohomologous cochains

For a diagonal system `S` on a complex `C` and a coinvariant cycle `v : C.X 4`, the pairing
`π ∘ (b ⊗ a) ∘ Δ_{2,2}` of two degree-two cochains `b`, `a` only depends on the cohomology classes of `b` and `a`
when the other cochain is a cocycle: a coboundary `d ≫ η` in the first slot (`pair_cob_left`) or the second slot
(`pair_cob_right`) pairs to zero, by the Leibniz rule for `Δ_{1,2}` resp. `Δ_{2,1}` and the invariance of `π ∘ (η ⊗ a) ∘ Δ_{1,2}`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ] {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : DiagSystem C)
  {W W' : Rep.{0} ℚ Γ} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ))

/-- A coboundary in the first slot pairs to zero against a cocycle on a coinvariant cycle. -/
theorem pair_cob_left (η : C.X 1 ⟶ W) (a : C.X 2 ⟶ W') (ha : C.d 3 2 ≫ a = 0) (v : C.X 4)
    (hv : IsCoinvCycle v) :
    (S.Δ 2 2 4 rfl ≫ ((C.d 2 1 ≫ η) ⊗ₘ a) ≫ π).hom v = 0 := by
  have h1 : (C.X 1 ◁ C.d 3 2) ≫ (η ⊗ₘ a) = 0 := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, ha, Category.id_comp,
      tensorHom_def, MonoidalPreadditive.whiskerLeft_zero, comp_zero]
  have h2 : (C.d 2 1 ▷ C.X 2) ≫ (η ⊗ₘ a) = (C.d 2 1 ≫ η) ⊗ₘ a := by
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have key : C.d 4 3 ≫ (S.Δ 1 2 3 rfl ≫ (η ⊗ₘ a) ≫ π) = S.Δ 2 2 4 rfl ≫ ((C.d 2 1 ≫ η) ⊗ₘ a) ≫ π := by
    rw [← Category.assoc, S.leibniz 1 2 3 rfl]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
    rw [← Category.assoc (C.d (1+1) 1 ▷ C.X 2), h2, ← Category.assoc (C.X 1 ◁ C.d (2+1) 2), h1, zero_comp,
      comp_zero, smul_zero, add_zero]
  rw [← key]
  exact hv (S.Δ 1 2 3 rfl ≫ (η ⊗ₘ a) ≫ π)

/-- A coboundary in the second slot pairs to zero against a cocycle on a coinvariant cycle. -/
theorem pair_cob_right (b : C.X 2 ⟶ W) (hb : C.d 3 2 ≫ b = 0) (η : C.X 1 ⟶ W') (v : C.X 4)
    (hv : IsCoinvCycle v) :
    (S.Δ 2 2 4 rfl ≫ (b ⊗ₘ (C.d 2 1 ≫ η)) ≫ π).hom v = 0 := by
  have h1 : (C.d 3 2 ▷ C.X 1) ≫ (b ⊗ₘ η) = 0 := by
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, hb, Category.id_comp,
      tensorHom_def, MonoidalPreadditive.zero_whiskerRight, zero_comp]
  have h2 : (C.X 2 ◁ C.d 2 1) ≫ (b ⊗ₘ η) = b ⊗ₘ (C.d 2 1 ≫ η) := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have key : C.d 4 3 ≫ (S.Δ 2 1 3 rfl ≫ (b ⊗ₘ η) ≫ π) = S.Δ 2 2 4 rfl ≫ (b ⊗ₘ (C.d 2 1 ≫ η)) ≫ π := by
    rw [← Category.assoc, S.leibniz 2 1 3 rfl]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
    rw [← Category.assoc (C.d (2+1) 2 ▷ C.X 1), h1, ← Category.assoc (C.X 2 ◁ C.d (1+1) 1), h2, zero_comp,
      comp_zero, zero_add]
    simp
  rw [← key]
  exact hv (S.Δ 2 1 3 rfl ≫ (b ⊗ₘ η) ≫ π)

/-- The pairing of two degree-two cocycles on a coinvariant cycle only depends on their cohomology classes. -/
theorem pair_cohomologous {x x' : C.X 2 ⟶ W} {y y' : C.X 2 ⟶ W'} (hx' : C.d 3 2 ≫ x' = 0)
    (hy : C.d 3 2 ≫ y = 0) (η : C.X 1 ⟶ W) (hxx : x = x' + C.d 2 1 ≫ η)
    (η' : C.X 1 ⟶ W') (hyy : y = y' + C.d 2 1 ≫ η') (v : C.X 4) (hv : IsCoinvCycle v) :
    (S.Δ 2 2 4 rfl ≫ (x ⊗ₘ y) ≫ π).hom v = (S.Δ 2 2 4 rfl ≫ (x' ⊗ₘ y') ≫ π).hom v := by
  have hy' : C.d 3 2 ≫ y' = 0 := by
    have h := hy
    rw [hyy, Preadditive.comp_add, ← Category.assoc, C.d_comp_d, zero_comp, add_zero] at h
    exact h
  have e1 := pair_cob_left S π η y hy v hv
  have e2 := pair_cob_right S π x' hx' η' v hv
  have : S.Δ 2 2 4 rfl ≫ (x ⊗ₘ y) ≫ π =
      S.Δ 2 2 4 rfl ≫ ((C.d 2 1 ≫ η) ⊗ₘ y) ≫ π + S.Δ 2 2 4 rfl ≫ (x' ⊗ₘ (C.d 2 1 ≫ η')) ≫ π +
        S.Δ 2 2 4 rfl ≫ (x' ⊗ₘ y') ≫ π := by
    rw [hxx, hyy]
    simp only [MonoidalPreadditive.add_tensor, MonoidalPreadditive.tensor_add, Preadditive.add_comp,
      Preadditive.comp_add]
    abel
  rw [this]
  simp only [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply, e1, e2, zero_add]

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
