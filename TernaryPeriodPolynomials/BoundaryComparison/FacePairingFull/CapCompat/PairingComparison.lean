module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.CapHomotopic

@[expose] public section


/-!
# The pairing of two cochains against a coinvariant cycle is compatible with a cap-homotopic chain map

If `u : C ⟶ D` is cap-homotopic along the cocycle `b` (`CapSystem.Homotopic`) and `a` is a cocycle of `D`, then for
every cycle `Ω` of the coinvariant chain complex of `C` (a chain whose boundary is killed by all invariant
functionals) the pairing `π ∘ (u^*b ⊗ u^*a) ∘ Δ_C (Ω)` equals `π ∘ (b ⊗ a) ∘ Δ_D (u Ω)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- A chain `Ω` of degree `m+1` whose boundary is killed by every invariant functional (a cycle of the coinvariants). -/
def IsCoinvCycle {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} {m : ℕ} (Ω : C.X (m+1)) : Prop :=
  ∀ φ : C.X m ⟶ 𝟙_ (Rep.{0} ℚ Γ), φ.hom ((C.d (m+1) m).hom Ω) = 0

theorem pairing_comparison {C D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (SC : DiagSystem C) (SD : DiagSystem D)
    (u : C ⟶ D) {W W' : Rep.{0} ℚ Γ} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ)) {n q : ℕ}
    (b : D.X n ⟶ W) (hb : D.d (n+1) n ≫ b = 0) (a : D.X (q+1) ⟶ W') (ha : D.d (q+1+1) (q+1) ≫ a = 0)
    (H : SC.toCapSystem.Homotopic SD.toCapSystem u b hb) (Ω : C.X (n+q+1)) (hΩ : IsCoinvCycle Ω) :
    π.hom (((u.f n ≫ b) ⊗ₘ (u.f (q+1) ≫ a)).hom ((SC.Δ n (q+1) (n+q+1) rfl).hom Ω)) =
      π.hom ((b ⊗ₘ a).hom ((SD.Δ n (q+1) (n+q+1) rfl).hom ((u.f (n+q+1)).hom Ω))) := by
  obtain ⟨h, -, hq⟩ := H
  have key := hq q
  set κ : W ⊗ D.X (q+1) ⟶ 𝟙_ (Rep.{0} ℚ Γ) := (W ◁ a) ≫ π with hκ
  have hz : (W ◁ D.d (q+1+1) (q+1)) ≫ κ = 0 := by
    rw [hκ, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalPreadditive.whiskerLeft_zero,
      zero_comp]
  have e := congrArg (fun m => m ≫ κ) key
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, hz,
    comp_zero, zero_add] at e
  have e4 := sub_eq_iff_eq_add.mp e
  have e5 := congrArg (fun m => m.hom Ω) e4
  have hφ := hΩ (h q ≫ κ)
  have l1 : (u.f n ≫ b) ⊗ₘ (u.f (q+1) ≫ a) =
      ((u.f n ≫ b) ▷ C.X (q+1)) ≫ (W ◁ u.f (q+1)) ≫ (W ◁ a) := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp]
  have l2 : b ⊗ₘ a = (b ▷ D.X (q+1)) ≫ (W ◁ a) := MonoidalCategory.tensorHom_def _ _
  simp only [Rep.add_hom, Rep.zsmul_hom, Rep.hom_comp] at e5 hφ
  have e6 : κ.hom ((W ◁ u.f (q+1)).hom ((SC.toCapSystem.cap (u.f n ≫ b) (chainMap_cocycle u b hb) (q+1)).hom Ω)) =
      (-1 : ℤ) ^ n • κ.hom ((h q).hom ((C.d (n+q+1) (n+q)).hom Ω)) +
        κ.hom ((SD.toCapSystem.cap b hb (q+1)).hom ((u.f (n+(q+1))).hom Ω)) := e5
  have hφ' : κ.hom ((h q).hom ((C.d (n+q+1) (n+q)).hom Ω)) = 0 := hφ
  rw [hφ', smul_zero, zero_add] at e6
  rw [l1, l2]
  exact e6


end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
