module

public import Mathlib

@[expose] public section


/-!
# Degree-two cohomology classes of a cochain complex of rational vector spaces

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section Cls

variable (K : CochainComplex (ModuleCat.{0} ℚ) ℕ)

/-- The morphism `ℚ ⟶ K.X 2` sending `1` to `a`. -/
def elt2 (a : K.X 2) : ModuleCat.of ℚ ℚ ⟶ K.X 2 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.X 2) a)

theorem elt2_comp (a : K.X 2) (ha : (K.d 2 3).hom a = 0) : elt2 K a ≫ K.d 2 3 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simpa [elt2] using ha

/-- The cycle of `K` in degree two attached to an element killed by the differential. -/
def cycle2 (a : K.X 2) (ha : (K.d 2 3).hom a = 0) : K.cycles 2 :=
  (K.liftCycles (elt2 K a) 3 (CochainComplex.next ℕ 2) (elt2_comp K a ha)).hom 1

theorem iCycles_cycle2 (a : K.X 2) (ha : (K.d 2 3).hom a = 0) :
    (K.iCycles 2).hom (cycle2 K a ha) = a := by
  have h : (K.liftCycles (elt2 K a) 3 (CochainComplex.next ℕ 2) (elt2_comp K a ha) ≫
      K.iCycles 2).hom 1 = a := by
    rw [K.liftCycles_i]
    simp [elt2]
  exact h

theorem prev_two : (ComplexShape.up ℕ).prev 2 = 1 :=
  ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel 1 2 from rfl)

theorem iCycles_injective (i : ℕ) : Function.Injective (K.iCycles i).hom :=
  (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance

theorem cycle2_add (a b : K.X 2) (ha : (K.d 2 3).hom a = 0) (hb : (K.d 2 3).hom b = 0)
    (hab : (K.d 2 3).hom (a + b) = 0) :
    cycle2 K (a + b) hab = cycle2 K a ha + cycle2 K b hb := by
  apply iCycles_injective K 2
  rw [map_add, iCycles_cycle2, iCycles_cycle2, iCycles_cycle2]

theorem cycle2_smul (r : ℚ) (a : K.X 2) (ha : (K.d 2 3).hom a = 0)
    (hra : (K.d 2 3).hom (r • a) = 0) : cycle2 K (r • a) hra = r • cycle2 K a ha := by
  apply iCycles_injective K 2
  rw [map_smul, iCycles_cycle2, iCycles_cycle2]

/-- The class in `H²(K)` of a degree-two cocycle. -/
def cls2 (a : K.X 2) (ha : (K.d 2 3).hom a = 0) : K.homology 2 :=
  (K.homologyπ 2).hom (cycle2 K a ha)

theorem cls2_add (a b : K.X 2) (ha : (K.d 2 3).hom a = 0) (hb : (K.d 2 3).hom b = 0)
    (hab : (K.d 2 3).hom (a + b) = 0) : cls2 K (a + b) hab = cls2 K a ha + cls2 K b hb := by
  unfold cls2
  rw [cycle2_add K a b ha hb hab, map_add]

theorem cls2_smul (r : ℚ) (a : K.X 2) (ha : (K.d 2 3).hom a = 0)
    (hra : (K.d 2 3).hom (r • a) = 0) : cls2 K (r • a) hra = r • cls2 K a ha := by
  unfold cls2
  rw [cycle2_smul K r a ha hra, map_smul]

theorem cls2_congr {a a' : K.X 2} (ha : (K.d 2 3).hom a = 0) (ha' : (K.d 2 3).hom a' = 0)
    (h : a = a') : cls2 K a ha = cls2 K a' ha' := by
  subst h
  rfl

theorem cls2_eq_zero_iff (a : K.X 2) (ha : (K.d 2 3).hom a = 0) :
    cls2 K a ha = 0 ↔ ∃ b : K.X 1, (K.d 1 2).hom b = a := by
  have hz : (K.liftCycles (elt2 K a) 3 (CochainComplex.next ℕ 2) (elt2_comp K a ha) ≫
      K.homologyπ 2).hom 1 = cls2 K a ha := rfl
  rw [← hz]
  constructor
  · intro h
    have h0 : K.liftCycles (elt2 K a) 3 (CochainComplex.next ℕ 2) (elt2_comp K a ha) ≫
        K.homologyπ 2 = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa using h
    obtain ⟨A', π, hπ, x₁, hx⟩ :=
      (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements 1 2 3
        (prev_two) (CochainComplex.next ℕ 2) (elt2 K a)
        (elt2_comp K a ha)).1 h0
    obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
    refine ⟨x₁.hom t, ?_⟩
    have := congrArg (fun m => m.hom t) hx
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    change (elt2 K a).hom (π.hom t) = (K.d 1 2).hom (x₁.hom t) at this
    rw [ht] at this
    simpa [elt2] using this.symm
  · rintro ⟨b, hb⟩
    have h0 : K.liftCycles (elt2 K a) 3 (CochainComplex.next ℕ 2) (elt2_comp K a ha) ≫
        K.homologyπ 2 = 0 := by
      refine (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements 1 2 3
        (prev_two) (CochainComplex.next ℕ 2) (elt2 K a)
        (elt2_comp K a ha)).2 ⟨ModuleCat.of ℚ ℚ, 𝟙 _, inferInstance,
          ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.X 1) b), ?_⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa [elt2] using hb.symm
    rw [h0]
    rfl

theorem map_cocycle {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X 2)
    (ha : (K.d 2 3).hom a = 0) : (L.d 2 3).hom ((φ.f 2).hom a) = 0 := by
  have h := congrArg (fun m => m.hom a) (φ.comm 2 3)
  change (L.d 2 3).hom ((φ.f 2).hom a) = (φ.f 3).hom ((K.d 2 3).hom a) at h
  rw [h, ha, map_zero]

theorem cycle2_map {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X 2)
    (ha : (K.d 2 3).hom a = 0) (hφ : (L.d 2 3).hom ((φ.f 2).hom a) = 0) :
    (HomologicalComplex.cyclesMap φ 2).hom (cycle2 K a ha) = cycle2 L ((φ.f 2).hom a) hφ := by
  apply iCycles_injective L 2
  have h := congrArg (fun m => m.hom (cycle2 K a ha)) (HomologicalComplex.cyclesMap_i φ 2)
  change (L.iCycles 2).hom ((HomologicalComplex.cyclesMap φ 2).hom (cycle2 K a ha)) =
    (φ.f 2).hom ((K.iCycles 2).hom (cycle2 K a ha)) at h
  rw [h, iCycles_cycle2, iCycles_cycle2]

/-- **Naturality of classes**: a cochain map sends the class of a cocycle to the class of its image. -/
theorem cls2_map {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X 2)
    (ha : (K.d 2 3).hom a = 0) (hφ : (L.d 2 3).hom ((φ.f 2).hom a) = 0) :
    (HomologicalComplex.homologyMap φ 2).hom (cls2 K a ha) = cls2 L ((φ.f 2).hom a) hφ := by
  have h := congrArg (fun m => m.hom (cycle2 K a ha)) (HomologicalComplex.homologyπ_naturality φ 2)
  change (HomologicalComplex.homologyMap φ 2).hom ((K.homologyπ 2).hom (cycle2 K a ha)) =
    (L.homologyπ 2).hom ((HomologicalComplex.cyclesMap φ 2).hom (cycle2 K a ha)) at h
  rw [cycle2_map K φ a ha hφ] at h
  exact h

/-- Every class of `H²(K)` is represented by a cocycle. -/
theorem exists_cls2 (x : K.homology 2) :
    ∃ (a : K.X 2) (ha : (K.d 2 3).hom a = 0), cls2 K a ha = x := by
  have hepi : Epi (K.homologyπ 2) := inferInstance
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 2)).1 hepi x
  have hd : (K.d 2 3).hom ((K.iCycles 2).hom z) = 0 := by
    have h := congrArg (fun m => m.hom z) (K.iCycles_d 2 3)
    exact h
  refine ⟨(K.iCycles 2).hom z, hd, ?_⟩
  unfold cls2
  congr 1
  apply iCycles_injective K 2
  exact iCycles_cycle2 K _ hd

end Cls

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
