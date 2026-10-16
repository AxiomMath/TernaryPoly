module

public import Mathlib

@[expose] public section


/-!
# Degree-`m+1` cohomology classes of a cochain complex of rational vector spaces

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section Cls

variable {m : ℕ} (K : CochainComplex (ModuleCat.{0} ℚ) ℕ)

/-- The morphism `ℚ ⟶ K.X (m+1)` sending `1` to `a`. -/
def eltS (a : K.X (m+1)) : ModuleCat.of ℚ ℚ ⟶ K.X (m+1) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.X (m+1)) a)

theorem eltS_comp (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) : eltS K a ≫ K.d (m+1) (m+1+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simpa [eltS] using ha

/-- The cycle of `K` in degree two attached to an element killed by the differential. -/
def cycleS (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) : K.cycles (m+1) :=
  (K.liftCycles (eltS K a) (m+1+1) (CochainComplex.next ℕ (m+1)) (eltS_comp K a ha)).hom 1

theorem iCycles_cycleS (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) :
    (K.iCycles (m+1)).hom (cycleS K a ha) = a := by
  have h : (K.liftCycles (eltS K a) (m+1+1) (CochainComplex.next ℕ (m+1)) (eltS_comp K a ha) ≫
      K.iCycles (m+1)).hom 1 = a := by
    rw [K.liftCycles_i]
    simp [eltS]
  exact h

theorem prev_succ (m : ℕ) : (ComplexShape.up ℕ).prev (m + 1) = m :=
  ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel m (m + 1) from rfl)

theorem iCyclesS_injective (i : ℕ) : Function.Injective (K.iCycles i).hom :=
  (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance

theorem cycleS_add (a b : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) (hb : (K.d (m+1) (m+1+1)).hom b = 0)
    (hab : (K.d (m+1) (m+1+1)).hom (a + b) = 0) :
    cycleS K (a + b) hab = cycleS K a ha + cycleS K b hb := by
  apply iCyclesS_injective K (m+1)
  rw [map_add, iCycles_cycleS, iCycles_cycleS, iCycles_cycleS]

theorem cycleS_smul (r : ℚ) (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0)
    (hra : (K.d (m+1) (m+1+1)).hom (r • a) = 0) : cycleS K (r • a) hra = r • cycleS K a ha := by
  apply iCyclesS_injective K (m+1)
  rw [map_smul, iCycles_cycleS, iCycles_cycleS]

/-- The class in `H²(K)` of a degree-`m+1` cocycle. -/
def clsS (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) : K.homology (m+1) :=
  (K.homologyπ (m+1)).hom (cycleS K a ha)

theorem clsS_add (a b : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) (hb : (K.d (m+1) (m+1+1)).hom b = 0)
    (hab : (K.d (m+1) (m+1+1)).hom (a + b) = 0) : clsS K (a + b) hab = clsS K a ha + clsS K b hb := by
  unfold clsS
  rw [cycleS_add K a b ha hb hab, map_add]

theorem clsS_smul (r : ℚ) (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0)
    (hra : (K.d (m+1) (m+1+1)).hom (r • a) = 0) : clsS K (r • a) hra = r • clsS K a ha := by
  unfold clsS
  rw [cycleS_smul K r a ha hra, map_smul]

theorem clsS_congr {a a' : K.X (m+1)} (ha : (K.d (m+1) (m+1+1)).hom a = 0) (ha' : (K.d (m+1) (m+1+1)).hom a' = 0)
    (h : a = a') : clsS K a ha = clsS K a' ha' := by
  subst h
  rfl

theorem clsS_eq_zero_iff (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0) :
    clsS K a ha = 0 ↔ ∃ b : K.X m, (K.d m (m+1)).hom b = a := by
  have hz : (K.liftCycles (eltS K a) (m+1+1) (CochainComplex.next ℕ (m+1)) (eltS_comp K a ha) ≫
      K.homologyπ (m+1)).hom 1 = clsS K a ha := rfl
  rw [← hz]
  constructor
  · intro h
    have h0 : K.liftCycles (eltS K a) (m+1+1) (CochainComplex.next ℕ (m+1)) (eltS_comp K a ha) ≫
        K.homologyπ (m+1) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa using h
    obtain ⟨A', π, hπ, x₁, hx⟩ :=
      (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements m (m+1) (m+1+1)
        (prev_succ m) (CochainComplex.next ℕ (m+1)) (eltS K a)
        (eltS_comp K a ha)).1 h0
    obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
    refine ⟨x₁.hom t, ?_⟩
    have := congrArg (fun m => m.hom t) hx
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    change (eltS K a).hom (π.hom t) = (K.d m (m+1)).hom (x₁.hom t) at this
    rw [ht] at this
    simpa [eltS] using this.symm
  · rintro ⟨b, hb⟩
    have h0 : K.liftCycles (eltS K a) (m+1+1) (CochainComplex.next ℕ (m+1)) (eltS_comp K a ha) ≫
        K.homologyπ (m+1) = 0 := by
      refine (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements m (m+1) (m+1+1)
        (prev_succ m) (CochainComplex.next ℕ (m+1)) (eltS K a)
        (eltS_comp K a ha)).2 ⟨ModuleCat.of ℚ ℚ, 𝟙 _, inferInstance,
          ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.X m) b), ?_⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa [eltS] using hb.symm
    rw [h0]
    rfl

theorem mapS_cocycle {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X (m+1))
    (ha : (K.d (m+1) (m+1+1)).hom a = 0) : (L.d (m+1) (m+1+1)).hom ((φ.f (m+1)).hom a) = 0 := by
  have h := congrArg (fun f => f.hom a) (φ.comm (m+1) (m+1+1))
  change (L.d (m+1) (m+1+1)).hom ((φ.f (m+1)).hom a) = (φ.f (m+1+1)).hom ((K.d (m+1) (m+1+1)).hom a) at h
  rw [h, ha, map_zero]

theorem cycleS_map {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X (m+1))
    (ha : (K.d (m+1) (m+1+1)).hom a = 0) (hφ : (L.d (m+1) (m+1+1)).hom ((φ.f (m+1)).hom a) = 0) :
    (HomologicalComplex.cyclesMap φ (m+1)).hom (cycleS K a ha) = cycleS L ((φ.f (m+1)).hom a) hφ := by
  apply iCyclesS_injective L (m+1)
  have h := congrArg (fun f => f.hom (cycleS K a ha)) (HomologicalComplex.cyclesMap_i φ (m+1))
  change (L.iCycles (m+1)).hom ((HomologicalComplex.cyclesMap φ (m+1)).hom (cycleS K a ha)) =
    (φ.f (m+1)).hom ((K.iCycles (m+1)).hom (cycleS K a ha)) at h
  rw [h, iCycles_cycleS, iCycles_cycleS]

/-- **Naturality of classes**: a cochain map sends the class of a cocycle to the class of its image. -/
theorem clsS_map {L : CochainComplex (ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ L) (a : K.X (m+1))
    (ha : (K.d (m+1) (m+1+1)).hom a = 0) (hφ : (L.d (m+1) (m+1+1)).hom ((φ.f (m+1)).hom a) = 0) :
    (HomologicalComplex.homologyMap φ (m+1)).hom (clsS K a ha) = clsS L ((φ.f (m+1)).hom a) hφ := by
  have h := congrArg (fun f => f.hom (cycleS K a ha)) (HomologicalComplex.homologyπ_naturality φ (m+1))
  change (HomologicalComplex.homologyMap φ (m+1)).hom ((K.homologyπ (m+1)).hom (cycleS K a ha)) =
    (L.homologyπ (m+1)).hom ((HomologicalComplex.cyclesMap φ (m+1)).hom (cycleS K a ha)) at h
  rw [cycleS_map K φ a ha hφ] at h
  exact h

/-- Every class of `H²(K)` is represented by a cocycle. -/
theorem exists_clsS (x : K.homology (m+1)) :
    ∃ (a : K.X (m+1)) (ha : (K.d (m+1) (m+1+1)).hom a = 0), clsS K a ha = x := by
  have hepi : Epi (K.homologyπ (m+1)) := inferInstance
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (m+1))).1 hepi x
  have hd : (K.d (m+1) (m+1+1)).hom ((K.iCycles (m+1)).hom z) = 0 := by
    have h := congrArg (fun m => m.hom z) (K.iCycles_d (m+1) (m+1+1))
    exact h
  refine ⟨(K.iCycles (m+1)).hom z, hd, ?_⟩
  unfold clsS
  congr 1
  apply iCyclesS_injective K (m+1)
  exact iCycles_cycleS K _ hd

end Cls

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
