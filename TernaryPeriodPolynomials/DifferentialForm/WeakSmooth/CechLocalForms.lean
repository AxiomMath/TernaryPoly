module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechBicomplex

@[expose] public section

/-! Genuine local smooth form families expressed as actual augmented Čech cochains. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
  SmoothSingularGlobal SmoothDeRhamGluing
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)

/-- Each actual finite Čech intersection lies in any one of its entries. -/
theorem cechLocal_entry_subset {k : ℕ} (t : Fin k → ι) (i : Fin k) :
    cechDomain U t ⊆ U (t i) := fun _ hx => mem_iInter.mp hx i

/-- An actual local smooth family gives an actual one-entry Čech cochain by true restriction. -/
def cechLocalFamily (k : ℕ) (v : ∀ i, EquivariantForm ρ (U i) k) : FormCechTerms ρ U k 1 :=
  fun t => restrictEquivariant ρ (cechLocal_entry_subset U t 0) k (v (t 0))

/-- Its actual covering representative on a one-entry intersection is the original local value. -/
theorem cechLocalFamily_value (k : ℕ) (v : ∀ i, EquivariantForm ρ (U i) k)
    (t : Fin 1 → ι) (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    ((cechLocalFamily ρ U k v t).val : RawForm Coordinates F k) x = (v (t 0)).val.val x :=
  restrictEquivariant_apply ρ (cechLocal_entry_subset U t 0) (v (t 0)) hx

/-- The actual two-entry Čech differential of a local smooth family is its actual overlap
restriction difference, with the exact alternating sign convention. -/
theorem cechLocalFamily_difference (k : ℕ) (v : ∀ i, EquivariantForm ρ (U i) k)
    (t : Fin 2 → ι) :
    formCechD ρ U k 1 (cechLocalFamily ρ U k v) t =
      restrictEquivariant ρ (cechLocal_entry_subset U t 1) k (v (t 1)) -
        restrictEquivariant ρ (cechLocal_entry_subset U t 0) k (v (t 0)) := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  apply (formCechD_value ρ U k 1 (cechLocalFamily ρ U k v) t x hx).trans
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero]
  rw [cechLocalFamily_value ρ U k v (t ∘ (0 : Fin 2).succAbove) x
    (liftedDomain_mono (cechDomain_select_subset U (0 : Fin 2).succAbove t) hx),
    cechLocalFamily_value ρ U k v (t ∘ (Fin.succ (0 : Fin 1)).succAbove) x
    (liftedDomain_mono (cechDomain_select_subset U (Fin.succ (0 : Fin 1)).succAbove t) hx)]
  change (1 : ℤ) • (v (t 1)).val.val x + (-1 : ℤ) • (v (t 0)).val.val x =
    (restrictEquivariant ρ (cechLocal_entry_subset U t 1) k (v (t 1))).val.val x -
      (restrictEquivariant ρ (cechLocal_entry_subset U t 0) k (v (t 0))).val.val x
  rw [restrictEquivariant_apply ρ _ _ hx, restrictEquivariant_apply ρ _ _ hx,
    one_zsmul, neg_one_zsmul, sub_eq_add_neg]

/-- The actual empty-entry augmentation restricts the original global form to each entry. -/
theorem cechEmpty_d_restriction (k : ℕ) (omega : EquivariantForm ρ univ k) (t : Fin 1 → ι) :
    formCechD ρ U k 0 (formCechEmptyEmbed ρ U k omega) t =
      restrictEquivariant ρ (subset_univ _) k omega := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  apply (formCechD_value ρ U k 0 (formCechEmptyEmbed ρ U k omega) t x hx).trans
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_zsmul]
  exact (restrictEquivariant_apply ρ (subset_univ _) omega
    (liftedDomain_mono (cechDomain_select_subset U (0 : Fin 1).succAbove t) hx)).trans
      (restrictEquivariant_apply ρ (subset_univ _) omega hx).symm

/-- Genuine local smooth primitives give the exact actual augmented Čech equation for their
true exterior differentials. -/
theorem cechLocalFamily_primitive (hU : ∀ i, IsOpen (U i))
    (omega : EquivariantForm ρ univ 2) (v : ∀ i, EquivariantForm ρ (U i) 1)
    (hv : ∀ i, differential ρ (hU i) 1 (v i) = restrictEquivariant ρ (subset_univ _) 2 omega) :
    formCechColumnD ρ U hU 1 1 (cechLocalFamily ρ U 1 v) =
      formCechD ρ U 2 0 (formCechEmptyEmbed ρ U 2 omega) := by
  funext t
  apply (restrictEquivariant_d ρ (hU (t 0)) (cechDomain_isOpen U hU t)
    (cechLocal_entry_subset U t 0) (v (t 0))).symm.trans
  apply (congrArg (restrictEquivariant ρ (cechLocal_entry_subset U t 0) 2) (hv (t 0))).trans
  apply (restrictEquivariant_trans (cechLocal_entry_subset U t 0) (subset_univ _) 2 omega).trans
  exact (cechEmpty_d_restriction ρ U 2 omega t).symm

end TernaryPoly.PolynomialFormWeakSmooth
