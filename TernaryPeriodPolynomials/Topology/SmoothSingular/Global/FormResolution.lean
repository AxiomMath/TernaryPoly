module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormExactness

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The genuine coefficient-to-smooth sheaf augmentation is injective. -/
instance coefficientToFormSheaf_mono : Mono (coefficientToFormSheaf ρ) := by
  have : ∀ U, Mono ((coefficientToForm ρ).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).mpr (coefficientForm_injective ρ U.unop.isOpen)
  have : Mono (coefficientToForm ρ) := NatTrans.mono_of_mono_app _
  have : Mono (coefficientToFormSheaf ρ).hom := (show Mono (coefficientToForm ρ) from inferInstance)
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ (coefficientToFormSheaf ρ)

/-- The actual coefficient augmentation identifies degree-zero homology of the smooth sheaf complex. -/
theorem formSheafAugmentation_quasiIso_zero : QuasiIsoAt (formSheafAugmentation ρ) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  have hd : CochainComplex.of.d (formSheaf ρ) (formSheafDifferential ρ) 0 1 =
      formSheafDifferential ρ 0 := CochainComplex.of_d _ _ 0
  simpa only [shortComplexFunctor', sc', formSheafAugmentation_f_zero,
    CochainComplex.single₀_obj_zero, formSheafComplex, hd] using
    (show (ShortComplex.mk (coefficientToFormSheaf ρ) (formSheafDifferential ρ 0)
      (coefficientToFormSheaf_closed ρ)).Exact ∧ Mono (coefficientToFormSheaf ρ) from
        ⟨coefficientToFormSheaf_exact ρ, inferInstance⟩)

/-- The genuine augmented smooth sheaf complex resolves the actual coefficient local system.
The proof uses the actual quotient Poincaré lemma and actual locally constant coefficient sections. -/
theorem formSheafAugmentation_quasiIso : QuasiIso (formSheafAugmentation ρ) := by
  constructor
  intro n
  cases n with
  | zero => exact formSheafAugmentation_quasiIso_zero ρ
  | succ n =>
    apply (quasiIsoAt_iff_exactAt (formSheafAugmentation ρ) (n+1) ?_).mpr
      (formSheafComplex_exactAt ρ n)
    apply (exactAt_iff_isZero_homology _ _).mpr
    exact isZero_single_obj_homology _ _ _ _ (Nat.succ_ne_zero n)

end TernaryPoly.SmoothSingularGlobal
