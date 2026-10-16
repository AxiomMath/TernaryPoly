module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularExactness

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open SymmetricSpaceCovering
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual sheafification functor preserves monomorphisms by its proved left exactness. -/
instance quotientSheafification_preservesMonomorphisms :
    quotientSheafification.PreservesMonomorphisms :=
  inferInstanceAs ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of OrbitSpace))
    (ModuleCat ℝ)).PreservesMonomorphisms)

/-- The actual coefficient-to-singular sheaf map is injective, since the literal presheaf
augmentation is injective and genuine sheafification is left exact. -/
instance coefficientToSingularSheaf_mono : Mono (coefficientToSingularSheaf ρ) := by
  change Mono ((coefficientSheafificationIso ρ).hom ≫
    quotientSheafification.map (coefficientToSingular ρ))
  infer_instance

/-- The actual singular augmentation induces an isomorphism on degree-zero sheaf homology. -/
theorem singularSheafAugmentation_quasiIso_zero : QuasiIsoAt (singularSheafAugmentation ρ) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  have hd : CochainComplex.of.d (singularSheaf ρ) (singularSheafDifferential ρ) 0 1 =
      singularSheafDifferential ρ 0 := CochainComplex.of_d _ _ 0
  simpa only [shortComplexFunctor', sc', singularSheafAugmentation_f_zero,
    CochainComplex.single₀_obj_zero, singularSheafComplex, hd] using
    (show (ShortComplex.mk (coefficientToSingularSheaf ρ) (singularSheafDifferential ρ 0)
      (coefficientToSingularSheaf_closed ρ)).Exact ∧ Mono (coefficientToSingularSheaf ρ) from
        ⟨coefficientToSingularSheaf_exact ρ, inferInstance⟩)

/-- The genuine augmented singular sheaf complex resolves the actual coefficient local system.
This uses actual covering frames, actual singular contraction, and the genuine stalk units. -/
theorem singularSheafAugmentation_quasiIso : QuasiIso (singularSheafAugmentation ρ) := by
  constructor
  intro n
  cases n with
  | zero => exact singularSheafAugmentation_quasiIso_zero ρ
  | succ n =>
    apply (quasiIsoAt_iff_exactAt (singularSheafAugmentation ρ) (n+1) ?_).mpr
      (singularSheafComplex_exactAt ρ n)
    apply (exactAt_iff_isZero_homology _ _).mpr
    exact isZero_single_obj_homology _ _ _ _ (Nat.succ_ne_zero n)

end TernaryPoly.SmoothSingularGlobal
