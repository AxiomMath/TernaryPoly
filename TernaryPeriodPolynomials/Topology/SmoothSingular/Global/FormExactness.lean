module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.StalkExactness
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ClosedForms

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open TopCat.Presheaf
open SmoothCoveringDeRham SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual smooth sheaf differential sequence is exact, by genuine local quotient primitives. -/
theorem formSheaf_exact (n : ℕ) :
    (ShortComplex.mk (formSheafDifferential ρ n) (formSheafDifferential ρ (n+1))
      (formSheafDifferential_squared ρ n)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro q
  change ((ShortComplex.mk (formDifferential ρ n) (formDifferential ρ (n+1))
    (formDifferential_squared ρ n)).map (stalkFunctor (ModuleCat ℝ) q)).Exact
  apply stalk_exact_of_local_lifting
  intro U q hq w hw
  change EquivariantForm ρ (U : Set OrbitSpace) (n+1) at w
  change differential ρ U.isOpen (n+1) w = 0 at hw
  obtain ⟨V, hV, hqV, hVU, hlift⟩ := quotient_local_poincare ρ U.isOpen hq
  obtain ⟨z, hz⟩ := hlift n w hw
  exact ⟨⟨V, hV⟩, hqV, homOfLE hVU, z, hz⟩

/-- The genuine coefficient sheaf is exactly the degree-zero kernel in the smooth sheaf complex. -/
theorem coefficientToFormSheaf_exact :
    (ShortComplex.mk (coefficientToFormSheaf ρ) (formSheafDifferential ρ 0)
      (coefficientToFormSheaf_closed ρ)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro q
  change ((ShortComplex.mk (coefficientToForm ρ) (formDifferential ρ 0)
    (coefficientToForm_closed ρ)).map (stalkFunctor (ModuleCat ℝ) q)).Exact
  apply stalk_exact_of_local_lifting
  intro U q hq w hw
  change EquivariantForm ρ (U : Set OrbitSpace) 0 at w
  change differential ρ U.isOpen 0 w = 0 at hw
  refine ⟨U, hq, 𝟙 U, closedFormCoefficient ρ U.isOpen w hw, ?_⟩
  change coefficientForm ρ U.isOpen (closedFormCoefficient ρ U.isOpen w hw) =
    restrictEquivariant ρ (Subset.refl (U : Set OrbitSpace)) 0 w
  rw [restrictEquivariant_id]
  exact coefficientForm_closedFormCoefficient ρ U.isOpen w hw

/-- Every positive degree of the genuine smooth sheaf complex is exact. -/
theorem formSheafComplex_exactAt (n : ℕ) : (formSheafComplex ρ).ExactAt (n+1) := by
  rw [exactAt_iff' _ n (n+1) ((n+1)+1) (by simp) (by simp)]
  simpa only [sc', shortComplexFunctor', formSheafComplex,
    CochainComplex.of_d (formSheaf ρ) (formSheafDifferential ρ) n,
    CochainComplex.of_d (formSheaf ρ) (formSheafDifferential ρ) (n+1)] using formSheaf_exact ρ n

end TernaryPoly.SmoothSingularGlobal
