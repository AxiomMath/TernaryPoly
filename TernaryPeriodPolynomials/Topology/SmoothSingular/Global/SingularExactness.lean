module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularZero
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SheafificationStalks

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Opposite TopologicalSpace Set HomologicalComplex
open TopCat.Presheaf SymmetricSpaceCovering
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual singular sheaf differential sequence is exact, by genuine local covering
primitives and the actual sheafification unit on stalks. -/
theorem singularSheaf_exact (n : ℕ) :
    (ShortComplex.mk (singularSheafDifferential ρ n) (singularSheafDifferential ρ (n+1))
      (singularSheafDifferential_squared ρ n)).Exact := by
  change ((ShortComplex.mk (singularPresheafDifferential ρ n)
    (singularPresheafDifferential ρ (n+1)) (singularPresheafDifferential_squared ρ n)).map
      quotientSheafification).Exact
  apply sheafification_exact_of_stalk_exact
  apply stalk_exact_of_local_lifting
  intro U q hq w hw
  change (coveringCochains ρ (U : Set OrbitSpace)).X (n+1) at w
  change (coveringCochains ρ (U : Set OrbitSpace)).d (n+1) ((n+1)+1) w = 0 at hw
  obtain ⟨V, hqV, hVU, z, hz⟩ := singular_local_lifting ρ U.isOpen hq n w hw
  exact ⟨V, hqV, homOfLE hVU, z, hz⟩

/-- The genuine sheafified singular augmentation is exact in degree zero. -/
theorem sheafifiedCoefficientToSingular_exact :
    ((ShortComplex.mk (coefficientToSingular ρ) (singularPresheafDifferential ρ 0)
      (coefficientToSingular_closed ρ)).map quotientSheafification).Exact := by
  apply sheafification_exact_of_stalk_exact
  apply stalk_exact_of_local_lifting
  intro U q hq w hw
  change (coveringCochains ρ (U : Set OrbitSpace)).X 0 at w
  change (coveringCochains ρ (U : Set OrbitSpace)).d 0 1 w = 0 at hw
  obtain ⟨V, hqV, hVU, z, hz⟩ := singular_zero_local_lifting ρ U.isOpen hq w hw
  exact ⟨V, hqV, homOfLE hVU, z, hz⟩

/-- The actual coefficient sheaf is exactly the kernel of degree-zero singular coboundary. -/
theorem coefficientToSingularSheaf_exact :
    (ShortComplex.mk (coefficientToSingularSheaf ρ) (singularSheafDifferential ρ 0)
      (coefficientToSingularSheaf_closed ρ)).Exact := by
  let e : (ShortComplex.mk (coefficientToSingularSheaf ρ) (singularSheafDifferential ρ 0)
      (coefficientToSingularSheaf_closed ρ)) ≅
      ((ShortComplex.mk (coefficientToSingular ρ) (singularPresheafDifferential ρ 0)
        (coefficientToSingular_closed ρ)).map quotientSheafification) :=
    ShortComplex.isoMk (coefficientSheafificationIso ρ) (Iso.refl _) (Iso.refl _)
      (by
        change coefficientToSingularSheaf ρ = coefficientToSingularSheaf ρ ≫ 𝟙 _
        exact (Category.comp_id _).symm) (by
        change 𝟙 _ ≫ singularSheafDifferential ρ 0 = singularSheafDifferential ρ 0 ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact ShortComplex.exact_of_iso e.symm (sheafifiedCoefficientToSingular_exact ρ)

/-- The true singular sheaf complex is exact in every positive degree. -/
theorem singularSheafComplex_exactAt (n : ℕ) : (singularSheafComplex ρ).ExactAt (n+1) := by
  rw [exactAt_iff' _ n (n+1) ((n+1)+1) (by simp) (by simp)]
  simpa only [sc', shortComplexFunctor', singularSheafComplex,
    CochainComplex.of_d (singularSheaf ρ) (singularSheafDifferential ρ) n,
    CochainComplex.of_d (singularSheaf ρ) (singularSheafDifferential ρ) (n+1)] using singularSheaf_exact ρ n

end TernaryPoly.SmoothSingularGlobal
