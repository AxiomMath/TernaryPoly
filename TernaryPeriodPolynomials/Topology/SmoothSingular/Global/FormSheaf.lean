module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormGluing

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Actual equivariant smooth forms satisfy the full open-cover sheaf condition. -/
theorem formPresheaf_isSheaf (n : ℕ) : (formPresheaf ρ n).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U w hw
  refine ⟨gluedForm ρ U n w hw, ?_, ?_⟩
  · intro i
    exact gluedForm_restrict ρ U n w hw i
  · intro z hz
    exact gluedForm_unique ρ U n w hw z hz

/-- The actual real smooth equivariant-form sheaf on the quotient. -/
def formSheaf (n : ℕ) : (TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ) :=
  ⟨formPresheaf ρ n, formPresheaf_isSheaf ρ n⟩

/-- The literal exterior derivative, between genuine sheaves. -/
def formSheafDifferential (n : ℕ) : formSheaf ρ n ⟶ formSheaf ρ (n+1) :=
  ⟨formDifferential ρ n⟩

/-- The differential squares to zero as a sheaf morphism. -/
theorem formSheafDifferential_squared (n : ℕ) :
    formSheafDifferential ρ n ≫ formSheafDifferential ρ (n+1) = 0 := by
  apply ObjectProperty.hom_ext
  exact formDifferential_squared ρ n

/-- The genuine smooth equivariant de Rham sheaf complex on the arithmetic quotient. -/
def formSheafComplex : CochainComplex ((TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ)) ℕ :=
  CochainComplex.of (formSheaf ρ) (formSheafDifferential ρ) (formSheafDifferential_squared ρ)

end TernaryPoly.SmoothSingularGlobal
