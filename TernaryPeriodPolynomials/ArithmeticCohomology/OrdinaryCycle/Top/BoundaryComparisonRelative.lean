module

public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionSurjective
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainHomotopy
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionProjective

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution
open SingularCoverNaturality SingularBoundaryRestriction

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
  (hinj : Function.Injective F)

/-- The literal inclusion of singular chains has an equivariant retraction in every degree,
obtained by extension by zero on the actual singular-simplex image. -/
def inclusionRetraction (n : ℕ) : (equivariantChains G E').X n ⟶
    (equivariantChains G E).X n :=
  cochainExtension F hF hinj (chainRep G E n) n (𝟙 _)

/-- The degree retraction is a left inverse to the literal singular inclusion. -/
theorem inclusionRetraction_identity (n : ℕ) :
    (chainMap F hF).f n ≫ inclusionRetraction F hF hinj n = 𝟙 _ :=
  cochainPullback_extension F hF hinj (chainRep G E n) n (𝟙 _)

include hinj in
/-- Actual injective equivariant maps induce monomorphisms on singular chains. -/
theorem inclusion_mono : Mono (chainMap F hF) := by
  apply mono_of_mono_f
  intro n
  exact mono_of_mono_fac (inclusionRetraction_identity F hF hinj n)

/-- The actual subspace, ambient and relative representation chains form the cokernel sequence. -/
def relativeSequence : ShortComplex (ChainComplex (Rep.{0} ℚ G) ℕ) :=
  ShortComplex.mk (chainMap F hF) (cokernel.π (chainMap F hF))
    (cokernel.condition (chainMap F hF))

include hinj in
/-- Exactness holds for the genuine singular inclusion and its genuine cokernel. -/
theorem relativeSequence_shortExact : (relativeSequence F hF).ShortExact where
  exact := (relativeSequence F hF).exact_of_g_is_cokernel (cokernelIsCokernel _)
  mono_f := inclusion_mono F hF hinj
  epi_g := by change Epi (cokernel.π (chainMap F hF)); infer_instance

/-- The complementary projection kills the actual subspace chains. -/
theorem complementaryProjection_condition (n : ℕ) :
    (chainMap F hF).f n ≫ (𝟙 _ - inclusionRetraction F hF hinj n ≫ (chainMap F hF).f n) = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    inclusionRetraction_identity, Category.id_comp, sub_self]

/-- A graded section of the actual relative-chain projection. It is not a chain map. -/
def relativeProjectionSection (n : ℕ) : (cokernel (chainMap F hF)).X n ⟶
    (equivariantChains G E').X n :=
  RelativeChainHomotopy.degreeDesc (chainMap F hF) n
    (𝟙 _ - inclusionRetraction F hF hinj n ≫ (chainMap F hF).f n)
    (complementaryProjection_condition F hF hinj n)

/-- The graded section is a right inverse of the actual relative-chain projection. -/
theorem relativeProjectionSection_identity (n : ℕ) :
    relativeProjectionSection F hF hinj n ≫ (cokernel.π (chainMap F hF)).f n = 𝟙 _ := by
  apply (cancel_epi ((cokernel.π (chainMap F hF)).f n)).mp
  rw [← Category.assoc]
  change ((cokernel.π (chainMap F hF)).f n ≫
    RelativeChainHomotopy.degreeDesc (chainMap F hF) n _ _) ≫ _ = _
  rw [RelativeChainHomotopy.projection_degreeDesc, Preadditive.sub_comp,
    Category.id_comp, Category.assoc]
  have h := HomologicalComplex.congr_hom (cokernel.condition (chainMap F hF)) n
  change (chainMap F hF).f n ≫ (cokernel.π (chainMap F hF)).f n = 0 at h
  rw [h, comp_zero, sub_zero, Category.comp_id]

include hinj in
/-- Relative singular chains are projective degreewise when the actual ambient action is free. -/
theorem relativeDegree_projective [IsCancelSMul G E'] (n : ℕ) :
    Projective ((cokernel (chainMap F hF)).X n) where
  factors {A B} u e _ := by
    let : Projective ((equivariantChains G E').X n) := chainRep_projective G E' n
    obtain ⟨l, hl⟩ := Projective.factors ((cokernel.π (chainMap F hF)).f n ≫ u) e
    refine ⟨relativeProjectionSection F hF hinj n ≫ l, ?_⟩
    rw [Category.assoc, hl, ← Category.assoc, relativeProjectionSection_identity,
      Category.id_comp]

end TernaryPoly.OrdinaryTopBoundaryComparison
