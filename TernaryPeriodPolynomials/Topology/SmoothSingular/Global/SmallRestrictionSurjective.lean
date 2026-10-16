module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.PredicateRetraction
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSubdomainCochains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RestrictionSurjective

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization SphereOddDegree
open Set SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰) (W : Rep.{0} ℝ G)

/-- The literal small-singular cochain restriction is surjective in every degree. -/
theorem smallRestriction_surjective (n : ℕ) : Function.Surjective ((smallRestriction G E 𝒰 h𝒰 W).f n) := by
  intro c
  let π : chainRep G E n ⟶ (smallComplex G E 𝒰 h𝒰).X n :=
    predicateGradedProjection G E n (IsSmallSimplex 𝒰) (hP := ⟨small_invariant G E 𝒰 h𝒰 n⟩)
  refine ⟨π ≫ c,?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg c.hom (predicateGradedProjection_leftInverse G E n (IsSmallSimplex 𝒰)
    (hP := ⟨small_invariant G E 𝒰 h𝒰 n⟩) x)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  {V D : Set OrbitSpace} (hV : V ⊆ ⋃ i, U i) (hD : D ⊆ ⋃ i, U i) (hVD : V ⊆ D)

/-- The ordinary real covering cochain restriction is degreewise surjective. -/
theorem coveringCochainRestriction_surjective (n : ℕ) :
    Function.Surjective ((coveringCochainRestriction ρ hVD).f n) :=
  RealBoundaryRestriction.cochainPullback_surjective (coverInclusion hVD)
    (coverInclusion_equivariant hVD) (by intro x y h; exact Subtype.ext (congrArg (fun z : CoverOpen D => z.val) h)) (Rep.of ρ) n

/-- Literal restriction onto actual covering-small cochains is degreewise surjective. -/
theorem coveringSmallRestriction_surjective (n : ℕ) :
    Function.Surjective ((coveringSmallRestriction ρ U hU V hV).f n) :=
  smallRestriction_surjective DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hV)
    (liftedOpenCover_invariant U hU V hV) (Rep.of ρ) n

/-- Genuine subdomain restriction of small cochains is surjective in every degree. -/
theorem smallSubdomainRestriction_surjective (n : ℕ) :
    Function.Surjective ((smallSubdomainRestriction ρ U hU hV hD hVD).f n) := by
  intro c
  obtain ⟨b,hb⟩ := coveringSmallRestriction_surjective ρ U hU hV n c
  obtain ⟨a,ha⟩ := coveringCochainRestriction_surjective ρ hVD n b
  refine ⟨(coveringSmallRestriction ρ U hU D hD).f n a,?_⟩
  have h := congrArg (fun f : coveringCochains ρ D ⟶ coveringSmallCochains ρ U hU V hV =>
    (f.f n).hom a) (smallSubdomainRestriction_square ρ U hU hV hD hVD)
  exact h.symm.trans ((congrArg (((coveringSmallRestriction ρ U hU V hV).f n).hom) ha).trans hb)

end TernaryPoly.SmoothSingularGlobal
