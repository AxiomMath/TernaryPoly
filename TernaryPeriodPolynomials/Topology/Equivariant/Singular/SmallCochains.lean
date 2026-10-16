module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallHomotopy
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComplex

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex EquivariantSingularResolution

variable {G : Type} [Group G]

/-- The genuine Hom cochains of an arbitrary representation chain complex. -/
abbrev homCochains (C : ChainComplex (Rep ℚ G) ℕ) (W : Rep.{0} ℚ G) := C.linearYonedaObj ℚ W

/-- Literal precomposition on genuine Hom cochains. -/
def homPullback {C D : ChainComplex (Rep ℚ G) ℕ} (f : C ⟶ D) (W : Rep.{0} ℚ G) :
    homCochains D W ⟶ homCochains C W :=
  (unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((((linearYoneda ℚ (Rep ℚ G)).obj W).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map f).op

/-- The genuine Hom pullback is literally precomposition by the given chain map. -/
theorem homPullback_apply {C D : ChainComplex (Rep ℚ G) ℕ} (f : C ⟶ D) (W : Rep.{0} ℚ G)
    (n : ℕ) (c : D.X n ⟶ W) : (homPullback f W).f n c = f.f n ≫ c := rfl

/-- Contravariant composition of the actual Hom pullback. -/
theorem homPullback_comp {C D K : ChainComplex (Rep ℚ G) ℕ} (f : C ⟶ D) (g : D ⟶ K)
    (W : Rep.{0} ℚ G) : homPullback (f ≫ g) W = homPullback g W ≫ homPullback f W := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

/-- Pullback along an actual equivariant chain homotopy equivalence is a quasi-isomorphism
for every rational coefficient representation, with no dimension restriction. -/
theorem homPullback_quasiIso_of_homotopyEquiv {C D : ChainComplex (Rep ℚ G) ℕ}
    (e : _root_.HomotopyEquiv C D) (W : Rep.{0} ℚ G) : QuasiIso (homPullback e.hom W) := by
  let e' := ((linearYoneda ℚ (Rep ℚ G)).obj W).rightOp.mapHomotopyEquiv e
  exact inferInstanceAs (QuasiIso ((unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map e'.hom.op))

variable (G) (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (𝒰 : SphereOddDegree.OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰)

/-- Genuine Hom cochains on the actual invariant small-chain complex. -/
abbrev smallCochains (W : Rep.{0} ℚ G) := homCochains (smallComplex G E 𝒰 h𝒰) W

/-- Actual restriction of singular equivariant cochains to the small subcomplex. -/
def smallRestriction (W : Rep.{0} ℚ G) :
    EquivariantSingularCohomology.cochains G E W ⟶ smallCochains G E 𝒰 h𝒰 W :=
  homPullback (smallInclusion G E 𝒰 h𝒰) W

/-- The actual small-cochain restriction is a quasi-isomorphism for every rational representation. -/
instance smallRestriction_quasiIso [IsCancelSMul G E] (W : Rep.{0} ℚ G) :
    QuasiIso (smallRestriction G E 𝒰 h𝒰 W) := by
  have h := homPullback_quasiIso_of_homotopyEquiv (smallHomotopyEquiv G E 𝒰 h𝒰) W
  rw [smallHomotopyEquiv_hom] at h
  exact h

/-- The literal small restriction identifies actual equivariant cohomology in every degree. -/
def smallCohomologyIso [IsCancelSMul G E] (W : Rep.{0} ℚ G) (n : ℕ) :
    (EquivariantSingularCohomology.cochains G E W).homology n ≅ (smallCochains G E 𝒰 h𝒰 W).homology n :=
  isoOfQuasiIsoAt (smallRestriction G E 𝒰 h𝒰 W) n

end TernaryPoly.EquivariantSingularSmall
