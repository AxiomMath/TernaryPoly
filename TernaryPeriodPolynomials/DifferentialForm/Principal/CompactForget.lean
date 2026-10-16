module

public import TernaryPeriodPolynomials.DifferentialForm.Principal.CoverHomeomorph
public import TernaryPeriodPolynomials.Topology.CoverGroup.GroupReindexCompactForget

@[expose] public section


/-! The original deck-group model and the principal-six model have the same actual
compact-support-forgetting map, under genuine ordinary and compact cohomology isomorphisms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormPrincipalCover
open CategoryTheory Limits HomologicalComplex PolynomialCoefficientMetric SymmetricSpacePositive
  SymmetricSpaceCovering SymmetricSpaceBordifiedCohomology IntegralGL3Congruence
  SingularLocalCoefficient SingularLocalSupport SingularLocalCompactDuality
  CompactInteriorRelativeBoundary

local instance originalCoverFact : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩
local instance interiorDeckFact : Fact (IsQuotientCoveringMap interiorCover DeckGroup) :=
  ⟨interiorDeckQuotientCovering⟩
local instance interiorPrincipalFact : Fact (IsQuotientCoveringMap interiorCover principalSix) :=
  ⟨interiorCover_isQuotientCovering⟩

/-- The actual group equivalence preserves the literal action on positive forms. -/
theorem deckActionCompatible (g : DeckGroup) (x : TopCat.of Space) :
    g • x = deckPrincipalEquiv g • x := rfl

/-- The local-system cochain pullback along the actual quotient homeomorphism is invertible. -/
def deckOrdinaryIso (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    (localCochains interiorCover interiorDeckQuotientCovering (Rep.res deckPrincipal V)).homology k ≅
      (localCochains singularCoveringProjection quotientProjection_quotientCovering
        (Rep.res deckPrincipal V)).homology k := by
  have := coveringCochainMap_isIso arithmeticCoverHomeomorph (Rep.res deckPrincipal V)
  exact (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) k).mapIso
    (asIso (coveringCochainMap arithmeticCoverHomeomorph (Rep.res deckPrincipal V)))

/-- Genuine ordinary local cohomology agrees in the two exact group presentations. -/
def principalOrdinaryIso (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    (localCochains interiorCover interiorCover_isQuotientCovering V).homology k ≅
      (localCochains singularCoveringProjection quotientProjection_quotientCovering
        (Rep.res deckPrincipal V)).homology k :=
  CoverGroupReindex.ordinaryIso deckPrincipalEquiv interiorCover
    deckActionCompatible V k ≪≫ deckOrdinaryIso V k

/-- Genuine compact local cohomology agrees, including its actual support kernels and colimit. -/
def principalCompactIso (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    compactCohomology interiorCover V k ≅
      compactCohomology singularCoveringProjection (Rep.res deckPrincipal V) k :=
  CoverGroupReindex.compactIso deckPrincipalEquiv interiorCover
    deckActionCompatible V k ≪≫
      coveringCompactIso arithmeticCoverHomeomorph (Rep.res deckPrincipal V) k

/-- The square retains the literal compactForget maps on both sides. -/
theorem principalCompactIso_forget (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    (principalCompactIso V k).hom ≫ compactForget singularCoveringProjection (Rep.res deckPrincipal V) k =
      compactForget interiorCover V k ≫ (principalOrdinaryIso V k).hom := by
  let C := CoverGroupReindex.compactIso deckPrincipalEquiv interiorCover deckActionCompatible V k
  let O := CoverGroupReindex.ordinaryIso deckPrincipalEquiv interiorCover deckActionCompatible V k
  let D := coveringCompactIso arithmeticCoverHomeomorph (Rep.res deckPrincipal V) k
  let F := homologyMap (coveringCochainMap arithmeticCoverHomeomorph (Rep.res deckPrincipal V)) k
  change (C.hom ≫ D.hom) ≫ compactForget singularCoveringProjection (Rep.res deckPrincipal V) k =
    compactForget interiorCover V k ≫ (O.hom ≫ F)
  calc
    _ = C.hom ≫ (D.hom ≫ compactForget singularCoveringProjection (Rep.res deckPrincipal V) k) :=
      Category.assoc _ _ _
    _ = C.hom ≫ (compactForget interiorCover (Rep.res deckPrincipal V) k ≫ F) :=
      congrArg (C.hom ≫ ·) (coveringCompactIso_forget singularCoveringProjection
        (Rep.res deckPrincipal V) interiorCover arithmeticCoverHomeomorph k)
    _ = (C.hom ≫ compactForget interiorCover (Rep.res deckPrincipal V) k) ≫ F :=
      (Category.assoc _ _ _).symm
    _ = (compactForget interiorCover V k ≫ O.hom) ≫ F :=
      congrArg (· ≫ F) (CoverGroupReindex.compactIso_forget deckPrincipalEquiv interiorCover
        deckActionCompatible V k)
    _ = _ := Category.assoc _ _ _

/-- Vanishing of the actual compact-to-ordinary map is independent of these two group presentations. -/
theorem principalCompactForget_eq_zero_iff (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    compactForget singularCoveringProjection (Rep.res deckPrincipal V) k = 0 ↔
      compactForget interiorCover V k = 0 := by
  constructor
  · intro hz
    apply (cancel_mono (principalOrdinaryIso V k).hom).mp
    rw [zero_comp, ← principalCompactIso_forget, hz, comp_zero]
  · intro hz
    apply (cancel_epi (principalCompactIso V k).hom).mp
    rw [comp_zero, principalCompactIso_forget, hz, zero_comp]

/-- The exact degree-two covering-group bridge required by the positive inner gate. -/
theorem principal_compactForget_zero (V : Rep.{0} ℚ principalSix)
    (h : compactForget singularCoveringProjection (Rep.res deckPrincipal V) 2 = 0) :
    compactForget interiorCover V 2 = 0 :=
  (principalCompactForget_eq_zero_iff V 2).mp h

end TernaryPoly.PolynomialFormPrincipalCover
