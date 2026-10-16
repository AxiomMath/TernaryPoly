module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityOpenProperty
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Homeomorph
public import TernaryPeriodPolynomials.Topology.Euclidean.BoxGluing

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation
open EquivariantSingularSmall

variable {B B' : TopCat.{0}}

/-- The identity coverings of genuinely homeomorphic bases form a literal covering homeomorphism. -/
def identityCoverHomeomorph (h : B ≃ₜ B') : CoverHomeomorph (G := Unit) (𝟙 B) (𝟙 B') where
  total := h
  base := h
  square := by simp
  equivariant _ _ := rfl

variable [T2Space B] {H : Type} [TopologicalSpace H] [ChartedSpace H B]
  (V : ModuleCat.{0} ℚ) (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- Actual cap duality and upper cohomology vanishing hold on every genuine Euclidean model,
for arbitrary rational modules and every genuine orientation. -/
theorem duality_homeomorphicEuclidean (h : B ≃ₜ EuclideanSpace ℝ (Fin (n+2))) :
    Duality (𝟙 B) (constantRep V) n e := by
  constructor
  · intro o a b hab
    exact SingularLocalCapHomeomorph.homeomorphicEuclidean_isIso V n e h o a b hab
  · intro a ha
    exact (EuclideanCompactCap.compactCohomology_isZero n V a (by omega)).of_iso
      (SingularLocalCapHomeomorph.compactCohomologyIso h V a).symm

local instance euclideanAction (n : ℕ) : MulAction Unit (TopCat.of (EuclideanSpace ℝ (Fin (n+2)))) :=
  identityAction _
local instance euclideanContinuousAction (n : ℕ) :
    ContinuousConstSMul Unit (TopCat.of (EuclideanSpace ℝ (Fin (n+2)))) := identityContinuousAction _
local instance euclideanCoverFact (n : ℕ) :
    Fact (IsQuotientCoveringMap (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) Unit) := ⟨identityCover _⟩

/-- Every actual Euclidean open satisfies the full open-set induction property. -/
theorem euclidean_openDuality (s : Set (EuclideanSpace ℝ (Fin (n+2)))) (hs : IsOpen s) :
    OpenDuality (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) (constantRep V) n
      (Homeomorph.refl _) s := by
  apply EuclideanBoxBasis.euclidean_open_induction (n+2)
    (OpenDuality (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) (constantRep V) n (Homeomorph.refl _))
    (openDuality_empty (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) (constantRep V) n (Homeomorph.refl _)) ?_
    (openDuality_union (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) (constantRep V) n (Homeomorph.refl _))
    (openDuality_iUnion (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin (n+2))))) (constantRep V) n (Homeomorph.refl _)) s hs
  intro A _ hA cs
  let := cs
  obtain ⟨h⟩ := hA
  let : MulAction Unit (TopCat.of A) := identityAction _
  let : ContinuousConstSMul Unit (TopCat.of A) := identityContinuousAction _
  let : Fact (IsQuotientCoveringMap (𝟙 (TopCat.of A)) Unit) := ⟨identityCover _⟩
  change Duality (𝟙 (TopCat.of A)) (constantRep V) n (Homeomorph.refl _)
  exact duality_homeomorphicEuclidean V n (Homeomorph.refl _) h

/-- Constant-coefficient duality on any space homeomorphic to an actual Euclidean open. -/
theorem duality_homeomorphicEuclideanOpen (s : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hs : IsOpen s) (h : B ≃ₜ s) : Duality (𝟙 B) (constantRep V) n e := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin (n+2))) s :=
    TopologicalSpace.Opens.instChartedSpace (⟨s,hs⟩ : Opens (EuclideanSpace ℝ (Fin (n+2))))
  let : MulAction Unit (TopCat.of s) := identityAction _
  let : ContinuousConstSMul Unit (TopCat.of s) := identityContinuousAction _
  let : Fact (IsQuotientCoveringMap (𝟙 (TopCat.of s)) Unit) := ⟨identityCover _⟩
  have hd := euclidean_openDuality V n s hs inferInstance
  change Duality (𝟙 (TopCat.of s)) (constantRep V) n (Homeomorph.refl _) at hd
  exact duality_homeomorph (𝟙 (TopCat.of s)) (constantRep V) n (Homeomorph.refl _) (𝟙 B) e
    (identityCoverHomeomorph h.symm) hd

end TernaryPoly.SingularLocalCompactDuality
