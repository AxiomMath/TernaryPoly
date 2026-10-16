module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalSupport
open RationalManifoldCompact RationalLocalOrientation

/-- Canonical equality transport between two equal homology degrees. -/
def homologyDegreeChange (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (i j : ℕ) (h : i = j) :
    K.homology i ⟶ K.homology j := eqToHom (congrArg (fun k => K.homology k) h)

/-- Equality transport of homology degrees commutes with the actual homology map. -/
theorem homologyDegreeChange_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (f : K ⟶ L) (i j : ℕ) (h : i = j) :
    homologyDegreeChange K i j h ≫ homologyMap f j =
      homologyMap f i ≫ homologyDegreeChange L i j h := by
  subst j
  simp [homologyDegreeChange]

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)

/-- The actual compact-subset fundamental class in the equal degree required by cap. -/
def capFundamentalClass (K : Compacts B) (a b : ℕ) (hab : a+b = n+2) :
    (supportChains (K : Set B)).homology (a+b) :=
  homologyDegreeChange _ (n+2) (a+b) hab.symm (compactFundamentalClass n e o K K.isCompact)

/-- Degree transport preserves the literal support-restriction identity for fundamental classes. -/
theorem capFundamentalClass_restriction (K L : Compacts B) (hKL : K ≤ L)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportRestriction (L : Set B) (K : Set B) hKL) (a+b)
      (capFundamentalClass n e o L a b hab) = capFundamentalClass n e o K a b hab := by
  unfold capFundamentalClass
  change (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
    homologyMap (supportRestriction (L : Set B) (K : Set B) hKL) (a+b)) _ = _
  rw [homologyDegreeChange_natural]
  change homologyDegreeChange _ (n+2) (a+b) hab.symm
    (homologyMap (supportRestriction (L : Set B) (K : Set B) hKL) (n+2)
      (compactFundamentalClass n e o L L.isCompact)) = _
  erw [compactFundamentalClass_restriction]

/-- Actual local chains, using cancellation supplied by the quotient covering itself. -/
abbrev coveringLocalChains : ChainComplex (ModuleCat.{0} ℚ) ℕ := by
  letI : IsCancelSMul G E := hp.out.isCancelSMul
  exact localChains p hp.out V

variable [IsCancelSMul G E]

/-- Cap against the actual compact-subset fundamental class at a fixed support. -/
def compactCapAt (K : Compacts B) (a b : ℕ) (hab : a+b = n+2) :
    (supportCochains p V (K : Set B)).homology a ⟶ (localChains p hp.out V).homology b :=
  ModuleCat.ofHom ((supportCapHomology p V (K : Set B) a b).flip
    (capFundamentalClass n e o K a b hab))

/-- Enlarging support preserves cap against the actual compact fundamental classes. -/
theorem compactCapAt_enlargement (K L : Compacts B) (hKL : K ≤ L)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) a ≫ compactCapAt p V n e o L a b hab =
      compactCapAt p V n e o K a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change supportCapHomology p V (L : Set B) a b
    (homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) a x)
    (capFundamentalClass n e o L a b hab) = _
  erw [supportCapHomology_enlargement,capFundamentalClass_restriction]
  rfl

omit [IsCancelSMul G E] in
/-- The actual compact-support cap homomorphism, descended from genuine compact-support pairings. -/
def compactCapMap (a b : ℕ) (hab : a+b = n+2) :
    compactCohomology p V a ⟶ (coveringLocalChains p V).homology b := by
  letI : IsCancelSMul G E := hp.out.isCancelSMul
  exact compactCohomologyDesc p V a _ (fun K => compactCapAt p V n e o K a b hab)
    (fun K L hKL => compactCapAt_enlargement p V n e o K L hKL a b hab)

/-- The descended compact-support map is exactly cap against the actual class at every compact support. -/
theorem compactCapMap_classMap (K : Compacts B) (a b : ℕ) (hab : a+b = n+2) :
    compactClassMap p V K a ≫ compactCapMap p V n e o a b hab = compactCapAt p V n e o K a b hab :=
  compactCohomologyDesc_ι p V a _ _ _ K

/-- Exact value of the compact-support cap homomorphism on a represented compact-support class. -/
theorem compactCapMap_apply (K : Compacts B) (a b : ℕ) (hab : a+b = n+2)
    (x : (supportCochains p V (K : Set B)).homology a) :
    compactCapMap p V n e o a b hab (compactClassMap p V K a x) =
      supportCapHomology p V (K : Set B) a b x (capFundamentalClass n e o K a b hab) :=
  congrArg (fun f => f x) (compactCapMap_classMap p V n e o K a b hab)

end TernaryPoly.SingularLocalCompactCap
