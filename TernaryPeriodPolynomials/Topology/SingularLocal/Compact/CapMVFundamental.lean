module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVConnectingPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVRelativeLocalization
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapOpen

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalSupport SingularLocalCompactCap RationalManifoldCompact RationalLocalOrientation
open SphereOddDegree

/-- Reindexing a literal cycle represents exactly the canonical homology degree transport. -/
theorem castChainCycle_class (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) {i j : ℕ} (h : i = j)
    (c : Homology.Cycles (C.sc' (i+1) i (i-1))) :
    Descent.chainClass C j (castChainCycle C h c) =
      homologyDegreeChange C i j h (Descent.chainClass C i c) := by
  subst j
  rfl

/-- Canonical homology degree transports compose as their literal degree equalities do. -/
theorem homologyDegreeChange_trans (C : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (i j k : ℕ) (hij : i = j) (hjk : j = k) :
    homologyDegreeChange C i j hij ≫ homologyDegreeChange C j k hjk =
      homologyDegreeChange C i k (hij.trans hjk) := by
  subst j
  subst k
  rfl

variable {B : TopCat.{0}} {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)

/-- The actual compact fundamental class is unchanged under the canonical equality of cap degrees. -/
theorem capFundamentalClass_change (K : Compacts B) (a b a' b' : ℕ)
    (hab : a+b = n+2) (hab' : a'+b' = n+2) (h : a+b = a'+b') :
    homologyDegreeChange (supportChains (K : Set B)) (a+b) (a'+b') h
      (capFundamentalClass n e o K a b hab) = capFundamentalClass n e o K a' b' hab' := by
  unfold capFundamentalClass
  exact congrArg (fun f => f (compactFundamentalClass n e o K K.isCompact))
    (homologyDegreeChange_trans _ _ _ _ hab.symm h)

/-- A representative of an actual compact fundamental class remains such a representative
after the scalar degree transport occurring in the cap Leibniz rule. -/
theorem fundamental_representative_cast (K : Compacts B) (C : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (q : C ⟶ supportChains (K : Set B)) (a b : ℕ) (hab : a+(b+1) = n+2)
    (c : Homology.Cycles (C.sc' (a+b+2) (a+b+1) (a+b)))
    (hc : homologyMap q (a+b+1) (Descent.chainClass C (a+b+1) c) = capFundamentalClass n e o K a (b+1) hab) :
    homologyMap q (a+1+b)
      (Descent.chainClass C (a+1+b) (castChainCycle C (by omega) c)) =
      capFundamentalClass n e o K (a+1) b (by omega) := by
  rw [castChainCycle_class]
  have ht := congrArg (fun f => f (Descent.chainClass C (a+b+1) c))
    (homologyDegreeChange_natural q (a+b+1) (a+1+b) (by omega))
  change homologyMap q (a+1+b) (homologyDegreeChange C (a+b+1) (a+1+b) _ _) =
    homologyDegreeChange (supportChains (K : Set B)) (a+b+1) (a+1+b) _ _ at ht
  exact ht.trans ((congrArg (homologyDegreeChange (supportChains (K : Set B))
    (a+b+1) (a+1+b) (by omega)) hc).trans
      (capFundamentalClass_change n e o K a (b+1) (a+1) b hab (by omega) (by omega)))

/-- Canonical localization of a genuine relative-small representative of an ambient compact
fundamental class gives precisely the canonical open compact fundamental class. -/
theorem relativeLocalizeScalar_fundamental (A K : Compacts B) (hKA : K ≤ A)
    (U : Opens B) [ChartedSpace H U] (hKU : (K : Set B) ⊆ U) (𝒰 : OpenCoverData B)
    (href : ∀ k (σ : singularSimplices B k), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover (K : Set B) K.isCompact.isClosed U hKU) σ)
    (a b : ℕ) (hab : a+b = n+2)
    (c : (cokernel (smallPush (sInclusion (A : Set B)ᶜ) 𝒰)).homology (a+b))
    (hc : homologyMap (relativeSmallMap (A : Set B)ᶜ 𝒰) (a+b) c = capFundamentalClass n e o A a b hab) :
    homologyMap (relativeLocalizeScalar (A : Set B)ᶜ (K : Set B)
      (fun _ hx hk => hx (hKA hk)) K.isCompact.isClosed U hKU 𝒰 href) (a+b) c =
      capFundamentalClass (B := TopCat.of U) n e (openOrientation n e o U)
        (compactWithinOpen U K hKU) a b hab := by
  have := supportExcisionMap_quasiIso (K : Set B) K.isCompact.isClosed U hKU
  apply (ModuleCat.mono_iff_injective (homologyMap (supportExcisionMap (K : Set B) U) (a+b))).mp inferInstance
  rw [capFundamentalClass_open n e o U (openOrientation n e o U)
    (openOrientation_compatible n e o U) K hKU a b hab]
  have hr := congrArg (fun f => homologyMap f (a+b))
    (relativeLocalizeScalar_excision (A : Set B)ᶜ (K : Set B) (fun _ hx hk => hx (hKA hk))
      K.isCompact.isClosed U hKU 𝒰 href)
  rw [homologyMap_comp,homologyMap_comp] at hr
  have hh := congrArg (fun f => f c) hr
  change homologyMap (supportExcisionMap (K : Set B) U) (a+b) _ =
    homologyMap (supportRestriction (A : Set B) (K : Set B) hKA) (a+b)
      (homologyMap (relativeSmallMap (A : Set B)ᶜ 𝒰) (a+b) c) at hh
  exact hh.trans ((congrArg (homologyMap (supportRestriction (A : Set B) (K : Set B) hKA) (a+b)) hc).trans
    (capFundamentalClass_restriction n e o K A hKA a b hab))

end TernaryPoly.SingularLocalCompactCapMV
