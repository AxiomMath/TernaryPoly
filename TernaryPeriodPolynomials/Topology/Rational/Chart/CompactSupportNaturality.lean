module

public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportIso

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalChartCompactSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology RationalLocalOrientation

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

/-- The compact chart-support comparison commutes with every actual point restriction,
using precisely the existing actual chart-local homology isomorphism. -/
theorem chartSupportHomologyIso_point (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (x : X) (hx : x ∈ K) (k : ℕ) :
    (chartSupportHomologyIso e K hK hKs k).hom ≫
        homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) k =
      homologyMap (supportPointMap K x hx) k ≫ (chartLocalHomologyIso e x (hKs hx) k).hom := by
  let p := homologyMap (supportPointMap ((Subtype.val : e.source → X) ⁻¹' K) ⟨x, hKs hx⟩ hx) k
  let q := homologyMap (supportPointMap ((Subtype.val : e.target → Y) ⁻¹' (e '' K))
    (e.toHomeomorphSourceTarget ⟨x, hKs hx⟩) ⟨x, hx, rfl⟩) k
  let m := homologyMap (chartSupportPairIso e K hKs).hom k
  let v := homologyMap (homeomorphLocalIso e.toHomeomorphSourceTarget ⟨x, hKs hx⟩).hom k
  have hm : m ≫ q = p ≫ v := by
    exact (homologyMap_comp _ _ k).symm.trans
      ((congrArg (fun f => homologyMap f k) (chartSupportPairIso_point e K hKs x hx)).trans
        (homologyMap_comp _ _ k))
  let a := supportExcisionIso K hK.isClosed ⟨e.source, e.open_source⟩ hKs k
  let b := supportExcisionIso (e '' K) (image_isCompact e K hK hKs).isClosed
    ⟨e.target, e.open_target⟩ (image_subset_target e K hKs) k
  let u := pointLocalHomologyIso x ⟨e.source, e.open_source⟩ (hKs hx) k
  let w := pointLocalHomologyIso (e x) ⟨e.target, e.open_target⟩ (e.map_source (hKs hx)) k
  have ht : b.hom ≫ homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) k = q ≫ w.hom :=
    supportExcisionIso_point (e '' K) (image_isCompact e K hK hKs).isClosed
      ⟨e.target, e.open_target⟩ (image_subset_target e K hKs) (e x) ⟨x, hx, rfl⟩ k
  have hs : a.inv ≫ p = homologyMap (supportPointMap K x hx) k ≫ u.inv :=
    supportExcisionIso_inv_point K hK.isClosed ⟨e.source, e.open_source⟩ hKs x hx k
  change (a.inv ≫ m ≫ b.hom) ≫ _ = _ ≫ (u.inv ≫ v ≫ w.hom)
  simp only [Category.assoc]
  erw [ht, ← Category.assoc m q w.hom, hm, Category.assoc,
    ← Category.assoc a.inv p (v ≫ w.hom), hs, Category.assoc]

/-- Elementwise, the comparison sends the local value of a compact-support class
through the actual chart-local isomorphism. -/
theorem chartSupportHomologyIso_point_apply (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (x : X) (hx : x ∈ K) (k : ℕ)
    (c : (relativeChains Kᶜ).homology k) :
    homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) k
        ((chartSupportHomologyIso e K hK hKs k).hom c) =
      (chartLocalHomologyIso e x (hKs hx) k).hom (homologyMap (supportPointMap K x hx) k c) :=
  congrArg (fun f => f c) (chartSupportHomologyIso_point e K hK hKs x hx k)

end TernaryPoly.RationalChartCompactSupport
