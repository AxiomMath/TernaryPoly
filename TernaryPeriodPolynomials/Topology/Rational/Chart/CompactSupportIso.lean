module

public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportPairs

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalChartCompactSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology RationalLocalOrientation

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

omit [T2Space X] in
/-- The actual support-excision isomorphism has the literal excision homology map. -/
theorem supportExcisionIso_hom (K : Set X) (hK : IsClosed K) (V : Opens X)
    (hKV : K ⊆ V) (k : ℕ) :
    (supportExcisionIso K hK V hKV k).hom = homologyMap (supportExcisionMap K V) k := rfl

/-- The source and target support-excision maps and actual chart pair homeomorphism
compute compact-support homology in every degree. -/
def chartSupportHomologyIso (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (k : ℕ) :
    (relativeChains Kᶜ).homology k ≅ (relativeChains (e '' K)ᶜ).homology k :=
  (supportExcisionIso K hK.isClosed ⟨e.source, e.open_source⟩ hKs k).symm ≪≫
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso
      (chartSupportPairIso e K hKs) ≪≫
        supportExcisionIso (e '' K) (image_isCompact e K hK hKs).isClosed
          ⟨e.target, e.open_target⟩ (image_subset_target e K hKs) k

/-- After source excision, the comparison is the actual chart homeomorphism followed
by target excision; this records the literal defining comparison square. -/
theorem chartSupportHomologyIso_excision (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (k : ℕ) :
    homologyMap (supportExcisionMap K e.source) k ≫ (chartSupportHomologyIso e K hK hKs k).hom =
      homologyMap ((chartSupportPairIso e K hKs).hom ≫ supportExcisionMap (e '' K) e.target) k := by
  change (supportExcisionIso K hK.isClosed ⟨e.source, e.open_source⟩ hKs k).hom ≫ _ = _
  dsimp only [chartSupportHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc, homologyMap_comp]
  rfl

/-- Closed-support excision commutes on homology with the actual point-excision isomorphism. -/
theorem supportExcisionIso_point (K : Set X) (hK : IsClosed K) (V : Opens X)
    (hKV : K ⊆ V) (x : X) (hx : x ∈ K) (k : ℕ) :
    (supportExcisionIso K hK V hKV k).hom ≫ homologyMap (supportPointMap K x hx) k =
      homologyMap (supportPointMap ((Subtype.val : V → X) ⁻¹' K) ⟨x, hKV hx⟩ hx) k ≫
        (pointLocalHomologyIso x V (hKV hx) k).hom := by
  rw [supportExcisionIso_hom, pointLocalHomologyIso_hom, ← homologyMap_comp, ← homologyMap_comp]
  exact congrArg (fun f => homologyMap f k) (supportExcisionMap_point K V x hx (hKV hx))

/-- The inverse support-excision map intertwines point restriction with inverse point excision. -/
theorem supportExcisionIso_inv_point (K : Set X) (hK : IsClosed K) (V : Opens X)
    (hKV : K ⊆ V) (x : X) (hx : x ∈ K) (k : ℕ) :
    (supportExcisionIso K hK V hKV k).inv ≫
        homologyMap (supportPointMap ((Subtype.val : V → X) ⁻¹' K) ⟨x, hKV hx⟩ hx) k =
      homologyMap (supportPointMap K x hx) k ≫ (pointLocalHomologyIso x V (hKV hx) k).inv := by
  rw [← cancel_epi (supportExcisionIso K hK V hKV k).hom,
    ← cancel_mono (pointLocalHomologyIso x V (hKV hx) k).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact (supportExcisionIso_point K hK V hKV x hx k).symm

end TernaryPoly.RationalChartCompactSupport
