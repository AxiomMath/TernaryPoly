module

public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportIso

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalChartCompactSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalOrientation

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual support excision commutes with restriction to a smaller support. -/
theorem supportExcisionMap_restriction (K L V : Set X) (hLK : L ⊆ K) :
    supportExcisionMap K V ≫ supportRestriction K L hLK =
      supportRestriction ((Subtype.val : V → X) ⁻¹' K) ((Subtype.val : V → X) ⁻¹' L)
        (Set.preimage_mono hLK) ≫ supportExcisionMap L V := by
  unfold supportExcisionMap excisionMap supportRestriction
  erw [relativeMap_comp, relativeMap_comp]
  rfl

/-- The actual source-target chart-pair isomorphisms commute with support restriction. -/
theorem chartSupportPairIso_restriction (e : OpenPartialHomeomorph X Y) (K L : Set X)
    (hKs : K ⊆ e.source) (hLs : L ⊆ e.source) (hLK : L ⊆ K) :
    (chartSupportPairIso e K hKs).hom ≫
        supportRestriction ((Subtype.val : e.target → Y) ⁻¹' (e '' K))
          ((Subtype.val : e.target → Y) ⁻¹' (e '' L)) (Set.preimage_mono (Set.image_mono hLK)) =
      supportRestriction ((Subtype.val : e.source → X) ⁻¹' K) ((Subtype.val : e.source → X) ⁻¹' L)
        (Set.preimage_mono hLK) ≫ (chartSupportPairIso e L hLs).hom := by
  unfold chartSupportPairIso supportRestriction
  rw [relativeHomeomorphIso_hom, relativeHomeomorphIso_hom]
  erw [relativeMap_comp, relativeMap_comp]
  rfl

variable [T2Space X] [T2Space Y]

/-- Compact-support chart comparisons are natural under actual support inclusion
within the same chart. -/
theorem chartSupportHomologyIso_restriction (e : OpenPartialHomeomorph X Y) (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (hKs : K ⊆ e.source) (hLs : L ⊆ e.source)
    (hLK : L ⊆ K) (k : ℕ) :
    homologyMap (supportRestriction K L hLK) k ≫ (chartSupportHomologyIso e L hL hLs k).hom =
      (chartSupportHomologyIso e K hK hKs k).hom ≫
        homologyMap (supportRestriction (e '' K) (e '' L) (Set.image_mono hLK)) k := by
  let a := supportExcisionIso K hK.isClosed ⟨e.source, e.open_source⟩ hKs k
  rw [← cancel_epi a.hom]
  have hs : a.hom ≫ homologyMap (supportRestriction K L hLK) k =
      homologyMap (supportRestriction ((Subtype.val : e.source → X) ⁻¹' K)
        ((Subtype.val : e.source → X) ⁻¹' L) (Set.preimage_mono hLK)) k ≫
          homologyMap (supportExcisionMap L e.source) k := by
    change homologyMap (supportExcisionMap K e.source) k ≫ _ = _
    rw [← homologyMap_comp, ← homologyMap_comp, supportExcisionMap_restriction]
  rw [← Category.assoc, hs, Category.assoc, chartSupportHomologyIso_excision]
  change _ = homologyMap (supportExcisionMap K e.source) k ≫ _
  rw [← Category.assoc, chartSupportHomologyIso_excision, ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  rw [Category.assoc, supportExcisionMap_restriction,
    ← Category.assoc, ← chartSupportPairIso_restriction e K L hKs hLs hLK, Category.assoc]

end TernaryPoly.RationalChartCompactSupport
