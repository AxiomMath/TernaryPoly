module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Ext
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeShapiroComparison
open CategoryTheory CategoryTheory.Abelian

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
/-- Contravariant Ext transport through a genuine isomorphism of source objects. -/
def extCongrLeft {A B E : C} (i : A ≅ B) (n : ℕ) : Ext B E n ≃+ Ext A E n where
  toFun a := (Ext.mk₀ i.hom).comp a (zero_add n)
  invFun a := (Ext.mk₀ i.inv).comp a (zero_add n)
  left_inv a := by simp only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]
  right_inv a := by simp only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
  map_add' a b := Ext.comp_add _ _ _ _

variable (R : Type v) [CommRing R] [Linear R C] {X E : C}
    (P : ProjectiveResolution X) (n : ℕ)

/-- The three terms of the genuine resolved cochain complex around a positive degree. -/
abbrev resolvedSegment : ShortComplex (ModuleCat R) :=
  (P.complex.linearYonedaObj R E).sc' n (n + 1) (n + 2)

/-- A resolved cocycle gives its actual derived-category Ext class. -/
def cocycleToExt : LinearMap.ker (resolvedSegment R (E := E) P n).g.hom →+
    Ext X E (n + 1) where
  toFun f := P.extMk f.val (n + 2) rfl f.property
  map_zero' := P.extMk_zero (n + 2) rfl
  map_add' f g := (P.add_extMk f.val g.val (n + 2) rfl f.property g.property).symm

lemma cocycleToExt_surjective : Function.Surjective (cocycleToExt R (E := E) P n) := by
  intro a
  obtain ⟨f, hf, h⟩ := P.extMk_surjective a (n + 2) rfl
  exact ⟨⟨f, hf⟩, h⟩

/-- The kernel is precisely the actual resolved coboundaries. -/
lemma cocycleToExt_ker : (cocycleToExt R (E := E) P n).ker =
    (LinearMap.range (resolvedSegment R (E := E) P n).moduleCatToCycles).toAddSubgroup := by
  ext f
  change P.extMk f.val (n + 2) rfl f.property = 0 ↔ _
  rw [P.extMk_eq_zero_iff f.val (n + 2) rfl f.property n rfl]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

/-- The two Mathlib Ext constructions meet in the same quotient of resolved cocycles.
This is an additive equivalence, proved from the projective-resolution representative API. -/
def extEquivResolutionHomology : Ext X E (n + 1) ≃+
    (P.complex.linearYonedaObj R E).homology (n + 1) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (cocycleToExt R P n)
    (cocycleToExt_surjective R P n)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (cocycleToExt_ker R P n)).trans
      (((P.complex.linearYonedaObj R E).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp) ≪≫ (resolvedSegment R (E := E) P n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv.symm))

/-- Actual group cohomology and actual derived-category Ext agree in every positive degree. -/
def trivialExtEquivGroupCohomology {G : Type} [Group G] (E : Rep.{0} ℚ G) (n : ℕ)
    [HasExt.{1} (Rep.{0} ℚ G)] :
    Ext.{1} (Rep.trivial ℚ G ℚ) E (n + 1) ≃+ groupCohomology E (n + 1) :=
  (extEquivResolutionHomology ℚ (Rep.barResolution ℚ G) n).trans
    (groupCohomologyIso E (n + 1) (Rep.barResolution ℚ G)).toLinearEquiv.toAddEquiv.symm

end TernaryPoly.RelativeShapiroComparison
