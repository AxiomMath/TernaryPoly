module

public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationSupport
public import TernaryPeriodPolynomials.Topology.Rational.Local.GeneratorDescent
public import Mathlib.Topology.Separation.Regular

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalOrientation
open CategoryTheory HomologicalComplex TopologicalSpace Topology
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology RationalLocalMap
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [RegularSpace X]

/-- A surjective local homeomorphism carries a locally represented family to any family agreeing
under its actual local maps. Closed-neighborhood shrinking and genuine excision construct the
local representatives downstairs. -/
theorem locallyRepresented_pushforward (f : C(X,Y)) (hf : IsLocalHomeomorph f)
    (hs : Function.Surjective f) (k : ℕ)
    (o : ∀ x : X, (localChains x).homology k) (ho : LocallyRepresented k o)
    (b : ∀ y : Y, (localChains y).homology k)
    (hb : ∀ x, localHomeomorphMap f hf x k (o x) = b (f x)) : LocallyRepresented k b := by
  intro y
  obtain ⟨x,rfl⟩ := hs y
  obtain ⟨U,K,hxU,hUK,c,hc⟩ := ho x
  obtain ⟨V,hxV,he⟩ := exists_open_embedding_neighborhood f hf x
  obtain ⟨L,hLnh,hL,hLUV⟩ := exists_mem_nhds_isClosed_subset
    ((U.isOpen.inter V.isOpen).mem_nhds (show x ∈ (U : Set X) ∩ V from ⟨hxU,hxV⟩))
  have hLV : L ⊆ V := fun _ hz => (hLUV hz).2
  have hLK : L ⊆ K := fun _ hz => hUK (hLUV hz).1
  let iso := supportExcisionIso L hL V hLV k
  let cL := homologyMap (supportRestriction K L hLK) k c
  let cV := iso.inv cL
  let cY := homologyMap (imageSupportMap f V L hLV he.injective) k cV
  refine ⟨⟨f '' interior L,hf.isOpenMap _ isOpen_interior⟩,f '' L,
    ⟨x,mem_interior_iff_mem_nhds.mpr hLnh,rfl⟩,
    Set.image_mono interior_subset,cY,?_⟩
  intro z hz hzL
  obtain ⟨w,hw,rfl⟩ := hz
  have hwL : w ∈ L := interior_subset hw
  have hwU : w ∈ U := (hLUV hwL).1
  have hh := congrArg (fun a => a cV) (imageSupportMap_local f hf V L hLV he w hwL k)
  change homologyMap (supportPointMap (f '' L) (f w) _) k cY =
    localHomeomorphMap f hf w k
      (homologyMap (supportPointMap L w hwL) k (homologyMap (supportExcisionMap L V) k cV)) at hh
  have hExc : homologyMap (supportExcisionMap L V) k cV = cL := by
    change (iso.inv ≫ iso.hom) cL = cL
    rw [iso.inv_hom_id]
    rfl
  have hr : homologyMap (supportRestriction K L hLK) k ≫
      homologyMap (supportPointMap L w hwL) k = homologyMap (supportPointMap K w (hLK hwL)) k := by
    rw [← homologyMap_comp,supportRestriction_point]
  have hrc := congrArg (fun a => a c) hr
  change homologyMap (supportPointMap L w hwL) k cL =
    homologyMap (supportPointMap K w (hLK hwL)) k c at hrc
  rw [hc w hwU (hLK hwL)] at hrc
  rw [hExc,hrc,hb] at hh
  exact hh

/-- Fiber-independent covering descent preserves genuine local representability of generators. -/
theorem descendedGenerator_locallyRepresented (f : C(X,Y)) (hf : IsLocalHomeomorph f)
    (hs : Function.Surjective f) (k : ℕ)
    (o : ∀ x : X, (localChains x).homology k) (ho : LocallyRepresented k o)
    (hinv : ∀ x x', f x = f x' → totalLocalMap f hf k ⟨x,o x⟩ = totalLocalMap f hf k ⟨x',o x'⟩) :
    LocallyRepresented k (descendedGenerator f hf hs k o) :=
  locallyRepresented_pushforward f hf hs k o ho _ (descendedGenerator_apply f hf hs k o hinv)

end TernaryPoly.RationalLocalOrientation
