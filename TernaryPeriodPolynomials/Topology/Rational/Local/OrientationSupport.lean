module

public import TernaryPeriodPolynomials.Topology.Rational.Local.Orientation
public import TernaryPeriodPolynomials.Topology.Rational.Local.Homeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalOrientation
open CategoryTheory HomologicalComplex TopologicalSpace Topology
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology RationalLocalMap
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Literal restriction from a larger support to a smaller one. -/
def supportRestriction (K L : Set X) (hLK : L ⊆ K) : relativeChains Kᶜ ⟶ relativeChains Lᶜ :=
  relativeMap (ContinuousMap.id X) _ _ (fun _ hz h => hz (hLK h))

theorem supportRestriction_point (K L : Set X) (hLK : L ⊆ K) (x : X) (hx : x ∈ L) :
    supportRestriction K L hLK ≫ supportPointMap L x hx = supportPointMap K x (hLK hx) := by
  unfold supportRestriction supportPointMap
  erw [relativeMap_comp]
  rfl

/-- The actual excision map for a support contained in a neighborhood. -/
def supportExcisionMap (L V : Set X) :
    relativeChains ((Subtype.val : V → X) ⁻¹' L)ᶜ ⟶ relativeChains Lᶜ :=
  excisionMap Lᶜ V

/-- Excision applies to any closed support contained in an open neighborhood. -/
theorem supportExcisionMap_quasiIso (L : Set X) (hL : IsClosed L) (V : Opens X) (hLV : L ⊆ V) :
    QuasiIso (supportExcisionMap L V) := by
  have hcover : (⟨Lᶜ,hL.isOpen_compl⟩ : Opens X) ⊔ V = ⊤ := by
    ext x
    change (x ∈ Lᶜ ∨ x ∈ V) ↔ True
    constructor
    · tauto
    · intro _
      by_cases hx : x ∈ L
      · exact Or.inr (hLV hx)
      · exact Or.inl hx
  exact excisionMap_quasiIso ⟨Lᶜ,hL.isOpen_compl⟩ V hcover

/-- The actual support-excision isomorphism on rational relative homology. -/
def supportExcisionIso (L : Set X) (hL : IsClosed L) (V : Opens X) (hLV : L ⊆ V) (k : ℕ) :
    (relativeChains ((Subtype.val : V → X) ⁻¹' L)ᶜ).homology k ≅ (relativeChains Lᶜ).homology k := by
  have := supportExcisionMap_quasiIso L hL V hLV
  exact asIso (homologyMap (supportExcisionMap L V) k)

/-- Excision of a support commutes with literal restriction to any point in that support. -/
theorem supportExcisionMap_point (L V : Set X) (x : X) (hx : x ∈ L) (hxV : x ∈ V) :
    supportExcisionMap L V ≫ supportPointMap L x hx =
      supportPointMap ((Subtype.val : V → X) ⁻¹' L) (⟨x,hxV⟩ : V) hx ≫ pointExcisionMap x V hxV := by
  rw [pointExcisionMap_eq_relativeMap]
  unfold supportExcisionMap excisionMap supportPointMap
  erw [relativeMap_comp,relativeMap_comp]
  rfl

/-- A map embedded on V carries the support pair in V to the literal image-support pair. -/
def imageSupportMap (f : C(X,Y)) (V L : Set X) (hLV : L ⊆ V)
    (hf : Function.Injective (fun v : V => f v.val)) :
    relativeChains ((Subtype.val : V → X) ⁻¹' L)ᶜ ⟶ relativeChains (f '' L)ᶜ :=
  relativeMap ⟨fun v : V => f v.val,f.continuous.comp continuous_subtype_val⟩ _ _ (by
    intro z hz he
    obtain ⟨w,hw,heq⟩ := he
    have hh : (⟨w,hLV hw⟩ : V) = z := hf heq
    apply hz
    change z.val ∈ L
    rw [← hh]
    exact hw)

/-- Image-support pushforward commutes with the actual localized pair map at each support point. -/
theorem imageSupportMap_point (f : C(X,Y)) (V L : Set X) (hLV : L ⊆ V)
    (hf : Function.Injective (fun v : V => f v.val)) (x : X) (hx : x ∈ L)
    (hV : IsolatesFiber f x V) :
    imageSupportMap f V L hLV hf ≫ supportPointMap (f '' L) (f x) ⟨x,hx,rfl⟩ =
      supportPointMap ((Subtype.val : V → X) ⁻¹' L) (⟨x,hLV hx⟩ : V) hx ≫
        neighborhoodPairMap f x V (hLV hx) hV := by
  unfold imageSupportMap supportPointMap neighborhoodPairMap
  erw [relativeMap_comp,relativeMap_comp]
  rfl

variable [T1Space X]

/-- The image-support and support-excision diagrams recover the actual canonical local map. -/
theorem imageSupportMap_local (f : C(X,Y)) (hf : IsLocalHomeomorph f) (V : Opens X)
    (L : Set X) (hLV : L ⊆ V) (he : IsOpenEmbedding (fun v : V => f v.val))
    (x : X) (hx : x ∈ L) (k : ℕ) :
    homologyMap (imageSupportMap f V L hLV he.injective) k ≫
      homologyMap (supportPointMap (f '' L) (f x) ⟨x,hx,rfl⟩) k =
    homologyMap (supportExcisionMap L V) k ≫ homologyMap (supportPointMap L x hx) k ≫
      localHomeomorphMap f hf x k := by
  let hV := isolatesFiber_of_isOpenEmbedding f x V (hLV hx) he
  rw [localHomeomorphMap_eq f hf x V (hLV hx) hV k,← homologyMap_comp,
    imageSupportMap_point f V L hLV he.injective x hx hV,homologyMap_comp]
  have hs := congrArg (fun a => homologyMap a k) (supportExcisionMap_point L V x hx (hLV hx))
  rw [homologyMap_comp,homologyMap_comp] at hs
  rw [← Category.assoc]
  erw [hs]
  rw [Category.assoc,← pointLocalHomologyIso_hom,localHomologyMap_inclusion]

end TernaryPoly.RationalLocalOrientation
