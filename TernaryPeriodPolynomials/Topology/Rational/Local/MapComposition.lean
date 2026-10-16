module

public import TernaryPeriodPolynomials.Topology.Rational.Local.MapEmbedding

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual map of punctured neighborhoods when their image is contained in the target. -/
def betweenNeighborhoodPairMap (f : C(X,Y)) (x : X) (V : Set X) (W : Set Y)
    (hx : x ∈ V) (hy : f x ∈ W) (hf : IsolatesFiber f x V) (hVW : Set.MapsTo f V W) :
    relativeChains ({(⟨x,hx⟩ : V)}ᶜ : Set V) ⟶
      relativeChains ({(⟨f x,hy⟩ : W)}ᶜ : Set W) :=
  relativeMap ⟨fun z : V => ⟨f z.val,hVW z.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ _ _
      (fun z hz he => hz (Subtype.ext (hf z.val z.property (congrArg Subtype.val he))))

/-- Including the target neighborhood recovers the actual localized pair map. -/
theorem betweenNeighborhoodPairMap_inclusion (f : C(X,Y)) (x : X) (V : Set X) (W : Set Y)
    (hx : x ∈ V) (hy : f x ∈ W) (hf : IsolatesFiber f x V) (hVW : Set.MapsTo f V W) :
    betweenNeighborhoodPairMap f x V W hx hy hf hVW ≫ pointExcisionMap (f x) W hy =
      neighborhoodPairMap f x V hx hf := by
  rw [pointExcisionMap_eq_relativeMap]
  unfold betweenNeighborhoodPairMap neighborhoodPairMap
  erw [relativeMap_comp]
  rfl

/-- Isolation of local fibers composes on compatible neighborhoods. -/
theorem isolatesFiber_comp (f : C(X,Y)) (g : C(Y,Z)) (x : X) (V : Set X) (W : Set Y)
    (hf : IsolatesFiber f x V) (hg : IsolatesFiber g (f x) W) (hVW : Set.MapsTo f V W) :
    IsolatesFiber (g.comp f) x V := fun z hz he => hf z hz (hg (f z) (hVW hz) he)

/-- The genuine pair map of a composite is the composite of the two neighborhood pair maps. -/
theorem betweenNeighborhoodPairMap_comp (f : C(X,Y)) (g : C(Y,Z)) (x : X)
    (V : Set X) (W : Set Y) (hx : x ∈ V) (hy : f x ∈ W)
    (hf : IsolatesFiber f x V) (hg : IsolatesFiber g (f x) W) (hVW : Set.MapsTo f V W) :
    betweenNeighborhoodPairMap f x V W hx hy hf hVW ≫ neighborhoodPairMap g (f x) W hy hg =
      neighborhoodPairMap (g.comp f) x V hx (isolatesFiber_comp f g x V W hf hg hVW) := by
  unfold betweenNeighborhoodPairMap neighborhoodPairMap
  erw [relativeMap_comp]
  rfl

variable [T1Space X] [T1Space Y]

/-- Actual local homology maps compose, with no global puncture-preservation assumption. -/
theorem localHomologyMap_comp (f : C(X,Y)) (g : C(Y,Z)) (x : X)
    (V : Opens X) (W : Opens Y) (hx : x ∈ V) (hy : f x ∈ W)
    (hf : IsolatesFiber f x V) (hg : IsolatesFiber g (f x) W)
    (hVW : Set.MapsTo f V W) (k : ℕ) :
    localHomologyMap f x V hx hf k ≫ localHomologyMap g (f x) W hy hg k =
      localHomologyMap (g.comp f) x V hx (isolatesFiber_comp f g x V W hf hg hVW) k := by
  apply (cancel_epi (pointLocalHomologyIso x V hx k).hom).mp
  rw [← Category.assoc,localHomologyMap_inclusion,localHomologyMap_inclusion]
  rw [← betweenNeighborhoodPairMap_inclusion f x V W hx hy hf hVW,homologyMap_comp,
    Category.assoc,← pointLocalHomologyIso_hom,localHomologyMap_inclusion,← homologyMap_comp,
    betweenNeighborhoodPairMap_comp]

omit [T1Space Y] in
/-- For a globally injective map, the localized map equals the literal map of ambient pairs. -/
theorem localHomologyMap_of_injective (f : C(X,Y)) (hf : Function.Injective f) (x : X)
    (V : Opens X) (hx : x ∈ V) (hV : IsolatesFiber f x V) (k : ℕ) :
    localHomologyMap f x V hx hV k =
      homologyMap (relativeMap f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y)
        (fun _ hz he => hz (hf he))) k := by
  apply (cancel_epi (pointLocalHomologyIso x V hx k).hom).mp
  rw [localHomologyMap_inclusion,pointLocalHomologyIso_hom,← homologyMap_comp,
    pointExcisionMap_eq_relativeMap]
  erw [relativeMap_comp]
  rfl

omit [T1Space Y] in
/-- The local homology map of a homeomorphism is its actual local homology isomorphism. -/
theorem localHomologyMap_homeomorph (e : X ≃ₜ Y) (x : X) (V : Opens X) (hx : x ∈ V)
    (hV : IsolatesFiber ⟨e,e.continuous⟩ x V) (k : ℕ) :
    localHomologyMap ⟨e,e.continuous⟩ x V hx hV k =
      homologyMap (homeomorphLocalIso e x).hom k := by
  rw [localHomologyMap_of_injective ⟨e,e.continuous⟩ e.injective]
  unfold homeomorphLocalIso
  rw [relativeHomeomorphIso_hom]
  rfl

end TernaryPoly.RationalLocalMap
