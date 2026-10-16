module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionNaturality
public import TernaryPeriodPolynomials.Topology.Rational.Local.ChartHomology

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A neighborhood contains only the specified point of its fiber. -/
def IsolatesFiber (f : C(X,Y)) (x : X) (V : Set X) : Prop :=
  ∀ z ∈ V, f z = f x → z = x

/-- The literal pair map from a fiber-isolating neighborhood to the target punctured pair.
A global covering need not itself map the complement of one lifted point into this pair. -/
def neighborhoodPairMap (f : C(X,Y)) (x : X) (V : Set X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) :
    relativeChains ({(⟨x,hx⟩ : V)}ᶜ : Set V) ⟶ localChains (f x) :=
  relativeMap ⟨fun z : V => f z.val,f.continuous.comp continuous_subtype_val⟩
    ({(⟨x,hx⟩ : V)}ᶜ : Set V) ({f x}ᶜ : Set Y) (fun z hz he => hz (Subtype.ext (hf z.val z.property he)))

/-- Restricting to a smaller neighborhood preserves the literal localized pair map. -/
theorem neighborhoodPairMap_natural (f : C(X,Y)) (x : X) (V W : Set X)
    (hxV : x ∈ V) (hxW : x ∈ W) (hVW : V ⊆ W)
    (hfV : IsolatesFiber f x V) (hfW : IsolatesFiber f x W) :
    pointNeighborhoodMap x V W hxV hxW hVW ≫ neighborhoodPairMap f x W hxW hfW =
      neighborhoodPairMap f x V hxV hfV := by
  unfold pointNeighborhoodMap neighborhoodPairMap
  erw [relativeMap_comp]
  rfl

variable [T1Space X]

/-- The genuine local homology map of a continuous map with an isolated local fiber. -/
def localHomologyMap (f : C(X,Y)) (x : X) (V : Opens X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (k : ℕ) :
    (localChains x).homology k ⟶ (localChains (f x)).homology k :=
  (pointLocalHomologyIso x V hx k).inv ≫ homologyMap (neighborhoodPairMap f x V hx hf) k

/-- The local homology map is characterized by the actual neighborhood inclusion square. -/
theorem localHomologyMap_inclusion (f : C(X,Y)) (x : X) (V : Opens X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (k : ℕ) :
    (pointLocalHomologyIso x V hx k).hom ≫ localHomologyMap f x V hx hf k =
      homologyMap (neighborhoodPairMap f x V hx hf) k := by
  simp [localHomologyMap]

/-- Passing to a smaller fiber-isolating neighborhood does not change the actual local map. -/
theorem localHomologyMap_natural (f : C(X,Y)) (x : X) (V W : Opens X)
    (hxV : x ∈ V) (hxW : x ∈ W) (hVW : V ≤ W)
    (hfV : IsolatesFiber f x V) (hfW : IsolatesFiber f x W) (k : ℕ) :
    localHomologyMap f x V hxV hfV k = localHomologyMap f x W hxW hfW k := by
  apply (cancel_epi (pointLocalHomologyIso x V hxV k).hom).mp
  rw [localHomologyMap_inclusion]
  rw [← pointLocalHomologyIso_natural x V W hxV hxW hVW k, Category.assoc,
    localHomologyMap_inclusion, ← homologyMap_comp]
  erw [neighborhoodPairMap_natural]

/-- Any two fiber-isolating open neighborhoods give exactly the same local homology map. -/
theorem localHomologyMap_independent (f : C(X,Y)) (x : X) (V W : Opens X)
    (hxV : x ∈ V) (hxW : x ∈ W)
    (hfV : IsolatesFiber f x V) (hfW : IsolatesFiber f x W) (k : ℕ) :
    localHomologyMap f x V hxV hfV k = localHomologyMap f x W hxW hfW k := by
  let U : Opens X := V ⊓ W
  have hxU : x ∈ U := ⟨hxV,hxW⟩
  have hfU : IsolatesFiber f x U := fun z hz he => hfV z hz.1 he
  exact (localHomologyMap_natural f x U V hxU hxV inf_le_left hfU hfV k).symm.trans
    (localHomologyMap_natural f x U W hxU hxW inf_le_right hfU hfW k)

end TernaryPoly.RationalLocalMap
