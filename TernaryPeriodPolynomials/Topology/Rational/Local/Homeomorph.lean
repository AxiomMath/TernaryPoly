module

public import TernaryPeriodPolynomials.Topology.Rational.Local.MapComposition
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory HomologicalComplex TopologicalSpace Topology
open RationalLocalChartHomology
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A local homeomorphism admits an actual open embedding neighborhood at every point. -/
theorem exists_open_embedding_neighborhood (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) :
    ∃ V : Opens X, x ∈ V ∧ IsOpenEmbedding (fun v : V => f v.val) := by
  obtain ⟨e,hx,he⟩ := hf x
  refine ⟨⟨e.source,e.open_source⟩,hx,?_⟩
  change IsOpenEmbedding (e.source.domRestrict f)
  rw [he]
  exact e.isOpenEmbedding_restrict

/-- One choice of an embedding neighborhood; the resulting local map is independent of it. -/
def embeddingNeighborhood (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) : Opens X :=
  (exists_open_embedding_neighborhood f hf x).choose

theorem mem_embeddingNeighborhood (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) :
    x ∈ embeddingNeighborhood f hf x :=
  (exists_open_embedding_neighborhood f hf x).choose_spec.1

theorem embeddingNeighborhood_isOpenEmbedding (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) :
    IsOpenEmbedding (fun v : embeddingNeighborhood f hf x => f v.val) :=
  (exists_open_embedding_neighborhood f hf x).choose_spec.2

theorem embeddingNeighborhood_isolatesFiber (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) :
    IsolatesFiber f x (embeddingNeighborhood f hf x) :=
  isolatesFiber_of_isOpenEmbedding f x _ (mem_embeddingNeighborhood f hf x)
    (embeddingNeighborhood_isOpenEmbedding f hf x)

variable [T1Space X]

/-- The canonical actual local homology map of a local homeomorphism. -/
def localHomeomorphMap (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) (k : ℕ) :
    (localChains x).homology k ⟶ (localChains (f x)).homology k :=
  localHomologyMap f x (embeddingNeighborhood f hf x) (mem_embeddingNeighborhood f hf x)
    (embeddingNeighborhood_isolatesFiber f hf x) k

/-- Every isolating open neighborhood computes the same canonical local map. -/
theorem localHomeomorphMap_eq (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X)
    (V : Opens X) (hx : x ∈ V) (hV : IsolatesFiber f x V) (k : ℕ) :
    localHomeomorphMap f hf x k = localHomologyMap f x V hx hV k :=
  localHomologyMap_independent f x _ V _ hx _ hV k

/-- The canonical local map of a homeomorphism is the literal point-pair homology map. -/
theorem localHomeomorphMap_homeomorph (e : X ≃ₜ Y) (x : X) (k : ℕ) :
    localHomeomorphMap ⟨e,e.continuous⟩ e.isLocalHomeomorph x k =
      homologyMap (homeomorphLocalIso e x).hom k :=
  localHomologyMap_homeomorph e x _ _ _ k

variable [T1Space Y]

/-- Every actual local map of a local homeomorphism is an isomorphism in every degree. -/
instance localHomeomorphMap_isIso (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) (k : ℕ) :
    IsIso (localHomeomorphMap f hf x k) :=
  localHomologyMap_isIso f x _ _ _ (embeddingNeighborhood_isOpenEmbedding f hf x) k

/-- The actual local homology isomorphism of a local homeomorphism. -/
def localHomeomorphIso (f : C(X,Y)) (hf : IsLocalHomeomorph f) (x : X) (k : ℕ) :
    (localChains x).homology k ≅ (localChains (f x)).homology k :=
  asIso (localHomeomorphMap f hf x k)

/-- Canonical local maps of local homeomorphisms compose on their actual local homology groups. -/
theorem localHomeomorphMap_comp (f : C(X,Y)) (g : C(Y,Z))
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) (x : X) (k : ℕ) :
    localHomeomorphMap f hf x k ≫ localHomeomorphMap g hg (f x) k =
      localHomeomorphMap (g.comp f) (hg.comp hf) x k := by
  let W := embeddingNeighborhood g hg (f x)
  let V : Opens X := embeddingNeighborhood f hf x ⊓ ⟨f ⁻¹' (W : Set Y),W.isOpen.preimage f.continuous⟩
  have hy : f x ∈ W := mem_embeddingNeighborhood g hg (f x)
  have hx : x ∈ V := ⟨mem_embeddingNeighborhood f hf x,hy⟩
  have hV : IsolatesFiber f x V := fun z hz he => embeddingNeighborhood_isolatesFiber f hf x z hz.1 he
  have hW : IsolatesFiber g (f x) W := embeddingNeighborhood_isolatesFiber g hg (f x)
  have hVW : Set.MapsTo f V W := fun _ hz => hz.2
  rw [localHomeomorphMap_eq f hf x V hx hV k,localHomeomorphMap_eq g hg (f x) W hy hW k,
    localHomeomorphMap_eq (g.comp f) (hg.comp hf) x V hx
      (isolatesFiber_comp f g x V W hV hW hVW) k]
  exact localHomologyMap_comp f g x V W hx hy hV hW hVW k

end TernaryPoly.RationalLocalMap
