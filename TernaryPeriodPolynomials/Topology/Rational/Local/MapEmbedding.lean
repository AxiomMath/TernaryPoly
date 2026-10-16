module

public import TernaryPeriodPolynomials.Topology.Rational.Local.Map
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalLocalMap
open CategoryTheory Limits HomologicalComplex TopologicalSpace Topology
open RationalRelativeSingular RationalRelativeExcision RationalLocalChartHomology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open embedding on a neighborhood isolates the fiber at each point of that neighborhood. -/
theorem isolatesFiber_of_isOpenEmbedding (f : C(X,Y)) (x : X) (V : Set X) (hx : x ∈ V)
    (he : IsOpenEmbedding (fun v : V => f v.val)) : IsolatesFiber f x V := by
  intro z hz heq
  exact congrArg Subtype.val (he.injective (a₁ := (⟨z,hz⟩ : V)) (a₂ := ⟨x,hx⟩) heq)

/-- A locally embedded neighborhood maps its literal punctured pair by a homeomorphism onto
an open image, followed by genuine point excision. -/
theorem neighborhoodPairMap_factorization (f : C(X,Y)) (x : X) (V : Set X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (he : IsOpenEmbedding (fun v : V => f v.val)) :
    neighborhoodPairMap f x V hx hf =
      (homeomorphLocalIso he.isEmbedding.toHomeomorph (⟨x,hx⟩ : V)).hom ≫
        pointExcisionMap (f x) (Set.range (fun v : V => f v.val)) ⟨⟨x,hx⟩,rfl⟩ := by
  erw [pointExcisionMap_eq_relativeMap]
  unfold homeomorphLocalIso
  rw [relativeHomeomorphIso_hom]
  erw [relativeMap_comp]
  rfl

variable [T1Space Y]

/-- The actual pair map of a locally embedded neighborhood is a quasi-isomorphism. -/
theorem neighborhoodPairMap_quasiIso (f : C(X,Y)) (x : X) (V : Set X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (he : IsOpenEmbedding (fun v : V => f v.val)) :
    QuasiIso (neighborhoodPairMap f x V hx hf) := by
  rw [neighborhoodPairMap_factorization f x V hx hf he]
  have hi : QuasiIso (pointExcisionMap (f x) (Set.range (fun v : V => f v.val))
      ⟨⟨x,hx⟩,rfl⟩) :=
    pointExcisionMap_quasiIso (f x) ⟨Set.range (fun v : V => f v.val),he.isOpen_range⟩
      ⟨⟨x,hx⟩,rfl⟩
  exact quasiIso_comp (hφ' := hi) (homeomorphLocalIso he.isEmbedding.toHomeomorph (⟨x,hx⟩ : V)).hom
    (pointExcisionMap (f x) (Set.range (fun v : V => f v.val)) ⟨⟨x,hx⟩,rfl⟩)

variable [T1Space X]

/-- A continuous map which is an open embedding near x induces an actual local homology
isomorphism; this is the genuine localized pair map. -/
theorem localHomologyMap_isIso (f : C(X,Y)) (x : X) (V : Opens X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (he : IsOpenEmbedding (fun v : V => f v.val)) (k : ℕ) :
    IsIso (localHomologyMap f x V hx hf k) := by
  have := neighborhoodPairMap_quasiIso f x V hx hf he
  unfold localHomologyMap
  infer_instance

/-- The actual local homology isomorphism of a continuous map embedded on an open neighborhood. -/
def localHomologyIso (f : C(X,Y)) (x : X) (V : Opens X) (hx : x ∈ V)
    (hf : IsolatesFiber f x V) (he : IsOpenEmbedding (fun v : V => f v.val)) (k : ℕ) :
    (localChains x).homology k ≅ (localChains (f x)).homology k := by
  have := localHomologyMap_isIso f x V hx hf he k
  exact asIso (localHomologyMap f x V hx hf k)

end TernaryPoly.RationalLocalMap
