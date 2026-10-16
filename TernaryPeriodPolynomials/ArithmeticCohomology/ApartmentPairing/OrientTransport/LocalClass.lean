module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartClass
public import TernaryPeriodPolynomials.Topology.Euclidean.OrientationScalar
public import TernaryPeriodPolynomials.Topology.Rational.Local.Homeomorph

@[expose] public section


/-!
# Relative classes of chains, and their naturality

For a space `X`, a set `S` and a chain `c` of `X` whose boundary is carried by `S`, `rcls S m c h` is the class of `c` in
`H_m(X, S)` (relative chains modulo `S`, the cokernel of the inclusion).  Equality of classes yields a decomposition up to a
chain over `S` and a boundary (`exists_decomp_of_rcls_eq`), and a map of pairs `g : (X, S) → (Y, T)` carries `rcls S m c`
to `rcls T m (g_# c)` (`rcls_map`).  With the library's local maps this gives the class of a chain in the local homology at a
point of the base of a local homeomorphism in terms of the class of its lift (`localHomologyMap_rcls`).

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
  TernaryPoly.RationalLocalChartHomology TernaryPoly.RationalRelativeExcision TernaryPoly.RationalLocalMap
  TernaryPoly.RationalSingularAugmentation
open TernaryPoly.SingularLocalCap.Descent

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

variable {X Y : TopCat.{0}}

/-- A chain lies over `S` iff its image in the relative chains modulo `S` vanishes (any space). -/
theorem rel_proj_eq_zero_iff (S : Set X) (n : ℕ) (x : singularChainGroup ℚ (X) n) :
    (cokernel.π (RationalRelativeSingular.inclusion S)).f n x = 0 ↔
      x ∈ subChainSubmodule ℚ (X) S n := by
  constructor
  · intro h0
    obtain ⟨b, hb⟩ := (SingularLocalCap.RelativeAlgebra.projection_zero_iff
      (RationalRelativeSingular.inclusion S) n _).mp h0
    rw [← hb]
    exact singularChainMap_sInclusion_mem _ _ b
  · intro hx
    obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) S n).2 ⟨x, hx⟩
    exact (SingularLocalCap.RelativeAlgebra.projection_zero_iff
      (RationalRelativeSingular.inclusion S) n _).mpr ⟨y, congrArg Subtype.val hy⟩

theorem rel_proj_cycle (S : Set X) (n : ℕ) (c : singularChainGroup ℚ (X) (n + 1))
    (h : (singularBoundary ℚ (X) n).hom c ∈ subChainSubmodule ℚ (X) S n) :
    (relativeChains S).d (n + 1) n ((cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c) = 0 := by
  have hd := ConcreteCategory.congr_hom ((cokernel.π (RationalRelativeSingular.inclusion S)).comm (n + 1) n) c
  have h0 : (cokernel.π (RationalRelativeSingular.inclusion S)).f n
      ((singularBoundary ℚ (X) n).hom c) = 0 := (rel_proj_eq_zero_iff S n _).mpr h
  exact hd.trans h0

/-- The class in `H_{n+1}(X, S)` of a chain whose boundary is carried by `S`. -/
def rcls (S : Set X) (n : ℕ) (c : singularChainGroup ℚ (X) (n + 1))
    (h : (singularBoundary ℚ (X) n).hom c ∈ subChainSubmodule ℚ (X) S n) :
    (relativeChains S).homology (n + 1) :=
  chainClass (relativeChains S) (n + 1)
    ⟨(cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c, rel_proj_cycle S n c h⟩

/-- A map of pairs carries the class of a chain to the class of its image. -/
theorem rcls_map (f : X ⟶ Y) (S : Set X) (T : Set Y) (hf : Set.MapsTo f.hom S T) (n : ℕ)
    (c : singularChainGroup ℚ (X) (n + 1))
    (h : (singularBoundary ℚ (X) n).hom c ∈ subChainSubmodule ℚ (X) S n)
    (h' : (singularBoundary ℚ (Y) n).hom ((singularChainMap ℚ f (n + 1)).hom c) ∈
      subChainSubmodule ℚ (Y) T n) :
    homologyMap (relativeMap f.hom S T hf) (n + 1) (rcls S n c h) =
      rcls T n ((singularChainMap ℚ f (n + 1)).hom c) h' := by
  unfold rcls
  apply TernaryPoly.SingularLocalCompactCap.Algebra.chainClass_natural
  have hπ : cokernel.π (RationalRelativeSingular.inclusion S) ≫ relativeMap f.hom S T hf =
      chainMap f.hom ≫ cokernel.π (RationalRelativeSingular.inclusion T) := by
    unfold relativeMap
    exact cokernel.π_desc _ _ _
  exact (ConcreteCategory.congr_hom (congrArg (fun G => G.f (n + 1)) hπ) c).symm

/-- A map of pairs carries chains with boundary over `S` to chains with boundary over `T`. -/
theorem push_mem (g : X ⟶ Y) (S : Set X) (T : Set Y) (hg : Set.MapsTo g.hom S T) (n : ℕ)
    {c : singularChainGroup ℚ X (n + 1)}
    (h : (singularBoundary ℚ X n).hom c ∈ subChainSubmodule ℚ X S n) :
    (singularBoundary ℚ Y n).hom ((singularChainMap ℚ g (n + 1)).hom c) ∈ subChainSubmodule ℚ Y T n := by
  have h1 := singularChainMap_boundary_apply ℚ g n c
  rw [h1]
  exact singularChainMap_mem_sub g T n (subChainSubmodule_mono (fun z hz => hg hz) n h)

theorem mapsTo_punct (g : X ⟶ Y) (x : X) (y : Y) (_hy : g.hom x = y)
    (hg : ∀ z, g.hom z = y → z = x) : Set.MapsTo g.hom ({x}ᶜ : Set X) ({y}ᶜ : Set Y) := by
  intro z hz hzy
  exact hz (hg z hzy)

section Local

variable [T1Space X]

/-- **Excision at a point, on classes.**  The class of a chain of a neighbourhood `V` of `x` maps to the class of its image
in the local chains at `x`. -/
theorem rcls_pointExcision (x : X) (V : Opens X) (hx : x ∈ V) (n : ℕ)
    (γ : singularChainGroup ℚ (TopCat.of V) (n + 1))
    (h : (singularBoundary ℚ (TopCat.of V) n).hom γ ∈
      subChainSubmodule ℚ (TopCat.of V) ({(⟨x, hx⟩ : V)}ᶜ : Set V) n)
    (h' : (singularBoundary ℚ X n).hom ((singularChainMap ℚ (sInclusion (V : Set X)) (n + 1)).hom γ) ∈
      subChainSubmodule ℚ X ({x}ᶜ : Set X) n) :
    (pointLocalHomologyIso x V hx (n + 1)).hom (rcls (X := TopCat.of V) ({(⟨x, hx⟩ : V)}ᶜ : Set V) n γ h) =
      rcls (X := X) ({x}ᶜ : Set X) n ((singularChainMap ℚ (sInclusion (V : Set X)) (n + 1)).hom γ) h' := by
  rw [pointLocalHomologyIso_hom, pointExcisionMap_eq_relativeMap]
  exact rcls_map (X := TopCat.of V) (Y := X) (sInclusion (V : Set X)) ({(⟨x, hx⟩ : V)}ᶜ : Set V)
    ({x}ᶜ : Set X) (mapsTo_punct (sInclusion (V : Set X)) ⟨x, hx⟩ x rfl (fun z hz => Subtype.ext hz)) n γ h h'

/-- **The local map on classes.**  The canonical local map of `f` at `x` (computed in a neighbourhood `V` isolating the
fibre) sends the class of a chain of `V` to the class of its image. -/
theorem localMap_rcls {Y : TopCat.{0}} [T1Space Y] (f : X ⟶ Y) (x : X) (V : Opens X) (hx : x ∈ V)
    (hf : IsolatesFiber f.hom x V) (n : ℕ)
    (γ : singularChainGroup ℚ (TopCat.of V) (n + 1))
    (h : (singularBoundary ℚ (TopCat.of V) n).hom γ ∈
      subChainSubmodule ℚ (TopCat.of V) ({(⟨x, hx⟩ : V)}ᶜ : Set V) n)
    (h' : (singularBoundary ℚ Y n).hom ((singularChainMap ℚ (sInclusion (V : Set X) ≫ f) (n + 1)).hom γ) ∈
      subChainSubmodule ℚ Y ({f x}ᶜ : Set Y) n) :
    localHomologyMap f.hom x V hx hf (n + 1)
        ((pointLocalHomologyIso x V hx (n + 1)).hom (rcls (X := TopCat.of V) ({(⟨x, hx⟩ : V)}ᶜ : Set V) n γ h)) =
      rcls (X := Y) ({f x}ᶜ : Set Y) n
        ((singularChainMap ℚ (sInclusion (V : Set X) ≫ f) (n + 1)).hom γ) h' := by
  have h1 := congrArg (fun L => L (rcls (X := TopCat.of V) ({(⟨x, hx⟩ : V)}ᶜ : Set V) n γ h))
    (localHomologyMap_inclusion f.hom x V hx hf (n + 1))
  refine h1.symm.symm.trans ?_
  exact rcls_map (X := TopCat.of V) (Y := Y) (sInclusion (V : Set X) ≫ f) ({(⟨x, hx⟩ : V)}ᶜ : Set V)
    ({f x}ᶜ : Set Y) (mapsTo_punct (sInclusion (V : Set X) ≫ f) ⟨x, hx⟩ (f x) rfl
      (fun z hz => Subtype.ext (hf z.val z.property hz))) n γ h h'

end Local

/-- A homeomorphism carries the local class of a chain at `x` to the local class of its image at `e x`. -/
theorem homeo_rcls (e : X ≃ₜ Y) (x : X) (n : ℕ) (c : singularChainGroup ℚ X (n + 1))
    (h : (singularBoundary ℚ X n).hom c ∈ subChainSubmodule ℚ X ({x}ᶜ : Set X) n)
    (h' : (singularBoundary ℚ Y n).hom ((singularChainMap ℚ (TopCat.ofHom ⟨e, e.continuous⟩) (n + 1)).hom c) ∈
      subChainSubmodule ℚ Y ({e x}ᶜ : Set Y) n) :
    homologyMap (homeomorphLocalIso e x).hom (n + 1) (rcls (X := X) ({x}ᶜ : Set X) n c h) =
      rcls (X := Y) ({e x}ᶜ : Set Y) n ((singularChainMap ℚ (TopCat.ofHom ⟨e, e.continuous⟩) (n + 1)).hom c) h' := by
  unfold homeomorphLocalIso
  rw [relativeHomeomorphIso_hom]
  exact rcls_map (X := X) (Y := Y) (TopCat.ofHom ⟨e, e.continuous⟩) ({x}ᶜ : Set X) ({e x}ᶜ : Set Y)
    (mapsTo_punct (TopCat.ofHom ⟨e, e.continuous⟩) x (e x) rfl (fun z hz => e.injective hz)) n c h h'

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
