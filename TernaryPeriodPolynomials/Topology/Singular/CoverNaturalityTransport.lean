module

public import TernaryPeriodPolynomials.Topology.GroupSingularCoefficientComparisonNaturality

@[expose] public section


noncomputable section
open CategoryTheory
namespace TernaryPoly.SingularCoverNaturality
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient

/-- Mapping a path class respects equality of continuous maps, with explicit endpoint casts. -/
theorem pathMap_congr {A C : Type*} [TopologicalSpace A] [TopologicalSpace C]
    {u v : C(A,C)} (h : u=v) {x y : A} (γ : Path.Homotopic.Quotient x y) :
    γ.map u=(γ.map v).cast (congrArg (fun k : C(A,C) => k x) h)
      (congrArg (fun k : C(A,C) => k y) h) := by
  subst v
  exact (Path.Homotopic.Quotient.cast_rfl_rfl _).symm

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [MulAction G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p'=p ≫ f)

/-- A commuting square sends an actual point of a covering fiber to its image upstairs. -/
def fiberMap {b : B} (e : Fiber p b) : Fiber p' (f b) :=
  ⟨F e.val,(congrArg (fun m : E ⟶ B' => m e.val) hsquare).trans (congrArg f e.property)⟩

/-- The actual fiber map of an equivariant square is equivariant. -/
theorem fiberMap_smul (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (hF : ∀ (g : G) (x : E), F (g • x)=g • F x) {b : B} (g : G) (e : Fiber p b) :
    fiberMap p p' F f hsquare (fiberSmul p hp g e)=
      fiberSmul p' hp' g (fiberMap p p' F f hsquare e) :=
  Subtype.ext (hF g e.val)

/-- The actual path lift proves transport naturality for a commuting square of covers. -/
theorem fiberMap_transport (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    {x y : B} (γ : Path.Homotopic.Quotient x y) (e : Fiber p x) :
    fiberTransport p' hp' (γ.map f.hom) (fiberMap p p' F f hsquare e)=
      fiberMap p p' F f hsquare (fiberTransport p hp γ e) := by
  let Γ := hp.isCoveringMap.liftPathQuotient γ e
  apply hp'.isCoveringMap.monodromy_eq_of_map_eq (Γ.map F.hom)
  have hcomp : (⟨p',hp'.continuous⟩ : C(E',B')).comp F.hom=
      f.hom.comp (⟨p,hp.continuous⟩ : C(E,B)) := by
    ext z
    exact congrArg (fun m : E ⟶ B' => m z) hsquare
  change (Γ.map F.hom).map p'.hom=(γ.map f.hom).cast
    (show p' (F e.val)=f x from (fiberMap p p' F f hsquare e).property)
    (show p' (F (fiberTransport p hp γ e).val)=f y from
      (fiberMap p p' F f hsquare (fiberTransport p hp γ e)).property)
  change p'.hom.comp F.hom=f.hom.comp p.hom at hcomp
  rw [←Path.Homotopic.Quotient.map_comp]
  rw [pathMap_congr hcomp,Path.Homotopic.Quotient.map_comp]
  have hm : Γ.map p.hom=γ.cast e.property (fiberTransport p hp γ e).property :=
    hp.isCoveringMap.map_liftPathQuotient γ e
  rw [hm]
  obtain ⟨γ⟩ := γ
  rfl

/-- Pullback of fiber coefficients is literal precomposition with the actual fiber map. -/
def coefficientPullback (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (hF : ∀ (g : G) (x : E), F (g • x)=g • F x) (V : Rep ℚ G) (b : B) :
    FiberCoefficient p' hp' V (f b) →ₗ[ℚ] FiberCoefficient p hp V b where
  toFun c := ⟨fun e => c.val (fiberMap p p' F f hsquare e),fun g e =>
    (congrArg c.val (fiberMap_smul p p' F f hsquare hp hp' hF g e)).trans (c.property g _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pullback of the actual coefficient system commutes with actual parallel transport. -/
theorem coefficientPullback_transport (hp : IsQuotientCoveringMap p G)
    (hp' : IsQuotientCoveringMap p' G)
    (hF : ∀ (g : G) (x : E), F (g • x)=g • F x) (V : Rep ℚ G)
    {x y : B} (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p' hp' V (f x)) :
    coefficientPullback p p' F f hsquare hp hp' hF V y
        (coefficientTransportLinear p' hp' (γ.map f.hom) c)=
      coefficientTransportLinear p hp γ (coefficientPullback p p' F f hsquare hp hp' hF V x c) := by
  apply Subtype.ext
  funext e
  change c.val (fiberTransport p' hp' (γ.map f.hom).symm (fiberMap p p' F f hsquare e))=
    c.val (fiberMap p p' F f hsquare (fiberTransport p hp γ.symm e))
  have hm : (γ.map f.hom).symm=γ.symm.map f.hom := by obtain ⟨γ⟩ := γ; rfl
  rw [hm]
  exact congrArg c.val (fiberMap_transport p p' F f hsquare hp hp' γ.symm e)

/-- The actual fiber pullback is a natural transformation of local systems over the base map. -/
def localSystemPullback (hp : IsQuotientCoveringMap p G)
    (hp' : IsQuotientCoveringMap p' G)
    (hF : ∀ (g : G) (x : E), F (g • x)=g • F x) (V : Rep ℚ G) :
    FundamentalGroupoid.map f.hom ⋙ coefficientLocalSystem (V := V) p' hp' ⟶
      coefficientLocalSystem (V := V) p hp where
  app b := ModuleCat.ofHom (coefficientPullback p p' F f hsquare hp hp' hF V b.as)
  naturality x y γ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact coefficientPullback_transport p p' F f hsquare hp hp' hF V γ c

end TernaryPoly.SingularCoverNaturality
