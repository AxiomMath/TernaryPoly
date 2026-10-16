module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVFlagCollar
public import TernaryPeriodPolynomials.Analysis.Compact.EmbeddingStrip

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology

namespace ProductOrbit
variable {G E T Y : Type*} [Group G] [MulAction G E]

def descend (f : E × T → Y) (hinv : ∀ (g : G) (x : E) (t : T), f (g • x,t)=f (x,t)) :
    Quotient (MulAction.orbitRel G E) × T → Y :=
  fun p => Quotient.lift (fun x => f (x,p.2)) (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    change g • y = x at hg
    rw [←hg, hinv]) p.1

@[simp] theorem descend_mk (f : E × T → Y)
    (hinv : ∀ (g : G) (x : E) (t : T), f (g • x,t)=f (x,t)) (x : E) (t : T) :
    descend f hinv (Quotient.mk _ x,t)=f (x,t) := rfl

variable [TopologicalSpace E] [TopologicalSpace T] [TopologicalSpace Y]
  [ContinuousConstSMul G E]

theorem projection_openQuotient : IsOpenQuotientMap
    (Prod.map (Quotient.mk (MulAction.orbitRel G E)) (id : T → T)) :=
  MulAction.isOpenQuotientMap_quotientMk.prodMap IsOpenQuotientMap.id

theorem descend_continuous (f : E × T → Y)
    (hinv : ∀ (g : G) (x : E) (t : T), f (g • x,t)=f (x,t)) (hf : Continuous f) :
    Continuous (descend f hinv) :=
  projection_openQuotient.continuous_comp_iff.mp hf

theorem descend_open (f : E × T → Y)
    (hinv : ∀ (g : G) (x : E) (t : T), f (g • x,t)=f (x,t)) (hf : IsOpenMap f) :
    IsOpenMap (descend f hinv) :=
  projection_openQuotient.isOpenMap_iff.mpr hf

end ProductOrbit

/-- Local injectivity descends along an open surjection. -/
theorem locallyInjective_of_open_surjection {E Q Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Q] (p : E → Q) (f : Q → Y) (hp : IsOpenMap p)
    (hs : Function.Surjective p) (hf : IsLocallyInjective (f ∘ p)) :
    IsLocallyInjective f := by
  intro q
  obtain ⟨x,rfl⟩ := hs q
  obtain ⟨V,hV,hx,hi⟩ := hf x
  refine ⟨p '' V, hp V hV, ⟨x,hx,rfl⟩, ?_⟩
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
  exact congrArg p (hi hx hy he)

open OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction IntegralGL3Congruence
  SymmetricSpaceBordifiedQuotient

@[simp] theorem boundaryProjection_smul (g : principalSix) (x : BoundaryCover) :
    boundaryProjection (g • x) = boundaryProjection x :=
  Subtype.ext (projection_smul principalSix g x.val)

def flagCollarBase (F : Flag) : FlagFaceOrbit F × ℝ → BoundaryBase :=
  ProductOrbit.descend (boundaryProjection ∘ flagCollarParam F) (by
    intro g x t
    change boundaryProjection (flagCollarParam F (g • x,t)) = _
    rw [flagCollarParam_equivariant, boundaryProjection_smul]
    rfl)

@[simp] theorem flagCollarBase_mk (F : Flag) (x : flagFace F) (t : ℝ) :
    flagCollarBase F (RestrictedQuotient.faceProjection (flagFace F) x,t) =
      boundaryProjection (flagCollarParam F (x,t)) := rfl

theorem flagCollarBase_continuous (F : Flag) : Continuous (flagCollarBase F) :=
  ProductOrbit.descend_continuous _ _
    (boundaryCovering.continuous.comp (flagCollarParam_isOpenEmbedding F).continuous)

theorem flagCollarBase_open (F : Flag) : IsOpenMap (flagCollarBase F) :=
  ProductOrbit.descend_open _ _
    (boundaryCovering.isOpenMap.comp (flagCollarParam_isOpenEmbedding F).isOpenMap)

theorem flagCollarBase_locallyInjective (F : Flag) : IsLocallyInjective (flagCollarBase F) := by
  apply locallyInjective_of_open_surjection
    (Prod.map (RestrictedQuotient.faceProjection (flagFace F)) id)
  · exact ProductOrbit.projection_openQuotient.isOpenMap
  · exact ProductOrbit.projection_openQuotient.surjective
  · exact (boundaryCovering.isLocalHomeomorph.comp
      (flagCollarParam_isOpenEmbedding F).isLocalHomeomorph).isLocallyInjective

theorem flagCollarBase_zero_injective (F : Flag) :
    Function.Injective (fun x : FlagFaceOrbit F => flagCollarBase F (x,0)) := by
  intro x y he
  apply (flagFaceQuotientHomeomorph F).injective
  induction x using Quotient.inductionOn with | _ x =>
  induction y using Quotient.inductionOn with | _ y =>
  apply Subtype.ext
  have he' := congrArg Subtype.val he
  change projection principalSix (flagCollarParam F (x,0)).val =
    projection principalSix (flagCollarParam F (y,0)).val at he'
  change projection principalSix x.val = projection principalSix y.val
  simpa only [flagCollarParam_zero] using he'

/-- Every actual corner-orbit quotient has an embedded uniform signed strip in the boundary. -/
theorem flagCollarBase_exists_strip (F : Flag) :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding ((Set.univ ×ˢ Set.Ioo (-ε) ε).domRestrict (flagCollarBase F)) := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  exact CompactEmbeddingNeighborhood.exists_strip_open_embedding (flagCollarBase F)
    (flagCollarBase_continuous F) (flagCollarBase_open F)
    (flagCollarBase_zero_injective F) (fun x => flagCollarBase_locallyInjective F (x,0))

end TernaryPoly.SymmetricSpaceBoundaryMV
