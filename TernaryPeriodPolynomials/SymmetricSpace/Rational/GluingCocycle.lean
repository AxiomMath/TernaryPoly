module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingTransitions

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates
open TopologicalSpace Topology

/-- Every subtype containing the actual dense interior has a dense actual Space parametrization. -/
def liftInterior (A : Set Corner) (hA : cornerInterior ⊆ A) (S : Space) : A :=
  ⟨cornerEmbedding S,hA (cornerHomeomorph S).property⟩

theorem denseRange_liftInterior (A : Set Corner) (hA : cornerInterior ⊆ A) :
    DenseRange (liftInterior A hA) := by
  rw [DenseRange,Subtype.dense_iff]
  have hi : Subtype.val '' Set.range (liftInterior A hA)=cornerInterior := by
    rw [←Set.range_comp]
    exact cornerEmbedding_range
  rw [hi,cornerInterior_dense.closure_eq]
  exact Set.subset_univ _

theorem transition_one (p : domain 1) : (transition 1 p).val=p.val := by
  have h : (fun q : domain 1 => (transition 1 q).val)=Subtype.val :=
    (denseRange_liftInterior (domain 1) (interior_subset_domain 1)).equalizer
      (continuous_subtype_val.comp (transition 1).continuous) continuous_subtype_val (by
        funext S
        change (transition 1 (interiorPoint 1 S)).val=cornerEmbedding S
        rw [transition_interiorPoint,act_one])
  exact congrFun h p

/-- The actual common source of the r transition and the direct s*r transition. -/
def commonDomain (r s : RealGL) : Opens Corner := domain r ⊓ domain (s*r)

def commonFirst (r s : RealGL) (p : commonDomain r s) : domain r := ⟨p.val,p.property.1⟩
def commonDirect (r s : RealGL) (p : commonDomain r s) : domain (s*r) := ⟨p.val,p.property.2⟩
def commonSecond (r s : RealGL) (p : commonDomain r s) : domain s :=
  ⟨(transition r (commonFirst r s p)).val,transition_inter r s (commonFirst r s p) p.property.2⟩

theorem continuous_commonFirst (r s : RealGL) : Continuous (commonFirst r s) :=
  continuous_subtype_val.subtype_mk _
theorem continuous_commonDirect (r s : RealGL) : Continuous (commonDirect r s) :=
  continuous_subtype_val.subtype_mk _
theorem continuous_commonSecond (r s : RealGL) : Continuous (commonSecond r s) :=
  (continuous_subtype_val.comp ((transition r).continuous.comp (continuous_commonFirst r s))).subtype_mk _

theorem interior_subset_commonDomain (r s : RealGL) : cornerInterior ⊆ commonDomain r s :=
  fun _ hp => ⟨interior_subset_domain r hp,interior_subset_domain (s*r) hp⟩

theorem commonSecond_interior (r s : RealGL) (S : Space) :
    commonSecond r s (liftInterior (commonDomain r s) (interior_subset_commonDomain r s) S)=
      interiorPoint s (act r S) := by
  apply Subtype.ext
  exact transition_interiorPoint r S

/-- The genuine local extensions satisfy the cocycle identity on the full overlap intersection. -/
theorem transition_cocycle (r s : RealGL) (p : commonDomain r s) :
    (transition s (commonSecond r s p)).val=(transition (s*r) (commonDirect r s p)).val := by
  have h : (fun q : commonDomain r s => (transition s (commonSecond r s q)).val)=
      (fun q : commonDomain r s => (transition (s*r) (commonDirect r s q)).val) :=
    (denseRange_liftInterior (commonDomain r s) (interior_subset_commonDomain r s)).equalizer
      (continuous_subtype_val.comp ((transition s).continuous.comp (continuous_commonSecond r s)))
      (continuous_subtype_val.comp ((transition (s*r)).continuous.comp (continuous_commonDirect r s))) (by
        funext S
        dsimp only [Function.comp_apply]
        rw [commonSecond_interior,transition_interiorPoint]
        change cornerEmbedding (act s (act r S))=(transition (s*r) (interiorPoint (s*r) S)).val
        rw [transition_interiorPoint,act_mul])
  exact congrFun h p

/-- Elementwise form of the actual cocycle, ready for the gluing constructor. -/
theorem transition_cocycle_apply (r s : RealGL) (p : domain r) (hp : p.val∈domain (s*r)) :
    (transition s ⟨(transition r p).val,transition_inter r s p hp⟩).val=
      (transition (s*r) ⟨p.val,hp⟩).val :=
  transition_cocycle r s ⟨p.val,p.property,hp⟩

end TernaryPoly.SymmetricSpaceRationalGluing
