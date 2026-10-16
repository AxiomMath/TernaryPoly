module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Singular
public import TernaryPeriodPolynomials.Topology.Rational.SingularConnected
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalSingularAugmentation
variable {X : Type} [TopologicalSpace X]

/-- Inclusion between nonempty path-connected spaces induces an isomorphism on H0. -/
theorem inclusion_zero_isIso [PathConnectedSpace X] (S : Set X) [PathConnectedSpace S] :
    IsIso (homologyMap (inclusion S) 0) := by
  have := augmentation_isIso_of_pathConnected X
  have := augmentation_isIso_of_pathConnected S
  have h : homologyMap (inclusion S) 0 ≫ augmentation X = augmentation S :=
    naturality ⟨Subtype.val,continuous_subtype_val⟩
  have : IsIso (homologyMap (inclusion S) 0 ≫ augmentation X) := by rw [h]; infer_instance
  exact (isIso_comp_right_iff _ _).mp this

/-- H0 of the actual relative pair vanishes when the nonempty subspace and ambient space
are path connected. -/
theorem relative_zero_isZero [PathConnectedSpace X] (S : Set X) [PathConnectedSpace S] :
    IsZero ((relativeChains S).homology 0) := by
  have := inclusion_zero_isIso S
  exact (exactAt_iff_isZero_homology _ _).mp
    ((RelativeChainSequence.shortExact (inclusion S)).exactAt_X₃ 0 (by change Epi (homologyMap (inclusion S) 0); infer_instance)
      (fun j hj => by change j+1=0 at hj; omega))

/-- H1 of the actual relative pair vanishes for a contractible ambient space and
path-connected nonempty subspace. -/
theorem relative_one_isZero [ContractibleSpace X] (S : Set X) [PathConnectedSpace S] :
    IsZero ((relativeChains S).homology 1) := by
  have := inclusion_zero_isIso S
  have hE : Epi (homologyMap (inclusion S) 1) :=
    (homology_isZero (X := X) 1 (by decide)).epi _
  exact (exactAt_iff_isZero_homology _ _).mp
    ((RelativeChainSequence.shortExact (inclusion S)).exactAt_X₃ 1 hE
      (fun j hj => by
        have hj0 : j=0 := by change j+1=1 at hj; omega
        subst j
        change Mono (homologyMap (inclusion S) 0)
        infer_instance))

end TernaryPoly.RationalRelativeSingular
