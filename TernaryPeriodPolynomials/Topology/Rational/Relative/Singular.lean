module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainSequence
public import TernaryPeriodPolynomials.Topology.Rational.SubspaceAugmentation

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalSingularAugmentation SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
variable {X : Type} [TopologicalSpace X]

/-- The literal chain map of a subspace inclusion. -/
abbrev inclusion (S : Set X) : chains S ⟶ chains X :=
  chainMap ⟨Subtype.val, continuous_subtype_val⟩

/-- Subspace chains inject in every degree. -/
theorem inclusion_injective (S : Set X) (n : ℕ) :
    Function.Injective ((inclusion S).f n).hom :=
  singularChainMap_injective_of_pushSimplex_injective
    (sInclusion (X := TopCat.of X) S) n (pushSimplex_sInclusion_injective (X := TopCat.of X) S n)

instance inclusion_f_mono (S : Set X) (n : ℕ) : Mono ((inclusion S).f n) :=
  (ModuleCat.mono_iff_injective _).mpr (inclusion_injective S n)

instance inclusion_mono (S : Set X) : Mono (inclusion S) :=
  mono_of_mono_f _ (fun _ => inferInstance)

/-- Actual rational relative singular chains are the cokernel of literal subspace inclusion. -/
abbrev relativeChains (S : Set X) := RelativeChainSequence.relative (inclusion S)

/-- The actual degree-lowering relative boundary homomorphism. -/
abbrev connecting (S : Set X) (k : ℕ) := RelativeChainSequence.connecting (inclusion S) k

/-- For a contractible ambient space, the actual connecting map is an isomorphism in every
positive lower degree. No contractibility of the subspace is assumed. -/
def relativeSuccIso [ContractibleSpace X] (S : Set X) (k : ℕ) (hk : k ≠ 0) :
    (relativeChains S).homology (k+1) ≅ (chains S).homology k := by
  have : IsIso (connecting S k) :=
    isIso_shortExact_δ ℚ (RelativeChainSequence.shortExact (inclusion S)) (k+1) k rfl
      (homology_isZero (X := X) (k+1) (by omega)) (homology_isZero (X := X) k hk)
  exact asIso (connecting S k)

@[simp] theorem relativeSuccIso_hom [ContractibleSpace X] (S : Set X) (k : ℕ) (hk : k ≠ 0) :
    (relativeSuccIso S k hk).hom = connecting S k := rfl

end TernaryPoly.RationalRelativeSingular
