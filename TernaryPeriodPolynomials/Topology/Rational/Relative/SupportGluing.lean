module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportLES

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- A pair of actual relative classes glues exactly when its literal difference vanishes. -/
theorem compatible_iff_glues (U V : Opens X) (k : ℕ)
    (z : ((relativeChains (U : Set X)).homology k ⊞ (relativeChains (V : Set X)).homology k : ModuleCat ℚ)) :
    homologyRestrictionDifference (U : Set X) (V : Set X) k z = 0 ↔
      ∃ x, homologyRestrictionPair (U : Set X) (V : Set X) k x = z :=
  exact_lift_iff _ _ _ (homology_exact_pair U V k) z

/-- The obstruction to uniqueness is precisely the image of the preceding genuine connecting map. -/
theorem restrictionPair_kernel_eq_connecting_range (U V : Opens X) (k : ℕ) :
    LinearMap.ker (homologyRestrictionPair (U : Set X) (V : Set X) k).hom =
      LinearMap.range (supportConnecting U V k).hom :=
  (homology_exact_union U V k).moduleCat_range_eq_ker.symm

/-- Gluing is unique precisely when the preceding connecting map is zero. -/
theorem restrictionPair_injective_iff_connecting_zero (U V : Opens X) (k : ℕ) :
    Function.Injective (homologyRestrictionPair (U : Set X) (V : Set X) k) ↔
      supportConnecting U V k = 0 := by
  rw [← LinearMap.ker_eq_bot, restrictionPair_kernel_eq_connecting_range, LinearMap.range_eq_bot]
  exact ModuleCat.hom_ext_iff.symm

/-- Vanishing of intersection-supported homology one degree higher guarantees unique gluing of every compatible pair. -/
theorem compatible_glues_uniquely (U V : Opens X) (k : ℕ)
    (h : IsZero ((relativeChains ((U : Set X) ∪ V)).homology (k+1)))
    (z : ((relativeChains (U : Set X)).homology k ⊞ (relativeChains (V : Set X)).homology k : ModuleCat ℚ))
    (hz : homologyRestrictionDifference (U : Set X) (V : Set X) k z = 0) :
    ∃! x, homologyRestrictionPair (U : Set X) (V : Set X) k x = z := by
  obtain ⟨x, hx⟩ := (compatible_iff_glues U V k z).mp hz
  have hi : Function.Injective (homologyRestrictionPair (U : Set X) (V : Set X) k) :=
    (restrictionPair_injective_iff_connecting_zero U V k).mpr (h.eq_of_src _ _)
  exact ⟨x, hx, fun y hy => hi (hy.trans hx.symm)⟩

/-- If degree-k intersection-supported homology also vanishes, every pair is compatible and glues uniquely. -/
theorem all_pairs_glue_uniquely (U V : Opens X) (k : ℕ)
    (hnext : IsZero ((relativeChains ((U : Set X) ∪ V)).homology (k+1)))
    (hcurrent : IsZero ((relativeChains ((U : Set X) ∪ V)).homology k))
    (z : ((relativeChains (U : Set X)).homology k ⊞ (relativeChains (V : Set X)).homology k : ModuleCat ℚ)) :
    ∃! x, homologyRestrictionPair (U : Set X) (V : Set X) k x = z := by
  apply compatible_glues_uniquely U V k hnext z
  have hzero : homologyRestrictionDifference (U : Set X) (V : Set X) k = 0 := hcurrent.eq_of_tgt _ _
  rw [hzero]
  rfl

end TernaryPoly.RationalRelativeSupport
