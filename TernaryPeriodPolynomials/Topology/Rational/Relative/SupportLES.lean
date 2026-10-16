module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportHomology
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportExactTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- The genuine relative-support boundary, obtained from the short exact small quotient chain sequence. -/
def supportConnecting (U V : Opens X) (k : ℕ) :
    (relativeChains ((U : Set X) ∪ V)).homology (k+1) ⟶
      (relativeChains ((U : Set X) ∩ V)).homology k :=
  (thirdHomologyIso U V (k+1)).inv ≫
    (quotientChainRow_shortExact (U : Set X) (V : Set X)).δ (k+1) k rfl ≫
      (firstHomologyIso (U : Set X) (V : Set X) k).hom

/-- The actual boundary comparison commutes with both literal homology isomorphisms. -/
theorem supportConnecting_comm (U V : Opens X) (k : ℕ) :
    (quotientChainRow_shortExact (U : Set X) (V : Set X)).δ (k+1) k rfl ≫
      (firstHomologyIso (U : Set X) (V : Set X) k).hom =
        (thirdHomologyIso U V (k+1)).hom ≫ supportConnecting U V k := by
  simp [supportConnecting]

/-- Consecutive unsigned restriction and difference maps compose to zero. -/
theorem restriction_pair_difference (U V : Opens X) (k : ℕ) :
    homologyRestrictionPair (U : Set X) (V : Set X) k ≫
      homologyRestrictionDifference (U : Set X) (V : Set X) k = 0 := by
  apply (cancel_epi (firstHomologyIso (U : Set X) (V : Set X) k).hom).mp
  rw [comp_zero, ← Category.assoc, ← firstHomology_comm, Category.assoc, ← middleHomology_comm,
    ← Category.assoc, ← homologyMap_comp, (quotientChainRow (U : Set X) (V : Set X)).zero,
    homologyMap_zero, zero_comp]

/-- The genuine connecting map is killed by the literal restriction pair. -/
theorem connecting_restriction_pair (U V : Opens X) (k : ℕ) :
    supportConnecting U V k ≫ homologyRestrictionPair (U : Set X) (V : Set X) k = 0 := by
  simp only [supportConnecting, Category.assoc]
  rw [← firstHomology_comm]
  erw [(quotientChainRow_shortExact (U : Set X) (V : Set X)).δ_comp_assoc, zero_comp, comp_zero]

/-- The literal difference map is killed by the genuine connecting map. -/
theorem restriction_difference_connecting (U V : Opens X) (k : ℕ) :
    homologyRestrictionDifference (U : Set X) (V : Set X) (k+1) ≫ supportConnecting U V k = 0 := by
  apply (cancel_epi (middleHomologyIso (U : Set X) (V : Set X) (k+1)).hom).mp
  rw [comp_zero, ← Category.assoc, ← middleHomology_comm]
  simp only [supportConnecting, Category.assoc, Iso.hom_inv_id_assoc]
  erw [← Category.assoc, (quotientChainRow_shortExact (U : Set X) (V : Set X)).comp_δ, zero_comp]

/-- Exactness at the direct sum of actual relative homology groups. -/
theorem homology_exact_pair (U V : Opens X) (k : ℕ) :
    (ShortComplex.mk _ _ (restriction_pair_difference U V k)).Exact :=
  exact_transport _ ((quotientChainRow_shortExact (U : Set X) (V : Set X)).homology_exact₂ k)
    (firstHomologyIso (U : Set X) (V : Set X) k) (middleHomologyIso (U : Set X) (V : Set X) k)
    (thirdHomologyIso U V k) _ _ _ (firstHomology_comm _ _ _) (middleHomology_comm _ _ _)

/-- Exactness at actual union-supported relative homology. -/
theorem homology_exact_union (U V : Opens X) (k : ℕ) :
    (ShortComplex.mk _ _ (connecting_restriction_pair U V k)).Exact :=
  exact_transport _ ((quotientChainRow_shortExact (U : Set X) (V : Set X)).homology_exact₁ (k+1) k rfl)
    (thirdHomologyIso U V (k+1)) (firstHomologyIso (U : Set X) (V : Set X) k)
    (middleHomologyIso (U : Set X) (V : Set X) k) _ _ _
    (supportConnecting_comm _ _ _) (firstHomology_comm _ _ _)

/-- Exactness at actual positive-degree intersection-supported relative homology. -/
theorem homology_exact_intersection (U V : Opens X) (k : ℕ) :
    (ShortComplex.mk _ _ (restriction_difference_connecting U V k)).Exact :=
  exact_transport _ ((quotientChainRow_shortExact (U : Set X) (V : Set X)).homology_exact₃ (k+1) k rfl)
    (middleHomologyIso (U : Set X) (V : Set X) (k+1)) (thirdHomologyIso U V (k+1))
    (firstHomologyIso (U : Set X) (V : Set X) k) _ _ _
    (middleHomology_comm _ _ _) (supportConnecting_comm _ _ _)

end TernaryPoly.RationalRelativeSupport
