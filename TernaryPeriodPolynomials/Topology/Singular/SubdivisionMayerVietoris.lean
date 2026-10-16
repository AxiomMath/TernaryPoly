module

public import TernaryPeriodPolynomials.Topology.Singular.SubdivisionBridge
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularSubdivision
open CategoryTheory Limits TopologicalSpace
open SphereOddDegree
open ContractibleSingularHomology
variable (X : Type) [TopologicalSpace X]

/-- Inclusion identifies chains of an actual subspace with its supported ambient chains. -/
def subspaceChainIso (S : Set X) :
    chains S ≅ subChainComplex ℚ (TopCat.of X) S :=
  asIso (subChainCorestrict ℚ (TopCat.of X) S)

@[simp] theorem subspaceChainIso_hom (S : Set X) :
    (subspaceChainIso X S).hom = subChainCorestrict ℚ (TopCat.of X) S := rfl

/-- The supported-chain homology is literally the rational homology of the subspace. -/
def supportedHomologyIso (S : Set X) (n : ℕ) :
    (subChainComplex ℚ (TopCat.of X) S).homology n ≅ (chains S).homology n :=
  subspaceHomologyIso (R := ℚ) (X := TopCat.of X) S n

/-- Rational Mayer–Vietoris, with vanishing hypotheses on the actual subspaces. -/
def mayerVietorisHomologyIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUi : IsZero ((chains U).homology (n + 1)))
    (hVi : IsZero ((chains V).homology (n + 1)))
    (hUj : IsZero ((chains U).homology n))
    (hVj : IsZero ((chains V).homology n)) :
    (chains X).homology (n + 1) ≅ (chains (↥((U : Set X) ∩ (V : Set X)))).homology n :=
  mvHomologyIso_succ ℚ (X := TopCat.of X) U V hUV n
    (hUi.of_iso (supportedHomologyIso X U (n + 1)))
    (hVi.of_iso (supportedHomologyIso X V (n + 1)))
    (hUj.of_iso (supportedHomologyIso X U n))
    (hVj.of_iso (supportedHomologyIso X V n)) ≪≫
    supportedHomologyIso X ((U : Set X) ∩ (V : Set X)) n

/-- The isomorphism uses the actual short-exact-sequence connecting map. -/
theorem mayerVietorisHomologyIso_hom (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUi : IsZero ((chains U).homology (n + 1)))
    (hVi : IsZero ((chains V).homology (n + 1)))
    (hUj : IsZero ((chains U).homology n))
    (hVj : IsZero ((chains V).homology n)) :
    (mayerVietorisHomologyIso X U V hUV n hUi hVi hUj hVj).hom =
      (smallChains_homologyIso ℚ (TopCat.of X) (twoSetCover (X := TopCat.of X) U V hUV) (n + 1)).inv ≫
        (mvShortExact ℚ (X := TopCat.of X) U V hUV).δ (n + 1) n (by simp [ComplexShape.down_Rel]) ≫
        (supportedHomologyIso X ((U : Set X) ∩ (V : Set X)) n).hom := by
  exact Category.assoc _ _ _

/-- Contractible members of a two-open cover give the positive-degree connecting isomorphism. -/
def mayerVietorisContractibleIso (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    (chains X).homology (n + 1) ≅ (chains (↥((U : Set X) ∩ (V : Set X)))).homology n :=
  mayerVietorisHomologyIso X U V hUV n
    (homology_isZero (n + 1) (Nat.succ_ne_zero n))
    (homology_isZero (n + 1) (Nat.succ_ne_zero n))
    (homology_isZero n hn) (homology_isZero n hn)

end TernaryPoly.SingularSubdivision
