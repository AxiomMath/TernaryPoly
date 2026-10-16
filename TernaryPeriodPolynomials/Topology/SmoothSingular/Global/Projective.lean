module

/- Adapted from the rational predecessor EquivariantSingularResolutionProjective.lean by explicit base-ring
replacement to ℝ and the actual SmoothSingularGlobal chain model. -/
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Chains

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial MonoidAlgebra
namespace TernaryPoly.SmoothSingularGlobal
open FreeActionLinearization

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- The actual categorical coproduct of singular generators is the concrete finitely supported module. -/
def degreeFinsuppIso (n : ℕ) :
    (underlyingChains X).X n ≅ ModuleCat.of ℝ (SingularSimplex X n →₀ ℝ) :=
  (TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n |>.coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℝ ℝ (SingularSimplex X n))

/-- The inverse comparison sends a basis coefficient to its literal singular-chain generator. -/
theorem degreeFinsuppIso_inv_single (n : ℕ) (σ : SingularSimplex X n) (r : ℝ) :
    (degreeFinsuppIso X n).inv (Finsupp.single σ r)=
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) r := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_inv
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℝ ℝ) n)
    (ModuleCat.finsuppCoconeIsColimit ℝ ℝ (SingularSimplex X n)) ⟨σ⟩
  exact congrArg (fun f => f r) h

/-- The comparison uses precisely the group-algebra coefficient wrapper of the permutation representation. -/
def degreeLinearEquiv (n : ℕ) : ℝ[SingularSimplex X n] ≃ₗ[ℝ] (underlyingChains X).X n :=
  MonoidAlgebra.coeffLinearEquiv ℝ ≪≫ₗ (degreeFinsuppIso X n).symm.toLinearEquiv

@[simp] theorem degreeLinearEquiv_single (n : ℕ) (σ : SingularSimplex X n) (r : ℝ) :
    degreeLinearEquiv X n (MonoidAlgebra.single σ r)=((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) r := by
  change (degreeFinsuppIso X n).inv (Finsupp.single σ r)=_
  exact degreeFinsuppIso_inv_single X n σ r

/-- The actual categorical chain representation is equivariantly the literal singular permutation representation. -/
def degreeEquiv (n : ℕ) :
    (Representation.ofMulAction ℝ G (SingularSimplex X n)).Equiv (chainAction G X n) :=
  .mk (degreeLinearEquiv X n) fun g => by
    apply MonoidAlgebra.lhom_ext'
    intro σ
    apply LinearMap.ext
    intro r
    change degreeLinearEquiv X n (Representation.ofMulAction ℝ G (SingularSimplex X n) g
      (MonoidAlgebra.single σ r)) =
      chainAction G X n g (degreeLinearEquiv X n (MonoidAlgebra.single σ r))
    rw [Representation.ofMulAction_single,degreeLinearEquiv_single,degreeLinearEquiv_single]
    exact (congrArg (fun f => f r) (generator_smul G X n σ g)).symm

def degreeRepIso (n : ℕ) : Rep.ofMulAction ℝ G (SingularSimplex X n) ≅ chainRep G X n :=
  Rep.mkIso (degreeEquiv G X n)

/-- Freeness of the space action gives projectivity of every actual singular-chain representation. -/
instance chainRep_projective [IsCancelSMul G X] (n : ℕ) : Projective (chainRep G X n) :=
  Projective.of_iso (degreeRepIso G X n)
    (singular_permutation_projective ℝ G X n)

end TernaryPoly.SmoothSingularGlobal
