module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSimplexCover
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechFlagCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree Module
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

namespace InvariantSetCover
variable {G S ι : Type} [Group G] [MulAction G S] (U : InvariantSetCover G S ι)

/-- The actual empty Čech flag at a point. -/
def zeroFlag (s : S) : U.Flag 0 := ⟨Fin.elim0,s,fun a => Fin.elim0 a⟩

/-- Empty flags retain the actual group action on their points. -/
theorem zeroFlag_smul (g : G) (s : S) : U.zeroFlag (g • s) = g • U.zeroFlag s := rfl

/-- Every actual empty flag is determined by its genuine point. -/
theorem zeroFlag_point (x : U.Flag 0) : U.zeroFlag x.point = x := by
  apply Flag.ext
  · funext i
    exact Fin.elim0 i
  · rfl

end InvariantSetCover

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The literal allowed-simplex basis of the actual cover-small chain module. -/
abbrev coverSmallBasis (n : ℕ) :
    Basis (CoverSmallSimplex U hU hcover n) ℝ ((coveringSmallChains U hU Set.univ hcover).X n) :=
  predicateBasis (TopCat.of (CoverOpen Set.univ)) n (IsSmallSimplex (liftedOpenCover U hU Set.univ hcover))

/-- Actual deck action sends each genuine small-chain generator to its translated generator. -/
theorem coverSmallBasis_smul (n : ℕ) (g : DeckGroup) (σ : CoverSmallSimplex U hU hcover n) :
    ((coveringSmallChains U hU Set.univ hcover).X n).ρ g (coverSmallBasis U hU hcover n σ) =
      coverSmallBasis U hU hcover n (g • σ) := by
  apply Subtype.ext
  exact (congrArg (chainAction DeckGroup (TopCat.of (CoverOpen Set.univ)) n g)
    (predicateBasis_apply (TopCat.of (CoverOpen Set.univ)) n
      (IsSmallSimplex (liftedOpenCover U hU Set.univ hcover)) σ)).trans
    ((chainAction_generator DeckGroup (TopCat.of (CoverOpen Set.univ)) n g σ.val).trans
      (predicateBasis_apply (TopCat.of (CoverOpen Set.univ)) n
        (IsSmallSimplex (liftedOpenCover U hU Set.univ hcover)) (g • σ)).symm)

/-- Evaluate genuine small-singular Hom cochains on the actual empty small-simplex flags. -/
def smallCochainToFlags (n : ℕ) : (coveringSmallCochains ρ U hU Set.univ hcover).X n →ₗ[ℝ]
    (smallSimplexIndexCover U hU hcover n).flagCochains ρ 0 where
  toFun f := ⟨fun x => f.hom (coverSmallBasis U hU hcover n x.point),fun g x =>
    (congrArg (fun c => f.hom c) (coverSmallBasis_smul U hU hcover n g x.point)).symm.trans
      (congrArg (fun l => l (coverSmallBasis U hU hcover n x.point)) (f.hom.isIntertwining' g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend actual empty-flag functions on the genuine small-chain basis, obtaining an actual
representation morphism, with equivariance checked on that same literal basis. -/
def smallFlagExtend (n : ℕ) (w : (smallSimplexIndexCover U hU hcover n).flagCochains ρ 0) :
    (coveringSmallChains U hU Set.univ hcover).X n ⟶ Rep.of ρ :=
  Rep.ofHom ⟨(coverSmallBasis U hU hcover n).constr ℝ
    (fun σ => w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag σ)),fun g => by
      apply (coverSmallBasis U hU hcover n).ext
      intro σ
      change (coverSmallBasis U hU hcover n).constr ℝ
        (fun σ => w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag σ))
          (((coveringSmallChains U hU Set.univ hcover).X n).ρ g (coverSmallBasis U hU hcover n σ)) = _
      rw [coverSmallBasis_smul,Basis.constr_basis]
      change w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag (g • σ)) =
        ρ g ((coverSmallBasis U hU hcover n).constr ℝ
          (fun σ => w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag σ)) (coverSmallBasis U hU hcover n σ))
      rw [Basis.constr_basis]
      exact w.property g ((smallSimplexIndexCover U hU hcover n).zeroFlag σ)⟩

/-- The genuine small-chain extension evaluates to the original actual empty-flag function. -/
theorem smallCochainToFlags_extend (n : ℕ)
    (w : (smallSimplexIndexCover U hU hcover n).flagCochains ρ 0) :
    smallCochainToFlags ρ U hU hcover n (smallFlagExtend ρ U hU hcover n w) = w := by
  apply Subtype.ext
  funext x
  change (coverSmallBasis U hU hcover n).constr ℝ
    (fun σ => w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag σ)) (coverSmallBasis U hU hcover n x.point) = w.val x
  rw [Basis.constr_basis]
  exact congrArg w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag_point x)

/-- Actual small-singular Hom cochains are determined by literal empty-flag evaluation. -/
theorem smallCochainToFlags_injective (n : ℕ) : Function.Injective (smallCochainToFlags ρ U hU hcover n) := by
  intro f g h
  apply (forget₂ (Rep ℝ DeckGroup) (ModuleCat ℝ)).map_injective
  apply ModuleCat.hom_ext
  apply (coverSmallBasis U hU hcover n).ext
  intro σ
  exact congrArg (fun w => w.val ((smallSimplexIndexCover U hU hcover n).zeroFlag σ)) h

/-- The genuine small-singular Hom term is exactly the actual equivariant empty-flag-function term. -/
def smallCochainFlagEquiv (n : ℕ) : (coveringSmallCochains ρ U hU Set.univ hcover).X n ≃ₗ[ℝ]
    (smallSimplexIndexCover U hU hcover n).flagCochains ρ 0 :=
  LinearEquiv.ofBijective (smallCochainToFlags ρ U hU hcover n)
    ⟨smallCochainToFlags_injective ρ U hU hcover n,
      fun w => ⟨smallFlagExtend ρ U hU hcover n w,smallCochainToFlags_extend ρ U hU hcover n w⟩⟩

end TernaryPoly.SmoothSingularGlobal
