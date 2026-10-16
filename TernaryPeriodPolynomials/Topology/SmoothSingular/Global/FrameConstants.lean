module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameCochains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameCoefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
open SymmetricSpaceCovering FreeActionLinearization CoveringSingularOrbits
open scoped Simplicial
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {U : Set OrbitSpace} {Y : TopCat.{0}} (T : SingularFrame DeckGroup (TopCat.of (CoverOpen U)) Y)

/-- A coefficient value is a genuine constant in the selected actual covering frame. -/
def frameConstantMap : F →ₗ[ℝ] coefficientSections ρ U :=
  (frameCoefficientExtension ρ T).comp (LocallyConstant.constₗ ℝ)

/-- The genuine constant frame section evaluates to the given value on the chosen lift. -/
theorem frameConstantMap_lift (c : F) (y : Y) :
    (frameConstantMap ρ T c).val (T.lift y) = c := by
  change ρ (T.label (T.lift y)) c = c
  rw [T.label_lift, map_one]
  rfl

/-- On a connected actual frame, every locally constant coefficient section is uniquely constant. -/
theorem frameConstantMap_bijective [ConnectedSpace Y] : Function.Bijective (frameConstantMap ρ T) := by
  constructor
  · intro c d h
    let y : Y := Classical.arbitrary Y
    have he := congrArg (fun f : coefficientSections ρ U => f.val (T.lift y)) h
    exact (frameConstantMap_lift ρ T c y).symm.trans (he.trans (frameConstantMap_lift ρ T d y))
  · intro f
    obtain ⟨c, hc⟩ := (frameCoefficientRestriction ρ T f).exists_eq_const
    refine ⟨c, ?_⟩
    change frameCoefficientExtension ρ T (LocallyConstant.const Y c) = f
    rw [← hc, frameCoefficientExtension_restriction]

/-- The true constant-frame map is a real-linear equivalence on connected local frames. -/
def frameConstantEquiv [ConnectedSpace Y] : F ≃ₗ[ℝ] coefficientSections ρ U :=
  LinearEquiv.ofBijective (frameConstantMap ρ T) (frameConstantMap_bijective ρ T)

/-- The actual ordinary constant singular cochain evaluates to its coefficient on each vertex. -/
theorem ordinaryFunctionEquiv_singularConstant (X : TopCat.{0}) (M : ModuleCat.{0} ℝ)
    (c : M) (σ : SingularSimplex X 0) :
    ordinaryFunctionEquiv X M 0 (SmoothSingularComparison.singularConstant X M c) σ = c := by
  change (SmoothSingularComparison.realSingularSum X
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) 1)) • c = c
  have h := congrArg (fun m => m.hom 1) (SmoothSingularComparison.realSingularSum_generator X σ)
  exact (congrArg (fun r : ℝ => r • c) h).trans (one_smul ℝ c)

/-- The genuine local frame identifies the actual singular coefficient augmentation with the
ordinary constant singular augmentation on every coefficient value. -/
theorem frameCochainRestriction_constant (c : F) :
    (frameCochainRestriction T (Rep.of ρ)).f 0
      (coefficientSingularMap ρ U (frameConstantMap ρ T c)) =
        SmoothSingularComparison.singularConstant Y (ModuleCat.of ℝ F) c := by
  apply (ordinaryFunctionEquiv Y (ModuleCat.of ℝ F) 0).injective
  funext σ
  calc
    _ = cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen U)) (Rep.of ρ) 0
        (coefficientSingularMap ρ U (frameConstantMap ρ T c)) (projection T.lift 0 σ) :=
      frameCochainRestriction_evaluate T (Rep.of ρ) 0 _ σ
    _ = (frameConstantMap ρ T c).val
        (TopCat.toSSetObjEquiv _ (.op ⦋0⦌) (projection T.lift 0 σ) (vertex 0)) :=
      coefficientSingularMap_eval ρ U _ _
    _ = c := frameConstantMap_lift ρ T c _
    _ = _ := (ordinaryFunctionEquiv_singularConstant Y (ModuleCat.of ℝ F) c σ).symm

end TernaryPoly.SmoothSingularGlobal
