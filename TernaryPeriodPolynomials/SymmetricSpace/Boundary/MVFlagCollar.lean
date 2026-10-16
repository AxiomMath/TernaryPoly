module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVArithmeticNormal
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVCornerQuotient

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open OrdinaryIncidence SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryFaceModels
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction SymmetricSpaceBorelCorner
  SymmetricSpaceGluedArithmetic Topology
open IntegralGL3Congruence
open scoped Pointwise

/-- The arithmetic Borel extension is the literal action in the chosen actual rational chart. -/
theorem framedBorel_chart (a : RationalGL) (g : arithmeticBorel a) (p : Corner) :
    integralAction g.val (chart a p) = chart a (extend (framedBorel a g) p) := by
  have hr : changeMatrix (integralRational g.val * a) a = (framedBorel a g).val := by
    change realRational (a⁻¹ * (integralRational g.val * a)) = framedIntegral a g.val
    rw [framedIntegral_apply]
    simp only [relative, mul_assoc]
  have hd : p ∈ domain (framedBorel a g).val :=
    (mem_domain_iff _ p).mpr ⟨Or.inr (framedBorel a g).property.2,
      Or.inr (framedBorel a g).property.1⟩
  have hp : p ∈ overlap (integralRational g.val * a) a := by
    change p ∈ domain (changeMatrix (integralRational g.val * a) a)
    rwa [hr]
  rw [integralAction_chart]
  apply (chart_eq_iff _ a p _).mpr
  refine ⟨hp, ?_⟩
  change (transition (changeMatrix (integralRational g.val * a) a) ⟨p, hp⟩).val = _
  rw [transition_congr hr ⟨p, hp⟩ ⟨p, hd⟩ rfl, transition_borel]

/-- A chosen frame for each actual incident rational flag. -/
def chosenFrame (F : Flag) : RationalGL :=
  (exists_frame_for_incident F.val.1 F.val.2 F.property).choose

theorem chosenFrame_spec (F : Flag) :
    lineLabel (chosenFrame F) = F.val.1 ∧ planeLabel (chosenFrame F) = F.val.2 :=
  (exists_frame_for_incident F.val.1 F.val.2 F.property).choose_spec

def flagCoordinates (F : Flag) : Vec3 ≃ₜ flagFace F :=
  flagHomeomorph F.val.1 F.val.2 (chosenFrame F) (chosenFrame_spec F).1 (chosenFrame_spec F).2

@[simp] theorem flagCoordinates_val (F : Flag) (u : Vec3) :
    (flagCoordinates F u).val = chart (chosenFrame F) (u, zeroRoot, zeroRoot) := rfl

/-- The true principal-six corner stabilizer is contained in the chosen arithmetic Borel. -/
theorem flagStabilizer_mem_arithmetic (F : Flag)
    (k : MulAction.stabilizer principalSix (flagFace F)) :
    k.val.val ∈ arithmeticBorel (chosenFrame F) := by
  have h0 : chart (chosenFrame F) origin ∈ flagFace F :=
    ⟨(lineFace_chart_iff _ _ _).mpr ⟨rfl, (chosenFrame_spec F).1⟩,
      (planeFace_chart_iff _ _ _).mpr ⟨rfl, (chosenFrame_spec F).2⟩⟩
  have hk : k.val • chart (chosenFrame F) origin ∈ flagFace F :=
    k.property.subset ⟨_, h0, rfl⟩
  change integralAction k.val.val (chart (chosenFrame F) origin) ∈ flagFace F at hk
  rw [integralAction_chart, flagFace_chart_iff] at hk
  have hF : flagLabel (chosenFrame F) = F :=
    Subtype.ext (Prod.ext (chosenFrame_spec F).1 (chosenFrame_spec F).2)
  have hl := congrArg (fun G : Flag => G.val.1) (hk.2.trans hF.symm)
  have hp := congrArg (fun G : Flag => G.val.2) (hk.2.trans hF.symm)
  have hb : changeMatrix (integralRational k.val.val * chosenFrame F) (chosenFrame F) ∈ borelStabilizer :=
    ⟨(planeLabel_eq_iff _ _).mp hp, (lineLabel_eq_iff _ _).mp hl⟩
  change framedIntegral (chosenFrame F) k.val.val ∈ borelStabilizer
  rw [framedIntegral_apply]
  simpa only [changeMatrix, relative, mul_assoc] using hb

def flagStabilizerBorel (F : Flag) (k : MulAction.stabilizer principalSix (flagFace F)) :
    arithmeticBorel (chosenFrame F) := ⟨k.val.val, flagStabilizer_mem_arithmetic F k⟩

/-- The actual flag-face coordinates transform by the existing root-independent Borel shear. -/
theorem flagCoordinates_smul (F : Flag) (k : MulAction.stabilizer principalSix (flagFace F))
    (u : Vec3) :
    k • flagCoordinates F u = flagCoordinates F
      (shear (framedBorel (chosenFrame F) (flagStabilizerBorel F k)) u) := by
  apply Subtype.ext
  change integralAction k.val.val (chart (chosenFrame F) (u, zeroRoot, zeroRoot)) = _
  have h := framedBorel_chart (chosenFrame F) (flagStabilizerBorel F k) (u, zeroRoot, zeroRoot)
  change integralAction k.val.val _ = _ at h
  rw [h, framedBorel_extend]
  rfl

def flagCollarParam (F : Flag) : (flagFace F × ℝ) → BoundaryCover :=
  signedParam (chosenFrame F) ∘ ((flagCoordinates F).symm.prodCongr (Homeomorph.refl ℝ))

theorem flagCollarParam_isOpenEmbedding (F : Flag) : IsOpenEmbedding (flagCollarParam F) :=
  (signedParam_isOpenEmbedding (chosenFrame F)).comp
    ((flagCoordinates F).symm.prodCongr (Homeomorph.refl ℝ)).isOpenEmbedding

/-- Its zero section is literally the full-flag inclusion into the actual upstairs boundary. -/
@[simp] theorem flagCollarParam_zero (F : Flag) (x : flagFace F) :
    (flagCollarParam F (x, 0)).val = x.val := by
  change (signedParam (chosenFrame F) ((flagCoordinates F).symm x, 0)).val = x.val
  rw [signedParam_zero, ←flagCoordinates_val]
  exact congrArg Subtype.val ((flagCoordinates F).apply_symm_apply x)

/-- The entire product chart is equivariant for the true corner stabilizer acting trivially
on its signed normal factor. -/
theorem flagCollarParam_equivariant (F : Flag)
    (k : MulAction.stabilizer principalSix (flagFace F)) (x : flagFace F) (s : ℝ) :
    flagCollarParam F (k • x, s) = k.val • flagCollarParam F (x, s) := by
  obtain ⟨u, rfl⟩ := (flagCoordinates F).surjective x
  rw [flagCoordinates_smul]
  apply Subtype.ext
  change chart (chosenFrame F)
    (signedAxesHomeomorph ((flagCoordinates F).symm (flagCoordinates F
      (shear (framedBorel (chosenFrame F) (flagStabilizerBorel F k)) u)), s)).val =
    integralAction k.val.val (chart (chosenFrame F)
      (signedAxesHomeomorph ((flagCoordinates F).symm (flagCoordinates F u), s)).val)
  simp only [Homeomorph.symm_apply_apply]
  have h := framedBorel_chart (chosenFrame F) (flagStabilizerBorel F k)
    (signedAxesHomeomorph (u, s)).val
  change integralAction k.val.val _ = _ at h
  rw [h, framedBorel_signedAxes]

end TernaryPoly.SymmetricSpaceBoundaryMV
