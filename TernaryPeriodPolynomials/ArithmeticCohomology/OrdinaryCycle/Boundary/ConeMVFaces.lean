module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMV

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

/-- Literal restriction on actual group H1, along B → P. -/
def restrictionP : groupCohomology.H1 (faceP A P) →ₗ[ℚ] groupCohomology.H1 (corner A P Q) :=
  (groupCohomology.map (intoP P Q) (𝟙 (corner A P Q)) 1).hom

/-- Literal restriction on actual group H1, along B → Q. -/
def restrictionQ : groupCohomology.H1 (faceQ A Q) →ₗ[ℚ] groupCohomology.H1 (corner A P Q) :=
  (groupCohomology.map (intoQ P Q) (𝟙 (corner A P Q)) 1).hom

def restrictedP (a : cocycles₁ (faceP A P)) : cocycles₁ (corner A P Q) :=
  groupCohomology.mapCocycles₁ (intoP P Q) (𝟙 (corner A P Q)) a

def restrictedQ (a : cocycles₁ (faceQ A Q)) : cocycles₁ (corner A P Q) :=
  groupCohomology.mapCocycles₁ (intoQ P Q) (𝟙 (corner A P Q)) a

@[simp] theorem restrictedP_apply (a : cocycles₁ (faceP A P)) (b : (P ⊓ Q : Subgroup G)) :
    restrictedP A P Q a b = a (intoP P Q b) := rfl

@[simp] theorem restrictedQ_apply (a : cocycles₁ (faceQ A Q)) (b : (P ⊓ Q : Subgroup G)) :
    restrictedQ A P Q a b = a (intoQ P Q b) := rfl

@[simp] theorem restrictionP_H1π (a : cocycles₁ (faceP A P)) :
    restrictionP A P Q (H1π (faceP A P) a) = H1π (corner A P Q) (restrictedP A P Q a) :=
  H1π_comp_map_apply (A := faceP A P) (B := corner A P Q)
    (intoP P Q) (𝟙 (corner A P Q)) a

@[simp] theorem restrictionQ_H1π (a : cocycles₁ (faceQ A Q)) :
    restrictionQ A P Q (H1π (faceQ A Q) a) = H1π (corner A P Q) (restrictedQ A P Q a) :=
  H1π_comp_map_apply (A := faceQ A Q) (B := corner A P Q)
    (intoQ P Q) (𝟙 (corner A P Q)) a

/-- The final map in the degree-zero/one MV segment is the difference of actual restrictions. -/
def restrictionDifference : FaceH1 A P Q →ₗ[ℚ] groupCohomology.H1 (corner A P Q) :=
  (restrictionP A P Q).comp (LinearMap.fst ℚ _ _) -
    (restrictionQ A P Q).comp (LinearMap.snd ℚ _ _)

@[simp] theorem restrictionDifference_faceClasses (c : Z1 A P Q) :
    restrictionDifference A P Q (faceClasses A P Q c) = 0 := by
  change restrictionP A P Q (H1π (faceP A P) (cycleP A P Q c)) -
    restrictionQ A P Q (H1π (faceQ A Q) (cycleQ A P Q c)) = 0
  rw [restrictionP_H1π,restrictionQ_H1π,← map_sub,H1π_eq_zero_iff]
  refine ⟨c.val.2.2,funext fun b => ?_⟩
  exact ((mem_Z1_iff A P Q c.val).mp c.property).2.2 b

/-- Compatible actual face classes lift to a cone class, with the genuine coboundary primitive. -/
theorem compatible_faces_lift (x : FaceH1 A P Q)
    (hx : restrictionDifference A P Q x = 0) : ∃ y, toFaces A P Q y = x := by
  rcases x with ⟨xP,xQ⟩
  induction xP using H1_induction_on with | h aP => ?_
  induction xQ using H1_induction_on with | h aQ => ?_
  change restrictionP A P Q (H1π (faceP A P) aP) -
    restrictionQ A P Q (H1π (faceQ A Q) aQ) = 0 at hx
  rw [restrictionP_H1π,restrictionQ_H1π,← map_sub,H1π_eq_zero_iff] at hx
  obtain ⟨u,hu⟩ := hx
  let c : Z1 A P Q := ⟨(aP,aQ,u),(mem_Z1_iff A P Q _).mpr
    ⟨aP.property,aQ.property,fun b => congrFun hu b⟩⟩
  exact ⟨classOf A P Q c,rfl⟩

/-- Exactness of cone H1 → full face H1 → corner H1. -/
theorem range_toFaces_eq_ker_restrictionDifference :
    LinearMap.range (toFaces A P Q) = LinearMap.ker (restrictionDifference A P Q) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective (boundaries A P Q) y
    exact restrictionDifference_faceClasses A P Q c
  · exact compatible_faces_lift A P Q x

end TernaryPoly.OrdinaryBoundaryCone
