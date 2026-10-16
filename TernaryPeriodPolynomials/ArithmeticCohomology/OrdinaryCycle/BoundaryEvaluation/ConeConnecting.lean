module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConeCorner
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison Preadditive

variable {G : Type} [Group G] (S : ShortComplex (ChainComplex (Rep.{0} ℚ G) ℕ))

/-- The actual cone projection is the quotient of the unshifted face coordinate. -/
theorem coneProjection_degree_one : (Cone.projection S).f 1 = Cone.second S 1 ≫ S.g.f 1 := by
  unfold Cone.projection Cone.second
  rw [homotopyCofiber.desc_f _ _ _ 1 0 (Cone.downRel 0)]
  simp

/-- The differential of the face part of an actual cone cycle is minus its corner inclusion. -/
theorem coneCycles_face_boundary :
    (-(Cone.total S).iCycles 1 ≫ Cone.first S 0) ≫ S.f.f 0 =
      ((Cone.total S).iCycles 1 ≫ Cone.second S 1) ≫ S.X₂.d 1 0 := by
  have h := congrArg (fun t => (Cone.total S).iCycles 1 ≫ t) (Cone.d_second S 0)
  rw [← Category.assoc, iCycles_d, zero_comp, comp_add] at h
  rw [neg_comp, Category.assoc, Category.assoc]
  exact (neg_eq_iff_add_eq_zero).mpr h.symm

variable (hS : S.ShortExact) (W : Rep.{0} ℚ G)
  (a : S.X₁.X 0 ⟶ W) (ha : S.X₁.d 1 0 ≫ a = 0)

/-- The actual quotient connecting morphism evaluates as minus the shifted cone corner.
This sign follows from the actual lifted differential, independently of any cone isomorphism. -/
theorem coneProjection_connecting_evaluation :
    homologyMap (Cone.projection S) 1 ≫ hS.δ 1 0 rfl ≫
      evaluationOfCochain S.X₁ W 0 a ha = -coneCornerHomology S.f W a ha := by
  let z := (Cone.total S).iCycles 1 ≫ (Cone.projection S).f 1
  have hz : z ≫ S.X₃.d 1 0 = 0 := by
    dsimp [z]
    rw [Category.assoc, (Cone.projection S).comm, ← Category.assoc, iCycles_d, zero_comp]
  have hy : ((Cone.total S).iCycles 1 ≫ Cone.second S 1) ≫ S.g.f 1 = z := by
    dsimp [z]
    rw [coneProjection_degree_one, Category.assoc]
  have hδ := hS.δ_eq 1 0 rfl z hz
    ((Cone.total S).iCycles 1 ≫ Cone.second S 1) hy
    (-(Cone.total S).iCycles 1 ≫ Cone.first S 0) (coneCycles_face_boundary S) 0 (by simp)
  have hl : S.X₃.liftCycles z 0 ((ComplexShape.down ℕ).next_eq' (Cone.downRel 0)) hz =
      cyclesMap (Cone.projection S) 1 := by
    apply (cancel_mono (S.X₃.iCycles 1)).mp
    rw [liftCycles_i, cyclesMap_i]
  rw [hl] at hδ
  have he := congrArg (fun t => t ≫ evaluationOfCochain S.X₁ W 0 a ha) hδ
  simp only [Category.assoc, evaluationOfCochain_projection] at he
  rw [← Category.assoc (S.X₁.liftCycles _ _ _ _), liftCycles_i] at he
  apply (cancel_epi ((Cone.total S).homologyπ 1)).mp
  rw [← Category.assoc, homologyπ_naturality, Category.assoc, he,
    comp_neg, coneCornerHomology_projection]
  simp only [neg_comp, Category.assoc, Cone.first, CofiberSequence.first]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
