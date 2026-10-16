module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionSize

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates
open SymmetricSpaceParabolicCoordinates

/-- Expanded entries of the actual reverse LDL matrix. -/
theorem flagMatrix_explicit (x y z a b : ℝ) :
    flagMatrix x y z a b=!![a+x^2*b+z^2,x*b+z*y,z;
      x*b+y*z,b+y^2,y;z,y,1] := by
  rw [flagMatrix_eq_assemble]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [assemble,binaryLDL] <;> ring

theorem height_normalize_flag (x y z a b : ℝ) :
    height (SymmetricSpacePositive.normalize (flagMatrix x y z a b))=
      (flagMatrix x y z a b).trace⁻¹ := by
  change (flagMatrix x y z a b).trace⁻¹*flagMatrix x y z a b 2 2=_
  rw [flagMatrix_explicit]
  simp

/-- Actual normalized representatives retain the positive scalar equal to their last entry. -/
theorem space_eq_height_flag (T : Space) :
    T.val=height T.val • flagMatrix ((ldlHomeomorph T).1 0) ((ldlHomeomorph T).1 1)
      ((ldlHomeomorph T).1 2) (ldlHomeomorph T).2.1.val (ldlHomeomorph T).2.2.val := by
  have he : SymmetricSpacePositive.normalize
      (flagMatrix ((ldlHomeomorph T).1 0) ((ldlHomeomorph T).1 1)
      ((ldlHomeomorph T).1 2) (ldlHomeomorph T).2.1.val (ldlHomeomorph T).2.2.val)=T.val := by
    rw [←ldlHomeomorph_symm,ldlHomeomorph.symm_apply_apply]
  have hh : height T.val=(flagMatrix ((ldlHomeomorph T).1 0) ((ldlHomeomorph T).1 1)
      ((ldlHomeomorph T).1 2) (ldlHomeomorph T).2.1.val (ldlHomeomorph T).2.2.val).trace⁻¹ :=
    (congrArg height he.symm).trans (height_normalize_flag _ _ _ _ _)
  calc
    T.val=SymmetricSpacePositive.normalize
      (flagMatrix ((ldlHomeomorph T).1 0) ((ldlHomeomorph T).1 1)
      ((ldlHomeomorph T).1 2) (ldlHomeomorph T).2.1.val (ldlHomeomorph T).2.2.val) := he.symm
    _=_ := by rw [hh]; rfl

theorem gram_eq_positive_flag (S : Space) (g : IntegralGL) :
    ∃ c : ℝ, 0<c ∧ conjugate (realIntegral g) S.val=
      c • flagMatrix ((ldlCoordinates S g).1 0) ((ldlCoordinates S g).1 1)
        ((ldlCoordinates S g).1 2) (ldlCoordinates S g).2.1.val (ldlCoordinates S g).2.2.val := by
  refine ⟨scale g S*height (act (realIntegral g) S).val,
    mul_pos (scale_pos g S) (height_pos _ (act (realIntegral g) S).property.1),?_⟩
  calc
    _=scale g S • (act (realIntegral g) S).val := conjugate_eq_scale_smul g S
    _=scale g S • (height (act (realIntegral g) S).val •
      flagMatrix ((ldlCoordinates S g).1 0) ((ldlCoordinates S g).1 1)
        ((ldlCoordinates S g).1 2) (ldlCoordinates S g).2.1.val (ldlCoordinates S g).2.2.val) :=
      congrArg (fun M : Mat => scale g S • M) (space_eq_height_flag (act (realIntegral g) S))
    _=_ := by rw [smul_smul]

theorem pairing_rows (S : Space) (g : IntegralGL) (i j : Fin 3) :
    pairing S (realVector (row g i)) (realVector (row g j))=
      conjugate (realIntegral g) S.val i j := by
  change ((realIntegral g).val i) ⬝ᵥ (S.val*ᵥ((realIntegral g).val j))=
    ((realIntegral g).val*S.val*(realIntegral g).val.conjTranspose) i j
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.mulVec,dotProduct]

/-- The two minimizations compare precisely these four actual LDL squared lengths. -/
theorem flag_energy_data (S : Space) (g : IntegralGL) :
    ∃ c : ℝ, 0<c ∧ energy S (row g 2)=c ∧
      energy S (row g 1)=c*((ldlCoordinates S g).2.2.val+((ldlCoordinates S g).1 1)^2) ∧
      projectedEnergy S (row g 2) (row g 1)=c*(ldlCoordinates S g).2.2.val ∧
      projectedEnergy S (row g 2) (row g 0)=
        c*((ldlCoordinates S g).2.1.val+((ldlCoordinates S g).1 0)^2*(ldlCoordinates S g).2.2.val) := by
  obtain ⟨c,hc,hgram⟩ := gram_eq_positive_flag S g
  have hp (i j : Fin 3) := pairing_rows S g i j
  simp only [hgram,Matrix.smul_apply,smul_eq_mul,flagMatrix_explicit] at hp
  let p := ldlCoordinates S g
  have he (i : Fin 3) : energy S (row g i)=pairing S (realVector (row g i)) (realVector (row g i)) := rfl
  have e2 : energy S (row g 2)=c := by simpa [he] using hp 2 2
  have e1 : energy S (row g 1)=c*(p.2.2.val+(p.1 1)^2) := (he 1).trans (hp 1 1)
  have e0 : energy S (row g 0)=c*(p.2.1.val+(p.1 0)^2*p.2.2.val+(p.1 2)^2) :=
    (he 0).trans (hp 0 0)
  have p21 : pairing S (realVector (row g 2)) (realVector (row g 1))=c*p.1 1 := hp 2 1
  have p20 : pairing S (realVector (row g 2)) (realVector (row g 0))=c*p.1 2 := hp 2 0
  refine ⟨c,hc,e2,e1,?_,?_⟩
  · change energy S (row g 1)-
      (pairing S (realVector (row g 2)) (realVector (row g 1))/energy S (row g 2))^2*
        energy S (row g 2)=c*p.2.2.val
    rw [e1,e2,p21]
    field_simp [ne_of_gt hc]
    ring
  · change energy S (row g 0)-
      (pairing S (realVector (row g 2)) (realVector (row g 0))/energy S (row g 2))^2*
        energy S (row g 2)=c*(p.2.1.val+(p.1 0)^2*p.2.2.val)
    rw [e0,e2,p20]
    field_simp [ne_of_gt hc]
    ring

end TernaryPoly.SymmetricSpaceSiegelReduction
