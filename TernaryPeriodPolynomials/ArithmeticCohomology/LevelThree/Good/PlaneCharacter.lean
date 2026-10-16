module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneJoint

@[expose] public section


/-!
# Characters with `χ(-1_∞) = 1` at the good plane

On rational matrices the coefficient representation `rationalCoefficientComponent n χ` only sees the
sign of the determinant through `χ(-1_∞) = χ(realAdeleUnit (-1)) = ±1`. When `χ(-1_∞) = 1` the
character `componentCharacter χ` is identically `1` (`componentCharacter_eq_one`), so the
representation, hence the local cohomology, the local Hecke operators and the local joint
generalized eigenspaces coincide with those of the trivial character
(`rationalCoefficientComponent_eq`). Every statement `LocalUpperBound n trivialCharacter ...` thus
transfers to such `χ` (`localUpperBound_of_signValue_one`). For `χ(-1_∞) = -1` the sign twist
changes the Levi action and is not treated here.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneCharacter

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel localOp localJoint)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (transports_cuspFlag)

/-- The value `χ(-1_∞)` of a rank-one character on the real unit `-1`. -/
def signValue (χ : RankOneCharacter) : ℂ := χ.toMonoidHom (realAdeleUnit (-1))

/-- If `χ(-1_∞) = 1`, the component character is trivial on all of `GL₃(ℝ)`. -/
theorem componentCharacter_eq_one (χ : RankOneCharacter) (h : signValue χ = 1) (g : RealGL3) :
    componentCharacter χ g = 1 := by
  change χ.toMonoidHom (realAdeleUnit (Matrix.GeneralLinearGroup.det g)) = 1
  generalize Matrix.GeneralLinearGroup.det g = t
  rcases lt_or_gt_of_ne t.ne_zero with ht | ht
  · have hpos : 0 < (-t : ℝˣ).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr ht
    have e : realAdeleUnit t = realAdeleUnit (-1) * realAdeleUnit (-t) := by
      have h1 := realUnitHom.map_mul (-1) (-t)
      have h2 : ((-1 : ℝˣ) * (-t)) = t := by simp
      rw [h2] at h1
      exact h1
    rw [e, map_mul, χ.positiveReal (-t) hpos]
    change signValue χ * 1 = 1
    rw [h, mul_one]
  · exact χ.positiveReal t ht

theorem realCoefficientComponent_eq (χ : RankOneCharacter) (h : signValue χ = 1) (n : ℕ) :
    realCoefficientComponent n χ = realCoefficientComponent n trivialCharacter := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  have h1 : componentCharacter trivialCharacter g = 1 := by
    change (1 : Adelesˣ →* ℂ) (realAdeleUnit (Matrix.GeneralLinearGroup.det g)) = 1
    rfl
  change componentCharacter χ g • realCoefficient n g v =
    componentCharacter trivialCharacter g • realCoefficient n g v
  rw [componentCharacter_eq_one χ h g, h1]

/-- **For `χ(-1_∞) = 1` the rational coefficient representation is that of the trivial
character.** -/
theorem rationalCoefficientComponent_eq (χ : RankOneCharacter) (h : signValue χ = 1) (n : ℕ) :
    rationalCoefficientComponent n χ = rationalCoefficientComponent n trivialCharacter := by
  unfold rationalCoefficientComponent
  rw [realCoefficientComponent_eq χ h n]

/-! ### Transfer of the local upper bound -/

/-- The local joint generalized eigenspace, as a function of the coefficient representation. -/
def jointFor {n : ℕ} (ρ : Representation ℂ RationalGL3 (HomogeneousPoly n))
    (c : HeckeCorrespondence → ℂ) (side : Side) (good : Bool) :
    Submodule ℂ (H2 (cuspLevel side good) ρ) :=
  ⨅ t : {t : HeckeCorrespondence // AwayThree t},
    (LocalHecke.cohomologyAction ρ
      (HeckeShapiro.localCorrespondence (transports_cuspFlag t.1 t.2 side good))
      ).maxGenEigenspace (c t.1)

theorem localJoint_eq_jointFor (n : ℕ) (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ)
    (side : Side) (good : Bool) :
    localJoint n χ c side good = jointFor (rationalCoefficientComponent n χ) c side good := rfl

theorem bound_of_rep_eq {n : ℕ} {ρ ρ' : Representation ℂ RationalGL3 (HomogeneousPoly n)}
    (h : ρ = ρ') (c : HeckeCorrespondence → ℂ) (side : Side) (good : Bool) (m : ℕ)
    (H : FiniteDimensional ℂ (jointFor ρ' c side good) ∧
      Module.finrank ℂ (jointFor ρ' c side good) ≤ m) :
    FiniteDimensional ℂ (jointFor ρ c side good) ∧
      Module.finrank ℂ (jointFor ρ c side good) ≤ m := by
  subst h
  exact H

/-- **The local upper bound at the good plane for every `χ` with `χ(-1_∞) = 1`.** -/
theorem localUpperBound_of_signValue_one (χ : RankOneCharacter) (h : signValue χ = 1) (n : ℕ)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ) (m : ℕ)
    (hm : Module.finrank ℂ (GoodPlaneJoint.levelJoint n c) ≤ m) :
    Separation.LocalUpperBound n χ c .plane true m := by
  have H := GoodPlaneJoint.localUpperBound_of_levelJoint n hn c m hm
  exact bound_of_rep_eq (rationalCoefficientComponent_eq χ h n) c .plane true m H

end TernaryPeriodPolynomials.LevelThree.GoodPlaneCharacter
