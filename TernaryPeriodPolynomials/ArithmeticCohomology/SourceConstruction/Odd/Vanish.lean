module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishGoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishBadLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Obstructions

@[expose] public section


/-!
# The level-three cusps carry no cohomology for an odd character

For a character `χ` with `χ(-1_∞) = -1` (for instance the odd quadratic character of conductor
three), the local cohomology `H²(Γ_F, V_χ)` vanishes at the good plane and at the bad line, for every
degree `n`. Hence the local joint generalized eigenspaces vanish there, the source-realization
statement at these two cusps holds, and the realization at the other cusp of each side is unaffected.

* `cuspH2_plane_true_subsingleton`, `cuspH2_line_false_subsingleton`;
* `localJoint_plane_true_eq_bot`, `localJoint_line_false_eq_bot`;
* `sourceRealization_plane_true_of_odd`, `sourceRealization_line_false_of_odd` (via the character
  obstruction `χ(integralAdeleUnit (-1)) ≠ 1`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **The local cohomology at the good plane vanishes for an odd character.** -/
theorem cuspH2_plane_true_subsingleton (n : ℕ) (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    Subsingleton (CuspH2 n χ .plane true) :=
  subsingleton_of_forall_eq_zero fun x => GoodPlaneVanish.cuspH2_plane_true_eq_zero n χ hodd x

/-- **The local cohomology at the bad line vanishes for an odd character.** -/
theorem cuspH2_line_false_subsingleton (n : ℕ) (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    Subsingleton (CuspH2 n χ .line false) :=
  subsingleton_of_forall_eq_zero fun x => BadLineVanish.cuspH2_line_false_eq_zero n χ hodd x

/-- The local joint generalized eigenspace at the good plane is zero. -/
theorem localJoint_plane_true_eq_bot (n : ℕ) (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ) :
    localJoint n χ c .plane true = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [Submodule.mem_bot]
  exact GoodPlaneVanish.cuspH2_plane_true_eq_zero n χ hodd x

/-- The local joint generalized eigenspace at the bad line is zero. -/
theorem localJoint_line_false_eq_bot (n : ℕ) (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (c : HeckeCorrespondence → ℂ) :
    localJoint n χ c .line false = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [Submodule.mem_bot]
  exact BadLineVanish.cuspH2_line_false_eq_zero n χ hodd x

/-- An odd character is nontrivial on the finite integral unit `-1`. -/
theorem character_integralUnit_neg_one_ne_one_of_odd (χ : RankOneCharacter)
    (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) :
    χ.toMonoidHom (integralAdeleUnit (-1)) ≠ 1 := by
  intro h
  have hrat := χ.rational (-1)
  have hsplit : Units.map rationalAdele (-1 : ℚˣ) =
      realAdeleUnit (-1) * integralAdeleUnit (-1) := by
    apply Units.ext
    change (rationalAdele (-1 : ℚ)) = ((-1 : ℝ) * 1, (1 : FiniteAdeles) * integralEmbedding (-1))
    rw [map_neg, map_one, mul_one, one_mul]
    apply Prod.ext
    · simp
    · simp
  rw [hsplit, map_mul, hodd, h, mul_one] at hrat
  norm_num at hrat

variable {n : ℕ}

/-- **Source realization at the good plane for an odd character.** -/
theorem sourceRealization_plane_true_of_odd (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    SourceRealization D hecke hhecke .plane true :=
  (sourceRealization_plane_true_iff_of_character D hecke hhecke (-1)
    (character_integralUnit_neg_one_ne_one_of_odd D.chi hodd)).mpr
    (localJoint_plane_true_eq_bot n D.chi hodd _)

/-- **Source realization at the bad line for an odd character.** -/
theorem sourceRealization_line_false_of_odd (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    SourceRealization D hecke hhecke .line false :=
  (sourceRealization_line_false_iff_of_character D hecke hhecke (-1)
    (character_integralUnit_neg_one_ne_one_of_odd D.chi hodd)).mpr
    (localJoint_line_false_eq_bot n D.chi hodd _)

end TernaryPeriodPolynomials.SourceConstruction
