module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.ThreeMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionSupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem map_lineUnipotent {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) :
    GeneralLinearGroup.map hom (lineUnipotent first second) =
      lineUnipotent (hom first) (hom second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, lineUnipotent, upperUnipotent]

def adeleAtThreeScalar (value : ℚ_[3]) : Adeles := (0, finiteAtThreeScalar value)

def adeleAwayThreeScalar (value : AdelesAwayThree) : Adeles := (value.1, value.2.val)

theorem adeleThreeJoin_add (localValue : ℚ_[3]) (awayValue : AdelesAwayThree) :
    adeleThreeJoin (localValue, awayValue) =
      adeleAtThreeScalar localValue + adeleAwayThreeScalar awayValue := by
  rw [adeleThreeJoin_apply]
  exact Prod.ext (zero_add _).symm rfl

theorem finiteAtThreeScalar_zero : finiteAtThreeScalar 0 = 0 := finiteAtThreeAdd.map_zero

theorem atThree_lineUnipotent (first second : ℚ_[3]) :
    atThree (lineUnipotent first second) =
      lineUnipotent (adeleAtThreeScalar first) (adeleAtThreeScalar second) := by
  apply adelicGL_ext
  · rw [realGroup_atThree]
    change 1 = GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)
      (lineUnipotent (adeleAtThreeScalar first) (adeleAtThreeScalar second))
    rw [map_lineUnipotent]
    exact (lineUnipotentHom ℝ).map_one.symm
  · rw [finiteGroup_atThree]
    change finiteAtThree (lineUnipotent first second) =
      GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)
        (lineUnipotent (adeleAtThreeScalar first) (adeleAtThreeScalar second))
    rw [map_lineUnipotent]
    apply Units.ext
    funext row column
    change finiteAtThreeMatrix (lineUnipotent first second).val row column = _
    fin_cases row <;> fin_cases column <;>
      simp [finiteAtThreeMatrix, lineUnipotent, upperUnipotent, adeleAtThreeScalar,
        finiteAtThreeScalar_zero]

theorem adelicThreeGroup_weyl : adelicThreeGroup (weyl : AdelicGL) = weyl := by
  change GeneralLinearGroup.map finiteThree
    (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) weyl) = weyl
  rw [map_weyl, map_weyl]

theorem adelicThreeGroup_awayUnipotent (first second : AdelesAwayThree) :
    adelicThreeGroup (lineUnipotent (adeleAwayThreeScalar first) (adeleAwayThreeScalar second)) = 1 := by
  change GeneralLinearGroup.map finiteThree
    (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)
      (lineUnipotent (adeleAwayThreeScalar first) (adeleAwayThreeScalar second))) = 1
  rw [map_lineUnipotent, map_lineUnipotent]
  change lineUnipotent (finiteThree first.2.val) (finiteThree second.2.val) = 1
  have first_zero : finiteThree first.2.val = 0 := first.2.property
  have second_zero : finiteThree second.2.val = 0 := second.2.property
  rw [first_zero, second_zero]
  exact (lineUnipotentHom ℚ_[3]).map_one

def awayThreeWeylInverse : AdelicGL := atThree weyl * weyl⁻¹

theorem awayThreeWeylInverse_three : adelicThreeGroup awayThreeWeylInverse = 1 := by
  rw [awayThreeWeylInverse, map_mul, atThree_three, map_inv, adelicThreeGroup_weyl, mul_inv_cancel]

def standardAwayThreeArgument (away : AdelesAwayThree × AdelesAwayThree) (base : AdelicGL) :
    AdelicGL :=
  awayThreeWeylInverse *
    lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2) * base

theorem standardAwayThreeArgument_three (away : AdelesAwayThree × AdelesAwayThree)
    (base : AdelicGL) (base_three : adelicThreeGroup base = 1) :
    adelicThreeGroup (standardAwayThreeArgument away base) = 1 := by
  rw [standardAwayThreeArgument, map_mul, map_mul, awayThreeWeylInverse_three,
    adelicThreeGroup_awayUnipotent, base_three, one_mul, one_mul]

theorem standardThreeCoordinates (localParameter : ℚ_[3] × ℚ_[3])
    (away : AdelesAwayThree × AdelesAwayThree) (base : AdelicGL) :
    weyl⁻¹ * lineUnipotent (radicalThreeJoin (localParameter, away)).1
      (radicalThreeJoin (localParameter, away)).2 * (atThree localGoodLine * base) =
    atThree (weyl⁻¹ * lineUnipotent localParameter.1 localParameter.2 * localGoodLine) *
      standardAwayThreeArgument away base := by
  change weyl⁻¹ * lineUnipotent (adeleThreeJoin (localParameter.1, away.1))
    (adeleThreeJoin (localParameter.2, away.2)) * (atThree localGoodLine * base) = _
  rw [adeleThreeJoin_add, adeleThreeJoin_add, lineUnipotent_add, ← atThree_lineUnipotent]
  have weyl_decompose : (weyl : AdelicGL)⁻¹ = atThree (weyl⁻¹) * awayThreeWeylInverse := by
    rw [awayThreeWeylInverse, map_inv, inv_mul_cancel_left]
  have commute_unipotent := (atThree_commute
    (lineUnipotent localParameter.1 localParameter.2) awayThreeWeylInverse
    awayThreeWeylInverse_three).symm
  have commute_good := (atThree_commute localGoodLine
    (awayThreeWeylInverse * lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2))
    (by rw [map_mul, awayThreeWeylInverse_three, adelicThreeGroup_awayUnipotent, one_mul])).symm
  rw [weyl_decompose]
  simp only [map_mul, standardAwayThreeArgument]
  calc
    _ = atThree (weyl⁻¹) *
        ((awayThreeWeylInverse * atThree (lineUnipotent localParameter.1 localParameter.2)) *
          (lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2) *
            (atThree localGoodLine * base))) := by simp only [mul_assoc]
    _ = atThree (weyl⁻¹) *
        ((atThree (lineUnipotent localParameter.1 localParameter.2) * awayThreeWeylInverse) *
          (lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2) *
            (atThree localGoodLine * base))) := by rw [commute_unipotent.eq]
    _ = (atThree (weyl⁻¹) * atThree (lineUnipotent localParameter.1 localParameter.2)) *
        ((awayThreeWeylInverse * lineUnipotent (adeleAwayThreeScalar away.1) (adeleAwayThreeScalar away.2)) *
          atThree localGoodLine) * base := by simp only [mul_assoc]
    _ = _ := by rw [commute_good.eq]; simp only [mul_assoc]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
