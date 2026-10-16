module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Independence
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryTraceAL
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


/-!
# The classical oldform pair of a spherical inducing datum

For `D` with spherical cusp `σ = D.cusp`, the level-one extraction gives a nonzero spherical vector
`v` of rotation weight `-(n+3)` with holomorphic scalar function.  Both `v` and its Atkin–Lehner
translate `v' = cuspFiniteRationalSlash σ W v`, `W = [[0,-1],[3,0]]`, are classical level-three
vectors (`atkinLehner_mem_levelThreeClassicalVectors`), so they give two cusp forms for `Γ₁(3)` of
weight `n + 3` that are linearly independent (`exists_classicalOldformPair`): the forms `f(τ)` and
`f(3τ)`.  Transporting them to the weight `(n + 1) + 2` of the period map, injectivity of the
level-three Eichler–Shimura period map makes their period classes linearly independent
(`linearIndependent_periodClasses_oldformPair`).

* `atkinLehner_mem_levelThreeClassicalVectors`: the Atkin–Lehner translate of a classical
  level-three vector is a classical level-three vector.
* `exists_classicalOldformPair`: two linearly independent cusp forms for `Γ₁(3)`.
* `linearIndependent_periodClasses_oldformPair`: two linearly independent period classes.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Oldform

open TernaryPeriodPolynomials.MultiplicityOne (atkinLehnerQ levelThreeClassicalVectors
  mem_levelThreeValues cuspSphericalValues_le_levelThreeValues slashW_borel_fixed mem_borelThree
  atkinLehnerQ_real_det levelThreeClassicalVectors_mem_of_holomorphic levelThreeForm
  levelThreeForm_coe levelThreeToCuspForm levelThreeToCuspForm_injective)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
  (levelThreePeriodMap)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodInjective
  (levelThreePeriodMap_injective)

/-! ## The Atkin–Lehner translate is a classical level-three vector -/

/-- **The Atkin–Lehner translate of a classical level-three vector is a classical level-three
vector**: it is fixed by the level (`slashW_borel_fixed`), has the same rotation weight, and its
scalar function is a scalar multiple of the slash of the scalar function of `v` by `W`, hence
holomorphic. -/
theorem atkinLehner_mem_levelThreeClassicalVectors (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    cuspFiniteRationalSlash σ atkinLehnerQ v ∈ levelThreeClassicalVectors σ halfWeight := by
  have fixed : v.val ∈ MultiplicityOne.levelThreeValues σ := hv.1
  have rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val := hv.2.1
  have source : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinear σ halfWeight 1 v) :=
    hv.2.2
  have positive : 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ).val.det := by
    rw [atkinLehnerQ_real_det]
    norm_num
  have holomorphic : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (cuspScalarWeightedLinear σ halfWeight 1
        (cuspFiniteRationalSlash σ atkinLehnerQ v)) := by
    rw [cuspFiniteRationalSlash_eq_slash σ central_positive halfWeight v rotation atkinLehnerQ
      positive]
    exact (source.slash (-2 * halfWeight)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) atkinLehnerQ)).const_smul _
  refine ⟨mem_levelThreeValues.mpr fun k hk => ?_,
    cuspFiniteRationalSlash_rotation σ atkinLehnerQ (2 * halfWeight) v rotation, holomorphic⟩
  exact slashW_borel_fixed σ halfWeight v fixed rotation k (mem_borelThree.mpr (And.left hk))

/-! ## The pair of cusp forms for `Γ₁(3)` -/

/-- **The classical oldform pair.**  A spherical inducing datum has a nonzero spherical vector `v`
of weight `-(n+3)` such that `v` and its Atkin–Lehner translate are classical level-three vectors
whose cusp forms for `Γ₁(3)` are linearly independent. -/
theorem exists_classicalOldformPair {n : ℕ} (D : InducingData n) (hsph : SphericalCusp D.cusp) :
    ∃ halfWeight : ℤ, 2 * halfWeight = -((n : ℤ) + 3) ∧ ∃ (negative : halfWeight < 0)
      (v : D.cusp.smooth) (hv : v ∈ levelThreeClassicalVectors D.cusp halfWeight)
      (hw : cuspFiniteRationalSlash D.cusp atkinLehnerQ v ∈
        levelThreeClassicalVectors D.cusp halfWeight),
      v.val ∈ cuspSphericalValues D.cusp ∧ v ≠ 0 ∧
      LinearIndependent ℂ ![levelThreeForm D.cusp halfWeight negative v hv,
        levelThreeForm D.cusp halfWeight negative _ hw] := by
  have hodd := odd_of_sphericalCusp hsph D.cohomological
  have central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      D.cusp.centralCharacter (realAdeleUnit unit) = 1 :=
    cohomological_centralCharacter_positive D.cusp D.cohomological
  obtain ⟨halfWeight, v, hweight, hv0, hsv, hrot, -, hhol⟩ :=
    cohomological_exists_spherical_holomorphic D.cusp hsph hodd D.cohomological
  have hlevel := cuspSphericalValues_le_levelThreeValues D.cusp hsv
  have hscalar := MultiplicityOne.cuspScalarWeightedRealization_holomorphic D.cusp
    halfWeight v hlevel hrot hhol 1
  have hv : v ∈ levelThreeClassicalVectors D.cusp halfWeight :=
    levelThreeClassicalVectors_mem_of_holomorphic D.cusp halfWeight v hlevel hrot hscalar
  have hw := atkinLehner_mem_levelThreeClassicalVectors D.cusp central_positive halfWeight v hv
  have negative : halfWeight < 0 := by omega
  refine ⟨halfWeight, hweight, negative, v, hv, hw, hsv, hv0, ?_⟩
  have pair : LinearIndependent ℂ ![v, cuspFiniteRationalSlash D.cusp atkinLehnerQ v] :=
    linearIndependent_atkinLehner D.cusp v hv0 hsv
  have pairSub : LinearIndependent ℂ
      (![⟨v, hv⟩, ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩] :
        Fin 2 → levelThreeClassicalVectors D.cusp halfWeight) := by
    apply LinearIndependent.of_comp (levelThreeClassicalVectors D.cusp halfWeight).subtype
    have hcomp : (levelThreeClassicalVectors D.cusp halfWeight).subtype ∘
        (![⟨v, hv⟩, ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩] :
          Fin 2 → levelThreeClassicalVectors D.cusp halfWeight) =
        ![v, cuspFiniteRationalSlash D.cusp atkinLehnerQ v] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact pair
  have mapped := pairSub.map' (levelThreeToCuspForm D.cusp halfWeight negative)
    (LinearMap.ker_eq_bot.mpr
      (levelThreeToCuspForm_injective D.cusp central_positive halfWeight negative))
  have hcomp : levelThreeToCuspForm D.cusp halfWeight negative ∘
      (![⟨v, hv⟩, ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩] :
        Fin 2 → levelThreeClassicalVectors D.cusp halfWeight) =
      ![levelThreeForm D.cusp halfWeight negative v hv,
        levelThreeForm D.cusp halfWeight negative _ hw] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp] at mapped
  exact mapped

/-! ## The pair of period classes -/

/-- A cusp form of weight `a` is a cusp form of weight `b` with the same underlying function
whenever `a = b`. -/
theorem exists_cuspForm_cast {Γ : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} {a b : ℤ} (h : a = b)
    (f : CuspForm Γ a) : ∃ g : CuspForm Γ b, ⇑g = ⇑f := by
  subst h
  exact ⟨f, rfl⟩

/-- **The period classes of the classical oldform pair are linearly independent.**  The two cusp
forms of `exists_classicalOldformPair`, transported to the weight `(n + 1) + 2` of the level-three
period map, have linearly independent period classes in every twist `e`. -/
theorem linearIndependent_periodClasses_oldformPair {n : ℕ} (D : InducingData n)
    (hsph : SphericalCusp D.cusp) (e : ℤ) :
    ∃ halfWeight : ℤ, 2 * halfWeight = -((n : ℤ) + 3) ∧
      ∃ (v : D.cusp.smooth)
        (f₁ f₂ : LevelThree.LevelThreePeriodCocycle.S (n + 1)),
        v ≠ 0 ∧ v.val ∈ cuspSphericalValues D.cusp ∧
        v ∈ levelThreeClassicalVectors D.cusp halfWeight ∧
        cuspFiniteRationalSlash D.cusp atkinLehnerQ v ∈
          levelThreeClassicalVectors D.cusp halfWeight ∧
        ⇑f₁ = cuspScalarWeightedLinear D.cusp halfWeight 1 v ∧
        ⇑f₂ = cuspScalarWeightedLinear D.cusp halfWeight 1
          (cuspFiniteRationalSlash D.cusp atkinLehnerQ v) ∧
        LinearIndependent ℂ
          ![levelThreePeriodMap (n + 1) e f₁, levelThreePeriodMap (n + 1) e f₂] := by
  obtain ⟨halfWeight, hweight, negative, v, hv, hw, hsv, hv0, hli⟩ :=
    exists_classicalOldformPair D hsph
  have hwt : -2 * halfWeight = ((n + 1 : ℕ) : ℤ) + 2 := by omega
  obtain ⟨f₁, hf₁⟩ : ∃ g : LevelThree.LevelThreePeriodCocycle.S (n + 1),
      ⇑g = ⇑(levelThreeForm D.cusp halfWeight negative v hv) :=
    exists_cuspForm_cast hwt _
  obtain ⟨f₂, hf₂⟩ : ∃ g : LevelThree.LevelThreePeriodCocycle.S (n + 1),
      ⇑g = ⇑(levelThreeForm D.cusp halfWeight negative
        (cuspFiniteRationalSlash D.cusp atkinLehnerQ v) hw) :=
    exists_cuspForm_cast hwt _
  have hF : LinearIndependent ℂ ![f₁, f₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    refine LinearIndependent.pair_iff.mp hli s t ?_
    apply DFunLike.ext
    intro z
    have hz := DFunLike.congr_fun hst z
    change s • f₁ z + t • f₂ z = 0 at hz
    rw [congrFun hf₁ z, congrFun hf₂ z] at hz
    exact hz
  have mapped := hF.map' (levelThreePeriodMap (n + 1) e)
    (LinearMap.ker_eq_bot.mpr (levelThreePeriodMap_injective (n + 1) e (Nat.succ_pos n)))
  have hcomp : levelThreePeriodMap (n + 1) e ∘ ![f₁, f₂] =
      ![levelThreePeriodMap (n + 1) e f₁, levelThreePeriodMap (n + 1) e f₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp] at mapped
  exact ⟨halfWeight, hweight, v, f₁, f₂, hv0, hsv, hv, hw,
    hf₁.trans (levelThreeForm_coe D.cusp halfWeight negative v hv),
    hf₂.trans (levelThreeForm_coe D.cusp halfWeight negative _ hw), mapped⟩

end TernaryPeriodPolynomials.Oldform
