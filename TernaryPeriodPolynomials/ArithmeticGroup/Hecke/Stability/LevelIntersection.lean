module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals

@[expose] public section


/-!
# The arithmetic level is the rational points of the finite compact level

`rationalFinite g ∈ finiteLevel ↔ g ∈ rationalLevel`. The forward direction
uses that a rational number integral at every finite place is an integer.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeStability

theorem rationalFinite_mem_of_rationalLevel {r : RationalGL3} (hr : r ∈ rationalLevel) :
    rationalFinite r ∈ finiteLevel := by
  rcases MonoidHom.mem_range.mp hr with ⟨a, ha⟩
  subst ha
  have hhom : (algebraMap ℚ FiniteAdeles).comp (Int.castRingHom ℚ) =
      integralEmbedding.comp (Int.castRingHom IntegralAdeles) := by
    ext z
    simp
  have hred : integralReduction.comp (Int.castRingHom IntegralAdeles) =
      Int.castRingHom (ZMod 3) := by
    ext z
    simp
  have hval : rationalFinite (rationalInclusion a) =
      GeneralLinearGroup.map integralEmbedding
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val) := by
    apply GeneralLinearGroup.ext
    intro i j
    simp only [rationalFinite, rationalInclusion, MonoidHom.comp_apply,
      Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
    exact RingHom.congr_fun hhom (a.val.val i j)
  have hkey : GeneralLinearGroup.map integralReduction
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val) =
      reductionThree a.val := by
    rw [reductionThree]
    apply GeneralLinearGroup.ext
    intro i j
    simp only [GeneralLinearGroup.map_apply]
    exact RingHom.congr_fun hred (a.val.val i j)
  rw [hval, finiteLevel]
  refine Subgroup.mem_map.mpr ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val, ?_, rfl⟩
  change GeneralLinearGroup.map integralReduction
    (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) a.val) ∈ rowStabilizer
  rw [hkey]
  exact a.property

/-- Entrywise integrality of a rational matrix whose finite image is integral. -/
theorem integer_entries_of_integral {g : RationalGL3}
    (A : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (h : GeneralLinearGroup.map integralEmbedding A = rationalFinite g) (i j : Fin 3) :
    ∃ m : ℤ, g.val i j = m := by
  apply (PlaneEisensteinContinuation.IntegralRationals.integral_iff_integer (g.val i j)).mp
  refine ⟨A.val i j, ?_⟩
  have := congrArg (fun B : FiniteGL => B.val i j) h
  simpa [rationalFinite, GeneralLinearGroup.map_apply] using this

theorem integer_inv_entries_of_integral {g : RationalGL3}
    (A : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (h : GeneralLinearGroup.map integralEmbedding A = rationalFinite g) (i j : Fin 3) :
    ∃ m : ℤ, (g⁻¹).val i j = m := by
  have hinv : GeneralLinearGroup.map integralEmbedding A⁻¹ = rationalFinite g⁻¹ := by
    rw [map_inv, map_inv, h]
  exact integer_entries_of_integral A⁻¹ hinv i j

theorem mem_rationalLevel_of_rationalFinite_mem {g : RationalGL3}
    (hg : rationalFinite g ∈ finiteLevel) : g ∈ rationalLevel := by
  classical
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp hg
  choose m hm using integer_entries_of_integral A hAg
  choose m' hm' using integer_inv_entries_of_integral A hAg
  have castInj : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
  have mul_one' : (Matrix.of m) * (Matrix.of m') = 1 := by
    apply Matrix.map_injective castInj
    ext i j
    have hij := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℚ => B i j) (Units.mul_inv g)
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul,
      Matrix.one_apply] at hij ⊢
    have e : ∑ x, ((m i x : ℤ) : ℚ) * ((m' x j : ℤ) : ℚ) =
        ∑ x, g.val i x * (g⁻¹).val x j := by simp [hm, hm']
    rw [e, hij]
    split_ifs <;> simp
  have one_mul' : (Matrix.of m') * (Matrix.of m) = 1 := by
    apply Matrix.map_injective castInj
    ext i j
    have hij := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℚ => B i j) (Units.inv_mul g)
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul,
      Matrix.one_apply] at hij ⊢
    have e : ∑ x, ((m' i x : ℤ) : ℚ) * ((m x j : ℤ) : ℚ) =
        ∑ x, (g⁻¹).val i x * g.val x j := by simp [hm, hm']
    rw [e, hij]
    split_ifs <;> simp
  let γ : IntegralGL3 := ⟨Matrix.of m, Matrix.of m', mul_one', one_mul'⟩
  have hγ : GeneralLinearGroup.map (Int.castRingHom ℚ) γ = g := by
    apply GeneralLinearGroup.ext
    intro i j
    simp [γ, GeneralLinearGroup.map_apply, hm]
  have hAγ : A = GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) γ := by
    apply GeneralLinearGroup.ext
    intro i j
    apply integralEmbedding_injective
    have := congrArg (fun B : FiniteGL => B.val i j) hAg
    simp only [GeneralLinearGroup.map_apply] at this
    rw [this]
    simp [rationalFinite, GeneralLinearGroup.map_apply, γ, hm]
  have hlevel : γ ∈ arithmeticLevel := by
    change reductionThree γ ∈ rowStabilizer
    have hred : GeneralLinearGroup.map integralReduction A = reductionThree γ := by
      rw [hAγ, reductionThree]
      apply GeneralLinearGroup.ext
      intro i j
      simp [GeneralLinearGroup.map_apply]
    rw [← hred]
    exact hA
  exact ⟨⟨γ, hlevel⟩, hγ⟩

theorem rationalFinite_mem_finiteLevel_iff (g : RationalGL3) :
    rationalFinite g ∈ finiteLevel ↔ g ∈ rationalLevel :=
  ⟨mem_rationalLevel_of_rationalFinite_mem, rationalFinite_mem_of_rationalLevel⟩

end TernaryPeriodPolynomials.HeckeStability
