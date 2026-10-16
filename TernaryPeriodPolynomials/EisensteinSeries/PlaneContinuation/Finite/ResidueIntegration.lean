module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentPeriodicity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Residue
open scoped ENNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteResidueIntegration

local instance placeNeZero (place : FinitePlace) : NeZero (Rat.HeightOneSpectrum.primesEquiv place).val :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero⟩

theorem residueMeasure (place : FinitePlace) (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val) :
    (finiteMeasure (finiteResidueCoset place residue)).toReal =
      ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ)⁻¹ := by
  rw [finiteResidueCoset_measure]
  have equality := congrArg ENNReal.toReal (finiteMeasure_primeSublattice place)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at equality
  have nonzero : ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ) ≠ 0 := by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero
  apply (mul_left_cancel₀ nonzero)
  rw [equality, mul_inv_cancel₀ nonzero]

theorem integral_residues (place : FinitePlace) (function : FiniteAdeles → ℂ)
    (integrable : IntegrableOn function (Set.range integralEmbedding) finiteMeasure)
    (values : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val → ℂ)
    (constantOnCosets : ∀ residue : ZMod (Rat.HeightOneSpectrum.primesEquiv place).val,
      ∀ quotient : IntegralAdeles, function ((residue.val : FiniteAdeles) +
        (Rat.HeightOneSpectrum.primesEquiv place).val * integralEmbedding quotient) = values residue) :
    ∫ value in Set.range integralEmbedding, function value ∂finiteMeasure =
      ((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ)⁻¹ • ∑ residue, values residue := by
  rw [← finiteResidueCosets_cover place] at integrable ⊢
  rw [integral_iUnion (fun residue => (finiteResidueCoset_compact place residue).measurableSet)
    (finiteResidueCosets_disjoint place) integrable, tsum_fintype, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro residue _
  have constantIntegral : ∫ value in finiteResidueCoset place residue, function value ∂finiteMeasure =
      ∫ _ in finiteResidueCoset place residue, values residue ∂finiteMeasure := by
    apply setIntegral_congr_fun (finiteResidueCoset_compact place residue).measurableSet
    rintro value ⟨quotient, rfl⟩
    exact constantOnCosets residue quotient
  rw [constantIntegral, setIntegral_const]
  exact congrArg (fun scalar : ℝ => scalar • values residue) (residueMeasure place residue)

theorem sum_residue_values (modulus : ℕ) [NeZero modulus] (function : ℕ → ℂ) :
    ∑ residue : ZMod modulus, function residue.val = ∑ integer ∈ Finset.range modulus, function integer := by
  apply Finset.sum_bij (fun residue _ => residue.val)
  · intro residue _
    exact Finset.mem_range.mpr residue.val_lt
  · intro first _ second _ equality
    exact ZMod.val_injective modulus equality
  · intro integer membership
    exact ⟨(integer : ZMod modulus), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp membership)⟩
  · intros
    rfl

theorem integral_three_residues (function : FiniteAdeles → ℂ)
    (integrable : IntegrableOn function (Set.range integralEmbedding) finiteMeasure)
    (values : ℕ → ℂ)
    (constantOnCosets : ∀ residue : ℕ, ∀ quotient : IntegralAdeles,
      function (integralEmbedding ((residue : IntegralAdeles) + 3 * quotient)) = values residue) :
    ∫ value in Set.range integralEmbedding, function value ∂finiteMeasure =
      (3 : ℝ)⁻¹ • (values 0 + values 1 + values 2) := by
  have primeEquality : (Rat.HeightOneSpectrum.primesEquiv placeThree).val = 3 :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply primeThree)
  have constantOnCosets' (residue : ZMod (Rat.HeightOneSpectrum.primesEquiv placeThree).val)
      (quotient : IntegralAdeles) : function ((residue.val : FiniteAdeles) +
        (Rat.HeightOneSpectrum.primesEquiv placeThree).val * integralEmbedding quotient) = values residue.val := by
    have equality := congrArg (fun integer : ℕ => (residue.val : FiniteAdeles) +
      (integer : FiniteAdeles) * integralEmbedding quotient) primeEquality
    rw [equality]
    simpa only [map_add, map_mul, map_natCast, map_ofNat, Nat.cast_ofNat] using constantOnCosets residue.val quotient
  have equality := integral_residues placeThree function integrable (fun residue => values residue.val) constantOnCosets'
  rw [sum_residue_values, primeEquality] at equality
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_ofNat] using equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteResidueIntegration
