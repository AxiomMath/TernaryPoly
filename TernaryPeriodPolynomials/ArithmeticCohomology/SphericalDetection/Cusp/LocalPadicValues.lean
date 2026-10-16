module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicMatrixEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLocalPadicValue (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] → ℂ :=
  fun matrix => cusp.realize vector (atFinite (base * finiteAtPadicGL 2 place matrix))

theorem cuspLocalPadicValue_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) :
    cuspLocalPadicValue cusp vector base place 1 = cusp.realize vector (atFinite base) := by
  simp only [cuspLocalPadicValue, map_one, mul_one]

theorem cuspLocalPadicValue_right (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (matrix : GeneralLinearGroup (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (compact : GeneralLinearGroup (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val]),
      cuspLocalPadicValue cusp vector base place (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) =
        cuspLocalPadicValue cusp vector base place matrix := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix compact
  obtain ⟨integral, equality⟩ := finiteAtPadicGL_integral 2 place compact
  change cusp.realize vector (atFinite (base * finiteAtPadicGL 2 place
    (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact))) = _
  rw [map_mul, ← mul_assoc, ← equality, cuspSpherical_realize_right cusp vector spherical]
  rfl

theorem cuspLocalPadicValue_bounded (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) :
    ∃ bound : ℝ, ∀ matrix, ‖cuspLocalPadicValue cusp vector base place matrix‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  exact ⟨bound, fun matrix => bounded (atFinite (base * finiteAtPadicGL 2 place matrix))⟩

/-- The primitive sum uses the forward local action dictated by the actual finite cusp integrand. -/
def cuspLocalPadicPrimitiveOperator (cusp : CuspidalRepresentation) (place : FinitePlace) (power : ℕ) :
    Module.End ℂ cusp.smooth := by
  classical
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact ∑ index : Fin ((Rat.HeightOneSpectrum.primesEquiv place).val ^ power) ⊕
      {index : Fin ((Rat.HeightOneSpectrum.primesEquiv place).val ^ power) //
        (Rat.HeightOneSpectrum.primesEquiv place).val ∣ index.val},
    cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place (padicPrimitiveRepresentative power index)))

theorem cuspLocalPadicPrimitiveOperator_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (power : ℕ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cusp.realize (cuspLocalPadicPrimitiveOperator cusp place power vector) (atFinite base) =
      padicPrimitiveSum power (cuspLocalPadicValue cusp vector base place) := by
  classical
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  simp only [cuspLocalPadicPrimitiveOperator, padicPrimitiveSum, cuspLocalPadicValue,
    LinearMap.sum_apply, map_sum, Finset.sum_apply, cuspSmoothAction_realize, atFinite_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
