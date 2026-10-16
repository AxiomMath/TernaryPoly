module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.SphereRecurrence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLocalPadicAction (cusp : CuspidalRepresentation) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] → Module.End ℂ cusp.smooth :=
  fun matrix => cuspSmoothAction cusp (atFinite (finiteAtPadicGL 2 place matrix))

def cuspLocalPadicCentralChar (cusp : CuspidalRepresentation) (place : FinitePlace) : ℂ :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  cusp.centralCharacter (finiteAdeleUnit (finiteAtPadicUnit place (padicPrimePowerUnit 1)))

theorem cuspLocalPadicAction_one (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) : cuspLocalPadicAction cusp place 1 vector = vector := by
  apply Subtype.ext
  change cusp.π (atFinite (finiteAtPadicGL 2 place 1)) vector.val = vector.val
  rw [map_one, atFinite_one, map_one]
  rfl

theorem cuspLocalPadicAction_mul (cusp : CuspidalRepresentation) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ first second vector,
      cuspLocalPadicAction cusp place (first * second) vector =
        cuspLocalPadicAction cusp place first (cuspLocalPadicAction cusp place second vector) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro first second vector
  simp only [cuspLocalPadicAction, map_mul, atFinite_mul, cuspSmoothAction_mul]

theorem cuspLocalPadicAction_right (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix compact,
      cuspLocalPadicAction cusp place (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) vector =
        cuspLocalPadicAction cusp place matrix vector := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix compact
  rw [cuspLocalPadicAction_mul]
  exact congrArg (cuspLocalPadicAction cusp place matrix)
    (cuspSmoothAction_finite_spherical cusp vector spherical _ (finiteAtPadicGL_integral 2 place compact))

theorem cuspLocalPadicAction_central (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cuspLocalPadicAction cusp place (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1)) vector =
      cuspLocalPadicCentralChar cusp place • vector := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  simp only [cuspLocalPadicAction, cuspLocalPadicCentralChar, finiteAtPadicGL_scalar,
    binary_atFinite_scalar, cuspSmoothAction_scalar]

theorem cuspLocalPadicSphereOperator_eq_sum (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (power : ℕ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cuspLocalPadicSphereOperator cusp place power vector =
      padicSphereSum (fun matrix => cuspLocalPadicAction cusp place matrix vector) power := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  cases power with
  | zero => exact (cuspLocalPadicAction_one cusp place vector).symm
  | succ power =>
    rw [padicSphereSum_eq_primitive, cuspLocalPadicSphereOperator_succ,
      cuspLocalPadicPrimitiveOperator, LinearMap.sum_apply]
    rfl

theorem padicSphereSum_map {prime : ℕ} [Fact prime.Prime] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (mapping : M →+ N)
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    padicSphereSum (fun matrix => mapping (value matrix)) power = mapping (padicSphereSum value power) := by
  cases power <;> simp only [padicSphereSum, map_sum]

theorem padicSphereSum_smul {prime : ℕ} [Fact prime.Prime] {M : Type*}
    [AddCommMonoid M] [Module ℂ M] (scalar : ℂ)
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    padicSphereSum (fun matrix => scalar • value matrix) power = scalar • padicSphereSum value power := by
  cases power <;> simp only [padicSphereSum, Finset.smul_sum]

theorem cuspLocalPadicSphereOperator_step_sum (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (power : ℕ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cuspLocalPadicSphereOperator cusp place power (cuspLocalPadicSphereOperator cusp place 1 vector) =
      padicSphereSum (fun matrix => ∑ index : Option (Fin (Rat.HeightOneSpectrum.primesEquiv place).val),
        cuspLocalPadicAction cusp place (matrix * padicPrimeForwardRepresentative index) vector) power := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [cuspLocalPadicSphereOperator_eq_sum, cuspLocalPadicSphereOperator_eq_sum, padicSphereSum_one]
  simp only [map_sum, cuspLocalPadicAction_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
