module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Localization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.CentralRational
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicHeckeAction

@[expose] public section


/-!
# Level-three vectors and the Hecke sum at a prime `p ≠ 3`

For a vector `v` fixed by the level `{k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` and of even rotation weight, the
unit `K_i = binaryHeckeOutsideCompact p i` of the `i`-th Hecke representative fixes `v`, even though
its reduction modulo three has second row `(0, ±1)` rather than `(0, 1)`: the sign is the scalar
`-1`, which fixes `v` because the central character is trivial on the rational `-1` and `-1` is a
rotation of even weight. Consequently the Hecke sum `cuspPrimeHeckeSum σ p v` is the sum of the
actions of the representatives localized at `p` (`levelThree_heckeLocalized_eq`), exactly as in the
spherical case.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-! ## The scalar `-1` -/

/-- The rotation by the angle `-1` is the scalar matrix `-1`. -/
theorem binaryRotations_neg_one :
    binaryRotations (-1) = GeneralLinearGroup.scalar (Fin 2) (-1 : ℝˣ) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryRotations, binaryRotation, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Circle.coe_neg]

/-- The central character is trivial at the real scalar `-1` on a vector of even rotation
weight. -/
theorem centralCharacter_real_neg_one (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (v : σ.smooth) (nonzero : v ≠ 0)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    σ.centralCharacter (realAdeleUnit (-1 : ℝˣ)) = 1 := by
  have rot := rotation (-1)
  rw [binaryRotations_neg_one, atInfinity_scalar] at rot
  have act : σ.π (GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit (-1 : ℝˣ))) v.val =
      σ.centralCharacter (realAdeleUnit (-1 : ℝˣ)) • v.val :=
    congrArg Subtype.val (cuspSmoothAction_scalar σ (realAdeleUnit (-1 : ℝˣ)) v)
  have sign : (((-1 : Circle) : ℂ)) ^ (2 * halfWeight) = 1 := by
    rw [Circle.coe_neg, Circle.coe_one]
    exact Even.neg_one_zpow (even_two_mul halfWeight)
  rw [act, sign, one_smul] at rot
  have vne : v.val ≠ 0 := fun h => nonzero (Subtype.ext h)
  exact smul_left_injective ℂ vne (rot.trans (one_smul ℂ v.val).symm)

/-- The finite scalar `-1` fixes every smooth vector of even rotation weight. -/
theorem levelThree_negOne_fixed (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding
      (GeneralLinearGroup.scalar (Fin 2) (-1 : IntegralAdelesˣ)))) v.val = v.val := by
  by_cases nonzero : v = 0
  · subst nonzero
    simp
  have real_one := centralCharacter_real_neg_one σ halfWeight v nonzero rotation
  have rational := cuspCentralCharacter_rational σ v nonzero (-1 : ℚˣ)
  rw [rationalAdeleUnit_real_finite, map_mul] at rational
  have real_eq : Units.map (algebraMap ℚ ℝ : ℚ →* ℝ) (-1 : ℚˣ) = (-1 : ℝˣ) :=
    Units.ext (by simp)
  rw [real_eq, real_one, one_mul] at rational
  have action : cuspSmoothAction σ (atFinite (GeneralLinearGroup.map integralEmbedding
      (GeneralLinearGroup.scalar (Fin 2) (-1 : IntegralAdelesˣ)))) v =
      σ.centralCharacter (finiteAdeleUnit (Units.map integralEmbedding (-1 : IntegralAdelesˣ))) •
        v := by
    rw [← cuspSmoothAction_scalar, ← binary_atFinite_scalar, ← GeneralLinearGroup.map_scalar]
  have unit_eq : Units.map integralEmbedding (-1 : IntegralAdelesˣ) =
      Units.map (algebraMap ℚ FiniteAdeles : ℚ →* FiniteAdeles) (-1 : ℚˣ) := Units.ext (by simp)
  rw [unit_eq, rational, one_smul] at action
  exact congrArg Subtype.val action

/-! ## Reductions of the outside compact -/

theorem scalar_val_entry {R : Type*} [CommRing R] (u : Rˣ) (i j : Fin 2) :
    (GeneralLinearGroup.scalar (Fin 2) u).val i j = if i = j then (u : R) else 0 := by
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- A matrix whose second row reduces to `(0, -1)` times the scalar `-1` is of the level. -/
theorem planeLeviLevel_mul_negOne {κ : GeneralLinearGroup (Fin 2) IntegralAdeles}
    (h10 : (GeneralLinearGroup.map integralReduction κ).val 1 0 = 0)
    (h11 : (GeneralLinearGroup.map integralReduction κ).val 1 1 = -1) :
    PlaneLeviLevel (κ * GeneralLinearGroup.scalar (Fin 2) (-1 : IntegralAdelesˣ)) := by
  have hneg : integralReduction (-1 : IntegralAdeles) = (-1 : ZMod 3) :=
    (RingHom.map_neg integralReduction (1 : IntegralAdeles)).trans
      (congrArg (fun z : ZMod 3 => -z) (map_one integralReduction))
  have entry (j : Fin 2) : (GeneralLinearGroup.map integralReduction
      (κ * GeneralLinearGroup.scalar (Fin 2) (-1 : IntegralAdelesˣ))).val 1 j =
      -(GeneralLinearGroup.map integralReduction κ).val 1 j := by
    rw [map_mul, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [GeneralLinearGroup.map_apply, scalar_val_entry]
    fin_cases j <;> simp
    all_goals rw [hneg]
    all_goals exact mul_neg_one _
  exact And.intro ((entry 0).trans (by rw [h10]; rfl))
    ((entry 1).trans (by rw [h11]; rfl))

theorem integralReduction_apply (x : IntegralAdeles) :
    integralReduction x = PadicInt.toZMod (threeIntegralEquiv (x placeThree)) := rfl

theorem integralReduction_congr {x y : IntegralAdeles} (h : x placeThree = y placeThree) :
    integralReduction x = integralReduction y := by
  rw [integralReduction_apply, integralReduction_apply, h]

theorem placeThree_ne_integralPrimePlace (prime : Nat.Primes) (h3 : prime.val ≠ 3) :
    placeThree ≠ integralPrimePlace prime := by
  intro h
  apply h3
  have equal : primeThree = prime := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective h
  exact (congrArg Subtype.val equal).symm

/-- The reduction modulo three of the outside compact is that of the integral Hecke matrix. -/
theorem outsideCompact_reduction_entry (prime : Nat.Primes) (h3 : prime.val ≠ 3)
    (index : Option (Fin prime.val)) (row column : Fin 2) :
    (GeneralLinearGroup.map integralReduction (binaryHeckeOutsideCompact prime index)).val
        row column =
      integralReduction (binaryHeckeIntegralMatrix prime index row column) := by
  have different := placeThree_ne_integralPrimePlace prime h3
  change integralReduction ((binaryHeckeOutsideCompact prime index).val row column) = _
  rw [binaryHeckeOutsideCompact_val]
  apply integralReduction_congr
  rw [binaryHeckeOutsideMatrix, ite_eq_right different]

theorem natCast_zmod_three_ne_zero_of_prime {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    (p : ZMod 3) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm

/-- **The outside compact of a Hecke representative fixes every level-three vector.** -/
theorem levelThree_outsideCompact_fixed (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (prime : Nat.Primes) (h3 : prime.val ≠ 3) (index : Option (Fin prime.val)) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding
      (binaryHeckeOutsideCompact prime index))) v.val = v.val := by
  have e10 : (GeneralLinearGroup.map integralReduction
      (binaryHeckeOutsideCompact prime index)).val 1 0 = 0 := by
    rw [outsideCompact_reduction_entry prime h3 index 1 0]
    cases index <;> simp [binaryHeckeIntegralMatrix]
  have e11 : (GeneralLinearGroup.map integralReduction
        (binaryHeckeOutsideCompact prime index)).val 1 1 = 1 ∨
      (GeneralLinearGroup.map integralReduction
        (binaryHeckeOutsideCompact prime index)).val 1 1 = -1 := by
    rw [outsideCompact_reduction_entry prime h3 index 1 1]
    cases index with
    | none =>
      left
      simp [binaryHeckeIntegralMatrix]
    | some j =>
      have nonzero := natCast_zmod_three_ne_zero_of_prime prime.property h3
      have cases_three : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
      have entry : integralReduction (binaryHeckeIntegralMatrix prime (some j) 1 1) =
          (prime.val : ZMod 3) := by
        simp [binaryHeckeIntegralMatrix]
      rw [entry]
      exact cases_three _ nonzero
  rcases e11 with e | e
  · exact hv (binaryHeckeOutsideCompact prime index) (And.intro e10 e)
  · have level := planeLeviLevel_mul_negOne e10 e
    have fixed := hv _ level
    rw [map_mul, atFinite_mul, map_mul, Module.End.mul_apply,
      levelThree_negOne_fixed σ halfWeight v rotation] at fixed
    exact fixed

/-- The localized representatives act on a level-three vector as the Hecke representatives. -/
theorem levelThree_heckeLocalized_eq (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (prime : Nat.Primes) (h3 : prime.val ≠ 3) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) (index : Option (Fin prime.val)) :
    σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) v.val =
      (cuspFiniteRationalSlash σ (binaryHeckeRepresentative prime index) v).val := by
  rw [binaryHeckeLocalized, _root_.mul_inv_rev, inv_inv, atFinite_mul, map_mul,
    Module.End.mul_apply,
    levelThree_outsideCompact_fixed σ halfWeight prime h3 index v hv rotation]
  change _ = σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (binaryHeckeRepresentative prime index)⁻¹)) v.val
  rw [map_inv]

/-- The Hecke sum of a level-three vector is the sum of the localized representatives. -/
theorem cuspPrimeHeckeSum_levelThree_eq_sum (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (prime : Nat.Primes) (h3 : prime.val ≠ 3) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    (cuspPrimeHeckeSum σ prime v).val =
      ∑ index : Option (Fin prime.val),
        σ.π (atFinite (binaryHeckeLocalized prime index)⁻¹) v.val := by
  rw [cuspPrimeHeckeSum_eq_sum]
  exact Finset.sum_congr rfl (fun index _ =>
    (levelThree_heckeLocalized_eq σ halfWeight prime h3 v hv rotation index).symm)

end TernaryPeriodPolynomials.MultiplicityOne
