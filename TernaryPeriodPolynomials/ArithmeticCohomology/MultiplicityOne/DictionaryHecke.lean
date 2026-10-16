module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryHeckeOmega
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Hecke

@[expose] public section


/-!
# The Hecke eigenvalue of a classical level-three vector

For a prime `p ≠ 3` and a classical level-three vector `v` the cusp form `levelThreeForm v` is an
eigenform of the Hecke operator `T_p` of `S_k(Γ₁(3))`, `k = -2 * halfWeight`, with eigenvalue

  `levelThreeEigenvalue σ halfWeight p = p^(-halfWeight - 1) · (p + 1) · ω(diag(p,1)⁻¹)`,

where `ω = omega σ` is the Satake scalar of the compression to the `GL₂(ℤ̂^{(3)})`-fixed
vectors. The computation is the same for every vector fixed by that group, in particular for
spherical vectors:
`levelThreeHeckeScalar` is the eigenvalue of `cuspPrimeHeckeSum σ p` on any nonzero vector of
`levelThreeValues σ`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.HeckeEigen.Satake

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- The eigenvalue of `cuspPrimeHeckeSum σ p` on the nonzero vectors of `levelThreeValues σ`:
`(p + 1) · ω(diag(p,1)⁻¹)`. -/
def levelThreeHeckeScalar (σ : CuspidalRepresentation) (p : Nat.Primes) : ℂ :=
  ((p.val : ℂ) + 1) * omega σ (Bo (dP p.property)⁻¹)

/-- The eigenvalue of the classical Hecke operator `T_p` of weight `-2 * halfWeight` on the cusp
form of a classical level-three vector: `p^(-halfWeight - 1)` times `levelThreeHeckeScalar`. -/
def levelThreeEigenvalue (σ : CuspidalRepresentation) (halfWeight : ℤ) (p : Nat.Primes) : ℂ :=
  (p.val : ℂ) ^ (-halfWeight - 1) * levelThreeHeckeScalar σ p

theorem cuspPrimeHeckeSum_levelThreeHeckeScalar (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (p : Nat.Primes) (hp : p.val ≠ 3) (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val) :
    cuspPrimeHeckeSum σ p v = levelThreeHeckeScalar σ p • v :=
  cuspPrimeHeckeSum_levelThree σ halfWeight p hp v hv rotation

theorem levelThreeChar_neg_two_mul (halfWeight : ℤ) (n : ℕ) :
    LevelThree.LevelThreeHecke.levelThreeChar (-2 * halfWeight) n = 1 := by
  unfold LevelThree.LevelThreeHecke.levelThreeChar
  split_ifs
  · exact Even.neg_one_zpow ⟨-halfWeight, by ring⟩
  · rfl

/-- **`levelThreeForm v` is a `T_p`-eigenform.** -/
theorem levelThreeHecke_levelThreeForm (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (p : Nat.Primes) (hp : p.val ≠ 3)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    LevelThree.LevelThreeHecke.levelThreeHecke (-2 * halfWeight) p hp
        (levelThreeForm σ halfWeight negative v hv) =
      levelThreeEigenvalue σ halfWeight p • levelThreeForm σ halfWeight negative v hv := by
  have eigen := cuspPrimeHeckeSum_levelThreeHeckeScalar σ halfWeight p hp v hv.1 hv.2.1
  ext τ
  rw [LevelThree.LevelThreeHecke.levelThreeHecke_apply]
  have rel := cuspPrimeHeckeSum_eigen_relation σ central_positive halfWeight v hv.2.1 p
    (levelThreeHeckeScalar σ p) eigen τ
  have form_apply : ∀ τ' : UpperHalfPlane, (levelThreeForm σ halfWeight negative v hv) τ' =
      cuspScalarWeightedRealization σ halfWeight v 1 τ' := fun _ => rfl
  have smul_apply :
      (levelThreeEigenvalue σ halfWeight p • levelThreeForm σ halfWeight negative v hv) τ =
        levelThreeEigenvalue σ halfWeight p * cuspScalarWeightedRealization σ halfWeight v 1 τ :=
    rfl
  rw [smul_apply, levelThreeChar_neg_two_mul, one_mul]
  simp only [form_apply, binaryHeckeDilate_smul, binaryHeckeTranslate_smul]
  exact rel.symm

end TernaryPeriodPolynomials.MultiplicityOne
