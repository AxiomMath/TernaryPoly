module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.Classical
public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.GoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.BadLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Final

@[expose] public section


/-!
# Rank two at a level-three cusp forces sphericity

Let `D` have trivial character and a nonzero associate pair, `3 ≤ n`, and let `c` be the pair
character. At the good plane `(.plane, true)` and at the bad line `(.line, false)` the local joint
generalized eigenspace of `c` embeds into the joint generalized eigenspace of the classical Hecke
operators on `S_{n+3}(Γ₁(3))` with eigenvalues `λ_p = p^{n+1} (c(T_p) - 1)`, given injectivity of
the parity-projected period map (`finrank_localJoint_goodPlane_le`,
`finrank_localJoint_badLine_le`). That space has dimension at most two. If the local space has
dimension two, so does the classical one, so it contains an oldform: a nonzero level-one cusp form
`f` of weight `n + 3` with `T_p f = λ_p f` for `p ≠ 3`, and `n` is odd
(`exists_levelOne_of_finrank_jointGen_two`). By the closed form of the pair character,
`λ_p = levelOneEigenvalue n D.cusp p` (`pair_scalar_closed_form`). Then `D.cusp` is spherical: if
not, `D` has a nonzero level-three vector, hence a nonzero holomorphic level-three vector of weight
`n + 3` (the level-three bridge), which the level-one eigenform `f` kills by the trace argument
 (`levelThreeVector_eq_zero`).

* `sphericalCusp_of_levelOne_eigenform`: the M1 step;
* `sphericalCusp_of_finrank_jointGen_two`: from a two-dimensional classical eigenspace;
* `sphericalCusp_of_rankTwo_goodPlane`, `sphericalCusp_of_rankTwo_badLine`: the two cusps, with
  the injectivity of the period map as a hypothesis.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.MultiplicityOne
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

namespace TernaryPeriodPolynomials.RankTwo

variable {n : ℕ}

/-- **A level-one eigenform with the eigenvalues of `D` forces sphericity** (M1's matching): for
`n` odd and a nonzero pair, a nonzero level-one cusp form of weight `n + 3` with
`T_p f = levelOneEigenvalue n D.cusp p • f` for all `p ≠ 3` makes `D.cusp` spherical. -/
theorem sphericalCusp_of_levelOne_eigenform (D : InducingData n) (hne : associatePair D ≠ ⊥)
    (hodd : Odd n) {k : ℤ} (hk : k = (n : ℤ) + 3) {f : CuspForm LevelOneHecke.levelOne k}
    (hf0 : f ≠ 0)
    (hf : ∀ p : Nat.Primes, p.val ≠ 3 →
      LevelOneHecke.levelOneHecke k p f = levelOneEigenvalue n D.cusp p • f) :
    SphericalCusp D.cusp := by
  by_contra hns
  obtain ⟨halfWeight, hw, v, hv, hv0⟩ := levelThreeBridge D.cusp n hodd D.cohomological
    (exists_levelThree_of_not_spherical D hne hns)
  have key : ∀ (k' : ℤ) (f' : CuspForm LevelOneHecke.levelOne k'), k' = -2 * halfWeight →
      f' ≠ 0 → (∀ p : Nat.Primes, p.val ≠ 3 →
        LevelOneHecke.levelOneHecke k' p f' = levelOneEigenvalue n D.cusp p • f') → False := by
    rintro k' f' rfl hf0' hf'
    exact hv0 (levelThreeVector_eq_zero D.cusp hodd
      (cohomological_centralCharacter_positive D.cusp D.cohomological) hns hw hf0' hf' v hv)
  exact key k f (by omega) hf0 hf

/-- **A two-dimensional classical joint eigenspace with the pair eigenvalues forces sphericity.**
If the joint generalized eigenspace of `T_p` (`p ≠ 3`) on `S_{n+3}(Γ₁(3))` with eigenvalues
`eig` has dimension two, and `eig p = p^{n+1} (c(T_p) - 1)` for the pair character `c`, then
`D.cusp` is spherical. -/
theorem sphericalCusp_of_finrank_jointGen_two (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (eig : Nat.Primes → ℂ)
    (heig : ∀ p : Nat.Primes, p.val ≠ 3 →
      eig p = (p.val : ℂ) ^ (n + 1) * (pairCharacter D hecke hhecke (TpExistence.tp p) - 1))
    (h2 : Module.finrank ℂ
      (LevelThree.LevelThreeJointGen.jointGenEigenspace (((n + 1 : ℕ) : ℤ) + 2) eig) =
        2) :
    SphericalCusp D.cusp := by
  obtain ⟨heven, g, hg0, hg⟩ := exists_levelOne_of_finrank_jointGen_two h2
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with hn | hn
    · exfalso
      obtain ⟨j, hj⟩ := hn
      obtain ⟨i, hi⟩ := heven
      omega
    · exact hn
  refine sphericalCusp_of_levelOne_eigenform D hne hodd (by omega) hg0 (fun p hp => ?_)
  rw [LevelOneMultiplicityOne.mem_eigenspaceAwayThree.mp hg p hp, heig p hp,
    pair_scalar_closed_form D hχ hecke hhecke hne hodd p hp]

/-- **Rank two at the good plane forces sphericity** (trivial character, `3 ≤ n`, nonzero pair),
given injectivity of the parity-projected period map `levelPeriodMap (n + 1) (-1)`. -/
theorem sphericalCusp_of_rankTwo_goodPlane (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1)))
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (h2 : Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) .plane true) = 2) :
    SphericalCusp D.cusp := by
  have hc := pairChar_two_bound D hχ hecke hhecke hn hne
  rw [hχ] at h2
  have hle := finrank_localJoint_goodPlane_le n (by omega) (pairCharacter D hecke hhecke) hc hinj
  have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) + 2 := by omega
  have hup := LevelThree.LevelThreeJointGen.finrank_jointGenEigenspace_le_two hpos
    (LevelThree.LevelThreePeterssonSemisimple.levelThree_semisimple
      (((n + 1 : ℕ) : ℤ) + 2))
    (fun q => (pairCharacter D hecke hhecke (TpExistence.tp q) - 1) /
      ((q.val : ℂ) ^ (n + 2))⁻¹ / ((q.val : ℂ) ^ (-(-1 : ℤ))))
  have h2' := le_antisymm hup (h2.symm.le.trans hle)
  refine sphericalCusp_of_finrank_jointGen_two D hχ hecke hhecke hne _ (fun p _ => ?_) h2'
  exact goodPlane_eigenvalue n _ _ (by exact_mod_cast p.property.ne_zero)

/-- **Rank two at the bad line forces sphericity** (trivial character, `3 ≤ n`, nonzero pair),
given injectivity of the parity-projected period map `levelPeriodMap (n + 1) 0`. -/
theorem sphericalCusp_of_rankTwo_badLine (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0))
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (h2 : Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) .line false) = 2) :
    SphericalCusp D.cusp := by
  have hc := pairChar_two_bound D hχ hecke hhecke hn hne
  rw [hχ] at h2
  have hle := finrank_localJoint_badLine_le hn (pairCharacter D hecke hhecke) hc hinj
  have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) + 2 := by omega
  have hup := LevelThree.LevelThreeJointGen.finrank_jointGenEigenspace_le_two hpos
    (LevelThree.LevelThreePeterssonSemisimple.levelThree_semisimple
      (((n + 1 : ℕ) : ℤ) + 2))
    (fun q => (pairCharacter D hecke hhecke (TpExistence.tp q) - 1) /
      ((q.val : ℂ) ^ (n + 1))⁻¹ / 1)
  have h2' := le_antisymm hup (h2.symm.le.trans hle)
  refine sphericalCusp_of_finrank_jointGen_two D hχ hecke hhecke hne _ (fun p _ => ?_) h2'
  exact badLine_eigenvalue n _ _

end TernaryPeriodPolynomials.RankTwo
