module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.Scalar

@[expose] public section


/-!
# Lemma 4.5 with the exponent-`+1` Hom-model correspondence and the exact scalar

Formalized by Claude Sonnet 5.5.

Scope: the library Hom model only (see `Scalar.lean`); not a statement about the paper's homology operator.

The downstream
argument never uses the printed identification of `T₂(p)` with the standard `T_p`; it uses

* Hecke stability of the liftable residue space under `T₂(p)`, and
* the Eichler-Shimura correspondence between `T₂(p)` and `T_p` on the period space *up to a nonzero scalar*.

Both hold for the exponent-`+1` Hom-model correspondence, whose scalar relative to `T_p` is `p^{d-1}`
(`homPlus_intertwines`): `periodMap (T_p f) = p^{d-1} • homPlusComplexHecke p (periodMap f)`.  Hence the
simultaneous-eigenperiod argument goes through verbatim for it (`stable_extreme_kernel_eq_bot_homPlus`,
`actualLiftable_complex_eq_bot_homPlus`).  The same conclusion for any other nonzero scalar multiple of the
standard operators is `TernaryPoly.BinaryCuspPeriodDetection` (`Intertwines`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.BinaryComplexPeriod TernaryPoly.BinaryCuspPeriod
open TernaryPoly.BinaryCuspPeriodDetection

/-- The exponent-`+1` Hom-model `T₂(p)` on the complex period space, indexed by `Nat.Primes`. -/
def homPlusPeriodHecke (d : ℕ) (p : Nat.Primes) : Module.End ℂ (space ℂ d) :=
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  homPlusComplexHecke d p.val

/-- The exact Hecke scalar `p^{d-1}` relating `T_p` and the exponent-`+1` Hom-model `T₂(p)` on periods. -/
def homPlusScalar (d : ℕ) (p : Nat.Primes) : ℂ := (p.val : ℂ) ^ ((d : ℤ) - 1)

theorem homPlusScalar_ne_zero (d : ℕ) (p : Nat.Primes) : homPlusScalar d p ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.mpr (BinaryCuspHecke.prime_pos p).ne')

/-- **`periodMap (T_p f) = p^{d-1} • T₂(p) (periodMap f)`**: the literal scalar intertwining of the
cusp-to-period map with the exponent-`+1` Hom-model correspondence. -/
theorem homPlus_intertwines (d : ℕ) (hd : Even d) :
    Intertwines d hd (homPlusPeriodHecke d) (homPlusScalar d) := by
  intro p f
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  change periodMap d hd (BinaryCuspHeckeEndomorphism.T d p.val f) =
    homPlusScalar d p • homPlusComplexHecke d p.val (periodMap d hd f)
  rw [homPlus_periodMap_zpow hd f p.val, smul_smul, homPlusScalar, ← zpow_add₀
    (Nat.cast_ne_zero.mpr (BinaryCuspHecke.prime_pos p).ne')]
  simp

/-- **The eigenperiod argument of Lemma 4.5 for the exponent-`+1` Hom-model `T₂(p)`**: a complex period subspace that
is stable under every such `T₂(p)` and annihilated by the extreme coefficient `[XY^{d-1}]` is zero. -/
theorem stable_extreme_kernel_eq_bot_homPlus (d : ℕ) (hd : Even d)
    (L : Submodule ℂ (space ℂ d))
    (hs : ∀ p q, q ∈ L → homPlusPeriodHecke d p q ∈ L)
    (hz : ∀ q ∈ L, extreme ℂ d q = 0) : L = ⊥ := by
  have hI := homPlus_intertwines d hd
  have hbij := periodMap_bijective_of_intertwines d hd (homPlusPeriodHecke d) (homPlusScalar d) hI
  have hcomm : ∀ p q, Commute (homPlusPeriodHecke d p) (homPlusPeriodHecke d q) := fun p q =>
    commute_of_intertwines d hd hbij.surjective (homPlusPeriodHecke d) (homPlusScalar d)
      (homPlusScalar_ne_zero d) hI p q
  apply CommutingEigenvector.eq_bot_of_functional (homPlusPeriodHecke d) hcomm (extreme ℂ d) ?_ L hs hz
  intro q hq he
  choose a ha using he
  exact extreme_ne_zero_of_intertwining_eigenperiod d hd (homPlusPeriodHecke d) (homPlusScalar d) hI
    q hq a ha

/-- The complexified liftable residue space is stable under the exponent-`+1` Hom-model `T₂(p)`
(`T₂(p) = p² ·` the exponent `-1` operator, whose stability is
`BinaryLiftableResidueDetection.actualLiftable_complex_stable`). -/
theorem actualLiftable_complex_stable_homPlus (n : ℕ) (p : Nat.Primes) :
    ∀ q ∈ complexSpan (n + 1) (actualLiftable n),
      homPlusPeriodHecke (n + 1) p q ∈ complexSpan (n + 1) (actualLiftable n) := by
  intro q hq
  let : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
  have h := BinaryLiftableResidueDetection.actualLiftable_complex_stable n p q hq
  change homPlusComplexHecke (n + 1) p.val q ∈ _
  rw [homPlusComplexHecke_eq, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ h

/-- **Lemma 4.5 for the exponent-`+1` Hom-model `T₂(p)`**: in odd ternary degree the complexified liftable residue
space vanishes, using only stability under `T₂(p)` (exponent `+1`) and the scalar `p^{d-1}` of
`homPlus_intertwines`; the printed identification of `T₂(p)` with `T_p` is not used. -/
theorem actualLiftable_complex_eq_bot_homPlus (n : ℕ) (hn : Odd n) :
    complexSpan (n + 1) (actualLiftable n) = ⊥ :=
  stable_extreme_kernel_eq_bot_homPlus (n + 1) (BinaryLiftableResidueDetection.successor_even hn)
    (complexSpan (n + 1) (actualLiftable n)) (actualLiftable_complex_stable_homPlus n)
    (actualLiftable_complex_extreme n)

end TernaryPeriodPolynomials.Argument.HeckeNormalization
