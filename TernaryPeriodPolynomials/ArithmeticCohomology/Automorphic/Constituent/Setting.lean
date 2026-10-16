module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Final
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.TypeSpace
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Continuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.ModelFamily

@[expose] public section


/-!
# The setting of the Bergman model of the lifts of weight `n + 3`

The common vocabulary for the cuspidal constituents of the model:

* `bergmanModel n`: the finite-adelic model of the adelic lifts of *all* cusp forms of weight
  `n + 3` for `Γ₁(3)` (`Regularity.lifts`), whose holomorphic model is the Bergman space
  `BergmanSpace (n + 3) (bergmanModel n).E` with the unitary representation `bergmanRep` of
  `GL₂(𝔸)`, realized by `realizationUnitary` (`n ≥ 3`);
* `bergmanK`: the level group `K'` of `Γ₁(3)` (`CuspIntegral.levelGroup`), which is the
  group of `levelThreeValues`;
* `typeSpace n`: the finite-dimensional type subspace of weight `-(n + 3)` and level `bergmanK`
  (lowest weight vectors of `K'`-fixed vectors);
* `Piece n`: a compression-simple subspace `N` of the type space with a nonzero vector `v`,
  and `Piece.cusp` its cuspidal representation on the closed cyclic span of `v`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
open TernaryPeriodPolynomials.Regularity
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryRealGammaOneThree)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- The level group `K'` of `Γ₁(3)`. -/
abbrev bergmanK : Subgroup BinaryFiniteGL :=
  TernaryPeriodPolynomials.CuspIntegral.levelGroup

/-- The finite-adelic model of the lifts of all cusp forms of weight `n + 3` for `Γ₁(3)`. -/
def bergmanModel (n : ℕ) : FiniteModel (n + 3) :=
  lifts (Set.univ : Set (CuspForm binaryRealGammaOneThree (((n + 3 : ℕ)) : ℤ)))

instance factTwoLeAddThree (n : ℕ) : Fact (2 ≤ n + 3) := ⟨by omega⟩

/-- The type subspace of weight `-(n + 3)` and level `K'` of the Bergman model. -/
abbrev typeSpace (n : ℕ) : Submodule ℂ (BergmanSpace (n + 3) (bergmanModel n).E) :=
  typeSubspace (bergmanRep (bergmanModel n)) (TypeData.typeGroup bergmanK)
    (Weight.typeCharacterInv (n + 3) bergmanK)

/-- The type space is finite dimensional. -/
instance typeSpace_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (typeSpace n) :=
  finiteDimensional_typeSubspace (bergmanModel n) (by omega) levelGroup_isOpenCompact

/-- A cuspidal constituent datum: a compression-simple subspace of the type space and a nonzero
vector in it. -/
structure Piece (n : ℕ) where
  /-- The compression-simple subspace. -/
  N : Submodule ℂ (BergmanSpace (n + 3) (bergmanModel n).E)
  /-- Compression simplicity. -/
  simple : CompressionSimple (bergmanRep (bergmanModel n)) (TypeData.typeGroup bergmanK)
    (Weight.typeCharacterInv (n + 3) bergmanK) N
  /-- The distinguished vector. -/
  v : BergmanSpace (n + 3) (bergmanModel n).E
  /-- The vector lies in `N`. -/
  mem : v ∈ N
  /-- The vector is nonzero. -/
  ne : v ≠ 0

/-- The cuspidal representation of a constituent (`n ≥ 3`): the closed cyclic span of `v`. -/
def Piece.cusp {n : ℕ} (hn : 3 ≤ n) (c : Piece n) : CuspidalRepresentation :=
  ModelFamily.cyclicOfLE (S := typeSpace n)
    (realizationUnitary (bergmanModel n) (by omega))
    (continuous_bergmanRep (by omega) (bergmanModel n))
    (TypeData.typeGroup bergmanK) (Weight.typeCharacterInv (n + 3) bergmanK)
    c.simple.le_typeSubspace c.simple c.mem c.ne

end TernaryPeriodPolynomials.Automorphic.Constituent
