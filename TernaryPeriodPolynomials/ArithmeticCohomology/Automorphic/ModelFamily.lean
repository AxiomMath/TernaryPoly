module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.CyclicRepresentation

@[expose] public section


/-!
# Cuspidal constituents inside a finite-dimensional type space

`cyclicOfLE` is `cyclicCuspidal` for a compression-simple subspace `N` contained in a
finite-dimensional subspace `S` of the type subspace (so `N` is finite-dimensional), and
`compressionStable_typeSubspace` records that the whole type subspace is compression-stable: the
compression of a vector of the type subspace is its orthogonal projection onto the type subspace.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
open TernaryPeriodPolynomials.Automorphic.CyclicRepresentation

namespace TernaryPeriodPolynomials.Automorphic.ModelFamily

section Generic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : Representation ℂ BinaryAdelicGL H} [IsUnitary π]

/-- `cyclicCuspidal` for a compression-simple subspace `N` contained in a finite-dimensional
subspace `S`. -/
def cyclicOfLE (R : Realization π IsUnitary.norm_map)
    (hc : ∀ v, Continuous (fun g => π g v)) (C : Subgroup BinaryAdelicGL) (χ : C → ℂ)
    {S N : Submodule ℂ H} [FiniteDimensional ℂ S] (hNS : N ≤ S)
    (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0) :
    CuspidalRepresentation :=
  have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNS
  cyclicCuspidal R hc C χ hN hvN hv

end Generic

/-- The type subspace is compression-stable. -/
theorem compressionStable_typeSubspace {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : Representation ℂ BinaryAdelicGL H) [IsUnitary π]
    (C : Subgroup BinaryAdelicGL) (χ : C → ℂ) :
    CompressionStable π C χ (typeSubspace π C χ) := fun _ _ _ =>
  Submodule.starProjection_apply_mem (typeSubspace π C χ) _

end TernaryPeriodPolynomials.Automorphic.ModelFamily
