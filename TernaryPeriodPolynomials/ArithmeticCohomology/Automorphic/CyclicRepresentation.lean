module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SubRepresentation
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.AbstractIrreducibility

@[expose] public section


/-!
# Cuspidal representations from compression-simple vectors

Combining the compression criterion `AbstractIrreducibility.cyclicSpan_isIrreducible` with the
restriction of a `Realization` to a closed invariant subspace
(`SubRepresentation.Realization.cuspidalOfInvariant`): the closed cyclic span of a nonzero vector
of a finite-dimensional compression-simple subspace of the type subspace of a realized unitary
representation is the Hilbert space of a `CuspidalRepresentation`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility

namespace TernaryPeriodPolynomials.Automorphic.CyclicRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : Representation ℂ BinaryAdelicGL H} [IsUnitary π]

/-- The cuspidal representation on the closed cyclic span of a nonzero vector of a
finite-dimensional compression-simple subspace. -/
def cyclicCuspidal (R : Realization π IsUnitary.norm_map)
    (hc : ∀ v, Continuous (fun g => π g v)) (C : Subgroup BinaryAdelicGL) (χ : C → ℂ)
    {N : Submodule ℂ H} [FiniteDimensional ℂ N]
    (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0) :
    CuspidalRepresentation :=
  let h := cyclicSpan_isIrreducible π C χ hN hvN hv
  R.cuspidalOfInvariant hc h.2.1 h.1 (fun g w hw => h.2.2.1 g w hw) h.2.2.2

/-- The Hilbert space of `cyclicCuspidal` is the closed cyclic span. -/
theorem cyclicCuspidal_H (R : Realization π IsUnitary.norm_map)
    (hc : ∀ v, Continuous (fun g => π g v)) (C : Subgroup BinaryAdelicGL) (χ : C → ℂ)
    {N : Submodule ℂ H} [FiniteDimensional ℂ N]
    (hN : CompressionSimple π C χ N) {v : H} (hvN : v ∈ N) (hv : v ≠ 0) :
    (cyclicCuspidal R hc C χ hN hvN hv).H = cyclicSpan π v := rfl

/-- Every vector of a finite-dimensional compression-stable subspace of the type subspace is a
finite sum of vectors of compression-simple subspaces; each nonzero summand `u_N` spans the
Hilbert space `cyclicSpan π u_N` of a `cyclicCuspidal` representation. -/
theorem exists_sum_compressionSimple (C : Subgroup BinaryAdelicGL) (χ : C → ℂ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hS : S ≤ typeSubspace π C χ)
    (hSs : CompressionStable π C χ S) {u : H} (hu : u ∈ S) :
    ∃ s : Finset (Submodule ℂ H), (∀ N ∈ s, N ≤ S ∧ CompressionSimple π C χ N) ∧
      ∃ μ : (N : Submodule ℂ H) → N, ∑ N ∈ s, (μ N : H) = u := by
  obtain ⟨s, hs, hus⟩ := exists_finset_compressionSimple π C χ hS hSs hu
  exact ⟨s, hs, (Submodule.mem_iSup_finset_iff_exists_sum (fun N : Submodule ℂ H => N) u).mp hus⟩

end TernaryPeriodPolynomials.Automorphic.CyclicRepresentation
