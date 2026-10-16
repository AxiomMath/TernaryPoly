module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDRadical

@[expose] public section


/-!
# The Koszul pairing of the plane radicals (identity plane `P₀`, good plane `P₁`)

Formalized by Claude Sonnet 5.5.

`FacePDRadical.latticeKoszul`/`latticeKoszul_perfect` are stated for an arbitrary embedded radical lattice `Ω ≤ rationalLevel`: the
Koszul pairing of the generator values `H¹(Ω, E) × H¹(Ω, E^φ) → ℂ` is perfect in both arguments.  The four lattices of the
boundary trace are `latL0`, `latL1` (line radicals, bad and good line) and `latP0`, `latP1` (plane radicals, identity and good
plane).  This file records the plane cases, so that the torus-fibre factor of `ar:eq:facepair` is perfect for both families of
faces.  (The explicit constants against the invariant pairing of `Sym^{n+1}` are those of the line lattices
`badLine_koszul_eq_binaryPairing(_odd)`, `goodLine_koszul_eq_binaryPairing`; for the plane faces they follow from the swap relation
`⟨B, A⟩_Q = ± ⟨A, B⟩_P` of the face pairings, not from a separate Kostant computation at the plane lattices.)
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latP0 latP1)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

/-- **The Koszul pairing of the identity-plane radical is perfect.** -/
theorem latP0_koszul_perfect (n : ℕ) (χ : RankOneCharacter) :
    letI := homogeneousPoly_finite n
    (∀ a : (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).H1,
        (∀ b : (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).H1',
          (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).pairing a b = 0) → a = 0) ∧
      ∀ b : (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).H1',
        (∀ a : (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).H1,
          (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).pairing a b = 0) → b = 0 :=
  latticeKoszul_perfect n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)

/-- **The Koszul pairing of the good-plane radical is perfect.** -/
theorem latP1_koszul_perfect (n : ℕ) (χ : RankOneCharacter) :
    letI := homogeneousPoly_finite n
    (∀ a : (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).H1,
        (∀ b : (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).H1',
          (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).pairing a b = 0) → a = 0) ∧
      ∀ b : (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).H1',
        (∀ a : (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).H1,
          (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).pairing a b = 0) → b = 0 :=
  latticeKoszul_perfect n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)

/-- The Koszul pairing of the generator values of `U`-equivariant cocycles at a plane lattice is the library's fibre pairing
`κ(f, g) = ⟨f ⌣ g, σ⟩`. -/
theorem latP0_koszul_eq_kostant (n : ℕ) (χ : RankOneCharacter)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : FiberKostant.UCocycle (FiberL1.dualRep (TraceRepresentatives.dualityData n χ)) latP0.sub g) :
    (latticeKoszul n χ latP0 (fun _ h => (L2Assembly.latP0_le h).1)).Phi
        (f ![1, latP0.u 1 0], f ![1, latP0.u 0 1]) (g ![1, latP0.u 1 0], g ![1, latP0.u 0 1]) =
      FiberFormula.kostant (TraceRepresentatives.dualityData n χ).B latP0.σ f g :=
  latticeKoszul_eq_kostant n χ latP0 _ hg

theorem latP1_koszul_eq_kostant (n : ℕ) (χ : RankOneCharacter)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : FiberKostant.UCocycle (FiberL1.dualRep (TraceRepresentatives.dualityData n χ)) latP1.sub g) :
    (latticeKoszul n χ latP1 (fun _ h => (L2Assembly.latP1_le h).1)).Phi
        (f ![1, latP1.u 1 0], f ![1, latP1.u 0 1]) (g ![1, latP1.u 1 0], g ![1, latP1.u 0 1]) =
      FiberFormula.kostant (TraceRepresentatives.dualityData n χ).B latP1.σ f g :=
  latticeKoszul_eq_kostant n χ latP1 _ hg

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD
