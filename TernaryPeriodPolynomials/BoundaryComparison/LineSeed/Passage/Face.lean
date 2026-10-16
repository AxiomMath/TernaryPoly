module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Seed
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN

@[expose] public section


/-!
# The line seed classes at every line cusp of `Γ(N)`, and the boundary vector `lineSeedBoundary` (Passage 3)

Line mirror of `SeedC3S4c.PlaneCusps.faceSeedKerClass` and `FormClassK.GammaNConstantTerms.seedBoundary`.  For `h ∈ SL₃(ℤ)` the line cusp
`Q' = h⁻¹ Q h` of `Γ(N)` has the seed classes `h^*[σ_f]`, `h^*[\overline{σ_f}]` of `f ∈ S_{n+3}(Γ₂(N))` (the paper's "rationally conjugate the other cusps
to the standard one"): the standard classes `lineNSeedKerClass`, transported by the conjugation `lineFaceKerMap`.  `lineSeedBoundary f` is the vector, over the
line faces `i` of `Γ(N)` (representative `i.rep`), of the sum of the holomorphic seed class of `f i false` and the antiholomorphic seed class of `f i true`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The class of the holomorphic line seed at the line cusp `h⁻¹ Q h`: the transport `h^*[σ_f]` of the seed class of `f ∈ S_{n+3}(Γ₂(N))` at `Q`. -/
def lineFaceSeedKerClass (h : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)).ker :=
  lineFaceKerMap N h n (lineNSeedKerClass f)

/-- The class of the antiholomorphic line seed at the line cusp `h⁻¹ Q h`. -/
def lineFaceSeedConjKerClass (h : SL(3, ℤ)) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    ↥(twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)).ker :=
  lineFaceKerMap N h n (lineNSeedConjKerClass f)

open scoped Classical in
/-- **The boundary vector of line seed classes**: at the line face `i` (representative `i.rep`) the class of the holomorphic seed of `f i false` plus the
class of the antiholomorphic seed of `f i true`, transported to the cusp `i.rep`. -/
def lineSeedBoundary (f : LineFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) : LineFaceH2 N n :=
  ∑ i : LineFaces N, DirectSum.lof ℂ (LineFaces N) (fun i => groupCohomology.H2 (lineFaceRep N i.rep n)) i
    ((lineFaceSeedKerClass N n i.rep (f i false)).1 + (lineFaceSeedConjKerClass N n i.rep (f i true)).1)

open scoped Classical in
theorem lineSeedBoundary_apply (f : LineFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (i : LineFaces N) :
    lineSeedBoundary N n f i =
      (lineFaceSeedKerClass N n i.rep (f i false)).1 + (lineFaceSeedConjKerClass N n i.rep (f i true)).1 := by
  unfold lineSeedBoundary
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [DirectSum.lof_eq_of]
  · intro j _ hj
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
  · simp

end TernaryPeriodPolynomials.Argument.LineSeed
