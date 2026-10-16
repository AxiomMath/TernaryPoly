module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.AvInv
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# The torus average on the face of `Γ(N)`, and the reduction of `ConstantTermVanishing`

(unfolding, "the binary root average
is zero by cuspidality").

* `latticeData_gammaN`: the plane group `Γ_P = Γ(N) ∩ P(ℤ)` has integral Levi blocks (`Γ₂(N) ⊂ SL₂(ℤ)`)
  and realizes the radical lattice `Nℤ²`, so `avInv n (latticeData_gammaN N)` is a linear map on the
  closed `Γ_P`-invariant forms of the face.
* `AveragePreservesClass N n` (obligation (a), Kasuya in the abelian case): the average does not change
  the de Rham class.
* `RestAverageVanishes N n f hn` (obligation (b), unfolding): the average of `restFaceForm` is zero.
* `constantTermVanishing_of_average`: (a) and (b) imply `ConstantTermVanishing N n f hn`, hence
  (`resP_eisensteinClass_iff`) the constant-term identity `r_P [𝓔_P(ω_h)] = [seed of f]`.

(a) and (b) are propositions defined here. (a) is proved as `averagePreservesClass` (`AveragePreserves.lean`; Cartan/Koszul homotopies
and a normalized zig-zag) and (b) as `restAverageVanishes` (`RestAverage.lean`; unfolding over the orbits of
the radical lattice, hypotheses `3 ≤ N`, `4 ≤ n`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory
open scoped MatrixGroups
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3S4c

theorem latticeData_gammaN (N : ℕ) [NeZero N] : LatticeData (gammaNPlaneData N) (N : ℝ) := by
  refine ⟨fun g => ?_, fun k => ?_⟩
  · obtain ⟨A, -, hA⟩ := gammaNPlaneData_lam_mem N g⁻¹
    refine ⟨A, ?_⟩
    rw [← hA, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    ext i j
    simp
  · refine ⟨gammaNInl N (Multiplicative.ofAdd (k 0, k 1)), ?_, ?_⟩
    · have := gammaN_lamM_inl (N := N) (Multiplicative.ofAdd (k 0, k 1))
      exact this
    · have := gammaN_w_inl (N := N) (Multiplicative.ofAdd (k 0, k 1))
      rw [this]
      funext i
      fin_cases i <;> simp [intVec]

section Reduction

open TernaryPoly.SmoothLocalDeRham TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Obligation (a), Kasuya for the abelian radical `Nℤ²`.** Averaging over the nilmanifold
`Nℤ² \\ ℝ²` (with coefficient transport) does not change the de Rham class in `H²(Γ_P, E_n)`.
Proved as `averagePreservesClass`. -/
def AveragePreservesClass : Prop :=
  ∀ F : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n),
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) (avInv n (latticeData_gammaN N) F) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n) F

variable (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **Obligation (b), the unfolded zero modes.** The torus average of the non-identity part of the
series vanishes (unfolding over the nontrivial double coset, vanishing of the constant term of the
cusp form). Proved as `restAverageVanishes` for `3 ≤ N`. -/
def RestAverageVanishes : Prop :=
  avInv n (latticeData_gammaN N) (restFaceForm N n f hn) = 0

/-- **`ConstantTermVanishing` follows from (a) and (b).** -/
theorem constantTermVanishing_of_average (ha : AveragePreservesClass N n)
    (hb : RestAverageVanishes N n f hn) : ConstantTermVanishing N n f hn := by
  unfold ConstantTermVanishing
  rw [← ha (restFaceForm N n f hn), hb, map_zero]

end Reduction

end TernaryPeriodPolynomials.Argument.EisensteinClass
