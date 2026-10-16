module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Generic

@[expose] public section


/-!
# `H²` of a Levi subgroup vanishes in the inhomogeneous model

The library proves (`ModularH2.H2_zero_of_injective_binary`) that complex degree-two cohomology
(Mathlib's `groupCohomology.H2`) of every group embedding into `GL₂(ℤ) × ℤˣ` vanishes. The
Hochschild-Serre arguments of `Face/Generic` use the library's inhomogeneous model
`InhomogeneousH2`; the two models have literally the same cocycle and coboundary formulas, which
gives `inhomogeneousH2_zero_of_binary`. Consequently `EdgeData` holds for every edge subgroup
`B ≤ Levi` as soon as `Levi` embeds into `GL₂(ℤ) × ℤˣ` (`edgeVanishing_of_binary`): all four
cusp types have such a Levi, and no parity restriction on `n` is needed.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- Complex `H²` of every group embedding in `GL₂(ℤ) × ℤˣ` vanishes in the inhomogeneous model. -/
theorem inhomogeneousH2_zero_of_binary {Γ : Type} [Group Γ]
    (ψ : Γ →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (representation : Representation ℂ Γ V)
    (x : InhomogeneousH2 representation) : x = 0 := by
  obtain ⟨cycle, rfl⟩ := (inhomogeneousBoundaries representation).mkQ_surjective x
  let A : Rep ℂ Γ := Rep.of representation
  have closed : (fun pair : Γ × Γ => (cycle.val pair.1 pair.2 : A)) ∈
      groupCohomology.cocycles₂ A := by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    have hc := cycle.property g h j
    change cycle.val (g * h) j + cycle.val g h =
      representation g (cycle.val h j) + cycle.val g (h * j)
    apply sub_eq_zero.mp
    rw [← neg_eq_zero]
    convert hc using 1
    abel
  have zero := TernaryPeriodPolynomials.Spectral.ModularH2.H2_zero_of_injective_binary
    ψ injective A (groupCohomology.H2π A ⟨_, closed⟩)
  rw [groupCohomology.H2π_eq_zero_iff] at zero
  obtain ⟨primitive, hprimitive⟩ := zero
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  funext a b
  exact congrFun hprimitive (a, b)

/-- The vanishing required by `EdgeData`, for every Levi subgroup when the Levi embeds in
`GL₂(ℤ) × ℤˣ`. -/
theorem edgeVanishing_of_binary {Radical Levi V : Type} [Group Radical] [Group Levi]
    [AddCommGroup V] [Module ℂ V] (action : Levi →* MulAut Radical)
    (representation : Representation ℂ (SemidirectProduct Radical Levi action) V)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    (B : Subgroup Levi)
    (x : InhomogeneousH2 (semidirectInvariantRepresentation (subAction action B)
      (subRepresentation action representation B))) : x = 0 :=
  inhomogeneousH2_zero_of_binary (ψ.comp B.subtype)
    (injective.comp B.subtype_injective) _ x

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
