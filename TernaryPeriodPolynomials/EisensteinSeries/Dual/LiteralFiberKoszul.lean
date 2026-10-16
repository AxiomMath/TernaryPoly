module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLiteralBridge

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.LiteralBridge

/-!
# The torus-fibre (Koszul) pairing of a radical lattice for the literal dual `E*`

Formalized by Claude Sonnet 5.5.

(the two-generator Koszul complex of the radical, "Poincare duality on its compact torus fiber with dual local systems")
and.  `FacePD.latticeKoszul` pairs `H¹(Ω, E)` with `H¹(Ω, E^φ)` through the apolar `dualPairing`.
Here the same Koszul data is built for the LITERAL contragredient `E* = (rationalCoefficientComponent n χ).dual` with the evaluation pairing `evPairing`
(`LiteralBridge`): `latticeKoszulLit` (the invariance `⟨ρ(u) a, ρ^∨(u) b⟩ = ⟨a, b⟩` holds for the contragredient of any representation),
`latticeKoszulLit_perfect` (perfect in both arguments), and `latticeKoszulLit_eq_kostant`, the library's fibre-integration pairing
`kostant (evPairing n) Ω.σ f g` of a cocycle of `E` and a `U`-equivariant cocycle of `E*` is the Koszul pairing of their generator values.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

/-- The evaluation pairing `E ⊗ E* → ℂ` is invariant under the diagonal action. -/
theorem evPairing_invariant (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3) (a : HomogeneousPoly n)
    (b : Module.Dual ℂ (HomogeneousPoly n)) :
    evPairing n ((rationalCoefficientComponent n χ) g a) ((rationalCoefficientComponent n χ).dual g b) = evPairing n a b := by
  change (b.comp ((rationalCoefficientComponent n χ) g⁻¹)) ((rationalCoefficientComponent n χ) g a) = b a
  rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem evPairing_left (n : ℕ) (a : HomogeneousPoly n) (h : ∀ b : Module.Dual ℂ (HomogeneousPoly n), evPairing n a b = 0) :
    a = 0 :=
  (Module.forall_dual_apply_eq_zero_iff ℂ a).1 h

theorem evPairing_right (n : ℕ) (b : Module.Dual ℂ (HomogeneousPoly n)) (h : ∀ a : HomogeneousPoly n, evPairing n a b = 0) :
    b = 0 :=
  LinearMap.ext h

/-- **The Koszul data of an embedded radical lattice for the literal contragredient**: `E` and `E*`, paired by evaluation. -/
def latticeKoszulLit (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3) :
    Koszul.KData (HomogeneousPoly n) (Module.Dual ℂ (HomogeneousPoly n)) :=
  koszulOfRep (rationalCoefficientComponent n χ) (rationalCoefficientComponent n χ).dual
    (Ω.u 1 0) (Ω.u 0 1) Ω.commute.eq (evPairing n)
    (fun a b => evPairing_invariant n χ _ a b) (fun a b => evPairing_invariant n χ _ a b)
    (evPairing_left n) (evPairing_right n)

/-- **Perfectness of the torus-fibre pairing for `E ⊗ E*`**, in both arguments. -/
theorem latticeKoszulLit_perfect (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3) :
    letI := homogeneousPoly_finite n
    (∀ a : (latticeKoszulLit n χ Ω).H1, (∀ b : (latticeKoszulLit n χ Ω).H1',
        (latticeKoszulLit n χ Ω).pairing a b = 0) → a = 0) ∧
    ∀ b : (latticeKoszulLit n χ Ω).H1', (∀ a : (latticeKoszulLit n χ Ω).H1,
        (latticeKoszulLit n χ Ω).pairing a b = 0) → b = 0 :=
  letI := homogeneousPoly_finite n
  ⟨fun a h => (latticeKoszulLit n χ Ω).pairing_left_nondegenerate a h,
    fun b h => (latticeKoszulLit n χ Ω).pairing_right_nondegenerate b h⟩

/-- **The library's fibre-integration pairing for `E ⊗ E*` is the Koszul pairing** of the generator values. -/
theorem latticeKoszulLit_eq_kostant (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3)
    {f : (Fin 2 → RationalGL3) → HomogeneousPoly n} {g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)}
    (hg : UCocycle (litRep n χ) Ω.sub g) :
    (latticeKoszulLit n χ Ω).Phi (f ![1, Ω.u 1 0], f ![1, Ω.u 0 1]) (g ![1, Ω.u 1 0], g ![1, Ω.u 0 1]) =
      kostant (evPairing n) Ω.σ f g :=
  (kostant_eq_koszul (rationalCoefficientComponent n χ) (rationalCoefficientComponent n χ).dual Ω.sub (Ω.u_mem 1 0)
    (Ω.u_mem 0 1) Ω.commute.eq (evPairing n) (fun a b => evPairing_invariant n χ _ a b)
    (fun a b => evPairing_invariant n χ _ a b) (evPairing_left n) (evPairing_right n) f g hg.1).symm

end TernaryPeriodPolynomials.Argument.EisensteinDual
