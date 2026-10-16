/-
  Formal obstruction evidence for `cuspidal_associate_projector`.

  The file isolates the two inputs that the target conclusion

  requires and that the definitions do not provide:

  1. `hecke_eq_canonical`: the hypothesis `ActualBoundaryHecke n trivialCharacter hecke`
     determines `hecke` uniquely as the canonical finite-coset action
     `Helpers.cohomologyAction` (via `realizesHecke_unique`).  So the target is a statement about this single

     concrete Hecke action, not about an arbitrary family.

  2. `projector_forces_invariance`: *any* solution `p` of `IsIsotypicalProjection`
     forces `associatePair` to be invariant under every `pairHecke` correspondence.
     Hence the existence clause of the target entails the Hecke-stability of the
     associate pair.  That stability is the Harder--Raghuram associate-pair
     spectral splitting (arXiv:1405.6513, Thm. 5.37/6.9).

  3. `abstract_shape_not_unique` (from the original library, reproduced
     here for self-containedness) shows that the three clauses of
     `IsIsotypicalProjection` alone do not force uniqueness: the logical shape is
     satisfied by two distinct projections in a two-dimensional model.  Hence the
     uniqueness clause also needs the missing multiplicity-one input.

  Together these say the statement is not derivable from its own
  hypotheses without the Harder--Raghuram/multiplicity-one input.  They are not a
  proof of the target and not a disproof of it; they locate the exact gap.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Helpers
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Insufficiency
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.Obstruction

variable {n : ℕ}

/-- The actual boundary Hecke action is uniquely determined by its finite-coset
formula: every `ActualBoundaryHecke` equals the canonical `cohomologyAction`
constructed in `TernaryPeriodPolynomials.HeckeTranslate.Helpers`. -/
theorem hecke_eq_canonical (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (side : Side) :
    hecke side = Helpers.cohomologyAction
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side) :=
  realizesHecke_unique _ _ _ (hhecke side)
    (Helpers.cohomologyAction_realizes _)

/-- A projection with the required range and identity on that range forces the
associate pair to be invariant under every Hecke correspondence. -/
theorem projector_forces_invariance {D : InducingData n}
    {T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)}
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hp : IsIsotypicalProjection D T p) (t : HeckeCorrespondence) :
    ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D := by
  intro x hx
  have h := congrArg (fun f : BoundaryCoordinates n D.chi →ₗ[ℂ] BoundaryCoordinates n D.chi =>
      f x) (hp.2.2 t)
  simp only [LinearMap.comp_apply] at h
  have hfix : (pairHecke D T t) x = p ((pairHecke D T t) x) := by
    rw [h, hp.2.1 x hx]
  rw [hfix]
  exact hp.1 ▸ LinearMap.mem_range_self p _


/-- The exact level shift produced by the Hecke transport: right multiplication of
the adelic variable by `atFinite k.val` moves past `rationalGroup r` at the cost
of conjugating `k` by the finite part `rationalFinite r`. -/
theorem hecke_transport_level_shift (r : RationalGL3) (k : finiteLevel) (g : AdelicGL) :
    g * atFinite k.val * rationalGroup r =
      g * rationalGroup r *
        atFinite ((rationalFinite r)⁻¹ * k.val * rationalFinite r) := by
  rw [mul_assoc, HeckeInvariance.atFinite_mul_rationalGroup, ← mul_assoc]

/-- Consequently the transported source cochain is `finiteLevel`-invariant exactly
when every conjugate `rationalFinite r⁻¹ * k * rationalFinite r` stays in
`finiteLevel`.  The natural Hecke transport therefore lands in `IsSourceCocycle`
only for correspondences whose finite parts normalize the fixed congruence level;
this is the precise formal point at which the direct transport route stops. -/
theorem hecke_transport_level_condition (r : RationalGL3) (k : finiteLevel)
    (h : (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (g : AdelicGL) :
    g * atFinite k.val * rationalGroup r =
      g * rationalGroup r * atFinite ((⟨(rationalFinite r)⁻¹ * k.val * rationalFinite r, h⟩ :
        finiteLevel).val) := by
  rw [hecke_transport_level_shift]

end TernaryPeriodPolynomials.HeckeTranslate.Obstruction

end
