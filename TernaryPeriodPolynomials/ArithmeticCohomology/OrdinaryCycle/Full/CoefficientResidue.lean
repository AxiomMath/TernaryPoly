module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientNaturality
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Equivariance

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open OrdinaryApartmentPresentation SinglePole

/-- The genuine full-level ordinary functionals valued in actual single-pole rational functions. -/
abbrev SinglePoleHom (n : ℕ) (e : ℤ) := Hom (singlePoleAction n e)
/-- The genuine full-level ordinary functionals valued in the actual finite residue direct sum. -/
abbrev ResidueHom (n : ℕ) (e : ℤ) := Hom (residueAction n e)

/-- The actual residue map induces the full-level map on ordinary cycle functionals. -/
def residueHom (n : ℕ) (e : ℤ) : SinglePoleHom n e →ₗ[ℚ] ResidueHom n e :=
  homMap (singlePoleAction n e) (residueAction n e) (residue n)
    (fun g x => (residue_equivariant n e g x).symm)

@[simp] theorem residueHom_apply (n : ℕ) (e : ℤ) (f : SinglePoleHom n e)
    (c : OrdinaryIncidenceChains.Cycles) :
    (residueHom n e f).val c = residue n (f.val c) := rfl

theorem residue_relations (n : ℕ) (e : ℤ) (v : singlePole n)
    (hv : Relations (singlePoleAction n e) v) : Relations (residueAction n e) (residue n v) :=
  relations_map (singlePoleAction n e) (residueAction n e) (residue n)
    (fun g x => (residue_equivariant n e g x).symm) v hv

/-- The actual single-pole and residue functionals are natural through the literal residue map. -/
theorem residue_functional (n : ℕ) (e : ℤ) (v : singlePole n)
    (hv : Relations (singlePoleAction n e) v) :
    functional (residueAction n e) (residue n v) (residue_relations n e v hv) =
      (residue n).comp (functional (singlePoleAction n e) v hv) :=
  functional_natural (singlePoleAction n e) (residueAction n e) (residue n)
    (fun g x => (residue_equivariant n e g x).symm) v hv

theorem residue_reference (n : ℕ) (e : ℤ) (f : SinglePoleHom n e) :
    (coefficientEquiv (residueAction n e) (residueHom n e f)).val =
      residue n (coefficientEquiv (singlePoleAction n e) f).val := rfl

/-- Liftable actual residues are the image of the actual map on full-level ordinary Hom spaces. -/
def liftableResidueHoms (n : ℕ) (e : ℤ) : Submodule ℚ (ResidueHom n e) :=
  (residueHom n e).range

/-- Reference-level liftability is equivalent to a lift satisfying the genuine apartment equations. -/
theorem reference_liftable_iff (n : ℕ) (e : ℤ) (f : ResidueHom n e) :
    f ∈ liftableResidueHoms n e ↔
      ∃ v : singlePole n, Relations (singlePoleAction n e) v ∧
        residue n v = f.val (frameCycle 1) := by
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨h.val (frameCycle 1),hom_relations _ h,rfl⟩
  · rintro ⟨v,hv,he⟩
    refine ⟨⟨functional (singlePoleAction n e) v hv,functional_equivariant _ _ hv⟩,?_⟩
    apply reference_injective (residueAction n e)
    change residue n (functional (singlePoleAction n e) v hv (frameCycle 1)) = _
    rw [functional_reference,he]

end TernaryPoly.OrdinaryFullCoefficient
