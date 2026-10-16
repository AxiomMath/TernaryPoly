module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneTransfer

@[expose] public section


/-!
# Away-from-three Hecke operators act by scalars on the plane boundary summand

If the finite-coset translate of every source cocycle is a fixed multiple `μ` of it, then every
actual Hecke operator acts on `boundarySummand D side` as `μ`. For the plane side this applies
with `μ` from `plane_hecke_scalar`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.HeckeTranslate

namespace TernaryPeriodPolynomials.HeckeEigen

variable {n : ℕ}

/-- **Summand scalar from a source scalar.** -/
theorem summand_scalar_of_source (D : InducingData n) (side : Side) (t : HeckeCorrespondence)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (μ : ℂ)
    (hμ : ∀ c, IsSourceCocycle D side c → ∀ x g,
      HeckeInvariance.translateSource D t c x g = μ • c x g) :
    ∀ a ∈ boundarySummand D side, hecke side t a = μ • a := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c, hc, z, heval, rfl⟩ := hb
    obtain ⟨z', hz', hclass⟩ := hhecke side t z
    rw [hclass, ← map_smul]
    congr 1
    have he := HeckeInvariance.evaluates_translate D side t heval hz'
    apply Subtype.ext; apply Subtype.ext
    funext x flag
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective flag
    change z'.val.val x (QuotientGroup.mk q) = μ • z.val.val x (QuotientGroup.mk q)
    rw [he x q, heval x q, hμ c hc]
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

/-- The finite-coset translate of a source cocycle is the right Hecke sum. -/
theorem translateSource_eq_sum {D : InducingData n} {side : Side} (t : HeckeCorrespondence)
    {c : SourceCochain n} (hc : IsSourceCocycle D side c) (x : Fin 3 → RealGL3) (g : AdelicGL) :
    HeckeInvariance.translateSource D t c x g =
      ∑ r ∈ t.representatives, c x (g * atFinite (rationalFinite r)) := by
  have := TranslateRationalLevel.translateSource_sum_eq t hc x g 1
  rw [TranslateRationalLevel.atFinite_one, mul_one] at this
  simpa only [one_mul] using this

/-- **Source scalar from a function scalar.** -/
theorem source_scalar_of_function {D : InducingData n} {side : Side} (t : HeckeCorrespondence)
    (μ : ℂ) (hμ : ∀ f : AdelicGL → ℂ, IsInduced D side cohomologicalPoint f → ∀ g : AdelicGL,
      ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) = μ * f g) :
    ∀ c, IsSourceCocycle D side c → ∀ x g,
      HeckeInvariance.translateSource D t c x g = μ • c x g := by
  intro c hc x g
  rw [translateSource_eq_sum t hc]
  apply AveragedHecke.poly_ext
  intro m
  rw [Submodule.coe_sum, MvPolynomial.coeff_sum, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul]
  exact hμ (fun g => (c x g).val.coeff m) (hc.1 x m) g

/-- **Away-from-three Hecke operators act by one scalar on the whole plane summand.** -/
theorem plane_summand_scalar (D : InducingData n) (t : HeckeCorrespondence) (ht : AwayThree t) :
    ∃ μ : ℂ, ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
      ∀ a ∈ boundarySummand D .plane, hecke .plane t a = μ • a := by
  obtain ⟨μ, hμ⟩ := plane_hecke_scalar D t ht
  exact ⟨μ, fun hecke hhecke =>
    summand_scalar_of_source D .plane t hecke hhecke μ (source_scalar_of_function t μ hμ)⟩

end TernaryPeriodPolynomials.HeckeEigen
