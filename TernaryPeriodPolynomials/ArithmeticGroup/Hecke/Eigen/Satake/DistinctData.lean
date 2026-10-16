module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.CuspEisensteinSeparation
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.SummandScalar

@[expose] public section



/-!
# Inducing data with different `T_p` eigenvalues have independent summands

Let `D` and `D'` have the same character and different cohomological `T_p` eigenvalues at some
prime `p ≠ 3`. Then their boundary summands meet only in `0`, on either side, and so do their
associate pairs. The actual Hecke operator `T_p` acts on the two summands by the two different
scalars. This is the "distinct eigencharacters" half of the dichotomy between associate pairs.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {n p : ℕ}

/-- `T_p` acts on every boundary summand by `cuspPlaneEigenvalue`. -/
theorem summand_Tp_scalar (D : InducingData n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors D.cusp K3)] (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a = cuspPlaneEigenvalue D hp • a := by
  apply summand_scalar_of_source D side t hecke hhecke
  apply source_scalar_of_function t
  cases side
  · exact plane_Tp_eq_cusp D hp h3 t ht hg
  · exact line_Tp_eq_cusp D hp h3 t ht hg

/-- **Independence of summands with different `T_p` eigenvalues.** -/
theorem summand_inf_eq_bot (σ σ' : CuspidalRepresentation) (χ : RankOneCharacter)
    (coh : Cohomological σ n) (coh' : Cohomological σ' n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors σ K3)] [Nontrivial (fixedVectors σ' K3)]
    (hecke : BoundaryHecke n χ) (hhecke : ActualBoundaryHecke n χ hecke)
    (hne : cuspPlaneEigenvalue (⟨σ, χ, coh⟩ : InducingData n) hp ≠
      cuspPlaneEigenvalue (⟨σ', χ, coh'⟩ : InducingData n) hp) (side : Side) :
    boundarySummand (⟨σ, χ, coh⟩ : InducingData n) side ⊓
      boundarySummand (⟨σ', χ, coh'⟩ : InducingData n) side = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  have e1 := summand_Tp_scalar (⟨σ, χ, coh⟩ : InducingData n) hp h3 t ht hg hecke hhecke side x hx
  have e2 :=
    summand_Tp_scalar (⟨σ', χ, coh'⟩ : InducingData n) hp h3 t ht hg hecke hhecke side x hx'
  rw [e1] at e2
  have : (cuspPlaneEigenvalue (⟨σ, χ, coh⟩ : InducingData n) hp -
      cuspPlaneEigenvalue (⟨σ', χ, coh'⟩ : InducingData n) hp) • x = 0 := by
    rw [sub_smul, e2, sub_self]
  have hfree : Module.Free ℂ (StratumH2 n (⟨σ, χ, coh⟩ : InducingData n).chi side) :=
    Module.Free.of_divisionRing ℂ _
  have htorsion : Module.IsTorsionFree ℂ (StratumH2 n (⟨σ, χ, coh⟩ : InducingData n).chi side) :=
    Module.Free.instIsTorsionFree ℂ _
  rcases smul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · rw [Submodule.mem_bot]
    exact h

/-- **Independence of associate pairs with different `T_p` eigenvalues.** -/
theorem associatePair_inf_eq_bot (σ σ' : CuspidalRepresentation) (χ : RankOneCharacter)
    (coh : Cohomological σ n) (coh' : Cohomological σ' n) (hp : p.Prime) (h3 : p ≠ 3)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors σ K3)] [Nontrivial (fixedVectors σ' K3)]
    (hecke : BoundaryHecke n χ) (hhecke : ActualBoundaryHecke n χ hecke)
    (hne : cuspPlaneEigenvalue (⟨σ, χ, coh⟩ : InducingData n) hp ≠
      cuspPlaneEigenvalue (⟨σ', χ, coh'⟩ : InducingData n) hp) :
    associatePair (⟨σ, χ, coh⟩ : InducingData n) ⊓
      associatePair (⟨σ', χ, coh'⟩ : InducingData n) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ ⟨hx, hx'⟩
  have hx : (a, b) ∈ associatePair (⟨σ, χ, coh⟩ : InducingData n) := hx
  have hx' : (a, b) ∈ associatePair (⟨σ', χ, coh'⟩ : InducingData n) := hx'
  rw [associatePair, Submodule.mem_prod] at hx hx'
  have ha := summand_inf_eq_bot σ σ' χ coh coh' hp h3 t ht hg hecke hhecke hne .plane
  have hb := summand_inf_eq_bot σ σ' χ coh coh' hp h3 t ht hg hecke hhecke hne .line
  have ha0 : a = 0 := by
    have : a ∈ (⊥ : Submodule ℂ _) := ha ▸ ⟨hx.1, hx'.1⟩
    exact (Submodule.mem_bot ℂ).mp this
  have hb0 : b = 0 := by
    have : b ∈ (⊥ : Submodule ℂ _) := hb ▸ ⟨hx.2, hx'.2⟩
    exact (Submodule.mem_bot ℂ).mp this
  rw [ha0, hb0, Submodule.mem_bot]
  rfl

/-- **Different local cusp data give independent pairs.** If `ω(diag(p,1))` differs at some
`p ≠ 3`, the associate pairs of `σ ⊗ χ` and `σ' ⊗ χ` meet only in `0`. -/
theorem associatePair_inf_eq_bot_of_omega_ne (σ σ' : CuspidalRepresentation)
    (χ : RankOneCharacter) (coh : Cohomological σ n) (coh' : Cohomological σ' n)
    (hp : p.Prime) (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    [Nontrivial (fixedVectors σ K3)] [Nontrivial (fixedVectors σ' K3)]
    (hecke : BoundaryHecke n χ) (hhecke : ActualBoundaryHecke n χ hecke)
    (hω : omega σ (Bo (dP hp)) ≠ omega σ' (Bo (dP hp))) :
    associatePair (⟨σ, χ, coh⟩ : InducingData n) ⊓
      associatePair (⟨σ', χ, coh'⟩ : InducingData n) = ⊥ := by
  apply associatePair_inf_eq_bot σ σ' χ coh coh' hp h3 t ht hg hecke hhecke
  intro h
  exact hω (omega_eq_of_cuspPlaneEigenvalue_eq (⟨σ, χ, coh⟩ : InducingData n)
    (⟨σ', χ, coh'⟩ : InducingData n) rfl hp rfl h)

end TernaryPeriodPolynomials.HeckeEigen.Satake
