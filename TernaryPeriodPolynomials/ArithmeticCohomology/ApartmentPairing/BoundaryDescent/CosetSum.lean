module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.TowerRes

@[expose] public section


/-!
# The literal sum over the right cosets `S\Γ` and the averaging projector (abstract)

Formalized by Claude Sonnet 5.5.  Residual (a) of the Lemma 3.3 row (the chain-level right-coset-sum transfer).

For a subgroup `S ≤ Γ` of finite index, `RCos S = Quotient (QuotientGroup.rightRel S)` is the set of right cosets `S\Γ`.
`sum_rcos_eq`: for `f` with `f (s g) = f g` the sum over `S\Γ` of `f (r.out)` is the sum over the left cosets of `f ((q.out)⁻¹)`.
`apply_avgR_sum`: for `N ⊴ Γ` acting trivially, `N ≤ S`, and a linear map `Φ` with `Φ ∘ ρ s = Φ` for `s ∈ S`,
`Φ (avg_{Γ/N} b) = [Γ:S]⁻¹ ∑_{r ∈ S\Γ} Φ (ρ (r.out) b)`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

open Representation TernaryPeriodPolynomials.Argument.Lemma33.Naturality
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Right

variable {Γ : Type*} [Group Γ] (S : Subgroup Γ) [S.FiniteIndex]

/-- The right cosets `S\Γ`. -/
abbrev RCos : Type _ := Quotient (QuotientGroup.rightRel S)

theorem sum_rcos_eq {W : Type*} [AddCommMonoid W] (f : Γ → W) (hf : ∀ s ∈ S, ∀ g, f (s * g) = f g) :
    ∑ r : RCos S, f r.out = ∑ q : Γ ⧸ S, f (q.out)⁻¹ := by
  refine Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel S) _ _ (fun r => ?_)
  set q := QuotientGroup.quotientRightRelEquivQuotientLeftRel S r with hqdef
  have hq : q = QuotientGroup.mk (r.out)⁻¹ := by
    rw [hqdef]
    conv_lhs => rw [← Quotient.out_eq' r]
    rfl
  have h1 : (QuotientGroup.mk (q.out) : Γ ⧸ S) = QuotientGroup.mk (r.out)⁻¹ := (QuotientGroup.out_eq' q).trans hq
  have h2 : (q.out)⁻¹ * (r.out)⁻¹ ∈ S := QuotientGroup.eq.mp h1
  have h3 : r.out * q.out ∈ S := by
    have := S.inv_mem h2
    simpa [mul_inv_rev] using this
  have h4 : r.out = (r.out * q.out) * (q.out)⁻¹ := by group
  conv_lhs => rw [h4]
  exact hf _ h3 _

theorem sum_rcos_mul {W : Type*} [AddCommMonoid W] (f : Γ → W) (hf : ∀ s ∈ S, ∀ g, f (s * g) = f g) (g : Γ) :
    ∑ r : RCos S, f (r.out * g) = ∑ r : RCos S, f r.out := by
  rw [sum_rcos_eq S (fun x => f (x * g)) (fun s hs x => by rw [mul_assoc]; exact hf s hs _), sum_rcos_eq S f hf]
  rw [← Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun q : Γ ⧸ S => f (q.out)⁻¹)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : (QuotientGroup.mk ((g⁻¹ • q).out) : Γ ⧸ S) = QuotientGroup.mk (g⁻¹ * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h2 : ((g⁻¹ • q).out)⁻¹ * (g⁻¹ * q.out) ∈ S := QuotientGroup.eq.mp h1
  have h3 : (q.out)⁻¹ * g = (((g⁻¹ • q).out)⁻¹ * (g⁻¹ * q.out))⁻¹ * ((g⁻¹ • q).out)⁻¹ := by group
  have h4 : f ((q.out)⁻¹ * g) = f ((g⁻¹ • q).out)⁻¹ := by
    rw [h3]; exact hf _ (S.inv_mem h2) _
  exact h4

end Right

section Avg

variable {Γ : Type*} [Group Γ] (N S : Subgroup Γ) [N.Normal] [N.FiniteIndex] [S.FiniteIndex]
  {B C : Type*} [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C] (ρ : Representation ℚ Γ B)

/-- **`Φ ∘ avg_{Γ/N}` is the average over the right cosets `S\Γ`** (when `Φ` is `S`-invariant and `N ≤ S` acts trivially). -/
theorem apply_avgR_sum (hNS : N ≤ S) (hN : ∀ n ∈ N, ρ n = 1) (Φ : B →ₗ[ℚ] C) (hΦ : ∀ s ∈ S, ∀ b, Φ (ρ s b) = Φ b) (b : B) :
    Φ (avgR N ρ b) = ((Fintype.card (Γ ⧸ S) : ℚ)⁻¹) • ∑ r : RCos S, Φ (ρ r.out b) := by
  have hσN : ∀ n ∈ N, linHom ρ (trivial ℚ Γ C) n = 1 := fun n hn => by
    ext f x
    simp [hN n⁻¹ (N.inv_mem hn)]
  have hσS : ∀ m ∈ S, linHom ρ (trivial ℚ Γ C) m Φ = Φ := fun m hm => by
    ext x
    simp [hΦ m⁻¹ (S.inv_mem hm)]
  have tower := avgR_tower_sum N S (linHom ρ (trivial ℚ Γ C)) hNS hσN Φ hσS
  have h1 : (avgR N (linHom ρ (trivial ℚ Γ C)) Φ) b =
      ((Fintype.card (Γ ⧸ N) : ℚ)⁻¹) • ∑ x : Γ ⧸ N, Φ (ρ (x.out)⁻¹ b) := by
    simp [avgR, LinearMap.sum_apply]
  have h2 : Φ (avgR N ρ b) = ((Fintype.card (Γ ⧸ N) : ℚ)⁻¹) • ∑ x : Γ ⧸ N, Φ (ρ x.out b) := by
    simp [avgR, LinearMap.sum_apply]
  have h3 : ∑ x : Γ ⧸ N, Φ (ρ (x.out)⁻¹ b) = ∑ x : Γ ⧸ N, Φ (ρ x.out b) := by
    rw [← Equiv.sum_comp (Equiv.inv (Γ ⧸ N)) (fun x => Φ (ρ x.out b))]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ρ (x.out)⁻¹ = ρ ((x⁻¹ : Γ ⧸ N).out) := by
      refine rho_eq_of_mk_eq hN ?_
      rw [QuotientGroup.out_eq', QuotientGroup.mk_inv, QuotientGroup.out_eq']
    simp only [Equiv.inv_apply, this]
  have h4 : ∑ q : Γ ⧸ S, Φ (ρ (q.out)⁻¹ b) = ∑ r : RCos S, Φ (ρ r.out b) := by
    refine (sum_rcos_eq S (fun g => Φ (ρ g b)) (fun s hs g => ?_)).symm
    simp only [map_mul, Module.End.mul_apply]
    exact hΦ s hs _
  have h5 := congrArg (fun F => F b) tower
  simp only [LinearMap.smul_apply, LinearMap.sum_apply] at h5
  rw [h1] at h5
  rw [h2, ← h3, h5]
  simp [h4.symm]

end Avg

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
