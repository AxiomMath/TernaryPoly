module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Invariance

@[expose] public section


/-!
# Reindexing the sum over triangle representatives along a finite-index subgroup

Formalized by Claude Sonnet 5.5.

Let `Δ = Γ(M) ≤ Γ = Γ(N)` act freely on the triangles of the Farey tree with representative systems `R_Δ`, `R_Γ`, and let `Q` be a `Γ`-set with base point `q₀`
whose stabilizer is `Δ`, with `u x • q₀ = x`.  For a `Δ`-invariant function `F` on triangles,
`∑_{y ∈ R_Γ} ∑_{x : Q} F(u_x⁻¹ y) = ∑_{r ∈ R_Δ} F(r)`: the map `(y, x) ↦ rep_Δ(u_x⁻¹ y)` is a bijection `R_Γ × Q → R_Δ` modulo `Δ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {N M : ℕ}

theorem sum_reindex (hN : 3 ≤ N) (hM : 3 ≤ M) (hle : gammaNGL M ≤ gammaNGL N)
    {Q : Type} [Fintype Q] [MulAction (gammaNGL N) Q] (q0 : Q) (u : Q → gammaNGL N) (hu : ∀ x, u x • q0 = x)
    (hstab : ∀ g : gammaNGL N, g • q0 = q0 ↔ (g : IntegralGL) ∈ gammaNGL M)
    (F : Tri → ℂ) (hF : ∀ (δ : gammaNGL M) (y : Tri), F (δ • y) = F y) :
    ∑ y ∈ (gammaNFareyData hN).RT.R, ∑ x : Q, F ((u x)⁻¹ • y) = ∑ r ∈ (gammaNFareyData hM).RT.R, F r := by
  set DN := gammaNFareyData hN with hDN
  set DM := gammaNFareyData hM with hDM
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun a _ => ((dec DM.RT ((u a.2)⁻¹ • a.1)).1 : Tri)) ?_ ?_ ?_ ?_
  · intro a _
    exact (dec DM.RT _).1.2
  · rintro ⟨y1, x1⟩ h1 ⟨y2, x2⟩ h2 h
    have hy1 : y1 ∈ DN.RT.R := (Finset.mem_product.mp h1).1
    have hy2 : y2 ∈ DN.RT.R := (Finset.mem_product.mp h2).1
    simp only at h
    have s1 := dec_spec DM.RT ((u x1)⁻¹ • y1)
    have s2 := dec_spec DM.RT ((u x2)⁻¹ • y2)
    set d1 : gammaNGL N := Subgroup.inclusion hle (dec DM.RT ((u x1)⁻¹ • y1)).2 with hd1
    set d2 : gammaNGL N := Subgroup.inclusion hle (dec DM.RT ((u x2)⁻¹ • y2)).2 with hd2
    set r := ((dec DM.RT ((u x1)⁻¹ • y1)).1 : Tri) with hr
    have s1' : d1 • r = (u x1)⁻¹ • y1 := s1
    have s2' : d2 • r = (u x2)⁻¹ • y2 := by
      have : ((dec DM.RT ((u x2)⁻¹ • y2)).1 : Tri) = r := h.symm
      rw [← this]; exact s2
    have e1 : y1 = (u x1 * d1) • r := by rw [mul_smul, s1', smul_inv_smul]
    have e2 : y2 = (u x2 * d2) • r := by rw [mul_smul, s2', smul_inv_smul]
    have hrel : (u x2 * d2 * (u x1 * d1)⁻¹) • y1 = y2 := by
      rw [e1, ← mul_smul, inv_mul_cancel_right, ← e2]
    have hy : y1 = y2 := DN.RT.inj y1 hy1 y2 hy2 _ hrel
    subst hy
    have h1 : u x2 * d2 * (u x1 * d1)⁻¹ = 1 := DN.freeT _ _ hrel
    have h3 : u x1 * d1 = u x2 * d2 := (mul_inv_eq_one.mp h1).symm
    have hd1' : d1 • q0 = q0 := (hstab d1).mpr (dec DM.RT ((u x1)⁻¹ • y1)).2.2
    have hd2' : d2 • q0 = q0 := (hstab d2).mpr (dec DM.RT ((u x2)⁻¹ • y1)).2.2
    have hx : x1 = x2 := by
      rw [← hu x1, ← hu x2]
      have : (u x1 * d1) • q0 = (u x2 * d2) • q0 := by rw [h3]
      rwa [mul_smul, mul_smul, hd1', hd2'] at this
    rw [hx]
  · intro r hr
    obtain ⟨y, hy, γ, hγ⟩ := DN.RT.cover r
    refine ⟨(y, γ⁻¹ • q0), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, ?_⟩
    simp only
    set x := γ⁻¹ • q0 with hx
    have hux : (γ * u x) • q0 = q0 := by
      rw [mul_smul, hu x, hx, smul_inv_smul]
    have hmem : ((γ * u x : gammaNGL N) : IntegralGL) ∈ gammaNGL M := (hstab _).mp hux
    set δ0 : gammaNGL M := ⟨_, hmem⟩ with hδ0
    have hy' : y = γ⁻¹ • r := by rw [← hγ, inv_smul_smul]
    have hrel : (u x)⁻¹ • y = δ0⁻¹ • r := by
      rw [hy', ← mul_smul, ← mul_inv_rev]
      rfl
    have hdec := dec_eq DM.RT DM.freeT (x := (u x)⁻¹ • y) (p := (⟨r, hr⟩, δ0⁻¹)) hrel.symm
    rw [hdec]
  · intro a ha
    have s := dec_spec DM.RT ((u a.2)⁻¹ • a.1)
    calc F ((u a.2)⁻¹ • a.1) = F ((dec DM.RT ((u a.2)⁻¹ • a.1)).2 • ((dec DM.RT ((u a.2)⁻¹ • a.1)).1 : Tri)) := by
          rw [s]
      _ = F ((dec DM.RT ((u a.2)⁻¹ • a.1)).1 : Tri) := hF _ _

end TernaryPeriodPolynomials.Argument.CuspidalInduction
