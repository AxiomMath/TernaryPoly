module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisCE
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisBracket

@[expose] public section


/-!
# `D² = 0` for the Chevalley-Eilenberg differential, and the unconditional Nomizu-Kasuya theorem for the Heisenberg group

Formalized by Claude Sonnet 5.5.

`D = Σ_k ε_k X_k + 𝔇` is the flat differential `d + ρ(θ) ∧` of the cochains `Λ•𝔥* ⊗ E` in the left-invariant coframe (`HeisCE`).  Its square vanishes (`Dop_Dop`): the second order terms
`Σ ε_k ε_l X_k X_l` give `ε₀ ε₁ X₂` by the bracket `[X₀, X₁] = X₂` (`HeisBracket`), the mixed terms `(ε_l 𝔇 + 𝔇 ε_l) X_l` give `-ε₀ ε₁ X₂` (`eps_D0`), and `𝔇² = 0` (`D0_sq`);
the algebraic bookkeeping is `Dsq_alg`.

`heis_nomizu_ce` is `heis_nomizu` (`HeisLattice`) with the Cartan data `ceData ρ h` of a unipotent `Heisenberg` module `E` and the hypothesis `D² = 0` discharged: every `D`-closed
smooth cochain `u`, periodic for the lattice `ax ℤ × ay ℤ × az ℤ`, is cohomologous in the periodic complex to the constant `heisAv u` (its Haar average) with `𝔇 (heisAv u) = 0`.
-/

open scoped ContDiff
noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

section Alg

variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The pointwise algebra of `D² = 0`. -/
theorem Dsq_alg (e : Fin 3 → M →L[ℝ] M) (d0 : M →L[ℝ] M) (a : Fin 3 → Fin 3 → M) (b : Fin 3 → M) (c : M)
    (hanti : ∀ k l x, e k (e l x) + e l (e k x) = 0) (hsq : ∀ k x, e k (e k x) = 0)
    (hB : ∀ l x, e l (d0 x) + d0 (e l x) = -(if l = 2 then e 0 (e 1 x) else 0))
    (hC : ∀ x, d0 (d0 x) = 0)
    (h01 : a 0 1 - a 1 0 = b 2) (h02 : a 0 2 = a 2 0) (h12 : a 1 2 = a 2 1) :
    (∑ l, e l (∑ k, e k (a l k) + d0 (b l))) + d0 (∑ k, e k (b k) + d0 c) = 0 := by
  have h10 : ∀ x, e 1 (e 0 x) = -e 0 (e 1 x) := fun x => eq_neg_of_add_eq_zero_left (hanti 1 0 x)
  have h20 : ∀ x, e 2 (e 0 x) = -e 0 (e 2 x) := fun x => eq_neg_of_add_eq_zero_left (hanti 2 0 x)
  have h21 : ∀ x, e 2 (e 1 x) = -e 1 (e 2 x) := fun x => eq_neg_of_add_eq_zero_left (hanti 2 1 x)
  have B0 := hB 0 (b 0)
  have B1 := hB 1 (b 1)
  have B2 := hB 2 (b 2)
  simp only [Fin.sum_univ_three, map_add, h10, h20, h21, hsq, hC]
  simp only [ite_true, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false, neg_zero] at B0 B1 B2
  have ha10 : a 1 0 = a 0 1 - b 2 := by rw [← h01]; abel
  rw [ha10, ← h02, ← h12]
  simp only [map_sub, neg_sub]
  have := B0
  have := B1
  have := B2
  linear_combination (norm := abel) B0 + B1 + B2

end Alg


section Concrete

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : Fin 3 → E →L[ℝ] E) (hρ : HeisMod ρ)

theorem Dop_apply (u : Pt → CE E) (p : Pt) :
    Dop (ceData ρ hρ) u p = ∑ k, epsC k (Xop k u p) + ceD0 ρ (u p) := by
  simp [Dop, lin, ceData, Finset.sum_apply]

theorem Dop_three (u : Pt → CE E) :
    Dop (ceData ρ hρ) u = lin (epsC 0) (Xop 0 u) + lin (epsC 1) (Xop 1 u) + lin (epsC 2) (Xop 2 u) +
      lin (ceD0 ρ) u := by
  funext p
  simp [Dop, lin, ceData, Fin.sum_univ_three]

theorem Xop_Dop {u : Pt → CE E} (hu : ContDiff ℝ ∞ u) (l : Fin 3) (p : Pt) :
    Xop l (Dop (ceData ρ hρ) u) p = ∑ k, epsC k (Xop l (Xop k u) p) + ceD0 ρ (Xop l u p) := by
  have hX : ∀ k, ContDiff ℝ ∞ (Xop k u) := fun k => Xop_contDiff hu k
  have hL : ∀ (L : CE E →L[ℝ] CE E) k, ContDiff ℝ ∞ (lin L (Xop k u)) := fun L k => lin_contDiff L (hX k)
  have h1 : ContDiff ℝ ∞ (lin (epsC 0) (Xop 0 u) + lin (epsC 1) (Xop 1 u)) := (hL _ 0).add (hL _ 1)
  have h2 : ContDiff ℝ ∞ (lin (epsC 0) (Xop 0 u) + lin (epsC 1) (Xop 1 u) + lin (epsC 2) (Xop 2 u)) :=
    h1.add (hL _ 2)
  rw [Dop_three, Xop_add h2 (lin_contDiff _ hu), Xop_add h1 (hL _ 2), Xop_add (hL _ 0) (hL _ 1),
    Xop_lin _ (hX 0), Xop_lin _ (hX 1), Xop_lin _ (hX 2), Xop_lin _ hu]
  simp [lin, Fin.sum_univ_three]

/-- **`D² = 0`** for the Chevalley-Eilenberg differential `D = Σ ε_k X_k + 𝔇` with unipotent coefficients. -/
theorem Dop_Dop {u : Pt → CE E} (hu : ContDiff ℝ ∞ u) : Dop (ceData ρ hρ) (Dop (ceData ρ hρ) u) = 0 := by
  funext p
  rw [Dop_apply, Dop_apply]
  simp only [Xop_Dop ρ hρ hu]
  have := Dsq_alg (fun k => epsC (E := E) k) (ceD0 ρ) (fun l k => Xop l (Xop k u) p) (fun l => Xop l u p) (u p)
    (fun k l x => by
      have := congrArg (fun A : CE E →L[ℝ] CE E => A x) (epsC_anti (E := E) k l)
      simpa using this)
    (fun k x => by
      have := congrArg (fun A : CE E →L[ℝ] CE E => A x) (epsC_sq (E := E) k)
      simpa using this)
    (fun l x => by
      have := congrArg (fun A : CE E →L[ℝ] CE E => A x) (eps_D0 ρ l)
      split_ifs at this ⊢ <;> simpa [epsC01_eq] using this)
    (fun x => by
      have := congrArg (fun A : CE E →L[ℝ] CE E => A x) (D0_sq hρ)
      simpa using this)
    (Xop_comm01 hu p) (congrFun (Xop_comm02 hu) p) (Xop_comm12 hu p)
  simpa using this

section Nomizu

variable [CompleteSpace E] {ax ay az : ℝ}

/-- **The Nomizu-Kasuya theorem for the Heisenberg nilmanifold with unipotent coefficients** (unconditional form of
`heis_nomizu`): a `D`-closed smooth cochain periodic for the lattice with generators `(ax, 0, 0)`, `(0, ay, 0)`, `(0, 0, az)`
differs from its constant Haar average `heisAv u` by `D η` with `η` periodic and smooth, and `𝔇 (heisAv u) = 0`. -/
theorem heis_nomizu_ce (hax : ax ≠ 0) (hay : ay ≠ 0) (haz : az ≠ 0) {u : Pt → CE E}
    (hu : u ∈ C1 ax ay az) (hcl : Dop (ceData ρ hρ) u = 0) :
    ∃ η ∈ (C1 ax ay az : Submodule ℝ (Pt → CE E)), ceD0 ρ (heisAv ax ay az u) = 0 ∧
      u - (fun _ => heisAv ax ay az u) = Dop (ceData ρ hρ) η :=
  heis_nomizu ax ay az (ceData ρ hρ) hax hay haz (fun _ hu => Dop_Dop ρ hρ hu) hu hcl

end Nomizu

end Concrete

end TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg
