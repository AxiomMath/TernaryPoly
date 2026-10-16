module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Actions
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- A one-cochain viewed through its actual degree-two differential. -/
def cob₂ (u : G φ → A) : cocycles₂ A :=
  ⟨d₁₂ A u, d₁₂_apply_mem_cocycles₂ u⟩

@[simp] theorem cob₂_apply (u : G φ → A) (g h : G φ) :
    cob₂ φ A u (g,h) = A.ρ g (u h) - u (g*h) + u g := rfl

theorem H2π_cob₂ (u : G φ → A) : H2π A (cob₂ φ A u) = 0 :=
  (H2π_eq_zero_iff _).mpr ⟨u, rfl⟩

def restrict₂ (c : cocycles₂ A) : cocycles₂ (radicalRep φ A) :=
  mapCocycles₂ (nIn φ) (𝟙 _) c

@[simp] theorem restrict₂_apply (c : cocycles₂ A) (n m : N) :
    restrict₂ φ A c (n,m) = c (nIn φ n, nIn φ m) := rfl

theorem q_mul_n (q : Q) (n : N) :
    qIn φ q * nIn φ (φ q⁻¹ n) = nIn φ n * qIn φ q := by
  rw [SemidirectProduct.inl_aut]
  simp [mul_assoc]

/-- Explicit homotopy showing that conjugation fixes a restricted two-cohomology class. -/
theorem restriction_conjugation_difference (c : cocycles₂ A) (q : Q) (n m : N) :
    A.ρ (qIn φ q) (c (nIn φ (φ q⁻¹ n), nIn φ (φ q⁻¹ m))) -
      c (nIn φ n, nIn φ m) =
    A.ρ (nIn φ n)
        (c (qIn φ q, nIn φ (φ q⁻¹ m)) - c (nIn φ m, qIn φ q)) -
      (c (qIn φ q, nIn φ (φ q⁻¹ (n*m))) - c (nIn φ (n*m), qIn φ q)) +
      (c (qIn φ q, nIn φ (φ q⁻¹ n)) - c (nIn φ n, qIn φ q)) := by
  have h₁ := (mem_cocycles₂_iff c).mp c.property
    (qIn φ q) (nIn φ (φ q⁻¹ n)) (nIn φ (φ q⁻¹ m))
  have h₂ := (mem_cocycles₂_iff c).mp c.property
    (nIn φ n) (qIn φ q) (nIn φ (φ q⁻¹ m))
  have h₃ := (mem_cocycles₂_iff c).mp c.property
    (nIn φ n) (nIn φ m) (qIn φ q)
  simp only [q_mul_n, ← map_mul] at h₁ h₂ h₃
  rw [map_sub]
  linear_combination (norm := module) -h₁ + h₂ - h₃

/-- Restriction lands in the fixed vectors for the genuine quotient action. -/
theorem restriction_H2_fixed (c : cocycles₂ A) (q : Q) :
    (cohomologyRep φ A 2).ρ q (H2π (radicalRep φ A) (restrict₂ φ A c)) =
      H2π (radicalRep φ A) (restrict₂ φ A c) := by
  rw [cohomologyRep_apply, H2π_comp_map_apply]
  apply (H2π_eq_iff _ _).mpr
  refine ⟨fun n => c (qIn φ q, nIn φ (φ q⁻¹ n)) - c (nIn φ n, qIn φ q), ?_⟩
  funext ⟨n,m⟩
  exact (restriction_conjugation_difference φ A c q n m).symm

/-- The fixed-vector hypothesis kills the restriction class, giving an actual primitive. -/
theorem restriction_primitive
    (hfixed : ∀ x : groupCohomology (radicalRep φ A) 2,
      (∀ q, (cohomologyRep φ A 2).ρ q x = x) → x = 0)
    (c : cocycles₂ A) :
    ∃ u : N → A, ∀ n m,
      A.ρ (nIn φ n) (u m) - u (n*m) + u n = c (nIn φ n, nIn φ m) := by
  have hz := hfixed _ (restriction_H2_fixed φ A c)
  obtain ⟨u, hu⟩ := (H2π_eq_zero_iff _).mp hz
  exact ⟨u, fun n m => congrFun hu (n,m)⟩

end TernaryPoly.LowDegreeHochschildSerre
