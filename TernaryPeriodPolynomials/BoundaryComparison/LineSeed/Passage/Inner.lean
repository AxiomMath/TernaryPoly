module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge

@[expose] public section


/-!
# Inner automorphisms act trivially on `H²` (Passage 4)

For a group `G`, a representation `M` and `c ∈ G`, the map on `H²(G, M)` induced by the conjugation `x ↦ c⁻¹ x c` with the coefficient map `ρ(c)` is the identity
(`map_conj_H2`).  On cocycles, `β^c(x, y) = ρ(c) β(c⁻¹xc, c⁻¹yc)` differs from `β` by the coboundary of `u(x) = β(c, c⁻¹xc) - β(x, c)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

variable {G : Type} [Group G] (M : Rep ℂ G) (c : G)

/-- Conjugation `x ↦ c⁻¹ x c` as a monoid homomorphism. -/
def conjInv : G →* G where
  toFun x := c⁻¹ * x * c
  map_one' := by simp
  map_mul' x y := by simp [mul_assoc]

/-- The intertwiner `ρ(c)` from the restriction along `conjInv c`. -/
def conjInvRep : Rep.res (conjInv c) M ⟶ M :=
  Rep.ofHom ⟨M.ρ c, fun x => by
    ext v
    change M.ρ c (M.ρ (c⁻¹ * x * c) v) = M.ρ x (M.ρ c v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group⟩

/-- **Inner automorphisms act trivially on `H²`.** -/
theorem map_conj_H2 (x : H2 M) : (groupCohomology.map (conjInv c) (conjInvRep M c) 2).hom x = x := by
  induction x using H2_induction_on with | _ β => ?_
  rw [groupCohomology.H2π_comp_map_apply]
  rw [← sub_eq_zero, ← map_sub, groupCohomology.H2π_eq_zero_iff]
  refine ⟨fun x => ((β : G × G → M) (c, c⁻¹ * x * c)) - (β : G × G → M) (x, c), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  have h1 := (mem_cocycles₂_iff _).1 β.2
  have e1 := h1 c (c⁻¹ * x * c) (c⁻¹ * y * c)
  have e2 := h1 x c (c⁻¹ * y * c)
  have e3 := h1 x y c
  have hx : c * (c⁻¹ * x * c) = x * c := by group
  have hy : c * (c⁻¹ * y * c) = y * c := by group
  have hxy : (c⁻¹ * x * c) * (c⁻¹ * y * c) = c⁻¹ * (x * y) * c := by group
  rw [hx, hxy] at e1
  rw [hy] at e2
  rw [groupCohomology.d₁₂_hom_apply]
  change _ = (groupCohomology.mapCocycles₂ (conjInv c) (conjInvRep M c) β : G × G → M) (x, y) - (β : G × G → M) (x, y)
  have hm : (groupCohomology.mapCocycles₂ (conjInv c) (conjInvRep M c) β : G × G → M) (x, y) =
      M.ρ c ((β : G × G → M) (c⁻¹ * x * c, c⁻¹ * y * c)) := rfl
  rw [hm]
  simp only [map_sub]
  linear_combination (norm := module) e1 - e2 + e3
