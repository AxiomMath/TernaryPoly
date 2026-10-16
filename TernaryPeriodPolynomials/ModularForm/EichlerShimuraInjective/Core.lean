module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.CosetDecay

@[expose] public section


/-!
# Core vanishing theorem

`core_f`, `core_g`: if `hol F + antihol G` is a coboundary of the period cocycles, then `F = G = 0` (Petersson positivity by Green's formula on a truncated fundamental domain of `SL₂(ℤ)`).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

section Core

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

theorem map_conj_invCoordPoly' (γ : GL (Fin 2) ℝ) (i : Fin 2) :
    MvPolynomial.map (starRingEnd ℂ) (invCoordPoly γ i) = invCoordPoly γ i := by
  fin_cases i <;> simp [invCoordPoly]

theorem map_conj_bind' (γ : GL (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.bind₁ (invCoordPoly γ) P) =
      MvPolynomial.bind₁ (invCoordPoly γ) (MvPolynomial.map (starRingEnd ℂ) P) := by
  rw [MvPolynomial.map_bind₁]
  congr 2
  funext i
  exact map_conj_invCoordPoly' γ i

omit [Γ.FiniteIndex] in
/-- Swapping the roles of the holomorphic and antiholomorphic parts. -/
theorem Setup.swap (S : Setup Γ n f g Gf Gg v) :
    Setup Γ n g f Gg Gf (MvPolynomial.map (starRingEnd ℂ) v) where
  hf := S.hg
  hg := S.hf
  mf := S.mg
  mg := S.mf
  dGf := S.dGg
  dGg := S.dGf
  Gf0 := S.Gg0
  Gg0 := S.Gf0
  vh := S.vh.map _
  cob γ hγ := by
    have h := congrArg (MvPolynomial.map (starRingEnd ℂ)) (S.cob γ hγ)
    rw [map_add, map_sub, MvPolynomial.map_map, map_conj_bind'] at h
    have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; simp
    rw [e, MvPolynomial.map_id] at h
    rw [add_comm]
    exact h

/-- **Core vanishing**: the holomorphic part of a combined period class that is a coboundary vanishes. -/
theorem core_f (S : Setup Γ n f g Gf Gg v) (hdf : Decays n f) (hdg : Decays n g) :
    ∀ z : ℂ, 0 < z.im → f z = 0 :=
  f_zero_of_decay S (Atil_integral_tendsto S hdf hdg)

theorem core_g (S : Setup Γ n f g Gf Gg v) (hdf : Decays n f) (hdg : Decays n g) :
    ∀ z : ℂ, 0 < z.im → g z = 0 :=
  core_f S.swap hdg hdf

end Core

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
