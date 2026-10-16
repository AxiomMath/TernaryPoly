module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.ReflectedClass

@[expose] public section


/-!
# R1c complete: `g5_levelOne` with the antiholomorphic seed of `H'^*`, hypotheses derived

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 and the finite reflection projection.

* `lam_eps_apply`, `mob_eps`, `dnm_eps`: the Levi block of `epsHom g` is `diag(-1,1) lam(g) diag(-1,1)`; hence `mob(lam(eps g))(-conj z) = -conj(mob (lam g) z)` and `dnm(lam(eps g))(-conj z) = conj(dnm (lam g) z)`.
* `hStar_differentiableOn`, `hStar_hmod`: `H^*(z) = conj(H(-conj z))` is holomorphic on the upper half plane and has the same weight `n+3` Levi modularity for `Gamma_P`.
* `g5_levelOne_antiholomorphic`: the class of the model's identity-plane cochain is `[seed H] + (-1)^(n+1) [antiholomorphic seed of H'^*]` (via `eps_seedClass`).
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
  TernaryPeriodPolynomials.Argument GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction
  TernaryPeriodPolynomials.Argument.LevelTransfer

open TernaryPeriodPolynomials.EdgeControl (spherical_fixed)
open TernaryPeriodPolynomials.SphericalDetection.Helpers TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.CuspidalSpan

theorem lam_apply (N : ℕ) (g : ↥(gammaNP N)) (i j : Fin 2) :
    (((gammaNPlaneData N).lam g : GL (Fin 2) ℝ) i j : ℝ) = (g.1 i.castSucc j.castSucc : ℤ) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem lam_eps_apply (N : ℕ) (g : ↥(gammaNP N)) (i j : Fin 2) :
    (((gammaNPlaneData N).lam (epsHom N g) : GL (Fin 2) ℝ) i j : ℝ) =
      (![-1, 1] : Fin 2 → ℝ) i * (![-1, 1] : Fin 2 → ℝ) j * (((gammaNPlaneData N).lam g : GL (Fin 2) ℝ) i j : ℝ) := by
  rw [lam_apply, lam_apply]
  change (((epsConj g.1 : SL(3, ℤ)) i.castSucc j.castSucc : ℤ) : ℝ) = _
  rw [epsConj_apply]
  fin_cases i <;> fin_cases j <;> simp


theorem mob_eps (N : ℕ) (g : ↥(gammaNP N)) (z : ℂ) :
    mob ((gammaNPlaneData N).lam (epsHom N g)) (-conj z) = -conj (mob ((gammaNPlaneData N).lam g) z) := by
  have e := lam_eps_apply N g
  unfold mob
  rw [e 0 0, e 0 1, e 1 0, e 1 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  rw [← neg_div]
  congr 1 <;> ring

theorem dnm_eps (N : ℕ) (g : ↥(gammaNP N)) (z : ℂ) :
    dnm ((gammaNPlaneData N).lam (epsHom N g)) (-conj z) = conj (dnm ((gammaNPlaneData N).lam g) z) := by
  have e := lam_eps_apply N g
  unfold dnm
  rw [e 1 0, e 1 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem hStar_differentiableOn {H : ℂ → ℂ} (hh : DifferentiableOn ℂ H upperSet) :
    DifferentiableOn ℂ (hStar H) upperSet := by
  intro z hz
  have hz' : (-conj z) ∈ upperSet := by
    simpa [upperSet] using hz
  have h1 : DifferentiableAt ℂ H (-conj z) :=
    (hh _ hz').differentiableAt (isOpen_upperSet.mem_nhds hz')
  have h2 : DifferentiableAt ℂ (fun w => H (-w)) (conj z) :=
    DifferentiableAt.comp (conj z) (f := fun w : ℂ => -w) h1 differentiableAt_id.neg
  have h3 := h2.conj_conj
  rw [Complex.conj_conj] at h3
  exact h3.differentiableWithinAt

theorem hStar_hmod (N n : ℕ) {H : ℂ → ℂ}
    (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      H (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * H z) :
    ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      hStar H (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * hStar H z := by
  intro g z hz
  have hz' : 0 < (-conj z).im := by simpa using hz
  have e := hmod (epsHom N g) (-conj z) hz'
  rw [mob_eps, dnm_eps] at e
  unfold hStar
  have e2 : H (-conj (mob ((gammaNPlaneData N).lam g) z)) =
      conj (dnm ((gammaNPlaneData N).lam g) z) ^ (n + 3) * H (-conj z) := e
  rw [e2, map_mul, map_pow, Complex.conj_conj]

/-- **`g5_levelOne` with the antiholomorphic seed of `H'^*`.**  Besides the cochain identity, the class of the identity-plane cochain of the model, pushed to Mathlib's group
cohomology of `Γ_P = Γ(N) ∩ P(ℤ)`, is `[seed H] + (-1)^(n+1) [antiholomorphic seed of H'^*]` with `H = F(1·b_F(1))`, `H' = F(J·b_F(1))` and
`H'^*(z) = \overline{H'(-\bar z)}`; all hypotheses on the scalar functions are proved from the Eichler input. -/
theorem g5_levelOne_antiholomorphic (N n : ℕ) [NeZero N] (h3 : 3 ∣ N) (D : InducingData n) (I : EichlerInput D.cusp n)
    (F : BinaryAdelicGL → ℂ → ℂ) (hF : F = cuspScalarWeightedRealization D.cusp I.halfWeight I.vector) :
    ∃ (Gm Gm' Gms : ℕ → ℂ → ℂ) (s : SeedHyp N n (F (1 * bF (1 : AdelicGL))) Gm)
      (s' : SeedHyp N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm')
      (ss : SeedHyp N n (hStar (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)))) Gms),
      LevelOneConclusion N n D F Gm Gm' s s' ∧
      (groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (Submodule.Quotient.mk (gramCocycleW (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm s.hh s.hG s.hmod)
              (rhoR_gammaNP N n) +
            reflCocycle N n (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL))) Gm' s'.hh s'.hG s'.hmod))) =
      complexifyG N n ((gammaNPlaneData N).seedClass (F (1 * bF (1 : AdelicGL))) n Gm s.hh s.hG s.hmod) +
        ((-1 : ℂ) ^ (n + 1)) • complexifyG N n ((gammaNPlaneData N).seedConjClass
          (hStar (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)))) n Gms ss.hh ss.hG ss.hmod) := by
  obtain ⟨Gm, Gm', s, s', hc⟩ := g5_levelOne_of_eichler N n h3 D I F hF
  have hhs := hStar_differentiableOn s'.hh
  obtain ⟨Gms, -, hGs⟩ := exists_moment_primitives _ hhs
  let ss : SeedHyp N n (hStar (F (atInfinity UpperHalfPlane.J * bF (1 : AdelicGL)))) Gms :=
    ⟨hhs, hGs, hStar_hmod N n s'.hmod⟩
  refine ⟨Gm, Gm', Gms, s, s', ss, hc, ?_⟩
  have he := eps_seedClass N n _ _ Gm' Gms s'.hh s'.hG s'.hmod ss.hh ss.hG ss.hmod (fun z _ => rfl)
  exact hc.2.trans (congrArg (fun t => complexifyG N n
    ((gammaNPlaneData N).seedClass (F (1 * bF (1 : AdelicGL))) n Gm s.hh s.hG s.hmod) + t) he)

end TernaryPeriodPolynomials.Argument.FormSeedBridge
