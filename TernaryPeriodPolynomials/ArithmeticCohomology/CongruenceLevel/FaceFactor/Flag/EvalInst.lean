module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Conj
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Def
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Natural

@[expose] public section


open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)


/-!
# M1 packaged as `FlagEval`, and the transport compatibility of the flag functionals

Formalized by Claude Sonnet 5.5.

* `flagEval : FlagEval` (`M3Def`): `G o = G_{o.out}` (`flagGen`), `lam o = λ_{o.out}` (`flagLam`).
* `lam_conj_transport`: for `o.out = g • F₀` (`g ∈ Γ(6)`), `λ_{o.out} ∘ flagConjTransport g F₀ o = λ_{F₀}`, the frame independence of `FlagH3/FrameIndep` in the shape of the conjugation transport: the frame
  `h₀ p⁻¹` of `g • F₀` (`g = p`) carries the Heisenberg cycle of the frame `h₀` of `F₀` through `s ↦ g⁻¹ s g` (`conj_unipElt`), and the flag functional is natural for group homomorphisms (`FlagCohomDatum.lam_transport`).
* `flagGen_conj_transport`, `flagEval_G_conj`: `T (G_{F₀}) = G_{o.out}`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.ConvergenceC4 (gammaN)

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- `resTrivialEquiv` does not change a cocycle function. -/
theorem resTrivialEquiv_class (G : Type) [Group G] (S : Subgroup G) (c : (Fin 3 → S) → ℚ)
    (hc : (inhomogeneousCochains.d (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ G))) 3).hom c = 0) :
    ∃ hc' : (inhomogeneousCochains.d (Rep.trivial ℚ S ℚ) 3).hom c = 0,
      resTrivialEquiv G S 3 ((groupCohomology.π (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ G))) 3).hom
        (groupCohomology.cocyclesMk c hc)) =
      (groupCohomology.π (Rep.trivial ℚ S ℚ) 3).hom (groupCohomology.cocyclesMk c hc') := by
  have hc' : (inhomogeneousCochains.d (Rep.trivial ℚ S ℚ) 3).hom c = 0 := hc
  refine ⟨hc', ?_⟩
  unfold resTrivialEquiv
  exact map_class_cocyclesMk' (A := Rep.res S.subtype (𝟙_ (Rep.{0} ℚ G))) (B := Rep.trivial ℚ S ℚ) _ _ 3 c hc (by exact hc')


/-- **`resTrivialEquiv` is natural for the conjugation transport.** -/
theorem resTrivialEquiv_flagConjTransport (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀)
    (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F₀).subtype Wq) 3) :
    resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 o.out) 3 ((flagConjTransport g F₀ o hF₀).hom x) =
      (groupCohomology.map (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
        (trivMap _) 3).hom (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F₀) 3 x) := by
  obtain ⟨c, hc, rfl⟩ := exists_class_cocyclesMk 3 x
  obtain ⟨h1, e1⟩ := map_class_cocyclesMk
    (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
    (conjComparison Wq g (MulAction.stabilizer Γ6 F₀) (MulAction.stabilizer Γ6 o.out)
      (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
      (conjStabHom_apply g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))) 3 c hc
  change resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 o.out) 3
    ((groupCohomology.map _ _ 3).hom ((groupCohomology.π _ 3).hom (groupCohomology.cocyclesMk c hc))) = _
  rw [e1]
  obtain ⟨k1, r1⟩ := resTrivialEquiv_class Γ6 (MulAction.stabilizer Γ6 o.out) _ h1
  rw [r1]
  obtain ⟨k2, r2⟩ := resTrivialEquiv_class Γ6 (MulAction.stabilizer Γ6 F₀) c hc
  rw [r2]
  have k3 : (inhomogeneousCochains.d (Rep.trivial ℚ (MulAction.stabilizer Γ6 o.out) ℚ) 3).hom
      (fun x => (trivMap (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))).hom
        (c (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2) ∘ x))) = 0 := k1
  rw [map_class_cocyclesMk' (A := Rep.trivial ℚ (MulAction.stabilizer Γ6 F₀) ℚ)
    (B := Rep.trivial ℚ (MulAction.stabilizer Γ6 o.out) ℚ) _ _ 3 c k2 k3]
  rfl

open TernaryPeriodPolynomials.Argument.GammaNFaces in
theorem conj_unipElt (g : Γ6) (F₀ F : Flag) (f : MulAction.stabilizer Γ6 F →* MulAction.stabilizer Γ6 F₀)
    (hf : ∀ s, (f s : Γ6) = g⁻¹ * (s : Γ6) * g)
    (h₀ h₁ : SL(3, ℤ)) (hh₀ : flagOf h₀ = F₀) (p : gammaN 6) (hp : gammaSixEquiv p = g)
    (hrel : h₁ = h₀ * p.1⁻¹) (hh₁ : flagOf h₁ = F) (a b c : ℤ) (ha : (6 : ℤ) ∣ a) (hb : (6 : ℤ) ∣ b) (hc : (6 : ℤ) ∣ c) :
    f (stabCongr F h₁ hh₁ (unipElt h₁ a b c ha hb hc)) =
      stabCongr F₀ h₀ hh₀ (unipElt h₀ a b c ha hb hc) := by
  apply Subtype.ext
  apply gammaSixEquiv.symm.injective
  apply Subtype.ext
  have e1 := stabCongr_val F h₁ hh₁ (unipElt h₁ a b c ha hb hc)
  have e2 := stabCongr_val F₀ h₀ hh₀ (unipElt h₀ a b c ha hb hc)
  rw [e2]
  rw [hf]
  rw [map_mul, map_mul, map_inv, ← hp, MulEquiv.symm_apply_apply]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [e1]
  have key : ∀ u : SL(3, ℤ), (p.1)⁻¹ * ((h₀ * p.1⁻¹)⁻¹ * u * (h₀ * p.1⁻¹)) * p.1 = h₀⁻¹ * u * h₀ := fun u => by group
  subst hrel
  exact key _

open TernaryPeriodPolynomials.Argument.GammaNFaces in
/-- **`λ_F` is compatible with the conjugation transport** (S6's `flagConjTransport`): for `o.out = g • F₀`, `λ_{o.out} ∘ T = λ_{F₀}`. -/
theorem lam_conj_transport (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀)
    (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F₀).subtype Wq) 3) :
    flagLam o.out ((flagConjTransport g F₀ o hF₀).hom x) = flagLam F₀ x := by
  obtain ⟨h₀, hh₀⟩ := exists_flagOf F₀
  obtain ⟨p, hp⟩ := gammaSixEquiv.surjective g
  have hh₁ : flagOf (h₀ * p.1⁻¹) = o.out := by
    rw [hF₀, ← hh₀, ← hp]; exact (smul_flagOf p h₀).symm
  have hS : ∀ s : MulAction.stabilizer Γ6 o.out, (s : Γ6) • (g • F₀) = g • F₀ := fun s => by rw [← hF₀]; exact s.2
  have hf := conjStabHom_apply g F₀ (MulAction.stabilizer Γ6 o.out) hS
  have key := resTrivialEquiv_flagConjTransport g F₀ o hF₀ x
  have hz : ∀ θ : (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ,
      chainEval (flagDataAt o.out (h₀ * p.1⁻¹) hh₁).z
        (fun y : Fin 3 → MulAction.stabilizer Γ6 o.out =>
          θ (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) hS ∘ y)) =
      chainEval (flagDataAt F₀ h₀ hh₀).z θ := fun θ =>
    chainEval_heisCycle_comp (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) hS) _ _ _ _
      (conj_unipElt g F₀ o.out _ hf h₀ _ hh₀ p hp rfl hh₁ 6 0 0 (dvd_refl _) (dvd_zero _) (dvd_zero _))
      (conj_unipElt g F₀ o.out _ hf h₀ _ hh₀ p hp rfl hh₁ 0 6 0 (dvd_zero _) (dvd_refl _) (dvd_zero _)) θ
  have e0 := LinearMap.congr_fun (flagLam_frame o.out _ hh₁) ((flagConjTransport g F₀ o hF₀).hom x)
  have e1 := LinearMap.congr_fun (flagLam_frame F₀ h₀ hh₀) x
  rw [e0, e1]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [key]
  exact FlagCohomDatum.lam_transport (flagDataAt F₀ h₀ hh₀) (flagDataAt o.out _ hh₁) _ hz _

/-- **`G_F` is carried by the conjugation transport**: `T (G_{F₀}) = G_{o.out}` for `o.out = g • F₀`. -/
theorem flagGen_conj_transport (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀) :
    (flagConjTransport g F₀ o hF₀).hom (flagGen F₀) = flagGen o.out :=
  flagLam_injective o.out (by rw [lam_conj_transport g F₀ o hF₀, flagLam_flagGen, flagLam_flagGen])

/-- **M1 packaged**: the evaluation data `FlagEval` of `M3Def`: `G o = G_{o.out}`, `lam o = λ_{o.out}`. -/
def flagEval : FlagEval where
  D := flagH3Data
  lam o := flagLam o.out
  lam_G o := flagLam_flagH3Data_G o

theorem flagEval_lam (o : labelOrbits Γ6 Flag) : flagEval.lam o = flagLam o.out := rfl

theorem flagEval_G (o : labelOrbits Γ6 Flag) : flagEval.D.G o = flagGen o.out := rfl

/-- **Transport compatibility** (`lamBase F₀ = flagLam F₀`): `E.lam o ∘ T = λ_{F₀}`. -/
theorem flagEval_lam_conj (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀)
    (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 F₀).subtype Wq) 3) :
    flagEval.lam o ((flagConjTransport g F₀ o hF₀).hom x) = flagLam F₀ x :=
  lam_conj_transport g F₀ o hF₀ x

/-- … and the class `E.D.G o` is the transport of `G_{F₀}`. -/
theorem flagEval_G_conj (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀) :
    flagEval.D.G o = (flagConjTransport g F₀ o hF₀).hom (flagGen F₀) :=
  (flagGen_conj_transport g F₀ o hF₀).symm

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
