module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.Separation

@[expose] public section


/-!
# Local multiplicity at the two level-one cusps

For the identity-plane cusp and the good-line cusp and a character `c` of the away-three Hecke
algebra with `‖c(T_2) - 1‖ ≤ 3/4` (the cuspidal pair character for `n ≥ 3`), the local joint
generalized eigenspace is finite dimensional of dimension at most one. For odd `n` the binary edge
embeds it into a joint generalized eigenspace of `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^σ)` whose eigenvalue at
`T_2` is separated from the Eisenstein eigenvalue (`Separation`), hence consists of period classes;
for even `n` it vanishes (`LocalUniqueness`).

Original work by Claude Sonnet 5.5 and Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.ParabolicES

namespace TernaryPeriodPolynomials.LevelOneEisenstein

/-- A submodule mapped into a finite-dimensional submodule by an injective map is finite
dimensional. -/
theorem finiteDimensional_of_injective_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (K : Submodule ℂ V)
    (L : Submodule ℂ W) [FiniteDimensional ℂ L] (hKL : ∀ x ∈ K, f x ∈ L) :
    FiniteDimensional ℂ K := by
  refine Module.Finite.of_injective (f.restrict hKL) ?_
  intro a b h
  exact Subtype.ext (hf (congrArg Subtype.val h))

variable {n : ℕ}

/-- **Identity-plane cusp: local multiplicity at most one.** -/
theorem localJoint_identityPlane_finite_le_one (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    FiniteDimensional ℂ (localJoint n trivialCharacter c .plane false) ∧
      Module.finrank ℂ (localJoint n trivialCharacter c .plane false) ≤ 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · rw [IdentityPlaneEven.localJoint_identityPlane_eq_bot n hn heven c]
    exact ⟨inferInstance, by simp⟩
  · have : FiniteDimensional ℂ (jointH1 (n + 1) (-1) (eIdentity n c)) :=
      jointH1_finiteDimensional _ _ _
    refine ⟨finiteDimensional_of_injective_map _ (IdentityPlaneHecke.edgeH2_injective n hn hodd)
      _ (jointH1 (n + 1) (-1) (eIdentity n c)) (fun _ hx => edgeH2_mem_jointH1 c hn hodd hx),
      (finrank_localJoint_identityPlane_le c hn hodd).trans ?_⟩
    exact finrank_jointH1_identity_le_one hodd _ (c (TpExistence.tp LocalUniqueness.two)) hc rfl

/-- **Good-line cusp: local multiplicity at most one.** -/
theorem localJoint_goodLine_finite_le_one (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    FiniteDimensional ℂ (localJoint n trivialCharacter c .line true) ∧
      Module.finrank ℂ (localJoint n trivialCharacter c .line true) ≤ 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · rw [localJoint_goodLine_eq_bot_of_even c hn heven hc]
    exact ⟨inferInstance, by simp⟩
  · have : FiniteDimensional ℂ (jointH1 (n + 1) 0 (eGoodLine n c)) :=
      jointH1_finiteDimensional _ _ _
    have hle := localJoint_le_ML (n := n) c hc
    have hfin : FiniteDimensional ℂ
        ((localJoint n trivialCharacter c .line true).comap (ML n).subtype) :=
      finiteDimensional_of_injective_map (phiL n hn) (phiL_injective hn) _
        (jointH1 (n + 1) 0 (eGoodLine n c)) (fun y hy => phiL_mem_jointH1 c hn y hy)
    refine ⟨Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle), ?_⟩
    exact (finrank_localJoint_goodLine_le c hn hc).trans
      (finrank_jointH1_goodLine_le_one hodd _ (c (TpExistence.tp LocalUniqueness.two)) hc rfl)

end TernaryPeriodPolynomials.LevelOneEisenstein
