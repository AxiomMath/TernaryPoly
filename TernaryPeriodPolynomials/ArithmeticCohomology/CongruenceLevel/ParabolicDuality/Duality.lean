module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Cochains
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLefschetz

@[expose] public section

/-!
# Poincaré duality for the Farey cochain complexes: `H¹_c(E) × H¹(E') → ℂ`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

`Coupling ρ ρ'`: a perfect `Γ`-invariant pairing of finite-dimensional complex `Γ`-modules.  `annihilator_ker_dc`: the annihilator of the
compactly supported cocycles `ker d_c(E) ⊆ C¹(E)` in `C¹(E')` is `δ C⁰(E')`; `annihilator_ker_dc'` the same with the roles exchanged.  This is
the cellular Poincaré-Lefschetz duality of the compactified modular curve: it rests on `pair1_delta` (`d_c` and `δ'` are adjoint up to `-2`)
and on the perfectness of the orbit pairings on `C⁰`, `C¹`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

variable {Γ : Subgroup IntegralGL}

/-- A perfect `Γ`-invariant pairing between two finite-dimensional complex `Γ`-modules (a representation and its dual). -/
structure Coupling {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ Γ E) (ρ' : Representation ℂ Γ E') where
  e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ
  inv : ∀ (γ : Γ) (v : E) (w : E'), e (ρ γ v) (ρ' γ w) = e v w
  left : ∀ v, (∀ w, e v w = 0) → v = 0
  right : ∀ w, (∀ v, e v w = 0) → w = 0

section Basic

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  {ρ : Representation ℂ Γ E} {ρ' : Representation ℂ Γ E'}

/-- The transposed pairing. -/
def Coupling.flip (C : Coupling ρ ρ') : Coupling ρ' ρ where
  e := C.e.flip
  inv := fun γ w v => by simpa using C.inv γ v w
  left := C.right
  right := C.left

theorem Coupling.flip_e (C : Coupling ρ ρ') : C.flip.e = C.e.flip := rfl

theorem pairR_flip {X : Type} [MulAction Γ X] (e : E →ₗ[ℂ] E' →ₗ[ℂ] ℂ) (S : RepSystem Γ X) (F : X → E) (G : X → E') :
    pairR e.flip S G F = pairR e S F G := by
  simp [pairR]

theorem c1_finite (D : FareyData Γ) [FiniteDimensional ℂ E] : FiniteDimensional ℂ (C1 ρ) := by
  have := eqFn_finite (ρ := ρ) D.RE
  exact Submodule.finiteDimensional_of_le (S₁ := C1 ρ) (S₂ := EqFn Γ OTE ρ) (fun F hF => (hF : F ∈ C1 ρ).1)

theorem c0_finite (D : FareyData Γ) [FiniteDimensional ℂ E] : FiniteDimensional ℂ (C0 ρ) :=
  eqFn_finite (ρ := ρ) D.RT

/-- The pairing on `C¹(E) × C¹(E')`. -/
def pV (C : Coupling ρ ρ') (D : FareyData Γ) : C1 ρ →ₗ[ℂ] C1 ρ' →ₗ[ℂ] ℂ :=
  (pairBil C.e D.RE).compl₁₂ (C1 ρ).subtype (C1 ρ').subtype

/-- The pairing on `C⁰(E) × C⁰(E')`. -/
def pW (C : Coupling ρ ρ') (D : FareyData Γ) : C0 ρ →ₗ[ℂ] C0 ρ' →ₗ[ℂ] ℂ :=
  (pairBil C.e D.RT).compl₁₂ (C0 ρ).subtype (C0 ρ').subtype

theorem pV_apply (C : Coupling ρ ρ') (D : FareyData Γ) (F : C1 ρ) (G : C1 ρ') :
    pV C D F G = pairR C.e D.RE F.1 G.1 := rfl

theorem pW_apply (C : Coupling ρ ρ') (D : FareyData Γ) (F : C0 ρ) (G : C0 ρ') :
    pW C D F G = pairR C.e D.RT F.1 G.1 := rfl

/-- `⟨δ H, G⟩ = -2 ⟨H, d_c G⟩`. -/
theorem pV_delta' (C : Coupling ρ ρ') (D : FareyData Γ) (H : C0 ρ) (G : C1 ρ') :
    pV C D (delta ρ H) G = -2 * pW C D H (dc ρ' G) := by
  have h := pair1_delta C.flip.e C.flip.inv D G H
  rw [Coupling.flip_e, pairR_flip, pairR_flip] at h
  rw [pV_apply, pW_apply]
  exact h

theorem pV_delta (C : Coupling ρ ρ') (D : FareyData Γ) (F : C1 ρ) (H' : C0 ρ') :
    pV C D F (delta ρ' H') = -2 * pW C D (dc ρ F) H' :=
  pair1_delta C.e C.inv D F H'

end Basic

section Duality

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
  {ρ : Representation ℂ Γ E} {ρ' : Representation ℂ Γ E'}

/-- **The annihilator of the compactly supported cocycles** `ker d_c ⊆ C¹(E)` inside `C¹(E')` is the space of coboundaries
`δ C⁰(E')`: Poincaré duality of the Farey surface `Γ\ℍ` between `H¹_c(E)` and `H¹(E')`. -/
theorem annihilator_ker_dc (C : Coupling ρ ρ') (D : FareyData Γ) (G : C1 ρ')
    (hG : ∀ F : C1 ρ, dc ρ F = 0 → pV C D F G = 0) : G ∈ LinearMap.range (delta ρ') := by
  have := c1_finite (ρ := ρ) D
  have := c1_finite (ρ := ρ') D
  have := c0_finite (ρ := ρ) D
  have := c0_finite (ρ := ρ') D
  refine annihilator_ker_eq_range (pV C D) ?_ (pW C D) ?_ ?_ (dc ρ) (delta ρ') (-1 / 2) ?_ G ?_
  · exact fun G h => pair1_right_perfect C.e C.inv D C.right G (fun F => h F)
  · exact fun F h => Subtype.ext (pairR_left_perfect ρ ρ' C.e D.RT D.freeT C.left F.2 (fun G hG => h ⟨G, hG⟩))
  · exact fun G h => Subtype.ext (pairR_right_perfect ρ ρ' C.e D.RT D.freeT C.right G.2 (fun F hF => h ⟨F, hF⟩))
  · intro F H'
    rw [pW_apply, pV_apply, pair1_delta C.e C.inv D F H']
    ring
  · intro F hF
    exact hG F (LinearMap.mem_ker.mp hF)

/-- The same with the roles of `E` and `E'` exchanged: the annihilator of `ker d_c(E')` in `C¹(E)` is `δ C⁰(E)`. -/
theorem annihilator_ker_dc' (C : Coupling ρ ρ') (D : FareyData Γ) (F : C1 ρ)
    (hF : ∀ G : C1 ρ', dc ρ' G = 0 → pV C D F G = 0) : F ∈ LinearMap.range (delta ρ) := by
  refine annihilator_ker_dc C.flip D F ?_
  intro G hG
  have := hF G hG
  rw [pV_apply] at this ⊢
  rw [Coupling.flip_e, pairR_flip]
  exact this

end Duality

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
