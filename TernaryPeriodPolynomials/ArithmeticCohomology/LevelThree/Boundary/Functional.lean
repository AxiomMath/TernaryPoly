module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.FullBound

@[expose] public section


/-!
# The boundary functionals of `H¹(Γ₁'(3), Sym^m ⊗ det^e)`

For a crossed one-cocycle `z` of the level-three Levi `Γ₁'(3)` with coefficients
`Sym^m(ℂ²) ⊗ det^e` put

* `β_∞(z) = z(T)(1, 0)`, `T = [[1,1],[0,1]]` (the value at the cusp `∞`),
* `β_0(z) = z(L)(0, 1)`, `L = [[1,0],[3,1]]` (the value at the cusp `0`).

Both vanish on coboundaries, because `(T - 1)V = {p(1,0) = 0}` and `(L - 1)V = {p(0,1) = 0}`
(`FullBound.movedSpace_upper_eq`, `movedSpace_lower_eq`), hence define linear maps
`betaInf`, `betaZero` on `CrossedH1 (levelRep m e)`.

* `cuspFunctional`: the generic construction `z ↦ φ (z g)` on a quotient by coboundaries, with
  `cuspFunctional_map` (equivariance under an operator that lifts to cocycles) and
  `ker_cuspFunctional_inf` (kernels of two such functionals intersect in `parabolicH1`);
* `ker_betaInf_inf_ker_betaZero`: `ker β_∞ ⊓ ker β_0 = parabolicH1 (levelRep m e) T L`, the classes
  trivial on both cusp stabilizers;
* `betaInf_eq_zero_of_even` (`e + m` even) and `betaZero_eq_zero_of_even` (`e` even): the reflection
  `diag(-1, 1)` kills the boundary values by parity (`FullBound.cusp_infinity_zero`,
  `cusp_zero_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryFunctional

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic
open TwoGenerator GammaOneThree SymFixed ParabolicBounds ReflectionBound SharpBounds FullBound
open GeneralEisenstein Module Matrix MvPolynomial

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- `z ↦ φ (z g)` on crossed cocycles. -/
def cuspCocycle (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ) :
    crossedCocycles ρ →ₗ[ℂ] ℂ :=
  φ.comp (TwoGenerator.evalAt ρ g)

theorem cuspCocycle_apply (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (z : crossedCocycles ρ) : cuspCocycle ρ g φ z = φ (z.val g) := rfl

theorem boundaries_le_ker_cuspCocycle (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (h : ∀ v, φ (ρ g v - v) = 0) :
    crossedBoundaries ρ ≤ LinearMap.ker (cuspCocycle ρ g φ) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  change φ (ρ g v - v) = 0
  exact h v

/-- The functional `[z] ↦ φ (z g)` on `H¹`, well defined when `φ` kills `(g - 1) V`. -/
def cuspFunctional (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (h : ∀ v, φ (ρ g v - v) = 0) : CrossedH1 ρ →ₗ[ℂ] ℂ :=
  (crossedBoundaries ρ).liftQ (cuspCocycle ρ g φ) (boundaries_le_ker_cuspCocycle ρ g φ h)

theorem cuspFunctional_mk (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (h : ∀ v, φ (ρ g v - v) = 0) (z : crossedCocycles ρ) :
    cuspFunctional ρ g φ h (Submodule.Quotient.mk z) = φ (z.val g) := rfl

theorem cuspFunctional_eq_zero (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (h : ∀ v, φ (ρ g v - v) = 0) (hz : ∀ z : crossedCocycles ρ, φ (z.val g) = 0) :
    cuspFunctional ρ g φ h = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.zero_apply]
  exact hz z

/-- **Equivariance**: if an endomorphism of `H¹` lifts to a map `lift` on cocycles and
`φ ((lift z) g) = c · φ (z g)`, then `cuspFunctional ∘ F = c · cuspFunctional`. -/
theorem cuspFunctional_map (ρ : Representation ℂ G V) (g : G) (φ : V →ₗ[ℂ] ℂ)
    (h : ∀ v, φ (ρ g v - v) = 0) (F : CrossedH1 ρ →ₗ[ℂ] CrossedH1 ρ)
    (lift : crossedCocycles ρ → crossedCocycles ρ)
    (hF : ∀ z : crossedCocycles ρ, F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (lift z))
    (c : ℂ) (hz : ∀ z : crossedCocycles ρ, φ ((lift z).val g) = c * φ (z.val g))
    (x : CrossedH1 ρ) : cuspFunctional ρ g φ h (F x) = c * cuspFunctional ρ g φ h x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [hF, cuspFunctional_mk, cuspFunctional_mk]
  exact hz z

/-- **Parabolic classes are the common kernel of two cusp functionals**, when `(T - 1) V` and
`(L - 1) V` are the kernels of `φ₁` and `φ₂`. -/
theorem ker_cuspFunctional_inf (ρ : Representation ℂ G V) (T L : G) (φ₁ φ₂ : V →ₗ[ℂ] ℂ)
    (h₁ : moved ρ T = LinearMap.ker φ₁) (h₂ : moved ρ L = LinearMap.ker φ₂)
    (hT : ∀ v, φ₁ (ρ T v - v) = 0) (hL : ∀ v, φ₂ (ρ L v - v) = 0) :
    LinearMap.ker (cuspFunctional ρ T φ₁ hT) ⊓ LinearMap.ker (cuspFunctional ρ L φ₂ hL) =
      parabolicH1 ρ T L := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e₁ : φ₁ (z.val T) = 0 := hx₁
    have e₂ : φ₂ (z.val L) = 0 := hx₂
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · rw [h₁, LinearMap.mem_ker]
      exact e₁
    · rw [h₂, LinearMap.mem_ker]
      exact e₂
  · rintro _ ⟨z, ⟨hzT, hzL⟩, rfl⟩
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
    rw [h₁, LinearMap.mem_ker] at hzT
    rw [h₂, LinearMap.mem_ker] at hzL
    exact ⟨hzT, hzL⟩

end Abstract

section Concrete

variable (m : ℕ) (e : ℤ)

theorem evalInf_sub (v : Binary.HomogeneousPoly m) :
    SymFixed.evalAt (m := m) ![1, 0] (levelRep m e (upper 1) v - v) = 0 := by
  have h : levelRep m e (upper 1) v - v ∈ moved (levelRep m e) (upper 1) :=
    sub_mem_moved _ _ _
  rw [moved_T_eq (m := m) e] at h
  exact LinearMap.mem_ker.mp h

theorem evalZero_sub (v : Binary.HomogeneousPoly m) :
    SymFixed.evalAt (m := m) ![0, 1] (levelRep m e (lower 1) v - v) = 0 := by
  have h : levelRep m e (lower 1) v - v ∈ moved (levelRep m e) (lower 1) :=
    sub_mem_moved _ _ _
  rw [moved_L_eq (m := m) e] at h
  exact LinearMap.mem_ker.mp h

/-- **The boundary functional at `∞`**: `[z] ↦ z(T)(1, 0)`. -/
def betaInf : CrossedH1 (levelRep m e) →ₗ[ℂ] ℂ :=
  cuspFunctional (levelRep m e) (upper 1) (SymFixed.evalAt (m := m) ![1, 0]) (evalInf_sub m e)

/-- **The boundary functional at `0`**: `[z] ↦ z(L)(0, 1)`. -/
def betaZero : CrossedH1 (levelRep m e) →ₗ[ℂ] ℂ :=
  cuspFunctional (levelRep m e) (lower 1) (SymFixed.evalAt (m := m) ![0, 1]) (evalZero_sub m e)

theorem betaInf_mk (z : crossedCocycles (levelRep m e)) :
    betaInf m e (Submodule.Quotient.mk z) = eval ![1, 0] (z.val (upper 1)).val := rfl

theorem betaZero_mk (z : crossedCocycles (levelRep m e)) :
    betaZero m e (Submodule.Quotient.mk z) = eval ![0, 1] (z.val (lower 1)).val := rfl

/-- **Parabolic classes = common kernel of the two boundary functionals.** -/
theorem ker_betaInf_inf_ker_betaZero :
    LinearMap.ker (betaInf m e) ⊓ LinearMap.ker (betaZero m e) =
      parabolicH1 (levelRep m e) (upper 1) (lower 1) :=
  ker_cuspFunctional_inf (levelRep m e) (upper 1) (lower 1) _ _ (moved_T_eq (m := m) e)
    (moved_L_eq (m := m) e) (evalInf_sub m e) (evalZero_sub m e)

theorem mem_parabolicH1_iff (x : CrossedH1 (levelRep m e)) :
    x ∈ parabolicH1 (levelRep m e) (upper 1) (lower 1) ↔
      betaInf m e x = 0 ∧ betaZero m e x = 0 := by
  rw [← ker_betaInf_inf_ker_betaZero, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]

/-- For `e + m` even the reflection forces the value at `∞` to vanish. -/
theorem betaInf_eq_zero_of_even (even : Even (e + m)) : betaInf m e = 0 :=
  cuspFunctional_eq_zero (levelRep m e) (upper 1) (SymFixed.evalAt (m := m) ![1, 0])
    (evalInf_sub m e) (fun z => cusp_infinity_zero e even z)

/-- For `e` even the reflection forces the value at `0` to vanish. -/
theorem betaZero_eq_zero_of_even (even : Even e) : betaZero m e = 0 :=
  cuspFunctional_eq_zero (levelRep m e) (lower 1) (SymFixed.evalAt (m := m) ![0, 1])
    (evalZero_sub m e) (fun z => cusp_zero_zero e even z)

/-- For `e` even the parabolic classes are exactly the kernel of `β_∞`. -/
theorem parabolicH1_eq_ker_betaInf (even : Even e) :
    parabolicH1 (levelRep m e) (upper 1) (lower 1) = LinearMap.ker (betaInf m e) := by
  rw [← ker_betaInf_inf_ker_betaZero, betaZero_eq_zero_of_even m e even, LinearMap.ker_zero,
    inf_top_eq]

/-- If both parities vanish, every class is parabolic. -/
theorem parabolicH1_eq_top (evenE : Even e) (evenSum : Even (e + m)) :
    parabolicH1 (levelRep m e) (upper 1) (lower 1) = ⊤ := by
  rw [parabolicH1_eq_ker_betaInf m e evenE, betaInf_eq_zero_of_even m e evenSum,
    LinearMap.ker_zero]

end Concrete

end TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryFunctional
