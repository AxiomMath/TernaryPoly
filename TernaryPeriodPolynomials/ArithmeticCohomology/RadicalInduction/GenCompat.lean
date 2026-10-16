module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenMu
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.LineSetup

@[expose] public section


/-!
# `Compat` for an arbitrary face group and the stabilizer, at the frame `h u`

Formalized by Claude Sonnet 5.5.

For subgroups `K ≤ Γ(6)`, `K' ≤ Γ(M)` of `SL₃(ℤ)`, `u ∈ Γ(6)` with `u K' u⁻¹ ⊆ K` and `u⁻¹ (K ∩ uΓ(M)u⁻¹) u ⊆ K'`: `muGen` is bijective (`muEquivGen`), the extensions of `S = K ∩ Γ(6)` (transported from
`extK` along `S ≃ K`) and of the stabilizer (transported from `ext'` along `μ`) are compatible (`compat_gen`) provided the matrix identities `u · inl'(r) · u⁻¹ = inl(r^{M/6})`, `u · s'(m) · u⁻¹ = s(m)` hold.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section CompatGen

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem back_mem_gammaN (K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6)) (h6 : 6 ∣ M) (p : ↥K') :
    (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ gammaN 6 :=
  (gammaN 6).mul_mem ((gammaN 6).mul_mem u.2 (gammaN_mono h6 (hK' p.2))) ((gammaN 6).inv_mem u.2)

/-- The inverse of `μ`: `p ↦ u p u⁻¹`. -/
def backGen (K K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
    (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M) (p : ↥K') :
    ↥(StabK (M := M) K u) :=
  ⟨⟨⟨(u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹, back_mem_gammaN K' hK' u h6 p⟩, hback p⟩, by
    refine (mem_stabilizer_quot_iff (Δ6 M) (SK K) u _).mpr ?_
    show (u : SL(3, ℤ))⁻¹ * ((u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹) * (u : SL(3, ℤ)) ∈ gammaN M
    have e : (u : SL(3, ℤ))⁻¹ * ((u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹) * (u : SL(3, ℤ)) = p := by group
    rw [e]; exact hK' p.2⟩

omit [NeZero M] in
theorem muGen_back (K K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
    (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
      (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
    (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M) (p : ↥K') :
    muGen K K' u hmem (backGen K K' hK' u hback h6 p) = p := by
  apply Subtype.ext
  change (u : SL(3, ℤ))⁻¹ * ((u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹) * (u : SL(3, ℤ)) = p
  group

omit [NeZero M] in
theorem muGen_injective (K K' : Subgroup SL(3, ℤ)) (u : ↥(gammaN 6))
    (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
      (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K') :
    Function.Injective (muGen (M := M) K K' u hmem) := by
  intro a b hab
  have h1 := congrArg (fun x : ↥K' => (x : SL(3, ℤ))) hab
  change (u : SL(3, ℤ))⁻¹ * (((a : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ)) =
    (u : SL(3, ℤ))⁻¹ * (((b : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ)) at h1
  have h2 : (((a : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) = (((b : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) := by
    calc (((a : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ))
        = (u : SL(3, ℤ)) * ((u : SL(3, ℤ))⁻¹ * (((a : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ))) * (u : SL(3, ℤ))⁻¹ := by group
      _ = (u : SL(3, ℤ)) * ((u : SL(3, ℤ))⁻¹ * (((b : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) * (u : SL(3, ℤ))) * (u : SL(3, ℤ))⁻¹ := by rw [h1]
      _ = (((b : ↥(SK K)) : ↥(gammaN 6)) : SL(3, ℤ)) := by group
  exact Subtype.ext (Subtype.ext (Subtype.ext h2))

omit [NeZero M] in
theorem muGen_bijective (K K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
    (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
      (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
    (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M) :
    Function.Bijective (muGen (M := M) K K' u hmem) :=
  ⟨muGen_injective K K' u hmem, fun p => ⟨backGen K K' hK' u hback h6 p, muGen_back K K' hK' u hmem hback h6 p⟩⟩

/-- `μ` as an isomorphism. -/
def muEquivGen (K K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
    (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
      (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
    (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M) :
    ↥(StabK (M := M) K u) ≃* ↥K' :=
  MulEquiv.ofBijective (muGen K K' u hmem) (muGen_bijective K K' hK' u hmem hback h6)

omit [NeZero M] in
theorem muEquivGen_symm_val (K K' : Subgroup SL(3, ℤ)) (hK' : K' ≤ gammaN M) (u : ↥(gammaN 6))
    (hmem : ∀ s : ↥(SK K), (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ gammaN M →
      (u : SL(3, ℤ))⁻¹ * (((s : ↥(gammaN 6)) : SL(3, ℤ))) * (u : SL(3, ℤ)) ∈ K')
    (hback : ∀ p : ↥K', (u : SL(3, ℤ)) * (p : SL(3, ℤ)) * (u : SL(3, ℤ))⁻¹ ∈ K) (h6 : 6 ∣ M) (p : ↥K') :
    ((((muEquivGen K K' hK' u hmem hback h6).symm p : ↥(StabK (M := M) K u)) : ↥(SK K)) : ↥(gammaN 6)).1 =
      (u : SL(3, ℤ)) * p.1 * (u : SL(3, ℤ))⁻¹ := by
  have h := congrArg (fun q : ↥K' => q.1) ((muEquivGen K K' hK' u hmem hback h6).apply_symm_apply p)
  change (u : SL(3, ℤ))⁻¹ * ((((muEquivGen K K' hK' u hmem hback h6).symm p : ↥(StabK (M := M) K u)) : ↥(SK K)) : ↥(gammaN 6)).1 *
    (u : SL(3, ℤ)) = p.1 at h
  rw [← h]
  group

end CompatGen

end TernaryPeriodPolynomials.Argument.RadicalInduction
