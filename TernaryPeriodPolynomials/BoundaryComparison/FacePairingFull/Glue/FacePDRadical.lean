module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDKoszul
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOddPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgePairing

@[expose] public section


/-!
# The torus-fibre (Koszul) pairing of the radical lattices of the library

Formalized by Claude Sonnet 5.5.

The library's fibre-integration pairing `κ(f, g) = ⟨f ⌣ g, σ⟩` of `U`-equivariant homogeneous one-cocycles of an embedded
radical lattice `U = ⟨u, v⟩ ≅ ℤ²` (`Kostant`: `FiberFormula.kostant`, torus cycle `σ = [u|v] - [v|u]`) is the Koszul pairing
`Phi` of the generator values (`kostant_eq_koszul`).  Hence

* the Koszul pairing of the lattice `latL0` (bad line) and `latL1` (good line) acting on `E` and on `E^φ = E ∘ φ` is perfect on
  `H¹` in both arguments (`latticeKoszul_perfect`; the pairing is the evaluation pairing `dualPairing n`, invariant under the
  level, the evaluation of the cup product on the fundamental class of the torus fibre);
* the library's three Kostant identities read as identities of the Koszul pairing:
  `badLine_koszul_eq_binaryPairing` (`(n+1)!/3`, even `n`), `badLine_koszul_eq_binaryPairing_odd` (`-(n+1)!/3`, odd `n`),
  `goodLine_koszul_eq_binaryPairing` (`-(n+1)!`): the Koszul pairing of the generator values of two equivariant cocycles is a
  nonzero constant times the classical `SL₂`-invariant pairing of their Kostant coordinates in `Sym^{n+1}`.
-/

open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains (cup11)
open TernaryPeriodPolynomials.BoundaryDuality.L2Torus (sigma bar2)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The fibre-integration pairing `κ(f, g) = ⟨f ⌣ g, [u|v] - [v|u]⟩` of the library, on a `U`-equivariant `g`, is the Koszul
cup formula `B (f(1,u)) (ρ'(u) g(1,v)) - B (f(1,v)) (ρ'(v) g(1,u))`. -/
theorem kostant_sigma (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W) (U : Subgroup G) {u v : G}
    (hu : u ∈ U) (hv : v ∈ U) (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W)
    (hg : ∀ γ ∈ U, ∀ a b, g ![γ * a, γ * b] = ρ' γ (g ![a, b])) :
    kostant B (sigma u v) f g =
      B (f ![1, u]) (ρ' u (g ![1, v])) - B (f ![1, v]) (ρ' v (g ![1, u])) := by
  unfold kostant sigma bar2
  rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
  unfold cup11
  have h1 : g ![u, u * v] = ρ' u (g ![1, v]) := by
    simpa using hg u hu 1 v
  have h2 : g ![v, v * u] = ρ' v (g ![1, u]) := by
    simpa using hg v hv 1 u
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h1, h2]

/-- The group element `g` acting on a representation as a linear equivalence. -/
def repEquiv (ρ : Representation ℂ G V) (g : G) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem repEquiv_apply (ρ : Representation ℂ G V) (g : G) (x : V) : repEquiv ρ g x = ρ g x := rfl

/-- The Koszul data of the abelian group `⟨u, v⟩` acting through `ρ` on `V` and `ρ'` on `W`, with an invariant perfect pairing. -/
def koszulOfRep (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (u v : G) (hc : u * v = v * u)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hu : ∀ a b, B (ρ u a) (ρ' u b) = B a b) (hv : ∀ a b, B (ρ v a) (ρ' v b) = B a b)
    (hl : ∀ a, (∀ b, B a b = 0) → a = 0) (hr : ∀ b, (∀ a, B a b = 0) → b = 0) :
    Koszul.KData V W where
  s₁ := repEquiv ρ u
  s₂ := repEquiv ρ v
  t₁ := repEquiv ρ' u
  t₂ := repEquiv ρ' v
  e := B
  comm x := by
    simp only [repEquiv_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc]
  comm' x := by
    simp only [repEquiv_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc]
  inv₁ := hu
  inv₂ := hv
  left := hl
  right := hr

/-- **The library's fibre-integration pairing is the Koszul pairing**: for `U`-equivariant homogeneous one-cocycles `f`
(coefficients `ρ`), `g` (coefficients `ρ'`) of an abelian lattice `⟨u, v⟩ ≤ U`, `κ(f, g) = ⟨f ⌣ g, [u|v] - [v|u]⟩` is the
Koszul pairing `Phi` of the generator values `(f(1,u), f(1,v))`, `(g(1,u), g(1,v))`. -/
theorem kostant_eq_koszul (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (U : Subgroup G) {u v : G}
    (hu : u ∈ U) (hv : v ∈ U) (hc : u * v = v * u) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hBu : ∀ a b, B (ρ u a) (ρ' u b) = B a b) (hBv : ∀ a b, B (ρ v a) (ρ' v b) = B a b)
    (hl : ∀ a, (∀ b, B a b = 0) → a = 0) (hr : ∀ b, (∀ a, B a b = 0) → b = 0)
    (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W)
    (hg : ∀ γ ∈ U, ∀ a b, g ![γ * a, γ * b] = ρ' γ (g ![a, b])) :
    kostant B (sigma u v) f g =
      (koszulOfRep ρ ρ' u v hc B hBu hBv hl hr).Phi (f ![1, u], f ![1, v]) (g ![1, u], g ![1, v]) := by
  rw [kostant_sigma B ρ' U hu hv f g hg]
  rfl

/-- The generator values of a closed `U`-equivariant one-cocycle form a Koszul cocycle. -/
theorem koszul_cocycle_of_ucocycle (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (U : Subgroup G) {u v : G}
    (hu : u ∈ U) (hv : v ∈ U) (hc : u * v = v * u) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hBu : ∀ a b, B (ρ u a) (ρ' u b) = B a b) (hBv : ∀ a b, B (ρ v a) (ρ' v b) = B a b)
    (hl : ∀ a, (∀ b, B a b = 0) → a = 0) (hr : ∀ b, (∀ a, B a b = 0) → b = 0)
    (f : (Fin 2 → G) → V)
    (hf : (∀ γ ∈ U, ∀ a b, f ![γ * a, γ * b] = ρ γ (f ![a, b])) ∧ ∀ x : Fin 3 → G, f ![x 1, x 2] - f ![x 0, x 2] + f ![x 0, x 1] = 0) :
    (koszulOfRep ρ ρ' u v hc B hBu hBv hl hr).d1 (f ![1, u], f ![1, v]) = 0 := by
  have e1 : f ![u, u * v] = ρ u (f ![1, v]) := by simpa using hf.1 u hu 1 v
  have e2 : f ![v, v * u] = ρ v (f ![1, u]) := by simpa using hf.1 v hv 1 u
  have c1 := hf.2 ![1, u, u * v]
  have c2 := hf.2 ![1, v, v * u]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at c1 c2
  rw [e1] at c1
  rw [e2, ← hc] at c2
  show (ρ v (f ![1, u]) - f ![1, u]) - (ρ u (f ![1, v]) - f ![1, v]) = 0
  linear_combination (norm := abel) c2 - c1

end General

section BadLine

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant

theorem homogeneousPoly_finite (n : ℕ) : FiniteDimensional ℂ (HomogeneousPoly n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)

/-- Left nondegeneracy of a bilinear form on a finite-dimensional space gives right nondegeneracy. -/
theorem right_of_left {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hl : ∀ a, (∀ b, B a b = 0) → a = 0) : ∀ b, (∀ a, B a b = 0) → b = 0 := by
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hl v (fun w => by simpa using congrArg (fun f => f w) hv)
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Subspace.dual_finrank_eq])).1 hinj
  have hinj' : Function.Injective B.flip := (LinearMap.flip_injective_iff₂ (B := B)).2 hsurj
  intro b hb
  have : B.flip b = 0 := LinearMap.ext (fun a => by simpa using hb a)
  exact hinj' (this.trans (map_zero _).symm)

theorem latL0_u10_level : latL0.u 1 0 ∈ rationalLevel :=
  (L2Assembly.latL0_le (latL0.u_mem 1 0)).1

theorem latL0_u01_level : latL0.u 0 1 ∈ rationalLevel :=
  (L2Assembly.latL0_le (latL0.u_mem 0 1)).1

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)

/-- **The Koszul data of an embedded radical lattice** `Ω ≤ rationalLevel` (generators `Ω.u 1 0`, `Ω.u 0 1`) acting on the
coefficients `E = Sym^n` by `ρ_χ` and on the `φ`-twisted dual coefficients `E^φ` by `ρ_χ ∘ φ`, with the evaluation pairing
`dualPairing n`. -/
def latticeKoszul (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3) (hΩ : Ω.sub ≤ rationalLevel) :
    Koszul.KData (HomogeneousPoly n) (HomogeneousPoly n) :=
  koszulOfRep (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
    (Ω.u 1 0) (Ω.u 0 1) Ω.commute.eq
    (dualityData n χ).B
    (fun a b => (dualityData n χ).invariant _ (hΩ (Ω.u_mem 1 0)) a b)
    (fun a b => (dualityData n χ).invariant _ (hΩ (Ω.u_mem 0 1)) a b)
    (fun a h => dualPairing_nondegenerate a h)
    (letI := homogeneousPoly_finite n
     right_of_left (dualityData n χ).B (fun a h => dualPairing_nondegenerate a h))

/-- **Perfectness of the torus-fibre (Koszul) pairing of a radical lattice**: `H¹(Ω, E) × H¹(Ω, E^φ) → ℂ`, in both arguments. -/
theorem latticeKoszul_perfect (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3) (hΩ : Ω.sub ≤ rationalLevel) :
    letI := homogeneousPoly_finite n
    (∀ a : (latticeKoszul n χ Ω hΩ).H1, (∀ b : (latticeKoszul n χ Ω hΩ).H1',
        (latticeKoszul n χ Ω hΩ).pairing a b = 0) → a = 0) ∧
    ∀ b : (latticeKoszul n χ Ω hΩ).H1', (∀ a : (latticeKoszul n χ Ω hΩ).H1,
        (latticeKoszul n χ Ω hΩ).pairing a b = 0) → b = 0 :=
  letI := homogeneousPoly_finite n
  ⟨fun a h => (latticeKoszul n χ Ω hΩ).pairing_left_nondegenerate a h,
    fun b h => (latticeKoszul n χ Ω hΩ).pairing_right_nondegenerate b h⟩

theorem latticeKoszul_eq_kostant (n : ℕ) (χ : RankOneCharacter) (Ω : L2Assembly.Lattice RationalGL3) (hΩ : Ω.sub ≤ rationalLevel)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) Ω.sub g) :
    (latticeKoszul n χ Ω hΩ).Phi (f ![1, Ω.u 1 0], f ![1, Ω.u 0 1]) (g ![1, Ω.u 1 0], g ![1, Ω.u 0 1]) =
      kostant (dualityData n χ).B Ω.σ f g :=
  (kostant_eq_koszul (rationalCoefficientComponent n χ) (dualRep (dualityData n χ)) Ω.sub (Ω.u_mem 1 0)
    (Ω.u_mem 0 1) Ω.commute.eq (dualityData n χ).B _ _ (fun a h => dualPairing_nondegenerate a h)
    (letI := homogeneousPoly_finite n
     right_of_left (dualityData n χ).B (fun a h => dualPairing_nondegenerate a h)) f g hg.1).symm

/-- **The Koszul pairing at the bad line, even `n`**: the Koszul pairing of the generator values of `U`-equivariant
cocycles is `(n+1)!/3` times the classical `SL₂`-invariant pairing of their Kostant coordinates. -/
theorem badLine_koszul_eq_binaryPairing (n : ℕ) (positive : 0 < n) (heven : Even n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    (latticeKoszul n trivialCharacter latL0 (fun _ h => (L2Assembly.latL0_le h).1)).Phi
        (f ![1, latL0.u 1 0], f ![1, latL0.u 0 1]) (g ![1, latL0.u 1 0], g ![1, latL0.u 0 1]) =
      (((n + 1).factorial : ℂ) / 3) *
        BinaryPairing.binaryPairing (n + 1) (PhiBad n positive f) (PsiBad n g) :=
  (latticeKoszul_eq_kostant n trivialCharacter latL0 _ hg).trans (kostantBad_eq_binaryPairing n positive heven hf hg)

theorem badLine_koszul_eq_binaryPairing_odd (n : ℕ) (positive : 0 < n) (hodd : Odd n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    (latticeKoszul n trivialCharacter latL0 (fun _ h => (L2Assembly.latL0_le h).1)).Phi
        (f ![1, latL0.u 1 0], f ![1, latL0.u 0 1]) (g ![1, latL0.u 1 0], g ![1, latL0.u 0 1]) =
      (-((n + 1).factorial : ℂ) / 3) *
        BinaryPairing.binaryPairing (n + 1) (PhiBad n positive f) (PsiBad n g) :=
  (latticeKoszul_eq_kostant n trivialCharacter latL0 _ hg).trans (kostantBad_eq_binaryPairing_odd n positive hodd hf hg)

/-- **The Koszul pairing at the good line**: `-(n+1)!` times the invariant pairing of the Kostant coordinates. -/
theorem goodLine_koszul_eq_binaryPairing (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    (latticeKoszul n χ latL1 (fun _ h => (L2Assembly.latL1_le h).1)).Phi
        (f ![1, latL1.u 1 0], f ![1, latL1.u 0 1]) (g ![1, latL1.u 1 0], g ![1, latL1.u 0 1]) =
      (-((n + 1).factorial : ℂ)) *
        BinaryPairing.binaryPairing (n + 1) (PhiTotal n f) (PsiTotal n g) :=
  (latticeKoszul_eq_kostant n χ latL1 _ hg).trans (kostant_eq_binaryPairing n χ positive hf hg)

end BadLine

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD
