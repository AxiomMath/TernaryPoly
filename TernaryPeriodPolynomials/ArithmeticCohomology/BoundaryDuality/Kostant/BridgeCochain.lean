module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBasic

@[expose] public section


/-!
# From homogeneous `U`-cocycles to the Kostant coordinates at the good line

A `U`-equivariant homogeneous one-cocycle `f` with vertices in `GL₃(ℚ)` (`U = latL1` the radical
lattice of the good line) is determined on `U` by the inhomogeneous cocycle
`p ↦ f(1, u(p))` of the radical lattice (`zCoc`).  For the dual coefficients `ρ ∘ φ` the
inversion `p ↦ g(1, u(p)⁻¹)` of the inhomogeneous cocycle is a cocycle of the identity-plane radical
(`wCoc`): the level involution carries `u(p)` to the inverse of the identity-plane radical element
`p`.  The coordinates `PhiTotal` (good-line coordinate in `Sym^{n+1}`) and `PsiTotal` (the rotated
identity-plane coordinate) are linear maps on all one-cochains.

The Kostant pairing of the fiber integration, `κ(f, g) = ⟨f ⌣ g, σ⟩`, is computed in these
coordinates (`kostant_eq_neg_binaryPairing`):

  `κ(f, g) = −(n+1)! · ⟨Φ f, Ψ g⟩`    (`⟨ , ⟩ = binaryPairing (n+1)`),

the minus sign being the sign of the cup product of the standard torus cycle against the pairing of
the adjoint Kostant form `kostantValue`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL)

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle uCocycle_pull1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (cochainRep cochainRep_apply cup11 rep_mul_apply')
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

variable {n : ℕ} {χ : RankOneCharacter}

/-! ### Closed one-cochains: elementary lemmas -/

theorem eq_of_closed {V : Type} [AddCommGroup V] {X A B : V} (c : A - X + B = 0) :
    X = A + B := by
  have h : X - (A + B) = -(A - X + B) := by abel
  rw [c, neg_zero] at h
  exact sub_eq_zero.mp h

theorem eq_sub_of_closed {V : Type} [AddCommGroup V] {A X C : V} (c : A - X + C = 0) :
    A = X - C := by
  have h : A - (X - C) = A - X + C := by abel
  rw [c] at h
  exact sub_eq_zero.mp h

/-- The inhomogeneous cocycle law of a `U`-equivariant homogeneous cocycle on the radical
lattice. -/
theorem uCocycle_law {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {f : (Fin 2 → RationalGL3) → V}
    (hf : UCocycle ρ latL1.sub f) (p q : RadicalLattice) :
    f ![1, lowerRadicalLattice (p * q)] =
      ρ (lowerRadicalLattice p) (f ![1, lowerRadicalLattice q]) +
        f ![1, lowerRadicalLattice p] := by
  have c := hf.2 ![1, lowerRadicalLattice p, lowerRadicalLattice p * lowerRadicalLattice q]
  have e := hf.1 (lowerRadicalLattice p) (lower_mem_sub p) 1 (lowerRadicalLattice q)
  rw [mul_one] at e
  change f ![lowerRadicalLattice p, lowerRadicalLattice p * lowerRadicalLattice q] -
    f ![1, lowerRadicalLattice p * lowerRadicalLattice q] + f ![1, lowerRadicalLattice p] = 0
    at c
  rw [e] at c
  rw [map_mul]
  exact eq_of_closed c

/-- The value at the identity of a `U`-equivariant homogeneous cocycle vanishes. -/
theorem uCocycle_one {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {f : (Fin 2 → RationalGL3) → V}
    (hf : UCocycle ρ latL1.sub f) : f ![1, 1] = 0 := by
  have h := uCocycle_law hf 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  exact add_eq_left.mp h.symm

/-- **The inhomogeneous cocycle of the good-line radical** attached to a `U`-equivariant
homogeneous cocycle. -/
def zCoc (n : ℕ) (χ : RankOneCharacter) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  ⟨fun p => f ![1, lowerRadicalLattice p], (groupCohomology.mem_cocycles₁_iff _).mpr
    (fun p q => by
      have h := uCocycle_law hf p q
      rw [rho_lower_eq n χ p] at h
      exact h)⟩

/-- **The inhomogeneous cocycle of the identity-plane radical** attached to a `U`-equivariant
cocycle for the dual coefficients: `p ↦ g(1, u(p)⁻¹)`. -/
def wCoc (n : ℕ) (χ : RankOneCharacter) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  ⟨fun p => g ![1, lowerRadicalLattice p⁻¹], (groupCohomology.mem_cocycles₁_iff _).mpr
    (fun p q => by
      have h := uCocycle_law hg p⁻¹ q⁻¹
      have e : dualRep (dualityData n χ) (lowerRadicalLattice p⁻¹) =
          (upperRadicalLatticeRep n).ρ p := by
        change rationalCoefficientComponent n χ (dualInvolution (lowerRadicalLattice p⁻¹)) = _
        rw [rho_dual_lower_eq, inv_inv]
      rw [e, ← mul_inv] at h
      exact h)⟩

theorem zCoc_apply (n : ℕ) (χ : RankOneCharacter) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f) (p : RadicalLattice) :
    zCoc n χ hf p = f ![1, lowerRadicalLattice p] := rfl

theorem wCoc_apply (n : ℕ) (χ : RankOneCharacter) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) (p : RadicalLattice) :
    wCoc n χ hg p = g ![1, lowerRadicalLattice p⁻¹] := rfl

/-! ### The total coordinates -/

/-- **The good-line coordinate** on all homogeneous one-cochains: it only reads the values at
`(1, u(e₁))` and `(1, u(e₂))`. -/
def PhiTotal (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (lowerRadicalCoordinate n).comp
    (LinearMap.pi fun i : Fin 2 =>
      ((lowerRadicalAverageEquiv n i).symm : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n).comp
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 → RationalGL3 => HomogeneousPoly n)
          (![1, lowerRadicalLattice (radicalLatticeGenerator i)] : Fin 2 → RationalGL3)))

/-- **The identity-plane coordinate** (before the rotation) on all homogeneous one-cochains. -/
def upperTotal (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (planeRadicalCoordinate n).comp
    (LinearMap.pi fun i : Fin 2 =>
      ((upperRadicalAverageEquiv n i).symm : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n).comp
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 → RationalGL3 => HomogeneousPoly n)
          (![1, lowerRadicalLattice (radicalLatticeGenerator i)⁻¹] : Fin 2 → RationalGL3)))

/-- **The rotated identity-plane coordinate**, on which the Levi group acts through the same
matrices as on the good-line coordinate. -/
def PsiTotal (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (binarySwap (n + 1)).comp (upperTotal n)

theorem PhiTotal_eq (n : ℕ) (χ : RankOneCharacter)
    {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f) :
    PhiTotal n f = lowerRadicalCocycleCoordinate n (zCoc n χ hf) := rfl

theorem upperTotal_eq (n : ℕ) (χ : RankOneCharacter)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    upperTotal n g = upperRadicalCocycleCoordinate n (wCoc n χ hg) := rfl

/-! ### The Kostant pairing of homogeneous cochains -/

/-- The Kostant pairing of the lattice `latL1` on the two generators. -/
theorem kostant_latL1 {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (f : (Fin 2 → RationalGL3) → V) (g : (Fin 2 → RationalGL3) → W) :
    kostant B latL1.σ f g =
      B (f ![1, lowerRadicalLattice radicalLatticeFirst])
          (g ![lowerRadicalLattice radicalLatticeFirst,
            lowerRadicalLattice radicalLatticeFirst * lowerRadicalLattice radicalLatticeSecond]) -
        B (f ![1, lowerRadicalLattice radicalLatticeSecond])
          (g ![lowerRadicalLattice radicalLatticeSecond,
            lowerRadicalLattice radicalLatticeSecond * lowerRadicalLattice radicalLatticeFirst]) := by
  have h1 : latL1.u 1 0 = lowerRadicalLattice radicalLatticeFirst := uL1_eq 1 0
  have h2 : latL1.u 0 1 = lowerRadicalLattice radicalLatticeSecond := uL1_eq 0 1
  have hσ : latL1.σ = L2Torus.sigma (lowerRadicalLattice radicalLatticeFirst)
      (lowerRadicalLattice radicalLatticeSecond) := by
    change L2Torus.sigma (latL1.u 1 0) (latL1.u 0 1) = _
    rw [h1, h2]
  unfold kostant
  rw [hσ, L2Torus.sigma, L2Torus.bar2, L2Torus.bar2, map_sub, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, one_smul, one_smul]
  rfl

/-- **Closed-form of the Kostant pairing** of a `U`-equivariant cocycle with a `U`-equivariant
cocycle of the dual coefficients, on the generator values. -/
theorem kostant_generators (n : ℕ) (χ : RankOneCharacter)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (_hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) :
    kostant (dualPairing n) latL1.σ f g =
      dualPairing n (f ![1, lowerRadicalLattice radicalLatticeFirst])
          ((upperRadicalLatticeRep n).ρ radicalLatticeFirst⁻¹
            (g ![1, lowerRadicalLattice radicalLatticeSecond])) -
        dualPairing n (f ![1, lowerRadicalLattice radicalLatticeSecond])
          ((upperRadicalLatticeRep n).ρ radicalLatticeSecond⁻¹
            (g ![1, lowerRadicalLattice radicalLatticeFirst])) := by
  have ea := hg.1 (lowerRadicalLattice radicalLatticeFirst) (lower_mem_sub _) 1
    (lowerRadicalLattice radicalLatticeSecond)
  have eb := hg.1 (lowerRadicalLattice radicalLatticeSecond) (lower_mem_sub _) 1
    (lowerRadicalLattice radicalLatticeFirst)
  rw [mul_one] at ea eb
  have da : dualRep (dualityData n χ) (lowerRadicalLattice radicalLatticeFirst) =
      (upperRadicalLatticeRep n).ρ radicalLatticeFirst⁻¹ :=
    rho_dual_lower_eq n χ radicalLatticeFirst
  have db : dualRep (dualityData n χ) (lowerRadicalLattice radicalLatticeSecond) =
      (upperRadicalLatticeRep n).ρ radicalLatticeSecond⁻¹ :=
    rho_dual_lower_eq n χ radicalLatticeSecond
  rw [kostant_latL1, ea, eb, da, db]
  rfl

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
