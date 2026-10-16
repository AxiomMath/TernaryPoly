module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadBasic

@[expose] public section


/-!
# From homogeneous `U`-cocycles to the Kostant coordinates at the bad line

A `U`-equivariant homogeneous one-cocycle `f` with vertices in `GL₃(ℚ)` (`U = latL0` the radical
lattice of the bad line) is determined on `U` by the inhomogeneous crossed cocycle
`r ↦ f(1, u(r))` of the radical (`zBad`).  For the dual coefficients `ρ ∘ φ`, the level involution
carries `u(r)` to a conjugate of the upper plane radical element `p`, `r = (-p₂, -p₁)`, in the frame
`badFrame`; the formula `p ↦ ρ(badFrame)⁻¹ g(1, u(-p₂, -p₁))` is a cocycle of the upper plane radical
(`wBad`).  The coordinate `PhiBad` (the explicit binary coordinate of the radical cohomology of the
bad line) is a linear map on all pairs of values, extended from the cycles by a linear complement,
and `upperTotalBad` is the coordinate of the cocycle `wBad` as a linear map on all one-cochains.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### Cocycle laws on a lattice -/

/-- The inhomogeneous cocycle law of a `U`-equivariant homogeneous cocycle at an element of `U`. -/
theorem uCocycle_mul_gen {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {U : Subgroup RationalGL3}
    {f : (Fin 2 → RationalGL3) → V} (hf : UCocycle ρ U f) {a : RationalGL3} (ha : a ∈ U)
    (b : RationalGL3) :
    f ![1, a * b] = ρ a (f ![1, b]) + f ![1, a] := by
  have c := hf.2 ![1, a, a * b]
  have e := hf.1 a ha 1 b
  rw [mul_one] at e
  change f ![a, a * b] - f ![1, a * b] + f ![1, a] = 0 at c
  rw [e] at c
  exact eq_of_closed c

/-- The value at the identity of a `U`-equivariant homogeneous cocycle vanishes. -/
theorem uCocycle_one_gen {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {U : Subgroup RationalGL3}
    {f : (Fin 2 → RationalGL3) → V} (hf : UCocycle ρ U f) : f ![1, 1] = 0 := by
  have h := uCocycle_mul_gen hf U.one_mem 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  exact add_eq_left.mp h.symm

/-- The value at the inverse of an element of `U`. -/
theorem uCocycle_inv_gen {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {U : Subgroup RationalGL3}
    {f : (Fin 2 → RationalGL3) → V} (hf : UCocycle ρ U f) {a : RationalGL3} (ha : a ∈ U) :
    f ![1, a⁻¹] = -ρ a⁻¹ (f ![1, a]) := by
  have h := uCocycle_mul_gen hf (U.inv_mem ha) a
  rw [inv_mul_cancel, uCocycle_one_gen hf] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The Kostant pairing of a lattice on the two generators. -/
theorem kostant_lattice (Ω : L2Assembly.Lattice RationalGL3) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (f : (Fin 2 → RationalGL3) → V) (g : (Fin 2 → RationalGL3) → W) :
    kostant B Ω.σ f g =
      B (f ![1, Ω.u 1 0]) (g ![Ω.u 1 0, Ω.u 1 0 * Ω.u 0 1]) -
        B (f ![1, Ω.u 0 1]) (g ![Ω.u 0 1, Ω.u 0 1 * Ω.u 1 0]) := by
  unfold kostant
  rw [show Ω.σ = L2Torus.sigma (Ω.u 1 0) (Ω.u 0 1) from rfl, L2Torus.sigma, L2Torus.bar2,
    L2Torus.bar2, map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
    one_smul, one_smul]
  rfl

/-! ### The crossed cocycle of the radical -/

/-- The radical representation of the semidirect model on the radical. -/
theorem rhoS_radical (n : ℕ) (r : Multiplicative (ℤ × ℤ)) :
    ((standardBadLineRepresentation n).comp SemidirectProduct.inl) r =
      rationalCoefficientComponent n trivialCharacter (latL0.hom r) := by
  rw [standardBadLineRepresentation_radical n, latL0_hom_eq]
  rfl

/-- The representation of the semidirect model at a Levi element. -/
theorem rhoS_inr (n : ℕ) (γ : binaryArithmeticLevel) :
    standardBadLineRepresentation n (SemidirectProduct.inr ((1 : ℤˣ), γ)) =
      rationalCoefficientComponent n trivialCharacter (badLevi γ) := by
  change rationalCoefficientComponent n trivialCharacter
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr ((1 : ℤˣ), γ))).val = _
  rw [equiv_inr_val]

/-- **The inhomogeneous crossed cocycle of the bad-line radical** attached to a `U`-equivariant
homogeneous cocycle. -/
def zBad (n : ℕ) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f) :
    crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl) :=
  ⟨fun r => f ![1, latL0.hom r], by
    intro a b
    have h := uCocycle_mul_gen hf (show latL0.hom a ∈ latL0.sub from ⟨a, rfl⟩) (latL0.hom b)
    rw [← map_mul] at h
    show f ![1, latL0.hom (a * b)] = f ![1, latL0.hom a] +
      ((standardBadLineRepresentation n).comp SemidirectProduct.inl) a (f ![1, latL0.hom b])
    rw [h, rhoS_radical]
    exact add_comm _ _⟩

theorem zBad_apply (n : ℕ) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (r : Multiplicative (ℤ × ℤ)) : (zBad n hf).val r = f ![1, latL0.hom r] := rfl

/-! ### The cocycle of the dual plane radical -/

/-- The frame conjugation in the form used for the cocycle law. -/
theorem badFrame_conj' (p : RadicalLattice) :
    badFrame⁻¹ * dualInvolution (latL0.hom (swapNegHom p)) = upperRadicalLattice p * badFrame⁻¹ :=
  eq_mul_inv_of_mul_eq (badFrame_conj p)

/-- The frame intertwines the dual action at the lattice with the upper plane radical. -/
theorem rho_frame_inv_dual (n : ℕ) (p : RadicalLattice) (y : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter badFrame⁻¹
        (dualRep (dualityData n trivialCharacter) (latL0.hom (swapNegHom p)) y) =
      (upperRadicalLatticeRep n).ρ p
        (rationalCoefficientComponent n trivialCharacter badFrame⁻¹ y) := by
  have h1 := congrArg (fun x : RationalGL3 => rationalCoefficientComponent n trivialCharacter x y)
    (badFrame_conj' p)
  simp only [map_mul, Module.End.mul_apply] at h1
  exact h1

/-- **The cocycle of the upper plane radical** attached to a `U`-equivariant cocycle for the dual
coefficients: `p ↦ ρ(badFrame)⁻¹ g(1, u(-p₂, -p₁))`. -/
def wBad (n : ℕ) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  ⟨fun p => rationalCoefficientComponent n trivialCharacter badFrame⁻¹
      (g ![1, latL0.hom (swapNegHom p)]),
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun p q => by
      have h := uCocycle_mul_gen hg
        (show latL0.hom (swapNegHom p) ∈ latL0.sub from ⟨_, rfl⟩) (latL0.hom (swapNegHom q))
      rw [← map_mul, ← map_mul] at h
      show rationalCoefficientComponent n trivialCharacter badFrame⁻¹
          (g ![1, latL0.hom (swapNegHom (p * q))]) =
        (upperRadicalLatticeRep n).ρ p (rationalCoefficientComponent n trivialCharacter badFrame⁻¹
          (g ![1, latL0.hom (swapNegHom q)])) +
          asUp n (rationalCoefficientComponent n trivialCharacter badFrame⁻¹
            (g ![1, latL0.hom (swapNegHom p)]))
      rw [h, map_add, rho_frame_inv_dual]
      rfl)⟩

theorem wBad_apply (n : ℕ) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) (p : RadicalLattice) :
    wBad n hg p = rationalCoefficientComponent n trivialCharacter badFrame⁻¹
      (g ![1, latL0.hom (swapNegHom p)]) := rfl

/-! ### The total coordinates -/

/-- The pair of values of a one-cochain at the two generators of the radical. -/
def badPairs (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] (HomogeneousPoly n × HomogeneousPoly n) :=
  LinearMap.prod
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 → RationalGL3 => HomogeneousPoly n)
      (![1, latL0.hom (integralRadicalGenerator 0)] : Fin 2 → RationalGL3))
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 → RationalGL3 => HomogeneousPoly n)
      (![1, latL0.hom (integralRadicalGenerator 1)] : Fin 2 → RationalGL3))

/-- A linear extension of the binary coordinate of the discrete radical cohomology from the cycles
to all pairs. -/
def badExtend (n : ℕ) (positive : 0 < n) :
    (HomogeneousPoly n × HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (LinearMap.exists_extend ((discreteRadicalBinaryEquiv n positive).toLinearMap.comp
    (discreteRadicalBoundaries n positive).mkQ)).choose

theorem badExtend_spec (n : ℕ) (positive : 0 < n) (c : discreteRadicalCycles n) :
    badExtend n positive c.val =
      discreteRadicalBinaryEquiv n positive ((discreteRadicalBoundaries n positive).mkQ c) :=
  LinearMap.congr_fun (LinearMap.exists_extend ((discreteRadicalBinaryEquiv n positive).toLinearMap.comp
    (discreteRadicalBoundaries n positive).mkQ)).choose_spec c

/-- **The bad-line coordinate** on all homogeneous one-cochains: it only reads the values at
`(1, u(e₁))` and `(1, u(e₂))`. -/
def PhiBad (n : ℕ) (positive : 0 < n) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (badExtend n positive).comp (badPairs n)

/-- On a `U`-equivariant cocycle the bad-line coordinate is the explicit coordinate of the class of
the inhomogeneous crossed cocycle. -/
theorem PhiBad_eq (n : ℕ) (positive : 0 < n) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f) :
    PhiBad n positive f = explicitRadicalBinaryEquiv n positive
      ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (zBad n hf)) := by
  have e1 : badPairs n f =
      (radicalCrossedEvaluation n (standardRadicalCocycleEquiv n (zBad n hf))).val := rfl
  change badExtend n positive (badPairs n f) = _
  rw [e1, badExtend_spec]
  rfl

/-- **The coordinate of the dual cocycle** as a linear map on all one-cochains. -/
def upperTotalBad (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (planeRadicalCoordinate n).comp
    (LinearMap.pi fun i : Fin 2 =>
      ((upperRadicalAverageEquiv n i).symm : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n).comp
        ((rationalCoefficientComponent n trivialCharacter badFrame⁻¹).comp
          (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 → RationalGL3 => HomogeneousPoly n)
            (![1, latL0.hom (swapNegHom (radicalLatticeGenerator i))] : Fin 2 → RationalGL3))))

theorem upperTotalBad_eq (n : ℕ) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    upperTotalBad n g = upperRadicalCocycleCoordinate n (wBad n hg) := rfl

/-- **The rotated coordinate of the dual cocycle**, in which the Levi group acts through the same
matrices as on the bad-line coordinate. -/
def PsiBad (n : ℕ) :
    ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (binarySwapVar (n + 1)).comp ((binarySwap (n + 1)).comp (upperTotalBad n))

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
