module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadPairing

@[expose] public section


/-!
# Levi equivariance of the bridge coordinates at the bad line

For `γ ∈ Γ₁'(3)` with Levi image `k = diag(1, γ)` the left action of `k` on the homogeneous
one-cochains is `f ↦ k⁻¹ ⋆ f`.  On a `U`-equivariant one-cocycle of the bad-line lattice it is
computed on the radical by the conjugation formula of `pull1_lattice`; the crossed cocycle of
`k⁻¹ ⋆ f` is the Levi translate of the crossed cocycle of `f` plus a coboundary, so the explicit
coordinate is equivariant for the Levi group (`PhiBad_levi`), through the equivariance of
`explicitRadicalBinaryEquiv`.  On the dual side the level involution acts on the dual radical, in
the frame `badFrame`, through the dual Levi element `σ γ^{-T} σ`; the rotated coordinate
`PsiBad` is equivariant for the same matrices (`PsiBad_levi`), by the intertwining of the exchange
and the rotation of the binary variables.  The Levi cocycles of the fiber data are `U`-equivariant
one-cocycles (`uCocycle_leviCocycle_bad`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle uCocycle_pull1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (cochainRep cochainRep_apply pull1 leviCocycle leviCocycle_equivariant leviCocycle_closed)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### The Levi action on the cochains of the lattice -/

/-- The Levi action on one-cochains preserves the `U`-equivariant one-cocycles of the bad line. -/
theorem uCocycle_cochainRep_badLevi {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {f : (Fin 2 → RationalGL3) → V}
    (hf : UCocycle ρ latL0.sub f) (γ : binaryArithmeticLevel) :
    UCocycle ρ latL0.sub (cochainRep ρ (badLevi γ) f) := by
  rw [cochainRep_apply]
  exact uCocycle_pull1 hf (fun u hu => by simpa only [inv_inv] using badLevi_inv_normalizes γ u hu)

/-- **The Levi cocycles `A(k⁻¹)`, `A'(k⁻¹)` of the fiber data at the bad line are `U`-equivariant
one-cocycles** for every `γ`. -/
theorem uCocycle_leviCocycle_bad {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) (γ : binaryArithmeticLevel) :
    UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub
        (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi γ)⁻¹) ∧
      UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub
        (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹) := by
  have hh : (badLevi γ)⁻¹ ∈ levelStabilizer L₀ := (levelStabilizer L₀).inv_mem (badLevi_mem_level γ)
  have hn : ∀ u ∈ latL0.sub, (badLevi γ)⁻¹ * u * ((badLevi γ)⁻¹)⁻¹ ∈ latL0.sub :=
    fun u hu => by simpa only [inv_inv] using badLevi_inv_normalizes γ u hu
  exact ⟨⟨leviCocycle_equivariant _ hF.omegaU_eq hn,
      leviCocycle_closed _ hF.omegaU_d (hF.zeta_eq _ hh)⟩,
    ⟨leviCocycle_equivariant _ hF.thetaU_eq hn,
      leviCocycle_closed _ hF.thetaU_d (hF.eta_eq _ hh)⟩⟩

/-! ### Levi equivariance of the bad-line coordinate -/

/-- **Levi equivariance of the bad-line coordinate**: for a `U`-equivariant cocycle `f`,
`Φ(k_γ⁻¹ ⋆ f) = γ ⋆ Φ(f)` in `Sym^{n+1}`. -/
theorem PhiBad_levi (n : ℕ) (positive : 0 < n)
    {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (γ : binaryArithmeticLevel) :
    PhiBad n positive (cochainRep (rationalCoefficientComponent n trivialCharacter) (badLevi γ) f) =
      binaryArithmeticRepresentation n γ (PhiBad n positive f) := by
  have hf' := uCocycle_cochainRep_badLevi hf γ
  have key : zBad n hf' =
      leviCrossedAction integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
          ((1 : ℤˣ), γ) (zBad n hf) +
        crossedBoundary ((standardBadLineRepresentation n).comp SemidirectProduct.inl)
          (rationalCoefficientComponent n trivialCharacter (badLevi γ)
            (f ![1, (badLevi γ)⁻¹])) := by
    apply Subtype.ext
    funext r
    have h := pull1_lattice (rationalCoefficientComponent n trivialCharacter) hf (badLevi γ)
      (latL0.hom r) (latL0.hom (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ r))
      ⟨_, rfl⟩ (badLevi_conj γ r)
    show pull1 (rationalCoefficientComponent n trivialCharacter) (badLevi γ)⁻¹ f
        ![1, latL0.hom r] =
      standardBadLineRepresentation n (SemidirectProduct.inr ((1 : ℤˣ), γ))
          (f ![1, latL0.hom (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ r)]) +
        (((standardBadLineRepresentation n).comp SemidirectProduct.inl) r
            (rationalCoefficientComponent n trivialCharacter (badLevi γ)
              (f ![1, (badLevi γ)⁻¹])) -
          rationalCoefficientComponent n trivialCharacter (badLevi γ) (f ![1, (badLevi γ)⁻¹]))
    rw [rhoS_inr, rhoS_radical]
    exact h
  have hmk : ∀ w : crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl),
      (crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
          (w + crossedBoundary ((standardBadLineRepresentation n).comp SemidirectProduct.inl)
            (rationalCoefficientComponent n trivialCharacter (badLevi γ)
              (f ![1, (badLevi γ)⁻¹]))) =
        (crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ w := by
    intro w
    have h0 : (crossedBoundaries ((standardBadLineRepresentation n).comp
        SemidirectProduct.inl)).mkQ
        (crossedBoundary ((standardBadLineRepresentation n).comp SemidirectProduct.inl)
          (rationalCoefficientComponent n trivialCharacter (badLevi γ)
            (f ![1, (badLevi γ)⁻¹]))) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
    rw [map_add, h0, add_zero]
  calc PhiBad n positive
        (cochainRep (rationalCoefficientComponent n trivialCharacter) (badLevi γ) f)
      = explicitRadicalBinaryEquiv n positive
        ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
          (zBad n hf')) := PhiBad_eq n positive hf'
    _ = explicitRadicalBinaryEquiv n positive
        ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
          (leviCrossedAction integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
            ((1 : ℤˣ), γ) (zBad n hf))) := by rw [key, hmk]
    _ = explicitRadicalBinaryEquiv n positive
        (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n) ((1 : ℤˣ), γ)
          ((crossedBoundaries ((standardBadLineRepresentation n).comp
            SemidirectProduct.inl)).mkQ (zBad n hf))) := by
      rw [leviCrossedH1Representation_mk]
    _ = binaryArithmeticRepresentation n γ (PhiBad n positive f) :=
      (explicitRadicalBinaryEquiv_equivariant n positive ((1 : ℤˣ), γ) _).trans
        (congrArg (binaryLeviRepresentation n ((1 : ℤˣ), γ)) (PhiBad_eq n positive hf).symm)

/-! ### The exchange of the variables and the determinant twists -/

/-- The action `Sym^d ⊗ det^τ` is the determinant power times the untwisted action. -/
theorem homogeneousAction_zpow_twist (d : ℕ) (τ : ℤ) (A : Binary.GL2) :
    Binary.homogeneousAction d τ A =
      (((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ τ) • Binary.homogeneousAction d 0 A := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, LinearMap.smul_apply, Submodule.coe_smul,
    Binary.homogeneousAction_coe, Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ τ =
    ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ τ * ((GeneralLinearGroup.det A : ℂˣ) : ℂ) ^ (0 : ℤ)
  rw [zpow_zero, mul_one]

/-- The exchange intertwines the twisted actions of `γ` and of its conjugate. -/
theorem binarySwapVar_action_twist (N : ℕ) (τ : ℤ) (γ : Binary.GL2)
    (f : Binary.HomogeneousPoly N) :
    binarySwapVar N (Binary.homogeneousAction N τ γ f) =
      Binary.homogeneousAction N τ (swapUnit * γ * swapUnit⁻¹) (binarySwapVar N f) := by
  have hdet : GeneralLinearGroup.det (swapUnit * γ * swapUnit⁻¹) = GeneralLinearGroup.det γ := by
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det swapUnit)
      (GeneralLinearGroup.det γ), mul_assoc, mul_inv_cancel, mul_one]
  rw [homogeneousAction_zpow_twist N τ γ, homogeneousAction_zpow_twist N τ
    (swapUnit * γ * swapUnit⁻¹), hdet]
  simp only [LinearMap.smul_apply]
  rw [map_smul, binarySwapVar_action]

theorem swap_conj_conj (g : Binary.GL2) : swapUnit * (swapUnit * g * swapUnit⁻¹) * swapUnit⁻¹ = g := by
  have hinv : swapUnit⁻¹ = swapUnit := inv_eq_of_mul_eq_one_right swapUnit_mul_self
  rw [hinv]
  calc swapUnit * (swapUnit * g * swapUnit) * swapUnit = (swapUnit * swapUnit) * g *
        (swapUnit * swapUnit) := by simp only [mul_assoc]
    _ = g := by rw [swapUnit_mul_self, one_mul, mul_one]

/-! ### Levi equivariance of the rotated dual coordinate -/

theorem rho_frame_inv_levi (n : ℕ) (γ : binaryArithmeticLevel) (y : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter badFrame⁻¹
        (dualRep (dualityData n trivialCharacter) (badLevi γ) y) =
      arithmeticLeviCoefficient n (badDualLevi γ)
        (rationalCoefficientComponent n trivialCharacter badFrame⁻¹ y) := by
  have h1 := congrArg (fun x : RationalGL3 => rationalCoefficientComponent n trivialCharacter x y)
    (eq_mul_inv_of_mul_eq (badFrame_conj_levi γ))
  simp only [map_mul, Module.End.mul_apply] at h1
  exact h1

/-- **Levi equivariance of the rotated dual coordinate, for the raw twist**: for a
`U`-equivariant cocycle `g` for the dual coefficients,
`Ψ(k_γ⁻¹ ⋆ g) = γ ⋆_{n+2} Ψ(g)` in `Sym^{n+1} ⊗ det^{n+2}`, for every `n`. -/
theorem PsiBad_levi_raw (n : ℕ)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g)
    (γ : binaryArithmeticLevel) :
    PsiBad n (cochainRep (dualRep (dualityData n trivialCharacter)) (badLevi γ) g) =
      Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
        (binaryIntegralComplex γ.1) (PsiBad n g) := by
  have hg' := uCocycle_cochainRep_badLevi hg γ
  have key : ∀ p, wBad n hg' p =
      (upperRadicalCocycleLevi n (badDualLevi γ) (wBad n hg)) p +
        ((upperRadicalLatticeRep n).ρ p
            (asUp n (rationalCoefficientComponent n trivialCharacter badFrame⁻¹
              (dualRep (dualityData n trivialCharacter) (badLevi γ) (g ![1, (badLevi γ)⁻¹])))) -
          asUp n (rationalCoefficientComponent n trivialCharacter badFrame⁻¹
            (dualRep (dualityData n trivialCharacter) (badLevi γ) (g ![1, (badLevi γ)⁻¹])))) := by
    intro p
    have h := pull1_lattice (dualRep (dualityData n trivialCharacter)) hg (badLevi γ)
      (latL0.hom (swapNegHom p))
      (latL0.hom (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ (swapNegHom p)))
      ⟨_, rfl⟩ (badLevi_conj γ (swapNegHom p))
    rw [conjAct_swapNeg] at h
    show rationalCoefficientComponent n trivialCharacter badFrame⁻¹
        (pull1 (dualRep (dualityData n trivialCharacter)) (badLevi γ)⁻¹ g
          ![1, latL0.hom (swapNegHom p)]) = _
    have t1 := rho_frame_inv_levi n γ
      (g ![1, latL0.hom (swapNegHom (upperLeviLatticeInput (badDualLevi γ) p))])
    rw [h, map_add, map_sub, rho_frame_inv_dual, t1]
    rfl
  have hup : upperRadicalCocycleCoordinate n (wBad n hg') =
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ))
        (upperRadicalCocycleCoordinate n (wBad n hg)) := by
    rw [coord_upper_eq_of_shift n _ _ _ key, upperRadicalCocycleCoordinate_equivariant]
  have hmat : ((swapUnit * binaryIntegralComplex γ.1 * swapUnit⁻¹ : Binary.GL2) :
      Matrix (Fin 2) (Fin 2) ℂ) *
      ((GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ) : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 :=
    levi_relation_complex γ.1 (badDualLevi γ) (badDualLevi_relation γ)
  simp only [PsiBad, LinearMap.comp_apply]
  rw [upperTotalBad_eq n hg', upperTotalBad_eq n hg, hup,
    binarySwap_homogeneousAction (n + 1) (-1) (swapUnit * binaryIntegralComplex γ.1 * swapUnit⁻¹)
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ)) hmat,
    binarySwapVar_action_twist, swap_conj_conj]

/-- **Levi equivariance of the rotated dual coordinate**: for a `U`-equivariant cocycle `g` for
the dual coefficients, `Ψ(k_γ⁻¹ ⋆ g) = γ ⋆ Ψ(g)` in `Sym^{n+1}`, for even `n`. -/
theorem PsiBad_levi (n : ℕ) (heven : Even n)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g)
    (γ : binaryArithmeticLevel) :
    PsiBad n (cochainRep (dualRep (dualityData n trivialCharacter)) (badLevi γ) g) =
      binaryArithmeticRepresentation n γ (PsiBad n g) := by
  have hEven : Even (((n + 1 : ℕ) : ℤ) - (-1) - 0) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨(k : ℤ) + 1, by omega⟩
  rw [PsiBad_levi_raw n hg γ]
  exact LinearMap.congr_fun (homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1)) 0
    hEven γ.1) _

/-- **Levi equivariance of the rotated dual coordinate for odd `n`**: the module is
`Sym^{n+1} ⊗ det⁻¹`, `Ψ(k_γ⁻¹ ⋆ g) = γ ⋆_{-1} Ψ(g)`. -/
theorem PsiBad_levi_odd (n : ℕ) (hodd : Odd n)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g)
    (γ : binaryArithmeticLevel) :
    PsiBad n (cochainRep (dualRep (dualityData n trivialCharacter)) (badLevi γ) g) =
      levelRep (n + 1) (-1) γ (PsiBad n g) := by
  have hEven : Even (((n + 1 : ℕ) : ℤ) - (-1) - (-1)) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨(k : ℤ) + 2, by omega⟩
  rw [PsiBad_levi_raw n hg γ]
  exact LinearMap.congr_fun (homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1)) (-1)
    hEven γ.1) _

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
