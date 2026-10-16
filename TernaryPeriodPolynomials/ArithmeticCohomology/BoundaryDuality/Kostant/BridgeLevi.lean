module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CocycleShift

@[expose] public section


/-!
# Levi equivariance of the bridge coordinates at the good line

For `γ ∈ GL₂(ℤ)` with Levi image `k = diag(γ, 1)` the left action of `k` on the homogeneous
one-cochains is `f ↦ k⁻¹ ⋆ f`.  On a `U`-equivariant one-cocycle `f` of the good-line lattice `U`
it is computed on the lattice by the conjugation formula

  `(k⁻¹ ⋆ f)(1, u) = ρ(k) f(1, u') + (ρ(u) − 1) ρ(k) f(1, k⁻¹)`,   `u k = k u'`,

so the class of the inhomogeneous cocycle of `k⁻¹ ⋆ f` is the Levi translate of the class of `f`
(`Phi_levi`): the coordinate `PhiTotal` is equivariant for `Sym^{n+1}` twisted by the determinant
sign `detSign χ (diag(γ, 1))` of the coefficients.  The same computation at the identity-plane
radical, where the level involution replaces `γ` by its inverse transpose, gives the equivariance of
the rotated coordinate `PsiTotal` (`Psi_levi`).  The Levi cocycles `A(k⁻¹) = k⁻¹ ⋆ ω_U − ω_U` are
`U`-equivariant one-cocycles for every `γ ∈ GL₂(ℤ)`, also those of determinant `-1`
(`uCocycle_leviCocycle_hom`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL)

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle uCocycle_pull1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (cochainRep cochainRep_apply pull1 leviCocycle leviCocycle_mul leviCocycle_equivariant
    leviCocycle_closed)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### The Levi action on the cochains of the lattice -/

/-- The Levi action on one-cochains preserves the `U`-equivariant one-cocycles. -/
theorem uCocycle_cochainRep_levi {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {f : (Fin 2 → RationalGL3) → V}
    (hf : UCocycle ρ latL1.sub f) (γ : GL2Z) :
    UCocycle ρ latL1.sub (cochainRep ρ (leviHom γ) f) := by
  rw [cochainRep_apply]
  exact uCocycle_pull1 hf (fun u hu => by simpa only [inv_inv] using levi_inv_normalizes γ u hu)

/-- **The conjugation formula**: for `u k = k u''` with `u''` in the lattice,
`(k⁻¹ ⋆ f)(1, u) = ρ(k) f(1, u'') + (ρ(u) − 1) ρ(k) f(1, k⁻¹)`. -/
theorem pull1_lattice {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) {U : Subgroup RationalGL3}
    {f : (Fin 2 → RationalGL3) → V}
    (hf : UCocycle ρ U f) (k u u'' : RationalGL3) (hu'' : u'' ∈ U)
    (hconj : u * k = k * u'') :
    pull1 ρ k⁻¹ f ![1, u] =
      ρ k (f ![1, u'']) + (ρ u (ρ k (f ![1, k⁻¹])) - ρ k (f ![1, k⁻¹])) := by
  have h1 : k⁻¹ * u = u'' * k⁻¹ := by
    calc k⁻¹ * u = k⁻¹ * (u * k) * k⁻¹ := by group
      _ = u'' * k⁻¹ := by rw [hconj]; group
  have c1 := hf.2 ![1, k⁻¹, k⁻¹ * u]
  have c2 := hf.2 ![1, u'', u'' * k⁻¹]
  have e := hf.1 u'' hu'' 1 k⁻¹
  rw [mul_one] at e
  change f ![k⁻¹, k⁻¹ * u] - f ![1, k⁻¹ * u] + f ![1, k⁻¹] = 0 at c1
  change f ![u'', u'' * k⁻¹] - f ![1, u'' * k⁻¹] + f ![1, u''] = 0 at c2
  rw [e] at c2
  have s1 := eq_sub_of_closed c1
  have s2 := eq_of_closed c2
  have hρ : ρ k (ρ u'' (f ![1, k⁻¹])) = ρ u (ρ k (f ![1, k⁻¹])) := by
    have h := congrArg (fun A : Module.End ℂ V => A (f ![1, k⁻¹])) (congrArg ρ hconj)
    simpa only [map_mul, Module.End.mul_apply] using h.symm
  change ρ k⁻¹⁻¹ (f ![k⁻¹ * 1, k⁻¹ * u]) = _
  rw [inv_inv, mul_one, s1, h1, s2]
  simp only [map_sub, map_add]
  rw [hρ]
  abel

/-! ### Class-level facts about the radical coordinates -/

/-- Two good-line cocycles differing by a coboundary have the same coordinate. -/
theorem coord_lower_eq_of_shift (n : ℕ) (positive : 0 < n)
    (z z0 : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) (v : lowerRadicalLatticeRep n)
    (h : ∀ p, z p = z0 p + ((lowerRadicalLatticeRep n).ρ p v - v)) :
    lowerRadicalCocycleCoordinate n z = lowerRadicalCocycleCoordinate n z0 := by
  rw [lowerRadicalCocycleCoordinate_eq_iff positive]
  have e : z = shiftCocycle (lowerRadicalLatticeRep n) z0 (-v) := by
    apply groupCohomology.cocycles₁_ext
    intro p
    rw [shiftCocycle_apply, h p, map_neg]
    abel
  rw [e, shiftCocycle_H1]

/-- Two identity-plane cocycles differing by a coboundary have the same coordinate. -/
theorem coord_upper_eq_of_shift (n : ℕ)
    (z z0 : groupCohomology.cocycles₁ (upperRadicalLatticeRep n)) (v : upperRadicalLatticeRep n)
    (h : ∀ p, z p = z0 p + ((upperRadicalLatticeRep n).ρ p v - v)) :
    upperRadicalCocycleCoordinate n z = upperRadicalCocycleCoordinate n z0 := by
  rw [upperRadicalCocycleCoordinate_eq_iff]
  have e : z = shiftCocycle (upperRadicalLatticeRep n) z0 (-v) := by
    apply groupCohomology.cocycles₁_ext
    intro p
    rw [shiftCocycle_apply, h p, map_neg]
    abel
  rw [e, shiftCocycle_H1]

/-! ### Levi equivariance of the coordinates -/

/-- **Levi equivariance of the good-line coordinate**: the Levi translate of a `U`-equivariant
cocycle has the coordinate `detSign χ (diag(γ, 1)) • (γ ⋆_0 Φ f)`. -/
theorem Phi_levi (n : ℕ) (χ : RankOneCharacter) (positive : 0 < n)
    {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f) (γ : GL2Z) :
    PhiTotal n (cochainRep (rationalCoefficientComponent n χ) (leviHom γ) f) =
      Twisted.detSign χ (leviHom γ) •
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
          (PhiTotal n f) := by
  have hf' := uCocycle_cochainRep_levi hf γ
  have key : ∀ p, zCoc n χ hf' p =
      (Twisted.detSign χ (leviHom γ) •
          lowerRadicalCocycleLevi n γ (zCoc n χ hf)) p +
        ((lowerRadicalLatticeRep n).ρ p
            (asLow n (rationalCoefficientComponent n χ (leviHom γ) (f ![1, (leviHom γ)⁻¹]))) -
          asLow n (rationalCoefficientComponent n χ (leviHom γ) (f ![1, (leviHom γ)⁻¹]))) := by
    intro p
    have h := pull1_lattice (rationalCoefficientComponent n χ) hf (leviHom γ)
      (lowerRadicalLattice p) (lowerRadicalLattice (lowerLeviLatticeInput γ p)) (lower_mem_sub _)
      (lowerLeviLatticeInput_conjugation γ p)
    rw [rho_lower_eq n χ p] at h
    have e : (Twisted.detSign χ (leviHom γ) •
        lowerRadicalCocycleLevi n γ (zCoc n χ hf)) p =
        rationalCoefficientComponent n χ (leviHom γ)
          (f ![1, lowerRadicalLattice (lowerLeviLatticeInput γ p)]) := by
      change Twisted.detSign χ (leviHom γ) •
        arithmeticLeviCoefficient n γ (f ![1, lowerRadicalLattice (lowerLeviLatticeInput γ p)]) = _
      exact (LinearMap.congr_fun (Twisted.rho_eq_detSign_smul n χ (leviHom γ)) _).symm
    rw [e]
    exact h
  rw [PhiTotal_eq n χ hf', PhiTotal_eq n χ hf,
    coord_lower_eq_of_shift n positive _ _ _ key, map_smul,
    lowerRadicalCocycleCoordinate_equivariant]

theorem dualRep_lower (n : ℕ) (χ : RankOneCharacter) (p : RadicalLattice) :
    dualRep (dualityData n χ) (lowerRadicalLattice p) = (upperRadicalLatticeRep n).ρ p⁻¹ :=
  rho_dual_lower_eq n χ p

/-- The dual coefficients at a Levi element are the coefficients at the inverse transpose. -/
theorem dualRep_levi (n : ℕ) (χ : RankOneCharacter) (γ : GL2Z) :
    dualRep (dualityData n χ) (leviHom γ) = rationalCoefficientComponent n χ (leviHom (invT γ)) := by
  change rationalCoefficientComponent n χ (dualInvolution (leviHom γ)) = _
  rw [dualInvolution_leviHom]

/-- The inverse of the inverse transpose has the transposed matrix. -/
theorem invT_inv_val (γ : GL2Z) :
    (((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) = (γ : Matrix (Fin 2) (Fin 2) ℤ)ᵀ := rfl

/-- The upper Levi action of the inverse transpose is the lower Levi action on the lattice. -/
theorem upperLeviLatticeInput_invT (γ : GL2Z) (p : RadicalLattice) :
    upperLeviLatticeInput (invT γ) p = lowerLeviLatticeInput γ p := by
  apply Multiplicative.toAdd.injective
  change ((((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * p.toAdd.1 +
        (((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * p.toAdd.2,
      (((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * p.toAdd.1 +
        (((invT γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * p.toAdd.2) =
    (p.toAdd.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + p.toAdd.2 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
      p.toAdd.1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + p.toAdd.2 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
  rw [invT_inv_val]
  simp only [Matrix.transpose_apply, Prod.mk.injEq]
  constructor <;> ring

/-- **Levi equivariance of the rotated identity-plane coordinate**: the Levi translate of a
`U`-equivariant cocycle for the dual coefficients has the coordinate
`detSign χ (diag(γ^{-T}, 1)) • (γ ⋆_{n+2} Ψ g)`. -/
theorem Psi_levi (n : ℕ) (χ : RankOneCharacter)
    {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n χ)) latL1.sub g) (γ : GL2Z) :
    PsiTotal n (cochainRep (dualRep (dualityData n χ)) (leviHom γ) g) =
      Twisted.detSign χ (leviHom (invT γ)) •
        Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
          (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) (PsiTotal n g) := by
  have hg' := uCocycle_cochainRep_levi hg γ
  have key : ∀ p, wCoc n χ hg' p =
      (Twisted.detSign χ (leviHom (invT γ)) •
          upperRadicalCocycleLevi n (invT γ) (wCoc n χ hg)) p +
        ((upperRadicalLatticeRep n).ρ p
            (asUp n (dualRep (dualityData n χ) (leviHom γ) (g ![1, (leviHom γ)⁻¹]))) -
          asUp n (dualRep (dualityData n χ) (leviHom γ) (g ![1, (leviHom γ)⁻¹]))) := by
    intro p
    have h := pull1_lattice (dualRep (dualityData n χ)) hg (leviHom γ)
      (lowerRadicalLattice p⁻¹) (lowerRadicalLattice (lowerLeviLatticeInput γ p⁻¹))
      (lower_mem_sub _) (lowerLeviLatticeInput_conjugation γ p⁻¹)
    rw [dualRep_lower n χ p⁻¹, inv_inv] at h
    have e : (Twisted.detSign χ (leviHom (invT γ)) •
        upperRadicalCocycleLevi n (invT γ) (wCoc n χ hg)) p =
        dualRep (dualityData n χ) (leviHom γ)
          (g ![1, lowerRadicalLattice (lowerLeviLatticeInput γ p⁻¹)]) := by
      have hu : upperLeviLatticeInput (invT γ) p = lowerLeviLatticeInput γ p :=
        upperLeviLatticeInput_invT γ p
      change Twisted.detSign χ (leviHom (invT γ)) • arithmeticLeviCoefficient n (invT γ)
        (g ![1, lowerRadicalLattice (upperLeviLatticeInput (invT γ) p)⁻¹]) = _
      rw [hu, ← map_inv (lowerLeviLatticeInput γ) p, dualRep_levi]
      exact (LinearMap.congr_fun
        (Twisted.rho_eq_detSign_smul n χ (leviHom (invT γ))) _).symm
    rw [e]
    exact h
  have hup : upperRadicalCocycleCoordinate n (wCoc n χ hg') =
      Twisted.detSign χ (leviHom (invT γ)) •
        Binary.homogeneousAction (n + 1) (-1)
          (GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ))
          (upperRadicalCocycleCoordinate n (wCoc n χ hg)) := by
    rw [coord_upper_eq_of_shift n _ _ _ key, map_smul, upperRadicalCocycleCoordinate_equivariant]
  simp only [PsiTotal, LinearMap.comp_apply]
  rw [upperTotal_eq n χ hg', upperTotal_eq n χ hg, hup, map_smul,
    binarySwap_homogeneousAction (n + 1) (-1) _ _
      (map_mul_transpose γ (invT γ) (mul_invT_transpose γ))]

/-! ### The Levi cocycles of the fiber data -/

/-- **The Levi cocycles `A(k⁻¹)`, `A'(k⁻¹)` of the fiber data are `U`-equivariant one-cocycles for
every `γ ∈ GL₂(ℤ)`**, also those of determinant `-1`. -/
theorem uCocycle_leviCocycle_hom {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
    {ζ : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) (γ : GL2Z) :
    UCocycle (rationalCoefficientComponent n χ) latL1.sub
        (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom γ)⁻¹) ∧
      UCocycle (dualRep (dualityData n χ)) latL1.sub
        (leviCocycle (dualRep (dualityData n χ)) θU (leviHom γ)⁻¹) := by
  have hh : (leviHom γ)⁻¹ ∈ levelStabilizer L₁ := (levelStabilizer L₁).inv_mem (leviHom_mem_level γ)
  have hn : ∀ u ∈ latL1.sub, (leviHom γ)⁻¹ * u * ((leviHom γ)⁻¹)⁻¹ ∈ latL1.sub :=
    fun u hu => by simpa only [inv_inv] using levi_inv_normalizes γ u hu
  exact ⟨⟨leviCocycle_equivariant _ hF.omegaU_eq hn,
      leviCocycle_closed _ hF.omegaU_d (hF.zeta_eq _ hh)⟩,
    ⟨leviCocycle_equivariant _ hF.thetaU_eq hn,
      leviCocycle_closed _ hF.thetaU_d (hF.eta_eq _ hh)⟩⟩

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
