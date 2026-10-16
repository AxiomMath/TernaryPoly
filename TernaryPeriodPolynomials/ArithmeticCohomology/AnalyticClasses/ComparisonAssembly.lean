module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ComparisonAssemblyAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.Rigidity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticRegular
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.Primitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.LieIntegral

@[expose] public section


/-!
# The real side of the comparison makes the twisted Eichler cocycle a coboundary

Let `F` be a scalar form with Eichler data, invariant under the integral Levi at infinity, and let
`t` be the real good-line transfer of its Eichler normal form. Suppose that the edge velocity of
`t` along the diagonal flow is `c ≠ 0` times the velocity of the transported twisted normal form.
If the coboundary of a one-cochain `β` of the arithmetic good-line stabilizer agrees, at an adelic
point `h` commuting with the real group, with `t + δH` on radical lattice pairs and in the mixed
coordinate, then the twisted Eichler normal form `γ ↦ N⁻(γ)(h)` is a one-coboundary of `GL₂(ℤ)`
acting on `Sym^{n+1}` without determinant twist.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Left invariance of the real transfer -/

theorem eichlerPeriod_left {F : BinaryAdelicGL → ℂ → ℂ} {k : BinaryAdelicGL}
    (invariant : ∀ h z, F (k * h) z = F h z) (z : ℂ) (h : BinaryAdelicGL) :
    eichlerPeriod n F z (k * h) = eichlerPeriod n F z h := by
  simp only [eichlerPeriod, eichlerIntegrand, invariant]

theorem binaryAmbientRepresentation_left (A : BinaryRealGL)
    {f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)} {k : BinaryAdelicGL}
    (invariant : ∀ h, f (k * h) = f h) (h : BinaryAdelicGL) :
    binaryAmbientRepresentation n A f (k * h) = binaryAmbientRepresentation n A f h := by
  change normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
      binaryCoefficient n A (f (k * h * atInfinity A)) =
    normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
      binaryCoefficient n A (f (h * atInfinity A))
  rw [mul_assoc, invariant]

theorem eichlerNormal_left {F : BinaryAdelicGL → ℂ → ℂ} {k : BinaryAdelicGL}
    (invariant : ∀ h z, F (k * h) z = F h z) (A : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerNormal n F A (k * h) = eichlerNormal n F A h := by
  rw [eichlerNormal_def, eichlerNormal_def, eichlerPeriod_left invariant,
    binaryAmbientRepresentation_left _ (eichlerPeriod_left invariant _)]

theorem relativeIntegrand_left
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)} {k : BinaryAdelicGL}
    (invariant : ∀ A h, N A (k * h) = N A h) (u : ℝ × ℝ) (a c : LineGroup)
    (h : BinaryAdelicGL) :
    relativeIntegrand N u a c (k * h) = relativeIntegrand N u a c h := by
  unfold relativeIntegrand pointCanonical
  rw [mul_assoc, invariant]

/-- **The real transfer of a left invariant normal form is left invariant.** -/
theorem lineTransferCochain_left
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)} {k : BinaryAdelicGL}
    (invariant : ∀ A h, N A (k * h) = N A h) (a b : LineGroup) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain N a b (k * h, functional) = lineTransferCochain N a b (h, functional) := by
  rw [lineTransferCochain_apply, lineTransferCochain_apply]
  simp only [relativeIntegrand_left invariant]

/-! ### The lattice coordinate as a sum over the generators -/

theorem latticeCoordinate_eq_sum (f : RadicalLattice → HomogeneousPoly n) :
    latticeCoordinate n f =
      ∑ i : Fin 2, lowerRadicalLatticeContribution n i (f (radicalLatticeGenerator i)) := by
  rw [Fin.sum_univ_two]
  exact lowerRadicalCoordinate_averages n (fun i => f (radicalLatticeGenerator i))

/-! ### The comparison -/

/-- **The real side of the comparison makes the twisted Eichler cocycle a coboundary.**

Let `F` have Eichler data (`9 ≤ n`) and be invariant under `GL₂(ℤ)` at infinity, and let
`t = lineTransferCochain (eichlerNormal n F)`. Assume the edge velocity identity with a constant
`c ≠ 0`. Let `h` be an adelic point commuting with the real group, let `H` be a one-cochain of
scalar tests, linear in the test at the real translates of `h` and invariant at `h` under the
integral Levi at infinity, and let `T = t + δH`. If the coboundary of `β` is `T` at `h` on radical
lattice pairs, and its mixed coordinate is the lattice coordinate of the radical edge of `T` at
`h`, then `γ ↦ N⁻(γ)(h)` is a one-coboundary of `GL₂(ℤ)` on `Sym^{n+1}`. -/
theorem exists_eichlerTwisted_coboundary (large : 9 ≤ n) {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F)
    (leftInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) h z,
      F (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * h) z = F h z)
    (c : ℂ) (hc : c ≠ 0)
    (velocity : ∀ h, lowerRadicalCoordinate n
      (fun i => lineVector (edgeMixedIntegral (eichlerNormal n F) i) h) =
        c • edgeNormalVelocity n F h)
    (normalVelocity : ∀ h (j : Fin (n + 2)), HasDerivAt
      (fun s => (binaryWeightBasis (n + 1)).coord j (edgeNormal n F (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (edgeNormalVelocity n F h)) 0)
    (h : BinaryAdelicGL) (central : ∀ g : BinaryRealGL, h * atInfinity g = atInfinity g * h)
    (H : LineGroup → LineValues n)
    (Hlinear : ∀ q (g : BinaryRealGL) ℓ,
      H q (h * atInfinity g, ℓ) = ℓ (lineVector (H q) (h * atInfinity g)))
    (HInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) q ℓ,
      H q (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * h, ℓ) = H q (h, ℓ))
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n)
    (radical : ∀ r₁ r₂, twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        lineVector (lineTransferCochain (eichlerNormal n F)
            (lineRadicalElement (latticeVector r₁)) (lineRadicalElement (latticeVector r₂)) +
          lineCoboundary H (lineRadicalElement (latticeVector r₁))
            (lineRadicalElement (latticeVector r₂))) h)
    (mixed : ∀ γ, goodLineMixedCoordinate n γ
      (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
        latticeCoordinate n (fun r => lineVector (radicalEdge
          (fun p q => lineTransferCochain (eichlerNormal n F) p q + lineCoboundary H p q)
          (integralLevi γ) (latticeVector r)) h)) :
    ∃ P : Binary.HomogeneousPoly (n + 1), ∀ γ : GeneralLinearGroup (Fin 2) ℤ,
      eichlerTwisted n F (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) h =
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) P -
          P := by
  set t := lineTransferCochain (eichlerNormal n F)
  have cocycle : IsTwoCocycle t := lineTransfer_isTwoCocycle (by omega) hF.pointCocycle
  have regular : EdgeRegular t := edgeRegular_eichlerNormal (by omega) hF
  obtain ⟨a, linear, differentiable, trivial, determined⟩ := exists_radicalPrimitive (by omega) hF
    (fun x => RadicalLie.integral_radicalObstruction hF (by omega) x)
  have moved (γ : GeneralLinearGroup (Fin 2) ℤ) : h * atInfinity (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)) =
        atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) (integralPivot γ)) * h := by
    rw [central, map_integralPivot]
  have aInvariant (γ : GeneralLinearGroup (Fin 2) ℤ) (Y : Fin 2 → ℝ) ℓ :
      a Y (h * atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) =
        a Y (h, ℓ) := by
    rw [moved]
    exact determined _ _ (fun Y Y' ℓ => lineTransferCochain_left
      (eichlerNormal_left (leftInvariant (integralPivot γ))) _ _ _ _) Y ℓ
  have HInvariant' (γ : GeneralLinearGroup (Fin 2) ℤ) (q : LineGroup) ℓ :
      H q (h * atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) =
        H q (h, ℓ) := by
    rw [moved]
    exact HInvariant _ q ℓ
  obtain ⟨P, hP⟩ := exists_derivativeEdge_coboundary (by omega) cocycle regular linear
    differentiable trivial h Hlinear aInvariant HInvariant' β radical mixed
  have edge (m : unimodularLevi) : derivativeEdge t m = c • edgeNormal n F m :=
    derivativeEdge_eq_smul_edgeNormal hF cocycle regular c (edgeNormalVelocity n F)
      (fun x j => by
        have derivative := hasDerivAt_coord_derivativeEdge_diagonal (by omega) hF x j
        rwa [velocity] at derivative)
      normalVelocity m
  have three : (3 : ℂ) * c ≠ 0 := mul_ne_zero (by norm_num) hc
  refine ⟨binarySwap n (((3 : ℂ) * c)⁻¹ • P), fun δ => ?_⟩
  have value := hP (integralPivot δ)
  rw [edge, Pi.smul_apply, smul_smul] at value
  have normal : edgeNormal n F (integralLevi (integralPivot δ)) h =
      binarySwap n (eichlerTwisted n F (GeneralLinearGroup.map (Int.castRingHom ℝ) δ) h) := by
    change binarySwap n (eichlerTwisted n F (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) (integralPivot δ))) h) = _
    rw [map_integralPivot, pivotConjugate_pivotConjugate]
  rw [normal, ← eq_inv_smul_iff₀ three] at value
  rw [← binarySwap_binarySwap (eichlerTwisted n F _ h), value, map_smul, map_sub,
    binarySwap_homogeneousAction, map_smul, map_smul, smul_sub]

/-- **The comparison at the identity adelic point.** -/
theorem exists_eichlerTwisted_coboundary_one (large : 9 ≤ n) {F : BinaryAdelicGL → ℂ → ℂ}
    (hF : EichlerData n F)
    (leftInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) h z,
      F (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * h) z = F h z)
    (c : ℂ) (hc : c ≠ 0)
    (velocity : ∀ h, lowerRadicalCoordinate n
      (fun i => lineVector (edgeMixedIntegral (eichlerNormal n F) i) h) =
        c • edgeNormalVelocity n F h)
    (normalVelocity : ∀ h (j : Fin (n + 2)), HasDerivAt
      (fun s => (binaryWeightBasis (n + 1)).coord j (edgeNormal n F (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (edgeNormalVelocity n F h)) 0)
    (H : LineGroup → LineValues n)
    (Hlinear : ∀ q (g : BinaryRealGL) ℓ,
      H q (atInfinity g, ℓ) = ℓ (lineVector (H q) (atInfinity g)))
    (HInvariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) q ℓ,
      H q (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ), ℓ) = H q (1, ℓ))
    (β : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n)
    (radical : ∀ r₁ r₂, twoBoundaryCycle (goodLineCoefficientRep n) β
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
        lineVector (lineTransferCochain (eichlerNormal n F)
            (lineRadicalElement (latticeVector r₁)) (lineRadicalElement (latticeVector r₂)) +
          lineCoboundary H (lineRadicalElement (latticeVector r₁))
            (lineRadicalElement (latticeVector r₂))) 1)
    (mixed : ∀ γ, goodLineMixedCoordinate n γ
      (fun pair => twoBoundaryCycle (goodLineCoefficientRep n) β pair) =
        ∑ i : Fin 2, lowerRadicalLatticeContribution n i (lineVector (radicalEdge
          (fun p q => lineTransferCochain (eichlerNormal n F) p q + lineCoboundary H p q)
          (integralLevi γ) (latticeVector (radicalLatticeGenerator i))) 1)) :
    ∃ P : Binary.HomogeneousPoly (n + 1), ∀ γ : GeneralLinearGroup (Fin 2) ℤ,
      eichlerTwisted n F (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) 1 =
        Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) P -
          P := by
  refine exists_eichlerTwisted_coboundary large hF leftInvariant c hc velocity normalVelocity 1
    (fun g => by rw [one_mul, mul_one]) H (fun q g ℓ => by rw [one_mul]; exact Hlinear q g ℓ)
    (fun γ q ℓ => by rw [mul_one]; exact HInvariant γ q ℓ) β radical (fun γ => ?_)
  rw [mixed γ, latticeCoordinate_eq_sum (fun r => lineVector (radicalEdge
    (fun p q => lineTransferCochain (eichlerNormal n F) p q + lineCoboundary H p q)
    (integralLevi γ) (latticeVector r)) 1)]

end TernaryPeriodPolynomials.AnalyticClasses
