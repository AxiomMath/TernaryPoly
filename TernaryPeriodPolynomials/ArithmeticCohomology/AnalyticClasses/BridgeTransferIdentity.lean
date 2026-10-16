module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.BridgeTransferBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeCocycle

@[expose] public section


/-!
# The real transfer of a binary cocycle that differs from a regular one by a coboundary

If `N₁ (A) = N₂ (A) + (A · κ - κ)` pointwise, with `N₂` a regular pointwise binary cocycle and
`κ` bounded with continuous translates, then for `n ≥ 5` the inhomogeneous real good-line
transfers satisfy `T_{N₁} (a, b) = T_{N₂} (a, b) + (a • H b - H (a b) + H a)` with
`H = bridgeTransfer κ`. Both `H a` and `T_N (a, b)` are linear in the test, and both are
left-invariant in the adelic point under every set leaving `κ`, respectively `N`, invariant.
For the reconstructed binary cocycle, `N₂` is the pointwise Eichler normal form of the classical
endpoint and `κ` is the lift of the finite-level correction, which is invariant under the rational
points.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

variable {n : ℕ}

/-! ### Additivity of the transfer -/

/-- The real transfer is additive in the binary cochain on integrable configurations. -/
theorem lineTransfer_add {N₁ N₂ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (x : Fin 3 → LineGroup)
    (integrable₁ : ∀ (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable (fun u => functional (lineTransferIntegrand N₁ x u h))
        ((volume : Measure ℝ).prod volume))
    (integrable₂ : ∀ (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable (fun u => functional (lineTransferIntegrand N₂ x u h))
        ((volume : Measure ℝ).prod volume)) :
    lineTransfer (fun A => N₁ A + N₂ A) x = lineTransfer N₁ x + lineTransfer N₂ x := by
  funext p
  obtain ⟨h, functional⟩ := p
  change _ = lineTransfer N₁ x (h, functional) + lineTransfer N₂ x (h, functional)
  unfold lineTransfer
  dsimp only
  rw [← integral_add (integrable₁ h functional) (integrable₂ h functional)]
  congr 1
  funext u
  rw [lineTransferIntegrand_add, map_add]

/-- **The bridge identity for the real good-line transfer** (`n ≥ 5`): if `N₁` differs from a
regular pointwise binary cocycle `N₂` by the binary coboundary of a bounded `κ` with continuous
translates, the transfers differ by the coboundary of `bridgeTransfer κ`. -/
theorem lineTransferCochain_eq_add_bridgeTransfer (large : 5 ≤ n) (N₂ : BinaryPointCocycle n)
    {N₁ : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (decomposition : ∀ A h,
      N₁ A h = N₂.value A h + (binaryAmbientRepresentation n A κ h - κ h))
    (a b : LineGroup) :
    lineTransferCochain N₁ a b = lineTransferCochain N₂.value a b +
      (a • bridgeTransfer κ b - bridgeTransfer κ (a * b) + bridgeTransfer κ a) := by
  have values : N₁ = fun A => N₂.value A + binaryCoboundary κ A := by
    funext A h
    exact decomposition A h
  subst values
  change lineTransfer _ ![1, a, a * b] = lineTransfer N₂.value ![1, a, a * b] + _
  rw [lineTransfer_add ![1, a, a * b] (lineTransferIntegrand_integrable large N₂ _)
    (lineTransferIntegrand_binaryCoboundary_integrable large bounded continuous _),
    ← lineTransferCochain_binaryCoboundary_of_bounded large bounded continuous a b]
  rfl

/-! ### Linearity in the test -/

/-- Integrals of scalar tests of an integrable family are linear in the test. -/
theorem linearTests_integral {F : LineValues n} {f : ℝ × ℝ → BinaryAdelicGL → HomogeneousPoly n}
    (integrable : ∀ (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Integrable (fun u => functional (f u h)) ((volume : Measure ℝ).prod volume))
    (value : ∀ (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      F (h, functional) = ∫ u, functional (f u h) ∂((volume : Measure ℝ).prod volume)) :
    LinearTests F := by
  intro h functional
  rw [functional_lineVector]
  simp_rw [value, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun j _ => (integrable h _).mul_const _)]
  congr 1
  funext u
  exact functional_eq_basis_sum functional (f u h)

/-- **The transfer of `θκ` is linear in the test** (`n ≥ 5`). -/
theorem linearTests_bridgeTransfer (large : 5 ≤ n)
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (bounded : ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ h, ‖functional (κ h)‖ ≤ C)
    (continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      Continuous (fun A => functional (binaryAmbientRepresentation n A κ h)))
    (a : LineGroup) : LinearTests (bridgeTransfer κ a) := by
  refine linearTests_integral (lineTransferIntegrand_degenerate_integrable large bounded continuous
    1 a) (fun h functional => ?_)
  rw [bridgeTransfer_eq_lineTransfer]
  rfl

/-- **The inhomogeneous real transfer of a regular binary cocycle is linear in the test**
(`n ≥ 5`). -/
theorem linearTests_lineTransferCochain (large : 5 ≤ n) (N : BinaryPointCocycle n)
    (a b : LineGroup) : LinearTests (lineTransferCochain N.value a b) :=
  linearTests_integral (lineTransferIntegrand_integrable large N ![1, a, a * b])
    (fun _ _ => rfl)

/-! ### Left invariance in the adelic point -/

/-- **The transfer of `θκ` is left-invariant** under every set leaving `κ` invariant. -/
theorem bridgeTransfer_left_invariant {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {S : Set BinaryAdelicGL} (invariant : ∀ s ∈ S, ∀ h, κ (s * h) = κ h) (a : LineGroup)
    {s : BinaryAdelicGL} (member : s ∈ S) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    bridgeTransfer κ a (s * h, functional) = bridgeTransfer κ a (h, functional) := by
  unfold bridgeTransfer planeBridgeCochain
  simp only [mul_assoc, invariant s member]

/-- **The inhomogeneous real transfer is left-invariant** under every set leaving the binary
cochain invariant. -/
theorem lineTransferCochain_left_invariant
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {S : Set BinaryAdelicGL} (invariant : ∀ s ∈ S, ∀ A h, N A (s * h) = N A h) (a b : LineGroup)
    {s : BinaryAdelicGL} (member : s ∈ S) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain N a b (s * h, functional) = lineTransferCochain N a b (h, functional) := by
  rw [lineTransferCochain_apply, lineTransferCochain_apply]
  unfold relativeIntegrand pointCanonical
  simp only [mul_assoc, invariant s member]

/-! ### The reconstructed binary cocycle -/

/-- The scalar tests of the lift of a smooth tuple are uniformly bounded. -/
theorem hilbertLift_bounded (cusp : CuspidalRepresentation) (vectors : Fin (n + 2) → cusp.H)
    (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, ∀ h, ‖functional (hilbertLift cusp n vectors h)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hilbertLift_coord_bound cusp vectors smooth
  obtain ⟨D, hD⟩ := bound_functional_of_coord (hilbertLift cusp n vectors) Set.univ
    (fun position => ⟨C, fun h _ => hC h position⟩) functional
  exact ⟨D, fun h => hD h (Set.mem_univ h)⟩

/-- The lift of a smooth tuple is invariant under the rational points. -/
theorem hilbertLift_leftRational (cusp : CuspidalRepresentation) (vectors : Fin (n + 2) → cusp.H)
    (smooth : ∀ position, vectors position ∈ cusp.smooth) (γ : BinaryRationalGL)
    (h : BinaryAdelicGL) :
    hilbertLift cusp n vectors (GeneralLinearGroup.map rationalAdele γ * h) =
      hilbertLift cusp n vectors h := by
  unfold hilbertLift
  apply Finset.sum_congr rfl
  intro position _
  rw [smoothRealize_of_mem cusp ⟨_, smooth position⟩, cusp.leftRational]

/-- **The bridge identity for the reconstructed binary cocycle** (`n ≥ 5`): its real transfer is
the real transfer of the pointwise Eichler normal form of the classical endpoint plus the
coboundary of the transfer of `θκ`, for `κ` the lift of the finite-level correction. -/
theorem lineTransferCochain_original_eq (large : 5 ≤ n) (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction))
    (a b : LineGroup) :
    lineTransferCochain (fun A => (original A).val) a b =
      lineTransferCochain (eichlerNormal n (endpointScalar cusp halfWeight vector)) a b +
        (a • bridgeTransfer (hilbertLift cusp n correction) b -
          bridgeTransfer (hilbertLift cusp n correction) (a * b) +
          bridgeTransfer (hilbertLift cusp n correction) a) :=
  lineTransferCochain_eq_add_bridgeTransfer large
    (eichlerNormalPointCocycle cusp stages halfWeight vector fixed original correction
      correction_smooth reconstruction)
    (hilbertLift_bounded cusp correction correction_smooth)
    (hilbertLift_ambient_continuous cusp correction correction_smooth)
    (original_eq_eichlerNormal_add_of_smooth cusp stages halfWeight vector fixed original
      correction correction_smooth reconstruction) a b

end TernaryPeriodPolynomials.AnalyticClasses
