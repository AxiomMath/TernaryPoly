module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FiniteAveragedForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.BridgeTransferIdentity

@[expose] public section


/-!
# The finite good-line average of scalar tests

For scalar tests `X(h, λ)` the finite good-line average is `⟨X⟩(h, λ) = ∫ w(f) X(b(f) h, λ) df`.
At `h = 1` it is the finite average of scalar tests at the cohomological point. It commutes with
the action of the real good-line stabilizer, which moves `h` on the right by a real matrix and
precomposes `λ`, and it is additive on integrable scalar tests.

If `X` is left invariant under `GL₂(ℚ)` and right invariant under `GL₂(Ẑ)` in the adelic point,
its average is invariant under left translation by real integral matrices at real points. This
applies to the real transfer `bridgeTransfer κ` of `θκ` for a function `κ` with the same
invariance, in particular for the lift of a smooth spherical tuple, and to the inhomogeneous real
transfer of a binary family with the same invariance.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The average -/

/-- **The finite good-line average of scalar tests**, at every adelic point. -/
def averagedLine (X : LineValues n) : LineValues n :=
  fun p => finiteAverageLeft n (fun h => X (h, p.2)) p.1

theorem averagedLine_apply (X : LineValues n) (h : BinaryAdelicGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine X (h, functional) =
      ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
        X (atFinite (standardGoodLineFiniteCoordinates finite).block * h, functional)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := rfl

/-- **The finite average of scalar tests is the average at the identity.** -/
theorem finiteAverageLine_eq_averagedLine (X : LineValues n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    finiteAverageLine X functional = averagedLine X (1, functional) := by
  simp only [averagedLine_apply, finiteAverageLine, mul_one]

/-- **The average commutes with the real good-line stabilizer.** -/
theorem averagedLine_smul (q : LineGroup) (X : LineValues n) :
    averagedLine (q • X) = q • averagedLine X := by
  funext p
  obtain ⟨h, functional⟩ := p
  rw [lineValues_smul_apply]
  simp only [averagedLine_apply, lineValues_smul_apply, mul_assoc]

theorem averagedLine_add_apply (X Y : LineValues n)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) : (X + Y) p = X p + Y p := rfl

theorem averagedLine_sub_apply (X Y : LineValues n)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) : (X - Y) p = X p - Y p := rfl

/-- Integrability of the weighted scalar tests along the finite average, at every adelic point. -/
def LineAverageIntegrable (X : LineValues n) : Prop :=
  ∀ (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
    Integrable (fun finite => standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      X (atFinite (standardGoodLineFiniteCoordinates finite).block * h, functional))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

theorem LineAverageIntegrable.smul {X : LineValues n} (integrable : LineAverageIntegrable X)
    (q : LineGroup) : LineAverageIntegrable (q • X) := by
  intro h functional
  simp only [lineValues_smul_apply, mul_assoc]
  exact integrable _ _

theorem LineAverageIntegrable.add {X Y : LineValues n} (first : LineAverageIntegrable X)
    (second : LineAverageIntegrable Y) : LineAverageIntegrable (X + Y) := by
  intro h functional
  simp only [averagedLine_add_apply, mul_add]
  exact (first h functional).add (second h functional)

theorem LineAverageIntegrable.sub {X Y : LineValues n} (first : LineAverageIntegrable X)
    (second : LineAverageIntegrable Y) : LineAverageIntegrable (X - Y) := by
  intro h functional
  simp only [averagedLine_sub_apply, mul_sub]
  exact (first h functional).sub (second h functional)

/-- **The average is additive** on integrable scalar tests. -/
theorem averagedLine_add {X Y : LineValues n} (first : LineAverageIntegrable X)
    (second : LineAverageIntegrable Y) :
    averagedLine (X + Y) = averagedLine X + averagedLine Y := by
  funext p
  obtain ⟨h, functional⟩ := p
  change averagedLine (X + Y) (h, functional) =
    averagedLine X (h, functional) + averagedLine Y (h, functional)
  simp only [averagedLine_apply]
  rw [← integral_add (first h functional) (second h functional)]
  simp only [averagedLine_add_apply, mul_add]

/-- The average is subtractive on integrable scalar tests. -/
theorem averagedLine_sub {X Y : LineValues n} (first : LineAverageIntegrable X)
    (second : LineAverageIntegrable Y) :
    averagedLine (X - Y) = averagedLine X - averagedLine Y := by
  funext p
  obtain ⟨h, functional⟩ := p
  change averagedLine (X - Y) (h, functional) =
    averagedLine X (h, functional) - averagedLine Y (h, functional)
  simp only [averagedLine_apply]
  rw [← integral_sub (first h functional) (second h functional)]
  simp only [averagedLine_sub_apply, mul_sub]

/-! ### Invariance under real integral Levi translations -/

/-- **The average of left `GL₂(ℚ)`-invariant, right `GL₂(Ẑ)`-invariant scalar tests is invariant
under left translation by real integral matrices** at real points. -/
theorem averagedLine_realLevi (X : LineValues n)
    (left : ∀ (γ : BinaryRationalGL) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      X (GeneralLinearGroup.map rationalAdele γ * h, functional) = X (h, functional))
    (right : ∀ (h : BinaryAdelicGL) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles)
      (functional : HomogeneousPoly n →ₗ[ℂ] ℂ),
      X (h * atFinite (GeneralLinearGroup.map integralEmbedding compact), functional) =
        X (h, functional))
    (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine X (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g,
        functional) = averagedLine X (atInfinity g, functional) :=
  finiteAverageLeft_realLevi (fun h => X (h, functional)) (fun γ h => left γ h functional)
    (fun h compact => right h compact functional) γ g

theorem mul_atFinite_mul_atInfinity (h : BinaryAdelicGL) (block : BinaryFiniteGL)
    (g : BinaryRealGL) :
    h * atFinite block * atInfinity g = h * atInfinity g * atFinite block := by
  rw [mul_assoc, ← (atInfinity_commute_atFinite g block).eq, ← mul_assoc]

/-- The transfer of `θκ` inherits right invariance from `κ`. -/
theorem bridgeTransfer_right_invariant {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {block : BinaryFiniteGL} (invariant : ∀ h, κ (h * atFinite block) = κ h) (a : LineGroup)
    (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    bridgeTransfer κ a (h * atFinite block, functional) = bridgeTransfer κ a (h, functional) := by
  unfold bridgeTransfer planeBridgeCochain
  simp only [mul_atFinite_mul_atInfinity, invariant]

/-- The inhomogeneous real transfer inherits right invariance from the binary family. -/
theorem lineTransferCochain_right_invariant
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    {block : BinaryFiniteGL} (invariant : ∀ A h, N A (h * atFinite block) = N A h)
    (a b : LineGroup) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    lineTransferCochain N a b (h * atFinite block, functional) =
      lineTransferCochain N a b (h, functional) := by
  rw [lineTransferCochain_apply, lineTransferCochain_apply]
  unfold relativeIntegrand pointCanonical
  simp only [mul_atFinite_mul_atInfinity, invariant]

/-- **Levi invariance of the averaged transfer of `θκ`**, for `κ` left `GL₂(ℚ)`-invariant and
right `GL₂(Ẑ)`-invariant. -/
theorem averagedLine_bridgeTransfer_realLevi
    {κ : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (left : ∀ (γ : BinaryRationalGL) (h : BinaryAdelicGL),
      κ (GeneralLinearGroup.map rationalAdele γ * h) = κ h)
    (right : ∀ (h : BinaryAdelicGL) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles),
      κ (h * atFinite (GeneralLinearGroup.map integralEmbedding compact)) = κ h)
    (b : LineGroup) (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine (bridgeTransfer κ b)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g, functional) =
      averagedLine (bridgeTransfer κ b) (atInfinity g, functional) :=
  averagedLine_realLevi _
    (fun γ h functional => bridgeTransfer_left_invariant
      (S := Set.range (GeneralLinearGroup.map rationalAdele))
      (fun _ member h => by
        obtain ⟨γ, rfl⟩ := member
        exact left γ h) b ⟨γ, rfl⟩ h functional)
    (fun h compact functional => bridgeTransfer_right_invariant (right · compact) b h functional)
    γ g functional

/-- **Levi invariance of the averaged inhomogeneous real transfer**, for a binary family that is
left `GL₂(ℚ)`-invariant and right `GL₂(Ẑ)`-invariant in the adelic point. -/
theorem averagedLine_lineTransferCochain_realLevi
    {N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (left : ∀ (γ : BinaryRationalGL) (A : BinaryRealGL) (h : BinaryAdelicGL),
      N A (GeneralLinearGroup.map rationalAdele γ * h) = N A h)
    (right : ∀ (A : BinaryRealGL) (h : BinaryAdelicGL)
      (compact : GeneralLinearGroup (Fin 2) IntegralAdeles),
      N A (h * atFinite (GeneralLinearGroup.map integralEmbedding compact)) = N A h)
    (a b : LineGroup) (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine (lineTransferCochain N a b)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g, functional) =
      averagedLine (lineTransferCochain N a b) (atInfinity g, functional) :=
  averagedLine_realLevi _
    (fun γ h functional => lineTransferCochain_left_invariant
      (S := Set.range (GeneralLinearGroup.map rationalAdele))
      (fun _ member A h => by
        obtain ⟨γ, rfl⟩ := member
        exact left γ A h) a b ⟨γ, rfl⟩ h functional)
    (fun h compact functional =>
      lineTransferCochain_right_invariant (fun A h => right A h compact) a b h functional)
    γ g functional

/-! ### The lift of a spherical tuple -/

/-- The lift of a smooth spherical tuple is right invariant under `GL₂(Ẑ)`. -/
theorem hilbertLift_right_invariant (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp)
    (h : BinaryAdelicGL) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    hilbertLift cusp n vectors (h * atFinite (GeneralLinearGroup.map integralEmbedding compact)) =
      hilbertLift cusp n vectors h := by
  unfold hilbertLift
  refine Finset.sum_congr rfl fun position _ => ?_
  have fixed : (⟨cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding compact))
      (vectors position), cusp.smooth_stable _ _ (smooth position)⟩ : cusp.smooth) =
      ⟨vectors position, smooth position⟩ := Subtype.ext (spherical position compact)
  rw [smoothRealize_of_mem cusp ⟨_, smooth position⟩, ← cusp.equivariant, fixed]

/-- **Levi invariance of the averaged transfer of `θκ`** for the lift `κ` of a smooth spherical
tuple. -/
theorem averagedLine_bridgeTransfer_hilbertLift_realLevi (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (spherical : ∀ position, vectors position ∈ cuspSphericalValues cusp)
    (b : LineGroup) (γ : GeneralLinearGroup (Fin 2) ℤ) (g : BinaryRealGL)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    averagedLine (bridgeTransfer (hilbertLift cusp n vectors) b)
        (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) γ) * atInfinity g, functional) =
      averagedLine (bridgeTransfer (hilbertLift cusp n vectors) b) (atInfinity g, functional) :=
  averagedLine_bridgeTransfer_realLevi (hilbertLift_leftRational cusp vectors smooth)
    (hilbertLift_right_invariant cusp vectors smooth spherical) b γ g functional

end TernaryPeriodPolynomials.AnalyticClasses
