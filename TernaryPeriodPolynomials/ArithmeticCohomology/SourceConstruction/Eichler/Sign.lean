module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwLift

@[expose] public section


/-!
# The sign-twisted Eichler cocycle

Headline statement of the sign-twisted Eichler construction.  For a spherical cuspidal
representation `σ` carrying a nonzero holomorphic lowest-weight vector of weight `-(n + 3)`, the
antisymmetrised potential `P⁻(z) = ½ (Per z - J Per(-z̄))` of the holomorphic Eichler form gives a
cocycle `α` for the twisted action `g ↦ sgn(det g) • binaryCohomologicalAction n g`, i.e.

`α (g * h) x = α g x + sgn (det g) • binaryCohomologicalAction n g (α h) x`,

which vanishes on the orthogonal group, has explicit smooth spherical lifts into the smooth
vectors of `σ`, real-analytic scalar coefficients, and is right invariant under `GL₂(Ẑ)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource

/-- The properties of a sign-twisted Eichler cocycle `α`: the cocycle identity for the action
`g ↦ sgn(det g) • binaryCohomologicalAction n g`, the vanishing on orthogonal matrices, cuspidal
values with explicit smooth spherical lifts, scalar real-analyticity, and right `GL₂(Ẑ)`-invariance.
-/
def IsSignEichlerCocycle (σ : CuspidalRepresentation) (n : ℕ)
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) : Prop :=
  (∀ g h x, α (g * h) x = α g x + signDet g • binaryCohomologicalAction n g (α h) x) ∧
  (∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0) ∧
  (∀ g, BinaryValues σ n (α g)) ∧
  (∀ m : Fin 2 →₀ ℕ, ∃ v : BinaryRealGL → σ.smooth,
    Smooth (fun x : Fin 1 → BinaryRealGL => (v (x 0)).val) ∧
    (∀ g A, σ.realize (v g) A = (α g A).val.coeff m) ∧
    (∀ g, (v g).val ∈ cuspSphericalValues σ)) ∧
  (∀ (A : BinaryAdelicGL) (m : Fin 2 →₀ ℕ),
    Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff m)) ∧
  (∀ (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL),
    α g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = α g x)

/-- The sign of the determinant, as a complex number, written with `if det < 0 then -1 else 1`. -/
theorem signDet_eq_ite (g : BinaryRealGL) :
    signDet g = if (GeneralLinearGroup.det g).val < 0 then -1 else 1 := by
  have ne : (GeneralLinearGroup.det g).val ≠ 0 := (GeneralLinearGroup.det g).ne_zero
  unfold signDet
  by_cases h : 0 < (GeneralLinearGroup.det g).val
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le)]
  · rw [ite_eq_right h, ite_eq_left (lt_of_le_of_ne (not_lt.1 h) ne)]

theorem IsSignEichlerCocycle.mul {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsSignEichlerCocycle σ n α) (g k : BinaryRealGL) (x : BinaryAdelicGL) :
    α (g * k) x = α g x + signDet g • binaryCohomologicalAction n g (α k) x := by
  obtain ⟨hmul, -⟩ := h
  exact hmul g k x

theorem IsSignEichlerCocycle.orthogonal {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsSignEichlerCocycle σ n α) (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : α k x = 0 := by
  obtain ⟨-, horth, -⟩ := h
  exact horth k hk x

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

/-- **The sign-twisted Eichler cocycle** `A ↦ ½ (Per(A i) - J Per(-conj (A i)))`, realized as a
polynomial-valued function on the adelic group. -/
def signEichlerCocycle (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  eichlerCocycleTw D A

/-- The smooth lift of a monomial coefficient of the sign-twisted Eichler cocycle. -/
def signLiftVector (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  liftVectorTw D stages m g

/-- The Hilbert-level sign-twisted cocycle `A ↦ P⁻(A · i)`. -/
def signHilbertCocycle (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  cocycleTw D A

theorem signEichlerCocycle_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.signEichlerCocycle (g * h) x = D.signEichlerCocycle g x +
      signDet g • binaryCohomologicalAction n g (D.signEichlerCocycle h) x :=
  eichlerCocycleTw_mul D stages g h x

theorem signHilbertCocycle_mul (A B : BinaryRealGL) :
    D.signHilbertCocycle (A * B) = D.signHilbertCocycle A +
      signDet A • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (D.signHilbertCocycle B) :=
  cocycleTw_mul D A B

/-- **Existence of the sign-twisted Eichler cocycle with its full regularity package.** -/
theorem signEichlerCocycle_spec (stages : AnalyticScalar.ContinuousStages σ) :
    IsSignEichlerCocycle σ n D.signEichlerCocycle :=
  ⟨D.signEichlerCocycle_mul stages, eichlerCocycleTw_orthogonal D,
    eichlerCocycleTw_binaryValues D stages,
    fun m => ⟨liftVectorTw D stages m, liftVectorTw_smooth D stages m,
      liftVectorTw_realize D stages m, liftVectorTw_spherical D stages m⟩,
    fun A m => eichlerCocycleTw_scalar_smooth D stages m A,
    eichlerCocycleTw_finiteLevel D stages⟩

end EichlerInput

/-- **The sign-twisted Eichler cocycle exists** for every Eichler input. -/
theorem exists_signEichlerCocycle {σ : CuspidalRepresentation} {n : ℕ}
    (stages : AnalyticScalar.ContinuousStages σ) (D : EichlerInput σ n) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsSignEichlerCocycle σ n α :=
  ⟨D.signEichlerCocycle, D.signEichlerCocycle_spec stages⟩

/-- **The sign-twisted Eichler cocycle exists** for every spherical cuspidal representation with a
nonzero cohomology class of odd degree. -/
theorem exists_signEichlerCocycle_of_cohomological (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsSignEichlerCocycle σ n α := by
  obtain ⟨D⟩ := EichlerInput.nonempty_of_cohomological σ spherical odd cohomological
  exact exists_signEichlerCocycle stages D

end TernaryPeriodPolynomials.SourceConstruction

end
