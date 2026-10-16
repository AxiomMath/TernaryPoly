module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Comparison

@[expose] public section


/- Ported from AxiomDeep (Claude Opus 5.5). -/
open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.GraphPieces.FlatExtensions

theorem smooth_zero {dimension count : ℕ} {Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] :
    Smooth (fun (_ : Fin count → Matrix.GeneralLinearGroup (Fin dimension) ℝ) =>
      (0 : Value)) := by
  exact contDiffOn_const

theorem smoothCuspLift_zero {degree count : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) :
    HasSmoothCuspLift data side parameter
      (fun (_ : Fin count → RealGL3) (_ : AdelicGL) => (0 : ℂ)) := by
  intro argument
  refine ⟨fun _ => 0, smooth_zero, ?_⟩
  intro vertices binaryElement
  simp

theorem induced_zero {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) : IsInduced data side parameter (fun _ => 0) := by
  refine ⟨fun _ => smooth_zero, fun _ _ => rfl,
    smoothCuspLift_zero data side parameter, ?_⟩
  cases side <;> refine ⟨fun _ _ _ => rfl, ?_, ?_⟩
  · intro scalar argument
    simp
  · intro argument
    change (fun (_ : BinaryAdelicGL) => _ * 0) ∈ cuspFunctions data.cusp
    simpa only [mul_zero, Pi.zero_def] using (cuspFunctions data.cusp).zero_mem
  · intro scalar argument
    simp
  · intro argument
    change (fun (_ : BinaryAdelicGL) => _ * 0) ∈ cuspFunctions data.cusp
    simpa only [mul_zero, Pi.zero_def] using (cuspFunctions data.cusp).zero_mem

theorem flat_zero {degree : ℕ} (data : InducingData degree) :
    IsFlatSection data (fun _ _ => 0) := by
  refine ⟨fun parameter => induced_zero data .plane parameter,
    fun _ _ => analyticAt_const, ?_⟩
  intro parameter binaryElement compactElement compactMembership
  simp

theorem eisensteinContinuation_zero :
    IsEisensteinContinuation (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun _ _ => analyticAt_const.meromorphicAt, 0, ?_⟩
  intro parameter halfPlane argument
  exact hasSum_zero

theorem standardContinuation_zero :
    IsStandardContinuation (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun _ _ => analyticAt_const.meromorphicAt, 0, ?_⟩
  intro parameter halfPlane argument
  exact ⟨integrable_zero _ _ _, (integral_zero _ _).symm⟩

def degreeMonomials (degree : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (Finsupp.finite_of_degree_eq degree).toFinset

theorem mem_degreeMonomials (degree : ℕ) (monomial : Fin 3 →₀ ℕ) :
    monomial ∈ degreeMonomials degree ↔ Finsupp.degree monomial = degree := by
  exact Set.Finite.mem_toFinset _

def assemblePolynomial (degree : ℕ) (coefficients : (Fin 3 →₀ ℕ) → ℂ) :
    HomogeneousPoly degree :=
  ⟨∑ monomial ∈ degreeMonomials degree, MvPolynomial.monomial monomial (coefficients monomial),
    MvPolynomial.IsHomogeneous.sum _ _ _ (by
      intro monomial membership
      exact MvPolynomial.isHomogeneous_monomial _
        ((mem_degreeMonomials degree monomial).mp membership))⟩

theorem assemblePolynomial_coeff (degree : ℕ) (coefficients : (Fin 3 →₀ ℕ) → ℂ)
    (monomial : Fin 3 →₀ ℕ) :
    (assemblePolynomial degree coefficients).val.coeff monomial =
      if Finsupp.degree monomial = degree then coefficients monomial else 0 := by
  classical
  simp [assemblePolynomial, MvPolynomial.coeff_monomial,
    mem_degreeMonomials]

theorem assemblePolynomial_original (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    assemblePolynomial degree (fun monomial => polynomial.val.coeff monomial) =
      polynomial := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [assemblePolynomial_coeff]
  split_ifs with homogeneous
  · rfl
  · exact (polynomial.property.coeff_eq_zero homogeneous).symm

theorem source_flatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) :
    ∃ extension : ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree,
      (∀ vertices monomial, IsFlatSection data
        (fun parameter argument =>
          (extension parameter vertices argument).val.coeff monomial)) ∧
      extension cohomologicalPoint = source := by
  classical
  have extensions : ∀ vertices monomial, ∃ extension,
      IsFlatSection data extension ∧ extension cohomologicalPoint =
        (fun argument => (source vertices argument).val.coeff monomial) := by
    intro vertices monomial
    exact holomorphic.1 _ (isSource.1 vertices monomial)
  choose scalarExtensions flat realizes using extensions
  refine ⟨fun parameter vertices argument => assemblePolynomial degree
    (fun monomial => scalarExtensions vertices monomial parameter argument), ?_, ?_⟩
  · intro vertices monomial
    by_cases homogeneous : Finsupp.degree monomial = degree
    · simpa only [assemblePolynomial_coeff, ite_eq_left homogeneous] using flat vertices monomial
    · simpa only [assemblePolynomial_coeff, ite_eq_right homogeneous] using flat_zero data
  · funext vertices argument
    simpa only [realizes] using assemblePolynomial_original degree (source vertices argument)

theorem source_eisensteinContinuation {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) :
    ∃ extension continuation :
        ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree,
      (∀ vertices monomial, IsFlatSection data
        (fun parameter argument =>
          (extension parameter vertices argument).val.coeff monomial)) ∧
      extension cohomologicalPoint = source ∧
      (∀ vertices monomial, IsEisensteinContinuation
        (fun parameter argument =>
          (extension parameter vertices argument).val.coeff monomial)
        (fun parameter argument =>
          (continuation parameter vertices argument).val.coeff monomial)) ∧
      (∀ vertices argument monomial, AnalyticAt ℂ
        (fun parameter => (continuation parameter vertices argument).val.coeff monomial) cohomologicalPoint) := by
  classical
  obtain ⟨extension, flat, realizes⟩ := source_flatExtension data holomorphic source isSource
  have continuations : ∀ vertices monomial, ∃ continuation,
      IsEisensteinContinuation
        (fun parameter argument => (extension parameter vertices argument).val.coeff monomial) continuation ∧
      ∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument)
        cohomologicalPoint := by
    intro vertices monomial
    exact holomorphic.2 _ (flat vertices monomial)
  choose scalarContinuations continues regular using continuations
  refine ⟨extension, fun parameter vertices argument => assemblePolynomial degree
    (fun monomial => scalarContinuations vertices monomial parameter argument),
    flat, realizes, ?_, ?_⟩
  · intro vertices monomial
    by_cases homogeneous : Finsupp.degree monomial = degree
    · simpa only [assemblePolynomial_coeff, ite_eq_left homogeneous] using
        continues vertices monomial
    · have coefficientZero : ∀ parameter argument,
          (extension parameter vertices argument).val.coeff monomial = 0 := by
        intro parameter argument
        exact (extension parameter vertices argument).property.coeff_eq_zero homogeneous
      simpa only [assemblePolynomial_coeff, ite_eq_right homogeneous, coefficientZero] using
        eisensteinContinuation_zero
  · intro vertices argument monomial
    by_cases homogeneous : Finsupp.degree monomial = degree
    · simpa only [assemblePolynomial_coeff, ite_eq_left homogeneous] using
        regular vertices monomial argument
    · simpa only [assemblePolynomial_coeff, ite_eq_right homogeneous] using
        (analyticAt_const : AnalyticAt ℂ (fun (_ : ℂ) => (0 : ℂ)) cohomologicalPoint)

end TernaryPeriodPolynomials.GraphPieces.FlatExtensions
