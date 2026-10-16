module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CochainEntry
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Weight
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceQuotient

@[expose] public section


/-!
# The conditional class-level entry comparison (ML4b, step (b))

`classLevel_conditional` is an **intermediate, CONDITIONAL result, not the completion** of ML4b.  Given a map `T` that
realizes the standard operator (`RealizesStandardConv`), the standard integral of the plane integral cochain
`cOmega` (Entry/CochainEntry) is computed by R-c (`StandardEndpointIntegral`), R-e (`FiniteEntryIdentity D ι ιL F r`) and the
real core (`standardIntegral_cOmega`): `J(s₀) = r · 2πi/(n+1) · c_Σ`.  Hence, if `cOmega` is a source cocycle (R-a) and
the integral cochains `cOmega`, `cSigma` define the same classes as `planeSource D E`, `lineSource D E'` (R-b), then
`T [planeSource D E] = c · [lineSource D E']` with `c = r · 2πi/(n+1) ≠ 0`.

Hypotheses: `hRa` (R-a), `hRbP`, `hRbL` (R-b), `hRc` (proved for `4 ≤ n`, `Entry/RCEndpoint`), `hRe`
(R-e).

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section
namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The scalar relating `J(s₀)` to the line integral cochain: `-r · c_∞ = r · 2πi/(n+1)`. -/
def entryScalar (n : ℕ) (r : ℂ) : ℂ := -r * (-2 * Real.pi * Complex.I / ((n : ℂ) + 1))

theorem entryScalar_ne_zero (n : ℕ) {r : ℂ} (hr : r ≠ 0) : entryScalar n r ≠ 0 := by
  unfold entryScalar
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine mul_ne_zero (neg_ne_zero.mpr hr) ?_
  refine div_ne_zero ?_ hn
  simp [hpi, Complex.I_ne_zero]

theorem coeff_cOmega (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((cOmega n D F y g : HomogeneousPoly n) : Poly).coeff κ =
      if κ.degree = n then cOmegaCoeff n D F y g κ else 0 := coeff_ofCoeffs n _ κ

theorem coeff_cSigma (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    ((cSigma n D F y g : HomogeneousPoly n) : Poly).coeff κ =
      if κ.degree = n then cSigmaCoeff n D F y g κ else 0 := coeff_ofCoeffs n _ κ

/-- **CONDITIONAL class-level entry comparison (ML4b, step (b)); an intermediate, not the completion.**
Hypotheses (all explicit): `hRc` (R-c, `StandardEndpointIntegral`), `hRe` (R-e, `FiniteEntryIdentity D ι ιL F r`,
`r ≠ 0`, required only on the support of the line weight `ιL`), `hRa` (R-a: the weighted plane integral cochain
`ι · cOmega` is a source cocycle), and the two class identifications `hRbP`, `hRbL` (R-b: `ι·cOmega` and `ι·planeSource`,
`ιL·cSigma` and `ιL·lineSource` define the same class).  Conclusion: any `T` realizing the standard operator sends the
class of `ι · planeSource D E` to a class represented by a line source cocycle `J` (the standard integral cochain) whose
`ιL`-component is `entryScalar n r = r · 2πi/(n+1) ≠ 0` times the `ιL`-component of `lineSource D E'`:
`J = entryScalar n r · c_Σ` on the support of `ιL`, and `[ιL · J] = entryScalar n r · [ιL · lineSource D E']`.  (`ιL = 1` is the whole spherical line section; `ιL` the indicator of the
good-line orbit gives the good-line component of the bad-plane section.) -/
theorem classLevel_conditional (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (ι ιL : AdelicGL → ℂ)
    (hι : ∀ g g' : AdelicGL, finiteGroup g = finiteGroup g' → ι g = ι g') (hιL : LineWeight ιL)
    (E : LeviCocycleData D.cusp n) (E' : LineLeviCocycleData D.cusp n) (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line) (hT : RealizesStandardConv D T)
    (hRc : StandardEndpointIntegral n) (r : ℂ) (hr : r ≠ 0) (hRe : FiniteEntryIdentity D ι ιL F r)
    (hRa : IsSourceCocycle D .plane (fun y g => ι g • cOmega n D F y g))
    (hRbP : ∀ hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g),
      SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • cOmega n D F y g, hRa⟩ =
        SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩)
    (hRbL : ∀ (hSig : IsSourceCocycle D .line (fun y g => ιL g • cSigma n D F y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • cSigma n D F y g, hSig⟩ =
        SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • lineSource D E' y g, hls⟩) :
    entryScalar n r ≠ 0 ∧ ∀ (hps : IsSourceCocycle D .plane (fun y g => ι g • planeSource D E y g))
      (hls : IsSourceCocycle D .line (fun y g => ιL g • lineSource D E' y g)),
      ∃ J : SourceSpace.sourceCocycles D .line,
        T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩) =
          SourceQuotient.sourceToSummand D .line J ∧
        (∀ y g, ιL g ≠ 0 → J.val y g = entryScalar n r • cSigma n D F y g) ∧
        ∃ hJ : IsSourceCocycle D .line (fun y g => ιL g • J.val y g),
          SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • J.val y g, hJ⟩ =
            entryScalar n r • SourceQuotient.sourceToSummand D .line
              ⟨fun y g => ιL g • lineSource D E' y g, hls⟩ := by
  let plane : SourceSpace.sourceCocycles D .plane := ⟨fun y g => ι g • cOmega n D F y g, hRa⟩
  have hex := (realizesStandardConv_iff D T).mp hT plane
  obtain ⟨line, hrel, hTval⟩ := hex
  obtain ⟨ext, cont, flat, endpoint, conv, regular, lineEndpoint⟩ := hrel
  have hext : ∀ x g, ext cohomologicalPoint x g = ι g • cOmega n D F x g := fun x g =>
    congrFun (congrFun endpoint x) g
  have hRc' := hRc D ext cont flat conv regular
  -- the continuation at the cohomological point is `entryScalar • cSigma` on the support of `ιL`
  have hJ : ∀ x g, ιL g ≠ 0 → cont cohomologicalPoint x g = entryScalar n r • cSigma n D F x g := by
    intro x g hg
    apply Subtype.ext
    apply MvPolynomial.ext
    intro κ
    have hobtain1 := hRc' x g κ
    obtain ⟨hI, hE⟩ := hobtain1
    rw [Submodule.coe_smul, MvPolynomial.coeff_smul, coeff_cSigma, smul_eq_mul]
    unfold entryScalar
    by_cases hdeg : κ.degree = n
    · rw [ite_eq_left hdeg, hE]
      have hint : Integrable (fun u : Adeles × Adeles =>
          ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) *
            cOmegaCoeff n D F x (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ) radicalMeasure := by
        refine hI.congr (Filter.Eventually.of_forall fun u => ?_)
        simp only [standardIntegrand, hext, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul,
          coeff_cOmega, ite_eq_left hdeg]
      rw [← standardIntegral_cOmega n (by omega) D ι ιL hι F holomorphic decay r hRe x g hg κ hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [standardIntegrand, hext, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul,
        coeff_cOmega, ite_eq_left hdeg]
    · rw [ite_eq_right hdeg, mul_zero]
      have h0 : ((cont cohomologicalPoint x g : HomogeneousPoly n) : Poly).coeff κ = 0 :=
        ((MvPolynomial.mem_homogeneousSubmodule n _).mp (cont cohomologicalPoint x g).2).coeff_eq_zero hdeg
      exact h0
  have hsc : entryScalar n r ≠ 0 := entryScalar_ne_zero n hr
  have hline : ∀ x g, ιL g ≠ 0 → line.val x g = entryScalar n r • cSigma n D F x g := by
    intro x g hg
    have := lineEndpoint
    rw [← congrFun (congrFun lineEndpoint x) g]
    exact hJ x g hg
  have hwline : (fun y g => ιL g • line.val y g) =
      fun y g => entryScalar n r • (ιL g • cSigma n D F y g) := by
    funext y g
    by_cases hg : ιL g = 0
    · simp [hg]
    · rw [hline y g hg, smul_comm]
  have hLine : IsSourceCocycle D .line (fun y g => ιL g • line.val y g) :=
    isSourceCocycle_smul_lineWeight D hιL _ line.property
  have hSig : IsSourceCocycle D .line (fun y g => ιL g • cSigma n D F y g) := by
    have := SourceSpace.source_smul D .line (entryScalar n r)⁻¹ _ hLine
    refine (funext fun y => funext fun g => ?_ :
      (fun y g => (entryScalar n r)⁻¹ • (ιL g • line.val y g)) = fun y g => ιL g • cSigma n D F y g) ▸ this
    show (entryScalar n r)⁻¹ • (ιL g • line.val y g) = _
    rw [show ιL g • line.val y g = entryScalar n r • (ιL g • cSigma n D F y g) from
      congrFun (congrFun hwline y) g, smul_smul, inv_mul_cancel₀ hsc, one_smul]
  refine ⟨hsc, fun hps hls => ⟨line, ?_, hline, hLine, ?_⟩⟩
  · calc T (SourceQuotient.sourceToSummand D .plane ⟨fun y g => ι g • planeSource D E y g, hps⟩)
        = T (SourceQuotient.sourceToSummand D .plane plane) := congrArg T (hRbP hps).symm
      _ = SourceQuotient.sourceToSummand D .line line := hTval
  · have hl : (⟨fun y g => ιL g • line.val y g, hLine⟩ : SourceSpace.sourceCocycles D .line) =
        entryScalar n r • (⟨fun y g => ιL g • cSigma n D F y g, hSig⟩ : SourceSpace.sourceCocycles D .line) :=
      Subtype.ext hwline
    calc SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • line.val y g, hLine⟩
        = entryScalar n r • SourceQuotient.sourceToSummand D .line ⟨fun y g => ιL g • cSigma n D F y g, hSig⟩ := by
          exact (congrArg (SourceQuotient.sourceToSummand D .line) hl).trans
            (LinearMap.map_smul (SourceQuotient.sourceToSummand D .line) (entryScalar n r) _)
      _ = entryScalar n r • SourceQuotient.sourceToSummand D .line
            ⟨fun y g => ιL g • lineSource D E' y g, hls⟩ :=
          congrArg (fun z => entryScalar n r • z) (hRbL hSig hls)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
