module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.OrbitData

@[expose] public section


/-!
# (C), step 10: the printed intertwiner `∫_{𝔸²} φ(w₀⁻¹u(s,t)) ds dt` is the orbit sum `lineA1K`

Formalized by Claude Sonnet 5.5.

For the adelic induced section of the seed `h = f ∘ ofComplex` of a cusp form `f` of weight `n + 3` on `Γ₂(N)`
(`N ≥ 3`, `n ≥ 4`), the literal integral over `𝔸²` for the Haar measure `radicalMeasure` of the coordinates
`(x; e_p, e_q)`, coefficient `m`, of the standard line face is absolutely convergent and equals
`Σ_o ∫_{ℝ²} PhiQ0(c_o)(N v) dv = lineA1K N 1 n f false x p q m`, the explicit coefficient of the radical average computed:
* `Fz_integral`: the integral in the regrouped coordinates (finite congruence cells × real plane);
* `printed_intertwiner_eval`: the same over `radicalMeasure`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The cell of the free orbit `o` in the regrouped space `𝔸_f² × ℝ²`. -/
def Spiece (o : FreeOrb N) : Set ((FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) := pieceFin N o ×ˢ Set.univ

theorem Spiece_measurable (o : FreeOrb N) : MeasurableSet (Spiece N o) :=
  (pieceFin_measurable N o).prod MeasurableSet.univ

theorem real_pieceFin (o : FreeOrb N) : (finiteMeasure.prod finiteMeasure).real (pieceFin N o) = ((N : ℝ) ^ 2)⁻¹ := by
  unfold Measure.real
  rw [volume_pieceFin, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  ring

theorem setIntegral_piece_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (o : FreeOrb N)
    (g : (Fin 2 → ℝ) → E) :
    ∫ z in Spiece N o, g z.2 ∂((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) =
      ((N : ℝ) ^ 2)⁻¹ • ∫ w, g w := by
  unfold Spiece
  rw [← Measure.prod_restrict, Measure.restrict_univ, integral_fun_snd]
  congr 1
  rw [← real_pieceFin N o]
  simp [Measure.real]

theorem integrableOn_piece_snd (o : FreeOrb N) {E : Type*} [NormedAddCommGroup E] {g : (Fin 2 → ℝ) → E}
    (hg : Integrable g) :
    IntegrableOn (fun z => g z.2) (Spiece N o)
      ((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) := by
  unfold Spiece IntegrableOn
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have : IsFiniteMeasure ((finiteMeasure.prod finiteMeasure).restrict (pieceFin N o)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_pieceFin]
        exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simp [NeZero.pos])) (ENNReal.inv_lt_top.2 (by simp [NeZero.pos]))⟩
  exact hg.comp_snd _

variable {N n f}

/-- **The integral of the regrouped integrand**: absolutely convergent, and the sum over the free orbits of the real
integrals of the orbit summands (each cell has volume `N⁻²`). -/
theorem Fz_integral (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    Integrable (Fz N n f x p q m) ((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) ∧
    ∫ z, Fz N n f x p q m z ∂((finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ))) =
      ∑' o : FreeOrb N, ∫ v : Fin 2 → ℝ, phiO N n f x p q m o ((N : ℝ) • v) := by
  set ν := (finiteMeasure.prod finiteMeasure).prod (volume : Measure (Fin 2 → ℝ)) with hν
  have hdisj : Pairwise (Function.onFun Disjoint (Spiece N)) := fun o o' h =>
    Set.disjoint_prod.2 (Or.inl (pieceFin_disjoint N hN h))
  have hon : ∀ o, ∀ z ∈ Spiece N o, Fz N n f x p q m z = phiO N n f x p q m o (shiftV (orbPt N o) z.2) :=
    fun o z hz => Fz_on_piece N n f hN hx p q m o hz.1 z.2
  have hG : ∀ o, Integrable (fun w => phiO N n f x p q m o (shiftV (orbPt N o) w)) := fun o =>
    (integrable_shiftV _ _).2 (phiO_integrable N n f hn hx p q m o)
  have hInt : ∀ o, IntegrableOn (Fz N n f x p q m) (Spiece N o) ν := fun o =>
    (integrableOn_piece_snd N o (hG o)).congr_fun (fun z hz => (hon o z hz).symm) (Spiece_measurable N o)
  have hnorm : ∀ o, ∫ z in Spiece N o, ‖Fz N n f x p q m z‖ ∂ν = ∫ v, ‖phiO N n f x p q m o ((N : ℝ) • v)‖ := by
    intro o
    calc ∫ z in Spiece N o, ‖Fz N n f x p q m z‖ ∂ν
        = ∫ z in Spiece N o, (fun w => ‖phiO N n f x p q m o (shiftV (orbPt N o) w)‖) z.2 ∂ν :=
          setIntegral_congr_fun (Spiece_measurable N o) (fun z hz => by simp only [hon o z hz])
      _ = ((N : ℝ) ^ 2)⁻¹ • ∫ w, ‖phiO N n f x p q m o (shiftV (orbPt N o) w)‖ := setIntegral_piece_snd N o (fun w => ‖phiO N n f x p q m o (shiftV (orbPt N o) w)‖)
      _ = ((N : ℝ) ^ 2)⁻¹ • ∫ v, ‖phiO N n f x p q m o v‖ := by
          rw [integral_shiftV (orbPt N o) (fun v => ‖phiO N n f x p q m o v‖)]
      _ = _ := by rw [integral_norm_phiO, smul_eq_mul]
  have hUnion : IntegrableOn (Fz N n f x p q m) (⋃ o, Spiece N o) ν :=
    integrableOn_iUnion_of_summable_integral_norm hInt (by
      simp_rw [hnorm]; exact phiO_norm_summable N n f hn hx p q m)
  have hzero : ∀ z, z ∉ (⋃ o, Spiece N o) → Fz N n f x p q m z = 0 := by
    intro z hz
    by_cases hd : ∃ π κ, IsDecomp N (gFin z.1) π κ
    · obtain ⟨o, ho⟩ := exists_orbit_of_decomp N z.1 hd
      exact absurd (show z ∈ ⋃ o, Spiece N o from Set.mem_iUnion.2 ⟨o, ho, trivial⟩) hz
    · exact Fz_eq_zero_of_not N n f x p q m z.1 z.2 hd
  refine ⟨hUnion.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_iUnion (Spiece_measurable N) hdisj hUnion]
  refine tsum_congr fun o => ?_
  calc ∫ z in Spiece N o, Fz N n f x p q m z ∂ν
      = ∫ z in Spiece N o, (fun w => phiO N n f x p q m o (shiftV (orbPt N o) w)) z.2 ∂ν :=
        setIntegral_congr_fun (Spiece_measurable N o) (fun z hz => hon o z hz)
    _ = ((N : ℝ) ^ 2)⁻¹ • ∫ w, phiO N n f x p q m o (shiftV (orbPt N o) w) :=
        setIntegral_piece_snd N o (fun w => phiO N n f x p q m o (shiftV (orbPt N o) w))
    _ = ((N : ℝ) ^ 2)⁻¹ • ∫ v, phiO N n f x p q m o v := by rw [integral_shiftV (orbPt N o) (phiO N n f x p q m o)]
    _ = _ := by
        rw [integral_phiO, Complex.real_smul]
        push_cast
        rfl

end TernaryPeriodPolynomials.Argument.FormClassK
