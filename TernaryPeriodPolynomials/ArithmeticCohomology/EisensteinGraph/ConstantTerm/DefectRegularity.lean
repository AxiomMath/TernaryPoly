module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.FixedStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.HomogeneousFunctionals

@[expose] public section


/-!
# Regularity of the defect translation family

For `n ≥ 4` the defect family
`r ↦ (E c - c_side)(y)(atInfinity (u_side (K r)) * rationalGroup q⁻¹)`
of `Basic.lean` has the two regularity properties needed by the averaging argument:

* **cocycle law** in the rational vertex tuple `y`, for every `r`
  (`defectFamily_isCocycle₂`);
* **continuity** in `r` of every linear functional of the polynomial value, for every `y`
  (`defectFamily_functional_continuous`).

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

/-! ## Faces of real vertex tuples -/

theorem realVertices_face123 (x : Fin 4 → RationalGL3) :
    GlobalEisensteinCocycle.realVertices ![x 1, x 2, x 3] =
      ![GlobalEisensteinCocycle.realVertexTuple x 1, GlobalEisensteinCocycle.realVertexTuple x 2,
        GlobalEisensteinCocycle.realVertexTuple x 3] := by
  funext index
  fin_cases index <;> rfl

theorem realVertices_face023 (x : Fin 4 → RationalGL3) :
    GlobalEisensteinCocycle.realVertices ![x 0, x 2, x 3] =
      ![GlobalEisensteinCocycle.realVertexTuple x 0, GlobalEisensteinCocycle.realVertexTuple x 2,
        GlobalEisensteinCocycle.realVertexTuple x 3] := by
  funext index
  fin_cases index <;> rfl

theorem realVertices_face013 (x : Fin 4 → RationalGL3) :
    GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 3] =
      ![GlobalEisensteinCocycle.realVertexTuple x 0, GlobalEisensteinCocycle.realVertexTuple x 1,
        GlobalEisensteinCocycle.realVertexTuple x 3] := by
  funext index
  fin_cases index <;> rfl

theorem realVertices_face012 (x : Fin 4 → RationalGL3) :
    GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 2] =
      ![GlobalEisensteinCocycle.realVertexTuple x 0, GlobalEisensteinCocycle.realVertexTuple x 1,
        GlobalEisensteinCocycle.realVertexTuple x 2] := by
  funext index
  fin_cases index <;> rfl

/-! ## (A) The cocycle law in the vertex tuple -/

/-- The Eisenstein value at real vertices satisfies the four-term cocycle relation, at every
adelic argument. -/
theorem eisensteinValue_fourTerm (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (x : Fin 4 → RationalGL3) (g : AdelicGL) :
    eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 1, x 2, x 3]) g -
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 2, x 3]) g +
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 3]) g -
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 2]) g = 0 := by
  have h := PolynomialEisenstein.polynomialValue_source_closed D hol c
    (GlobalEisensteinCocycle.realVertexTuple x) g
  rw [← realVertices_face123, ← realVertices_face023, ← realVertices_face013,
    ← realVertices_face012] at h
  exact h

theorem sourceCocycle_isSource {D : InducingData n} {side : Side}
    (s : SourceSpace.sourceCocycles D side) : IsSourceCocycle D side s.val :=
  s.property

/-- A source cocycle satisfies the four-term relation at real vertices of a rational tuple. -/
theorem sourceCocycle_fourTerm {D : InducingData n} {side : Side}
    (s : SourceSpace.sourceCocycles D side) (x : Fin 4 → RationalGL3) (g : AdelicGL) :
    s.val (GlobalEisensteinCocycle.realVertices ![x 1, x 2, x 3]) g -
      s.val (GlobalEisensteinCocycle.realVertices ![x 0, x 2, x 3]) g +
      s.val (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 3]) g -
      s.val (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 2]) g = 0 := by
  have h := (sourceCocycle_isSource s).2.2.2 (GlobalEisensteinCocycle.realVertexTuple x) g
  rw [← realVertices_face123, ← realVertices_face023, ← realVertices_face013,
    ← realVertices_face012] at h
  exact h

theorem four_term_sub {V : Type} [AddCommGroup V] (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V)
    (ha : a₁ - a₂ + a₃ - a₄ = 0) (hb : b₁ - b₂ + b₃ - b₄ = 0) :
    (a₁ - b₁) - (a₂ - b₂) + (a₃ - b₃) - (a₄ - b₄) = 0 := by
  have e : (a₁ - b₁) - (a₂ - b₂) + (a₃ - b₃) - (a₄ - b₄) =
      (a₁ - a₂ + a₃ - a₄) - (b₁ - b₂ + b₃ - b₄) := by abel
  rw [e, ha, hb, sub_zero]

/-- **Cocycle law.** For every translation parameter `r` the defect family is a homogeneous
2-cocycle on rational vertex tuples. -/
theorem defectFamily_isCocycle₂ (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ) :
    IsCocycle₂ (defectFamily large D hol c side q K r) := by
  intro x
  simp only [defectFamily_eq]
  exact four_term_sub _ _ _ _ _ _ _ _ (eisensteinValue_fourTerm D hol c x _)
    (sourceCocycle_fourTerm (sideSource large D hol c side) x _)

/-! ## (B) Continuity in the translation parameter -/

theorem planeUnipotent_real_continuous :
    Continuous (fun p : ℝ × ℝ => (planeUnipotent p.1 p.2 : RealGL3)) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;>
    first
      | exact continuous_const
      | exact continuous_fst
      | exact continuous_snd
      | exact continuous_fst.neg
      | exact continuous_snd.neg

theorem lineUnipotent_real_continuous :
    Continuous (fun p : ℝ × ℝ => (lineUnipotent p.1 p.2 : RealGL3)) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;>
    first
      | exact continuous_const
      | exact continuous_fst
      | exact continuous_snd
      | exact continuous_fst.neg
      | exact continuous_snd.neg

theorem sideUnipotent_real_continuous (side : Side) (K : ℕ) :
    Continuous (fun r : ℝ × ℝ =>
      (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2) : RealGL3)) := by
  have hk : Continuous (fun r : ℝ × ℝ => (((K : ℝ) * r.1, (K : ℝ) * r.2) : ℝ × ℝ)) := by
    fun_prop
  cases side
  · exact planeUnipotent_real_continuous.comp hk
  · exact lineUnipotent_real_continuous.comp hk

/-- The adelic argument of the defect family is continuous in the translation parameter. -/
theorem defectArgument_continuous (side : Side) (q : RationalGL3) (K : ℕ) :
    Continuous (fun r : ℝ × ℝ =>
      atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) * rationalGroup q⁻¹) :=
  ((StandardConstruction.HilbertFixedStandard.atInfinity_continuous.comp
    (sideUnipotent_real_continuous side K))).mul continuous_const

/-- Continuity of each monomial coefficient of the defect family in the parameter. -/
theorem defectFamily_coeff_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) (m : Fin 3 →₀ ℕ) :
    Continuous (fun r : ℝ × ℝ =>
      (defectFamily large D hol c side q K r y).val.coeff m) := by
  have hg := defectArgument_continuous side q K
  have e : (fun r : ℝ × ℝ => (defectFamily large D hol c side q K r y).val.coeff m) =
      fun r : ℝ × ℝ =>
        (SectionSpace.sectionEisensteinValue D hol
          (PolynomialEisenstein.coefficientSection D m
            (PolynomialEisenstein.sourceSection D c
              (GlobalEisensteinCocycle.realVertices y)))).val
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        ((sideSource large D hol c side).val
          (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹)).val.coeff m := by
    funext r
    rw [defectFamily_eq, Submodule.coe_sub, MvPolynomial.coeff_sub]
    congr 1
    exact PolynomialNaturality.polynomialValue_coeff D hol
      (PolynomialEisenstein.sourceSection D c (GlobalEisensteinCocycle.realVertices y)) m _
  rw [e]
  exact ((sectionEisensteinValue_continuous D hol large _).comp hg).sub
    ((StandardConstruction.InducedContinuity.induced_continuous D side cohomologicalPoint _
      ((sourceCocycle_isSource (sideSource large D hol c side)).1
        (GlobalEisensteinCocycle.realVertices y) m)).comp hg)

/-- **Continuity.** Every linear functional of the defect family is continuous in the
translation parameter, at every rational vertex tuple. -/
theorem defectFamily_functional_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3)
    (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun r : ℝ × ℝ => μ (defectFamily large D hol c side q K r y)) := by
  obtain ⟨weight, hweight⟩ := FlagExactness.homogeneous_functional_eq_sum n μ
  simp_rw [hweight]
  exact continuous_finsetSum _ (fun s _ =>
    (defectFamily_coeff_continuous large D hol c side q K y s.val).mul continuous_const)

/-- Both regularity properties of the defect translation family. -/
theorem defectFamily_regularity (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) :
    (∀ r : ℝ × ℝ, IsCocycle₂ (defectFamily large D hol c side q K r)) ∧
      ∀ (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ),
        Continuous (fun r : ℝ × ℝ => μ (defectFamily large D hol c side q K r y)) :=
  ⟨defectFamily_isCocycle₂ large D hol c side q K,
    defectFamily_functional_continuous large D hol c side q K⟩

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
