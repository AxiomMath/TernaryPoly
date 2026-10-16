module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormAugmentation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LinearPrimitives

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Manifold ContDiff

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- Positive actual finite-support Čech rows are exact, with the genuine partition homotopy
as primitive. All support assertions are proved for the actual family, not assumed. -/
theorem finiteFormCech_positive_exact (n k : ℕ)
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+2))
    (hw : (familySupport w).Finite)
    (hd : formCechD ρ (fun i => (C.sheet i).quotientDomain) n (k+2) w = 0) :
    ∃ z : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1),
      (familySupport z).Finite ∧ formCechD ρ (fun i => (C.sheet i).quotientDomain) n (k+1) z = w := by
  obtain ⟨φ,hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) (by rw [C.covers])
  exact ⟨formCechH ρ _ n (fun i => (C.sheet i).quotientDomain_isOpen) φ hφ (k+1) w,
    formCechH_finiteSupport ρ C n (k+1) φ hφ w hw,
    formCech_primitive ρ _ n (fun i => (C.sheet i).quotientDomain_isOpen) φ hφ k w hd⟩

/-- Every finite-support actual Čech zero-cocycle is the literal restriction of a genuinely
quotient-compact global form. -/
theorem finiteFormCech_zero_exact (n : ℕ)
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n 1)
    (hw : (familySupport w).Finite)
    (hd : formCechD ρ (fun i => (C.sheet i).quotientDomain) n 1 w = 0) :
    ∃ z : CompactSupportForm ρ Set.univ n,
      formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n z.val = w := by
  obtain ⟨φ,hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates)
    isClosed_univ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) (by rw [C.covers])
  have he := formCechAugmentationMap_exact ρ (fun i => (C.sheet i).quotientDomain) n
    (fun i => (C.sheet i).quotientDomain_isOpen) φ hφ
  have hd' : (formCechComplex ρ (fun i => (C.sheet i).quotientDomain) n).d 0 1 w = 0 :=
    (congrArg (fun f => f.hom w) (formCechD_eq_complex ρ _ n 0)).symm.trans hd
  obtain ⟨z,hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp he w hd'
  refine ⟨⟨z,compactSupport_of_formCechAugmentationMap_finiteSupport ρ C n z ?_⟩,hz⟩
  simpa only [hz] using hw

/-- Actual positive overlap primitives preserve finite tuple support on this genuine cover. -/
theorem finiteFormCech_column_exact (n k : ℕ)
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) (n+1) (k+1))
    (hw : (familySupport w).Finite)
    (hd : ∀ t, differential ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) t) (n+1) (w t) = 0) :
    ∃ z : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1),
      (familySupport z).Finite ∧ ∀ t,
        differential ρ (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen) t) n (z t) = w t := by
  apply finiteFamily_primitive _ (fun t => differential ρ
    (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) t) n) w hw
  intro t
  exact cechOverlap_form_primitive_zero ρ (C.sheet ∘ t) n (w t) (hd t)

end TernaryPoly.SmoothSingularGlobal
