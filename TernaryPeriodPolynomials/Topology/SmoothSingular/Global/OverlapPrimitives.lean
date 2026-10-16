module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OverlapResolutions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering

/-- Actual exactness supplies a literal primitive in a real cochain complex. -/
theorem complex_primitive_of_exactAt {C : CochainComplex (ModuleCat.{0} ℝ) ℕ} (n : ℕ)
    (he : C.ExactAt (n+1)) (w : C.X (n+1)) (hw : C.d (n+1) (n+2) w = 0) :
    ∃ z : C.X n, C.d n (n+1) z = w :=
  (ShortComplex.moduleCat_exact_iff _).mp
    ((exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).mp he) w hw

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual covering differential evaluates to its literal exterior-derivative map. -/
theorem coveringComplex_d_apply {U : Set OrbitSpace} (hU : IsOpen U) (p : ℕ)
    (w : EquivariantForm ρ U p) : (coveringComplex ρ hU).d p (p+1) w = differential ρ hU p w :=
  congrArg (fun f => f.hom w)
    (CochainComplex.of_d (fun n => ModuleCat.of ℝ (EquivariantForm ρ U n))
      (fun n => ModuleCat.ofHom (differential ρ hU n)) p)

/-- Every positive closed actual form on a genuine finite Čech overlap has an actual primitive. -/
theorem cechOverlap_form_primitive {n : ℕ} (t : Fin (n+1) → ConvexSheet) (p : ℕ)
    (w : EquivariantForm ρ (cechDomain ConvexSheet.quotientDomain t) (p+1))
    (hw : differential ρ (cechDomain_isOpen ConvexSheet.quotientDomain
      ConvexSheet.quotientDomain_isOpen t) (p+1) w = 0) :
    ∃ z : EquivariantForm ρ (cechDomain ConvexSheet.quotientDomain t) p,
      differential ρ (cechDomain_isOpen ConvexSheet.quotientDomain
        ConvexSheet.quotientDomain_isOpen t) p z = w := by
  have := cechOverlap_formAugmentation_quasiIso ρ t
  unfold coveringFormAugmentation at this
  have he := augmentation_target_exactAt
    (K := coveringComplex ρ (cechDomain_isOpen ConvexSheet.quotientDomain ConvexSheet.quotientDomain_isOpen t))
    (ModuleCat.ofHom (coefficientFormMap ρ (cechDomain_isOpen ConvexSheet.quotientDomain
      ConvexSheet.quotientDomain_isOpen t)))
    (coveringCoefficientForm_closed ρ _) p
  have hd : (coveringComplex ρ (cechDomain_isOpen ConvexSheet.quotientDomain
      ConvexSheet.quotientDomain_isOpen t)).d (p+1) (p+2) w = 0 :=
    (coveringComplex_d_apply ρ _ (p+1) w).trans hw
  obtain ⟨z,hz⟩ := complex_primitive_of_exactAt p he w hd
  exact ⟨z,(coveringComplex_d_apply ρ _ p z).symm.trans hz⟩

omit [FiniteDimensional ℝ F] in
/-- Every positive closed actual singular cochain on a genuine finite Čech overlap has an
actual singular cochain primitive. -/
theorem cechOverlap_singular_primitive {n : ℕ} (t : Fin (n+1) → ConvexSheet) (p : ℕ)
    (w : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).X (p+1))
    (hw : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d (p+1) (p+2) w = 0) :
    ∃ z, (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d p (p+1) z = w := by
  have := cechOverlap_singularAugmentation_quasiIso ρ t
  unfold coveringSingularAugmentation at this
  have he := augmentation_target_exactAt
    (K := coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t))
    (ModuleCat.ofHom (coefficientSingularMap ρ (cechDomain ConvexSheet.quotientDomain t)))
    (show ModuleCat.ofHom (coefficientSingularMap ρ (cechDomain ConvexSheet.quotientDomain t)) ≫
      (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d 0 1 = 0 from by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact coefficientSingularMap_closed ρ _) p
  exact complex_primitive_of_exactAt p he w hw

omit [FiniteDimensional ℝ F] in
/-- Every actual singular zero-cocycle on an overlap comes from an actual coefficient section. -/
theorem cechOverlap_singular_zero {n : ℕ} (t : Fin (n+1) → ConvexSheet)
    (w : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).X 0)
    (hw : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d 0 1 w = 0) :
    ∃ z, coefficientSingularMap ρ (cechDomain ConvexSheet.quotientDomain t) z = w := by
  have := cechOverlap_singularAugmentation_quasiIso ρ t
  exact (ShortComplex.moduleCat_exact_iff _).mp (coveringSingular_zero_exact ρ) w hw

end TernaryPoly.SmoothSingularGlobal
