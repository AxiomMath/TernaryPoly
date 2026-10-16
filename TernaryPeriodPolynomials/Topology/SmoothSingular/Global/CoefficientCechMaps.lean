module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientCech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularCechBicomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormAugmentation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

section Forms
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i))

/-- The literal coefficient augmentation on every intersection, in smooth degree zero. -/
def coefficientCechToForms (k : ℕ) : CoefficientCechTerms ρ U k →ₗ[ℝ] FormCechTerms ρ U 0 k :=
  LinearMap.pi (fun t => (coefficientFormMap ρ (cechDomain_isOpen U hU t)).comp (LinearMap.proj t))

/-- Actual coefficient augmentation commutes with every actual Čech tuple restriction. -/
theorem coefficientCechToForms_select {p q : ℕ} (f : Fin p → Fin q)
    (w : CoefficientCechTerms ρ U p) :
    formCechSelect ρ U 0 f (coefficientCechToForms ρ U hU p w) =
      coefficientCechToForms ρ U hU q (coefficientCechSelect ρ U f w) := by
  funext t
  exact coefficientForm_restrict ρ (cechDomain_isOpen U hU (t ∘ f))
    (cechDomain_isOpen U hU t) (cechDomain_select_subset U f t) (w (t ∘ f))

/-- The actual coefficient-to-form map commutes with the complete alternating Čech sum. -/
theorem coefficientCechToForms_d (p : ℕ) (w : CoefficientCechTerms ρ U (p+1)) :
    formCechD ρ U 0 (p+1) (coefficientCechToForms ρ U hU (p+1) w) =
      coefficientCechToForms ρ U hU (p+2)
        ((∑ i : Fin (p+2), (-1 : ℤ)^i.val • coefficientCechSelect ρ U i.succAbove) w) := by
  simp only [formCechD,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  exact Finset.sum_congr rfl fun (i : Fin (p+2)) _ => congrArg (fun z => (-1 : ℤ)^i.val • z)
    (coefficientCechToForms_select ρ U hU i.succAbove w)

/-- The common coefficient Čech complex maps into smooth vertical degree zero by literal
coefficient augmentation. -/
def coefficientFormCechChain : coefficientCechComplex ρ U ⟶ (formCechBicomplex ρ U hU).flip.X 0 where
  f p := ModuleCat.ofHom (coefficientCechToForms ρ U hU (p+1))
  comm' p q hpq := by
    obtain rfl : q = p+1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change horizontal (formCechBicomplex ρ U hU) p 0 (coefficientCechToForms ρ U hU (p+1) w) =
      coefficientCechToForms ρ U hU (p+2) (((coefficientCechComplex ρ U).d p (p+1)).hom w)
    have hh := congrArg (fun f : FormCechTerms ρ U 0 (p+1) →ₗ[ℝ] FormCechTerms ρ U 0 (p+2) =>
      f (coefficientCechToForms ρ U hU (p+1) w)) (formCechBicomplex_horizontal ρ U hU p 0)
    have hc := congrArg (fun f : CoefficientCechTerms ρ U (p+1) →ₗ[ℝ] CoefficientCechTerms ρ U (p+2) =>
      coefficientCechToForms ρ U hU (p+2) (f w)) (coefficientCechComplex_d ρ U p)
    exact hh.trans ((coefficientCechToForms_d ρ U hU p w).trans hc.symm)

/-- The smooth coefficient augmentation is killed by the true exterior derivative. -/
theorem coefficientFormCechChain_vertical : coefficientFormCechChain ρ U hU ≫
    (formCechBicomplex ρ U hU).flip.d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change vertical (formCechBicomplex ρ U hU) p 0 (coefficientCechToForms ρ U hU (p+1) w) = 0
  rw [formCechBicomplex_vertical]
  funext t
  exact coefficientForm_closed ρ (cechDomain_isOpen U hU t) (w t)

/-- The actual vertical augmentation of the Čech–de Rham bicomplex by the common coefficients. -/
def coefficientFormTotalAugmentation :
    TotalAugmentation (coefficientCechComplex ρ U) (formCechBicomplex ρ U hU).flip where
  map := coefficientFormCechChain ρ U hU
  horizontal_zero := coefficientFormCechChain_vertical ρ U hU

end Forms
section Singular
variable {F : Type} [AddCommGroup F] [Module ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Set OrbitSpace)

/-- The literal coefficient augmentation on every intersection, in singular degree zero. -/
def coefficientCechToSingular (k : ℕ) : CoefficientCechTerms ρ U k →ₗ[ℝ] SingularCechTerms ρ U 0 k :=
  LinearMap.pi (fun t => (coefficientSingularMap ρ (cechDomain U t)).comp (LinearMap.proj t))

theorem coefficientCechToSingular_select {p q : ℕ} (f : Fin p → Fin q)
    (w : CoefficientCechTerms ρ U p) :
    singularCechSelect ρ U f 0 (coefficientCechToSingular ρ U p w) =
      coefficientCechToSingular ρ U q (coefficientCechSelect ρ U f w) := by
  funext t
  exact coefficientSingularMap_restrict ρ (cechDomain_select_subset U f t) (w (t ∘ f))

/-- The actual coefficient-to-singular map commutes with the full alternating Čech sum. -/
theorem coefficientCechToSingular_d (p : ℕ) (w : CoefficientCechTerms ρ U (p+1)) :
    (∑ i : Fin (p+2), (-1 : ℤ)^i.val • singularCechSelect ρ U i.succAbove 0)
      (coefficientCechToSingular ρ U (p+1) w) =
      coefficientCechToSingular ρ U (p+2)
        ((∑ i : Fin (p+2), (-1 : ℤ)^i.val • coefficientCechSelect ρ U i.succAbove) w) := by
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  exact Finset.sum_congr rfl fun (i : Fin (p+2)) _ => congrArg (fun z => (-1 : ℤ)^i.val • z)
    (coefficientCechToSingular_select ρ U i.succAbove w)

/-- The same actual common coefficient Čech complex maps into singular vertical degree zero. -/
def coefficientSingularCechChain : coefficientCechComplex ρ U ⟶ (singularCechBicomplex ρ U).flip.X 0 where
  f p := ModuleCat.ofHom (coefficientCechToSingular ρ U (p+1))
  comm' p q hpq := by
    obtain rfl : q = p+1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change horizontal (singularCechBicomplex ρ U) p 0 (coefficientCechToSingular ρ U (p+1) w) =
      coefficientCechToSingular ρ U (p+2) (((coefficientCechComplex ρ U).d p (p+1)).hom w)
    have hh := congrArg (fun f : SingularCechTerms ρ U 0 (p+1) →ₗ[ℝ] SingularCechTerms ρ U 0 (p+2) =>
      f (coefficientCechToSingular ρ U (p+1) w)) (singularCechBicomplex_horizontal ρ U p 0)
    have hc := congrArg (fun f : CoefficientCechTerms ρ U (p+1) →ₗ[ℝ] CoefficientCechTerms ρ U (p+2) =>
      coefficientCechToSingular ρ U (p+2) (f w)) (coefficientCechComplex_d ρ U p)
    exact hh.trans ((coefficientCechToSingular_d ρ U p w).trans hc.symm)

/-- The singular coefficient augmentation is killed by the true singular coboundary. -/
theorem coefficientSingularCechChain_vertical : coefficientSingularCechChain ρ U ≫
    (singularCechBicomplex ρ U).flip.d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change vertical (singularCechBicomplex ρ U) p 0 (coefficientCechToSingular ρ U (p+1) w) = 0
  rw [singularCechBicomplex_vertical]
  funext t
  exact coefficientSingularMap_closed ρ (cechDomain U t) (w t)

/-- The actual vertical augmentation of the Čech–singular bicomplex by the common coefficients. -/
def coefficientSingularTotalAugmentation :
    TotalAugmentation (coefficientCechComplex ρ U) (singularCechBicomplex ρ U).flip where
  map := coefficientSingularCechChain ρ U
  horizontal_zero := coefficientSingularCechChain_vertical ρ U

end Singular
end TernaryPoly.SmoothSingularGlobal
