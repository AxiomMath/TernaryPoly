module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodTensor
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodRationalComparison
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Period

@[expose] public section


open TensorProduct
noncomputable section
namespace TernaryPoly.BinaryComplexPeriod

/-- Extended rational periods span the whole actual complex period space. -/
theorem span_extend_eq_top (d : ℕ) :
    Submodule.span ℂ (Set.range (extend (algebraMap ℚ ℂ) d))=⊤ := by
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨t,rfl⟩ := (tensorPeriodEquiv d).surjective q
  induction t using TensorProduct.inductionOn with
  | tmul a q =>
    rw [tensorPeriodEquiv_tmul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨q,rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Scalar extension of any actual rational period endomorphism. -/
def complexifyEnd (d : ℕ) (T : Module.End ℚ (space ℚ d)) : Module.End ℂ (space ℂ d) :=
  (tensorPeriodEquiv d).toLinearMap.comp
    ((AlgebraTensorModule.lTensor ℂ ℂ T).comp (tensorPeriodEquiv d).symm.toLinearMap)

@[simp] theorem tensorPeriodEquiv_symm_extend (d : ℕ) (q : space ℚ d) :
    (tensorPeriodEquiv d).symm (extend (algebraMap ℚ ℂ) d q)=1 ⊗ₜ[ℚ] q := by
  apply (tensorPeriodEquiv d).injective
  simp

/-- Scalar extension retains the exact value of a rational endomorphism on extended periods. -/
theorem complexifyEnd_extend (d : ℕ) (T : Module.End ℚ (space ℚ d)) (q : space ℚ d) :
    complexifyEnd d T (extend (algebraMap ℚ ℂ) d q)=extend (algebraMap ℚ ℂ) d (T q) := by
  simp [complexifyEnd]

/-- A complex-linear endomorphism is determined by its values on literal rational periods. -/
theorem end_ext_on_rational (d : ℕ) (T U : Module.End ℂ (space ℂ d))
    (h : ∀ q,T (extend (algebraMap ℚ ℂ) d q)=U (extend (algebraMap ℚ ℂ) d q)) : T=U := by
  apply LinearMap.ext
  intro q
  have hq : q ∈ Submodule.span ℂ (Set.range (extend (algebraMap ℚ ℂ) d)) := by
    rw [span_extend_eq_top]; trivial
  induction hq using Submodule.span_induction with
  | mem q hq => obtain ⟨r,rfl⟩ := hq; exact h r
  | zero => simp
  | add q r _ _ hq hr => simp only [map_add,hq,hr]
  | smul a q _ hq => simp only [map_smul,hq]

/-- The actual rational modular-symbol Hecke in the field-generic period coordinates. -/
def rationalSymbolHecke (d : ℕ) (g : BinaryModularSymbol.GL2) : Module.End ℚ (space ℚ d) :=
  (rationalEquiv d).toLinearMap.comp
    ((BinaryRationalHecke.periodHecke d g).comp (rationalEquiv d).symm.toLinearMap)

/-- The actual binary Hecke operator extended to the entire complex period space. -/
def complexHecke (d : ℕ) (g : BinaryModularSymbol.GL2) : Module.End ℂ (space ℂ d) :=
  complexifyEnd d (rationalSymbolHecke d g)

theorem complexHecke_extend (d : ℕ) (g : BinaryModularSymbol.GL2) (q : space ℚ d) :
    complexHecke d g (extend (algebraMap ℚ ℂ) d q)=
      extend (algebraMap ℚ ℂ) d (rationalSymbolHecke d g q) :=
  complexifyEnd_extend d _ q

/-- Every genuinely Hecke-stable rational subspace remains stable under the actual complex operator. -/
theorem complexHecke_span_stable (d : ℕ) (g : BinaryModularSymbol.GL2)
    (L : Submodule ℚ (space ℚ d))
    (hL : ∀ q ∈ L,rationalSymbolHecke d g q ∈ L) :
    ∀ q ∈ complexSpan d L,complexHecke d g q ∈ complexSpan d L :=
  complexSpan_stable d L _ _ hL (complexHecke_extend d g)

end TernaryPoly.BinaryComplexPeriod
