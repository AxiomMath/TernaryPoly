module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Connecting
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

@[expose] public section


noncomputable section
namespace TernaryPoly.HalfSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex

variable {K L M : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (g : L ⟶ M)

/-- The literal quotient sequence of two composable chain inclusions. -/
abbrev tripleSequence := (kernelCokernelCompSequence.snakeInput f g).L₃

/-- The nested quotient sequence is genuinely short exact whenever the second map is mono. -/
theorem tripleSequence_shortExact [Mono g] : (tripleSequence f g).ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := (kernelCokernelCompSequence.snakeInput f g).L₂'_exact.mono_g
    ((isZero_kernel_of_mono g).eq_of_src _ _)
  epi_g := by
    change Epi (cokernel.map (f ≫ g) g f (𝟙 M) (by simp))
    infer_instance

/-- The actual localized connecting map uses precisely the nested quotient short exact sequence. -/
def tripleConnecting [Mono g] (n : ℕ) :
    (cokernel g).homology (n+1) ⟶ (cokernel f).homology n :=
  (tripleSequence_shortExact f g).δ (n+1) n rfl

/-- The literal projection from the ordinary pair sequence to its nested quotient sequence. -/
def pairToTriple : RelativeChainSequence.sequence g ⟶ tripleSequence f g where
  τ₁ := cokernel.π f
  τ₂ := cokernel.π (f ≫ g)
  τ₃ := 𝟙 (cokernel g)
  comm₁₂ := by simp [RelativeChainSequence.sequence,tripleSequence,kernelCokernelCompSequence.snakeInput,cokernel.map]
  comm₂₃ := by simp [tripleSequence,kernelCokernelCompSequence.snakeInput,
    RelativeChainSequence.sequence,cokernel.map]

/-- The actual local boundary map is exactly ordinary connecting followed by quotient projection;
there is no additional sign or arbitrary scalar. -/
theorem tripleConnecting_eq [Mono g] (n : ℕ) :
    tripleConnecting f g n =
      RelativeChainSequence.connecting g n ≫ homologyMap (cokernel.π f) n := by
  have h := HomologySequence.δ_naturality (pairToTriple f g)
    (RelativeChainSequence.shortExact g) (tripleSequence_shortExact f g) (n+1) n rfl
  change RelativeChainSequence.connecting g n ≫ homologyMap (cokernel.π f) n =
    homologyMap (𝟙 (cokernel g)) (n+1) ≫ tripleConnecting f g n at h
  rw [homologyMap_id,Category.id_comp] at h
  exact h.symm

/-- A class with zero literal local boundary lifts through the actual nested quotient map. -/
theorem tripleConnecting_zero_iff_lifts [Mono g] (n : ℕ) (c : (cokernel g).homology (n+1)) :
    tripleConnecting f g n c = 0 ↔ ∃ b : (cokernel (f ≫ g)).homology (n+1),
      homologyMap (tripleSequence f g).g (n+1) b = c := by
  have h := (tripleSequence_shortExact f g).homology_exact₃ (n+1) n rfl
  change c ∈ LinearMap.ker (tripleConnecting f g n).hom ↔
    c ∈ LinearMap.range (homologyMap (tripleSequence f g).g (n+1)).hom
  rw [h.moduleCat_range_eq_ker]
  rfl

end TernaryPoly.HalfSpaceBoundaryOrientation
