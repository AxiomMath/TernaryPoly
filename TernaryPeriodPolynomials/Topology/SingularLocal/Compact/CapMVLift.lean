module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVChainMono

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex
open scoped TensorProduct
open SingularLocalCap

/-- A bilinear map killed by the second arrow lifts canonically through a monic first arrow
of an actual exact sequence of rational modules. -/
def exactLiftBilinear (S : ShortComplex (ModuleCat.{0} ℚ)) (hS : S.Exact) [Mono S.f]
    (P Q : ModuleCat.{0} ℚ) (β : P →ₗ[ℚ] Q →ₗ[ℚ] S.X₂)
    (hβ : ∀ x c, S.g (β x c) = 0) : P →ₗ[ℚ] Q →ₗ[ℚ] S.X₁ := by
  let t : ModuleCat.of ℚ (P ⊗[ℚ] Q) ⟶ S.X₂ := ModuleCat.ofHom (TensorProduct.lift β)
  have ht : t ≫ S.g = 0 := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x c
    exact hβ x c
  exact (TensorProduct.mk ℚ P Q).compr₂ (hS.lift t ht).hom

/-- The canonical bilinear lift retains its literal value under the actual first inclusion. -/
theorem exactLiftBilinear_inclusion (S : ShortComplex (ModuleCat.{0} ℚ)) (hS : S.Exact) [Mono S.f]
    (P Q : ModuleCat.{0} ℚ) (β : P →ₗ[ℚ] Q →ₗ[ℚ] S.X₂)
    (hβ : ∀ x c, S.g (β x c) = 0) (x : P) (c : Q) :
    S.f (exactLiftBilinear S hS P Q β hβ x c) = β x c := by
  let t : ModuleCat.of ℚ (P ⊗[ℚ] Q) ⟶ S.X₂ := ModuleCat.ofHom (TensorProduct.lift β)
  have ht : t ≫ S.g = 0 := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x c
    exact hβ x c
  exact congrArg (fun f : ModuleCat.of ℚ (P ⊗[ℚ] Q) ⟶ S.X₂ => f (x ⊗ₜ[ℚ] c))
    (hS.lift_f t ht)

variable (S : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact)
  (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (K : ChainComplex (ModuleCat.{0} ℚ) ℕ)
  (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] S.X₂.X b)
  (hz : ∀ a b x c, S.g.f b (β a b x c) = 0)

/-- The actual degreewise exact sequence canonically lifts a cap pairing into its first chain complex. -/
def exactLiftPairing (a b : ℕ) : C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] S.X₁.X b := by
  have hs := (shortExact_iff_degreewise_shortExact S).mp hS b
  have := hs.mono_f
  exact exactLiftBilinear (S.map (eval (ModuleCat ℚ) (ComplexShape.down ℕ) b)) hs.exact
    (C.X a) (K.X (a+b)) (β a b) (hz a b)

/-- The lifted pairing is exactly the given cap after the actual first chain inclusion. -/
theorem exactLiftPairing_inclusion (a b : ℕ) (x : C.X a) (c : K.X (a+b)) :
    S.f.f b (exactLiftPairing S hS C K β hz a b x c) = β a b x c := by
  have hs := (shortExact_iff_degreewise_shortExact S).mp hS b
  have := hs.mono_f
  exact exactLiftBilinear_inclusion _ hs.exact _ _ (β a b) (hz a b) x c

/-- Actual chain exactness preserves the precise Leibniz sign when lifting the cap pairing. -/
theorem exactLiftPairing_leibniz (hβ : Descent.Leibniz C K S.X₂ β) :
    Descent.Leibniz C K S.X₁ (exactLiftPairing S hS C K β hz) := by
  intro a b x c
  have := hS.mono_f
  apply (ModuleCat.mono_iff_injective (S.f.f b)).mp inferInstance
  rw [map_add,map_zsmul,exactLiftPairing_inclusion,exactLiftPairing_inclusion]
  have hc := congrArg (fun f => f (exactLiftPairing S hS C K β hz a (b+1) x c)) (S.f.comm (b+1) b)
  change S.X₂.d (b+1) b (S.f.f (b+1) _) = S.f.f b (S.X₁.d (b+1) b _) at hc
  rw [← hc,exactLiftPairing_inclusion]
  exact hβ a b x c

end TernaryPoly.SingularLocalCompactCapMV
