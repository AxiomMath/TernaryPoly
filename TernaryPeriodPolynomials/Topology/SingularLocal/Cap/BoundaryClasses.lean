module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.RelativeLeibniz

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap.BoundaryClasses
open CategoryTheory Limits HomologicalComplex

variable {A : ModuleCat.{0} ℚ}

/-- A family of actual chain cycles represents a morphism into actual homology. -/
def classMap (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x : A ⟶ K.X n) (hx : x ≫ K.d n (n-1) = 0) : A ⟶ K.homology n :=
  K.liftCycles x (n-1) (down_next n) hx ≫ K.homologyπ n

/-- A chain whose differential lifts from the subcomplex represents an actual relative cycle. -/
theorem projected_cycle {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (i : K ⟶ L)
    (n : ℕ) (x₂ : A ⟶ L.X (n+1)) (x₁ : A ⟶ K.X n)
    (h : x₁ ≫ i.f n = x₂ ≫ L.d (n+1) n) :
    (x₂ ≫ (cokernel.π i).f (n+1)) ≫ (cokernel i).d (n+1) (n+1-1) = 0 := by
  change (x₂ ≫ (cokernel.π i).f (n+1)) ≫ (cokernel i).d (n+1) n = 0
  rw [Category.assoc,(cokernel.π i).comm,← Category.assoc,← h,Category.assoc]
  have hz := HomologicalComplex.congr_hom (cokernel.condition i) n
  change i.f n ≫ (cokernel.π i).f n = 0 at hz
  rw [hz,comp_zero]

/-- Injectivity of the actual subcomplex inclusion makes a lifted boundary a cycle. -/
theorem lifted_boundary_cycle {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (i : K ⟶ L) [Mono i]
    (n : ℕ) (x₂ : A ⟶ L.X (n+1)) (x₁ : A ⟶ K.X n)
    (h : x₁ ≫ i.f n = x₂ ≫ L.d (n+1) n) : x₁ ≫ K.d n (n-1) = 0 := by
  rw [← cancel_mono (i.f (n-1)),zero_comp,Category.assoc,← i.comm,← Category.assoc,h,Category.assoc,
    L.d_comp_d,comp_zero]

/-- The actual cokernel connecting homomorphism sends a represented relative cycle to its lifted boundary. -/
theorem connecting_classMap {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (i : K ⟶ L) [Mono i]
    (n : ℕ) (x₂ : A ⟶ L.X (n+1)) (x₁ : A ⟶ K.X n)
    (h : x₁ ≫ i.f n = x₂ ≫ L.d (n+1) n) :
    classMap (cokernel i) (n+1) (x₂ ≫ (cokernel.π i).f (n+1)) (projected_cycle i n x₂ x₁ h) ≫
        RelativeChainSequence.connecting i n =
      classMap K n x₁ (lifted_boundary_cycle i n x₂ x₁ h) := by
  exact (RelativeChainSequence.shortExact i).δ_eq (n+1) n rfl
    (x₂ ≫ (cokernel.π i).f (n+1)) (projected_cycle i n x₂ x₁ h) x₂ rfl x₁ h
    (n-1) (down_next n)

/-- A single actual cycle is represented using its linear family of rational multiples. -/
def elementMap {M : ModuleCat.{0} ℚ} (x : M) : ModuleCat.of ℚ ℚ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M x)

/-- A linear map applied to a represented element is represented by its composite. -/
theorem elementMap_comp {M N : ModuleCat.{0} ℚ} (x : M) (f : M ⟶ N) :
    elementMap x ≫ f = elementMap (f x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact map_smul f.hom r x

/-- Scalar multiples of a cycle represent the corresponding scalar multiple of its homology class. -/
theorem classMap_zsmul (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x : A ⟶ K.X n) (hx : x ≫ K.d n (n-1) = 0) (r : ℤ)
    (hr : (r • x) ≫ K.d n (n-1) = 0) :
    classMap K n (r • x) hr = r • classMap K n x hx := by
  unfold classMap
  have h : K.liftCycles (r • x) (n-1) (down_next n) hr =
      r • K.liftCycles x (n-1) (down_next n) hx := by
    rw [← cancel_mono (K.iCycles n),Preadditive.zsmul_comp,HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i]
  rw [h,Preadditive.zsmul_comp]

end TernaryPoly.SingularLocalCap.BoundaryClasses
