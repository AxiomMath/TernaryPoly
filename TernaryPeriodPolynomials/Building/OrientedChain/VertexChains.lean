module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedVertexChains
open OrientedListChains OrientedChainJoin
variable {V I : Type*}

/-- Evaluation of a finite raw chain on its empty-list coefficient. -/
def rawEmptyCoefficient : Raw V →ₗ[ℚ] ℚ := Finsupp.lapply []

/-- Prefixing creates no empty-list coefficient. -/
theorem rawEmptyCoefficient_rawCons (a : V) (c : Raw V) :
    rawEmptyCoefficient (rawCons a c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd,add_zero]
  | single l q =>
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    rw [hq,map_smul,map_smul,rawCons_simplex]
    simp [rawEmptyCoefficient,rawSimplex]

/-- All actual orientation relations have zero empty-list coefficient. -/
theorem rawEmptyCoefficient_relation {c : Raw V} (hc : c ∈ relations V) :
    rawEmptyCoefficient c = 0 := by
  induction hc with
  | swap a b l => simp [rawEmptyCoefficient,rawSimplex]
  | cons a hc ih => exact rawEmptyCoefficient_rawCons a _
  | zero => exact map_zero _
  | add hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q hc ih => rw [map_smul,ih,smul_zero]

/-- A genuine coefficient functional descended through the oriented quotient. -/
def emptyCoefficient : Chain V →ₗ[ℚ] ℚ :=
  (relations V).liftQ rawEmptyCoefficient (fun _ hc => rawEmptyCoefficient_relation hc)

@[simp] theorem emptyCoefficient_nil : emptyCoefficient (simplex ([] : List V)) = 1 := by
  change rawEmptyCoefficient (rawSimplex []) = 1
  simp [rawEmptyCoefficient,rawSimplex]

/-- Finite indexed combinations of actual oriented singleton simplices. -/
def singletonMap (v : I → V) : (I →₀ ℚ) →ₗ[ℚ] Chain V :=
  Finsupp.linearCombination ℚ (fun i => simplex [v i])

@[simp] theorem singletonMap_single (v : I → V) (i : I) (q : ℚ) :
    singletonMap v (Finsupp.single i q) = q • simplex [v i] :=
  Finsupp.linearCombination_single ℚ q i

/-- The literal total coefficient of a finite indexed vertex chain. -/
def coefficientSum : (I →₀ ℚ) →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ => 1)

@[simp] theorem coefficientSum_single (i : I) (q : ℚ) :
    coefficientSum (Finsupp.single i q) = q := by simp [coefficientSum]

/-- The augmented boundary of a singleton combination is its actual coefficient sum. -/
theorem boundary_singletonMap (v : I → V) (z : I →₀ ℚ) :
    boundary (singletonMap v z) = coefficientSum z • simplex [] := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,zero_smul]
  | add c d hc hd => simp only [map_add,hc,hd,add_smul]
  | single i q =>
    simp only [singletonMap_single,map_smul,boundary_cons,boundary_nil,map_zero,
      sub_zero,coefficientSum_single]

/-- The quotient's empty coefficient detects augmentation-zero from an actual boundary equation. -/
theorem coefficientSum_eq_zero_of_boundary (v : I → V) (z : I →₀ ℚ)
    (hz : boundary (singletonMap v z) = 0) : coefficientSum z = 0 := by
  have he := congrArg (emptyCoefficient : Chain V →ₗ[ℚ] ℚ) (boundary_singletonMap v z)
  rw [hz,map_zero,map_smul,emptyCoefficient_nil,smul_eq_mul,mul_one] at he
  exact he.symm

/-- A covering family of actual vertices spans every degree-one oriented chain of a precomplex. -/
theorem exists_singletonMap (C : PreAbstractSimplicialComplex V) (v : I → V)
    (hcover : ∀ a : V, {a} ∈ C → ∃ i, v i = a)
    {c : Chain V} (hc : c ∈ chains C 1) : ∃ z : I →₀ ℚ, singletonMap v z = c := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hlen
    have ha : {a} ∈ C := by
      simpa using hl.resolve_left (by simp)
    obtain ⟨i,hi⟩ := hcover a ha
    exact ⟨Finsupp.single i 1,by rw [singletonMap_single,one_smul,hi]⟩
  | zero => exact ⟨0,map_zero _⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨x,hx⟩ := ihc
    obtain ⟨y,hy⟩ := ihd
    exact ⟨x+y,by rw [map_add,hx,hy]⟩
  | smul q c hc ih =>
    obtain ⟨x,hx⟩ := ih
    exact ⟨q • x,by rw [map_smul,hx]⟩

end TernaryPoly.OrientedVertexChains
