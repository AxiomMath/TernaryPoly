module

public import TernaryPeriodPolynomials.Building.Primitive.Basic
public import TernaryPeriodPolynomials.Polynomial.Operators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial

namespace TernaryPoly.PrimitiveTransfer

/-- The literal equations over an arbitrary coefficient ring. -/
def Relations {R : Type*} [CommRing R] (p : MvPolynomial (Fin 3) R) : Prop :=
  bind₁ ![X 1, X 2, X 0] p = p ∧
    p + bind₁ ![-X 1, X 0 - X 1, X 2] p +
      bind₁ ![X 1 - X 0, -X 0, X 2] p = 0

lemma map_bind_vec3 {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : MvPolynomial (Fin 3) R) (a b c : MvPolynomial (Fin 3) R) :
    map φ (bind₁ ![a,b,c] p) =
      bind₁ ![map φ a, map φ b, map φ c] (map φ p) := by
  rw [map_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

lemma map_coeff_smul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) (p : MvPolynomial (Fin 3) R) :
    map φ (r • p) = φ r • map φ p := by
  simp [Algebra.smul_def, algebraMap_eq]

/-- Coefficient maps preserve the two literal substitution relations. -/
theorem Relations.map {R S : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial (Fin 3) R} (hp : Relations p) (φ : R →+* S) :
    Relations (MvPolynomial.map φ p) := by
  constructor
  · have h := congrArg (MvPolynomial.map φ) hp.1
    simpa only [map_bind_vec3, map_X] using h
  · have h := congrArg (MvPolynomial.map φ) hp.2
    simpa only [map_add, map_zero, map_bind_vec3, map_X, map_neg, map_sub] using h

/-- An injective coefficient map also reflects both substitution relations. -/
theorem Relations.of_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) {p : MvPolynomial (Fin 3) R}
    (hp : Relations (MvPolynomial.map φ p)) : Relations p := by
  constructor
  · apply MvPolynomial.map_injective φ hφ
    simpa only [map_bind_vec3, map_X] using hp.1
  · apply MvPolynomial.map_injective φ hφ
    simpa only [map_add, map_zero, map_bind_vec3, map_X, map_neg, map_sub] using hp.2

/-- Rational scalar multiples descend to integral homogeneous solutions. -/
theorem integral_multiple_relations {f : TernaryPolynomial} {n : ℕ}
    (hf : PeriodRelations f) (hdeg : f.IsHomogeneous n)
    {a : ℚ} {p : MvPolynomial (Fin 3) ℤ}
    (hp : MvPolynomial.map (Int.castRingHom ℚ) p = a • f) :
    p.IsHomogeneous n ∧ Relations p := by
  constructor
  · apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
    rw [hp]
    exact (homogeneousSubmodule (Fin 3) ℚ n).smul_mem a hdeg
  · apply Relations.of_map (Int.castRingHom ℚ) Int.cast_injective
    rw [hp]
    exact hf.smul a

/-- A primitive integral solution and its nonzero mod-two reduction retain degree and relations. -/
theorem exists_primitive_period_solution {f : TernaryPolynomial} {n : ℕ}
    (hzero : f ≠ 0) (hf : PeriodRelations f) (hdeg : f.IsHomogeneous n) :
    ∃ a : ℚ, ∃ p : MvPolynomial (Fin 3) ℤ,
      a ≠ 0 ∧ MvPolynomial.map (Int.castRingHom ℚ) p = a • f ∧
      p.IsHomogeneous n ∧ Relations p ∧
      (MvPolynomial.map (Int.castRingHom (ZMod 2)) p).IsHomogeneous n ∧
      Relations (MvPolynomial.map (Int.castRingHom (ZMod 2)) p) ∧
      MvPolynomial.map (Int.castRingHom (ZMod 2)) p ≠ 0 := by
  obtain ⟨a, ha, p, hp, hmod⟩ := exists_primitive_integral_multiple hzero
  obtain ⟨hdegree, hrelations⟩ := integral_multiple_relations hf hdeg hp
  exact ⟨a, p, ha, hp, hdegree, hrelations,
    hdegree.map _, hrelations.map _, hmod⟩

/-- An integral swap eigenvalue descends from a rational scalar multiple. -/
theorem integral_multiple_swap {f : TernaryPolynomial} (ε : ℤ)
    (hs : TernaryPoly.S f = (ε : ℚ) • f) {a : ℚ} {p : MvPolynomial (Fin 3) ℤ}
    (hp : MvPolynomial.map (Int.castRingHom ℚ) p = a • f) :
    bind₁ ![X 1, X 0, X 2] p = ε • p := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_bind_vec3, map_coeff_smul, hp]
  simp only [map_X]
  change TernaryPoly.S (a • f) = (ε : ℚ) • (a • f)
  rw [map_smul, hs, smul_comm a (ε : ℚ) f]

/-- Swap eigenvalue equations map from integers to any coefficient ring. -/
theorem map_swap_eigen {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {p : MvPolynomial (Fin 3) R} (ε : R)
    (hs : bind₁ ![X 1, X 0, X 2] p = ε • p) :
    bind₁ ![X 1, X 0, X 2] (MvPolynomial.map φ p) =
      φ ε • MvPolynomial.map φ p := by
  have h := congrArg (MvPolynomial.map φ) hs
  simpa only [map_bind_vec3, map_X, map_coeff_smul] using h

/-- Primitive reduction also preserves the signed swap equation, including either symmetry sector. -/
theorem exists_primitive_signed_period_solution {f : TernaryPolynomial} {n : ℕ}
    (hzero : f ≠ 0) (hf : PeriodRelations f) (hdeg : f.IsHomogeneous n)
    (ε : ℤ) (hs : TernaryPoly.S f = (ε : ℚ) • f) :
    ∃ a : ℚ, ∃ p : MvPolynomial (Fin 3) ℤ,
      a ≠ 0 ∧ MvPolynomial.map (Int.castRingHom ℚ) p = a • f ∧
      p.IsHomogeneous n ∧ Relations p ∧ bind₁ ![X 1, X 0, X 2] p = ε • p ∧
      (MvPolynomial.map (Int.castRingHom (ZMod 2)) p).IsHomogeneous n ∧
      Relations (MvPolynomial.map (Int.castRingHom (ZMod 2)) p) ∧
      bind₁ ![X 1, X 0, X 2] (MvPolynomial.map (Int.castRingHom (ZMod 2)) p) =
        (Int.castRingHom (ZMod 2)) ε • MvPolynomial.map (Int.castRingHom (ZMod 2)) p ∧
      MvPolynomial.map (Int.castRingHom (ZMod 2)) p ≠ 0 := by
  obtain ⟨a, p, ha, hp, hdegree, hrelations, hdegree2, hrelations2, hmod⟩ :=
    exists_primitive_period_solution hzero hf hdeg
  have hswap := integral_multiple_swap ε hs hp
  exact ⟨a, p, ha, hp, hdegree, hrelations, hswap, hdegree2, hrelations2,
    map_swap_eigen (Int.castRingHom (ZMod 2)) ε hswap, hmod⟩

end TernaryPoly.PrimitiveTransfer
