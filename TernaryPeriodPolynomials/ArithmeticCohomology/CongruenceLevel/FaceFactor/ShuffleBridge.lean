module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantMu
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.N2Algebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalForm

@[expose] public section


/-!
# The shuffle model of a split extension, and the torus homotopy in additive coordinates

Formalized by Claude Sonnet 5.5.

* `pairModelOfSplitting s`: `PairModel E (Additive N) L` for a split extension `1 → N → E → L → 1` with `N` commutative: `pr a σ = inl a · s σ`, `ψ σ = ` conjugation by `s σ`.
  `ψ σ⁻¹ = splitRadicalInput σ` (`pm_psi_inv`), `nl a = inl a`, `ll σ = s σ`.
* `hμ_of_torus`: the `torus_homotopy_hom` for `N = ℤ²` gives the homotopy hypothesis of `T1` in additive coordinates.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [CommGroup N] [Group E] [Group L] {ext : GroupExtension N E L}

/-- **The shuffle model of a split extension.** -/
def pairModelOfSplitting (s : ext.Splitting) : PairModel E (Additive N) L where
  ψ σ := (s.conjAct σ).toMonoidHom.toAdditive
  ψ_one x := by simp
  ψ_mul σ τ x := by simp [map_mul]
  pr a σ := ext.inl (Additive.toMul a) * s σ
  pr_mul a σ b τ := by
    have h : ext.inl ((s.conjAct σ) (Additive.toMul b)) = s σ * ext.inl (Additive.toMul b) * (s σ)⁻¹ :=
      ext.inl_conjAct_comm (e := s σ) (n := Additive.toMul b)
    change ext.inl (Additive.toMul a) * s σ * (ext.inl (Additive.toMul b) * s τ) =
      ext.inl (Additive.toMul a * (s.conjAct σ) (Additive.toMul b)) * s (σ * τ)
    rw [map_mul, h, map_mul]
    group

theorem pm_nl (s : ext.Splitting) (a : Additive N) :
    (pairModelOfSplitting s).nl a = ext.inl (Additive.toMul a) := by
  simp [PairModel.nl, pairModelOfSplitting]

theorem pm_ll (s : ext.Splitting) (σ : L) : (pairModelOfSplitting s).ll σ = s σ := by
  simp [PairModel.ll, pairModelOfSplitting]

theorem pm_nl_ofMul (s : ext.Splitting) (r : N) : (pairModelOfSplitting s).nl (Additive.ofMul r) = ext.inl r := by
  rw [pm_nl]; rfl

/-- `ψ σ⁻¹` is `splitRadicalInput σ` (the action `σ · r` with `s σ · inl(σ · r) = inl r · s σ`). -/
theorem pm_psi_inv (s : ext.Splitting) (σ : L) (r : N) :
    (pairModelOfSplitting s).ψ σ⁻¹ (Additive.ofMul r) = Additive.ofMul (splitRadicalInput s σ r) := rfl

theorem pm_pr (s : ext.Splitting) (r : N) (σ : L) :
    (pairModelOfSplitting s).pr (Additive.ofMul r) σ = ext.inl r * s σ := rfl

section Torus

open Finsupp

/-- Additive coordinates on the bar chains of `ℤ²`. -/
def toAddCh2 : (Fin 2 → Multiplicative (ℤ × ℤ)) → Additive (Multiplicative (ℤ × ℤ)) × Additive (Multiplicative (ℤ × ℤ)) :=
  fun x => (Additive.ofMul (x 0), Additive.ofMul (x 1))

def toAddCh3 : (Fin 3 → Multiplicative (ℤ × ℤ)) →
    Additive (Multiplicative (ℤ × ℤ)) × Additive (Multiplicative (ℤ × ℤ)) × Additive (Multiplicative (ℤ × ℤ)) :=
  fun x => (Additive.ofMul (x 0), Additive.ofMul (x 1), Additive.ofMul (x 2))

theorem torusBd3_lmapDomain (m : BarCh 3 (Multiplicative (ℤ × ℤ))) :
    torusBd3 (Additive (Multiplicative (ℤ × ℤ))) (lmapDomain ℚ ℚ toAddCh3 m) = lmapDomain ℚ ℚ toAddCh2 (bdry3 m) := by
  have h : (torusBd3 (Additive (Multiplicative (ℤ × ℤ)))).comp (lmapDomain ℚ ℚ toAddCh3) =
      (lmapDomain ℚ ℚ toAddCh2).comp bdry3 := by
    apply Finsupp.lhom_ext
    intro x r
    simp [torusBd3, bdry3, toAddCh2, toAddCh3, Finsupp.linearCombination_single, ofMul_mul, map_sub, map_add]
  exact LinearMap.congr_fun h m

/-- **The homotopy hypothesis of `T1` for `N = ℤ²`**: for an endomorphism `σ` of determinant one there is a chain `m` with `∂m = ν^σ - ν`
in additive coordinates. -/
theorem hmu_of_torus (σ : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ))
    (hdet : (σ latE1).toAdd.1 * (σ latE2).toAdd.2 - (σ latE1).toAdd.2 * (σ latE2).toAdd.1 = 1) :
    ∃ m : (Additive (Multiplicative (ℤ × ℤ)) × Additive (Multiplicative (ℤ × ℤ)) × Additive (Multiplicative (ℤ × ℤ))) →₀ ℚ,
      torusBd3 (Additive (Multiplicative (ℤ × ℤ))) m =
        nuChain (Additive.ofMul (σ latE1)) (Additive.ofMul (σ latE2)) -
          nuChain (Additive.ofMul latE1) (Additive.ofMul latE2) := by
  obtain ⟨m, hm⟩ := torus_homotopy_hom σ (σ latE1).toAdd.1 (σ latE2).toAdd.1 (σ latE1).toAdd.2 (σ latE2).toAdd.2
    (by apply Multiplicative.toAdd.injective; ext <;> simp [latE1, latE2])
    (by apply Multiplicative.toAdd.injective; ext <;> simp [latE1, latE2]) (by linarith [hdet])
  refine ⟨lmapDomain ℚ ℚ toAddCh3 m, ?_⟩
  rw [torusBd3_lmapDomain, hm]
  simp [torusNuOf, torusNu, nuChain, toAddCh2, map_sub]

end Torus

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
