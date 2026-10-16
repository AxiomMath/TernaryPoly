module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalCocycles

@[expose] public section


/-!
# The sublattice `m ℤ²` of the radical lattice

Formalized by Claude Sonnet 5.5.

`latt m` is the range of `r ↦ r ^ m` on `RadicalLattice = Multiplicative (ℤ × ℤ)`; it has index `m ^ 2` (`index_latt`), and is stable under every endomorphism (`map_mem_latt`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The sublattice `mℤ²`. -/
def latt (m : ℕ) : Subgroup RadicalLattice := (powMonoidHom m : RadicalLattice →* RadicalLattice).range

theorem pow_mem_latt (m : ℕ) (r : RadicalLattice) : r ^ m ∈ latt m := ⟨r, rfl⟩

theorem map_mem_latt (m : ℕ) (ψ : RadicalLattice →* RadicalLattice) {r : RadicalLattice} (h : r ∈ latt m) :
    ψ r ∈ latt m := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨ψ s, by simp [map_pow]⟩

/-- Reduction modulo `m`. -/
def reduceMod (m : ℕ) : RadicalLattice →* Multiplicative (ZMod m × ZMod m) :=
  AddMonoidHom.toMultiplicative ((Int.castAddHom (ZMod m)).prodMap (Int.castAddHom (ZMod m)))

theorem reduceMod_apply (m : ℕ) (r : RadicalLattice) :
    (reduceMod m r).toAdd = ((r.toAdd.1 : ZMod m), (r.toAdd.2 : ZMod m)) := rfl

theorem ker_reduceMod (m : ℕ) : (reduceMod m).ker = latt m := by
  ext r
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [reduceMod_apply] at h'
    have h1 : ((r.toAdd.1 : ℤ) : ZMod m) = 0 := congrArg Prod.fst h'
    have h2 : ((r.toAdd.2 : ℤ) : ZMod m) = 0 := congrArg Prod.snd h'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    refine ⟨Multiplicative.ofAdd (a, b), ?_⟩
    apply Multiplicative.toAdd.injective
    simp [ha, hb, Prod.ext_iff]
  · rintro ⟨s, rfl⟩
    apply Multiplicative.toAdd.injective
    simp [reduceMod_apply]

theorem reduceMod_surjective (m : ℕ) : Function.Surjective (reduceMod m) := by
  intro y
  obtain ⟨⟨a, b⟩, hy⟩ : ∃ p : ZMod m × ZMod m, p = y.toAdd := ⟨y.toAdd, rfl⟩
  obtain ⟨a', ha⟩ := ZMod.intCast_surjective a
  obtain ⟨b', hb⟩ := ZMod.intCast_surjective b
  refine ⟨Multiplicative.ofAdd (a', b'), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [reduceMod_apply]
  simp [ha, hb, ← hy]

theorem index_latt (m : ℕ) [NeZero m] : (latt m).index = m ^ 2 := by
  rw [← ker_reduceMod, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (reduceMod_surjective m)]
  simp [Nat.card_eq_fintype_card, ZMod.card, sq]

end TernaryPeriodPolynomials.Argument.RadicalInduction
