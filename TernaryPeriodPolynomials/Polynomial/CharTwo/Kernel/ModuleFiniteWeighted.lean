module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GradedCount
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DicksonWeights

@[expose] public section





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- For a finite-variable polynomial ring over `ZMod 2` graded by a
weight function `w` with no zero weights, the weighted-homogeneous-degree-`n` submodule is a
finite `(ZMod 2)`-module. Needed so that `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
(which requires `FiniteDimensional K` on both sides, and `FiniteDimensional K V` unfolds
reducibly to `Module.Finite K V`) can later be applied to Ψ_d. Mirrors
`finrank_weightedHomogeneousSubmodule`'s own proof (`GradedCount.lean`) verbatim up through the
same basis construction, swapping the `finrank_eq_card_basis`/`Nat.card_eq_fintype_card`
cardinality conclusion for the more basic `Module.Finite.of_basis` on that same basis (so the
`Nontrivial (ZMod 2)` fact used only for the cardinality computation is not needed here). -/
theorem moduleFinite_weightedHomogeneousSubmodule {σ : Type*} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    Module.Finite (ZMod 2) (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) w n) := by
  have hfin : {d : σ →₀ ℕ | Finsupp.weight w d = n}.Finite :=
    Finsupp.finite_of_nat_weight_eq w hw n
  let _ : Fintype {d : σ →₀ ℕ | Finsupp.weight w d = n} := hfin.fintype
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.of_basis
    (Finsupp.basisSingleOne.map
      (AddMonoidAlgebra.supportedEquivFinsupp (R := ZMod 2) (S := ZMod 2)
        {d : σ →₀ ℕ | Finsupp.weight w d = n}).symm)

/-- Specialization to `w = stdWeight`, as a registered instance so that typeclass search
(needed e.g. by `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`) finds it
automatically for any concrete degree. -/
instance instModuleFiniteWeightedHomogeneousSubmoduleStdWeight (n : ℕ) :
    Module.Finite (ZMod 2) (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight n) :=
  moduleFinite_weightedHomogeneousSubmodule stdWeight (by decide) n

/-- Specialization to `w = ![4,6,7]`, as a registered instance for the same reason. -/
instance instModuleFiniteWeightedHomogeneousSubmoduleGen467 (n : ℕ) :
    Module.Finite (ZMod 2)
      (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ) n) :=
  moduleFinite_weightedHomogeneousSubmodule (![4, 6, 7] : Fin 3 → ℕ) (by decide) n

end TernaryPeriodPolynomials.Argument.CharTwoKernel
