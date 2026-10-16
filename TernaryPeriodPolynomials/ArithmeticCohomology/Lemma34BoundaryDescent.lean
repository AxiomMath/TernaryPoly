module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.LevelK
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.TransferResQ

@[expose] public section


/-!
# Proposition 3.4, passage to the boundary: `H₃(K,E) ≅ H₃(Γ',E)_Δ` and the same descent on boundary homology

Proof of `thm:boundary-evaluation`, first paragraph, and the passage to a
finite-index subgroup in Lemma 3.3.  Formalized by Claude Sonnet 5.5.

* `repN H M`, `repDeltaN H M`: the conjugation action of `H` (of `Δ = H/Γ(6)`) on `H₃(Γ(6), E)`; `groupCoinvEquiv`, `groupCoinvDelta`:
  `H₃(H, E) ≃ₗ[ℚ] Coinvariants` with `[z] ↦ Cor z` (rational averaging).
* `repBd V₀ H` (Naturality), `repDeltaBd`: the geometric action on `H₃(∂X̄_{Γ(6)}; 𝓜)`; `boundaryCoinvEquiv`, `boundaryCoinvDelta`:
  `H₃(∂X̄_H; 𝓜) ≃ₗ[ℚ] Coinvariants` with `[c] ↦ q c`.
* `jN`, `jCoinv`, `jCoinvDelta`, `jQH_boundaryCoinvEquiv`, `jQH_boundaryCoinvDelta`: the descent isomorphisms intertwine `j_*` on coinvariants with
  `j^H_*`; `jCoinv_surjective`, `jQH_surjective`: surjectivity descends.
* `j_surjective_Vnt`, `boundary_descent_K`: the instance `H = K`, `E = E_{n,t}`, `n > 0` used in the proof of Proposition 3.4.
* `RCos`, `trCoinv`, `transferCx`, `transfer_eq_resQ`: the literal chain-level right-coset-sum transfer `[y]_H ↦ ∑_{r ∈ H'\H} [r y]_{H'}` and its
  identification with `Naturality.resQ` (the `[H:H']`-times-average form).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma34BoundaryDescent

open TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

export TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
  (repN repDeltaN groupCoinvEquiv groupCoinvDelta repDeltaBd boundaryCoinvEquiv boundaryCoinvDelta jN jN_equivariant jCoinv
    jCoinvDelta jQH_boundaryCoinvEquiv jQH_boundaryCoinvDelta jCoinv_surjective jCoinvDelta_surjective jQH_surjective
    j_surjective_Vnt boundary_descent_K RCos trCoinv transferCx transfer_eq_resQ apply_avgR_sum)

end TernaryPeriodPolynomials.Argument.Statements.Lemma34BoundaryDescent
