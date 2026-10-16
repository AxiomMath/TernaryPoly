module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Reference
public import TernaryPeriodPolynomials.ModularForm.Symbol.SLAction

@[expose] public section

noncomputable section

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryModularSymbol

/-- Actual holomorphic modular symbol: endpoint at source minus endpoint at target, extended
linearly over the literal rational augmentation kernel. -/
def full {d : ℕ} (f : Forms d) : St →ₗ[ℚ] Functions :=
  (-Finsupp.lsum ℚ (fun L => LinearMap.toSpanSingleton ℚ Functions (endpoint f L))).comp
    St.subtype

/-- The orientation agrees with the actual reference symbol infinity to zero. -/
theorem full_symbol {d : ℕ} (f : Forms d) (L M : Line) (v : Coordinates) :
    full f (symbol L M) v = endpoint f L v - endpoint f M v := by
  simp only [full, LinearMap.comp_apply, LinearMap.neg_apply, Submodule.subtype_apply,
    symbol_val, map_sub, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul, Pi.neg_apply, Pi.sub_apply]
  ring

theorem full_symbol_sl {d : ℕ} (f : Forms d) (g : SL2) (L M : Line) :
    full f (action (slRational g) (symbol L M)) = functionAction (slRational g) (full f (symbol L M)) := by
  funext v
  rw [action_symbol, full_symbol, functionAction_slRational, full_symbol,
    endpoint_sl, endpoint_sl]
  ring

/-- Full-level special-linear equivariance of the genuine analytic symbol on every divisor. -/
theorem full_equivariant {d : ℕ} (f : Forms d) (g : SL2) (c : St) :
    full f (action (slRational g) c) = functionAction (slRational g) (full f c) := by
  have hc : c ∈ Submodule.span ℚ (Set.range (symbol infinity)) := by rw [span_symbols]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc => obtain ⟨M,rfl⟩ := hc; exact full_symbol_sl f g infinity M
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add, hc, hd]
  | smul q c _ hc => simp only [map_smul, hc]

/-- Equivalent fixed-vector form of the exact analytic SL2 equivariance. -/
theorem full_fixed_sl {d : ℕ} (f : Forms d) (g : SL2) :
    homAction functionAction (slRational g) (full f) = full f :=
  (homAction_fixed_iff _ _ _).2 (full_equivariant f g)

/-- The reference value is the actual full period polynomial, embedded faithfully by evaluation. -/
theorem full_reference {d : ℕ} (hd : Even d) (f : Forms d) :
    full f reference = evaluate (period f) := by
  funext v
  rw [reference, full_symbol, ←infinity_eq_augmentedLine, endpoint_infinity, endpoint_zero hd]
  simp [evaluate]

end TernaryPoly.BinaryCuspSymbol
