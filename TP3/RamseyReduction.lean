module

public import TP3.Structure
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace TP3

/-- The independence estimate needed to deduce the main Ramsey theorem.
This is a proposition to be proved by the sampling argument. -/
def IndependenceBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ H : Finset (Finset (Fin n)), IsTripleSystem H → ¬ HasTightPath H →
      ∃ S : Finset (Fin n), Independent H S ∧
        c * Real.sqrt ((n : ℝ) * Real.log (Real.log (n : ℝ))) ≤ S.card

/-- The conversion in Section 5, including the integer rounding and the
choice of an independent subset with exactly t vertices. -/
theorem ramsey_bound_of_independence_bound (h : IndependenceBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, 3 ≤ t₀ ∧
      ∀ t : ℕ, t₀ ≤ t →
        ∃ N : ℕ, (N : ℝ) ≤ C * (t : ℝ) ^ 2 / Real.log (Real.log (t : ℝ)) ∧
          ∀ H : Finset (Finset (Fin N)), IsTripleSystem H →
            HasTightPath H ∨
              ∃ S : Finset (Fin N), S.card = t ∧ Independent H S := by
  obtain ⟨c,hc,n₀,hi⟩ := h
  obtain ⟨m,hm⟩ := exists_nat_gt (Real.exp 1)
  let A : ℝ := max 1 (1 / c ^ 2)
  have hA : 1 ≤ A := le_max_left _ _
  have hAc : 1 ≤ c ^ 2 * A := by
    have hpos : 0 < c ^ 2 := sq_pos_of_pos hc
    have hh : 1 / c ^ 2 ≤ A := le_max_right _ _
    have := (div_le_iff₀ hpos).mp hh
    nlinarith
  refine ⟨A+1, by linarith, max n₀ (max 3 m), ?_, ?_⟩
  · omega
  intro t ht
  have ht3 : 3 ≤ t := by omega
  have htm : m ≤ t := by omega
  have htn : n₀ ≤ t := by omega
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have hexpt : Real.exp 1 < (t : ℝ) := hm.trans_le (by exact_mod_cast htm)
  have hlogt : 1 < Real.log (t : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos 1) hexpt
    simpa using this
  let L : ℝ := Real.log (Real.log (t : ℝ))
  have hL : 0 < L := Real.log_pos hlogt
  have hLt : L ≤ (t : ℝ) :=
    (Real.log_le_self (by linarith : 0 ≤ Real.log (t : ℝ))).trans
      (Real.log_le_self htpos.le)
  have htbase : (t : ℝ) ≤ (t : ℝ)^2 / L := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLt htpos.le]
  let N : ℕ := ⌈A * (t : ℝ)^2 / L⌉₊
  have hNlow : A * (t : ℝ)^2 / L ≤ (N : ℝ) := Nat.le_ceil _
  have hbase : (t : ℝ)^2 / L ≤ A * (t : ℝ)^2 / L := by
    have hp : 0 ≤ (t : ℝ)^2 / L := by positivity
    calc
      (t : ℝ)^2 / L ≤ A * ((t : ℝ)^2 / L) := by nlinarith
      _ = _ := by ring
  have htN : (t : ℝ) ≤ N := htbase.trans (hbase.trans hNlow)
  have htNnat : t ≤ N := by exact_mod_cast htN
  have hNpos : 0 < (N : ℝ) := htpos.trans_le htN
  have hNupper : (N : ℝ) ≤ (A+1) * (t : ℝ)^2 / L := by
    have hbpos : 0 ≤ A * (t : ℝ)^2 / L := by positivity
    have hh : (N : ℝ) < A * (t : ℝ)^2 / L + 1 := Nat.ceil_lt_add_one hbpos
    have hbone : 1 ≤ (t : ℝ)^2 / L := ht1.trans htbase
    calc
      (N : ℝ) ≤ A * (t : ℝ)^2 / L + 1 := hh.le
      _ ≤ A * (t : ℝ)^2 / L + (t : ℝ)^2 / L := by linarith
      _ = _ := by ring
  refine ⟨N, hNupper, ?_⟩
  intro H hH
  by_cases hp : HasTightPath H
  · exact Or.inl hp
  right
  obtain ⟨S,hS,hcard⟩ := hi N (htn.trans htNnat) H hH hp
  have hlogN : Real.log (t : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log htpos htN
  have hLN : L ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log (by linarith) hlogN
  have hNL : A * (t : ℝ)^2 ≤ (N : ℝ) * L :=
    (div_le_iff₀ hL).mp hNlow
  have hquad : (t : ℝ)^2 ≤ c^2 * ((N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    calc
      (t : ℝ)^2 ≤ (c^2 * A) * (t : ℝ)^2 := by
        nlinarith [sq_nonneg (t : ℝ)]
      _ = c^2 * (A * (t : ℝ)^2) := by ring
      _ ≤ c^2 * ((N : ℝ) * L) := mul_le_mul_of_nonneg_left hNL (sq_nonneg c)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLN hNpos.le) (sq_nonneg c)
  have hroot : (t : ℝ) ≤ c * Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    have hh := Real.sqrt_le_sqrt hquad
    simpa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
      abs_of_pos hc, abs_of_nonneg htpos.le] using hh
  have htc : t ≤ S.card := by exact_mod_cast (hroot.trans hcard)
  obtain ⟨T,hTS,hTcard⟩ := Finset.exists_subset_card_eq htc
  exact ⟨T,hTcard,independent_mono hS hTS⟩

end TP3
