module

public import TP3.ExtractionGrowth

@[expose] public section

namespace TP3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extract a positive proportion of the enlarged sample, with independent
pair neighbourhoods and maximum degree at most 100 k squared. -/
theorem extraction_theorem (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (k : ℕ) (hk : 40000 ≤ k) (x : ℝ)
    (hx : Real.exp ((k:ℝ)^60) ≤ x)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ x^2) :
    ∃ T : Finset V, IndependentPairNeighborhoods (induced H T) ∧
      (∀ v, (degree (induced H T) v : ℝ) ≤ 100*(k:ℝ)^2) ∧
      (Fintype.card V : ℝ)*k/(2*x) ≤ T.card := by
  obtain ⟨hxpos,ht,hE,ha,hfraction⟩ := ExtractionParameters.parameter_threshold hk x hx
  have hk0 : 0 < k := by omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk0
  obtain ⟨hg,hb,hr,hh⟩ := ExtractionParameters.parameter_ratios hk0 x hxpos
  obtain ⟨T,_hF,_h4,hind,hTdegree,hsize⟩ := quantitative_extraction H hH hfree
    (x^2) (ExtractionParameters.a₀ k*x) (ExtractionParameters.s₀ k*x)
    (ExtractionParameters.c₀ k*x) (ExtractionParameters.g₀ k*x)
    (ExtractionParameters.b k) (ExtractionParameters.R k) (ExtractionParameters.h k)
    (ExtractionParameters.r k) (ExtractionParameters.t k/x) (ExtractionParameters.τ k)
    (ExtractionParameters.D k) (sq_nonneg x) hdegree ha
    (by unfold ExtractionParameters.s₀; positivity)
    (by unfold ExtractionParameters.c₀; positivity)
    (by unfold ExtractionParameters.g₀; positivity)
    hg.le hb.le hr.le hh.le (ExtractionParameters.R_pos hk0)
    (div_nonneg (hkpos.le.trans (ExtractionParameters.t_ge_k hk0)) hxpos.le)
    ((div_le_one hxpos).mpr ht) (ExtractionParameters.τ_pos hk0).le
    (ExtractionParameters.τ_le_one hk0) (by unfold ExtractionParameters.D; positivity)
  refine ⟨T,hind,hTdegree,?_⟩
  have hh := (mul_le_mul_of_nonneg_left hfraction (Nat.cast_nonneg (α := ℝ) (Fintype.card V))).trans hsize
  convert hh using 1 <;> ring

end TP3
