module

public import TP3.ExtractionIndependence

@[expose] public section

namespace TP3

theorem nat_le_scale_exp (j : ℕ) : (j:ℝ) ≤ Real.exp ((j:ℝ)^60) := by
  by_cases hj : j=0
  · simp [hj]
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hp : (j:ℝ) ≤ (j:ℝ)^60 := by
    simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 60 by omega)
  have he := Real.add_one_le_exp ((j:ℝ)^60)
  linarith

/-- Choose the largest integer whose extraction threshold is available.
The next threshold bounds the logarithmic loss without using real roots. -/
theorem exists_extraction_scale (K : ℕ) (x : ℝ) (hx : Real.exp ((K:ℝ)^60) ≤ x) :
    ∃ k : ℕ, K ≤ k ∧ Real.exp ((k:ℝ)^60) ≤ x ∧
      x < Real.exp (((k:ℝ)+1)^60) := by
  classical
  obtain ⟨M,hM⟩ := exists_nat_gt x
  let F := (Finset.range (M+1)).filter (fun j : ℕ => Real.exp ((j:ℝ)^60) ≤ x)
  have hK : K ∈ F := by
    have hh : (K:ℝ) < M := lt_of_le_of_lt ((nat_le_scale_exp K).trans hx) hM
    have hKM : K < M := by exact_mod_cast hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hx⟩
  obtain ⟨k,hk,hmax⟩ := F.exists_max_image id ⟨K,hK⟩
  refine ⟨k,hmax K hK,(Finset.mem_filter.mp hk).2,?_⟩
  by_contra! hnext
  have hn : Real.exp (((k+1:ℕ):ℝ)^60) ≤ x := by simpa using hnext
  have hh : ((k+1:ℕ):ℝ) < M := lt_of_le_of_lt ((nat_le_scale_exp (k+1)).trans hn) hM
  have hkm : k+1 < M := by exact_mod_cast hh
  have hm : k+1 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn⟩
  have := hmax (k+1) hm
  change k+1 ≤ k at this
  omega

theorem scale_logarithmic_gain (n x : ℝ) (hn : 1 < n) (hx : 0 < x)
    (hxsq : x^2=3*n) (k : ℕ) (hk : 2 ≤ k)
    (hnext : x < Real.exp (((k:ℝ)+1)^60)) :
    Real.log (Real.log n) ≤ 144*Real.log (k:ℝ) := by
  have hn0 : 0 < n := by linarith
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hkp : 0 < (k:ℝ)+1 := by linarith
  have hlx : Real.log x ≤ ((k:ℝ)+1)^60 := by
    simpa using Real.log_le_log hx hnext.le
  have hln : Real.log n ≤ 2*Real.log x := by
    have hh := Real.log_le_log hn0 (show n ≤ x^2 by linarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hln' : Real.log n ≤ 2*((k:ℝ)+1)^60 := by linarith
  have hll := Real.log_le_log (Real.log_pos hn) hln'
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hkp.ne'),Real.log_pow] at hll
  have hklog : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hk2
  have hnextlog : Real.log ((k:ℝ)+1) ≤ 2*Real.log (k:ℝ) := by
    have hh := Real.log_le_log hkp (show (k:ℝ)+1 ≤ (k:ℝ)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  norm_num at hll
  linarith

end TP3
