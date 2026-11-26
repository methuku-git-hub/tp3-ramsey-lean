module

public import TP3.ExtractionError

@[expose] public section

namespace TP3.ExtractionParameters

theorem polynomial_exp_bound (k C : ℝ) (m : ℕ) (hk : 0 ≤ k) (hC : 0 ≤ C) :
    C*k^m ≤ Real.exp (C+(m:ℝ)*k) := by
  have hc : C ≤ Real.exp C := by have := Real.add_one_le_exp C; linarith
  have hx : k ≤ Real.exp k := by have := Real.add_one_le_exp k; linarith
  have hh := mul_le_mul hc (pow_le_pow_left₀ hk hx m) (pow_nonneg hk m) (Real.exp_nonneg C)
  simpa only [Real.exp_add,Real.exp_nat_mul] using hh

theorem t_formula {k : ℕ} (hk : 0 < k) :
    t k=(k:ℝ)*(40000*(k:ℝ)^25)^(400*k^53) := by
  have hm : b k*R k=400*k^53 := by unfold b R; ring
  have hτ : τ k=1/(40000*(k:ℝ)^25) := by dsimp [τ,r,R]; push_cast; congr 1; ring
  unfold t
  rw [hm,hτ]
  simp only [one_div,inv_pow,div_inv_eq_mul]

theorem t_exp_bound {k : ℕ} (hk : 40000 ≤ k) : t k ≤ Real.exp ((k:ℝ)^57) := by
  have hk0 : 0 < k := by omega
  have hk40000 : (40000:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hbase : 40000*(k:ℝ)^25 ≤ Real.exp ((k:ℝ)^2) := by
    apply (polynomial_exp_bound k 40000 25 hkpos.le (by norm_num)).trans
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [sq_nonneg ((k:ℝ)-40000)]
  have hkexp : (k:ℝ) ≤ Real.exp k := by have := Real.add_one_le_exp (k:ℝ); linarith
  have ht := mul_le_mul hkexp
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 40000*(k:ℝ)^25) hbase (400*k^53))
    (by positivity) (Real.exp_nonneg _)
  rw [← Real.exp_nat_mul,← Real.exp_add] at ht
  rw [t_formula hk0]
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hk55 : (k:ℝ) ≤ (k:ℝ)^55 := by
    simpa using pow_le_pow_right₀ hk1 (show 1 ≤ 55 by omega)
  have hk2 : (401:ℝ) ≤ (k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-40000)]
  calc
    _ = (k:ℝ)+400*(k:ℝ)^55 := by push_cast; ring
    _ ≤ 401*(k:ℝ)^55 := by linarith
    _ ≤ (k:ℝ)^2*(k:ℝ)^55 := mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = _ := by ring

theorem E_exp_bound {k : ℕ} (hk : 40000 ≤ k) : E k ≤ Real.exp ((k:ℝ)^59) := by
  have hk0 : 0 < k := by omega
  have hk40000 : (40000:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hc : 10000*(k:ℝ)^80 ≤ Real.exp ((k:ℝ)^2) := by
    apply (polynomial_exp_bound k 10000 80 hkpos.le (by norm_num)).trans
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [sq_nonneg ((k:ℝ)-40000)]
  have ht0 : 0 ≤ t k := hkpos.le.trans (t_ge_k hk0)
  have ht := mul_le_mul hc (pow_le_pow_left₀ ht0 (t_exp_bound hk) 7)
    (by positivity) (Real.exp_nonneg _)
  rw [← Real.exp_nat_mul,← Real.exp_add] at ht
  apply (E_bound hk0).trans (ht.trans _)
  apply Real.exp_le_exp.mpr
  have hp : (k:ℝ)^2 ≤ (k:ℝ)^57 := pow_le_pow_right₀ hk1 (by omega)
  have hk2 : (8:ℝ) ≤ (k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-40000)]
  calc
    _ ≤ 8*(k:ℝ)^57 := by norm_num; linarith
    _ ≤ (k:ℝ)^2*(k:ℝ)^57 := mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = _ := by ring

/-- An explicit threshold, chosen generously to keep all estimates elementary. -/
theorem parameter_threshold {k : ℕ} (hk : 40000 ≤ k) (x : ℝ)
    (hx : Real.exp ((k:ℝ)^60) ≤ x) :
    0 < x ∧ t k ≤ x ∧ E k ≤ x ∧ 2 < a₀ k*x ∧
    k/(2*x) ≤ extractionFraction (x^2) (a₀ k*x) (s₀ k*x) (c₀ k*x)
      (g₀ k*x) (b k) (R k) (h k) (r k) (t k/x) (τ k) (D k) := by
  have hk0 : 0 < k := by omega
  have hk40000 : (40000:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have ht : t k ≤ x := (t_exp_bound hk).trans ((Real.exp_le_exp.mpr
    (pow_le_pow_right₀ hk1 (show 57 ≤ 60 by omega))).trans hx)
  have hE : E k ≤ x := (E_exp_bound hk).trans ((Real.exp_le_exp.mpr
    (pow_le_pow_right₀ hk1 (show 59 ≤ 60 by omega))).trans hx)
  have ha : 2 < a₀ k*x := by
    have hp : 2*(k:ℝ)^8 ≤ (k:ℝ)^60 := by
      have hk2 : (2:ℝ) ≤ (k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-40000)]
      calc
        _ ≤ (k:ℝ)^2*(k:ℝ)^8 := mul_le_mul_of_nonneg_right hk2 (by positivity)
        _ = (k:ℝ)^10 := by ring
        _ ≤ _ := pow_le_pow_right₀ hk1 (by omega)
    have he := Real.add_one_le_exp ((k:ℝ)^60)
    have hh : 2*(k:ℝ)^8 < x := by linarith
    dsimp only [a₀]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (lt_div_iff₀ (by positivity)).mpr hh
  refine ⟨hxpos,ht,hE,ha,?_⟩
  rw [extractionFraction_scaled _ _ _ _ _ _ _ _ _ _ _ _ _ hxpos.ne' (t_cancel hk0)]
  change k/(2*x) ≤ A k/x-E k/x^2
  have hA := A_lower (show 10 ≤ k by omega)
  have hmain := div_le_div_of_nonneg_right hA hxpos.le
  have herr := div_le_div_of_nonneg_right hE (sq_nonneg x)
  have herr' : E k/x^2 ≤ 1/x := by convert herr using 1 <;> field_simp <;> ring
  have hsmall : 1/x ≤ (k:ℝ)/(4*x) := by
    apply (div_le_div_iff₀ hxpos (by positivity)).mpr
    nlinarith
  linear_combination hmain+herr'+hsmall

end TP3.ExtractionParameters
