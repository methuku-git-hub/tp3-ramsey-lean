module

public import TP3.PairRestrictions

@[expose] public section

namespace TP3

/-- The cost x log(ep/x) increases up to p. The proof uses only
log z ≤ z-1, avoiding differentiation. -/
theorem entropy_cost_mono {p x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hyp : y ≤ p) :
    x * Real.log (Real.exp 1 * p / x) ≤
      y * Real.log (Real.exp 1 * p / y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hp : 0 < p := hy.trans_le hyp
  have hlog : 0 ≤ Real.log (p/y) :=
    Real.log_nonneg ((one_le_div hy).mpr hyp)
  have hupper := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hmul := mul_le_mul_of_nonneg_left hupper hx.le
  have hfrac : x * (y/x-1) = y-x := by field_simp
  rw [hfrac] at hmul
  have hsplit : Real.log (Real.exp 1 * p / x) =
      1 + Real.log (p/y) + Real.log (y/x) := by
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hp.ne') hx.ne',
      Real.log_mul (Real.exp_ne_zero 1) hp.ne', Real.log_exp,
      Real.log_div hp.ne' hy.ne', Real.log_div hy.ne' hx.ne']
    ring
  have hbase : Real.log (Real.exp 1 * p / y) = 1 + Real.log (p/y) := by
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hp.ne') hy.ne',
      Real.log_mul (Real.exp_ne_zero 1) hp.ne', Real.log_exp,
      Real.log_div hp.ne' hy.ne']
    ring
  rw [hsplit,hbase]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hlog]

/-- The precise algebraic implication needed at the end of the proof.
The hypotheses are explicit estimates, not assumptions of the final
Ramsey theorem. Their derivation from the random experiment remains a
separate proof obligation. Here w represents E[W(I)]/N. -/
theorem density_gain_of_estimates {p δ D L ρ w : ℝ}
    (hp : 0 < p) (hp_small : p ≤ 1/4) (hδ : 0 < δ) (hD : 0 < D)
    (hL : 0 < L) (hscale : δ^2 * D = L)
    (hsmall : δ/100 ≤ p) (hρ : 0 < ρ) (hw : 0 ≤ w)
    (hcharge : δ*w ≤ ρ * Real.log (Real.exp 1*p/ρ))
    (haverage : Real.log (p/(4*ρ)) ≤
      4*Real.log 2/(1-p)*w + 4*δ*D*ρ/(1-p))
    (hlog_upper : Real.log (100*Real.exp 1*p/δ) ≤ 2*L)
    (hlog_lower : L/5 < Real.log (25*p/δ)) :
    δ/100 < ρ := by
  by_contra! hρsmall
  have hden : 0 < 1-p := by linarith
  have hcost := entropy_cost_mono hρ hρsmall hsmall
  have hquot : Real.exp 1*p/(δ/100) = 100*Real.exp 1*p/δ := by ring
  rw [hquot] at hcost
  have hmul := mul_le_mul_of_nonneg_left hlog_upper (by positivity : 0 ≤ δ/100)
  have hwupper : w ≤ L/50 := by
    have hh := hcharge.trans (hcost.trans hmul)
    nlinarith
  have hδterm : δ*D*ρ ≤ L/100 := by
    have hm := mul_le_mul_of_nonneg_left hρsmall (mul_pos hδ hD).le
    nlinarith [hscale]
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlogw : Real.log 2*w ≤ w := by nlinarith
  have hrhs : 4*Real.log 2/(1-p)*w + 4*δ*D*ρ/(1-p) ≤ L/5 := by
    have heq : 4*Real.log 2/(1-p)*w + 4*δ*D*ρ/(1-p) =
        (4*Real.log 2*w+4*δ*D*ρ)/(1-p) := by ring
    rw [heq, div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hp_small hL.le]
  have hratio : 25*p/δ ≤ p/(4*ρ) := by
    apply (div_le_div_iff₀ hδ (by positivity : 0 < 4*ρ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρsmall hp.le]
  have hlog_ratio := Real.log_le_log (by positivity : 0 < 25*p/δ) hratio
  exact (not_lt_of_ge (hlog_ratio.trans (haverage.trans hrhs))) hlog_lower

end TP3
