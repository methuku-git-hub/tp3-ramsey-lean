module

public import TP3.DensityInequality

@[expose] public section

namespace TP3

/-- Reparametrize D as exp(12L). These are exactly the manuscript's
p = D^(-5/12) and δ = sqrt(log D/(12D)), expressed without fractional
powers. Explicit estimates hold already for L ≥ 100. -/
theorem parameter_choice (L : ℝ) (hL : 100 ≤ L) :
    let D := Real.exp (12*L)
    let p := Real.exp (-5*L)
    let δ := Real.sqrt L * Real.exp (-6*L)
    0 < p ∧ p ≤ 1/4 ∧ 0 < δ ∧ 0 < D ∧ 0 < L ∧
      δ^2 * D = L ∧ δ/100 ≤ p ∧
      Real.log (100*Real.exp 1*p/δ) ≤ 2*L ∧
      L/5 < Real.log (25*p/δ) ∧
      D^2 * (δ*p^4+p^5) ≤ 1/2 := by
  dsimp only
  have hLpos : 0 < L := by linarith
  have hspos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hs2 : (Real.sqrt L)^2 = L := Real.sq_sqrt hLpos.le
  have hsle : Real.sqrt L ≤ L := by nlinarith
  have hlogs : Real.log (Real.sqrt L) = Real.log L/2 := Real.log_sqrt hLpos.le
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogLle : Real.log L ≤ L-1 := Real.log_le_sub_one_of_pos hLpos
  have hexpL : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hsmall : Real.exp (-L) ≤ 1/4 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos L)]
    linarith [Real.add_one_le_exp L]
  have hp_small : Real.exp (-5*L) ≤ 1/4 := by
    apply (Real.exp_le_exp.mpr (by linarith : -5*L ≤ -L)).trans hsmall
  have hscale : (Real.sqrt L * Real.exp (-6*L))^2 * Real.exp (12*L) = L := by
    rw [mul_pow, ← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    have he : Real.exp ((2:ℝ)*(-6*L)) * Real.exp (12*L) = 1 := by
      rw [← Real.exp_add]
      have hz : (2:ℝ)*(-6*L)+12*L = 0 := by ring
      rw [hz, Real.exp_zero]
    calc
      _ = (Real.sqrt L)^2 * (Real.exp ((2:ℝ)*(-6*L)) * Real.exp (12*L)) := by ring
      _ = L := by rw [he, mul_one, hs2]
  have hδsmall : Real.sqrt L * Real.exp (-6*L) /100 ≤ Real.exp (-5*L) := by
    have he : Real.exp (-5*L) = Real.exp L * Real.exp (-6*L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have h : Real.sqrt L /100 ≤ Real.exp L := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos (-6*L)).le]
  have hlog100 : Real.log (100:ℝ) ≤ 99 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
    linarith
  have hlog25 : 0 ≤ Real.log (25:ℝ) := Real.log_nonneg (by norm_num)
  have hupper_id :
      Real.log (100*Real.exp 1*Real.exp (-5*L)/(Real.sqrt L*Real.exp (-6*L))) =
        Real.log 100+1+L-Real.log L/2 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _),
      Real.log_mul hspos.ne' (Real.exp_ne_zero _)]
    simp only [Real.log_exp, hlogs]
    ring
  have hlower_id :
      Real.log (25*Real.exp (-5*L)/(Real.sqrt L*Real.exp (-6*L))) =
        Real.log 25+L-Real.log L/2 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _),
      Real.log_mul hspos.ne' (Real.exp_ne_zero _)]
    simp only [Real.log_exp, hlogs]
    ring
  have hbad_id :
      Real.exp (12*L)^2 *
        ((Real.sqrt L*Real.exp (-6*L))*Real.exp (-5*L)^4+Real.exp (-5*L)^5) =
        Real.sqrt L*Real.exp (-2*L)+Real.exp (-L) := by
    simp only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_add]
    have hfirst : Real.exp ((2:ℝ)*(12*L)) *
        ((Real.sqrt L*Real.exp (-6*L))*Real.exp ((4:ℝ)*(-5*L))) =
        Real.sqrt L*Real.exp (-2*L) := by
      calc
        _ = Real.sqrt L * (Real.exp ((2:ℝ)*(12*L))*
              Real.exp (-6*L)*Real.exp ((4:ℝ)*(-5*L))) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
    rw [hfirst, ← Real.exp_add]
    congr 2
    ring
  have hbad : Real.sqrt L*Real.exp (-2*L)+Real.exp (-L) ≤ 1/2 := by
    have he : Real.exp L*Real.exp (-2*L) = Real.exp (-L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_right (hsle.trans hexpL) (Real.exp_pos (-2*L)).le
    rw [he] at hh
    linarith
  refine ⟨Real.exp_pos _,hp_small,mul_pos hspos (Real.exp_pos _),Real.exp_pos _,
    hLpos,hscale,hδsmall,?_,?_,?_⟩
  · rw [hupper_id]
    linarith
  · rw [hlower_id]
    linarith
  · rwa [hbad_id]

end TP3
