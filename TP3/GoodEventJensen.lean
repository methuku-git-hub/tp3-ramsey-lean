module

public import TP3.Conditioning
public import TP3.PairRestrictions

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

/-- Jensen's inequality after retaining an event of probability at
least one half. The first moment is taken with its indicator, so no
unjustified independence or change of conditional law is involved. -/
theorem good_event_exp_lower (μ : FiniteLaw Ω) (G : Ω → Prop) (X : Ω → ℝ)
    (hg : (1:ℝ)/2 ≤ μ.event G) (C : ℝ) (hC : 0 ≤ C)
    (hm : μ.mean (fun ω => if G ω then X ω else 0) ≤ C) :
    (1:ℝ)/2*Real.exp (-2*C) ≤ μ.mean (fun ω => if G ω then Real.exp (-X ω) else 0) := by
  have hgpos : 0 < μ.event G := lt_of_lt_of_le (by norm_num) hg
  let ν := μ.condition G hgpos
  have hmean : ν.mean X ≤ 2*C := by
    rw [condition_mean]
    apply (div_le_iff₀ hgpos).mpr
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*C by positivity)
    nlinarith
  have hneg : ν.mean (fun ω => -X ω) = -ν.mean X := by
    simpa only [neg_one_mul] using ν.mean_mul_const (-1) X
  have hj := ν.exp_mean_le (fun ω => -X ω)
  rw [hneg] at hj
  have he : Real.exp (-2*C) ≤ ν.mean (fun ω => Real.exp (-X ω)) := by
    apply le_trans (Real.exp_le_exp.mpr (by linarith : -2*C ≤ -ν.mean X)) hj
  have hid : μ.mean (fun ω => if G ω then Real.exp (-X ω) else 0) =
      μ.event G*ν.mean (fun ω => Real.exp (-X ω)) := by
    rw [condition_mean]
    field_simp
  rw [hid]
  calc
    _ ≤ μ.event G*Real.exp (-2*C) := mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left he hgpos.le

end TP3.FiniteLaw
