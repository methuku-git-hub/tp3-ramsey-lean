module

public import TP3.RamseyScale
public import TP3.GeneralDegree
public import TP3.RamseyReduction

@[expose] public section

namespace TP3

/-- The unconditional independence estimate. All thresholds are absolute;
the integer scale is chosen separately for each order n. -/
theorem independence_bound : IndependenceBound := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (40000:ℝ) (Real.exp 600))
  have hKlog : Real.exp 600 ≤ (K:ℝ) := (le_max_right _ _).trans hK.le
  have hKlarge : 40000 ≤ K := by
    have hh : (40000:ℝ) ≤ K := (le_max_left _ _).trans hK.le
    exact_mod_cast hh
  let n₀ : ℕ := ⌈Real.exp (2*(K:ℝ)^60)⌉₊+2
  refine ⟨1/480000,by norm_num,n₀,?_⟩
  intro n hn H hH hfree
  have hn2 : 2 ≤ n := by dsimp [n₀] at hn; omega
  have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0:ℝ) < n := by linarith
  have hnlarge : Real.exp (2*(K:ℝ)^60) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (2*(K:ℝ)^60)⌉₊ ≤ n by
      dsimp [n₀] at hn; omega))
  let x := Real.sqrt (3*(n:ℝ))
  have hxpos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have hxsq : x^2=3*(n:ℝ) := Real.sq_sqrt (by positivity)
  have hthreshold : Real.exp ((K:ℝ)^60) ≤ x := by
    have heq : Real.exp ((K:ℝ)^60)^2=Real.exp (2*(K:ℝ)^60) := by
      simpa using (Real.exp_nat_mul ((K:ℝ)^60) 2).symm
    have he := Real.exp_pos ((K:ℝ)^60)
    nlinarith
  obtain ⟨k,hKk,hkx,hnext⟩ := exists_extraction_scale K x hthreshold
  have hk : 40000 ≤ k := hKlarge.trans hKk
  have hklog : Real.exp 600 ≤ (k:ℝ) := hKlog.trans (by exact_mod_cast hKk)
  have hdegree (v : Fin n) : (degree H v : ℝ) ≤ x^2 := by
    rw [hxsq]
    simpa using pathFree_degree_bound hH hfree v
  obtain ⟨I,hI,hsize⟩ := independence_from_extraction H hH hfree
    (by simpa using (show 0 < n by omega)) k hk hklog x hkx hdegree
  refine ⟨I,hI,le_trans ?_ hsize⟩
  simp only [Fintype.card_fin]
  have hlog := scale_logarithmic_gain n x hn1 hxpos hxsq k (by omega) hnext
  have hnroot : Real.sqrt (n:ℝ)^2=n := Real.sq_sqrt hnpos.le
  have hnroot0 := Real.sqrt_nonneg (n:ℝ)
  have hxupper : x ≤ 2*Real.sqrt (n:ℝ) := by nlinarith
  have hprod : Real.sqrt (n:ℝ)*x ≤ 2*(n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hxupper hnroot0
    nlinarith
  have hratio : Real.sqrt (n:ℝ)/2 ≤ (n:ℝ)/x := by
    apply (le_div_iff₀ hxpos).mpr
    linarith
  have hroot : Real.sqrt ((n:ℝ)*Real.log (Real.log (n:ℝ))) ≤
      12*(Real.sqrt (n:ℝ)*Real.sqrt (Real.log (k:ℝ))) := by
    have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hnpos.le)
    have h144 : Real.sqrt (144:ℝ)=12 := by
      rw [show (144:ℝ)=12^2 by norm_num,Real.sqrt_sq (by norm_num)]
    calc
      _ ≤ Real.sqrt ((n:ℝ)*(144*Real.log (k:ℝ))) := hh
      _ = Real.sqrt (144*((n:ℝ)*Real.log (k:ℝ))) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 144),h144,Real.sqrt_mul hnpos.le]
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg (Real.log (k:ℝ))))
    (show (0:ℝ) ≤ 20000 by norm_num)
  calc
    _ ≤ (Real.sqrt (n:ℝ)/2*Real.sqrt (Real.log (k:ℝ)))/20000 := by linarith
    _ ≤ _ := by convert hh using 1 <;> ring

end TP3
