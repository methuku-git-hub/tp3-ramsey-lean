module

public import TP3.ExtractionParameters

@[expose] public section

namespace TP3.ExtractionParameters

theorem t_ge_k {k : ℕ} (hk : 0 < k) : (k:ℝ) ≤ t k := by
  unfold t
  apply (le_div_iff₀ (pow_pos (τ_pos hk) _)).mpr
  have hh := pow_le_one₀ (τ_pos hk).le (τ_le_one hk) (n := b k*R k)
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) k)]

theorem collision_bound {k : ℕ} (hk : 0 < k) (j : ℕ) (hj : j ≤ 5) :
    collisionCoefficient (b k) (h k) (g₀ k) (t k) j ≤
      350*(k:ℝ)^80*(t k)^7 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ht1 : 1 ≤ t k := hk1.trans (t_ge_k hk)
  have hk8 : 1 ≤ (k:ℝ)^8 := one_le_pow₀ hk1
  have hj' : (j:ℝ) ≤ 5 := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hj2 : (j:ℝ)^2 ≤ 25 := by nlinarith
  have hp1 : (t k)^(j+1) ≤ (t k)^7 := pow_le_pow_right₀ ht1 (by omega)
  have hp2 : (t k)^(j+2) ≤ (t k)^7 := pow_le_pow_right₀ ht1 (by omega)
  have hins : (j:ℝ)*(t k)^(j+1)+g₀ k*(t k)^(j+2) ≤
      7*(k:ℝ)^8*(t k)^7 := by
    have h₁ := mul_le_mul hj' hp1 (by positivity) (by norm_num : (0:ℝ) ≤ 5)
    have h₂ := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ g₀ k by unfold g₀; positivity)
    have h₃ := mul_le_mul_of_nonneg_right hk8 (show 0 ≤ 5*(t k)^7 by positivity)
    dsimp only [g₀] at h₂ ⊢
    nlinarith
  unfold collisionCoefficient
  calc
    _ ≤ 25*(b k:ℝ)*h k*(7*(k:ℝ)^8*(t k)^7) := by
      gcongr
      unfold g₀
      positivity
    _ = _ := by unfold b h; push_cast; ring

theorem E_bound {k : ℕ} (hk : 0 < k) : E k ≤ 10000*(k:ℝ)^80*(t k)^7 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have ht1 : 1 ≤ t k := hk1.trans (t_ge_k hk)
  have ht0 : 0 ≤ t k := by linarith
  let Z := (k:ℝ)^80*(t k)^7
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have h72 : (k:ℝ)^72 ≤ (k:ℝ)^80 := pow_le_pow_right₀ hk1 (by omega)
  have h46 : (k:ℝ)^46 ≤ (k:ℝ)^80 := pow_le_pow_right₀ hk1 (by omega)
  have h80 : (1:ℝ) ≤ (k:ℝ)^80 := one_le_pow₀ hk1
  have ht3 : (t k)^3 ≤ (t k)^7 := pow_le_pow_right₀ ht1 (by omega)
  have ht4 : (t k)^4 ≤ (t k)^7 := pow_le_pow_right₀ ht1 (by omega)
  have ht7 : 1 ≤ (t k)^7 := one_le_pow₀ ht1
  have h₁ : 3*g₀ k*b k*h k*(t k)^3 ≤ 12*Z := by
    have hh := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ 12*(k:ℝ)^80 by positivity)
    convert hh using 1 <;> dsimp [g₀,b,h,Z] <;> push_cast <;> ring
  have h₂ : 54*(b k:ℝ)*h k*(t k)^4 ≤ 108*Z := by
    have hh := mul_le_mul h72 ht4 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 108 by norm_num)
    convert hh' using 1 <;> dsimp [b,h,Z] <;> push_cast <;> ring
  have h₃ : (r k:ℝ)*h k*(k:ℝ)^2 ≤ 2*Z := by
    have hh := mul_le_mul h46 ht7 (by norm_num : (0:ℝ) ≤ 1) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 2 by norm_num)
    convert hh' using 1 <;> dsimp [r,h,Z] <;> push_cast <;> ring
  have hcoef1 : g₀ k/(2*R k) ≤ 1 := by
    have heq : g₀ k/(2*R k)=1/(200*(k:ℝ)) := by dsimp [g₀,R]; push_cast; field_simp <;> ring
    rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcoef2 : 1/s₀ k ≤ 1 := by
    apply (div_le_iff₀ (by unfold s₀; positivity)).mpr
    simpa [s₀] using one_le_pow₀ hk1 (n := 2)
  have hcoef3 : s₀ k*(2*a₀ k+c₀ k*r k) ≤ 4 := by
    have heq : s₀ k*(2*a₀ k+c₀ k*r k)=2/(k:ℝ)^6+2/(k:ℝ)^8 := by
      dsimp [s₀,a₀,c₀,r]; push_cast; field_simp <;> ring
    rw [heq]
    have h6 : 2/(k:ℝ)^6 ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by
      have := one_le_pow₀ hk1 (n := 6); linarith)
    have h8 : 2/(k:ℝ)^8 ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by
      have := one_le_pow₀ hk1 (n := 8); linarith)
    linarith
  have hcoef4 : 1/D k ≤ 1 := by
    apply (div_le_iff₀ (by unfold D; positivity)).mpr
    unfold D
    have := one_le_pow₀ hk1 (n := 2)
    linarith
  have hJ (j : ℕ) (hj : j ≤ 5) : collisionCoefficient (b k) (h k) (g₀ k) (t k) j ≤ 350*Z := by
    simpa only [Z,mul_assoc] using collision_bound hk j hj
  have hJ0 (j : ℕ) : 0 ≤ collisionCoefficient (b k) (h k) (g₀ k) (t k) j := by
    unfold collisionCoefficient g₀; positivity
  have h₄ := mul_le_mul hcoef1 (hJ 2 (by omega)) (hJ0 2) (by norm_num : (0:ℝ) ≤ 1)
  have h₅ := mul_le_mul hcoef2 (hJ 2 (by omega)) (hJ0 2) (by norm_num : (0:ℝ) ≤ 1)
  have h₆ := mul_le_mul hcoef3 (hJ 5 (by omega)) (hJ0 5) (by norm_num : (0:ℝ) ≤ 4)
  have h₇ : (t k)^4 ≤ Z := by
    have hh := mul_le_mul h80 ht4 (by positivity) (by positivity)
    simpa only [one_mul] using hh
  have h₈ := mul_le_mul hcoef4 (hJ 3 (by omega)) (hJ0 3) (by norm_num : (0:ℝ) ≤ 1)
  unfold E errorCoefficient
  dsimp only [Z] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hZ
  linear_combination h₁+h₂+h₃+h₄+h₅+h₆+h₇+h₈+7427*hZ

end TP3.ExtractionParameters
