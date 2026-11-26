module

public import TP3.ExtractionTheorem
public import TP3.VertexRestriction

@[expose] public section

namespace TP3

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem structured_independence_polynomial (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (T : Finset V) (hT : T.Nonempty)
    (hind : IndependentPairNeighborhoods (induced H T))
    (k : ℝ) (hk : Real.exp 600 ≤ k)
    (hdegree : ∀ v, (degree (induced H T) v : ℝ) ≤ 100*k^2) :
    ∃ I ⊆ T, Independent H I ∧ (T.card : ℝ)*Real.sqrt (Real.log k)/(10000*k) ≤ I.card := by
  have hkpos : 0 < k := (Real.exp_pos _).trans_le hk
  have hlog : 600 ≤ Real.log k := by
    simpa using Real.log_le_log (Real.exp_pos 600) hk
  let L := Real.log (10*k)/6
  have hlogmul : Real.log k ≤ Real.log (10*k) := Real.log_le_log hkpos (by nlinarith)
  have hL : 100 ≤ L := by dsimp [L]; linarith
  have hexp : Real.exp (12*L)=100*k^2 := by
    have heq : 12*L=2*Real.log (10*k) := by dsimp [L]; ring
    rw [heq]
    have hh := Real.exp_nat_mul (Real.log (10*k)) 2
    norm_num at hh
    rw [hh,Real.exp_log (by positivity)]
    ring
  have hinv : Real.exp (-6*L)=1/(10*k) := by
    have heq : -6*L = -Real.log (10*k) := by dsimp [L]; ring
    rw [heq,Real.exp_neg,Real.exp_log (by positivity)]
    simp only [one_div]
  obtain ⟨I,hIT,hI,hsize⟩ := structured_independence_on_set H hH hfree T hT hind L hL
    (fun v => by rw [hexp]; exact hdegree v)
  refine ⟨I,hIT,hI,le_trans ?_ hsize⟩
  rw [hinv]
  have hL0 : 0 ≤ L := by linarith
  have hroot : Real.sqrt (Real.log k) ≤ 3*Real.sqrt L := by
    have hh : Real.log k ≤ 9*L := by dsimp [L]; linarith
    have hh' := Real.sqrt_le_sqrt hh
    have h9 : Real.sqrt (9:ℝ)=3 := by
      rw [show (9:ℝ)=3^2 by norm_num,Real.sqrt_sq (by norm_num)]
    simpa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9),h9] using hh'
  have hroot' : Real.sqrt (Real.log k) ≤ 10*Real.sqrt L := by
    have := Real.sqrt_nonneg L
    linarith
  have hm := mul_le_mul_of_nonneg_left hroot' (Nat.cast_nonneg (α := ℝ) T.card)
  have hh := div_le_div_of_nonneg_right hm (show 0 ≤ 10000*k by positivity)
  convert hh using 1 <;> field_simp <;> ring

/-- The extraction and averaged arguments combined. The threshold and
all sampling parameters have been discharged. -/
theorem independence_from_extraction (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (hN : 0 < Fintype.card V)
    (k : ℕ) (hk : 40000 ≤ k) (hklog : Real.exp 600 ≤ (k:ℝ)) (x : ℝ)
    (hx : Real.exp ((k:ℝ)^60) ≤ x)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ x^2) :
    ∃ I : Finset V, Independent H I ∧
      (Fintype.card V : ℝ)*Real.sqrt (Real.log (k:ℝ))/(20000*x) ≤ I.card := by
  obtain ⟨T,hind,hTdegree,hTsize⟩ := extraction_theorem H hH hfree k hk x hx hdegree
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hNpos : (0:ℝ) < Fintype.card V := by exact_mod_cast hN
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    have ht : (0:ℝ) < T.card := (by positivity : (0:ℝ) < (Fintype.card V:ℝ)*k/(2*x)).trans_le hTsize
    exact_mod_cast ht
  obtain ⟨I,_hIT,hI,hsize⟩ := structured_independence_polynomial H hH hfree T hT hind k hklog hTdegree
  refine ⟨I,hI,le_trans ?_ hsize⟩
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hTsize (Real.sqrt_nonneg (Real.log (k:ℝ))))
    (show 0 ≤ 10000*(k:ℝ) by positivity)
  convert hh using 1 <;> field_simp <;> ring

end TP3
