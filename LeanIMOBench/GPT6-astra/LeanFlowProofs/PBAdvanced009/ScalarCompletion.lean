import Mathlib

theorem LeanFlowProofs.PB009.scalarCompletion
    (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbc : b ≠ c) :
    let d : ℝ := c - b
    let T : ℝ := a ^ 2 + b * c
    let W : ℝ := a ^ 2 * d ^ 2 + T ^ 2
    let s : ℝ := a * b * c / W
    ∀ t q u v w : ℝ,
      t ≠ 0 → q ≠ c →
      a * d * ((t * a * d) ^ 2 + (t * T) ^ 2) -
        a * (T + d ^ 2) * (t * a * d) - b * c * d * (t * T) = 0 →
      (s * a * d) ^ 2 + (s * T) ^ 2 -
        u * (s * a * d) - v * (s * T) + w = 0 →
      (t * a * d) ^ 2 + (t * T) ^ 2 -
        u * (t * a * d) - v * (t * T) + w = 0 →
      c ^ 2 - u * c + w = 0 →
      q ^ 2 - u * q + w = 0 →
      t = 1 / a ∧ q = b := by 
  dsimp only
  let d := c - b
  let T := a ^ 2 + b * c
  let W := a ^ 2 * d ^ 2 + T ^ 2
  let s := a * b * c / W
  change ∀ t q u v w : ℝ, t ≠ 0 → q ≠ c → _
  intro t q u v w ht hq h0 hs hp hcirc hqcirc
  change a * d * ((t * a * d)^2 + (t*T)^2) - a*(T+d^2)*(t*a*d) - b*c*d*(t*T) = 0 at h0
  change (s*a*d)^2 + (s*T)^2 - u*(s*a*d) - v*(s*T) + w = 0 at hs
  change (t*a*d)^2 + (t*T)^2 - u*(t*a*d) - v*(t*T) + w = 0 at hp
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hT : 0 < T := by dsimp [T]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hfac : d * t * W * (a*t-1) = 0 := by
    calc
      d * t * W * (a*t-1) = a * d * ((t * a * d)^2 + (t*T)^2) - a*(T+d^2)*(t*a*d) - b*c*d*(t*T) := by dsimp [W, T]; ring
      _ = 0 := h0
  have hat : a*t = 1 := by
    have := (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero (mul_ne_zero hd ht) (ne_of_gt hW))
    linarith
  have htval : t = 1/a := (eq_div_iff (ne_of_gt ha)).mpr (by nlinarith [hat])
  have hWs : W*s = a*b*c := by dsimp [s]; field_simp
  have hgap : a^2*b*c < W := by
    have hpos : 0 < a^2 * (b*c) := mul_pos (sq_pos_of_pos ha) (mul_pos hb hc)
    have hfour : 0 < (a^2)^2 := sq_pos_of_pos (sq_pos_of_pos ha)
    dsimp [W, T]
    nlinarith [sq_nonneg (a*d), sq_nonneg (b*c)]
  have hst : t-s ≠ 0 := by
    intro heq
    have he : s = t := by linarith
    rw [he] at hWs
    have : W = a^2*b*c := by nlinarith only [hat, congrArg (fun x : ℝ => a*x) hWs, congrArg (fun x : ℝ => W*x) hat]
    linarith
  have hs' : W*s^2 - (u*a*d+v*T)*s + w = 0 := by
    dsimp [W]; nlinarith only [hs]
  have hp' : W*t^2 - (u*a*d+v*T)*t + w = 0 := by
    dsimp [W]; nlinarith only [hp]
  have hwfac : (t-s)*(w-W*s*t) = 0 := by
    nlinarith only [congrArg (fun x : ℝ => t*x) hs', congrArg (fun x : ℝ => s*x) hp']
  have hw : w = W*s*t := by
    have := (mul_eq_zero.mp hwfac).resolve_left hst
    linarith
  have hwbc : w = b*c := by
    calc
      w = W*s*t := hw
      _ = (a*t)*(b*c) := by rw [hWs]; ring
      _ = b*c := by rw [hat]; ring
  have hqfac : (q-c)*(w-c*q) = 0 := by
    nlinarith only [congrArg (fun x : ℝ => q*x) hcirc, congrArg (fun x : ℝ => c*x) hqcirc]
  have hwcq : w = c*q := by
    have := (mul_eq_zero.mp hqfac).resolve_left (sub_ne_zero.mpr hq)
    linarith
  exact ⟨htval, by nlinarith only [hwbc, hwcq, hc]⟩

