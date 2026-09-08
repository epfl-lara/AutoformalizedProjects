import Mathlib

theorem LeanFlowProofs.PB003.scalarData
    (x y z r R : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hinradius : r ^ 2 * (x + y + z) = x * y * z)
    (hcircumradius : 4 * R * r * (x + y + z) =
      (y + z) * (z + x) * (x + y)) :
    let s : ℝ := x + y + z;
    2 * r < R ∧
      (∀ t : ℝ, t ∈ ({x, y, z} : Set ℝ) →
        r * (1 + r ^ 2 / t ^ 2) < R ∧
          ((s - t) / (s + t)) * (t ^ 2 + r ^ 2) =
            2 * R * r * (1 - (s - t) / (s + t))) ∧
      (s - x) / (s + x) ≠ (s - y) / (s + y) := by 
  dsimp
  have hs : 0 < x + y + z := by positivity
  have heuler : 2 * r < R := by
    have hpos : 0 < x * (y-z)^2 + y * (z-x)^2 + z * (x-y)^2 := by
      have : 0 < z * (x-y)^2 := mul_pos hz (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
      positivity
    have hid : (y+z)*(z+x)*(x+y) - 8*x*y*z =
        x*(y-z)^2 + y*(z-x)^2 + z*(x-y)^2 := by ring
    have hp : 0 < 4*r*(x+y+z) := by positivity
    nlinarith
  have localData : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      r^2*(a+b+c)=a*b*c →
      4*R*r*(a+b+c)=(b+c)*(c+a)*(a+b) →
      r*(1+r^2/a^2)<R ∧
      ((a+b+c-a)/(a+b+c+a))*(a^2+r^2) =
        2*R*r*(1-(a+b+c-a)/(a+b+c+a)) := by
    intro a b c ha hb hc hi ho
    have hs' : 0 < a+b+c := by positivity
    have hid : (b+c)*(a^2+r^2) = 4*R*r*a := by
      have h1 := congrArg (fun t : ℝ => t * a) ho
      have h2 := congrArg (fun t : ℝ => t * (b+c)) hi
      apply (mul_right_cancel₀ (ne_of_gt hs'))
      nlinarith [h1, h2]
    have hbound : 4*r^2 < a*(b+c) := by
      have hpos : 0 < a^2*(b+c) + a*(b-c)^2 := by positivity
      nlinarith
    constructor
    · have hclean : r*(1+r^2/a^2)*a^2 = r*(a^2+r^2) := by
        field_simp
      have hm := mul_lt_mul_of_pos_right hbound (show 0 < a^2+r^2 by positivity)
      have hh := congrArg (fun t : ℝ => t*a) hid
      have hp : 0 < 4*r := by positivity
      have hf : r*(a^2+r^2) < R*a^2 := by nlinarith
      nlinarith [sq_pos_of_pos ha]
    · have hd : a+b+c+a ≠ 0 := ne_of_gt (by positivity)
      field_simp
      nlinarith [hid]
  refine ⟨heuler, ?_, ?_⟩
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact localData x y z hx hy hz hinradius hcircumradius
    · have hi : r^2*(y+z+x)=y*z*x := by nlinarith [hinradius]
      have ho : 4*R*r*(y+z+x)=(z+x)*(x+y)*(y+z) := by nlinarith [hcircumradius]
      convert localData y z x hy hz hx hi ho using 1 <;> ring
    · have hi : r^2*(z+x+y)=z*x*y := by nlinarith [hinradius]
      have ho : 4*R*r*(z+x+y)=(x+y)*(y+z)*(z+x) := by nlinarith [hcircumradius]
      convert localData z x y hz hx hy hi ho using 1 <;> ring
  · intro heq
    have hd1 : x+y+z+x ≠ 0 := ne_of_gt (by positivity)
    have hd2 : x+y+z+y ≠ 0 := ne_of_gt (by positivity)
    have hh := (div_eq_div_iff hd1 hd2).mp heq
    apply hxy
    nlinarith
