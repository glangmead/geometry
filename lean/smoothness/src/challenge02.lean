import data.real.basic

namespace challenges

-- basic definitions
def upper_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, s ≤ b }
def lower_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, b ≤ s }
def is_least (S : set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

/-- A set has at most one least upper bound -/
theorem challenge2 (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  unfold is_lub at ha,
  unfold is_lub at hb,
  unfold is_least at ha,
  unfold is_least at hb,
  unfold lower_bounds at ha,
  unfold lower_bounds at hb,
  cases ha,
  cases hb,
  have hab : a ≤ b := by exact ha_right b hb_left,
  have hba : b ≤ a := by exact hb_right a ha_left,
  exact le_antisymm hab hba,
end

end challenges