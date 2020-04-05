import tactic

open function

theorem challenge4 (X Y Z : Type) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
  intro gfs,
  unfold surjective at gfs,
  intro z,
  --match (gfs z) with ⟨foo, bar⟩ :=
  have h : ∃ (a : X), (g ∘ f) a = z := by exact gfs z,
  cases h,
  use f h_w,
  exact h_h,

end
