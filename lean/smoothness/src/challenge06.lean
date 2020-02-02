import data.set.basic

open set

def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

example (X : Type) (R : X → X → Prop) (hR : equivalence R) (x : X) : equivalence_class R x ≠ ∅ :=
begin
  unfold equivalence at hR,
  intro h,
  unfold equivalence_class at h,
  have inhabit : x ∈ equivalence_class R x :=
  begin
    sorry
  end,
  have nonempty : ∃ x1 : X, x1 ∈ (equivalence_class R x) := sorry,
  exact ne_empty_iff_exists_mem.mpr (nonempty),
end
