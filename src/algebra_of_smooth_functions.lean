-- import geometry.manifold.real_instances
-- import geometry.manifold.mfderiv
import data.set.basic
import ring_theory.algebra
import tactic.pi_instances
import topology.basic
import topology.instances.real

noncomputable theory

section playground

-- variables {n : ℕ}
  -- {I : model_with_corners ℝ (euclidean_space n) (euclidean_space n)} [model_with_corners.boundaryless I]
  -- (M : Type*) [topological_space M] [manifold (euclidean_space n) M] [smooth_manifold_with_corners I M]

-- instance euclidean_model : has_coe (euclidean_space n) (model_with_corners ℝ (euclidean_space n) (euclidean_space n)) := sorry
-- instance line_model : has_coe ℝ (model_with_corners ℝ ℝ ℝ) := sorry

def real_functions (α : Type*) := α → ℝ

instance fns_are_ring (α: Type*) : ring (real_functions α) := by pi_instance

def cont_real_fns (α: Type*) [tm : topological_space α] := {f : real_functions α // continuous f}

instance cont_fns_are_ring (α: Type*) [tm : topological_space α] : ring (cont_real_fns α) := {
  add := λ f g, ⟨f.val + g.val, continuous.add f.property g.property ⟩,
  add_assoc := by {intros; apply subtype.eq; apply add_assoc},
  zero := ⟨0, continuous_const⟩,
  zero_add := by {intros; apply subtype.eq; apply zero_add},
  add_zero := by {intros; apply subtype.eq; apply add_zero},
  neg := λ f, ⟨-f.val, continuous.neg f.property⟩,
  add_left_neg := by {intros; apply subtype.eq; apply add_left_neg},
  add_comm := by {intros; apply subtype.eq; apply add_comm},
  mul := λ f g, ⟨f.val * g.val, continuous.mul f.property g.property⟩,
  mul_assoc := by {intros; apply subtype.eq; apply mul_assoc},
  one := ⟨1, continuous_const⟩,
  one_mul := by {intros; apply subtype.eq; apply one_mul},
  mul_one := by {intros; apply subtype.eq; apply mul_one},
  left_distrib := by {intros; apply subtype.eq; apply left_distrib},
  right_distrib := by {intros; apply subtype.eq; apply right_distrib},
}

instance fns_are_algebra (M : Type*) : algebra ℝ (real_functions M) := {
  smul := λ r f m, r * f m,
  to_fun := λ r m, r,
  commutes' := by {intros; ext; apply mul_comm},
  smul_def' := by {intros; ext; refl}, -- smul and to_fun are compatible
  map_one'  := by {intros; ext; refl},
  map_mul'  := by {intros; ext; refl},
  map_zero' := by {intros; ext; refl},
  map_add'  := by {intros; ext; refl}
}

instance cont_fns_are_algebra (α: Type*) [tm : topological_space α] : algebra ℝ (cont_real_fns α) := {
  smul := λ r f, ⟨λ m, r * f.val m, continuous.mul continuous_const f.property⟩,
  to_fun := λ r, ⟨λ m, r, continuous_const⟩,
  commutes' := by {intros; apply subtype.eq; ext; apply mul_comm},
  smul_def' := by {intros; apply subtype.eq; ext; refl},
  map_one' := by {intros; apply subtype.eq; ext; refl},
  map_mul' := by {intros; apply subtype.eq; ext; refl},
  map_zero' := by {intros; apply subtype.eq; ext; refl},
  map_add' := by {intros; apply subtype.eq; ext; refl},
}

  -- begin
  --   intros r f,
  --   ext,
  --   show f x * r = r * f x, -- change tactic, claim my expression is defeq to goal
  --   apply mul_comm,
  -- end,

-- /-- A function `f` between measurable spaces is measurable if the preimage of every
--   measurable set is measurable. -/
-- def measurable [m₁ : measurable_space α] [m₂ : measurable_space β] (f : α → β) : Prop :=
-- m₂ ≤ m₁.map f


end playground
