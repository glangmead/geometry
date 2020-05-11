import data.set.basic
import data.equiv.fin
import ring_theory.algebra
import tactic.pi_instances
import topology.basic
import topology.instances.real
import geometry.manifold.real_instances
import geometry.manifold.mfderiv

noncomputable theory

section playground

-- Real-valued functions and their properties (ring, algebra)
def real_functions (α : Type*) := α → ℝ

instance fns_are_ring (α: Type*) : ring (real_functions α) := by pi_instance

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

-- continuous Real-valued functions and those same properties (ring, algebra)
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

instance cont_fns_are_algebra (α: Type*) [tm : topological_space α] : algebra ℝ (cont_real_fns α) := 
{
  smul := λ r f, ⟨λ m, r * f.val m, continuous.mul continuous_const f.property⟩,
  to_fun := λ r, ⟨λ m, r, continuous_const⟩,
  commutes' := by {intros; apply subtype.eq; ext; apply mul_comm},
  smul_def' := by {intros; apply subtype.eq; ext; refl},
  map_one' := by {intros; apply subtype.eq; ext; refl},
  map_mul' := by {intros; apply subtype.eq; ext; refl},
  map_zero' := by {intros; apply subtype.eq; ext; refl},
  map_add' := by {intros; apply subtype.eq; ext; refl},
}

-- def euc_to_r : (euclidean_space 1) → ℝ := begin
--   have x : fin 1 := begin
--     have s : punit := punit.star,
--     exact fin_one_equiv.symm s,
--   end,
--   intro f,
--   exact f x,
-- end

-- def r_to_euc : ℝ → (euclidean_space 1) := λ x n, x

def r_model : model_with_corners ℝ ℝ ℝ := {
   to_fun := id,
   inv_fun := id,
   source := set.univ,
   target := set.univ,
   map_source := by simp,
   map_target := by simp,
   left_inv := by simp,
   right_inv := by simp,
   source_eq := by simp,
   unique_diff := by { rw set.range_id, exact is_open_univ.unique_diff_on }, -- see model_with_corners_self
   continuous_to_fun := continuous_id,
   continuous_inv_fun := continuous_id,
}

section smooth

def smooth_real_fns {n : ℕ}
  (I : model_with_corners ℝ (euclidean_space n) (euclidean_space n))
  (M : Type) [tm: topological_space M] [m: manifold (euclidean_space n) M] [smc: smooth_manifold_with_corners I M] := 
  {f : real_functions M // mdifferentiable I r_model f}

instance smooth_fns_are_ring {n : ℕ}
  (I : model_with_corners ℝ (euclidean_space n) (euclidean_space n))
  (M : Type) [tm: topological_space M] [m: manifold (euclidean_space n) M] [smc: smooth_manifold_with_corners I M] 
  : ring (smooth_real_fns I M) := {
  add := begin
      refine λ f g, ⟨f.val + g.val, _⟩,
      intro x,
      have hcf : continuous_at f.val x := and.left (f.property x),
      have hcg : continuous_at g.val x := and.left (g.property x),
      have hc : continuous_at (f.val + g.val) x := continuous_at.add hcf hcg,
      refine and.intro hc _,
      exact differentiable_within_at.add (and.right (f.property x)) (and.right (g.property x)),
    end,
  mul := begin
      refine λ f g, ⟨f.val * g.val, _⟩,
      intro x,
      have hcf : continuous_at f.val x := and.left (f.property x),
      have hcg : continuous_at g.val x := and.left (g.property x),
      have hc : continuous_at (f.val * g.val) x := continuous_at.mul hcf hcg,
      refine and.intro hc _,
      exact differentiable_within_at.mul (and.right (f.property x)) (and.right (g.property x)),
    end,
  neg := begin 
    refine λ f, ⟨-f.val, _⟩,
    intro x,
    have hcf : continuous_at f.val x := and.left (f.property x),
    have hc : continuous_at (-f.val) x := continuous_at.neg hcf,
    refine and.intro hc _,
    exact differentiable_within_at.neg (and.right (f.property x)),
  end,
  zero := ⟨0, mdifferentiable_const I r_model⟩,
  one := ⟨1, mdifferentiable_const I r_model⟩,
  add_assoc := by {intros; apply subtype.eq; apply add_assoc},
  zero_add := by {intros; apply subtype.eq; apply zero_add},
  add_zero := by {intros; apply subtype.eq; apply add_zero},
  add_left_neg := by {intros; apply subtype.eq; apply add_left_neg},
  add_comm := by {intros; apply subtype.eq; apply add_comm},
  mul_assoc := by {intros; apply subtype.eq; apply mul_assoc},
  one_mul := by {intros; apply subtype.eq; apply one_mul},
  mul_one := by {intros; apply subtype.eq; apply mul_one},
  left_distrib := by {intros; apply subtype.eq; apply left_distrib},
  right_distrib := by {intros; apply subtype.eq; apply right_distrib},
}
  
instance smooth_fns_are_algebra {n : ℕ}
  (I : model_with_corners ℝ (euclidean_space n) (euclidean_space n))
  (M : Type) [tm: topological_space M] [m: manifold (euclidean_space n) M] [smc: smooth_manifold_with_corners I M] 
  : algebra ℝ (smooth_real_fns I M) := 
{
  smul := begin
    refine λ r f, ⟨λ m, r * f.val m, _⟩,
    intro x,
    have hcf : continuous_at f.val x := and.left (f.property x),
    have hc : continuous_at (λ m, r * f.val m) x := continuous_at.mul continuous_at_const hcf,
    refine and.intro hc _,
    exact differentiable_within_at.mul (differentiable_within_at_const r) (and.right (f.property x)),
  end,
  to_fun := λ r, ⟨λ m, r, mdifferentiable_const I r_model⟩,
  commutes' := by {intros; apply subtype.eq; ext; apply mul_comm},
  smul_def' := by {intros; apply subtype.eq; ext; refl},
  map_one' := by {intros; apply subtype.eq; ext; refl},
  map_mul' := by {intros; apply subtype.eq; ext; refl},
  map_zero' := by {intros; apply subtype.eq; ext; refl},
  map_add' := by {intros; apply subtype.eq; ext; refl},
}

instance r_smooth_mfd : smooth_manifold_with_corners r_model ℝ := {}
  
end smooth

end playground
