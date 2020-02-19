import geometry.manifold.real_instances
import data.set.basic

noncomputable theory

@[user_attribute]
meta def my_continuity_lemmas : user_attribute :=
{ name := `my_continuity_lemmas,
  descr := "lemmas usable to prove continuity" }
attribute [my_continuity_lemmas] continuous.comp continuous.mul continuous_fst continuous_snd continuous_subtype_val continuous_const continuous.sub real.continuous.inv


lemma certain_func_is_continuous : continuous (λ x:ℝ, 4 * (x:ℝ)) := 
begin
  apply continuous.mul _ _,
  apply_instance,
  exact continuous_const,
  exact continuous_id,
end

def real_gt_one := {x: ℝ | 1 < x}
instance : has_coe real_gt_one ℝ := ⟨subtype.val⟩
instance real_gt_one_top_space : topological_space real_gt_one := by apply_instance
-- instance : can_lift ℝ real_gt_one :=
-- { coe := coe,
--   cond := λ r, 1 < r,
--   prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }
lemma continuous_coe : continuous (coe : real_gt_one → ℝ) := continuous_subtype_val

lemma certain_func_is_continuous_gtone : continuous (λ x:real_gt_one, 4 * (x:ℝ)) := 
begin
  apply continuous.mul _ _,
  apply_instance,
  exact continuous_const,
  exact continuous_subtype_val,
end

-- tactics: change, finish

lemma certain_twovar_func_continuous : continuous (λx:(ℝ × real_gt_one), x.1 * (1 - (x.2.1))⁻¹) :=
begin
  apply continuous.mul _ _,
  apply_instance,
  refine continuous.comp _ _,
  apply continuous_fst,
  apply continuous_id,
  apply real.continuous.inv,
  intros a,
  have := a.2.2,
  intro nonzero,
  change (a.snd.val : ℝ) > 1 at this,
  linarith only [this, nonzero],
  apply continuous.sub,
  apply continuous_const,
  refine continuous.comp _ _,
  apply continuous_subtype_val,
  apply continuous_snd,
end

lemma foo : continuous (λx:ℝ×ℝ, (x.1) * (1 - x.2)⁻¹) :=
continuous.mul continuous_fst (real.continuous.inv _ $ continuous.sub continuous_const continuous_snd)

lemma foo' : continuous (λx:ℝ×ℝ, x.2) := continuous_snd

lemma bar : continuous (λx:ℝ×ℝ, x.1⁻¹) := 
continuous.comp (real.continuous.inv _ continuous_id) (continuous_fst)

lemma bar' (n : ℕ) (i : fin n) : continuous (λx:(euclidean_space n), x i) := continuous_apply i

lemma barbar' (n : ℕ) (i : fin (n + 1)) : continuous (λx:(euclidean_space (n + 1)), (x i) * (1 - x n)⁻¹) := 
continuous.mul (continuous_apply _) (real.continuous.inv _ _)

#check continuous_inv

