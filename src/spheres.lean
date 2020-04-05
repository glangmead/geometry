import geometry.manifold.real_instances

noncomputable theory

variable (n : ℕ)

theorem finset.image_val_univ_eq_range (n : ℕ) : finset.image (λ (x : fin n), x.val) finset.univ = finset.range n :=
begin
  ext j, -- sigh
  rw [finset.mem_range, finset.mem_image],
  split,
    rintro ⟨⟨j,hj⟩, _, rfl⟩,
    exact hj,
  intro hj,
  use ⟨j, hj⟩,
  split, apply finset.mem_univ, refl,
end

theorem finset.sum_univ_fin_eq_sum_range (n : ℕ) (f : fin n → ℝ) :
  finset.sum finset.univ f = (finset.range n).sum (λ i, if hi : i < n then f ⟨i, hi⟩ else 0) :=
begin
  set F : ℕ → ℝ := λ i, if hi : i < n then f ⟨i, hi⟩ else 0 with hF,
  have H : f = λ (i : fin n), F (i.val),
  { ext i,
    rw hF,
    show f i = dite (i.val < n) (λ (hi : i.val < n), f ⟨i.val, hi⟩) (λ (hi : ¬i.val < n), 0),
    rw dif_pos i.is_lt,
    cases i, refl,
  },
  rw H,
  rw ←finset.sum_image,
  { congr',
    apply finset.image_val_univ_eq_range,
  },
  intros _ _ _ _,
  exact fin.eq_of_veq,
end

theorem finset.sum_div {α : Type*} {s : finset α} (f : α → ℝ) (d : ℝ) : finset.sum s (λ a, f a / d) = finset.sum s f / d :=
begin
  by_cases hd : d = 0,
    rw [hd, div_zero],
    convert finset.sum_const_zero,
    ext _,
    rw div_zero,
  rw [div_eq_mul_inv, finset.sum_mul],
  congr',
end

def unit_sphere (n) := { x : euclidean_space (n + 1) // finset.univ.sum (λ i, (x i) ^ 2) = 1}

open finset

def stereographic_projection_inv_north (n) : (euclidean_space n) → (unit_sphere n) :=
λx, ⟨λ(i : fin (n + 1)), (if lt : i.val < n
    then (2 * (x (fin.cast_lt i lt)) / (finset.univ.sum (λ j, (x j) ^ 2) + 1))
    else (((finset.univ.sum (λj, (x j)^2) - 1) / (finset.univ.sum (λ j, (x j)^2) + 1)))),
begin
  rw [sum_univ_fin_eq_sum_range, sum_range_succ, dif_pos (nat.lt_succ_self n), dif_neg (lt_irrefl n)],
  suffices : ((sum univ (λ (j : fin n), x j ^ 2) - 1) / (sum univ (λ (j : fin n), x j ^ 2) + 1)) ^ 2 +
    (sum (range n) (λ (i : ℕ), if hi : i < n then (2 * x ⟨i, hi⟩)^2  else 0) / (sum univ (λ (j : fin n), x j ^ 2) + 1) ^ 2)
    = 1,
  { convert this using 2, clear this,
    rw ←sum_div,
    apply finset.sum_congr, refl,
    intros i hi,
    rw finset.mem_range at hi,
    rw dif_pos (lt_trans hi (nat.lt_succ_self n)),
    rw dif_pos hi,
    rw dif_pos hi,
    rw pow_div,
    congr',
  },
  rw pow_div,
  rw ←add_div,
  rw div_eq_one_iff_eq,
  swap,
  { apply ne_of_gt,
    apply pow_pos,
    apply lt_of_lt_of_le zero_lt_one,
    apply le_add_of_nonneg_left',
    apply sum_nonneg,
    intros,
    rw pow_two,
    apply mul_self_nonneg,
  },
  rw [sub_eq_add_neg, pow_two, pow_two, add_mul_self_eq, add_mul_self_eq],
  rw [neg_mul_neg, mul_neg_one, mul_one, mul_one],
  rw add_comm,
  repeat {rw ←add_assoc},
  congr' 1,
  rw [add_assoc, add_left_comm],
  apply congr_arg,
  apply add_neg_eq_of_eq_add,
  rw [mul_sum, ←sum_add_distrib],
  rw sum_univ_fin_eq_sum_range,
  apply sum_congr, refl,
  intros i hi,
  rw mem_range at hi,
  rw [dif_pos hi, dif_pos hi],
  ring,
end
⟩

instance sphere_top_space (n) : topological_space (unit_sphere n) := subtype.topological_space
instance sphere_has_coe_to_euclidean_space (n) : has_coe (unit_sphere n) (euclidean_space (n + 1)) := coe_subtype

def fin_embedding (n) : has_coe (fin n) (fin (n + 1)) := {
  coe := by exact fin.succ
}

meta def my_tac : tactic unit :=
`[ repeat { {left, assumption} <|> right <|> assumption } ]



-- The unit sphere minus its north pole will be a coordinate chart via stereographic projection
-- def unit_sphere_minus_north_pole (n) := { x : unit_sphere n // ((x : (euclidean_space (n + 1))) n) ≤ 1 }
def unit_sphere_minus_north_pole (n) : set (unit_sphere n) :=
  {x | (x : (euclidean_space (n + 1))) n < 1}
-- instance sphere_minus_np_top_space (n) : topological_space (unit_sphere_minus_north_pole n) := subtype.topological_space
-- instance sphere_minus_np_has_coe_to_sphere (n) : has_coe (unit_sphere_minus_north_pole n) (unit_sphere n) := coe_subtype
-- instance sphere_minus_np_has_coe_to_euclidean_space (n) : has_coe (unit_sphere_minus_north_pole n) (euclidean_space (n + 1)) := sorry

-- def stereographic_projection_north (n) : (unit_sphere_minus_north_pole (n + 1)) → (euclidean_space (n + 1)) := 
--   λ sphere i, ((sphere : euclidean_space (n + 2)) i) * (1 - ((sphere : euclidean_space (n + 2)) (n + 1)))⁻¹



def stereographic_projection_north_local_equiv : local_equiv (unit_sphere n) (euclidean_space n) :=
{ 
  source := unit_sphere_minus_north_pole n,
  target := {x : (euclidean_space n) | true},
  to_fun := λ sphere, (λi, ((sphere : euclidean_space (n + 1)) i) * (1 - ((sphere : euclidean_space (n + 1)) (n + 1)))⁻¹),
  inv_fun := stereographic_projection_inv_north n,
  map_source := 
  begin
    simp at *,
  end, -- all these fields say that the functions `to_fun` and `inv_fun` are inverse
  map_target := begin
    
  end, -- to each other on the sets `source` and `target`
  left_inv := sorry,
  right_inv := sorry 
}

def stereographic_projection_north : local_homeomorph (unit_sphere n) (euclidean_space n) :=
{
  ..stereographic_projection_north_local_equiv n }

lemma continuous_sp_north (n:ℕ) : continuous (stereographic_projection_north n) := 
begin
  unfold stereographic_projection_north,
  apply continuous.mul _ _,
end

-- The unit sphere minus its south pole will be a coordinate chart via stereographic projection
def unit_sphere_minus_south_pole (n) := { x : unit_sphere n // (-1 ≤ (x : (euclidean_space (n + 1))) n) }
instance sphere_minus_sp_top_space (n) : topological_space (unit_sphere_minus_south_pole n) := subtype.topological_space

#check continuous_inv
#check real.continuous_inv
#check inv_eq_one_div
#check continuous.comp
#check continuous.mul

-- Stereographic projection:
-- define
-- prove continuous
-- prove inverse
-- prove inverse continuous
-- prove homeomorphism
-- prove overlaps are smooth
-- prove diffeomorphism
-- define sphere as manifold

def stereographic_projection_south (n) : (unit_sphere_minus_south_pole n) → (euclidean_space n) := 
  λ sphere i, ((sphere : euclidean_space (n + 1)) i) * (1 - ((sphere : euclidean_space (n + 1)) n))⁻¹ 

def unit_sphere_manifold_core (n) [has_zero (fin n)] : manifold_core (euclidean_space n) (unit_sphere n) := 
{ atlas := _,
  chart_at := _,
  mem_chart_source := _,
  chart_mem_atlas := _,
  open_source := _,
  continuous_to_fun := _ }

  def stereographic_projection_north_inv (n) : (euclidean_space n) → (unit_sphere_minus_north_pole n) := sorry
  --λ x, let denom := 1 + finset.univ.sum (λ i, (x i) ^ 2) in 

def stereo_homeomorph (n) : homeomorph (unit_sphere_minus_north_pole n) (euclidean_space n) := sorry
-- image_i = src_i / (1 - src_0)

