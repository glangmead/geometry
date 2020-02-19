import geometry.manifold.real_instances
import tactic.hint

noncomputable theory

variable (n : ℕ)

def fin_embedding (n) : has_coe (fin n) (fin (n + 1)) := {
  coe := by exact fin.succ
}

def fin_upgrade (n) (i : fin (n + 1)) (lt : i.val < n) : (fin n) := {
  val := i.val,
  is_lt := lt
}


-- Unit sphere of dimension n, inside euclidean space of dimension n + 1
def unit_sphere (n) := { x : euclidean_space (n + 1) // finset.univ.sum (λ i, (x i) ^ 2) = 1}
instance sphere_top_space (n) : topological_space (unit_sphere n) := subtype.topological_space
instance sphere_has_coe_to_euclidean_space (n) : has_coe (unit_sphere n) (euclidean_space (n + 1)) := coe_subtype

-- The unit sphere minus its north pole will be a coordinate chart via stereographic projection
-- def unit_sphere_minus_north_pole (n) := { x : unit_sphere n // ((x : (euclidean_space (n + 1))) n) ≤ 1 }
def unit_sphere_minus_north_pole (n) : set (unit_sphere n) :=
  {x | (x : (euclidean_space (n + 1))) n < 1}
-- instance sphere_minus_np_top_space (n) : topological_space (unit_sphere_minus_north_pole n) := subtype.topological_space
-- instance sphere_minus_np_has_coe_to_sphere (n) : has_coe (unit_sphere_minus_north_pole n) (unit_sphere n) := coe_subtype
-- instance sphere_minus_np_has_coe_to_euclidean_space (n) : has_coe (unit_sphere_minus_north_pole n) (euclidean_space (n + 1)) := sorry

-- def stereographic_projection_north (n) : (unit_sphere_minus_north_pole (n + 1)) → (euclidean_space (n + 1)) := 
--   λ sphere i, ((sphere : euclidean_space (n + 2)) i) * (1 - ((sphere : euclidean_space (n + 2)) (n + 1)))⁻¹

/-- *The* unit sphere minus its north pole will be a coordinate chart via stereographic projection
-/

def stereographic_projection_inv_north (n) : (euclidean_space n) → (unit_sphere n) :=
λx, ⟨λ(i : fin (n + 1)), (if lt : i.val < n 
    then (2 * (x (fin_upgrade n i lt)) / (finset.univ.sum (λ j, (x j) ^ 2) + 1))
    else (((finset.univ.sum (λj, (x j)^2) - 1) / (finset.univ.sum (λ j, (x j)^2) + 1)))), 
begin
  sorry,  
end
⟩
-- ring
-- norm_num
-- simp at *
-- dsimp at *

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
    simp at *,
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

