import geometry.manifold.real_instances

def unit_sphere (n : ℕ) [has_zero (fin n)] := { x : euclidean_space n // finset.univ.sum (λ i, (x i) ^ 2) = 1}

instance has_coe_to_euclidean_space (n : ℕ) [has_zero (fin n)] : has_coe (unit_sphere n) (euclidean_space n) := sorry

def unit_sphere_minus_north_pole (n : ℕ) [has_zero (fin n)] := { x : unit_sphere n | ((x : (euclidean_space n)) 0) ≠ 1 }
def unit_sphere_minus_south_pole (n : ℕ) [has_zero (fin n)] := { x : unit_sphere n | ((x : (euclidean_space n)) 0) ≠ -1 }

def stereographic_projection_north (n : ℕ) [has_zero (fin n)] : (unit_sphere_minus_north_pole n) → (euclidean_space (n - 1)) := sorry
-- image_i = src_i / (1 - src_0)

def stereographic_projection_south (n : ℕ) [has_zero (fin n)] : (unit_sphere_minus_north_pole n) → (euclidean_space (n - 1)) := sorry
-- image_i = src_i / (src_0 - 1)

def unit_sphere_manifold_core (n : ℕ) [has_zero (fin n)] : manifold_core (euclidean_space (n - 1)) (unit_sphere n) := sorry

