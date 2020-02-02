-- let X, Y, Z be sets.
variables {X Y Z : Type} 

-- a function f : X → Y is *injective* if f(a) = f(b) → a = b for all a,b in X.
def injective (f : X → Y)  : Prop :=
∀ a b : X, f(a) = f(b) → a = b

-- challenge: the composite of two injective functions is injective
theorem challenge1
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  intros a b,
  intro hfg,
  have fab : (f a) = (f b) := (hg (f a) (f b)) hfg,
  have ab : a = b := (hf a b) fab,
  exact ab,
end
