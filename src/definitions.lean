import topology.bounded_continuous_function

noncomputable theory
open set classical
local attribute [instance] prop_decidable

variables {X : Type*} [metric_space X] [compact_space X]

-- We adopt the notation of bounded countinuous function from mathlib
local infixr ` →ᵇ ` : 25 := bounded_continuous_function

/- This file contains all the definitions used throughout the project.

The main defintions are the following:
- lattice operation on bounded continuous functions defined as max and min
- standard defintion of the notion of uniform convergence of functions
- closure₀ as the closure of a set of bounded continuous functions 
under lattice operations
- closure₂ as the closure of a set of bounded continuous functions 
under lattice operations and uniform convergence to the limit
- boundary_points is the set of points in ℝ², z such that there exists a function 
f in the indicated set of bounded continuous functions such that z = (f(x), f(y))
- converges_to_R2 is the standard definition of convergence in ℝ²
- closure' is the closure of a set of points in ℝ² under lattice operations 
and convergence.
-/

/- max_bounded and min_bounded are trival -/
theorem max_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (max (f x) (g x)) (max (f y) (g y)) ≤ C := sorry

theorem min_bounded {f g : X → ℝ} 
(hf :  ∃ (C : ℝ), ∀ (x y : X), dist (f x) (f y) ≤ C) 
(hg :  ∃ (C : ℝ), ∀ (x y : X), dist (g x) (g y) ≤ C) :
∃ (C : ℝ), ∀ (x y : X), dist (min (f x) (g x)) (min (f y) (g y)) ≤ C := sorry

instance : has_sup (X →ᵇ ℝ) := 
⟨λ f g, ⟨λ x, max (f x) (g x), continuous.max f.2.1 g.2.1, max_bounded f.2.2 g.2.2⟩⟩

instance : has_inf (X →ᵇ ℝ) := 
⟨λ f g, ⟨λ x, min (f x) (g x), continuous.min f.2.1 g.2.1, min_bounded f.2.2 g.2.2⟩⟩

/- We define our own uniform convergence since mathlib's version is too powerful for 
our purpose -/
def unif_converges_to {α} (F : ℕ → α → ℝ) (f : α → ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : α, abs (f x - F n x) < ε

def closure₀ (M₀ : set (X →ᵇ ℝ)) :=
  {h : X →ᵇ ℝ | ∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g}

def closure₂ (M₀ : set (X →ᵇ ℝ)) := 
  {h : X →ᵇ ℝ | (∃ f g ∈ M₀, h = f ⊔ g ∨ h = f ⊓ g) ∨ 
  ∃ (F : ℕ → X →ᵇ ℝ) (H : ∀ i, F i ∈ closure₀ M₀), unif_converges_to (λ n, F n) h}

def boundary_points (M : set (X →ᵇ ℝ)) (x y : X) := 
  {z | ∃ (f : X →ᵇ ℝ) (hf : f ∈ M), (f x, f y) = z}

def converges_to_R2 (s : ℕ → ℝ × ℝ) (x) := 
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) x < ε

-- We do not need to define inf and sup for tuples since its induced automatically!
-- try : #eval (1, 4) ⊔ (2, 3)

def closure' (S : set (ℝ × ℝ)) := 
  {z | (∃ r t ∈ S, r ⊔ t = z ∨ r ⊓ t = z) ∨ 
  ∃ (s : ℕ → ℝ × ℝ) (hs : ∀ n : ℕ, (s n) ∈ S), converges_to_R2 s z}

def has_seperate_points (M₀ : set (X →ᵇ ℝ)) :=
  ∀ x y : X, x ≠ y → ∃ (f : X →ᵇ ℝ) (hf : f ∈ M₀), f x ≠ f y

attribute [reducible] closure₀ closure₂ boundary_points closure'