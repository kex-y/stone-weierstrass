import topology.bounded_continuous_function
import assumptions

noncomputable theory
open set classical
local attribute [instance] prop_decidable

variables {X : Type*} [metric_space X] [compact_space X]

-- We adopt the notation of bounded countinuous function from mathlib
local infixr ` →ᵇ ` : 25 := bounded_continuous_function

lemma closure₂_of_univ : 
closure₂ (@univ (X →ᵇ ℝ)) = univ :=
begin
  ext f, split; intro hf,
    { exact mem_univ f },
    { left, refine ⟨f, f, hf, hf, or.inl _⟩,
      unfold has_sup.sup, 
      ext, simpa }
end

/- The first lemma we need states that:

f ∈ closure₂ M₀ ↔ 
∀ x, y ∈ X, ∀ ε > 0, ∃ f' ∈ closure₀ M₀, such that 
|f(x) - f'(x)| < ε and |f(y) - f'(y)| < ε -/

/- The forward direction is trivial -/
lemma dense_at_points_in_closure
{M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ} (h : f ∈ closure₂ M₀) : 
∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) (H : g ∈ closure₀ M₀), 
abs (f x - g x) < ε ∧ abs (f y - g y) < ε := 
begin
  rcases h with ⟨g, h, hg, hh, h⟩; intros ε hε x y,
    { cases h with hlub hglb, 
        exact ⟨g ⊔ h, ⟨g, h, hg, hh, or.inl rfl⟩, by simpa [hlub, hε]⟩,
        exact ⟨g ⊓ h, ⟨g, h, hg, hh, or.inr rfl⟩, by simpa [hglb, hε]⟩ },
    { rcases h with ⟨F, hF, hlim⟩,
      cases hlim ε hε with N hN,
      exact ⟨F N, hF N, by simp [hN N (le_refl N)]⟩ }
end

/- To prove the reverse we fix x ∈ X and vary y. 

Since X is a compact space, We an use Heine-Borel on the entire space.

This is the lemma we'll use: compact.elim_finite_subcover -/

/- So let us fix x ∈ X and given y ∈ X write the function g satisfying 
h : abs (f(x) - g(x)) < ε ∧ abs (f(y) - g(y)) < ε, f_y (the existence 
of which is guarenteed by our hypothesis), we define 
  S(y) := {z ∈ X | f(z) - f_y(z) < ε}
It's obvious that y ∈ S(y) by h.right so 
  X ⊆ ⋃ (y : X) S(y) ⇒ X = ⋃ (y : X) S(y)

Now as X is compact, there is a finite subcover of X so there exists 
points in X, y₁, ⋯, yₙ, such that 
  X = U i ∈ {1, ⋯, n}, S(yᵢ).

So now, by letting g_x := ⊔ i, f_yᵢ, we have ∀ z ∈ X, 
  g_x(z) ≥ f_yₖ(z) > f(z) - ε
for some k ∈ {1, ⋯, n}.

Now we will define T(x) := {z ∈ X | g_x(z) < f(z) + ε}. 
As ∀ yᵢ, f_yᵢ(x) < f(x) + ε by h.left, so is g_x(x) < f(x) + ε. 
Thus, x ∈ T(x) and X ⊆ ⋃ (x : X) T(x) and again as X is compact, there 
is x₁, ⋯, xₘ, such that 
  X = U i ∈ {1, ⋯, m}, S(xᵢ).

So, by letting h := ⊓ i, g_xᵢ, we have ∀ z ∈ X, h(z) ≤ g_xₖ(z) < f(z) + ε.
Now, as g_xᵢ(z) > f(z) - ε, for all i, so is h(z) > f(z) - ε and hence 
there is a function in closure₀ M₀ thats arbitarily close to f. 
-/

/- Given x ∈ X, we create a function thats greater than f(z) - ε at all z while 
smaller than f(x) + ε. -/
lemma has_bcf_gt {M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ} 
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
∀ ε > 0, ∀ x : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), ∀ z : X, f z - ε < g z ∧ g x < f x + ε := 
begin
  intros ε hε x, choose g hg₀ hg₁ using h ε (by {norm_cast, exact hε}) x,
  let S : X → set X := λ y, {z | f z - g y z < ε}, 
  cases compact.elim_finite_subcover _inst_2.1 S 
    (is_open_aux_set₀ (by norm_cast; exact hε)) _ with I hI,
    { let p := I.sup g,
      refine ⟨p, finset_sup_mem_closure₀ hg₀, 
        λ z, ⟨_, finset_sup_lt (λ i hi, by linarith [(abs_lt.1 (hg₁ i).1).1])⟩⟩,
        suffices : ∃ i ∈ I, f z - ε < g i z,
            rcases this with ⟨i, hi₀, hi₁⟩,
            exact lt_of_lt_of_le hi₁ (le_finset_sup g i hi₀ z),
        have : z ∈ ⋃ (i : X) (H : i ∈ I), S i, exact hI (by trivial),
        cases mem_Union.1 this with i hi, cases mem_Union.1 hi with hi hz,
        rw mem_set_of_eq at hz, exact ⟨i, hi, by linarith⟩ },
    { intros y hy, exact mem_Union.2 ⟨y, (abs_lt.1 (hg₁ y).2).2⟩ }
end

/- We again use the same method obtaining a function arbitarily close to f -/
lemma has_bcf_close {M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ} 
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
∀ (ε : ℝ) (hε : 0 < ε), ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), ∀ z : X, abs (f z - g z) < ε := 
begin
  intros ε hε, choose g hg₀ hg₁ using has_bcf_gt h ε hε,
  let S : X → set X := λ x, {z | g x z < f z + ε},
  cases compact.elim_finite_subcover _inst_2.1 S (is_open_aux_set₁ hε) _ with I hI,
    { let p := I.inf g, refine ⟨p, finset_inf_mem_closure₀ hg₀, λ z, _⟩, 
      rw abs_lt, refine ⟨_, _⟩,
        { rw neg_lt_sub_iff_lt_add,
          suffices : ∃ i ∈ I, g i z < f z + ε, 
            rcases this with ⟨i, hi₀, hi₁⟩,
            refine lt_of_le_of_lt (finset_inf_le g i hi₀ z) hi₁,             
          have : z ∈ ⋃ (i : X) (H : i ∈ I), S i, refine hI (by trivial),
          cases mem_Union.1 this with i hi, cases mem_Union.1 hi with hi hz,
          refine ⟨i, hi, hz⟩ },
        { suffices : ∀ i ∈ I, f z - ε < g i z, 
            exact sub_lt.2 (lt_finset_inf this),
          intros i hi, exact (hg₁ i z).1 } },
    { intros x hx, exact mem_Union.2 ⟨x, (hg₁ x x).2⟩ }
end

/- With that we conclude that there is some sequence of functions in closure₀ M₀ 
that is uniformly convergent towards f -/
lemma in_closure₂_of_dense_at_points {M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ}
(h : ∀ ε > 0, ∀ x y : X, ∃ (g : X →ᵇ ℝ) 
(H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε) : 
f ∈ closure₂ M₀ := or.inr $
begin
  choose F hF₀ hF₁ using λ (n : ℕ), 
    has_bcf_close h (1 / (n + 1)) (nat.one_div_pos_of_nat),
  refine ⟨F, hF₀, λ ε hε, _⟩,
  cases exists_nat_gt (1 / ε) with N hN,
  refine ⟨N, λ n hn x, lt_of_lt_of_le (hF₁ n x) $ 
    one_div_le_of_one_div_le_of_pos hε $ le_trans (le_of_lt hN) _⟩,
  norm_cast, exact le_add_right hn,
end

/- Finally, we can conclude that f can be constructed from M₀ using inf, sup 
and uniform convergence iff. for all pairs of points in X, (x, y), there is 
some sequence of functions in M₀ that converges pointwise to f(x) and f(y) at 
x and y. -/
theorem in_closure₂_iff_dense_at_points {M₀ : set (X →ᵇ ℝ)} {f : X →ᵇ ℝ} : 
f ∈ closure₂ M₀ ↔ ∀ ε > 0, ∀ x y : X, 
∃ (g : X →ᵇ ℝ) (H : g ∈ closure₀ M₀), abs (f x - g x) < ε ∧ abs (f y - g y) < ε := 
⟨λ h, dense_at_points_in_closure h, λ h, in_closure₂_of_dense_at_points h⟩

/- From this, a corollaries can be deduced immediately:

- If ∀ x, y ∈ X, a, b ∈ ℝ, ∃ f ∈ M₀, f(x) = a, f(y) = b, then 
  closure₂ M₀ = M (= @univ X →ᵇ ℝ)
where M is the set of all bounded continuous functions from X to ℝ. -/

/- Due to reasons commented from above, we will now consider pairs of points in 
X rather than functions. 

We define M₀' : X → X → ℝ × ℝ : x, y ↦ {(f(x), f(y)) | f ∈ M₀};
    (α, β) ⊔ (γ, δ) := (max α γ, max β δ);
and (α, β) ⊓ (γ, δ) := (min α γ, min β δ).

We also define a closure with respect to this inf, sup and limits of 
sequences in ℝ². -/

lemma le_closure' {S : set (ℝ × ℝ)} : S ⊆ closure' S :=
begin
  intros x hx, left, refine ⟨x, x, hx, hx, or.inl _⟩, 
  unfold has_sup.sup, 
  unfold semilattice_sup.sup,
  unfold lattice.sup,
  simp
end

lemma zero_mem_of_subalgebra {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
(0 : X →ᵇ ℝ) ∈ M₀'.carrier := M₀'.2.1.1.1

lemma one_mem_of_subalgebra {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
(1 : X →ᵇ ℝ) ∈ M₀'.carrier := M₀'.2.2.1

lemma neg_mem_of_subalgebra {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
∀ f ∈ M₀'.carrier, -f ∈ M₀'.carrier := M₀'.2.1.2

lemma add_mem_of_subalgebra {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
∀ f g ∈ M₀'.carrier, f + g ∈ M₀'.carrier := M₀'.2.1.1.2

lemma mul_mem_of_subalgebra {M₀' : subalgebra ℝ (X →ᵇ ℝ)} :
∀ f g ∈ M₀'.carrier, f * g ∈ M₀'.carrier := M₀'.2.2.2

lemma zero_mem_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :
(0 : ℝ × ℝ) ∈ boundary_points (closure₂ M₀'.carrier) x y :=
begin
  refine ⟨(0 : X →ᵇ ℝ), _, _⟩, 
  apply closure_le_seq₁, rw hc, 
  exact zero_mem_of_subalgebra,
  refl
end

lemma one_mem_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :
(1 : ℝ × ℝ) ∈ boundary_points (closure₂ M₀'.carrier) x y := 
begin
  refine ⟨(1 : X →ᵇ ℝ), _, _⟩, 
  apply closure_le_seq₁, rw hc, 
  exact one_mem_of_subalgebra,
  refl
end

/- neg_mem is a bit trickier since we need to show that closure₂ 
is closed under neg (note that we are not assuming closure₂ M₀ is 
a subalgebra). To prove this we construct an uniformly convergent sequence 
of functions in M₀ that converges to -f. -/
lemma neg_mem_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :
∀ β ∈ boundary_points (closure₂ M₀'.carrier) x y,
-β ∈ boundary_points (closure₂ M₀'.carrier) x y :=
begin
  intros β hβ, rcases hβ with ⟨f, hf₀, hf₁⟩,
  refine ⟨-f, _, _⟩,
  cases hf₀,
    { rcases hf₀ with ⟨g, h, hg, hh, hgh⟩,
      cases hgh; left,
      refine ⟨-g, -h, neg_mem_of_subalgebra g hg, neg_mem_of_subalgebra h hh, _⟩,
      right, exact neg_inf_eq_sup.1 hgh,
      refine ⟨-g, -h, neg_mem_of_subalgebra g hg, neg_mem_of_subalgebra h hh, _⟩,
      left, exact neg_sup_eq_inf.1 hgh },
    { rcases hf₀ with ⟨F, hF₀, hF₁⟩,
      right, 
      refine ⟨λ n, -F n, λ i, _, _⟩,
      rw hc at *, exact neg_mem_of_subalgebra (F i) (hF₀ i),
      exact neg_unif_converges_to hF₁ },
    rw ←hf₁, refl
end

/- It is a similar story for add_mem and mul_mem. These requires 
- if λ n, F n ⟶ f and λ n, G n ⟶ g, then λ n, F n + G n ⟶ f + g
- if λ n, F n ⟶ f and λ n, G n ⟶ g, then λ n, F n * G n ⟶ f * g
respectively (both of which are standar results so).
-/
lemma add_mem_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :
∀ β γ ∈ boundary_points (closure₂ M₀'.carrier) x y,
β + γ ∈ boundary_points (closure₂ M₀'.carrier) x y := sorry

lemma mul_mem_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :
∀ β γ ∈ boundary_points (closure₂ M₀'.carrier) x y,
β * γ ∈ boundary_points (closure₂ M₀'.carrier) x y := sorry

/- The boundary points of a closed subalgebra of (X →ᵇ ℝ) over ℝ
form a subring. -/
lemma is_subring_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)}
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) : 
is_subring (boundary_points (closure₂ M₀'.carrier) x y) :=
{ zero_mem := zero_mem_of_boundary_points hc,
  add_mem := add_mem_of_boundary_points hc,
  neg_mem := neg_mem_of_boundary_points hc,
  one_mem := one_mem_of_boundary_points hc,
  mul_mem := mul_mem_of_boundary_points hc }

lemma boundary_points_range_le {M₀' : subalgebra ℝ (X →ᵇ ℝ)}
{x y} (hc : closure₀ M₀'.carrier = M₀'.carrier) :  
range (algebra_map ℝ (ℝ × ℝ)) ≤ boundary_points (closure₂ M₀'.carrier) x y :=
begin
  intros z hz, cases mem_range.1 hz with r hr,
  refine ⟨r • 1, _, _⟩,
  apply closure_le_seq₁, rw hc,
  exact subalgebra_closed_under_smul' r one_mem_of_subalgebra,
  suffices : (r, r) = z,
    simpa [show ∀ x, (1 : X →ᵇ ℝ) x = 1, by intro z; refl],
  rw ←hr, refl
end

/- With that, we can construct a subalgebra of ℝ² with underlying 
set being boundary_points (closure₂ M₀'.carrier) x y-/
def subalgebra_of_boundary_points {M₀' : subalgebra ℝ (X →ᵇ ℝ)}
(x y) (hc : closure₀ M₀'.carrier = M₀'.carrier) : 
  subalgebra ℝ (ℝ × ℝ) :=
{ carrier := boundary_points (closure₂ M₀'.carrier) x y,
  subring := is_subring_boundary_points hc,
  range_le' := boundary_points_range_le hc}

lemma in_closure'_of_in_closoure₂ {M₀' : subalgebra ℝ (X →ᵇ ℝ)} {f : X →ᵇ ℝ} 
(h : f ∈ closure₂ M₀'.carrier) (hc : closure₀ M₀'.carrier = M₀'.carrier) : 
∀ x y : X, x ≠ y → (f x, f y) ∈ closure' (boundary_points M₀'.carrier x y) :=
begin
  intros x y hxy, right,
  rw in_closure₂_iff_dense_at_points at h,
  choose F hF₀ hF₁ using λ (n : ℕ), 
    h (1 / (n + 1)) (nat.one_div_pos_of_nat) x y,
  refine ⟨λ n, (F n x, F n y), λ n, ⟨F n, hc ▸ hF₀ n, rfl⟩, λ ε hε, _⟩, 
  cases exists_nat_gt (1 / ε) with N hN,
  refine ⟨N, λ n hn, _⟩,
  suffices : abs (F n x - f x) < ε ∧ abs (F n y - f y) < ε,
    unfold dist, simp [this],
  split; rw abs_sub;
    try { refine lt_of_lt_of_le (hF₁ n).1 _ <|> refine lt_of_lt_of_le (hF₁ n).2 _ };
    refine one_div_le_of_one_div_le_of_pos hε (le_trans (le_of_lt hN) _);
    norm_cast; exact le_add_right hn
end

lemma bcf_pair_sup_eq_bcf_sup_pair {u v : X →ᵇ ℝ} {x y} : 
(u x, u y) ⊔ (v x, v y) = ((u ⊔ v) x, (u ⊔ v) y) := rfl

lemma bcf_pair_inf_eq_bcf_inf_pair {u v : X →ᵇ ℝ} {x y} : 
(u x, u y) ⊓ (v x, v y) = ((u ⊓ v) x, (u ⊓ v) y) := rfl

lemma one_mapsto_one {x} : (1 : X →ᵇ ℝ) x = 1 := rfl

lemma in_closure₂_of_in_closure' {M₀' : subalgebra ℝ (X →ᵇ ℝ)} {f : X →ᵇ ℝ} 
(hc : closure₀ M₀'.carrier = M₀'.carrier) 
(h : ∀ x y : X, x ≠ y → (f x, f y) ∈ closure' (boundary_points M₀'.carrier x y)) : 
f ∈ closure₂ M₀'.carrier :=
begin
  rw in_closure₂_iff_dense_at_points,
  intros ε hε x y,
  cases em (x = y) with hxy hxy,
  have : (f x, f x) ∈ closure' (boundary_points M₀'.carrier x y),
    refine le_closure' ⟨(f x) • 1, _⟩,
    refine ⟨subalgebra_closed_under_smul' (f x) one_mem_of_subalgebra, _⟩,
    rw ←hxy, simp [one_mapsto_one],
  cases this with h' h',
    { rcases h' with ⟨r, t, ⟨u, hu₀, hu₁⟩, ⟨v, hv₀, hv₁⟩, hrt⟩,
      cases hrt, rw hc,
        { refine ⟨u ⊔ v, (hc ▸ closure₀_closed_with_sup) hu₀ hv₀, _⟩,
          rw [←hu₁, ←hv₁, bcf_pair_sup_eq_bcf_sup_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2, hxy], simpa },
        { refine ⟨u ⊓ v, closure₀_closed_with_inf _ _, _⟩;
          try { rw hc, assumption }, 
          rw [←hu₁, ←hv₁, bcf_pair_inf_eq_bcf_inf_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2, hxy], simpa } },
    { rcases h' with ⟨s, hs₀, hs₁⟩,
      cases hs₁ ε hε with N hN, 
      rcases hs₀ N with ⟨g, hg₀, hg₁⟩,
      refine ⟨g, _, _⟩, rw hc, assumption,
      have := hN N (le_refl N),
      rw ←hg₁ at this, unfold dist at this, simp at this,
      split; rw [abs_sub]; simp only [this],
      convert this.2, rwa hxy },
  cases h x y hxy with h' h',
    { rcases h' with ⟨r, t, ⟨u, hu₀, hu₁⟩, ⟨v, hv₀, hv₁⟩, hrt⟩,
      cases hrt, rw hc,
        { refine ⟨u ⊔ v, (hc ▸ closure₀_closed_with_sup) hu₀ hv₀, _⟩,
          rw [←hu₁, ←hv₁, bcf_pair_sup_eq_bcf_sup_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2], simpa },
        { refine ⟨u ⊓ v, closure₀_closed_with_inf _ _, _⟩;
          try { rw hc, assumption }, 
          rw [←hu₁, ←hv₁, bcf_pair_inf_eq_bcf_inf_pair] at hrt,
          rw [(prod.mk.inj hrt).1, (prod.mk.inj hrt).2], simpa } },
    { rcases h' with ⟨s, hs₀, hs₁⟩,
      cases hs₁ ε hε with N hN, 
      rcases hs₀ N with ⟨g, hg₀, hg₁⟩,
      refine ⟨g, _, _⟩, rw hc, assumption,
      have := hN N (le_refl N),
      rw ←hg₁ at this, unfold dist at this, simp at this,
      split; rw abs_sub; simp only [this] }
end

lemma in_closure₂_iff_in_closure' {M₀' : subalgebra ℝ (X →ᵇ ℝ)} {f : X →ᵇ ℝ} 
(hc : closure₀ M₀'.carrier = M₀'.carrier) : 
f ∈ closure₂ M₀'.carrier ↔ 
∀ x y : X, x ≠ y → (f x, f y) ∈ closure' (boundary_points M₀'.carrier x y) :=
⟨λ h, in_closure'_of_in_closoure₂ h hc, λ h, in_closure₂_of_in_closure' hc h⟩

/- With this, we can formulate the relation between M₀ and M₀'(x, y) formally, i.e.
if M₀, M₁ ⊆ M, 
  hM : M₀ = closure₂ M₀ and M₁ = closure₂ M₁
  hb : ∀ x, y ∈ X, M₀*(x, y) = M₁*(x, y)
then M₀ = M₁. -/
lemma boundary_points_eq_of_eq (M₀' M₁' : subalgebra ℝ (X →ᵇ ℝ)) 
(h : M₀'.carrier = M₁'.carrier) : 
∀ x y : X, x ≠ y → boundary_points M₀'.carrier x y = boundary_points M₁'.carrier x y := 
λ _ _ _, by rw h

lemma closure₀_eq_of_closure₂_eq {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
(h : closure₂ M₀'.carrier = M₀'.carrier) :
closure₀ M₀'.carrier = M₀'.carrier := sorry

lemma eq_of_boundary_points_eq (M₀' M₁' : subalgebra ℝ (X →ᵇ ℝ))
(h : ∀ x y : X, x ≠ y → boundary_points M₀'.carrier x y = boundary_points M₁'.carrier x y)
(hM₀ : M₀'.carrier = closure₂ M₀'.carrier) 
(hM₁ : M₁'.carrier = closure₂ M₁'.carrier) : M₀'.carrier = M₁'.carrier := 
begin
  ext f, split; intro hf;
  { try {rw hM₀ <|> rw hM₁}, try {rw hM₀ at hf <|> rw hM₁ at hf},
    try { rw in_closure₂_iff_in_closure' (closure₀_eq_of_closure₂_eq hM₁.symm), 
      rw in_closure₂_iff_in_closure' (closure₀_eq_of_closure₂_eq hM₀.symm) at hf },
    try { rw in_closure₂_iff_in_closure' (closure₀_eq_of_closure₂_eq hM₁.symm) at hf, 
      rw in_closure₂_iff_in_closure' (closure₀_eq_of_closure₂_eq hM₀.symm) },
    intros x y hxy, try {rw ←h x y <|> rw h x y},
    exact hf x y hxy, assumption }
end

theorem eq_iff_boundary_points_eq (M₀' M₁' : subalgebra ℝ (X →ᵇ ℝ))
(hM₀ : M₀'.carrier = closure₂ M₀'.carrier) 
(hM₁ : M₁'.carrier = closure₂ M₁'.carrier) : 
M₀'.carrier = M₁'.carrier ↔ 
∀ x y : X, x ≠ y → boundary_points M₀'.carrier x y = boundary_points M₁'.carrier x y := 
⟨λ h, boundary_points_eq_of_eq _ _ h, λ h, eq_of_boundary_points_eq _ _ h hM₀ hM₁⟩

/- Now that we've reformulated the problem such that it considers points in ℝ² 
rather than all bounded continuous functions, the question now becomes, 
under what condition, is the boundary points of closure₂ M₀ equal to ℝ². -/
lemma closure₂_subalgebra_carrier {M₀' : subalgebra ℝ (X →ᵇ ℝ)} : 
(closure₂_subalgebra M₀').carrier = closure₂ M₀'.carrier := rfl

lemma univ_subalgebra_carrier : 
(univ_subalgebra.carrier : set (X →ᵇ ℝ)) = univ := rfl

theorem func_dense_iff_boundary_points_dense (M₀' : subalgebra ℝ (X →ᵇ ℝ)) :
closure₂ M₀'.carrier = univ ↔ 
∀ x y, x ≠ y → boundary_points (closure₂ M₀'.carrier) x y = univ := 
begin
  have := eq_iff_boundary_points_eq (closure₂_subalgebra M₀') univ_subalgebra
    (closure₂_of_closure₂ M₀'.carrier).symm (closure₂_of_univ).symm,
  rw [closure₂_subalgebra_carrier, univ_subalgebra_carrier] at this,
  split, 
    { intros h x y hxy,
      rw this at h, rw (h x y),
      exact boundary_points_of_univ x y,
      assumption },
    { intro h, rw this, intros x y hxy, rw h x y, 
      exact (boundary_points_of_univ x y).symm,
      assumption }
end

/- Now that we have proved that given a closed subalgebra of X →ᵇ ℝ over 
ℝ - M₀', boundary_points (closure₂ M₀'.carrier) x y form a subalgebra of 
ℝ², we can use this fact in combination of our theorem from ralgebra.lean 
concluding boundary_points (closure₂ M₀'.carrier) x y must be 
  {(0, 0)} ∨ {p | ∃ x : ℝ, p = (x, 0)} ∨
  {p | ∃ y : ℝ, p = (0, y)} ∨ {p | ∃ z : ℝ, p = (z, z)} ∨ ℝ²
Now due to `one_mem_of_boundary_points`, we eliminate our possiblities to 
{p | ∃ z : ℝ, p = (z, z)} ∨ ℝ², the first of which is not possible if 
we have seperate points. -/

/- (Weierstrass-Stone's Theorem)
Let M₀ be a subalgebra of (X →ᵇ ℝ) that's closed (M₂ = closure₀ M₀) 
and seperate points. Then closure₂ M₀ = univ. -/
theorem weierstrass_stone {M₀' : subalgebra ℝ (X →ᵇ ℝ)} 
(hc   : closure₀ M₀'.carrier = M₀'.carrier) 
(hsep : has_seperate_points M₀'.carrier) 
(hns  : ∃ β γ : X, β ≠ γ):
closure₂ M₀'.carrier = univ :=
begin
  rw func_dense_iff_boundary_points_dense,
  intros x y hxy,
  cases subalgebra_of_R2 (subalgebra_of_boundary_points x y hc),
    { suffices : ((1, 1) : ℝ × ℝ) ∈ (subalgebra_of_boundary_points x y hc).carrier,
        exfalso, rw [h, mem_singleton_iff] at this, 
        replace this := congr_arg prod.fst this, simp at this, assumption,
      exact one_mem_of_boundary_points hc },
  cases h,
    { suffices : ((1, 1) : ℝ × ℝ) ∈ (subalgebra_of_boundary_points x y hc).carrier,
        exfalso, rw h at this, cases this with r hr,
        simp at hr, assumption,
      exact one_mem_of_boundary_points hc },
  cases h,
    { suffices : ((1, 1) : ℝ × ℝ) ∈ (subalgebra_of_boundary_points x y hc).carrier,
        exfalso, rw h at this, cases this with r hr,
        simp at hr, assumption,
      exact one_mem_of_boundary_points hc },
  cases h,
    { rcases hsep x y hxy with ⟨f, hf₀, hf₁⟩,
      suffices : ((f x, f y) : ℝ × ℝ) ∈ (subalgebra_of_boundary_points x y hc).carrier,
        exfalso, rw h at this, cases this with r hr,
        apply hf₁, replace this : f x = r := congr_arg prod.fst hr,
        rw this, simp [show f y = r, by exact congr_arg prod.snd hr],
      refine ⟨f, _, rfl⟩, apply closure_le_seq₁, rwa hc },
    { exact h }
end