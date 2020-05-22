/-
Basic concepts:

- Random variables :
X is a random variable of the probability space (Ω, ℬ, P)
iff. X : Ω → ℝ and ∀ x ∈ ℝ, {ω ∈ Ω | X(ω) ≤ x} ∈ ℬ 

Given two random variables X Y, they are said to have the 
same probability distibutions if P(X ∈ A) = P(Y ∈ A) ∀ A a 
borel measurable set.

- Independence : 
A family of random variables Xᵢ is said to be independent iff.
P(⋂ i, Xᵢ ≤ xᵢ) = Πi, P(Xᵢ ≤ xᵢ)

If X = (Xᵢ) is a random variable in ℝⁿ with density function 
p : ℝⁿ → ℝ. Then, for all g : ℝⁿ → ℝ, a separately continuous 
function in each coordinates, then
E(g(X)) = ∫ ⋯ ∫ g(x₁, ⋯ , xₙ)p(x₁, ⋯ , xₙ) dxᵢ
-/