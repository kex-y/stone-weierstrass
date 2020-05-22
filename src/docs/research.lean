/- 
Law of Large Numbers, the Central Limit Theorem and the Large 
Deviation Theory

Suppose we have a sequence of n random variables Xᵢ,
and we have Sₙ = ∑ Xᵢ. Then, if Xᵢ are i.i.d. then Sₙ is called 
a random walk. Furthermore, if P(Xᵢ = ± 1) = 1 / 2, then Sₙ is 
called a simply symmetric random walk.

# The Law of Large Numbers 

Let Xᵢ be uncorrelated i.i.d. random variables with E(Xᵢ) = μ,
then ∀ ε > 0, 

P(ω : |1 / n Sₙ(ω) - μ | > ε) ⟶ 0 as n ⟶ ∞.

↑ This means 1 / n Sₙ converges to μ in probability.

---
Example :

Let Xᵢ be real i.i.d random variables, then for any t ∈ ℝ, 
for Yᵢ(ω) := 1 if Xᵢ(ω) ≤ t else 0, we have P(Yᵢ = 1) = P(Xᵢ ≤ t)
and 

1 / n ∑ Yᵢ ⟶ P(Xᵢ ≤ t)
---

## Markov's Inequality

Suppose that X is a random variable with a first moment, 
then Markov's inequality states 

P(|X| > a) ≤ 1 / a E(|X|)

*proof* (LLN) Assume Var(Xᵢ) ≤ C < ∞. Wlog. we can assume μ = 0,
then,
P(|1 / n Sₙ| ≥ ε) ≤ 1 / (nε)² E(|Sₙ|²) by Markov's inequality
..                ≤ 1 / (nε)² ∑ Var(Xᵢ) as Var(Xᵢ) = E((Xᵢ - μ)²) = E(Xᵢ²) and we use independence to bring out the sum
..                ≤ 1 / (ε²n) C ⟶ 0

## Bernoilli's Law of Large Numbers

Let Xᵢ ~ Bern(p) for some p ∈ (0, 1). Then for all ε > 0,
P(ω : | 1 / n Sₙ(ω) - p | > ε) ⟶ 0 and we can find an upper bound 
P(ω : | 1 / n Sₙ(ω) - p | > ε) ≤ 1 / (ε²n) + 1 / (εn) + 1 / (εn)²

Now by consider that the sum of Bernoullis is a Binomial 
random variable, P(Sₙ = k)= (n k) pᵏ(1 - p)ⁿ⁻ᵏ, so with this 
we can find a bound for n choose k.

## Monte-Carlo Method

Let f : [0, 1] → ℝ be a continuous function, the question is 
what is ∫₀¹ f if this integral doesn't have a closed form.

Let Xₙ be i.i.d. uniformly distributed on [0, 1], then 
E(f(Xₙ)) = ∫₀¹ f

Then by the LLN, we can approximate the value of this integral with 
1 / n ∑ f(Xₖ) ⟶ ∫₀¹ f

# Central Limit Theorem

Definition. A sequence of random variables Yₙ is said to converge 
weakly (or in distribution) to a limit Y,
P(Yₙ ≤ a) ⟶ P(Y ≤ a),
for all a at which F is continuous where F is the cdf of Y.

The central limit theorem states that if Xᵢ is a sequence 
of random variables with E(Xᵢ) = μ, Var(Xᵢ) = σ², then 
1 / (σ √n) (Sₙ - n μ) ⟶ N (0, 1).

## Invariance Principle -- Look up later
-/
