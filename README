This repository contains formal proofs for some results for Lyapunov/auxiliary function methods. They use Lean4 with mathlib4.

Currently there are two main results:

# Classical Lyapunov function
Lyapunov.lean contains the theorem currently called "Lyapunov", which a very simple Lyapunov theorem for stability. It states that if
$$
f\cdot \nabla V(x) \leq 0
$$
and
$$
V(x) \geq \left|x\right|^2
$$
for all $x\in\mathbb{R}^n$, for continuous $f:\mathbb{R}^n\to\mathbb{R}^n$ and continuously differentiable $V:\mathbb{R}^n\to\mathbb{R}$, then solutions to
$$
\frac{dx}{dt} = f(x)
$$
which exist for all time are bounded.

# Bounds for time averages
We define the time average of a continuous observable $\Phi:\mathbb{R}^n\to\mathbb{R}$ as
$$
\bar\Phi(x_0) = \limsup_{T\to\infty} T^{-1}\int_0^T \Phi(x(t)) dt,
$$
where $x(t)$ is a solution to
$$
\frac{dx}{dt} = f(x), \qquad x(0)=x_0,
$$
which remains in the compact set $\mathcal{B}\subset\mathbb{R}^n$.

We prove that
$$
\bar\Phi(x_0) \leq \sup_{x\in\mathcal{B}} \left(\Phi(x) + f\cdot\nabla V(x) \right) 
$$
for any continuously differentiable $V:\mathbb{R}^n\to\mathbb{R}$.