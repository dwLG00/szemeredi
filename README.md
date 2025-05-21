# Furstenberg's proof of Szemerédi's Theorem

Szemerédi's Theorem is a theorem in combinatorics that states that if one has a subset of the natural numbers whose sparseness is bounded above, then it contains an arithmetic progression of arbitrary length. Formally, if $A \subset \mathbb{N}$ is a subset with positive upper density, i.e. $\limsup_{N \to \infty} \frac{|\{1, \dots, N\} \cap A|}{N} > 0$, then for any $k \in \mathbb{N}$ there exists terms $a_1, \dots, a_k \in A$ with $a_{i+1} - a_i = c$ for all $i < k$ for $c \neq 0$.

Furstenberg's (re-)proof utilized the language of Ergodic Theory to prove Szemerédi's Theorem. I gave a [talk on part of the proof](https://dylwall.com/static/documents/Furstenberg_Szemeredi.pdf) in April of 2025.

# Roadmap

### Big-picture proof
- ~~Define Measure-preserving systems~~ implemented
- ~~Define "SZ" property~~ implemented
- **Construction of corresponding measure-preserving system**: in progress
- Correspondence theorem

### Proving every measure-preserving system is SZ
- Define weak-mixing systems
- Prove weak-mixing systems are SZ
- Define extensions (and relatively weak-mixing/compact extensions)
- Prove the structure theorem
- Prove that a relatively weak-mixing/compact extension of an SZ system is SZ
- Prove that the sup of a totally ordered subset of a family of SZ factors is in the family (and is thus SZ)
- Prove that all measure-preserving systems are SZ
