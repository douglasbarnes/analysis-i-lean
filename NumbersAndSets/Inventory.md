# Numbers and Sets declaration inventory

Source: `IA_M/numbers_and_sets.tex` (2014, A. G. Thomason; notes by Dexter Chua).

The TeX contains **148** formal environments: 62 definitions, 41 theorems, 33 propositions, 9 corollaries, 2 lemmas, and 1 explicitly presented axiom. The Lean modules use Mathlib primitives for standard definitions and proved wrappers for the course-facing named results. The source’s informal “unproven” sum-of-two-squares proposition is recorded as source content, not introduced as a Lean axiom.

| # | Kind | Source heading / opening | Lean disposition |
|---:|---|---|---|
| 1 | defi | Proof | `Foundations.lean` / Mathlib core |
| 2 | defi | Statement | `Foundations.lean` / Mathlib core |
| 3 | prop | For all natural numbers n , n^3 - n is a multiple of 3. | `Foundations.lean` / Mathlib core |
| 4 | prop | If n^2 is even, then so is n . | `Foundations.lean` / Mathlib core |
| 5 | prop | The solutions to x^2 - 5x + 6 = 0 are x = 2 and x = 3 . | `Foundations.lean` / Mathlib core |
| 6 | prop | Every positive number is 1 . | `Foundations.lean` / Mathlib core |
| 7 | defi | Set | `Foundations.lean` / Mathlib core |
| 8 | defi | Equality of sets | `Foundations.lean` / Mathlib core |
| 9 | defi | Subsets | `Foundations.lean` / Mathlib core |
| 10 | thm | (A=B) (A B B A) | `Foundations.lean` / Mathlib core |
| 11 | defi | Intersection, union, set difference, symmetric difference and power set | `Foundations.lean` / Mathlib core |
| 12 | prop | (A B) C = A (B C) (A B) C = A (B C) A (B C) = (A B) (A C) | `Foundations.lean` / Mathlib core |
| 13 | defi | Ordered pair | `Foundations.lean` / Mathlib core |
| 14 | defi | Cartesian product | `Foundations.lean` / Mathlib core |
| 15 | defi | Function/map | `Foundations.lean` / Mathlib core |
| 16 | defi | Injective function | `Foundations.lean` / Mathlib core |
| 17 | defi | Surjective function | `Foundations.lean` / Mathlib core |
| 18 | defi | Bijective function | `Foundations.lean` / Mathlib core |
| 19 | defi | Permutation | `Foundations.lean` / Mathlib core |
| 20 | defi | Composition of functions | `Foundations.lean` / Mathlib core |
| 21 | defi | Image of function | `Foundations.lean` / Mathlib core |
| 22 | defi | Pre-image of function | `Foundations.lean` / Mathlib core |
| 23 | defi | Identity map | `Foundations.lean` / Mathlib core |
| 24 | defi | Left inverse of function | `Foundations.lean` / Mathlib core |
| 25 | defi | Right inverse of function | `Foundations.lean` / Mathlib core |
| 26 | thm | The left inverse of f exists iff f is injective. | `Foundations.lean` / Mathlib core |
| 27 | thm | The right inverse of f exists iff f is surjective. | `Foundations.lean` / Mathlib core |
| 28 | defi | Inverse of function | `Foundations.lean` / Mathlib core |
| 29 | defi | Relation | `Foundations.lean` / Mathlib core |
| 30 | defi | Reflexive relation | `Foundations.lean` / Mathlib core |
| 31 | defi | Symmetric relation | `Foundations.lean` / Mathlib core |
| 32 | defi | Transitive relation | `Foundations.lean` / Mathlib core |
| 33 | defi | Equivalence relation | `Foundations.lean` / Mathlib core |
| 34 | defi | Equivalence class | `Foundations.lean` / Mathlib core |
| 35 | defi | Partition of set | `Foundations.lean` / Mathlib core |
| 36 | thm | If is an equivalence relation on A , then the equivalence classes of form a partition of A . | `Foundations.lean` / Mathlib core |
| 37 | defi | Quotient map | `Foundations.lean` / Mathlib core |
| 38 | defi | Factor of integers | `NumberTheory.lean` / Mathlib arithmetic |
| 39 | thm | Division Algorithm | `NumberTheory.lean` / Mathlib arithmetic |
| 40 | defi | Common factor of integers | `NumberTheory.lean` / Mathlib arithmetic |
| 41 | defi | Highest common factor/greatest common divisor | `NumberTheory.lean` / Mathlib arithmetic |
| 42 | prop | If c a and c b , c (ua + vb) for all u, v . | `NumberTheory.lean` / Mathlib arithmetic |
| 43 | thm | Let a,b . Then (a, b) exists. | `NumberTheory.lean` / Mathlib arithmetic |
| 44 | cor | (from the proof) Let d = (a, b) , then d is the smallest positive linear combination of a and b . | `NumberTheory.lean` / Mathlib arithmetic |
| 45 | cor | B\'{e}zout's identity | `NumberTheory.lean` / Mathlib arithmetic |
| 46 | prop | Euclid's Algorithm | `NumberTheory.lean` / Mathlib arithmetic |
| 47 | defi | Prime number | `NumberTheory.lean` / Mathlib arithmetic |
| 48 | thm | Every number can be written as a product of primes. | `NumberTheory.lean` / Mathlib arithmetic |
| 49 | thm | There are infinitely many primes. | `NumberTheory.lean` / Mathlib arithmetic |
| 50 | thm | If a bc and (a, b) = 1 , then a c . | `NumberTheory.lean` / Mathlib arithmetic |
| 51 | defi | Coprime numbers | `NumberTheory.lean` / Mathlib arithmetic |
| 52 | cor | If p is a prime and p ab , then p a or p b . (True for all p, a, b ) | `NumberTheory.lean` / Mathlib arithmetic |
| 53 | cor | If p is a prime and p n_1n_2 n_i , then p n_i for some i . | `NumberTheory.lean` / Mathlib arithmetic |
| 54 | thm | Fundamental Theorem of Arithmetic | `NumberTheory.lean` / Mathlib arithmetic |
| 55 | cor | If a = p_1^{i_1}p_2^{i_2} p_r^{i_r} and b = p_1^{j_1}p_2^{j_2} p_r^{j_r} , where p_i are distinct pr | `NumberTheory.lean` / Mathlib arithmetic |
| 56 | thm | Pigeonhole Principle | `Combinatorics.lean` / Mathlib combinatorics |
| 57 | defi | Indicator function/characteristic function | `Combinatorics.lean` / Mathlib combinatorics |
| 58 | prop | i_A = i_B A = B i_{A B} = i_A i_B i_{ } = 1 - i_A i_{A B} = 1 - i_{ } = 1 - i_{ A B} = 1 - i_{ }i_{ | `Combinatorics.lean` / Mathlib combinatorics |
| 59 | prop | A B = A + B - A B | `Combinatorics.lean` / Mathlib combinatorics |
| 60 | thm | Inclusion-Exclusion Principle | `Combinatorics.lean` / Mathlib combinatorics |
| 61 | defi | Combination $\binom{n}{r}$ | `Combinatorics.lean` / Mathlib combinatorics |
| 62 | prop | By definition, {0} + {1} + + {n} = 2^n | `Combinatorics.lean` / Mathlib combinatorics |
| 63 | thm | Binomial theorem | `Combinatorics.lean` / Mathlib combinatorics |
| 64 | prop | {r} = {n - r} . This is because choosing r things to keep is the same as choosing n - r things to th | `Combinatorics.lean` / Mathlib combinatorics |
| 65 | prop | {r} = {(n - r)!r!} . | `Combinatorics.lean` / Mathlib combinatorics |
| 66 | thm | Weak Principle of Induction | `Combinatorics.lean` / Mathlib combinatorics |
| 67 | thm | Inclusion-exclusion principle. | `Combinatorics.lean` / Mathlib combinatorics |
| 68 | thm | Strong principle of induction | `Combinatorics.lean` / Mathlib combinatorics |
| 69 | thm | The strong principle of induction is equivalent to the weak principle of induction. | `Combinatorics.lean` / Mathlib combinatorics |
| 70 | defi | Partial order | `Foundations.lean` or `NumberTheory.lean` |
| 71 | defi | Total order | `Foundations.lean` or `NumberTheory.lean` |
| 72 | defi | Well-ordered total order | `Foundations.lean` or `NumberTheory.lean` |
| 73 | thm | Well-ordering principle | `Foundations.lean` or `NumberTheory.lean` |
| 74 | thm | The well-ordering principle is equivalent to the strong principle of induction. | `Foundations.lean` or `NumberTheory.lean` |
| 75 | defi | Modulo | `Foundations.lean` or `NumberTheory.lean` |
| 76 | prop | If a b m , and d m , then a b d . | `Foundations.lean` or `NumberTheory.lean` |
| 77 | prop | If a b m and u v m , then a + u b + v m and au bv m . | `Foundations.lean` or `NumberTheory.lean` |
| 78 | thm | There are infinitely many primes that are -1 4 . | `Foundations.lean` or `NumberTheory.lean` |
| 79 | defi | Unit (modular arithmetic) | `Foundations.lean` or `NumberTheory.lean` |
| 80 | thm | u is a unit modulo m if and only if (u, m) = 1 . | `Foundations.lean` or `NumberTheory.lean` |
| 81 | cor | If (a, m) = 1 , then the congruence ax b m has a unique solution (mod m ). | `Foundations.lean` or `NumberTheory.lean` |
| 82 | prop | There is a solution to ax b m if and only if (a, m) b . If d = (a, m) b , then the solution is the u | `Foundations.lean` or `NumberTheory.lean` |
| 83 | thm | Chinese remainder theorem | `Foundations.lean` or `NumberTheory.lean` |
| 84 | prop | Given any (m,n) = 1 , c is a unit mod mn iff c is a unit both mod m and mod n . | `Foundations.lean` or `NumberTheory.lean` |
| 85 | defi | Euler's totient function | `Foundations.lean` or `NumberTheory.lean` |
| 86 | prop | (mn) = (m) (n) if (m, n) = 1 , i.e. is multiplicative. If p is a prime, (p) = p - 1 If p is a prime, | `Foundations.lean` or `NumberTheory.lean` |
| 87 | thm | Wilson's theorem | `Foundations.lean` or `NumberTheory.lean` |
| 88 | thm | Fermat's little theorem | `Foundations.lean` or `NumberTheory.lean` |
| 89 | thm | Fermat-Euler Theorem | `Foundations.lean` or `NumberTheory.lean` |
| 90 | defi | Quadratic residues | `Foundations.lean` or `NumberTheory.lean` |
| 91 | prop | If p is an odd prime, then -1 is a quadratic residue if and only if p 1 4 . | `Foundations.lean` or `NumberTheory.lean` |
| 92 | prop | (Unproven) A prime p is the sum of two squares if and only if p 1 4 . | `Foundations.lean` or `NumberTheory.lean` |
| 93 | prop | There are infinitely many primes 1 4 . | `Foundations.lean` or `NumberTheory.lean` |
| 94 | prop | Let p = 4k + 3 be a prime. Then if a is a quadratic residue, i.e. a z^2 p for some z , then z = a^{k | `Foundations.lean` or `NumberTheory.lean` |
| 95 | thm | RSA Encryption | `Foundations.lean` or `NumberTheory.lean` |
| 96 | defi | Natural numbers | Mathlib number-system/order primitives |
| 97 | defi | Integers | Mathlib number-system/order primitives |
| 98 | defi | Rationals | Mathlib number-system/order primitives |
| 99 | defi | Totally ordered field | Mathlib number-system/order primitives |
| 100 | prop | is a totally ordered-field. | Mathlib number-system/order primitives |
| 101 | prop | is densely ordered, i.e. for any p, q , if p < q , then there is some r such that p < r < q . | Mathlib number-system/order primitives |
| 102 | prop | There is no rational q with q^2 = 2 . | Mathlib number-system/order primitives |
| 103 | defi | Least upper bound/supremum and greatest lower bound/infimum | Mathlib number-system/order primitives |
| 104 | defi | Real numbers | Mathlib number-system/order primitives |
| 105 | axiom | Least upper bound axiom | Mathlib number-system/order primitives |
| 106 | cor | Every non-empty set of the real numbers bounded below has an infimum. | Mathlib number-system/order primitives |
| 107 | defi | Closed and open intervals | Mathlib number-system/order primitives |
| 108 | thm | Axiom of Archimedes | Mathlib number-system/order primitives |
| 109 | prop | { {n}: n } = 0 . | Mathlib number-system/order primitives |
| 110 | thm | is dense in , i.e. given r, s , with r < s , q with r < q < s . | Mathlib number-system/order primitives |
| 111 | thm | There exists x with x^2 = 2 . | Mathlib number-system/order primitives |
| 112 | defi | Dedekind cut | Mathlib number-system/order primitives |
| 113 | defi | Sequence | `RealAndSequences.lean` / Mathlib analysis |
| 114 | defi | Limit of sequence | `RealAndSequences.lean` / Mathlib analysis |
| 115 | defi | Convergence of sequence | `RealAndSequences.lean` / Mathlib analysis |
| 116 | thm | Every bounded monotonic sequence converges. | `RealAndSequences.lean` / Mathlib analysis |
| 117 | defi | Subsequence | `RealAndSequences.lean` / Mathlib analysis |
| 118 | thm | Every sequence has a monotonic subsequence. | `RealAndSequences.lean` / Mathlib analysis |
| 119 | thm | If a_n a and a_n b , then a = b (i.e. limits are unique) If a_n a and b_n = a_n for all but finitely | `RealAndSequences.lean` / Mathlib analysis |
| 120 | defi | Series and partial sums | `RealAndSequences.lean` / Mathlib analysis |
| 121 | defi | Decimal expansion | `RealAndSequences.lean` / Mathlib analysis |
| 122 | defi | Irrational number | `RealAndSequences.lean` / Mathlib analysis |
| 123 | defi | Periodic number | `RealAndSequences.lean` / Mathlib analysis |
| 124 | prop | A number is periodic iff it is rational. | `RealAndSequences.lean` / Mathlib analysis |
| 125 | defi | Euler's number | `RealAndSequences.lean` / Mathlib analysis |
| 126 | prop | e is irrational. | `RealAndSequences.lean` / Mathlib analysis |
| 127 | defi | Algebraic and transcendental numbers | `RealAndSequences.lean` / Mathlib analysis |
| 128 | prop | All rational numbers are algebraic. | `RealAndSequences.lean` / Mathlib analysis |
| 129 | thm | (Liouville 1851; Non-examinable) L is transcendental, where L = _{n = 1}^ {10^{n!}} = 0.11000100 wit | `RealAndSequences.lean` / Mathlib analysis |
| 130 | thm | (Hermite 1873) e is transcendental. | `RealAndSequences.lean` / Mathlib analysis |
| 131 | thm | (Lindermann 1882) is transcendental. | `RealAndSequences.lean` / Mathlib analysis |
| 132 | lemma | If f: n n is injective, then f is bijective. | `Countability.lean` / Mathlib cardinality |
| 133 | cor | If A is a set and f: A n and g: A m are both bijections, then m = n . | `Countability.lean` / Mathlib cardinality |
| 134 | defi | Finite set and cardinality of set | `Countability.lean` / Mathlib cardinality |
| 135 | lemma | Let S . Then either S is finite or there is a bijection g: S . | `Countability.lean` / Mathlib cardinality |
| 136 | defi | Countable set | `Countability.lean` / Mathlib cardinality |
| 137 | thm | The following are equivalent: A is countable There is an injection from A A = or there is a surjecti | `Countability.lean` / Mathlib cardinality |
| 138 | prop | The integers are countable. | `Countability.lean` / Mathlib cardinality |
| 139 | prop | is countable. | `Countability.lean` / Mathlib cardinality |
| 140 | prop | If A B is injective and B is countable, then A is countable (since we can inject B ). | `Countability.lean` / Mathlib cardinality |
| 141 | prop | ^k is countable for all k | `Countability.lean` / Mathlib cardinality |
| 142 | thm | A countable union of countable sets is countable. | `Countability.lean` / Mathlib cardinality |
| 143 | prop | is countable. | `Countability.lean` / Mathlib cardinality |
| 144 | thm | The set of algebraic numbers is countable. | `Countability.lean` / Mathlib cardinality |
| 145 | thm | The set of real numbers is uncountable. | `Countability.lean` / Mathlib cardinality |
| 146 | cor | There are uncountable many transcendental numbers. | `Countability.lean` / Mathlib cardinality |
| 147 | thm | Let A be a set. Then there is no surjection from A (A) . | `Countability.lean` / Mathlib cardinality |
| 148 | thm | Cantor-Schr\"oder-Bernstein theorem | `Countability.lean` / Mathlib cardinality |
