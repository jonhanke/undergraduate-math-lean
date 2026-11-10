# Course outline: judson2026 (abstract-algebra)

Generated from [`docs/coverage/abstract-algebra/checklist.md`](../../coverage/abstract-algebra/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build AbstractAlgebra` builds this topic.

518 items in 23 chapters; 517 with a Lean name (99.8%).

## Chapter 1

12 items; 12 with a Lean name; 12 in Mathlib.


#### Section 1.2

- **Proposition 1.2.2 (pdf p.17)**, p.17 [AA-001]: Union and intersection of sets are associative, commutative and distribute over each other; union, intersection and complement are the basic set operations — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_2`, `Set.union_assoc`, `Set.inter_assoc`, `Set.union_comm`
- **Theorem 1.2.3 (pdf p.18)**, p.18 [AA-002]: De Morgan: $(A\cup B)' = A'\cap B'$ and $(A\cap B)' = A'\cup B'$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_3`, `Set.compl_union`, `Set.compl_inter`
- **Definition (unnumbered) Cartesian product, relation (pdf p.18)**, p.18 [AA-003]: Cartesian product $A\times B$ as the set of ordered pairs; a relation is a subset of $A\times B$ — *in Mathlib* — `Set.prod`
- **Definition (unnumbered) function, image, injective, surjective (pdf p.19)**, p.19 [AA-004]: Definition of a map with domain and image, and of one-to-one, onto and bijective maps — *in Mathlib* — `Function.Bijective`, `Set.image`, `Set.range`
- **Theorem 1.2.15 (pdf p.21)**, p.21 [AA-005]: Composition of maps is associative: $h\circ(g\circ f)=(h\circ g)\circ f$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_15`, `Function.comp_assoc`
- **Definition (unnumbered) permutation (pdf p.21)**, p.21 [AA-007]: A permutation of a set is a bijection of the set onto itself — *in Mathlib* — `Equiv.Perm`, `Equiv`
- **Definition (unnumbered) invertible map (pdf p.22)**, p.22 [AA-006]: A map is invertible exactly when it is one-to-one and onto — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_20`, `Function.bijective_iff_has_inverse`
- **Theorem 1.2.20 (pdf p.23)**, p.23 [AA-006]: A map is invertible exactly when it is one-to-one and onto — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_20`, `Function.bijective_iff_has_inverse`
- **Theorem 1.2.25 (pdf p.24)**, p.24 [AA-009]: The equivalence classes of an equivalence relation partition the set, and two classes are equal or disjoint — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_25`, `UndergradKB.AbstractAlgebra.Course.judson_1_2_26`, `Setoid.isPartition_classes`, `Setoid.eq_of_mem_classes`
- **Definition (unnumbered) equivalence relation, class (pdf p.24)**, p.24 [AA-008]: Equivalence relation (reflexive, symmetric, transitive) and equivalence class of an element — *in Mathlib* — `Equivalence`, `Setoid`, `Setoid.classes`, `Setoid.mem_classes`
- **Corollary 1.2.26 (pdf p.25)**, p.25 [AA-009]: The equivalence classes of an equivalence relation partition the set, and two classes are equal or disjoint — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_25`, `UndergradKB.AbstractAlgebra.Course.judson_1_2_26`, `Setoid.isPartition_classes`, `Setoid.eq_of_mem_classes`
- **Example 1.2.30 (pdf p.25)**, p.25 [AA-010]: Congruence modulo $n$ is an equivalence relation on the integers — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_1_2_30`, `Int.ModEq`, `ZMod.intCast_eq_intCast_iff`

## Chapter 2

16 items; 16 with a Lean name; 3 proved proved here; 13 in Mathlib.


#### Section 2.1

- **Principle 2.1.1 (pdf p.31)**, p.31 [AA-011]: First principle of induction: base case plus step $S(k)\Rightarrow S(k+1)$ gives $S(n)$ for all $n\ge n_0$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_1`, `Nat.le_induction`
- **Example 2.1.4 (pdf p.31)**, p.31 [AA-015]: Binomial theorem $(a+b)^n=\sum_k\binom nk a^k b^{n-k}$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_4`, `add_pow`, `Commute.add_pow`
- **Principle 2.1.5 (pdf p.32)**, p.32 [AA-012]: Second principle of induction (strong induction) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_5`, `Nat.strong_induction_on`
- **Principle 2.1.6 (pdf p.32)**, p.32 [AA-013]: Well-ordering principle: every nonempty set of positive integers has a least element — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_6`, `WellFounded.has_min`, `wellFounded_lt`, `Nat.find`
- **Lemma 2.1.7 (pdf p.32)**, p.32 [AA-014]: Induction (first principle), strong induction and well-ordering are logically equivalent — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_7`, `UndergradKB.AbstractAlgebra.Course.judson_2_1_8`, `UndergradKB.AbstractAlgebra.one_le_of_induction`, `UndergradKB.AbstractAlgebra.wellOrdering_of_induction`
- **Theorem 2.1.8 (pdf p.32)**, p.32 [AA-014]: Induction (first principle), strong induction and well-ordering are logically equivalent — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_2_1_7`, `UndergradKB.AbstractAlgebra.Course.judson_2_1_8`, `UndergradKB.AbstractAlgebra.one_le_of_induction`, `UndergradKB.AbstractAlgebra.wellOrdering_of_induction`

#### Section 2.2

- **Theorem 2.2.1 (pdf p.33)**, p.33 [AA-016]: Division algorithm: for $b>0$ there are unique $q,r$ with $a=bq+r$ and $0\le r<b$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_1`, `Int.ediv_emod_unique''`
- **Theorem 2.2.2 (pdf p.33)**, p.33 [AA-018]: gcd$(a,b)$ exists and is an integer combination $ar+bs$; coprime integers have $ar+bs=1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_2`, `UndergradKB.AbstractAlgebra.Course.judson_2_2_3`, `Int.gcd_eq_gcd_ab`, `Nat.gcd_eq_gcd_ab`
- **Definition (unnumbered) divides, gcd, relatively prime (pdf p.33)**, p.33 [AA-017]: Divisor, common divisor, greatest common divisor (divisible by every common divisor), and relatively prime integers — *proved proved here* — `UndergradKB.AbstractAlgebra.gcd_universal_property`
- **Corollary 2.2.3 (pdf p.34)**, p.34 [AA-018]: gcd$(a,b)$ exists and is an integer combination $ar+bs$; coprime integers have $ar+bs=1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_2`, `UndergradKB.AbstractAlgebra.Course.judson_2_2_3`, `Int.gcd_eq_gcd_ab`, `Nat.gcd_eq_gcd_ab`
- **Definition (unnumbered) Euclidean algorithm, Example 2.2.4 (pdf p.34-35)**, p.34 [AA-019]: Euclidean algorithm: repeated division computes the gcd and back-substitution gives Bezout coefficients — *in Mathlib* — `Nat.xgcd`, `Nat.xgcd_val`, `Nat.gcd_eq_gcd_ab`, `EuclideanDomain.gcd`
- **Lemma 2.2.5 (pdf p.35)**, p.35 [AA-021]: Euclid's lemma: a prime dividing a product divides one of the factors — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_5`, `Nat.Prime.dvd_mul`, `Prime.dvd_or_dvd`
- **Theorem 2.2.6 (pdf p.35)**, p.35 [AA-022]: There are infinitely many primes — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_6`, `Nat.exists_infinite_primes`
- **Theorem 2.2.7 (pdf p.35)**, p.35 [AA-023]: Fundamental theorem of arithmetic: every integer greater than 1 is a product of primes, uniquely up to order — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_2_2_7`, `Nat.primeFactorsList_unique`, `Nat.prod_primeFactorsList`, `Nat.factorization_prod_pow_eq_self`
- **Definition (unnumbered) prime, composite (pdf p.35)**, p.35 [AA-020]: Prime and composite integers — *in Mathlib* — `Nat.Prime`, `Prime`, `Irreducible`
- **Definition (unnumbered) $\mathbb Z_n$ (pdf p.41)**, p.41 [AA-024]: Integers mod $n$ with addition and multiplication mod $n$ form a commutative ring (commutative, associative, identities, additive inverses, distributive) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_1_4`, `ZMod`, `ZMod.commRing`, `ZMod.intCast_eq_intCast_iff`

## Chapter 3

28 items; 28 with a Lean name; 4 proved proved here; 24 in Mathlib.


#### Section 3.1

- **Proposition 3.1.4 items 1-5 (pdf p.42)**, p.42 [AA-024]: Integers mod $n$ with addition and multiplication mod $n$ form a commutative ring (commutative, associative, identities, additive inverses, distributive) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_1_4`, `ZMod`, `ZMod.commRing`, `ZMod.intCast_eq_intCast_iff`
- **Proposition 3.1.4 item 6 (pdf p.42-43)**, p.42 [AA-025]: A nonzero residue $a$ is invertible mod $n$ iff $\gcd(a,n)=1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_1_4_inverse`, `ZMod.isUnit_iff_coprime`, `ZMod.unitOfCoprime`, `ZMod.coe_mul_inv_eq_one`
- **Section 3.1.2 (pdf p.43-45)**, p.43 [AA-030]: The symmetries of an equilateral triangle form a nonabelian group of order 6, written $S_3$ or $D_3$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_6`, `UndergradKB.AbstractAlgebra.Course.judson_3_2_6_perm`, `UndergradKB.AbstractAlgebra.dihedralGroup_three`
- **Definition (unnumbered) group (pdf p.45-46)**, p.45 [AA-026]: Definition of a group: associative operation with identity and inverses — *in Mathlib* — `Group`, `AddGroup`

#### Section 3.2

- **Example 3.2.1 (pdf p.46)**, p.46 [AA-028]: The integers under addition and the integers mod $n$ under addition are abelian groups — *in Mathlib* — `ZMod.commRing`, `AddCommGroup`
- **Example 3.2.2 (pdf p.46)**, p.46 [AA-028]: The integers under addition and the integers mod $n$ under addition are abelian groups — *in Mathlib* — `ZMod.commRing`, `AddCommGroup`
- **Example 3.2.4 (pdf p.46-47)**, p.46 [AA-029]: The units of $\mathbb Z_n$ (classes coprime to $n$) form a group under multiplication, denoted $U(n)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_4`, `Units`, `ZMod.unitOfCoprime`, `ZMod.isUnit_iff_coprime`
- **Definition (unnumbered) abelian group (pdf p.46)**, p.46 [AA-027]: Abelian (commutative) versus nonabelian groups — *in Mathlib* — `CommGroup`, `AddCommGroup`, `Commute`
- **Example 3.2.6 (pdf p.47)**, p.47 [AA-030]: The symmetries of an equilateral triangle form a nonabelian group of order 6, written $S_3$ or $D_3$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_6`, `UndergradKB.AbstractAlgebra.Course.judson_3_2_6_perm`, `UndergradKB.AbstractAlgebra.dihedralGroup_three`
- **Example 3.2.7 (pdf p.47)**, p.47 [AA-031]: General linear group of invertible $2\times2$ real matrices and its subgroup $SL_2(\mathbb R)$ of determinant-one matrices — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_3_3`, `Matrix.GeneralLinearGroup`, `Matrix.SpecialLinearGroup`, `Matrix.SpecialLinearGroup.toGL`
- **Example 3.2.8 (pdf p.48)**, p.48 [AA-032]: Quaternion group $Q_8$ of order 8, nonabelian — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_8`, `UndergradKB.AbstractAlgebra.quaternionGroup_two`
- **Example 3.2.9 (pdf p.48)**, p.48 [AA-033]: Nonzero real or complex numbers form a group under multiplication — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_9`, `Units`
- **Proposition 3.2.10 (pdf p.48)**, p.48 [AA-036]: The identity of a group is unique — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_10`, `UndergradKB.AbstractAlgebra.identity_unique_left`, `UndergradKB.AbstractAlgebra.identity_unique_right`, `UndergradKB.AbstractAlgebra.inverse_unique`
- **Proposition 3.2.11 (pdf p.48)**, p.48 [AA-037]: Inverses in a group are unique — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_11`, `inv_eq_of_mul_eq_one_right`, `eq_inv_of_mul_eq_one_left`
- **Proposition 3.2.12 (pdf p.48)**, p.48 [AA-038]: $(ab)^{-1}=b^{-1}a^{-1}$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_12`, `mul_inv_rev`
- **Proposition 3.2.13 (pdf p.48)**, p.48 [AA-039]: $(a^{-1})^{-1}=a$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_13`, `inv_inv`
- **Definition (unnumbered) order of a group (pdf p.48)**, p.48 [AA-034]: Order of a group is its number of elements; groups are finite or infinite — *in Mathlib* — `Nat.card`, `Finite`, `Infinite`
- **Proposition 3.2.14 (pdf p.49)**, p.49 [AA-040]: The equations $ax=b$ and $xa=b$ have unique solutions in a group — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_14`, `mul_left_surjective`, `mul_right_injective`, `mul_left_injective`
- **Proposition 3.2.15 (pdf p.49)**, p.49 [AA-041]: Left and right cancellation laws hold in a group — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_15`, `mul_left_cancel`, `mul_right_cancel`
- **Theorem 3.2.16 (pdf p.49)**, p.49 [AA-042]: Laws of exponents in a group: $g^mg^n=g^{m+n}$, $(g^m)^n=g^{mn}$, and $(gh)^n=g^nh^n$ when abelian; additive notation versions — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_16`, `zpow_add`, `zpow_mul`, `mul_zpow`

#### Section 3.3

- **Example 3.3.1 (pdf p.50)**, p.50 [AA-033]: Nonzero real or complex numbers form a group under multiplication — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_2_9`, `Units`
- **Example 3.3.3 (pdf p.50-51)**, p.50 [AA-031]: General linear group of invertible $2\times2$ real matrices and its subgroup $SL_2(\mathbb R)$ of determinant-one matrices — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_3_3`, `Matrix.GeneralLinearGroup`, `Matrix.SpecialLinearGroup`, `Matrix.SpecialLinearGroup.toGL`
- **Definition (unnumbered) subgroup, trivial and proper subgroup (pdf p.50)**, p.50 [AA-043]: Subgroup: a subset that is a group under the restricted operation; trivial subgroup $\{e\}$ and proper subgroups — *in Mathlib* — `Subgroup`
- **Example 3.3.5 (pdf p.51)**, p.51 [AA-035]: Direct product of groups with coordinatewise operation (e.g. $\mathbb Z_2\times\mathbb Z_2$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_3_5`, `Prod.instGroup`, `Prod.instCommGroup`
- **Proposition 3.3.7 (pdf p.51)**, p.51 [AA-044]: Three-condition subgroup test: contains $e$, closed under products and inverses — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_3_7`, `Subgroup`, `Subgroup.one_mem`, `Subgroup.mul_mem`
- **Proposition 3.3.8 (pdf p.52)**, p.52 [AA-045]: Two-condition subgroup test: nonempty and $gh^{-1}\in H$ for all $g,h\in H$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_3_8`, `Subgroup.ofDiv`

#### Section 3.5

- **Definition (unnumbered) center, defined in Exercise 3.5.48 (pdf p.56)**, p.56 [AA-046]: Center of a group (elements commuting with everything) is a subgroup — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_5_48`, `Subgroup.center`, `Subgroup.mem_center_iff`
- **Definition (unnumbered) centralizer, defined in Exercise 3.5.53 (pdf p.56)**, p.56 [AA-047]: Centralizer of a subgroup (elements commuting with every element of it) is a subgroup — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_3_5_53`, `Subgroup.centralizer`

## Chapter 4

15 items; 15 with a Lean name; 4 proved proved here; 11 in Mathlib.


#### Section 4.1

- **Theorem 4.1.3 (pdf p.59)**, p.59 [AA-048]: For $a\in G$, $\langle a\rangle=\{a^k : k\in\mathbb{Z}\}$ is a subgroup and is the smallest subgroup containing $a$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_3`, `Subgroup.zpowers`, `Subgroup.mem_zpowers_iff`, `Subgroup.zpowers_eq_closure`
- **Remark 4.1.4 (pdf p.60)**, p.60 [AA-049]: Definition: cyclic subgroup generated by $a$, cyclic group $G=\langle a\rangle$, generator — *in Mathlib* — `IsCyclic`, `IsCyclic.exists_generator`, `Subgroup.zpowers`
- **Remark 4.1.4 (pdf p.60)**, p.60 [AA-050]: Definition: the order $\lvert a\rvert$ of an element is the least $n>0$ with $a^n=e$, or infinite — *in Mathlib* — `orderOf`, `orderOf_eq_zero_iff`
- **Theorem 4.1.9 (pdf p.60)**, p.60 [AA-051]: Every cyclic group is abelian — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_9`, `IsCyclic.commGroup`
- **Theorem 4.1.10 (pdf p.61)**, p.61 [AA-052]: Every subgroup of a cyclic group is cyclic — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_10`, `Subgroup.isCyclic`, `Subgroup.isCyclic_of_le`
- **Corollary 4.1.11 (pdf p.61)**, p.61 [AA-053]: The subgroups of $\mathbb{Z}$ are exactly $n\mathbb{Z}$, $n\ge 0$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_11`, `UndergradKB.AbstractAlgebra.subgroups_of_int`
- **Proposition 4.1.12 (pdf p.61)**, p.61 [AA-054]: If $a$ generates a cyclic group of order $n$ then $a^k=e$ iff $n\mid k$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_12`, `orderOf_dvd_iff_pow_eq_one`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_one_iff_modEq`
- **Theorem 4.1.13 (pdf p.61)**, p.61 [AA-055]: If $b=a^k$ and $a$ generates a cyclic group of order $n$, then $\lvert b\rvert=n/\gcd(k,n)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_13`, `orderOf_pow'`, `orderOf_pow`, `ZMod.addOrderOf_coe`
- **Corollary 4.1.14 (pdf p.61)**, p.61 [AA-056]: The generators of $\mathbb{Z}_n$ are the residues $r$ with $\gcd(r,n)=1$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_4_1_14`, `UndergradKB.AbstractAlgebra.zmultiples_eq_top_iff_coprime`, `UndergradKB.AbstractAlgebra.zmultiples_eq_top_iff_coprime_val`

#### Section 4.2

- **Proposition 4.2.5 (pdf p.64)**, p.64 [AA-057]: Polar form multiplication: moduli multiply and arguments add, $r\,\mathrm{cis}\theta\cdot s\,\mathrm{cis}\varphi=rs\,\mathrm{cis}(\theta+\varphi)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_4_2_5`, `UndergradKB.AbstractAlgebra.polar_mul_exp`, `UndergradKB.AbstractAlgebra.polar_mul_cos_sin`
- **Theorem 4.2.7 (pdf p.64)**, p.64 [AA-058]: De Moivre: $(r\,\mathrm{cis}\theta)^n=r^n\mathrm{cis}(n\theta)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_2_7`, `Complex.cos_add_sin_mul_I_pow`
- **Definition (unnumbered) in Section 4.2.1 (pdf p.65)**, p.65 [AA-060]: Definition: $n$th roots of unity ($z^n=1$) and primitive $n$th root of unity (a generator of that group) — *in Mathlib* — `rootsOfUnity`, `IsPrimitiveRoot`, `Complex.isPrimitiveRoot_iff`, `Complex.isPrimitiveRoot_exp`
- **Proposition 4.2.9 (pdf p.65)**, p.65 [AA-059]: The circle group $T=\{z\in\mathbb{C}:\lvert z\rvert=1\}$ is a subgroup of $\mathbb{C}^*$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_2_9`, `Circle`, `Circle.instCommGroup`, `Circle.toUnits`
- **Theorem 4.2.10 (pdf p.65)**, p.65 [AA-061]: The $n$th roots of unity in $\mathbb{C}$ are $\mathrm{cis}(2k\pi/n)$, $0\le k<n$, and form a cyclic subgroup of $T$ of order $n$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_4_2_10`, `Complex.mem_rootsOfUnity`, `Complex.card_rootsOfUnity`, `rootsOfUnity.isCyclic`
- **Section 4.3 (pdf p.66-67)**, p.66 [AA-062]: Computing $a^m \bmod n$ by writing $m$ in binary and multiplying repeated squares $a^{2^i}$ — *proved proved here* — `UndergradKB.AbstractAlgebra.powModBinary`, `UndergradKB.AbstractAlgebra.powModBinary_eq`

## Chapter 5

18 items; 18 with a Lean name; 6 proved proved here; 12 in Mathlib.


#### Section 5.1

- **Theorem 5.1.1 (pdf p.73)**, p.73 [AA-063]: The symmetric group $S_n$ of permutations of $\{1,\dots,n\}$ under composition is a group with $n!$ elements — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_1`, `Equiv.Perm`, `Fintype.card_perm`
- **Definition (unnumbered) (pdf p.74)**, p.74 [AA-064]: Definition: a permutation group is a subgroup of $S_n$ (or $S_X$) — *in Mathlib* — `Equiv.Perm`, `Subgroup`
- **Definition (unnumbered) (pdf p.75)**, p.75 [AA-065]: Definition: a cycle of length $k$, cycle notation, and disjoint cycles — *proved proved here* — `UndergradKB.AbstractAlgebra.formPerm_isCycle_length`, `UndergradKB.AbstractAlgebra.disjoint_cycles_commute`
- **Proposition 5.1.8 (pdf p.76)**, p.76 [AA-066]: Disjoint cycles (indeed disjoint permutations) commute — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_8`, `Equiv.Perm.Disjoint.commute`
- **Theorem 5.1.9 (pdf p.76)**, p.76 [AA-067]: Every permutation of a finite set is a product of disjoint cycles — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_9`, `Equiv.Perm.cycleFactorsFinset`, `Equiv.Perm.cycleFactorsFinset_noncommProd`, `Equiv.Perm.cycle_induction_on`
- **Proposition 5.1.12 (pdf p.77)**, p.77 [AA-069]: Every permutation of a finite set is a product of transpositions — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_12`, `Equiv.Perm.swap_induction_on`, `Equiv.Perm.closure_isSwap`
- **Lemma 5.1.14 (pdf p.77)**, p.77 [AA-070]: Parity is well defined: a permutation cannot be both an even-length and an odd-length product of transpositions (the identity is only an even product) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_15`, `UndergradKB.AbstractAlgebra.Course.judson_5_1_14`, `Equiv.Perm.sign`, `Equiv.Perm.sign_swap`
- **Definition (unnumbered) (pdf p.77)**, p.77 [AA-068]: Definition: a transposition is a 2-cycle — *in Mathlib* — `Equiv.swap`, `Equiv.Perm.IsSwap`, `Equiv.Perm.card_support_eq_two`
- **Theorem 5.1.15 (pdf p.78)**, p.78 [AA-070]: Parity is well defined: a permutation cannot be both an even-length and an odd-length product of transpositions (the identity is only an even product) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_15`, `UndergradKB.AbstractAlgebra.Course.judson_5_1_14`, `Equiv.Perm.sign`, `Equiv.Perm.sign_swap`
- **Theorem 5.1.16 (pdf p.78)**, p.78 [AA-072]: Definition and subgroup property: even permutations form the alternating group $A_n\le S_n$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_16`, `alternatingGroup`, `alternatingGroup_eq_sign_ker`
- **Definition (unnumbered) (pdf p.78)**, p.78 [AA-071]: Definition: even and odd permutations — *in Mathlib* — `Equiv.Perm.sign`, `Equiv.Perm.mem_alternatingGroup`, `Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length`
- **Proposition 5.1.17 (pdf p.79)**, p.79 [AA-073]: For $n\ge2$ there are as many even as odd permutations, so $\lvert A_n\rvert=n!/2$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_5_1_17`, `card_alternatingGroup`, `two_mul_card_alternatingGroup`, `alternatingGroup.index_eq_two`
- **Definition (unnumbered) (pdf p.79)**, p.79 [AA-074]: Definition: the dihedral group $D_n$ of rigid motions of a regular $n$-gon — *proved proved here* — `UndergradKB.AbstractAlgebra.polygonSymmetries_equiv_dihedral`

#### Section 5.2

- **Theorem 5.2.2 (pdf p.80)**, p.80 [AA-075]: $D_n$ is a subgroup of $S_n$ of order $2n$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_5_2_2`, `UndergradKB.AbstractAlgebra.dihedralGroup_embeds_perm`
- **Theorem 5.2.3 (pdf p.80)**, p.80 [AA-076]: $D_n$ is generated by a rotation $r$ of order $n$ and a reflection $s$ of order 2 with $srs=r^{-1}$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_5_2_3`, `UndergradKB.AbstractAlgebra.dihedralGroup_generated`
- **Proposition 5.2.8 (pdf p.83)**, p.83 [AA-077]: The group of rotations of a cube has 24 elements and is isomorphic to $S_4$ (via its action on the 4 diagonals) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_5_2_8`, `UndergradKB.AbstractAlgebra.Course.judson_5_2_9`, `UndergradKB.AbstractAlgebra.cubeRotationsEquivPerm`, `UndergradKB.AbstractAlgebra.card_cubeRotations`
- **Theorem 5.2.9 (pdf p.83)**, p.83 [AA-077]: The group of rotations of a cube has 24 elements and is isomorphic to $S_4$ (via its action on the 4 diagonals) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_5_2_8`, `UndergradKB.AbstractAlgebra.Course.judson_5_2_9`, `UndergradKB.AbstractAlgebra.cubeRotationsEquivPerm`, `UndergradKB.AbstractAlgebra.card_cubeRotations`
- **Definition (unnumbered) (pdf p.89)**, p.89 [AA-078]: Definition: left coset $gH$ and right coset $Hg$ of a subgroup — *in Mathlib* — `QuotientGroup.mk`, `mem_leftCoset_iff`, `mem_rightCoset_iff`

## Chapter 6

17 items; 17 with a Lean name; 3 proved proved here; 14 in Mathlib.


#### Section 6.1

- **Lemma 6.1.3 (pdf p.90)**, p.90 [AA-079]: Equivalent conditions for $g_1H=g_2H$ (including $g_1^{-1}g_2\in H$ and $g_2\in g_1H$) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_6_1_3`, `UndergradKB.AbstractAlgebra.coset_equivalences`
- **Theorem 6.1.4 (pdf p.90)**, p.90 [AA-080]: Left (and right) cosets of $H$ partition $G$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_1_4`, `UndergradKB.AbstractAlgebra.Course.judson_6_1_5`, `QuotientGroup.leftRel`, `QuotientGroup.rightRel`
- **Remark 6.1.5 (pdf p.90)**, p.90 [AA-080]: Left (and right) cosets of $H$ partition $G$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_1_4`, `UndergradKB.AbstractAlgebra.Course.judson_6_1_5`, `QuotientGroup.leftRel`, `QuotientGroup.rightRel`
- **Definition (unnumbered) (pdf p.90)**, p.90 [AA-081]: Definition: the index $[G:H]$ is the number of left cosets — *in Mathlib* — `Subgroup.index`, `Subgroup.index_eq_card`
- **Theorem 6.1.8 (pdf p.91)**, p.91 [AA-082]: The number of left cosets equals the number of right cosets — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_1_8`, `QuotientGroup.quotientRightRelEquivQuotientLeftRel`, `QuotientGroup.card_quotient_rightRel`

#### Section 6.2

- **Proposition 6.2.1 (pdf p.91)**, p.91 [AA-083]: For $g\in G$, $h\mapsto gh$ is a bijection $H\to gH$ (all cosets have size $\lvert H\rvert$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_1`, `Subgroup.leftCosetEquivSubgroup`
- **Theorem 6.2.2 (pdf p.91)**, p.91 [AA-084]: Lagrange: $\lvert G\rvert=[G:H]\lvert H\rvert$, so $\lvert H\rvert$ divides $\lvert G\rvert$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_2`, `Subgroup.card_subgroup_dvd_card`, `Subgroup.index_mul_card`, `Subgroup.card_mul_index`
- **Corollary 6.2.3 (pdf p.91)**, p.91 [AA-085]: The order of an element of a finite group divides the order of the group — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_3`, `orderOf_dvd_natCard`, `orderOf_dvd_card`
- **Corollary 6.2.4 (pdf p.91)**, p.91 [AA-086]: A group of prime order is cyclic, generated by any non-identity element — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_4`, `isCyclic_of_prime_card`
- **Corollary 6.2.5 (pdf p.91)**, p.91 [AA-087]: For $K\le H\le G$ finite, $[G:K]=[G:H][H:K]$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_5`, `Subgroup.relIndex_mul_index`, `Subgroup.relIndex_dvd_index_of_le`, `Subgroup.index_dvd_of_le`
- **Proposition 6.2.7 (pdf p.92)**, p.92 [AA-088]: $A_4$ has no subgroup of order 6 (converse of Lagrange fails) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_7`, `UndergradKB.AbstractAlgebra.alternatingGroup_four_no_subgroup_order_six`
- **Theorem 6.2.8 (pdf p.92)**, p.92 [AA-089]: Two cycles are conjugate in $S_n$ iff they have the same length — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_2_8`, `Equiv.Perm.IsCycle.isConj_iff`, `Equiv.Perm.IsCycle.isConj`, `Equiv.Perm.IsCycle.conj`
- **Definition (unnumbered) (pdf p.92)**, p.92 [AA-090]: Definition: Euler totient $\varphi(n)$, the number of $1\le m<n$ coprime to $n$ — *in Mathlib* — `Nat.totient`, `Nat.totient_eq_card_coprime`

#### Section 6.3

- **Theorem 6.3.1 (pdf p.93)**, p.93 [AA-091]: $\lvert U(n)\rvert=\varphi(n)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_3_1`, `ZMod.card_units_eq_totient`
- **Theorem 6.3.2 (pdf p.93)**, p.93 [AA-092]: Euler's theorem: $a^{\varphi(n)}\equiv1\pmod n$ for $\gcd(a,n)=1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_3_2`, `Nat.ModEq.pow_totient`, `ZMod.pow_totient`
- **Theorem 6.3.3 (pdf p.93)**, p.93 [AA-093]: Fermat's little theorem: $a^{p-1}\equiv1\pmod p$ for $p\nmid a$, and $b^p\equiv b$ for all $b$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_6_3_3`, `Nat.ModEq.pow_card_sub_one_eq_one`, `Int.ModEq.pow_card_sub_one_eq_one`, `ZMod.pow_card_sub_one_eq_one`
- **Definition (unnumbered, pdf p.96)**, p.96 [AA-094]: A cryptosystem is a pair of an encryption map and a decryption map indexed by a secret key (private key) or by a public/private key pair (public key cryptosystem) — *proved proved here* — `UndergradKB.AbstractAlgebra.Cryptosystem`

## Chapter 7

10 items; 10 with a Lean name; 10 proved proved here.


#### Section 7.1

- **Example 7.1.1 (pdf p.97)**, p.97 [AA-095]: The shift cipher $f(p)=p+b \bmod 26$ is a bijection of $\mathbb{Z}_{26}$ with inverse $p \mapsto p-b$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_1_1`, `UndergradKB.AbstractAlgebra.shiftCipher`, `UndergradKB.AbstractAlgebra.shiftCipher_bijective`
- **Example 7.1.3 (pdf p.98)**, p.98 [AA-096]: The affine cipher $f(p)=ap+b \bmod n$ can be decrypted exactly when $\gcd(a,n)=1$, with inverse $p \mapsto a^{-1}(p-b)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_1_3`, `UndergradKB.AbstractAlgebra.affineCipher_bijective_iff`, `UndergradKB.AbstractAlgebra.affineCipher`
- **Example 7.1.4 (pdf p.98)**, p.98 [AA-097]: A matrix cipher $f(p)=Ap+b$ over $\mathbb{Z}_{26}$ on blocks of letters is invertible when $A$ is an invertible matrix, with inverse $p \mapsto A^{-1}(p-b)$; $A$ is invertible iff $\det A$ is a unit — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_1_4`, `UndergradKB.AbstractAlgebra.matrixCipher`, `UndergradKB.AbstractAlgebra.matrixCipher_bijective`, `UndergradKB.AbstractAlgebra.matrix_invertible_iff_det_unit`
- **Definition (unnumbered, pdf p.98)**, p.98 [AA-096]: The affine cipher $f(p)=ap+b \bmod n$ can be decrypted exactly when $\gcd(a,n)=1$, with inverse $p \mapsto a^{-1}(p-b)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_1_3`, `UndergradKB.AbstractAlgebra.affineCipher_bijective_iff`, `UndergradKB.AbstractAlgebra.affineCipher`
- **Definition (unnumbered, pdf p.98)**, p.98 [AA-097]: A matrix cipher $f(p)=Ap+b$ over $\mathbb{Z}_{26}$ on blocks of letters is invertible when $A$ is an invertible matrix, with inverse $p \mapsto A^{-1}(p-b)$; $A$ is invertible iff $\det A$ is a unit — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_1_4`, `UndergradKB.AbstractAlgebra.matrixCipher`, `UndergradKB.AbstractAlgebra.matrixCipher_bijective`, `UndergradKB.AbstractAlgebra.matrix_invertible_iff_det_unit`

#### Section 7.2

- **Example 7.2.1 (pdf p.99)**, p.99 [AA-098]: RSA: with $n=pq$, $m=\varphi(n)$, public $E$ coprime to $m$ and secret $D$ with $DE\equiv 1 \pmod m$, encryption is $x \mapsto x^E \bmod n$ and decryption is $y \mapsto y^D \bmod n$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_2_1`, `UndergradKB.AbstractAlgebra.rsaEncrypt`, `UndergradKB.AbstractAlgebra.rsaDecrypt`, `UndergradKB.AbstractAlgebra.rsaCryptosystem`
- **Definition (unnumbered, pdf p.99)**, p.99 [AA-098]: RSA: with $n=pq$, $m=\varphi(n)$, public $E$ coprime to $m$ and secret $D$ with $DE\equiv 1 \pmod m$, encryption is $x \mapsto x^E \bmod n$ and decryption is $y \mapsto y^D \bmod n$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_2_1`, `UndergradKB.AbstractAlgebra.rsaEncrypt`, `UndergradKB.AbstractAlgebra.rsaDecrypt`, `UndergradKB.AbstractAlgebra.rsaCryptosystem`
- **Discussion after Example 7.2.1 (unnumbered, pdf p.100)**, p.100 [AA-099]: RSA correctness: for $n=pq$ with distinct primes and $DE\equiv 1 \pmod{\varphi(n)}$, $(x^E)^D\equiv x \pmod n$ for all $x<n$ (both $\gcd(x,n)=1$ and non-coprime cases) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_2_rsa_correct`, `UndergradKB.AbstractAlgebra.rsa_correct`
- **Discussion (unnumbered, pdf p.100)**, p.100 [AA-100]: Message verification: a sender signs by applying his secret decryption key before encrypting with the receiver's public key, so the receiver can check authorship by applying the sender's public key — *proved proved here* — `UndergradKB.AbstractAlgebra.message_verification`
- **Definition (unnumbered, pdf p.104; Additional Exercises 7.5)**, p.104 [AA-101]: A pseudoprime base $b$ is an odd composite $n$ with $b^{n-1}\equiv 1 \pmod n$; a Carmichael number is a composite that is a pseudoprime to every base coprime to it (smallest is 561) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_7_2_pseudoprime`, `UndergradKB.AbstractAlgebra.Course.judson_7_2_carmichael_561`, `UndergradKB.AbstractAlgebra.IsPseudoprime`, `UndergradKB.AbstractAlgebra.isPseudoprime_iff_fermatPsp`

## Chapter 8

29 items; 29 with a Lean name; 26 proved proved here; 3 in Mathlib.


#### Section 8.1

- **Example 8.1.3 (pdf p.108)**, p.108 [AA-103]: Appending an even-parity check bit to a binary word gives a code that detects every single-bit error — *proved proved here* — `UndergradKB.AbstractAlgebra.evenParity_detects_single_error`, `UndergradKB.AbstractAlgebra.parityBlockCode`, `UndergradKB.AbstractAlgebra.parityBlockCode_codewords_even`
- **Definition (unnumbered, pdf p.109-110)**, p.109 [AA-104]: A binary symmetric channel flips each bit independently with probability $q=1-p$; maximum-likelihood decoding decodes a received word to the nearest codeword — *proved proved here* — `UndergradKB.AbstractAlgebra.errProb`
- **Theorem 8.1.7 (pdf p.110)**, p.110 [AA-105]: On a binary symmetric channel the probability of exactly $k$ errors in an $n$-bit word is $\binom{n}{k} q^k p^{n-k}$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_1_7`, `UndergradKB.AbstractAlgebra.prob_exactly_k_errors`
- **Example 8.1.9 (pdf p.111)**, p.111 [AA-102]: An $(n,m)$-block code is an injective encoding map $\mathbb{Z}_2^m\to\mathbb{Z}_2^n$ together with a decoding map $\mathbb{Z}_2^n\to\mathbb{Z}_2^m$; codewords are the image of the encoder — *proved proved here* — `UndergradKB.AbstractAlgebra.BlockCode`, `UndergradKB.AbstractAlgebra.BlockCode.codewords`
- **Proposition 8.1.11 (pdf p.111)**, p.111 [AA-107]: Hamming distance is a metric on binary words and $w(x)=d(x,0)$: nonnegative, zero iff equal, symmetric, triangle inequality — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_8_1_11`, `hammingDist_zero_right`, `hammingDist_eq_zero`, `hammingDist_comm`
- **Definition (unnumbered, pdf p.111)**, p.111 [AA-102]: An $(n,m)$-block code is an injective encoding map $\mathbb{Z}_2^m\to\mathbb{Z}_2^n$ together with a decoding map $\mathbb{Z}_2^n\to\mathbb{Z}_2^m$; codewords are the image of the encoder — *proved proved here* — `UndergradKB.AbstractAlgebra.BlockCode`, `UndergradKB.AbstractAlgebra.BlockCode.codewords`
- **Definition (unnumbered, pdf p.111)**, p.111 [AA-106]: Hamming distance $d(x,y)$ counts differing coordinates, weight $w(x)$ counts nonzero coordinates, and $d_{\min}$ is the least distance between distinct codewords — *proved proved here* — `UndergradKB.AbstractAlgebra.minDist`, `UndergradKB.AbstractAlgebra.minDist_le`, `UndergradKB.AbstractAlgebra.weight_eq_dist_zero`
- **Theorem 8.1.13 (pdf p.112)**, p.112 [AA-108]: A code with minimum distance $2n+1$ corrects any $n$ or fewer errors and detects any $2n$ or fewer errors — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_1_13`, `UndergradKB.AbstractAlgebra.correct_up_to`, `UndergradKB.AbstractAlgebra.detect_up_to`
- **Definition (unnumbered, pdf p.113)**, p.113 [AA-109]: A group code is a binary code that is a subgroup of $\mathbb{Z}_2^n$ (closure under addition suffices) — *proved proved here* — `UndergradKB.AbstractAlgebra.GroupCode`, `UndergradKB.AbstractAlgebra.groupCodeOfAddClosed`

#### Section 8.2

- **Lemma 8.2.2 (pdf p.114)**, p.114 [AA-110]: $w(x+y)=d(x,y)$ for binary $n$-tuples — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_8_2_2`, `hammingDist_eq_hammingNorm`
- **Theorem 8.2.3 (pdf p.114)**, p.114 [AA-111]: For a group code the minimum distance equals the minimum weight of a nonzero codeword — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_2_3`, `UndergradKB.AbstractAlgebra.minDist_groupCode`
- **Example 8.2.4 (pdf p.115)**, p.115 [AA-103]: Appending an even-parity check bit to a binary word gives a code that detects every single-bit error — *proved proved here* — `UndergradKB.AbstractAlgebra.evenParity_detects_single_error`, `UndergradKB.AbstractAlgebra.parityBlockCode`, `UndergradKB.AbstractAlgebra.parityBlockCode_codewords_even`
- **Theorem 8.2.6 (pdf p.115)**, p.115 [AA-112]: The null space $\{x : Hx=0\}$ of a binary matrix $H$ is a group code — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_2_6`, `UndergradKB.AbstractAlgebra.nullCode`
- **Definition (unnumbered, pdf p.115)**, p.115 [AA-113]: A linear code is a code given as the null space of some binary matrix $H$ — *proved proved here* — `UndergradKB.AbstractAlgebra.IsLinearCode`, `UndergradKB.AbstractAlgebra.isLinearCode_nullCode`
- **Definition (unnumbered, pdf p.116)**, p.116 [AA-114]: A canonical parity-check matrix has the form $H=(A\mid I_m)$ with associated standard generator matrix $G=\binom{I_{n-m}}{A}$ — *proved proved here* — `UndergradKB.AbstractAlgebra.canonH`, `UndergradKB.AbstractAlgebra.stdG`

#### Section 8.3

- **Theorem 8.3.3 (pdf p.118)**, p.118 [AA-115]: For a canonical parity-check matrix, the first $n-m$ bits of a codeword are free information bits and the last $m$ are check bits, giving an $(n,n-m)$-block code — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_3`, `UndergradKB.AbstractAlgebra.mem_nullCode_canonH_iff`
- **Theorem 8.3.4 (pdf p.118)**, p.118 [AA-116]: The image of a standard generator matrix is an $(n,k)$-block code and a group code (the encoding map is injective and additive) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_4`, `UndergradKB.AbstractAlgebra.stdBlockCode`, `UndergradKB.AbstractAlgebra.stdBlockCode_encode_add`, `UndergradKB.AbstractAlgebra.stdCode`
- **Lemma 8.3.5 (pdf p.118)**, p.118 [AA-117]: For $H=(A\mid I_m)$ and $G=\binom{I_{n-m}}{A}$ over $\mathbb{Z}_2$, $HG=0$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_5`, `UndergradKB.AbstractAlgebra.canonH_mul_stdG`
- **Theorem 8.3.6 (pdf p.119)**, p.119 [AA-118]: The code generated by $G$ equals the null space of the associated canonical $H$ ($y\in C$ iff $Hy=0$) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_6`, `UndergradKB.AbstractAlgebra.stdCode_eq_nullCode`
- **Proposition 8.3.8 (pdf p.120)**, p.120 [AA-119]: For a binary matrix $H$ the product $He_i$ is the $i$-th column of $H$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_8`, `Matrix.mulVec_single_one`
- **Theorem 8.3.9 (pdf p.120)**, p.120 [AA-120]: The null space of $H$ is a single-error-detecting code iff $H$ has no zero column — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_9`, `UndergradKB.AbstractAlgebra.nullCode_detects_iff`
- **Theorem 8.3.12 (pdf p.120)**, p.120 [AA-121]: The null space of $H$ is a single-error-correcting code iff $H$ has no zero column and no two equal columns — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_3_12`, `UndergradKB.AbstractAlgebra.nullCode_corrects_iff`

#### Section 8.4

- **Proposition 8.4.2 (pdf p.121)**, p.121 [AA-123]: If $x=c+e$ with $c$ a codeword, the syndrome of $x$ equals the syndrome of the error $e$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_4_2`, `UndergradKB.AbstractAlgebra.syndrome_add_codeword`
- **Definition (unnumbered, pdf p.121)**, p.121 [AA-122]: The syndrome of a word $x\in\mathbb{Z}_2^n$ with respect to $H$ is $Hx$ — *proved proved here* — `UndergradKB.AbstractAlgebra.syndrome`
- **Theorem 8.4.3 (pdf p.122)**, p.122 [AA-124]: For a single-error-correcting code, a received word with at most one error has syndrome 0 if error-free, otherwise its syndrome equals the column of $H$ at the error position — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_4_3`, `UndergradKB.AbstractAlgebra.syndrome_single_error`
- **Definition (unnumbered, pdf p.122-123)**, p.122 [AA-125]: Coset (standard) decoding: a coset leader is a least-weight word in a coset $e+C$, and a received $r$ is decoded to $r+e$ with $e$ the leader of its coset; a decoding table lists a leader for each syndrome — *proved proved here* — `UndergradKB.AbstractAlgebra.IsCosetLeader`, `UndergradKB.AbstractAlgebra.exists_cosetLeader`, `UndergradKB.AbstractAlgebra.isCosetLeader_nullCode_iff`
- **Example 8.4.7 (pdf p.123)**, p.123 [AA-125]: Coset (standard) decoding: a coset leader is a least-weight word in a coset $e+C$, and a received $r$ is decoded to $r+e$ with $e$ the leader of its coset; a decoding table lists a leader for each syndrome — *proved proved here* — `UndergradKB.AbstractAlgebra.IsCosetLeader`, `UndergradKB.AbstractAlgebra.exists_cosetLeader`, `UndergradKB.AbstractAlgebra.isCosetLeader_nullCode_iff`
- **Proposition 8.4.9 (pdf p.123)**, p.123 [AA-126]: Two binary words lie in the same coset of the code $C=\mathrm{Null}(H)$ iff they have the same syndrome — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_8_4_9`, `UndergradKB.AbstractAlgebra.sameCoset_iff_syndrome`, `UndergradKB.AbstractAlgebra.quotient_eq_iff_syndrome`, `UndergradKB.AbstractAlgebra.cosetDecode`

#### Section 8.6

- **Definition (in Exercise 8.6.26, pdf p.129)**, p.129 [AA-127]: A Hamming code is the null space of a binary matrix whose $i$-th column is $i$ written in binary; it is perfect when it has the maximum number of information bits for its check bits and shortened otherwise — *proved proved here* — `UndergradKB.AbstractAlgebra.hammingMatrix`, `UndergradKB.AbstractAlgebra.hammingMatrix_cols`, `UndergradKB.AbstractAlgebra.hammingCode_corrects`

## Chapter 9

20 items; 20 with a Lean name; 6 proved proved here; 14 in Mathlib.

- **Definition 9.1 (pdf p.131)**, p.131 [AA-128]: Two groups are isomorphic if there is a bijective operation-preserving map between them — *in Mathlib* — `MulEquiv`

#### Section 9.1

- **Theorem 9.1.6 (pdf p.132)**, p.132 [AA-129]: An isomorphism has an isomorphism as inverse and preserves order of the group, commutativity, cyclicity and existence of subgroups of each order — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_6`, `MulEquiv.symm`, `Nat.card_congr`, `MulEquiv.isCyclic`
- **Theorem 9.1.7 (pdf p.133)**, p.133 [AA-132]: Every infinite cyclic group is isomorphic to $\mathbb{Z}$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_7`, `intEquivOfZPowersEqTop`, `zpowersHom_bijective`, `zmultiplesEquivInt`
- **Theorem 9.1.8 (pdf p.133)**, p.133 [AA-133]: A cyclic group of order $n$ is isomorphic to $\mathbb{Z}_n$; in particular any group of prime order $p$ is isomorphic to $\mathbb{Z}_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_8`, `UndergradKB.AbstractAlgebra.Course.judson_9_1_9`, `zmodCyclicMulEquiv`, `mulEquivOfCyclicCardEq`
- **Corollary 9.1.9 (pdf p.133)**, p.133 [AA-133]: A cyclic group of order $n$ is isomorphic to $\mathbb{Z}_n$; in particular any group of prime order $p$ is isomorphic to $\mathbb{Z}_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_8`, `UndergradKB.AbstractAlgebra.Course.judson_9_1_9`, `zmodCyclicMulEquiv`, `mulEquivOfCyclicCardEq`
- **Theorem 9.1.10 (pdf p.133)**, p.133 [AA-130]: Isomorphism of groups is an equivalence relation — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_10`, `MulEquiv.refl`, `MulEquiv.symm`, `MulEquiv.trans`
- **Theorem 9.1.12 (pdf p.134)**, p.134 [AA-134]: Cayley: every group is isomorphic to a group of permutations (left regular representation $g\mapsto\lambda_g$, with right regular representation $\rho_g$ as variant) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_12`, `Equiv.Perm.subgroupOfMulAction`, `MulAction.toPermHom`, `MulAction.toPerm_injective`

#### Section 9.2

- **Proposition 9.2.1 (pdf p.135)**, p.135 [AA-135]: The Cartesian product $G\times H$ (and finite products $G_1\times\cdots\times G_n$) is a group under componentwise operation (external direct product); $\mathbb{Z}_2^n$ is the group of binary $n$-tuples — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_1`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_4`, `Prod.instGroup`, `Pi.group`
- **Example 9.2.4 (pdf p.136)**, p.136 [AA-135]: The Cartesian product $G\times H$ (and finite products $G_1\times\cdots\times G_n$) is a group under componentwise operation (external direct product); $\mathbb{Z}_2^n$ is the group of binary $n$-tuples — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_1`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_4`, `Prod.instGroup`, `Pi.group`
- **Theorem 9.2.5 (pdf p.136)**, p.136 [AA-136]: The order of $(g,h)$ in $G\times H$ is $\mathrm{lcm}(\operatorname{ord} g,\operatorname{ord} h)$, and similarly for $n$-fold products — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_5`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_6`, `Prod.orderOf`, `Pi.orderOf`
- **Corollary 9.2.6 (pdf p.136)**, p.136 [AA-136]: The order of $(g,h)$ in $G\times H$ is $\mathrm{lcm}(\operatorname{ord} g,\operatorname{ord} h)$, and similarly for $n$-fold products — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_5`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_6`, `Prod.orderOf`, `Pi.orderOf`
- **Theorem 9.2.9 (pdf p.136)**, p.136 [AA-137]: $\mathbb{Z}_m\times\mathbb{Z}_n\cong\mathbb{Z}_{mn}$ iff $\gcd(m,n)=1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_9`, `ZMod.chineseRemainder`, `Group.isCyclic_prod_iff`, `mulEquivOfCyclicCardEq`
- **Corollary 9.2.10 (pdf p.136)**, p.136 [AA-138]: $\prod \mathbb{Z}_{n_i}\cong \mathbb{Z}_{n_1\cdots n_k}$ iff the $n_i$ are pairwise coprime; hence $\mathbb{Z}_m$ is the product of $\mathbb{Z}_{p_i^{e_i}}$ over the prime-power factorization of $m$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_10`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_11`, `UndergradKB.AbstractAlgebra.zmod_mul_equiv_iff_coprime`, `UndergradKB.AbstractAlgebra.zmod_prod_equiv_iff_coprime`
- **Corollary 9.2.11 (pdf p.137)**, p.137 [AA-138]: $\prod \mathbb{Z}_{n_i}\cong \mathbb{Z}_{n_1\cdots n_k}$ iff the $n_i$ are pairwise coprime; hence $\mathbb{Z}_m$ is the product of $\mathbb{Z}_{p_i^{e_i}}$ over the prime-power factorization of $m$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_10`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_11`, `UndergradKB.AbstractAlgebra.zmod_mul_equiv_iff_coprime`, `UndergradKB.AbstractAlgebra.zmod_prod_equiv_iff_coprime`
- **Theorem 9.2.15 (pdf p.137)**, p.137 [AA-140]: If $G$ is the internal direct product of $H_1,\dots,H_n$ then $G\cong \prod H_i$ (in particular $G\cong H\times K$) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_15`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_17`, `UndergradKB.AbstractAlgebra.internalDirectProductEquiv₂`, `UndergradKB.AbstractAlgebra.internalDirectProductEquiv`
- **Definition (unnumbered, pdf p.137-138)**, p.137 [AA-139]: $G$ is the internal direct product of subgroups $H$ and $K$ (and of $H_1,\dots,H_n$) when $G=HK$, the subgroups intersect trivially (resp. each meets the join of the others trivially), and elements of different factors commute — *proved proved here* — `UndergradKB.AbstractAlgebra.IsInternalDirectProduct`
- **Theorem 9.2.17 (pdf p.138)**, p.138 [AA-140]: If $G$ is the internal direct product of $H_1,\dots,H_n$ then $G\cong \prod H_i$ (in particular $G\cong H\times K$) — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_9_2_15`, `UndergradKB.AbstractAlgebra.Course.judson_9_2_17`, `UndergradKB.AbstractAlgebra.internalDirectProductEquiv₂`, `UndergradKB.AbstractAlgebra.internalDirectProductEquiv`

#### Section 9.4

- **Definition (in Exercises 9.4.34, 9.4.37, 9.4.41, pdf p.140-141)**, p.140 [AA-131]: An automorphism is an isomorphism of $G$ with itself; they form the group $\mathrm{Aut}(G)$, and conjugation $x\mapsto gxg^{-1}$ gives the inner automorphisms $\mathrm{Inn}(G)$ — *in Mathlib* — `MulAut`, `MulAut.conj`
- **Exercise-defined right regular representation (Exercise 9.4.44, pdf p.141)**, p.141 [AA-134]: Cayley: every group is isomorphic to a group of permutations (left regular representation $g\mapsto\lambda_g$, with right regular representation $\rho_g$ as variant) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_9_1_12`, `Equiv.Perm.subgroupOfMulAction`, `MulAction.toPermHom`, `MulAction.toPerm_injective`

#### Section 9.2

- **Examples 9.2.12-9.2.14, 9.2.16** [AA-139]: $G$ is the internal direct product of subgroups $H$ and $K$ (and of $H_1,\dots,H_n$) when $G=HK$, the subgroups intersect trivially (resp. each meets the join of the others trivially), and elements of different factors commute — *proved proved here* — `UndergradKB.AbstractAlgebra.IsInternalDirectProduct`

## Chapter 10

13 items; 13 with a Lean name; 3 proved proved here; 10 in Mathlib.


#### Section 10.1

- **Definition (unnumbered, 10.1.1) (pdf p.143)**, p.143 [AA-141]: A subgroup $N \le G$ is normal when $gN = Ng$ for every $g \in G$. — *in Mathlib* — `Subgroup.Normal`, `normal_iff_eq_cosets`
- **Example 10.1.1 (pdf p.143)**, p.143 [AA-142]: Every subgroup of an abelian group is normal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_1_1`
- **Theorem 10.1.3 (pdf p.143)**, p.143 [AA-143]: For $N \le G$, normality is equivalent to $gNg^{-1} \subseteq N$ for all $g$, and to $gNg^{-1} = N$ for all $g$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_1_3`, `Subgroup.normal_iff_map_conj_eq`, `normal_iff_eq_cosets`
- **Theorem 10.1.4 (pdf p.144)**, p.144 [AA-144]: For $N$ normal in $G$ the cosets form a group $G/N$ under $(aN)(bN)=abN$, of order $[G:N]$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_1_4`, `QuotientGroup.Quotient.group`, `Subgroup.index_eq_card`
- **Definition (unnumbered, factor/quotient group) (pdf p.144)**, p.144 [AA-144]: For $N$ normal in $G$ the cosets form a group $G/N$ under $(aN)(bN)=abN$, of order $[G:N]$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_1_4`, `QuotientGroup.Quotient.group`, `Subgroup.index_eq_card`
- **Example 10.1.6 (pdf p.145)**, p.145 [AA-145]: The cosets $k+n\mathbb{Z}$ of $n\mathbb{Z}$ in $\mathbb{Z}$ form the additive factor group $\mathbb{Z}/n\mathbb{Z}$ with $n$ elements. — *proved proved here* — `UndergradKB.AbstractAlgebra.card_int_quotient_zmultiples`, `UndergradKB.AbstractAlgebra.intQuotientZMultiplesEquivZMod`
- **Definition (unnumbered, 10.2) (pdf p.145)**, p.145 [AA-146]: A group is simple if it is nontrivial and its only normal subgroups are the trivial one and the whole group. — *in Mathlib* — `IsSimpleGroup`
- **Definition (unnumbered, 10.2) (pdf p.145)**, p.145 [AA-147]: A cyclic group of prime order $p$ is simple. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_2_prime_order_simple`, `isSimpleGroup_of_prime_card`, `IsPGroup.isSimpleGroup_iff_card_eq`

#### Section 10.2

- **Lemma 10.2.1 (pdf p.145)**, p.145 [AA-148]: For $n \ge 3$ the alternating group $A_n$ is generated by 3-cycles. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_2_1`, `Equiv.Perm.closure_three_cycles_eq_alternating`, `alternatingGroup.closure_isThreeCycles_eq_top`
- **Lemma 10.2.2 (pdf p.146)**, p.146 [AA-149]: For $n \ge 3$, a normal subgroup of $A_n$ containing a 3-cycle equals $A_n$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_10_2_2`, `UndergradKB.AbstractAlgebra.alternatingGroup_eq_top_of_threeCycle`
- **Lemma 10.2.3 (pdf p.146)**, p.146 [AA-150]: For $n \ge 5$, every nontrivial normal subgroup of $A_n$ contains a 3-cycle. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_10_2_3`, `UndergradKB.AbstractAlgebra.exists_threeCycle_of_normal_ne_bot`
- **Theorem 10.2.4 (pdf p.148)**, p.148 [AA-151]: The alternating group $A_n$ is simple for $n \ge 5$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_10_2_4`, `alternatingGroup.isSimpleGroup`

#### Section 10.4

- **Definition (unnumbered, within Exercise 10.4.14) (pdf p.150)**, p.150 [AA-152]: The commutator subgroup $G'$ is the subgroup generated by all commutators $aba^{-1}b^{-1}$. — *in Mathlib* — `commutator`, `commutator_eq_closure`, `Abelianization`

## Chapter 11

17 items; 17 with a Lean name; 5 proved proved here; 12 in Mathlib.

- **Definition (unnumbered, 11.1) (pdf p.151)**, p.151 [AA-153]: A homomorphism of groups is a product-preserving map; its range is the homomorphic image. — *in Mathlib* — `MonoidHom`, `MonoidHom.range`

#### Section 11.1

- **Example 11.1.1 (pdf p.151)**, p.151 [AA-154]: For $g \in G$, the map $n \mapsto g^n$ is a homomorphism $\mathbb{Z} \to G$ with image $\langle g \rangle$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_1`, `zpowersHom`, `range_zpowersHom`
- **Proposition 11.1.4 (pdf p.152)**, p.152 [AA-158]: A homomorphism preserves identity and inverses, sends subgroups to subgroups, and pulls subgroups (normal ones to normal ones) back to subgroups. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_4`, `map_one`, `map_inv`, `Subgroup.map`
- **Definition (unnumbered, kernel) (pdf p.152)**, p.152 [AA-159]: The kernel of a homomorphism is a normal subgroup of the domain. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_5`, `MonoidHom.ker`, `MonoidHom.mem_ker`
- **Theorem 11.1.5 (pdf p.153)**, p.153 [AA-159]: The kernel of a homomorphism is a normal subgroup of the domain. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_5`, `MonoidHom.ker`, `MonoidHom.mem_ker`
- **Example 11.1.6 (pdf p.151, p.153)**, p.153 [AA-156]: The determinant is a homomorphism $GL_n(\mathbb{R}) \to \mathbb{R}^*$ whose kernel is $SL_n(\mathbb{R})$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_2`, `Matrix.detMonoidHom`, `Matrix.GeneralLinearGroup.det`, `Matrix.det_mul`
- **Example 11.1.7 (pdf p.152, p.153)**, p.153 [AA-157]: $\theta \mapsto \cos\theta + i\sin\theta$ is a homomorphism from $(\mathbb{R},+)$ onto the circle group with kernel $2\pi\mathbb{Z}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.circle_exp_ker`, `UndergradKB.AbstractAlgebra.circle_exp_surjective`
- **Example 11.1.9 (pdf p.153)**, p.153 [AA-155]: The kernel of $n \mapsto g^n$ is $\{0\}$ if $g$ has infinite order and $n\mathbb{Z}$ if $g$ has order $n$. — *proved proved here* — `UndergradKB.AbstractAlgebra.ker_zmultiplesHom`, `UndergradKB.AbstractAlgebra.ker_zmultiplesHom_of_addOrderOf_eq_zero`, `UndergradKB.AbstractAlgebra.zpow_eq_one_iff_mem_zmultiples`, `UndergradKB.AbstractAlgebra.mem_ker_zpowersHom_iff`

#### Section 11.2

- **Theorem 11.2.1 (pdf p.153)**, p.153 [AA-161]: First Isomorphism Theorem: $G/\ker\psi \cong \psi(G)$ via a unique isomorphism compatible with the quotient map. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_2_1`, `QuotientGroup.quotientKerEquivRange`, `QuotientGroup.quotientKerEquivOfSurjective`
- **Definition (unnumbered, canonical homomorphism) (pdf p.153)**, p.153 [AA-160]: For $N$ normal, $g \mapsto gN$ is a surjective homomorphism $G \to G/N$ with kernel $N$ (canonical homomorphism). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_canonical_hom`, `QuotientGroup.mk'`, `QuotientGroup.mk'_surjective`, `QuotientGroup.ker_mk'`
- **Example 11.2.2 (pdf p.154)**, p.154 [AA-162]: Cyclic groups of order $n$ are isomorphic to $\mathbb{Z}/n\mathbb{Z}$ and infinite cyclic groups to $\mathbb{Z}$; so up to isomorphism cyclic groups are $\mathbb{Z}$ and $\mathbb{Z}_n$. — *proved proved here* — `UndergradKB.AbstractAlgebra.infiniteCyclicMulEquiv`, `UndergradKB.AbstractAlgebra.finiteCyclicMulEquiv`
- **Theorem 11.2.3 (pdf p.154)**, p.154 [AA-163]: Second Isomorphism Theorem: for $H \le G$, $N \trianglelefteq G$, $HN$ is a subgroup, $H\cap N \trianglelefteq H$ and $H/(H\cap N) \cong HN/N$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_2_3`, `QuotientGroup.quotientInfEquivProdNormalQuotient`, `Subgroup.Normal.subgroupOf`
- **Theorem 11.2.4 (pdf p.155)**, p.155 [AA-164]: Correspondence Theorem: subgroups of $G$ containing $N$ correspond bijectively to subgroups of $G/N$, with normal ones matching. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_11_2_4`, `UndergradKB.AbstractAlgebra.correspondence_normal`
- **Theorem 11.2.5 (pdf p.155)**, p.155 [AA-165]: Third Isomorphism Theorem: for normal $N \subseteq H$ in $G$, $G/H \cong (G/N)/(H/N)$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_2_5`, `QuotientGroup.quotientQuotientEquivQuotient`
- **Definition (unnumbered, inner automorphism; in 11.5 exercises) (pdf p.158)**, p.158 [AA-166]: Conjugation by $g$ is an automorphism of $G$ (inner automorphism), and $g \mapsto i_g$ is a homomorphism into $\mathrm{Aut}(G)$. — *in Mathlib* — `MulAut.conj`, `MulAut`

#### Section 11.1

- **Example 11.1.2** [AA-156]: The determinant is a homomorphism $GL_n(\mathbb{R}) \to \mathbb{R}^*$ whose kernel is $SL_n(\mathbb{R})$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_11_1_2`, `Matrix.detMonoidHom`, `Matrix.GeneralLinearGroup.det`, `Matrix.det_mul`
- **Example 11.1.3** [AA-157]: $\theta \mapsto \cos\theta + i\sin\theta$ is a homomorphism from $(\mathbb{R},+)$ onto the circle group with kernel $2\pi\mathbb{Z}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.circle_exp_ker`, `UndergradKB.AbstractAlgebra.circle_exp_surjective`

## Chapter 12

26 items; 26 with a Lean name; 13 proved proved here; 12 in Mathlib; 1 not formalized.


#### Section 12.1

- **Definition (unnumbered, 12.1.1) (pdf p.159)**, p.159 [AA-167]: A linear map $\mathbb{R}^n \to \mathbb{R}^m$ corresponds to an $m \times n$ matrix, and conversely. — *in Mathlib* — `Matrix.toLin'`, `LinearMap.toMatrix'`, `LinearMap.toMatrix'_toLin'`
- **Definition (unnumbered, 12.1.1) (pdf p.161)**, p.161 [AA-168]: A square matrix is invertible iff its determinant is nonzero. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_1_invertible_iff_det_ne_zero`, `Matrix.isUnit_iff_isUnit_det`
- **Definition (unnumbered, 12.1.1) (pdf p.161)**, p.161 [AA-169]: The determinant is multiplicative, $\det A^{-1} = 1/\det A$, and $\det A^t = \det A$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_1_det_properties`, `Matrix.det_mul`, `Matrix.det_nonsing_inv`, `Matrix.det_transpose`
- **Definition (unnumbered, 12.1.1) (pdf p.161)**, p.161 [AA-170]: A linear map of $\mathbb{R}^n$ scales volume by $\lvert\det\rvert$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_1_volume_scaling`, `MeasureTheory.Measure.addHaar_image_linearMap`
- **Definition (unnumbered, 12.1.2) (pdf p.161)**, p.161 [AA-171]: The invertible (nonsingular) $n \times n$ matrices over $\mathbb{R}$ form the general linear group $GL_n(\mathbb{R})$. — *in Mathlib* — `Matrix.GeneralLinearGroup`, `Matrix.GeneralLinearGroup.det`
- **Definition (unnumbered, 12.1.2) (pdf p.161)**, p.161 [AA-172]: The matrices of determinant 1 form a subgroup $SL_n(\mathbb{R})$ of $GL_n(\mathbb{R})$. — *in Mathlib* — `Matrix.SpecialLinearGroup`
- **Definition (unnumbered, 12.1.3) (pdf p.162)**, p.162 [AA-173]: The orthogonal group $O(n)$ consists of matrices with $A^{-1} = A^t$ and is a subgroup of $GL_n(\mathbb{R})$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_3_orthogonal_group`, `Matrix.orthogonalGroup`, `Matrix.mem_orthogonalGroup_iff`
- **Definition (unnumbered, 12.1.3) (pdf p.163)**, p.163 [AA-175]: A set of vectors is orthonormal when each has length 1 and distinct ones are orthogonal. — *in Mathlib* — `Orthonormal`
- **Definition (unnumbered, 12.1.3) (pdf p.163)**, p.163 [AA-176]: An orthogonal matrix has determinant $\pm 1$. — *proved proved here* — `UndergradKB.AbstractAlgebra.det_orthogonal_eq_one_or_neg_one`
- **Proposition 12.1.6 (pdf p.163)**, p.163 [AA-174]: Basic properties of the Euclidean inner product on $\mathbb{R}^n$: symmetry, bilinearity, positivity, nondegeneracy. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_6`, `real_inner_comm`, `inner_add_right`, `real_inner_smul_right`
- **Theorem 12.1.8 (pdf p.163)**, p.163 [AA-177]: For a square matrix, columns orthonormal, $A^{-1}=A^t$, and preserving inner products, distances, or lengths are all equivalent. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_8`, `UndergradKB.AbstractAlgebra.orthogonal_tfae`
- **Definition (unnumbered, 12.1.4) (pdf p.165)**, p.165 [AA-179]: The special orthogonal group $SO(n)$ is $O(n) \cap SL_n(\mathbb{R})$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_12_1_4_special_orthogonal_group`, `Matrix.specialOrthogonalGroup`, `Matrix.mem_specialOrthogonalGroup_iff`
- **Definition (unnumbered, 12.1.4) (pdf p.165)**, p.165 [AA-180]: The Euclidean group $E(n)$ is the set of pairs $(A,x)$ with $A \in O(n)$, $x \in \mathbb{R}^n$, under $(A,x)(B,y)=(AB, Ay+x)$. — *proved proved here* — `UndergradKB.AbstractAlgebra.EuclideanGroup`, `UndergradKB.AbstractAlgebra.EuclideanGroup.toIsometryHom`, `UndergradKB.AbstractAlgebra.EuclideanGroup.toIsometryHom_injective`, `UndergradKB.AbstractAlgebra.EuclideanGroup.toIsometryHom_surjective`
- **Example 12.1.10 (pdf p.165)**, p.165 [AA-178]: Elements of $O(2)$ are rotations (matrix with cos, sin) or reflections (determinant $-1$, squaring to identity). — *proved proved here* — `UndergradKB.AbstractAlgebra.orthogonal_two_rotation_or_reflection`
- **Definition (unnumbered, 12.2) (pdf p.166)**, p.166 [AA-181]: An isometry (rigid motion) of $\mathbb{R}^n$ is a distance-preserving map. — *in Mathlib* — `Isometry`, `IsometryEquiv`

#### Section 12.2

- **Lemma 12.2.2 (pdf p.166)**, p.166 [AA-182]: An isometry of $\mathbb{R}^2$ fixing the origin is linear, given by an element of $O(2)$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_2_2`, `UndergradKB.AbstractAlgebra.isometry_fixing_zero_orthogonal`, `UndergradKB.AbstractAlgebra.isometry_fixing_zero_orthogonal_two`
- **Definition (unnumbered, 12.2) (pdf p.167)**, p.167 [AA-184]: The symmetry group of a set $X \subset \mathbb{R}^n$ is the subgroup of isometries preserving $X$. — *proved proved here* — `UndergradKB.AbstractAlgebra.symmetryGroup`, `UndergradKB.AbstractAlgebra.mem_symmetryGroup_iff`
- **Theorem 12.2.3 (pdf p.167)**, p.167 [AA-183]: Isometries of $\mathbb{R}^2$ form the Euclidean group $E(2)$ (rotations, reflections, translations, glide reflections). — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_2_3`, `UndergradKB.AbstractAlgebra.Course.judson_12_2_3_euclidean_group`, `UndergradKB.AbstractAlgebra.isometry_iff_orthogonal_add`, `UndergradKB.AbstractAlgebra.isometry_two_iff`
- **Theorem 12.2.4 (pdf p.167)**, p.167 [AA-185]: The only finite symmetry groups in $\mathbb{R}^2$ are cyclic $\mathbb{Z}_n$ and dihedral $D_n$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_2_4`, `UndergradKB.AbstractAlgebra.finite_subgroup_orthogonal_two`
- **Definition (unnumbered, 12.2.1) (pdf p.168)**, p.168 [AA-186]: The lattice generated by linearly independent $x,y$ is the set of integer combinations $mx+ny$, with $x,y$ a basis of it. — *proved proved here* — `UndergradKB.AbstractAlgebra.lattice2`, `UndergradKB.AbstractAlgebra.mem_lattice2`
- **Definition (unnumbered, 12.2.1) (pdf p.169)**, p.169 [AA-187]: Two bases of a lattice differ by a unimodular matrix (integer entries, determinant $\pm1$). — *proved proved here* — `UndergradKB.AbstractAlgebra.lattice2_basis_change`
- **Definition (unnumbered, 12.2.1) (pdf p.170)**, p.170 [AA-188]: Space group, translation subgroup and point group of a lattice pattern; $G/T \cong G_0$ where $T$ is the translation subgroup. — *proved proved here* — `UndergradKB.AbstractAlgebra.EuclideanGroup.rotHom`, `UndergradKB.AbstractAlgebra.EuclideanGroup.pointGroup`, `UndergradKB.AbstractAlgebra.EuclideanGroup.translationSubgroup`, `UndergradKB.AbstractAlgebra.EuclideanGroup.mem_translationSubgroup_iff`
- **Theorem 12.2.8 (pdf p.170)**, p.170 [AA-189]: Every translation group in $\mathbb{R}^2$ is isomorphic to $\mathbb{Z}\times\mathbb{Z}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_2_8`, `UndergradKB.AbstractAlgebra.lattice2_addEquiv`
- **Theorem 12.2.9 (pdf p.170)**, p.170 [AA-190]: The point group of a wallpaper group is isomorphic to $\mathbb{Z}_n$ or $D_n$ with $n \in \{1,2,3,4,6\}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_12_2_9`, `UndergradKB.AbstractAlgebra.Course.judson_12_2_9_int_matrix`, `UndergradKB.AbstractAlgebra.orderOf_int_matrix_two`, `UndergradKB.AbstractAlgebra.crystallographic_restriction`
- **Theorem 12.2.12 (pdf p.171)**, p.171 [AA-191]: There are exactly 17 wallpaper groups. — *not formalized* — `UndergradKB.AbstractAlgebra.point_group_crystallographic`
- **Definition (unnumbered) generated subgroup / finitely generated (pdf p.176)**, p.176 [AA-192]: The subgroup generated by a set of elements is the smallest subgroup containing it; a group is finitely generated if a finite set generates it. — *in Mathlib* — `Subgroup.closure`, `Subgroup.FG`, `Group.FG`

## Chapter 13

16 items; 16 with a Lean name; 6 proved proved here; 10 in Mathlib.


#### Section 13.1

- **Proposition 13.1.3 (pdf p.177)**, p.177 [AA-193]: The subgroup generated by $\{g_i\}$ consists exactly of the finite products of integer powers of the $g_i$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_3`, `UndergradKB.AbstractAlgebra.mem_closure_iff_exists_list`
- **Theorem 13.1.4 (pdf p.177)**, p.177 [AA-199]: Fundamental theorem of finite abelian groups: every finite abelian group is isomorphic to a product of cyclic groups $\mathbb{Z}_{p_i^{\alpha_i}}$ of prime-power order. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_4`, `CommGroup.equiv_prod_multiplicative_zmod_of_finite`, `AddCommGroup.equiv_directSum_zmod_of_finite`
- **Definition (unnumbered) p-group (pdf p.177)**, p.177 [AA-194]: A $p$-group is a group in which every element has order a power of $p$ (a $p$-subgroup is a subgroup that is a $p$-group). — *in Mathlib* — `IsPGroup`, `IsPGroup.iff_orderOf`
- **Lemma 13.1.6 (pdf p.178)**, p.178 [AA-195]: Cauchy: a finite group (in the abelian case, Lemma 13.1.6) has an element of order $p$ for each prime $p$ dividing its order. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_6`, `UndergradKB.AbstractAlgebra.Course.judson_15_1_1`, `exists_prime_orderOf_dvd_card`, `exists_prime_orderOf_dvd_card'`
- **Lemma 13.1.7 (pdf p.178)**, p.178 [AA-196]: A finite group is a $p$-group if and only if its order is a power of $p$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_7`, `UndergradKB.AbstractAlgebra.Course.judson_15_1_2`, `IsPGroup.iff_card`, `IsPGroup.of_card`
- **Lemma 13.1.8 (pdf p.178)**, p.178 [AA-197]: A finite abelian group is the internal direct product of its subgroups of elements of $p_i$-power order, one for each prime $p_i$ dividing its order. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_8`, `UndergradKB.AbstractAlgebra.Course.judson_13_1_8_prod`, `UndergradKB.AbstractAlgebra.abelian_internal_direct_product_primary`, `UndergradKB.AbstractAlgebra.abelianPrimaryEquiv`
- **Lemma 13.1.9 (pdf p.179)**, p.179 [AA-198]: A finite abelian $p$-group splits as the product of a cyclic subgroup generated by an element of maximal order and a complementary subgroup. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_9`, `UndergradKB.AbstractAlgebra.exists_complement_of_max_order`
- **Theorem 13.1.10 (pdf p.180)**, p.180 [AA-200]: Fundamental theorem of finitely generated abelian groups: such a group is a product of finite cyclic groups of prime-power order and copies of $\mathbb{Z}$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_10`, `AddCommGroup.equiv_free_prod_directSum_zmod`, `CommGroup.equiv_free_prod_prod_multiplicative_zmod`
- **Definition (unnumbered) subnormal series / normal series / length / refinement / isomorph…**, p.180 [AA-201]: Subnormal series and normal series of a group, their length, refinements, and isomorphism of series. — *proved proved here* — `UndergradKB.AbstractAlgebra.SubnormalSeries`, `UndergradKB.AbstractAlgebra.SubnormalSeries.IsSeriesOfGroup`, `UndergradKB.AbstractAlgebra.SubnormalSeries.IsNormalSeries`, `UndergradKB.AbstractAlgebra.SubnormalSeries.IsRefinedBy`

#### Section 13.2

- **Example 13.2.6 (pdf p.181)**, p.181 [AA-205]: $S_n$ is solvable for $n \le 4$ and not solvable for $n \ge 5$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_2_9_solvable`, `UndergradKB.AbstractAlgebra.Course.judson_13_2_9_not_solvable`, `Equiv.Perm.isSolvable`, `Equiv.Perm.not_isSolvable`
- **Definition (unnumbered) composition series / principal series (pdf p.181)**, p.181 [AA-202]: A composition series is a subnormal series with simple factors; a principal series is a normal series with simple factors. — *proved proved here* — `UndergradKB.AbstractAlgebra.isMaxNormalIn_iff_isSimpleGroup`, `UndergradKB.AbstractAlgebra.SubnormalSeries.IsCompositionSeries`, `UndergradKB.AbstractAlgebra.SubnormalSeries.IsPrincipalSeries`
- **Theorem 13.2.8 (pdf p.182)**, p.182 [AA-203]: Jordan-Holder theorem: any two composition series of a group are equivalent (same factors up to isomorphism and order). — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_13_2_8`, `UndergradKB.AbstractAlgebra.jordan_holder_subgroups`, `UndergradKB.AbstractAlgebra.jordan_holder_group`
- **Example 13.2.9 (pdf p.183)**, p.183 [AA-205]: $S_n$ is solvable for $n \le 4$ and not solvable for $n \ge 5$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_2_9_solvable`, `UndergradKB.AbstractAlgebra.Course.judson_13_2_9_not_solvable`, `Equiv.Perm.isSolvable`, `Equiv.Perm.not_isSolvable`
- **Definition (unnumbered) solvable group (pdf p.183)**, p.183 [AA-204]: A group is solvable if it has a subnormal series with abelian factor groups. — *in Mathlib* — `Group.IsSolvable`, `Subgroup.derivedSeries`
- **Definition (unnumbered) derived series (pdf p.185)**, p.185 [AA-206]: The commutator subgroup $G'$ is generated by the commutators $aba^{-1}b^{-1}$; the derived series is $G^{(i+1)}=(G^{(i)})'$. — *in Mathlib* — `commutator`, `commutator_eq_closure`, `Subgroup.derivedSeries`, `Subgroup.derivedSeries_succ`
- **Definition (unnumbered) group action / G-set (pdf p.186)**, p.186 [AA-208]: A (left) action of a group on a set satisfies $ex=x$ and $(g_1g_2)x=g_1(g_2x)$; the set is a $G$-set. — *in Mathlib* — `MulAction`

## Chapter 14

18 items; 18 with a Lean name; 3 proved proved here; 15 in Mathlib.


#### Section 14.1

- **Example 14.1.5 (pdf p.187)**, p.187 [AA-209]: Standard actions: left multiplication of a subgroup on $G$, conjugation of a subgroup on $G$, and $G$ acting on left cosets $G/H$ by $g\cdot xH=gxH$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_5`, `MulAction.isPretransitive_quotient`, `ConjAct`, `MulAut.conj`
- **Proposition 14.1.6 (pdf p.187)**, p.187 [AA-210]: $G$-equivalence ($gx=y$ for some $g$) is an equivalence relation on a $G$-set. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_6`, `MulAction.orbitRel`
- **Definition (unnumbered) orbit (pdf p.187)**, p.187 [AA-211]: The orbit of $x$ is its $G$-equivalence class; orbits partition $X$. — *in Mathlib* — `MulAction.orbit`, `MulAction.mem_orbit_iff`, `MulAction.orbitRel.Quotient`
- **Definition (unnumbered) fixed point set / stabilizer (pdf p.187-188)**, p.187 [AA-212]: The fixed point set $X_g$ of an element and the stabilizer (isotropy) subgroup $G_x$ of a point. — *in Mathlib* — `MulAction.fixedBy`, `MulAction.fixedPoints`, `MulAction.stabilizer`
- **Proposition 14.1.10 (pdf p.188)**, p.188 [AA-213]: The stabilizer $G_x$ of a point is a subgroup of $G$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_10`, `MulAction.stabilizer`, `MulAction.mem_stabilizer_iff`
- **Theorem 14.1.11 (pdf p.188)**, p.188 [AA-214]: Orbit-stabilizer theorem: the orbit of $x$ has size $[G:G_x]$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_11`, `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, `MulAction.orbitEquivQuotientStabilizer`, `MulAction.index_stabilizer`

#### Section 14.2

- **Discussion before Example 14.2.1 (pdf p.188-189)**, p.188 [AA-217]: Orbit decomposition: for a finite $G$-set, $\lvert X\rvert$ is the sum over orbit representatives of $[G:G_{x_i}]$ (equivalently $\lvert X_G\rvert$ plus the sizes of nontrivial orbits). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_2_orbit_decomposition`, `MulAction.card_eq_sum_card_group_div_card_stabilizer`, `MulAction.card_eq_sum_card_group_div_card_stabilizer'`
- **Example 14.2.3 (pdf p.189)**, p.189 [AA-219]: Two permutations in $S_n$ are conjugate iff they have the same cycle type (so classes correspond to partitions of $n$). — *proved proved here* — `UndergradKB.AbstractAlgebra.card_conjClasses_perm`
- **Definition (unnumbered) center / conjugacy class / centralizer subgroup (pdf p.189)**, p.189 [AA-216]: Center $Z(G)$, conjugacy classes (orbits under conjugation) and centralizer of an element. — *in Mathlib* — `Subgroup.center`, `ConjClasses`, `Subgroup.centralizer`, `IsConj`
- **Theorem (unnumbered) class equation (pdf p.189)**, p.189 [AA-218]: Class equation: $\lvert G\rvert=\lvert Z(G)\rvert+\sum [G:C(x_i)]$ over nontrivial conjugacy classes; each class size divides $\lvert G\rvert$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_2_class_equation`, `UndergradKB.AbstractAlgebra.Course.judson_14_2_class_size_dvd`, `Group.nat_card_center_add_sum_card_noncenter_eq_card`, `Group.card_center_add_sum_card_noncenter_eq_card`
- **Theorem 14.2.4 (pdf p.190)**, p.190 [AA-220]: A group of order $p^n$ ($n \ge 1$) has a nontrivial center. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_2_4`, `IsPGroup.center_nontrivial`, `IsPGroup.bot_lt_center`
- **Corollary 14.2.5 (pdf p.190)**, p.190 [AA-221]: A group of order $p^2$ is abelian. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_2_5`, `IsPGroup.commutative_of_card_eq_prime_sq`

#### Section 14.3

- **Lemma 14.3.2 (pdf p.191)**, p.191 [AA-215]: Equivalent points have conjugate (hence isomorphic) stabilizers: $G_{gx}=gG_xg^{-1}$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_3_2`, `MulAction.stabilizer_smul_eq_stabilizer_map_conj`
- **Theorem 14.3.3 (pdf p.191)**, p.191 [AA-222]: Burnside's counting theorem: the number of orbits equals the average number of fixed points $\frac1{\lvert G\rvert}\sum_g \lvert X_g\rvert$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_3_3`, `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
- **Proposition 14.3.5 (pdf p.193)**, p.193 [AA-223]: A permutation group on $X$ induces a permutation group on colorings $X \to Y$ by $f \mapsto f\circ\sigma$, and $\sigma$ fixes $\lvert Y\rvert^{c}$ colorings where $c$ is its number of cycles. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_14_3_5`, `UndergradKB.AbstractAlgebra.card_fixed_colorings`
- **Definition (unnumbered) switching function / equivalent switching functions (pdf p.194)**, p.194 [AA-224]: A switching (Boolean) function of $n$ variables is a map $\mathbb{Z}_2^n \to \mathbb{Z}_2$; there are $2^{2^n}$ of them, and two are equivalent if one is obtained from the other by permuting the variables. — *proved proved here* — `UndergradKB.AbstractAlgebra.SwitchingFunction`, `UndergradKB.AbstractAlgebra.card_switchingFunction`, `UndergradKB.AbstractAlgebra.SwitchingFunction.equivalent_iff`

#### Section 14.1

- **Example 14.1.3** [AA-209]: Standard actions: left multiplication of a subgroup on $G$, conjugation of a subgroup on $G$, and $G$ acting on left cosets $G/H$ by $g\cdot xH=gxH$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_5`, `MulAction.isPretransitive_quotient`, `ConjAct`, `MulAut.conj`
- **Example 14.1.4** [AA-209]: Standard actions: left multiplication of a subgroup on $G$, conjugation of a subgroup on $G$, and $G$ acting on left cosets $G/H$ by $g\cdot xH=gxH$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_14_1_5`, `MulAction.isPretransitive_quotient`, `ConjAct`, `MulAut.conj`

## Chapter 15

18 items; 17 with a Lean name; 3 proved proved here; 14 in Mathlib; 1 not formalized.


#### Section 15.1

- **Theorem 15.1.1 (pdf p.200)**, p.200 [AA-195]: Cauchy: a finite group (in the abelian case, Lemma 13.1.6) has an element of order $p$ for each prime $p$ dividing its order. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_6`, `UndergradKB.AbstractAlgebra.Course.judson_15_1_1`, `exists_prime_orderOf_dvd_card`, `exists_prime_orderOf_dvd_card'`
- **Definition (unnumbered) p-subgroup (pdf p.200)**, p.200 [AA-194]: A $p$-group is a group in which every element has order a power of $p$ (a $p$-subgroup is a subgroup that is a $p$-group). — *in Mathlib* — `IsPGroup`, `IsPGroup.iff_orderOf`
- **Corollary 15.1.2 (pdf p.201)**, p.201 [AA-196]: A finite group is a $p$-group if and only if its order is a power of $p$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_13_1_7`, `UndergradKB.AbstractAlgebra.Course.judson_15_1_2`, `IsPGroup.iff_card`, `IsPGroup.of_card`
- **Theorem 15.1.4 (pdf p.201)**, p.201 [AA-227]: First Sylow theorem: if $p^r$ divides $\lvert G\rvert$ then $G$ has a subgroup of order $p^r$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_1_4`, `Sylow.exists_subgroup_card_pow_prime`, `Sylow.exists_subgroup_card_pow_succ`
- **Definition (unnumbered) Sylow p-subgroup (pdf p.201)**, p.201 [AA-225]: A Sylow $p$-subgroup is a maximal $p$-subgroup. — *in Mathlib* — `Sylow`, `Sylow.nonempty`
- **Definition (unnumbered) normalizer (pdf p.201)**, p.201 [AA-226]: The normalizer $N(H)=\{g: gHg^{-1}=H\}$ is a subgroup and the largest subgroup in which $H$ is normal. — *in Mathlib* — `Subgroup.normalizer`, `Subgroup.le_normalizer`, `Subgroup.normalizer_eq_top_iff`
- **Lemma 15.1.5 (pdf p.202)**, p.202 [AA-228]: If a $p$-element $x$ normalizes a Sylow $p$-subgroup $P$, then $x \in P$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_1_5`, `IsPGroup.inf_normalizer_sylow`, `IsPGroup.sylow_mem_fixedPoints_iff`
- **Lemma 15.1.6 (pdf p.202)**, p.202 [AA-229]: The number of $H$-conjugates of $K$ is $[H : N(K)\cap H]$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_15_1_6`, `UndergradKB.AbstractAlgebra.card_conjugates`
- **Theorem 15.1.7 (pdf p.202)**, p.202 [AA-230]: Second Sylow theorem: all Sylow $p$-subgroups are conjugate. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_1_7`, `Sylow.isPretransitive_of_finite`, `MulAction.exists_smul_eq`
- **Theorem 15.1.8 (pdf p.202)**, p.202 [AA-231]: Third Sylow theorem: the number of Sylow $p$-subgroups is $\equiv 1 \pmod p$ and divides $\lvert G\rvert$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_1_8`, `card_sylow_modEq_one`, `Sylow.card_dvd_index`, `Sylow.card_eq_index_normalizer`

#### Section 15.2

- **Theorem 15.2.2 (pdf p.203)**, p.203 [AA-232]: If $p<q$ are primes, every group of order $pq$ has a normal subgroup of order $q$ (so is not simple), and is cyclic when $q \not\equiv 1 \pmod p$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_15_2_2`, `UndergradKB.AbstractAlgebra.Course.judson_15_2_2_cyclic`, `UndergradKB.AbstractAlgebra.exists_normal_subgroup_card_of_card_eq_mul_primes`, `UndergradKB.AbstractAlgebra.isCyclic_of_card_eq_mul_primes`
- **Theorem 15.2.5 (pdf p.204)**, p.204 [AA-207]: The commutator subgroup $G'$ is normal in $G$ and $G/G'$ is abelian. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_2_5`, `Subgroup.commutator_normal`, `commutator_def`, `Abelianization`
- **Example 15.2.8 (pdf p.204)**, p.204 [AA-233]: A finite $p$-group of order $p^n$ with $n>1$ is not simple (a simple $p$-group has order $p$). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_15_2_8`, `IsPGroup.isSimpleGroup_iff_card_eq`, `IsPGroup.center_nontrivial`
- **Definition (unnumbered) commutator subgroup (pdf p.185, p.204)**, p.204 [AA-206]: The commutator subgroup $G'$ is generated by the commutators $aba^{-1}b^{-1}$; the derived series is $G^{(i+1)}=(G^{(i)})'$. — *in Mathlib* — `commutator`, `commutator_eq_closure`, `Subgroup.derivedSeries`, `Subgroup.derivedSeries_succ`
- **Lemma 15.2.10 (pdf p.205)**, p.205 [AA-234]: For finite subgroups $H,K$: $\lvert HK\rvert = \lvert H\rvert\lvert K\rvert / \lvert H\cap K\rvert$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_15_2_10`, `UndergradKB.AbstractAlgebra.card_mul_set_mul_card_inf`
- **Theorem 15.2.12 (pdf p.206)**, p.206 [AA-235]: Feit-Thompson odd order theorem: every finite simple group of non-prime order has even order. — *not formalized* — –
- **Definition (unnumbered) ring (pdf p.210)**, p.210 [AA-236]: A ring is an abelian group under + with an associative multiplication distributing over + on both sides. — *in Mathlib* — `Ring`, `CommRing`, `Semiring`, `NonUnitalRing`
- **Definition (unnumbered) ring with unity, commutative ring (pdf p.210)**, p.210 [AA-237]: A ring with unity has $1 \neq 0$ with $1a = a1 = a$; a commutative ring has $ab = ba$ throughout. — *in Mathlib* — `Ring`, `CommRing`, `Nontrivial`

## Chapter 16

41 items; 41 with a Lean name; 8 proved proved here; 33 in Mathlib.


#### Section 16.1

- **Example 16.1.7 (pdf p.211)**, p.211 [AA-242]: The quaternions $a+bi+cj+dk$ with real coefficients form a noncommutative division ring (inverse via the conjugate and $a^2+b^2+c^2+d^2$). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_1_7`, `Quaternion`, `QuaternionAlgebra`, `instDivisionRing`
- **Proposition 16.1.8 (pdf p.212)**, p.212 [AA-243]: In any ring, $a0 = 0a = 0$, $a(-b) = (-a)b = -ab$ and $(-a)(-b) = ab$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_1_8`, `mul_zero`, `zero_mul`, `mul_neg`
- **Proposition 16.1.10 (pdf p.213)**, p.213 [AA-245]: A subset is a subring iff it is nonempty and closed under products and differences. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_1_10`, `UndergradKB.AbstractAlgebra.Course.judson_16_1_10_unital`, `UndergradKB.AbstractAlgebra.exists_subring_iff`, `UndergradKB.AbstractAlgebra.exists_nonUnitalSubring_iff`
- **Definition (unnumbered) zero divisor (pdf p.211, pdf p.213)**, p.213 [AA-238]: A nonzero element $a$ of a commutative ring is a zero divisor if $ab = 0$ for some nonzero $b$. — *proved proved here* — `UndergradKB.AbstractAlgebra.isDomain_iff_no_zero_divisors`
- **Definition (unnumbered) integral domain (pdf p.210, pdf p.213)**, p.213 [AA-239]: An integral domain is a commutative ring with $1 \neq 0$ and no zero divisors. — *in Mathlib* — `IsDomain`, `NoZeroDivisors`
- **Definition (unnumbered) unit (pdf p.213)**, p.213 [AA-240]: A unit of a ring with identity is an element having a multiplicative inverse. — *in Mathlib* — `IsUnit`, `Units`
- **Definition (unnumbered) subring (pdf p.213)**, p.213 [AA-244]: A subring is a subset that is itself a ring under the inherited operations. — *in Mathlib* — `Subring`

#### Section 16.2

- **Example 16.2.1 (pdf p.214)**, p.214 [AA-252]: The Gaussian integers $\mathbb{Z}[i]$ form an integral domain that is not a field, with units $\pm 1, \pm i$. — *proved proved here* — `UndergradKB.AbstractAlgebra.gaussianInt_isUnit_iff`, `UndergradKB.AbstractAlgebra.gaussianInt_isDomain_not_field`
- **Proposition 16.2.4 (pdf p.214)**, p.214 [AA-246]: A commutative ring with identity is an integral domain iff nonzero elements can be cancelled in products. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_2_4`, `IsDomain`, `IsCancelMulZero`, `IsLeftCancelMulZero`
- **Theorem 16.2.5 (pdf p.214)**, p.214 [AA-247]: Every finite integral domain is a field. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_2_5`, `Finite.isField_of_domain`, `Fintype.fieldOfDomain`, `Finite.isDomain_to_isField`
- **Definition (unnumbered) division ring, field (pdf p.211, pdf p.213, pdf p.214)**, p.214 [AA-241]: A division ring is a ring with identity in which every nonzero element is a unit; a commutative division ring is a field. — *in Mathlib* — `DivisionRing`, `Field`, `IsField`
- **Definition (unnumbered) characteristic (pdf p.214)**, p.214 [AA-248]: The characteristic of a ring is the least positive $n$ with $nr = 0$ for all $r$, or 0 if none exists. — *in Mathlib* — `CharP`, `ringChar`
- **Example 16.2.6 (pdf p.215)**, p.215 [AA-251]: For a prime $p$, $\mathbb{Z}_p$ is a field of characteristic $p$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_2_6`, `ZMod.charP`, `ringChar_zmod_n`
- **Lemma 16.2.7 (pdf p.215)**, p.215 [AA-249]: In a ring with identity, the characteristic equals the additive order of 1. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_2_7`, `ringChar`
- **Theorem 16.2.8 (pdf p.215)**, p.215 [AA-250]: The characteristic of an integral domain is a prime or 0. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_2_8`, `CharP.char_is_prime_or_zero`

#### Section 16.3

- **Example 16.3.1 (pdf p.215)**, p.215 [AA-255]: Reduction mod $n$ is a ring homomorphism $\mathbb{Z} \to \mathbb{Z}_n$ with kernel $n\mathbb{Z}$ and $\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}_n$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_1`, `Int.castRingHom`, `Int.quotientSpanNatEquivZMod`, `ZMod.charP`
- **Definition (unnumbered) ring homomorphism, isomorphism, kernel (pdf p.215)**, p.215 [AA-253]: A ring homomorphism preserves + and products; it is an isomorphism if bijective; its kernel is the preimage of 0. — *in Mathlib* — `RingHom`, `RingEquiv`, `RingHom.ker`
- **Proposition 16.3.3 (pdf p.216)**, p.216 [AA-254]: A ring homomorphism sends 0 to 0, sends 1 to 1 when onto, has commutative image from a commutative ring, and has field image from a field when nonzero. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_3_zero_one`, `UndergradKB.AbstractAlgebra.Course.judson_16_3_3`, `UndergradKB.AbstractAlgebra.Course.judson_16_3_3_field`, `UndergradKB.AbstractAlgebra.range_mul_comm`
- **Example 16.3.4 (pdf p.216)**, p.216 [AA-257]: An ideal of a ring with identity containing a unit (in particular 1) is the whole ring. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_4`, `Ideal.eq_top_of_isUnit_mem`, `Ideal.eq_top_iff_one`, `Ideal.span_singleton_eq_top`
- **Example 16.3.5 (pdf p.216)**, p.216 [AA-258]: In a commutative ring with identity, $\langle a \rangle = \{ar\}$ is an ideal, called principal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_5`, `Ideal.span`, `Ideal.mem_span_singleton`, `Submodule.IsPrincipal`
- **Theorem 16.3.6 (pdf p.216)**, p.216 [AA-259]: Every ideal of $\mathbb{Z}$ is principal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_6`, `IsPrincipalIdealRing`
- **Example 16.3.7 (pdf p.217)**, p.217 [AA-259]: Every ideal of $\mathbb{Z}$ is principal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_6`, `IsPrincipalIdealRing`
- **Proposition 16.3.8 (pdf p.217)**, p.217 [AA-260]: The kernel of a ring homomorphism is an ideal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_8`, `RingHom.ker`
- **Remark 16.3.9 (pdf p.216, pdf p.217)**, p.217 [AA-256]: An ideal is a subring absorbing multiplication by arbitrary ring elements on both sides (one-sided versions give left and right ideals). — *in Mathlib* — `Ideal`, `Ideal.IsTwoSided`, `Submodule`
- **Theorem 16.3.10 (pdf p.217)**, p.217 [AA-261]: For an ideal $I$, $R/I$ is a ring and $r \mapsto r+I$ is a surjective ring homomorphism with kernel $I$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_10`, `Ideal.Quotient.mk`, `Ideal.Quotient.eq`
- **Theorem 16.3.11 (pdf p.217)**, p.217 [AA-261]: For an ideal $I$, $R/I$ is a ring and $r \mapsto r+I$ is a surjective ring homomorphism with kernel $I$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_10`, `Ideal.Quotient.mk`, `Ideal.Quotient.eq`
- **Theorem 16.3.12 (pdf p.218)**, p.218 [AA-262]: First isomorphism theorem for rings: $R/\ker\psi \cong \psi(R)$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_12`, `RingHom.quotientKerEquivRange`, `RingHom.quotientKerEquivOfSurjective`, `RingHom.kerLift`
- **Theorem 16.3.13 (pdf p.218)**, p.218 [AA-263]: Second isomorphism theorem for rings: $I/(I\cap J) \cong (I+J)/J$ for a subring $I$ and an ideal $J$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_13`, `UndergradKB.AbstractAlgebra.second_isomorphism_theorem`
- **Theorem 16.3.14 (pdf p.218)**, p.218 [AA-264]: Third isomorphism theorem for rings: $R/I \cong (R/J)/(I/J)$ for ideals $J \subseteq I$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_14`
- **Theorem 16.3.15 (pdf p.218)**, p.218 [AA-265]: Correspondence theorem: subrings (ideals) containing $I$ correspond bijectively to subrings (ideals) of $R/I$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_3_15`, `UndergradKB.AbstractAlgebra.idealQuotientOrderIso`

#### Section 16.4

- **Theorem 16.4.1 (pdf p.218)**, p.218 [AA-267]: For commutative $R$ with 1, $M$ is maximal iff $R/M$ is a field. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_1`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient`
- **Definition (unnumbered) maximal ideal (pdf p.218)**, p.218 [AA-266]: A maximal ideal is a proper ideal contained in no other proper ideal. — *in Mathlib* — `Ideal.IsMaximal`, `Ideal.isMaximal_iff`
- **Example 16.4.2 (pdf p.219)**, p.219 [AA-267]: For commutative $R$ with 1, $M$ is maximal iff $R/M$ is a field. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_1`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient`
- **Example 16.4.2 (pdf p.219)**, p.219 [AA-271]: The ideal $p\mathbb{Z}$ is maximal for prime $p$ and these are the nonzero prime ideals of $\mathbb{Z}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_5`, `UndergradKB.AbstractAlgebra.int_ideal_isPrime_ne_bot_iff`, `UndergradKB.AbstractAlgebra.int_span_isMaximal`
- **Proposition 16.4.4 (pdf p.219)**, p.219 [AA-269]: For commutative $R$ with $1 \neq 0$, $P$ is prime iff $R/P$ is an integral domain. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_4`, `Ideal.Quotient.isDomain_iff_prime`
- **Example 16.4.5 (pdf p.219)**, p.219 [AA-271]: The ideal $p\mathbb{Z}$ is maximal for prime $p$ and these are the nonzero prime ideals of $\mathbb{Z}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_5`, `UndergradKB.AbstractAlgebra.int_ideal_isPrime_ne_bot_iff`, `UndergradKB.AbstractAlgebra.int_span_isMaximal`
- **Corollary 16.4.6 (pdf p.219)**, p.219 [AA-270]: Every maximal ideal of a commutative ring with identity is prime. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_4_6`, `Ideal.IsMaximal.isPrime`
- **Definition (unnumbered) prime ideal (pdf p.219)**, p.219 [AA-268]: A prime ideal is a proper ideal $P$ with $ab \in P$ implying $a \in P$ or $b \in P$. — *in Mathlib* — `Ideal.IsPrime`, `Ideal.IsPrime.mem_or_mem`

#### Section 16.5

- **Lemma 16.5.1 (pdf p.220)**, p.220 [AA-272]: For coprime $m,n$ the system $x \equiv a \pmod m$, $x \equiv b \pmod n$ has a solution unique mod $mn$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_5_1`, `Nat.chineseRemainder`, `Nat.chineseRemainder_modEq_unique`, `ZMod.chineseRemainder`
- **Theorem 16.5.3 (pdf p.221)**, p.221 [AA-273]: Chinese Remainder Theorem: pairwise coprime moduli give a solvable system, unique mod the product. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_5_3`, `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfList_modEq_unique`, `Nat.chineseRemainderOfFinset`
- **Example 16.5.5 (pdf p.223)**, p.223 [AA-274]: Arithmetic on large integers can be done componentwise modulo pairwise coprime moduli and recombined by the Chinese Remainder Theorem. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_16_5_5`, `ZMod.chineseRemainder`, `ZMod.prodEquivPi`

## Chapter 17

20 items; 20 with a Lean name; 8 proved proved here; 12 in Mathlib.


#### Section 17.1

- **Example 17.1.2 (pdf p.231)**, p.231 [AA-278]: Over an integral domain, $\deg(pq) = \deg p + \deg q$ and $R[x]$ is an integral domain. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_1_4`, `Polynomial.degree_mul`, `Polynomial.natDegree_mul`
- **Definition (unnumbered) polynomial over R (pdf p.230, pdf p.231)**, p.231 [AA-275]: Polynomials over a ring $R$ in an indeterminate $x$, with sum and convolution product, form the set $R[x]$. — *in Mathlib* — `Polynomial`, `Polynomial.X`, `Polynomial.C`
- **Definition (unnumbered) leading coefficient, monic, degree (pdf p.230, pdf p.231)**, p.231 [AA-276]: Coefficients, leading coefficient, monic polynomial, degree (with $\deg 0 = -\infty$). — *in Mathlib* — `Polynomial.leadingCoeff`, `Polynomial.Monic`, `Polynomial.degree`, `Polynomial.natDegree`
- **Theorem 17.1.3 (pdf p.232)**, p.232 [AA-277]: For commutative $R$ with identity, $R[x]$ is a commutative ring with identity. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_1_3`, `Polynomial`
- **Proposition 17.1.4 (pdf p.232)**, p.232 [AA-278]: Over an integral domain, $\deg(pq) = \deg p + \deg q$ and $R[x]$ is an integral domain. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_1_4`, `Polynomial.degree_mul`, `Polynomial.natDegree_mul`
- **Theorem 17.1.5 (pdf p.233)**, p.233 [AA-280]: Evaluation at $\alpha \in R$ is a ring homomorphism $R[x] \to R$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_1_5`, `Polynomial.evalRingHom`, `Polynomial.eval_mul`, `Polynomial.eval₂RingHom`

#### Section 17.2

- **Theorem 17.2.1 (pdf p.233)**, p.233 [AA-281]: Division algorithm in $F[x]$: for $g \neq 0$ there are unique $q, r$ with $f = gq + r$ and $\deg r < \deg g$ or $r = 0$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_17_2_1`, `UndergradKB.AbstractAlgebra.division_algorithm_unique`, `UndergradKB.AbstractAlgebra.division_algorithm_exists`
- **Definition (unnumbered) polynomial ring in two or more indeterminates (pdf p.233)**, p.233 [AA-279]: Polynomials in several indeterminates: $R[x,y] \cong (R[x])[y]$, and $R[x_1,\dots,x_n]$ is defined similarly. — *proved proved here* — `UndergradKB.AbstractAlgebra.mvPolynomialFinTwoEquiv`
- **Corollary 17.2.3 (pdf p.235)**, p.235 [AA-282]: $\alpha$ is a zero (root) of $p$ iff $x - \alpha$ divides $p$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_2_3`, `Polynomial.IsRoot`, `Polynomial.dvd_iff_isRoot`, `Polynomial.mul_divByMonic_eq_iff_isRoot`
- **Corollary 17.2.4 (pdf p.235)**, p.235 [AA-283]: A nonzero polynomial of degree $n$ over a field has at most $n$ distinct zeros. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_2_4`, `Polynomial.card_roots'`, `Polynomial.card_roots`, `Polynomial.card_le_degree_of_subset_roots`
- **Proposition 17.2.5 (pdf p.235)**, p.235 [AA-285]: Bezout for polynomials over a field: $\gcd(p,q) = rp + sq$, and the gcd is unique. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_2_5`, `EuclideanDomain.gcd_eq_gcd_ab`, `Polynomial.instEuclideanDomain`
- **Definition (unnumbered) gcd of polynomials, relatively prime (pdf p.235)**, p.235 [AA-284]: The greatest common divisor of two polynomials over a field is the monic common divisor divisible by every common divisor; coprime means gcd 1. — *proved proved here* — `UndergradKB.AbstractAlgebra.exists_unique_monic_gcd`
- **Definition (unnumbered) irreducible polynomial (pdf p.236)**, p.236 [AA-286]: A nonconstant polynomial over a field is irreducible if it is not a product of two polynomials of smaller degree. — *in Mathlib* — `Irreducible`, `Polynomial.degree_pos_of_irreducible`, `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`

#### Section 17.3

- **Lemma 17.3.3 (pdf p.237)**, p.237 [AA-287]: A rational polynomial is $\frac{r}{s}$ times an integer polynomial with coprime coefficients, $\gcd(r,s)=1$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_3`, `UndergradKB.AbstractAlgebra.exists_primitive_smul_rat`
- **Theorem 17.3.4 (pdf p.237)**, p.237 [AA-288]: Gauss's Lemma: a monic integer polynomial that factors over $\mathbb{Q}$ into lower-degree factors factors into monic integer polynomials of the same degrees. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_4`, `UndergradKB.AbstractAlgebra.gauss_lemma_monic`
- **Corollary 17.3.5 (pdf p.238)**, p.238 [AA-289]: If a monic integer polynomial with nonzero constant term has a rational zero, then it has an integer zero dividing $a_0$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_5`, `isInteger_of_is_root_of_monic`, `num_dvd_of_is_root`, `den_dvd_of_is_root`
- **Theorem 17.3.7 (pdf p.238)**, p.238 [AA-290]: Eisenstein's Criterion: if a prime $p$ divides all coefficients but the leading one and $p^2 \nmid a_0$, the integer polynomial is irreducible over $\mathbb{Q}$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_7`, `UndergradKB.AbstractAlgebra.eisenstein_irreducible_rat`
- **Theorem 17.3.10 (pdf p.239)**, p.239 [AA-291]: If $F$ is a field, every ideal of $F[x]$ is principal. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_10`, `Polynomial.instEuclideanDomain`, `IsPrincipalIdealRing`
- **Example 17.3.11 (pdf p.239)**, p.239 [AA-292]: In $F[x,y]$ the ideal generated by $x$ and $y$ is not principal. — *proved proved here* — `UndergradKB.AbstractAlgebra.not_isPrincipal_span_X_X`
- **Theorem 17.3.12 (pdf p.239)**, p.239 [AA-293]: For a field $F$ and $p(x) \in F[x]$, the ideal $\langle p(x) \rangle$ is maximal iff $p(x)$ is irreducible. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_17_3_12`, `UndergradKB.AbstractAlgebra.span_singleton_isMaximal_iff_irreducible`

## Chapter 18

42 items; 42 with a Lean name; 7 proved proved here; 35 in Mathlib.


#### Section 18.1

- **Lemma 18.1.3 (pdf p.247-248)**, p.247 [AA-294]: For an integral domain $D$, pairs $(a,b)$ with $b\neq 0$ modulo $ad=bc$ form an equivalence relation, addition and multiplication of classes are well defined, and the result is a field (the field of fractions $F_D$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_3`, `IsFractionRing`, `FractionRing`, `FractionRing.field`
- **Theorem 18.1.4 (pdf p.248)**, p.248 [AA-295]: A domain $D$ embeds in a field of fractions in which every element is a quotient of two elements of $D$, and any injective ring map from $D$ into a field $E$ extends uniquely to $F_D\to E$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_4`, `IsFractionRing.injective`, `IsFractionRing.div_surjective`, `IsFractionRing.lift`
- **Definition field of fractions (pdf p.248)**, p.248 [AA-294]: For an integral domain $D$, pairs $(a,b)$ with $b\neq 0$ modulo $ad=bc$ form an equivalence relation, addition and multiplication of classes are well defined, and the result is a field (the field of fractions $F_D$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_3`, `IsFractionRing`, `FractionRing`, `FractionRing.field`
- **Example 18.1.5 (pdf p.249)**, p.249 [AA-296]: The field of fractions of $F[x]$ is the field of rational expressions $F(x)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_5`, `RatFunc`
- **Corollary 18.1.7 (pdf p.249)**, p.249 [AA-297]: A field of characteristic 0 contains a copy of $\mathbb{Q}$; a field of characteristic $p$ contains a copy of $\mathbb{Z}_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_6`, `UndergradKB.AbstractAlgebra.Course.judson_18_1_7`, `DivisionRing.toRatAlgebra`, `Rat.castHom`

#### Section 18.2

- **Example 18.2.1 (pdf p.249)**, p.249 [AA-301]: Irreducible need not be prime: in the subring of $\mathbb{Q}[x,y]$ generated by $x^2,y^2,xy$, the element $xy$ is irreducible but not prime — *proved proved here* — `UndergradKB.AbstractAlgebra.xy_irreducible_not_prime`
- **Definition divides/unit/associates (pdf p.249)**, p.249 [AA-298]: Divisibility $a\mid b$, units, and associates ($a=ub$ for a unit $u$) in a commutative ring — *in Mathlib* — `IsUnit`, `Associated`, `dvd_dvd_iff_associated`
- **Definition irreducible (pdf p.249)**, p.249 [AA-299]: A nonzero nonunit $p$ of a domain is irreducible if $p=ab$ forces $a$ or $b$ to be a unit — *in Mathlib* — `Irreducible`
- **Definition prime element (pdf p.249)**, p.249 [AA-300]: A prime element $p$ (nonzero nonunit) satisfies $p\mid ab\Rightarrow p\mid a$ or $p\mid b$ — *in Mathlib* — `Prime`, `Irreducible.prime`, `irreducible_iff_prime`
- **Definition UFD (pdf p.249-250)**, p.249 [AA-302]: Unique factorization domain: every nonzero nonunit is a product of irreducibles, uniquely up to order and associates — *in Mathlib* — `UniqueFactorizationMonoid`, `UniqueFactorizationMonoid.of_exists_prime_factors`, `UniqueFactorizationMonoid.factors`
- **Example 18.2.2 (pdf p.250)**, p.250 [AA-303]: $\mathbb{Z}$ is a UFD (fundamental theorem of arithmetic) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_2`, `Int.euclideanDomain`
- **Example 18.2.3 (pdf p.250)**, p.250 [AA-304]: $\mathbb{Z}[\sqrt{-3}]$ is a domain that is not a UFD ($4=2\cdot 2=(1-\sqrt{-3})(1+\sqrt{-3})$) — *proved proved here* — `UndergradKB.AbstractAlgebra.not_ufd_zsqrtd_neg_three`
- **Lemma 18.2.4 (pdf p.250)**, p.250 [AA-306]: In a domain, $a\mid b$ iff $\langle b\rangle\subseteq\langle a\rangle$; $a,b$ associates iff $\langle a\rangle=\langle b\rangle$; $a$ a unit iff $\langle a\rangle=D$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_4`, `Ideal.span_singleton_le_span_singleton`, `Ideal.span_singleton_eq_span_singleton`, `Ideal.span_singleton_eq_top`
- **Theorem 18.2.5 (pdf p.250)**, p.250 [AA-307]: In a PID, a nonzero principal ideal $\langle p\rangle$ is maximal iff $p$ is irreducible — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_5`, `PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.irreducible_iff_isMaximal_span_singleton`
- **Definition PID (pdf p.250)**, p.250 [AA-305]: Principal ideal domain: an integral domain in which every ideal is principal — *in Mathlib* — `IsPrincipalIdealRing`, `IsDomain`
- **Corollary 18.2.6 (pdf p.251)**, p.251 [AA-308]: In a PID, every irreducible element is prime — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_6`, `irreducible_iff_prime`, `Irreducible.prime`
- **Lemma 18.2.7 (pdf p.251)**, p.251 [AA-310]: In a PID every ascending chain of ideals stabilizes — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_7`, `monotone_stabilizes_iff_noetherian`
- **Theorem 18.2.8 (pdf p.251)**, p.251 [AA-311]: Every PID is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_8`
- **Definition ACC/Noetherian (pdf p.251)**, p.251 [AA-309]: Ascending chain condition on ideals (Noetherian ring): every increasing chain of ideals stabilizes — *in Mathlib* — `IsNoetherianRing`, `monotone_stabilizes_iff_noetherian`, `isNoetherianRing_iff_ideal_fg`
- **Example 18.2.10 (pdf p.252)**, p.252 [AA-313]: $\mathbb{Z}[x]$ is a UFD but not a PID (the ideal $(5,x)$ is not principal) — *proved proved here* — `UndergradKB.AbstractAlgebra.not_isPrincipal_span_five_X`, `UndergradKB.AbstractAlgebra.int_polynomial_ufd_not_pid`
- **Example 18.2.13 (pdf p.252-253)**, p.252 [AA-315]: $\mathbb{Z}$ (absolute value), $F[x]$ (degree) and the Gaussian integers $\mathbb{Z}[i]$ (norm $a^2+b^2$) are Euclidean domains — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_11`, `Int.euclideanDomain`, `Polynomial.instEuclideanDomain`
- **Corollary 18.2.23 (pdf p.252, 255)**, p.252 [AA-312]: If $F$ is a field then $F[x]$ is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_9`, `Polynomial.instEuclideanDomain`
- **Definition Euclidean domain (pdf p.252)**, p.252 [AA-314]: Euclidean domain: a domain with a division algorithm governed by a Euclidean valuation $\nu\colon D\setminus\{0\}\to\mathbb{N}_0$ with $\nu(a)\le\nu(ab)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.isEuclideanValuation_int`, `UndergradKB.AbstractAlgebra.isEuclideanValuation_polynomial`
- **Theorem 18.2.14 (pdf p.253)**, p.253 [AA-316]: Every Euclidean domain is a PID — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_14`
- **Corollary 18.2.15 (pdf p.253)**, p.253 [AA-317]: Every Euclidean domain is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_15`
- **Definition content/primitive (pdf p.253-254)**, p.253 [AA-318]: Content of a polynomial over a UFD is the gcd of its coefficients; a polynomial is primitive when its content is 1 — *in Mathlib* — `Polynomial.content`, `Polynomial.IsPrimitive`, `Polynomial.isPrimitive_primPart`, `Polynomial.content_eq_gcd_range_succ`
- **Theorem 18.2.17 (pdf p.254)**, p.254 [AA-319]: Gauss's lemma: a product of primitive polynomials over a UFD is primitive — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_17`, `Polynomial.IsPrimitive.mul`
- **Lemma 18.2.18 (pdf p.254)**, p.254 [AA-320]: The content of $p(x)q(x)$ is the product of the contents — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_18`, `Polynomial.content_mul`
- **Lemma 18.2.19 (pdf p.254)**, p.254 [AA-321]: If $p\in D[x]$ factors in $F[x]$ ($F$ the fraction field of a UFD $D$), it factors in $D[x]$ with the same degrees — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_19`, `UndergradKB.AbstractAlgebra.factor_of_map_ufd`
- **Corollary 18.2.20 (pdf p.254)**, p.254 [AA-322]: A primitive polynomial over a UFD is irreducible in $D[x]$ iff irreducible in $F[x]$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_20`, `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`
- **Corollary 18.2.21 (pdf p.254)**, p.254 [AA-323]: A monic $p\in D[x]$ factoring in $F[x]$ factors in $D[x]$ with matching degrees — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_21`, `UndergradKB.AbstractAlgebra.monic_factor_of_map_ufd`
- **Corollary 18.2.24 (pdf p.254-255)**, p.254 [AA-324]: If $D$ is a UFD then $D[x]$ is a UFD; in particular $\mathbb{Z}[x]$ is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_22`, `UndergradKB.AbstractAlgebra.Course.judson_18_2_24`
- **Corollary 18.2.25 (pdf p.255)**, p.255 [AA-325]: If $D$ is a UFD then $D[x_1,\dots,x_n]$ is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_25`
- **Remark 18.2.26 (pdf p.255)**, p.255 [AA-326]: Euclidean domain implies PID implies UFD, and neither converse holds — *proved proved here* — `UndergradKB.AbstractAlgebra.int_polynomial_ufd_not_pid`

#### Section 18.1

- **Lemma 18.1.1** [AA-294]: For an integral domain $D$, pairs $(a,b)$ with $b\neq 0$ modulo $ad=bc$ form an equivalence relation, addition and multiplication of classes are well defined, and the result is a field (the field of fractions $F_D$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_3`, `IsFractionRing`, `FractionRing`, `FractionRing.field`
- **Lemma 18.1.2** [AA-294]: For an integral domain $D$, pairs $(a,b)$ with $b\neq 0$ modulo $ad=bc$ form an equivalence relation, addition and multiplication of classes are well defined, and the result is a field (the field of fractions $F_D$) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_3`, `IsFractionRing`, `FractionRing`, `FractionRing.field`
- **Corollary 18.1.6** [AA-297]: A field of characteristic 0 contains a copy of $\mathbb{Q}$; a field of characteristic $p$ contains a copy of $\mathbb{Z}_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_1_6`, `UndergradKB.AbstractAlgebra.Course.judson_18_1_7`, `DivisionRing.toRatAlgebra`, `Rat.castHom`

#### Section 18.2

- **Corollary 18.2.9** [AA-312]: If $F$ is a field then $F[x]$ is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_9`, `Polynomial.instEuclideanDomain`
- **Example 18.2.11** [AA-315]: $\mathbb{Z}$ (absolute value), $F[x]$ (degree) and the Gaussian integers $\mathbb{Z}[i]$ (norm $a^2+b^2$) are Euclidean domains — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_11`, `Int.euclideanDomain`, `Polynomial.instEuclideanDomain`
- **Example 18.2.12** [AA-315]: $\mathbb{Z}$ (absolute value), $F[x]$ (degree) and the Gaussian integers $\mathbb{Z}[i]$ (norm $a^2+b^2$) are Euclidean domains — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_11`, `Int.euclideanDomain`, `Polynomial.instEuclideanDomain`
- **Example 18.2.16** [AA-318]: Content of a polynomial over a UFD is the gcd of its coefficients; a polynomial is primitive when its content is 1 — *in Mathlib* — `Polynomial.content`, `Polynomial.IsPrimitive`, `Polynomial.isPrimitive_primPart`, `Polynomial.content_eq_gcd_range_succ`
- **Theorem 18.2.22** [AA-324]: If $D$ is a UFD then $D[x]$ is a UFD; in particular $\mathbb{Z}[x]$ is a UFD — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_18_2_22`, `UndergradKB.AbstractAlgebra.Course.judson_18_2_24`

## Chapter 19

43 items; 43 with a Lean name; 12 proved proved here; 31 in Mathlib.


#### Section 19.1

- **Example 19.1.2 (pdf p.260)**, p.260 [AA-328]: The power set $P(X)$ ordered by inclusion is a poset (and in fact a lattice and Boolean algebra) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_10`, `Set.instBooleanAlgebra`, `Set.instCompleteAtomicBooleanAlgebra`
- **Definition partial order/poset (pdf p.260)**, p.260 [AA-327]: A partial order is a reflexive, antisymmetric, transitive relation; a set with one is a poset — *in Mathlib* — `PartialOrder`
- **Example 19.1.5 (pdf p.261)**, p.261 [AA-330]: Divisibility is a partial order on the natural numbers — *proved proved here* — `UndergradKB.AbstractAlgebra.nat_dvd_partial_order_axioms`, `UndergradKB.AbstractAlgebra.NatDvd.le_iff`, `UndergradKB.AbstractAlgebra.associates_nat_le_iff`
- **Example 19.1.11 (pdf p.261-262)**, p.261 [AA-329]: The subgroups of a group form a poset under inclusion, indeed a lattice with meet $H\cap K$ and join the subgroup generated by $H\cup K$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_11`, `Subgroup.sup_eq_closure`, `Subgroup.closure_union`
- **Definition bounds (pdf p.261-262)**, p.261 [AA-331]: Upper bound, least upper bound (supremum), lower bound, greatest lower bound (infimum) of a subset of a poset — *in Mathlib* — `upperBounds`, `IsLUB`
- **Theorem 19.1.9 (pdf p.262)**, p.262 [AA-332]: A least upper bound (greatest lower bound) of a subset, if it exists, is unique — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_9`, `UndergradKB.AbstractAlgebra.Course.judson_19_1_9_glb`, `IsLUB.unique`
- **Example 19.1.10 (pdf p.262)**, p.262 [AA-328]: The power set $P(X)$ ordered by inclusion is a poset (and in fact a lattice and Boolean algebra) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_10`, `Set.instBooleanAlgebra`, `Set.instCompleteAtomicBooleanAlgebra`
- **Axiom 19.1.12 (pdf p.262)**, p.262 [AA-334]: Principle of Duality: a statement true for all lattices stays true after reversing the order and swapping join and meet — *in Mathlib* — `OrderDual.instLattice`
- **Theorem 19.1.13 (pdf p.262)**, p.262 [AA-335]: In a lattice, join and meet are commutative, associative, idempotent, and satisfy the absorption laws — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_13`, `sup_comm`, `sup_assoc`, `sup_idem`
- **Definition lattice/join/meet (pdf p.262)**, p.262 [AA-333]: A lattice is a poset in which every pair has a join $a\vee b$ (least upper bound) and meet $a\wedge b$ (greatest lower bound) — *in Mathlib* — `Lattice`, `SemilatticeSup`, `SemilatticeInf`, `isLUB_pair`
- **Theorem 19.1.14 (pdf p.263)**, p.263 [AA-336]: A nonempty set with two operations satisfying those four laws is a lattice for the order $a\preceq b\iff a\vee b=b$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_14`, `Lattice.mk'`, `sup_eq_right`
- **Definitions (pdf p.263-264)**, p.263 [AA-337]: Largest and smallest elements; complemented lattice; distributive lattice; Boolean algebra = bounded distributive complemented lattice — *in Mathlib* — `OrderTop`, `OrderBot`, `BoundedOrder`, `ComplementedLattice`

#### Section 19.2

- **Theorem 19.2.1 (pdf p.264)**, p.264 [AA-338]: A lattice satisfies $a\wedge(b\vee c)=(a\wedge b)\vee(a\wedge c)$ for all elements iff it satisfies the dual law — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_1`, `DistribLattice`, `sup_inf_left`, `inf_sup_left`
- **Theorem 19.2.2 (pdf p.264-265)**, p.264 [AA-339]: A set is a Boolean algebra iff it has two operations satisfying commutativity, associativity, both distributive laws, identities $I,O$, and complements — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_2`, `UndergradKB.AbstractAlgebra.Course.judson_19_2_2_converse`, `UndergradKB.AbstractAlgebra.BooleanAxioms.toBooleanAlgebra`
- **Theorem 19.2.3 (pdf p.265)**, p.265 [AA-340]: Boolean-algebra identities: $a\vee I=I$, $a\wedge O=O$, cancellation, uniqueness of complements, $(a')'=a$, $I'=O$, De Morgan — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_3`, `sup_top_eq`, `eq_of_inf_eq_sup_eq`, `compl_unique`
- **Lemma 19.2.4 (pdf p.266)**, p.266 [AA-344]: In a finite Boolean algebra, every nonzero element lies above some atom — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_4`, `IsAtomic`
- **Lemma 19.2.5 (pdf p.266)**, p.266 [AA-345]: Distinct atoms have meet $O$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_5`, `IsAtom.inf_eq_bot_of_ne`
- **Definition isomorphism of Boolean algebras (pdf p.266)**, p.266 [AA-342]: A bijection between Boolean algebras preserving join and meet is an isomorphism — *in Mathlib* — `OrderIso`, `LatticeHom`, `BoundedLatticeHom`
- **Definition atom (pdf p.266)**, p.266 [AA-343]: An atom is a nonzero element with no nonzero element strictly below it — *in Mathlib* — `IsAtom`, `IsAtom.le_iff`, `isAtom_iff_le_of_ge`
- **Lemma 19.2.6 (pdf p.267)**, p.267 [AA-341]: In a Boolean algebra, $a\preceq b$ iff $a\wedge b'=O$ iff $a'\vee b=I$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_6`, `UndergradKB.AbstractAlgebra.le_iff_inf_compl_eq_bot_iff_compl_sup_eq_top`
- **Lemma 19.2.7 (pdf p.267)**, p.267 [AA-346]: If $b\not\preceq c$ in a Boolean algebra, some atom lies below $b$ but not below $c$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_7`, `UndergradKB.AbstractAlgebra.exists_atom_le_not_le`
- **Lemma 19.2.8 (pdf p.267)**, p.267 [AA-347]: In a finite Boolean algebra every element is the join of the atoms below it, and uniquely so — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_8`, `UndergradKB.AbstractAlgebra.sup_atoms_le_eq`
- **Theorem 19.2.9 (pdf p.267-268)**, p.267 [AA-348]: Every finite Boolean algebra is isomorphic to the power set of the set of its atoms — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_9`, `UndergradKB.AbstractAlgebra.atomsOrderIso`
- **Corollary 19.2.10 (pdf p.268)**, p.268 [AA-349]: A finite Boolean algebra has $2^n$ elements — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_2_10`, `UndergradKB.AbstractAlgebra.card_eq_two_pow_card_atoms`
- **Definition series-parallel circuits (pdf p.268-269)**, p.268 [AA-350]: Switches in series (meet) and in parallel (join) generate the series-parallel circuits, whose behavior is a Boolean expression — *proved proved here* — `UndergradKB.AbstractAlgebra.Circuit`, `UndergradKB.AbstractAlgebra.Circuit.eval`

#### Section 19.3

- **Theorem 19.3.7 (pdf p.269)**, p.269 [AA-351]: The set of all (equivalence classes of) circuits is a Boolean algebra under parallel and series — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_19_3_7`, `UndergradKB.AbstractAlgebra.CircuitClass.instBooleanAlgebra`, `UndergradKB.AbstractAlgebra.CircuitClass.eval_series_parallel_compl`

#### Section 19.1

- **Example 19.1.4** [AA-329]: The subgroups of a group form a poset under inclusion, indeed a lattice with meet $H\cap K$ and join the subgroup generated by $H\cup K$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_19_1_11`, `Subgroup.sup_eq_closure`, `Subgroup.closure_union`

#### Section 19.3

- **Example 19.3.6** [AA-350]: Switches in series (meet) and in parallel (join) generate the series-parallel circuits, whose behavior is a Boolean expression — *proved proved here* — `UndergradKB.AbstractAlgebra.Circuit`, `UndergradKB.AbstractAlgebra.Circuit.eval`
- **Definition (unnumbered) ideal** [AA-256]: An ideal is a subring absorbing multiplication by arbitrary ring elements on both sides (one-sided versions give left and right ideals). — *in Mathlib* — `Ideal`, `Ideal.IsTwoSided`, `Submodule`
- **D155** [AA-298]: Divisibility $a\mid b$, units, and associates ($a=ub$ for a unit $u$) in a commutative ring — *in Mathlib* — `IsUnit`, `Associated`, `dvd_dvd_iff_associated`
- **D156** [AA-299]: A nonzero nonunit $p$ of a domain is irreducible if $p=ab$ forces $a$ or $b$ to be a unit — *in Mathlib* — `Irreducible`
- **D157** [AA-305]: Principal ideal domain: an integral domain in which every ideal is principal — *in Mathlib* — `IsPrincipalIdealRing`, `IsDomain`
- **D158** [AA-309]: Ascending chain condition on ideals (Noetherian ring): every increasing chain of ideals stabilizes — *in Mathlib* — `IsNoetherianRing`, `monotone_stabilizes_iff_noetherian`, `isNoetherianRing_iff_ideal_fg`
- **D159** [AA-314]: Euclidean domain: a domain with a division algorithm governed by a Euclidean valuation $\nu\colon D\setminus\{0\}\to\mathbb{N}_0$ with $\nu(a)\le\nu(ab)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.isEuclideanValuation_int`, `UndergradKB.AbstractAlgebra.isEuclideanValuation_polynomial`
- **D166** [AA-327]: A partial order is a reflexive, antisymmetric, transitive relation; a set with one is a poset — *in Mathlib* — `PartialOrder`
- **D167** [AA-327]: A partial order is a reflexive, antisymmetric, transitive relation; a set with one is a poset — *in Mathlib* — `PartialOrder`
- **D168** [AA-331]: Upper bound, least upper bound (supremum), lower bound, greatest lower bound (infimum) of a subset of a poset — *in Mathlib* — `upperBounds`, `IsLUB`
- **D169** [AA-331]: Upper bound, least upper bound (supremum), lower bound, greatest lower bound (infimum) of a subset of a poset — *in Mathlib* — `upperBounds`, `IsLUB`
- **D170** [AA-331]: Upper bound, least upper bound (supremum), lower bound, greatest lower bound (infimum) of a subset of a poset — *in Mathlib* — `upperBounds`, `IsLUB`
- **D171** [AA-333]: A lattice is a poset in which every pair has a join $a\vee b$ (least upper bound) and meet $a\wedge b$ (greatest lower bound) — *in Mathlib* — `Lattice`, `SemilatticeSup`, `SemilatticeInf`, `isLUB_pair`
- **D172** [AA-333]: A lattice is a poset in which every pair has a join $a\vee b$ (least upper bound) and meet $a\wedge b$ (greatest lower bound) — *in Mathlib* — `Lattice`, `SemilatticeSup`, `SemilatticeInf`, `isLUB_pair`
- **D173** [AA-333]: A lattice is a poset in which every pair has a join $a\vee b$ (least upper bound) and meet $a\wedge b$ (greatest lower bound) — *in Mathlib* — `Lattice`, `SemilatticeSup`, `SemilatticeInf`, `isLUB_pair`
- **D175** [AA-350]: Switches in series (meet) and in parallel (join) generate the series-parallel circuits, whose behavior is a Boolean expression — *proved proved here* — `UndergradKB.AbstractAlgebra.Circuit`, `UndergradKB.AbstractAlgebra.Circuit.eval`

## Chapter 20

13 items; 13 with a Lean name; 13 in Mathlib.

- **Definition (unnumbered, 20.1) (pdf p.275)**, p.275 [AA-352]: A vector space over a field $F$ is an abelian group $V$ with an $F$-scalar multiplication satisfying associativity, two distributive laws and $1v=v$. — *in Mathlib* — `Module`, `AddCommGroup`, `Field`

#### Section 20.1

- **Proposition 20.1.5 (pdf p.276)**, p.276 [AA-353]: In a vector space $0v=0$, $\alpha 0=0$, $\alpha v=0\Rightarrow \alpha=0$ or $v=0$, $(-1)v=-v$, and $-(\alpha v)=(-\alpha)v=\alpha(-v)$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_1_5`, `zero_smul`, `smul_zero`, `smul_eq_zero`
- **Definition (unnumbered, 20.2) (pdf p.276)**, p.276 [AA-354]: A subspace of $V$ is a subset closed under vector addition and scalar multiplication. — *in Mathlib* — `Submodule`
- **Definition (unnumbered, 20.2) (pdf p.277)**, p.277 [AA-355]: A linear combination of $v_1,\dots,v_n$ is $\sum \alpha_i v_i$, and the span is the set of all such combinations. — *in Mathlib* — `Submodule.span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_le`

#### Section 20.2

- **Proposition 20.2.3 (pdf p.277)**, p.277 [AA-356]: The span of finitely many vectors is a subspace of $V$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_2_3`, `Submodule.span`
- **Definition (unnumbered, 20.3) (pdf p.277)**, p.277 [AA-357]: Vectors $v_1,\dots,v_n$ are linearly independent iff $\sum\alpha_i v_i=0$ forces all $\alpha_i=0$ (dependent otherwise). — *in Mathlib* — `LinearIndependent`, `linearIndependent_iff'`, `not_linearIndependent_iff`
- **Definition (unnumbered, 20.3) (pdf p.278)**, p.278 [AA-361]: A basis of $V$ is a linearly independent spanning set. — *in Mathlib* — `Module.Basis`, `Module.Basis.mk`

#### Section 20.3

- **Proposition 20.3.1 (pdf p.278)**, p.278 [AA-358]: If $v_1,\dots,v_n$ are linearly independent, the coefficients of a vector in terms of them are unique. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_1`, `LinearIndependent.eq_coords_of_eq`, `LinearIndependent.repr_eq`
- **Proposition 20.3.2 (pdf p.278)**, p.278 [AA-359]: A set of vectors is linearly dependent iff one of them is a linear combination of the others. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_2`, `linearIndependent_iff_notMem_span`
- **Proposition 20.3.3 (pdf p.278)**, p.278 [AA-360]: If $V$ is spanned by $n$ vectors, any $m>n$ vectors in $V$ are linearly dependent. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_3`, `linearIndependent_le_span`, `linearIndependent_le_span'`, `linearIndependent_le_basis`
- **Proposition 20.3.6 and dimension definition (pdf p.279)**, p.279 [AA-362]: Any two bases of a vector space have the same size, so the dimension $\dim V$ is well defined. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_6`, `Module.Basis.mk_eq_rank''`, `Module.finrank_eq_card_basis`, `Module.finrank`
- **Theorem 20.3.7 parts 1-2 (pdf p.279)**, p.279 [AA-363]: In an $n$-dimensional space, any $n$ independent vectors form a basis, and any $n$ spanning vectors form a basis. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_7_indep`, `UndergradKB.AbstractAlgebra.Course.judson_20_3_7_span`, `LinearIndependent.span_eq_top_of_card_eq_finrank`, `basisOfLinearIndependentOfCardEqFinrank`
- **Theorem 20.3.7 part 3 (pdf p.279)**, p.279 [AA-364]: In an $n$-dimensional space, independent vectors $v_1,\dots,v_k$ with $k<n$ extend to a basis. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_20_3_7_extend`, `Module.Basis.extend`, `exists_linearIndependent_cons_of_lt_finrank`

## Chapter 21

38 items; 38 with a Lean name; 18 proved proved here; 20 in Mathlib.

- **Definition (unnumbered, 21.1) (pdf p.284)**, p.284 [AA-365]: A field $E$ is an extension of $F$ when $F$ is a subfield of $E$ ($F$ is the base field). — *in Mathlib* — `Algebra`, `IntermediateField`

#### Section 21.1

- **Theorem 21.1.5 (pdf p.285)**, p.285 [AA-366]: Kronecker: every nonconstant $p\in F[x]$ has a root in some extension field $E$ of $F$ (take $F[x]/\langle p\rangle$ for $p$ irreducible). — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_5`
- **Definition (unnumbered, 21.1.1) (pdf p.286)**, p.286 [AA-367]: An element of an extension is algebraic over $F$ if it is a root of a nonzero polynomial in $F[x]$, otherwise transcendental; an extension is algebraic if every element is. — *in Mathlib* — `IsAlgebraic`, `Transcendental`, `Algebra.IsAlgebraic`
- **Definition (unnumbered, 21.1.1) (pdf p.286)**, p.286 [AA-368]: $F(\alpha_1,\dots,\alpha_n)$ is the smallest field containing $F$ and the $\alpha_i$; an extension $F(\alpha)$ is simple. — *in Mathlib* — `IntermediateField.adjoin`
- **Theorem 21.1.9 (pdf p.287)**, p.287 [AA-369]: $\alpha$ is transcendental over $F$ iff $F(\alpha)\cong F(x)$ (the rational function field). — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_9`, `UndergradKB.AbstractAlgebra.transcendental_iff_nonempty_algEquiv_ratFunc`
- **Theorem 21.1.10 and minimal polynomial definition (pdf p.287)**, p.287 [AA-370]: An algebraic $\alpha$ has a unique monic irreducible polynomial of least degree vanishing at it, and it divides every polynomial vanishing at $\alpha$ (minimal polynomial). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_10`, `minpoly`, `minpoly.monic`, `minpoly.irreducible`
- **Proposition 21.1.12 (pdf p.288)**, p.288 [AA-371]: For $\alpha$ algebraic with minimal polynomial $p$, $F(\alpha)\cong F[x]/\langle p\rangle$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_12`, `IntermediateField.adjoinRootEquivAdjoin`
- **Theorem 21.1.13 (pdf p.288)**, p.288 [AA-372]: If $\alpha$ has degree $n$ over $F$, every element of $F(\alpha)$ is uniquely $b_0+b_1\alpha+\dots+b_{n-1}\alpha^{n-1}$ (so $\{1,\alpha,\dots,\alpha^{n-1}\}$ is a basis and $[F(\alpha):F]=n$). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_13`, `IntermediateField.adjoin.powerBasis`, `IntermediateField.adjoin.finrank`, `IntermediateField.adjoin.finiteDimensional`
- **Definition (unnumbered, 21.1) (pdf p.289)**, p.289 [AA-373]: An extension $E/F$ that is finite dimensional as an $F$-vector space is finite of degree $[E:F]=\dim_F E$. — *in Mathlib* — `Module.Finite`, `FiniteDimensional`, `Module.finrank`
- **Theorem 21.1.15 (pdf p.289)**, p.289 [AA-374]: Every finite extension is algebraic. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_15`, `Algebra.IsAlgebraic.of_finite`, `IsAlgebraic.of_finite`
- **Remark 21.1.16 (pdf p.289)**, p.289 [AA-375]: The converse fails: the algebraic reals over $\mathbb Q$ form an infinite (non-finite) algebraic extension. — *proved proved here* — `UndergradKB.AbstractAlgebra.algebraicClosure_rat_real_not_finite`
- **Theorem 21.1.17 (pdf p.289)**, p.289 [AA-376]: Tower law: for finite extensions $F\subset E\subset K$, $[K:F]=[K:E][E:F]$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_17`, `Module.finrank_mul_finrank`, `Module.finrank_mul_finrank'`
- **Corollary 21.1.18 (pdf p.290)**, p.290 [AA-377]: For a chain $F_1\subset\dots\subset F_k$ of finite extensions, $[F_k:F_1]=\prod[F_{i+1}:F_i]$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_18`, `UndergradKB.AbstractAlgebra.relfinrank_chain`
- **Corollary 21.1.19 (pdf p.290)**, p.290 [AA-378]: If $\alpha$ is algebraic over $F$ and $\beta\in F(\alpha)$, then the degree of $\beta$ over $F$ divides the degree of $\alpha$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_19`, `minpoly.degree_dvd`, `IntermediateField.finrank_dvd_of_le_right`
- **Theorem 21.1.22 (pdf p.291)**, p.291 [AA-379]: $E/F$ is finite iff $E=F(\alpha_1,\dots,\alpha_n)$ with algebraic $\alpha_i$ iff $E$ is a finite tower of algebraic simple extensions. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_22`, `UndergradKB.AbstractAlgebra.finite_tfae_tower`
- **Theorem 21.1.23 (pdf p.291)**, p.291 [AA-380]: The elements of $E$ algebraic over $F$ form a subfield (in particular the algebraic numbers form a field). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_23`, `UndergradKB.AbstractAlgebra.Course.judson_21_1_24`, `algebraicClosure`, `integralClosure`
- **Definition (unnumbered, 21.1.2) (pdf p.292)**, p.292 [AA-381]: A field is algebraically closed if every nonconstant polynomial has a root in it; the algebraic closure of $F$ in $E$ is the field of elements algebraic over $F$. — *in Mathlib* — `IsAlgClosed`, `IsAlgClosed.exists_root`, `algebraicClosure`
- **Corollary 21.1.24 (pdf p.292)**, p.292 [AA-380]: The elements of $E$ algebraic over $F$ form a subfield (in particular the algebraic numbers form a field). — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_23`, `UndergradKB.AbstractAlgebra.Course.judson_21_1_24`, `algebraicClosure`, `integralClosure`
- **Theorem 21.1.25 (pdf p.292)**, p.292 [AA-382]: A field is algebraically closed iff every nonconstant polynomial factors into linear factors. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_25`, `IsAlgClosed.of_exists_root`, `IsAlgClosed.exists_root`
- **Corollary 21.1.26 (pdf p.292)**, p.292 [AA-383]: An algebraically closed field has no proper algebraic extension. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_26`, `IsAlgClosed.algebraMap_bijective_of_isIntegral`, `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`
- **Theorem 21.1.27 (pdf p.292)**, p.292 [AA-384]: Every field has an algebraic closure, unique up to isomorphism. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_27`, `AlgebraicClosure`, `IsAlgClosure`, `IsAlgClosure.equiv`
- **Theorem 21.1.28 (pdf p.292)**, p.292 [AA-385]: Fundamental Theorem of Algebra: $\mathbb C$ is algebraically closed. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_28`, `Complex.isAlgClosed`, `Complex.exists_root`
- **Definition (unnumbered, 21.2) (pdf p.292)**, p.292 [AA-386]: A splitting field of $p\in F[x]$ is an extension $E=F(\alpha_1,\dots,\alpha_n)$ over which $p$ factors into linear factors; $p$ splits in $E$ if it is a product of linear factors there. — *in Mathlib* — `Polynomial.IsSplittingField`, `Polynomial.Splits`

#### Section 21.2

- **Theorem 21.2.3 (pdf p.293)**, p.293 [AA-387]: Every nonconstant polynomial over $F$ has a splitting field. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_2_3`, `Polynomial.SplittingField`, `Polynomial.SplittingField.splits`, `Polynomial.IsSplittingField.splits`
- **Lemma 21.2.4 (pdf p.293)**, p.293 [AA-388]: An isomorphism $E\to F$ extends to an isomorphism $E(\alpha)\to F(\beta)$ sending $\alpha$ to $\beta$ when $\beta$ is a root of the image of the minimal polynomial of $\alpha$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_2_4`, `UndergradKB.AbstractAlgebra.exists_ringEquiv_adjoin`
- **Theorem 21.2.6 (pdf p.294)**, p.294 [AA-389]: An isomorphism of base fields extends to an isomorphism of splitting fields; hence the splitting field is unique up to isomorphism. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_2_6`, `UndergradKB.AbstractAlgebra.Course.judson_21_2_8`, `UndergradKB.AbstractAlgebra.exists_ringEquiv_of_isSplittingField`, `UndergradKB.AbstractAlgebra.splittingField_unique`
- **Corollary 21.2.8 (pdf p.294)**, p.294 [AA-389]: An isomorphism of base fields extends to an isomorphism of splitting fields; hence the splitting field is unique up to isomorphism. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_2_6`, `UndergradKB.AbstractAlgebra.Course.judson_21_2_8`, `UndergradKB.AbstractAlgebra.exists_ringEquiv_of_isSplittingField`, `UndergradKB.AbstractAlgebra.splittingField_unique`

#### Section 21.3

- **Definition (unnumbered, 21.3.1) (pdf p.295)**, p.295 [AA-390]: A real number is constructible if a segment of that length can be built from a unit segment with straightedge and compass in finitely many steps. — *proved proved here* — `UndergradKB.AbstractAlgebra.ConstructiblePt`, `UndergradKB.AbstractAlgebra.Constructible`
- **Theorem 21.3.1 (pdf p.295)**, p.295 [AA-391]: The constructible real numbers form a subfield of $\mathbb R$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_1`, `UndergradKB.AbstractAlgebra.constructibleField`
- **Lemma 21.3.3 (pdf p.296)**, p.296 [AA-392]: The square root of a (positive) constructible number is constructible. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_3`, `UndergradKB.AbstractAlgebra.Constructible.sqrt`
- **Lemma 21.3.5 (pdf p.296)**, p.296 [AA-393]: Over a subfield $F\subset\mathbb R$, a line through two $F$-points is $ax+by+c=0$ and a circle with center and radius in $F$ is $x^2+y^2+dx+ey+f=0$, with coefficients in $F$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_5`, `UndergradKB.AbstractAlgebra.line_equation_over`, `UndergradKB.AbstractAlgebra.circle_equation_over`
- **Lemma 21.3.6 (pdf p.297)**, p.297 [AA-394]: Intersections of lines and circles defined over a field $F$ of constructible numbers have coordinates in $F(\sqrt\alpha)$ for some $\alpha\in F$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_6`, `UndergradKB.AbstractAlgebra.lineLine_coords`, `UndergradKB.AbstractAlgebra.lineCircle_coords`, `UndergradKB.AbstractAlgebra.circleCircle_coords`
- **Theorem 21.3.7 (pdf p.297)**, p.297 [AA-395]: A real $\alpha$ is constructible iff it lies in the top of a tower $\mathbb Q=F_0\subset\dots\subset F_k$ of square-root extensions; then $[\mathbb Q(\alpha):\mathbb Q]$ is a power of 2. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_7`, `UndergradKB.AbstractAlgebra.constructiblePt_tower`, `UndergradKB.AbstractAlgebra.constructible_iff_tower`, `UndergradKB.AbstractAlgebra.Constructible.finrank_eq_two_pow`
- **Unnumbered result, Section 21.3.2 (pdf p.298)**, p.298 [AA-397]: Doubling the cube is impossible, since $\sqrt[3]{2}$ has degree 3 over $\mathbb Q$, not a power of 2. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_doubling_cube`, `UndergradKB.AbstractAlgebra.not_constructible_cbrt_two`
- **Unnumbered result, Section 21.3.2 (pdf p.298)**, p.298 [AA-398]: Squaring the circle is impossible, since $\pi$ is transcendental over $\mathbb Q$. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_squaring_circle`, `UndergradKB.AbstractAlgebra.transcendental_pi`, `UndergradKB.AbstractAlgebra.not_constructible_sqrt_pi`
- **Unnumbered result, Section 21.3.3 (pdf p.298)**, p.298 [AA-399]: Trisecting a $60^\circ$ angle is impossible, since $\cos 20^\circ$ is a root of the irreducible cubic $8x^3-6x-1$ and so has degree 3. — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_trisect_angle`, `UndergradKB.AbstractAlgebra.irreducible_eight_cubic`, `UndergradKB.AbstractAlgebra.not_constructible_cos_twenty_degrees`, `UndergradKB.AbstractAlgebra.not_constructiblePt_exp_twenty_degrees`
- **Unnumbered formula, Section 21.3.3 (pdf p.298)**, p.298 [AA-400]: Triple-angle formula $\cos 3\theta=4\cos^3\theta-3\cos\theta$. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_triple_angle`, `Real.cos_three_mul`, `Complex.cos_three_mul`
- **Corollary 21.3.8 (pdf p.298)**, p.298 [AA-396]: The field of constructible numbers is an algebraic extension of $\mathbb Q$ (but not a finite one). — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_21_3_8`, `UndergradKB.AbstractAlgebra.Constructible.isAlgebraic`, `UndergradKB.AbstractAlgebra.constructibleIntermediateField_not_finite`

## Chapter 22

21 items; 21 with a Lean name; 10 proved proved here; 11 in Mathlib.


#### Section 22.1

- **Proposition 22.1.1 (pdf p.303)**, p.303 [AA-401]: A finite field has prime characteristic $p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_1`, `CharP.char_is_prime`, `FiniteField.card'`
- **Proposition 22.1.2 (pdf p.303)**, p.303 [AA-402]: A finite field of characteristic $p$ has $p^n$ elements for some $n\ge 1$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_2`, `FiniteField.card`, `FiniteField.card'`, `FiniteField.pow_finrank_eq_card`
- **Lemma 22.1.3 (pdf p.303)**, p.303 [AA-403]: Freshman's dream: in characteristic $p$, $(a+b)^{p^n}=a^{p^n}+b^{p^n}$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_3`, `add_pow_char_pow`, `add_pow_char`, `sub_pow_char_pow`
- **Lemma 22.1.5 (pdf p.304)**, p.304 [AA-405]: $f$ is separable iff $f$ and $f'$ are relatively prime — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_5`, `Polynomial.separable_def`, `Polynomial.nodup_roots_iff_of_splits`
- **Definition (unnumbered) (pdf p.304)**, p.304 [AA-404]: Definition of a separable polynomial (book: distinct roots in a splitting field) — *proved proved here* — `UndergradKB.AbstractAlgebra.separable_iff_nodup_roots_splittingField`
- **Theorem 22.1.6 (pdf p.305)**, p.305 [AA-406]: For every prime $p$ and $n\ge1$ there is a field with $p^n$ elements, unique up to isomorphism, namely the splitting field of $x^{p^n}-x$ over $\mathbb{Z}_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_6`, `GaloisField`, `GaloisField.card`, `FiniteField.algEquivOfCardEq`
- **Theorem 22.1.7 (pdf p.305)**, p.305 [AA-408]: Subfields of $\mathrm{GF}(p^n)$ have $p^m$ elements with $m\mid n$, and conversely each $m\mid n$ gives a unique subfield $\cong \mathrm{GF}(p^m)$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_7`, `UndergradKB.AbstractAlgebra.finiteField_subfield_card_dvd`, `UndergradKB.AbstractAlgebra.finiteField_exists_unique_subfield`
- **Definition (unnumbered) (pdf p.305)**, p.305 [AA-407]: Definition of the Galois field $\mathrm{GF}(p^n)$ as the unique field of order $p^n$ — *in Mathlib* — `GaloisField`
- **Theorem 22.1.10 (pdf p.306)**, p.306 [AA-409]: A finite subgroup of the unit group of a field is cyclic; in particular $F^\times$ is cyclic for a finite field $F$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_10`, `UndergradKB.AbstractAlgebra.Course.judson_22_1_11`, `isCyclic_of_injective_ringHom`, `isCyclic_subgroup_units`
- **Corollary 22.1.11 (pdf p.306)**, p.306 [AA-409]: A finite subgroup of the unit group of a field is cyclic; in particular $F^\times$ is cyclic for a finite field $F$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_10`, `UndergradKB.AbstractAlgebra.Course.judson_22_1_11`, `isCyclic_of_injective_ringHom`, `isCyclic_subgroup_units`
- **Corollary 22.1.12 (pdf p.306)**, p.306 [AA-410]: Every finite extension of a finite field is simple — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_1_12`, `Field.exists_primitive_element_of_finite_bot`, `Field.exists_primitive_element_of_finite_top`
- **Definition (unnumbered) (pdf p.307)**, p.307 [AA-412]: Definition of cyclic code: a binary block code closed under cyclic shift — *proved proved here* — `UndergradKB.AbstractAlgebra.CyclicCodes.IsCyclicCode`
- **Definition (unnumbered) (pdf p.308)**, p.308 [AA-411]: Definition of polynomial codes: fix $g\in\mathbb{Z}_2[x]$ of degree $n-k$; codewords are the multiples of $g$ of degree $<n$ — *proved proved here* — `UndergradKB.AbstractAlgebra.CyclicCodes.polynomialCode_eq_map`

#### Section 22.2

- **Theorem 22.2.3 (pdf p.309)**, p.309 [AA-413]: A linear code in $\mathbb{Z}_2^n$ is cyclic iff it is an ideal of $R_n=\mathbb{Z}_2[x]/\langle x^n-1\rangle$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_22_2_3`, `UndergradKB.AbstractAlgebra.CyclicCodes.isCyclicCode_iff_exists_ideal`
- **Definition and statement (unnumbered) (pdf p.309)**, p.309 [AA-414]: Every ideal of $R_n$ is generated by a unique monic divisor $g$ of $x^n-1$ (minimal generator polynomial) — *proved proved here* — `UndergradKB.AbstractAlgebra.CyclicCodes.exists_unique_monic_generator`
- **Proposition 22.2.5 (pdf p.310)**, p.310 [AA-415]: If $x^n-1=g h$ then the standard matrices built from $g$ and $h$ are generator and parity-check matrices of $\langle g\rangle$ and $HG=0$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_22_2_5`, `UndergradKB.AbstractAlgebra.CyclicCodes.mem_cyclicCodeOf_iff_mul_eq_zero`
- **Definition (unnumbered) (pdf p.310)**, p.310 [AA-416]: Definition of the Vandermonde matrix and its determinant — *in Mathlib* — `Matrix.vandermonde`
- **Lemma 22.2.7 (pdf p.311)**, p.311 [AA-417]: Vandermonde determinant equals the product of pairwise differences — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_22_2_7`, `Matrix.det_vandermonde`, `Matrix.det_vandermonde_eq_zero_iff`, `Matrix.det_vandermonde_ne_zero_iff`
- **Theorem 22.2.8 (pdf p.311)**, p.311 [AA-418]: BCH bound: if $s$ consecutive powers of a primitive $n$th root $\omega$ are roots of $g$, then the cyclic code $\langle g\rangle$ has minimum distance at least $s+1$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_22_2_8`, `UndergradKB.AbstractAlgebra.CyclicCodes.bch_bound`
- **Theorem 22.2.9 (pdf p.312)**, p.312 [AA-420]: Equivalent descriptions of a BCH code: via generator lcm, via vanishing at $\omega^i$, via a Vandermonde-type parity-check matrix — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_22_2_9`, `UndergradKB.AbstractAlgebra.CyclicCodes.mem_bchCode_iff`
- **Definition (unnumbered) (pdf p.312)**, p.312 [AA-419]: Definition of BCH code of length $n$ and designed distance $d=2r+1$: generator is the lcm of minimal polynomials of $\omega^1,\dots,\omega^{2r}$ — *proved proved here* — `UndergradKB.AbstractAlgebra.CyclicCodes.bchCode`

## Chapter 23

27 items; 27 with a Lean name; 8 proved proved here; 19 in Mathlib.


#### Section 23.1

- **Proposition 23.1.1 (pdf p.318)**, p.318 [AA-421]: The automorphisms of a field form a group under composition — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_1`, `RingAut`
- **Proposition 23.1.2 (pdf p.318)**, p.318 [AA-422]: The automorphisms of $E$ fixing $F$ form a group — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_2`, `AlgEquiv.aut`
- **Proposition 23.1.5 (pdf p.319)**, p.319 [AA-424]: An automorphism in $G(E/F)$ permutes the roots in $E$ of any $f\in F[x]$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_5`, `UndergradKB.AbstractAlgebra.autEquiv_rootSet`
- **Definition (unnumbered) (pdf p.319)**, p.319 [AA-423]: Definition of the Galois group $G(E/F)$ of an extension and of the Galois group of a polynomial (that of its splitting field) — *in Mathlib* — `AlgEquiv.aut`, `Polynomial.Gal`
- **Proposition 23.1.6 (pdf p.320)**, p.320 [AA-425]: Conjugate elements (same minimal polynomial) over $F$ yield an $F$-isomorphism $F(\alpha)\to F(\beta)$ sending $\alpha$ to $\beta$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_6`, `UndergradKB.AbstractAlgebra.exists_algEquiv_adjoin_of_minpoly_eq`
- **Theorem 23.1.7 (pdf p.320)**, p.320 [AA-426]: For the splitting field $E$ of a separable polynomial over $F$, $\lvert G(E/F)\rvert=[E:F]$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_7`, `Polynomial.Gal.card_of_separable`, `IsGalois.card_aut_eq_finrank`, `IsGalois.of_separable_splitting_field`
- **Corollary 23.1.9 (pdf p.320)**, p.320 [AA-427]: For a finite extension $E/F$ of finite fields of degree $k$, $G(E/F)$ is cyclic of order $k$ (generated by Frobenius) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_9`, `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`, `FiniteField.frobeniusAlgEquivOfAlgebraic`, `IsGalois.card_aut_eq_finrank`
- **Definition (unnumbered) (pdf p.321)**, p.321 [AA-428]: Definition of multiplicity, simple root, and separable extension (every element is a root of a separable polynomial over $F$) — *in Mathlib* — `Algebra.IsSeparable`, `Polynomial.rootMultiplicity`, `Polynomial.Separable`
- **Proposition 23.1.12 (pdf p.322)**, p.322 [AA-429]: An irreducible polynomial is separable in characteristic 0, and in characteristic $p$ when it is not a polynomial in $x^p$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_12`, `UndergradKB.AbstractAlgebra.Course.judson_23_1_12_charP`, `UndergradKB.AbstractAlgebra.irreducible_separable_charZero`, `UndergradKB.AbstractAlgebra.irreducible_separable_iff_not_expand`
- **Theorem 23.1.13 (pdf p.322)**, p.322 [AA-430]: Primitive Element Theorem: a finite separable extension is simple, $E=F(\alpha)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_1_13`, `Field.exists_primitive_element`

#### Section 23.2

- **Proposition 23.2.1 (pdf p.322)**, p.322 [AA-431]: The fixed set of a family or group of automorphisms is a subfield (the fixed field) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_2`, `FixedPoints.subfield`, `FixedPoints.intermediateField`, `IntermediateField.fixedField`
- **Corollary 23.2.2 (pdf p.323)**, p.323 [AA-431]: The fixed set of a family or group of automorphisms is a subfield (the fixed field) — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_2`, `FixedPoints.subfield`, `FixedPoints.intermediateField`, `IntermediateField.fixedField`
- **Proposition 23.2.4 (pdf p.323)**, p.323 [AA-433]: For a splitting field $E$ of a separable polynomial over $F$, the fixed field of $G(E/F)$ is $F$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_4`, `IsGalois.mem_bot_iff_fixed`, `IsGalois.tfae`, `IsGalois.fixedField_top`
- **Lemma 23.2.5 (pdf p.323)**, p.323 [AA-434]: Artin-type bound: for a finite group $G$ of automorphisms of $E$ with $F=E_G$, $[E:F]\le\lvert G\rvert$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_5`, `FixedPoints.finrank_le_card`, `FixedPoints.finrank_eq_card`
- **Theorem 23.2.6 (pdf p.324)**, p.324 [AA-435]: Equivalent: $E/F$ finite normal separable; $E$ is a splitting field of a separable polynomial; $F=E_G$ for a finite automorphism group $G$ — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_6`, `UndergradKB.AbstractAlgebra.galois_tfae`
- **Definition (unnumbered) (pdf p.324)**, p.324 [AA-432]: Definition of a normal extension: every irreducible polynomial with a root in $E$ splits in $E$ — *in Mathlib* — `Normal`, `Normal.splits`
- **Corollary 23.2.7 (pdf p.325)**, p.325 [AA-436]: If $F=K_G$ for a finite group $G$ of automorphisms of $K$ then $G=G(K/F)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_7`, `FixedPoints.toAlgAut_bijective`, `FixedPoints.toAlgAutMulEquiv`, `FixedPoints.toAlgAut_surjective`
- **Theorem 23.2.10 (pdf p.325)**, p.325 [AA-437]: Fundamental Theorem of Galois Theory: subfields between $F$ and $E$ correspond bijectively and inclusion-reversingly to subgroups of $G(E/F)$; degrees and indices match; normality corresponds to normal subgroups with quotient group $G(K/F)$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_2_10`, `UndergradKB.AbstractAlgebra.Course.judson_23_2_10_normal`, `IsGalois.intermediateFieldEquivSubgroup`, `IntermediateField.fixingSubgroup_fixedField`
- **Definition (unnumbered) (pdf p.328)**, p.328 [AA-438]: Definition of $n$th roots of unity and primitive $n$th root of unity (generator of the cyclic group of roots) — *in Mathlib* — `rootsOfUnity`, `IsPrimitiveRoot`
- **Definition (unnumbered) (pdf p.328)**, p.328 [AA-439]: Definitions of extension by radicals and a polynomial solvable by radicals; also solvable group — *proved proved here* — `UndergradKB.AbstractAlgebra.SolvableByRadicals`

#### Section 23.3

- **Lemma 23.3.2 (pdf p.329)**, p.329 [AA-440]: Over characteristic 0, the splitting field of $x^n-a$ has solvable Galois group — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_2`, `gal_X_pow_sub_C_isSolvable`, `gal_X_pow_sub_one_isSolvable`, `gal_X_pow_isSolvable`
- **Lemma 23.3.3 (pdf p.329)**, p.329 [AA-441]: A radical extension is contained in a normal radical extension tower — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_3`, `UndergradKB.AbstractAlgebra.isRadical_normalClosure`
- **Theorem 23.3.4 (pdf p.330)**, p.330 [AA-442]: If $f$ is solvable by radicals over a characteristic-0 field then its Galois group is solvable — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_4`, `UndergradKB.AbstractAlgebra.isSolvable_gal_of_solvableByRadicals`
- **Lemma 23.3.5 (pdf p.330)**, p.330 [AA-443]: For $p$ prime, a subgroup of $S_p$ containing a transposition and a $p$-cycle is all of $S_p$ — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_5`, `Equiv.Perm.closure_prime_cycle_swap`, `Equiv.Perm.subgroup_eq_top_of_swap_mem`
- **Example 23.3.7 (pdf p.331)**, p.331 [AA-444]: The quintic $x^5-6x^3-27x-3$ has Galois group $S_5$ over $\mathbb{Q}$, hence is not solvable by radicals — *proved proved here* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_7`, `UndergradKB.AbstractAlgebra.Quintic.quintic_galActionHom_bijective`, `UndergradKB.AbstractAlgebra.Quintic.quintic_gal_not_isSolvable`, `UndergradKB.AbstractAlgebra.Quintic.quintic_not_solvableByRadicals`
- **Theorem 23.3.8 (pdf p.332)**, p.332 [AA-445]: Fundamental Theorem of Algebra: $\mathbb{C}$ is algebraically closed — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_23_3_8`, `Complex.isAlgClosed`, `IsAlgClosed`
- **proof deferred to Chapter 23** [AA-385]: Fundamental Theorem of Algebra: $\mathbb C$ is algebraically closed. — *in Mathlib* — `UndergradKB.AbstractAlgebra.Course.judson_21_1_28`, `Complex.isAlgClosed`, `Complex.exists_root`
