# Course outline: hefferon2020 (linear-algebra)

Generated from [`docs/coverage/linear-algebra/checklist.md`](../../coverage/linear-algebra/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build LinearAlgebra` builds this topic.

352 items in 20 chapters; 351 with a Lean name (99.7%).

## Chapter One

40 items; 40 with a Lean name; 20 proved proved here; 20 in Mathlib.


#### Section One.I

- **One.I.1.1**, p.12 [LA-001]: A linear equation $a_1x_1+\dots+a_nx_n=d$ over $\mathbb R$, a system of such equations, and a solution as an $n$-tuple (column vector) satisfying every equation. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_1_1`, `UndergradKB.LinearAlgebra.hefferon_One_I_2_9`
- **One.I.1.5**, p.14 [LA-003]: Gauss's Method is safe: applying any one of the three row operations to a linear system does not change its set of solutions. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_1_5`, `UndergradKB.LinearAlgebra.solutionSet_eq_of_isUnit`
- **One.I.1.6**, p.15 [LA-002]: The three elementary row operations on a system or matrix: swap two rows, multiply a row by a nonzero scalar, add a multiple of one row to a different row. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_1_6_swap`, `UndergradKB.LinearAlgebra.hefferon_One_I_1_6_scale`, `UndergradKB.LinearAlgebra.hefferon_One_I_1_6_add`
- **One.I.1.10**, p.16 [LA-005]: A system or matrix is in echelon form if each row's leading entry (first nonzero) lies strictly right of the leading entry above and all zero rows are at the bottom. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_I_1_10`, `Matrix.IsRowEchelon`, `Matrix.IsLeadingEntry`, `Matrix.IsRowEchelon.row_eq_zero_of_lt`
- **One.I.1.Summary**, p.19 [LA-006]: Summary of Gauss's Method: row operations bring any system to echelon form; a contradictory row means no solution, no contradiction and every variable leading means a unique solution, otherwise many solutions. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_1_Summary`, `UndergradKB.LinearAlgebra.hefferon_One_III_1_GaussJordan`
- **One.I.2.2**, p.23 [LA-007]: In an echelon form system the non-leading variables are the free variables; the leading variables can be solved in terms of them, which parametrizes the solution set. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_2_2`, `UndergradKB.LinearAlgebra.solution_unique_of_free_eq`, `UndergradKB.LinearAlgebra.exists_solution_of_free`
- **One.I.2.6**, p.25 [LA-130]: An $m$-by-$n$ matrix is a rectangular array of scalars with entries $A_{j,k}$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_29`, `Matrix`
- **One.I.2.7**, p.26 [LA-008]: A system is abbreviated by its augmented matrix (coefficients with a bar and the constant column), and row operations on the matrix mirror the operations on the system. — *proved proved here* — `UndergradKB.LinearAlgebra.augmented`, `UndergradKB.LinearAlgebra.hefferon_One_I_2_7`, `UndergradKB.LinearAlgebra.solutionSet_rowOp`, `UndergradKB.LinearAlgebra.augmented_mulVec`
- **One.I.2.9**, p.27 [LA-001]: A linear equation $a_1x_1+\dots+a_nx_n=d$ over $\mathbb R$, a system of such equations, and a solution as an $n$-tuple (column vector) satisfying every equation. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_1_1`, `UndergradKB.LinearAlgebra.hefferon_One_I_2_9`
- **One.I.2.10**, p.27 [LA-032]: Addition in F^n is coordinatewise. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_13`
- **One.I.2.11**, p.27 [LA-035]: Scalar multiplication on F^n multiplies each coordinate by the scalar. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_18`, `Pi.module`
- **One.I.3.1**, p.34 [LA-017]: The solution set of any linear system is $\{p+c_1\beta_1+\dots+c_k\beta_k\}$ with $p$ a particular solution and $k$ the number of free variables after Gauss reduction ("general = particular + homogeneous"). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_1`
- **One.I.3.2**, p.34 [LA-018]: A linear equation is homogeneous if its constant is $0$; the homogeneous system associated to a system has the same coefficients and zero constants, and always has the zero vector as a solution. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_2`
- **One.I.3.6**, p.35 [LA-019]: The solution set of a homogeneous system is $\{c_1\beta_1+\dots+c_k\beta_k\}$ for some vectors $\beta_i$, where $k$ is the number of free variables of an echelon form. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_6`, `UndergradKB.LinearAlgebra.exists_homog_basis`
- **One.I.3.Span**, p.37 [LA-062]: The span of a list is the set of all its linear combinations; the span of the empty list is {0}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_4`, `Submodule.span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_empty`
- **One.I.3.7**, p.38 [LA-020]: For a particular solution $p$ of a linear system, the solution set equals $\{p+h\}$ where $h$ ranges over solutions of the associated homogeneous system. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_I_3_7`, `LinearMap.sub_mem_ker_iff`, `Matrix.mulVec_add`, `Matrix.mulVec_zero`
- **One.I.3.10**, p.39 [LA-021]: The solution set of a linear system is empty, a single point, or infinite. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_10`
- **One.I.3.11**, p.40 [LA-022]: A square matrix is nonsingular if it is the coefficient matrix of a homogeneous system with a unique solution (the zero vector), and singular otherwise. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_11`
- **One.I.3.Remark**, p.41 [LA-023]: For a square system the coefficient matrix being nonsingular means a unique solution for every right-hand side; a singular matrix never gives exactly one solution. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_I_3_Remark`, `Matrix.mulVec_injective_iff_isUnit`, `Matrix.mulVec_surjective_iff_isUnit`

#### Section One.II

- **One.II.1.Flat**, p.50 [LA-024]: A $k$-flat (linear surface) in $\mathbb R^n$ is a set $\{p+t_1v_1+\dots+t_kv_k\}$; a hyperplane is an $(n-1)$-flat. — *proved proved here* — `UndergradKB.LinearAlgebra.IsFlat`, `UndergradKB.LinearAlgebra.hefferon_One_II_1_flat`
- **One.II.1.Geometry**, p.51 [LA-017]: The solution set of any linear system is $\{p+c_1\beta_1+\dots+c_k\beta_k\}$ with $p$ a particular solution and $k$ the number of free variables after Gauss reduction ("general = particular + homogeneous"). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_I_3_1`
- **One.II.2.1**, p.52 [LA-337]: The norm of $v$ is $\sqrt{\langle v,v\rangle}$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_7`, `InnerProductSpace.Core.toNormedAddCommGroup`, `real_inner_self_eq_norm_sq`, `inner_self_eq_norm_sq_to_K`
- **One.II.2.3**, p.53 [LA-333]: The dot product on $\mathbf R^n$ is $x\cdot y=\sum x_iy_i$; it is positive definite, linear in $x$, and symmetric. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_1`, `dotProduct`, `EuclideanSpace.inner_eq_star_dotProduct`
- **One.II.2.Normalize**, p.53 [LA-338]: A nonzero vector divided by its length has length one (normalization). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_Normalize`, `norm_smul_inv_norm`
- **One.II.2.5**, p.54 [LA-346]: Triangle inequality $\lVert u+v\rVert\le\lVert u\rVert+\lVert v\rVert$, with equality iff one vector is a nonnegative real multiple of the other. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_17`, `norm_add_le`, `sameRay_iff_norm_add`, `norm_add_eq_iff_real`
- **One.II.2.6**, p.55 [LA-344]: Cauchy-Schwarz: $\lvert\langle u,v\rangle\rvert\le\lVert u\rVert\lVert v\rVert$, with equality iff one vector is a scalar multiple of the other. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_14`, `norm_inner_le_norm`, `abs_real_inner_le_norm`, `norm_inner_eq_norm_iff`
- **One.II.2.7**, p.56 [LA-349]: The angle between nonzero vectors $u,v\in\mathbb R^n$ is $\arccos\big(u\cdot v/(\lVert u\rVert\lVert v\rVert)\big)$ (a right angle if either is zero), well defined by Cauchy-Schwarz. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_7`, `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_7_zero`, `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_7_wd`, `InnerProductGeometry.angle`
- **One.II.2.8**, p.56 [LA-350]: Vectors in $\mathbb R^n$ are orthogonal iff their dot product is zero, and parallel (same direction) iff the dot product equals the product of their lengths. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_8_orth`, `UndergradKB.LinearAlgebra.Course.hefferon_One_II_2_8_par`, `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`, `inner_eq_norm_mul_iff_real`
- **One.II.2.Ex18**, p.57 [LA-333]: The dot product on $\mathbf R^n$ is $x\cdot y=\sum x_iy_i$; it is positive definite, linear in $x$, and symmetric. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_1`, `dotProduct`, `EuclideanSpace.inner_eq_star_dotProduct`
- **One.II.2.Ex19**, p.57 [LA-344]: Cauchy-Schwarz: $\lvert\langle u,v\rangle\rvert\le\lVert u\rVert\lVert v\rVert$, with equality iff one vector is a scalar multiple of the other. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_14`, `norm_inner_le_norm`, `abs_real_inner_le_norm`, `norm_inner_eq_norm_iff`

#### Section One.III

- **One.III.1.3**, p.61 [LA-009]: A matrix or system is in reduced echelon form if it is in echelon form, every leading entry is 1, and each leading entry is the only nonzero entry in its column. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_III_1_3`, `Matrix.IsReducedRowEchelon`
- **One.III.1.GaussJordan**, p.61 [LA-010]: Gauss-Jordan reduction: after reaching echelon form, scale each leading entry to 1 and clear its column upward; this brings any matrix to reduced echelon form and lets one read off the solution set. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_III_1_GaussJordan`
- **One.III.1.5**, p.62 [LA-004]: Elementary row operations are reversible: each operation can be undone by another elementary operation (swap by swap, scaling by $1/k$, adding $kr_i$ to $r_j$ by adding $-kr_i$; needs $i\ne j$). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_III_1_5`
- **One.III.1.6**, p.63 [LA-012]: Row reducibility is an equivalence relation on matrices of a given size (reflexive by zero operations, symmetric by reversibility, transitive by concatenation), so matrices partition into row-equivalence classes. — *in Mathlib* — `Matrix.RowEquivalent.refl`, `symm`, `trans`
- **One.III.1.7**, p.63 [LA-011]: Two matrices are row equivalent if each can be reduced to the other by elementary row operations. — *in Mathlib* — `Matrix.RowEquivalent`
- **One.III.2.3**, p.67 [LA-063]: Linear Combination Lemma: a linear combination of linear combinations of $x_1,\dots,x_n$ is a linear combination of $x_1,\dots,x_n$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_One_III_2_3`, `Finsupp.linearCombination_linearCombination`, `Submodule.span_span`
- **One.III.2.4**, p.67 [LA-013]: If one matrix is obtained from another by row operations, each row of the second is a linear combination of the rows of the first. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_III_2_4`, `UndergradKB.LinearAlgebra.rowEquivalent_vecMul`
- **One.III.2.5**, p.68 [LA-014]: In an echelon form matrix no nonzero row is a linear combination of the other nonzero rows (the nonzero rows are linearly independent). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_4`, `UndergradKB.LinearAlgebra.nonzeroRows_linearIndependent`
- **One.III.2.6**, p.69 [LA-015]: Every matrix is row equivalent to a unique reduced echelon form matrix, so reduced echelon form is a canonical form for row equivalence. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_III_2_6`, `UndergradKB.LinearAlgebra.eq_of_rowEquivalent_of_reduced`
- **One.III.2.7**, p.70 [LA-016]: Two echelon forms derived from one system by Gauss's Method have the same free variables (the set of free variables is unique, although the choice of parameters is not). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_One_III_2_7`, `UndergradKB.LinearAlgebra.IsFreeColumn`

## Chapter Two

71 items; 71 with a Lean name; 22 proved proved here; 49 in Mathlib.


#### Section Two.I

- **Two.I.1.1**, p.94 [LA-036]: A vector space over F is a set with addition and scalar multiplication satisfying commutativity, associativity, additive identity and inverses, multiplicative identity, and both distributive laws; elements are vectors. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_19`, `Module`, `AddCommGroup`, `AddCommMonoid`
- **Two.I.1.4**, p.97 [LA-031]: F^n is the set of all lists of n elements of F; the k-th entry is the k-th coordinate. — *in Mathlib* — `Pi.module`, `Fin.cons`
- **Two.I.1.6**, p.97 [LA-044]: A one-element vector space is called a trivial space; every vector space has at least its zero vector. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_I_1_6`, `Subsingleton`, `Unique`, `Module`
- **Two.I.1.7**, p.98 [LA-044]: A one-element vector space is called a trivial space; every vector space has at least its zero vector. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_I_1_6`, `Subsingleton`, `Unique`, `Module`
- **Two.I.1.8**, p.98 [LA-070]: P_m(F) is the set of polynomials of degree at most m, a subspace of P(F). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_12`, `Polynomial.degreeLE`, `Polynomial.degreeLT`
- **Two.I.1.9**, p.99 [LA-133]: Matrix addition and scalar multiplication are entrywise. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_34`, `Matrix.add_apply`, `Matrix.smul_apply`
- **Two.I.1.10**, p.99 [LA-038]: F^infinity denotes the set of all infinite sequences of elements of F, a vector space under termwise operations. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_23`, `Pi.module`
- **Two.I.1.11**, p.100 [LA-067]: A polynomial over F is a function p with p(z)=a0+a1 z+...+am z^m; P(F) is the set of all of them, a vector space. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_10`
- **Two.I.1.12**, p.100 [LA-039]: For any set S, the set F^S of functions S -> F is a vector space under pointwise addition and scalar multiplication. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_25`, `Pi.module`, `Function.module`
- **Two.I.1.15**, p.101 [LA-049]: The solution set of a homogeneous linear system in n unknowns is a vector space under the operations inherited from R^n. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_I_1_15`, `LinearMap.ker`, `Matrix.mulVecLin`
- **Two.I.1.16**, p.102 [LA-042]: The scalar 0 times any vector v is the zero vector. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_30`, `zero_smul`
- **Two.I.2.1**, p.106 [LA-047]: A subspace of V is a subset that is itself a vector space with the inherited operations. — *in Mathlib* — `Submodule`
- **Two.I.2.4**, p.107 [LA-050]: Every vector space has the trivial subspace {0} and itself as subspaces; a subspace other than the whole space is proper. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_I_2_4`, `Submodule.mem_bot`, `Submodule.mem_top`, `le_top`
- **Two.I.2.9**, p.108 [LA-051]: For a nonempty subset S: S is a subspace iff it is closed under linear combinations of pairs iff it is closed under linear combinations of any finite number of vectors. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_I_2_9`
- **Two.I.2.13**, p.110 [LA-062]: The span of a list is the set of all its linear combinations; the span of the empty list is {0}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_4`, `Submodule.span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_empty`
- **Two.I.2.14**, p.110 [LA-062]: The span of a list is the set of all its linear combinations; the span of the empty list is {0}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_4`, `Submodule.span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_empty`
- **Two.I.2.15**, p.110 [LA-064]: The span of a list is the smallest subspace containing every vector of the list. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_6`, `Submodule.span_le`, `Submodule.subset_span`, `Submodule.span_induction`
- **Two.I.2.converse**, p.111 [LA-064]: The span of a list is the smallest subspace containing every vector of the list. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_6`, `Submodule.span_le`, `Submodule.subset_span`, `Submodule.span_induction`
- **Two.I.2.smallest**, p.111 [LA-064]: The span of a list is the smallest subspace containing every vector of the list. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_6`, `Submodule.span_le`, `Submodule.subset_span`, `Submodule.span_induction`
- **Two.I.2.19**, p.112 [LA-099]: The subspaces of R^3 are exactly the zero subspace, the lines through the origin, the planes through the origin, and R^3 itself. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_2_11`

#### Section Two.II

- **Two.II.1.2**, p.119 [LA-081]: Adding v to a set S leaves the span unchanged iff v lies in the span of S; so removing an element v of S keeps the span iff v is in the span of the others. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_II_1_2`, `UndergradKB.LinearAlgebra.hefferon_Two_II_1_3`
- **Two.II.1.3**, p.119 [LA-081]: Adding v to a set S leaves the span unchanged iff v lies in the span of S; so removing an element v of S keeps the span iff v is in the span of the others. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_II_1_2`, `UndergradKB.LinearAlgebra.hefferon_Two_II_1_3`
- **Two.II.1.4**, p.119 [LA-073]: A list is linearly independent if the only scalars with sum a_k v_k = 0 are all zero. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_15`, `LinearIndependent`, `Fintype.linearIndependent_iff`, `linearIndependent_iff'`
- **Two.II.1.5**, p.120 [LA-073]: A list is linearly independent if the only scalars with sum a_k v_k = 0 are all zero. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_15`, `LinearIndependent`, `Fintype.linearIndependent_iff`, `linearIndependent_iff'`
- **Two.II.1.11**, p.122 [LA-075]: The empty set is linearly independent, and any set containing the zero vector is linearly dependent. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_II_1_11`, `linearIndependent_empty`, `linearIndependent_empty_type`, `LinearIndependent.ne_zero`
- **Two.II.1.12**, p.122 [LA-075]: The empty set is linearly independent, and any set containing the zero vector is linearly dependent. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_II_1_11`, `linearIndependent_empty`, `linearIndependent_empty_type`, `LinearIndependent.ne_zero`
- **Two.II.1.14**, p.123 [LA-076]: A set is linearly independent iff removing any one of its vectors strictly shrinks the span; so a spanning set is minimal iff it is linearly independent. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_II_1_14`, `linearIndependent_iff_notMem_span`, `Submodule.span_mono`
- **Two.II.1.15**, p.123 [LA-077]: If S is linearly independent and v is not in S then S together with v is independent iff v is not in the span of S. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_II_1_15`, `linearIndepOn_id_insert`, `LinearIndepOn.id_insert`, `linearIndepOn_insert`
- **Two.II.1.17**, p.125 [LA-087]: Every spanning list in a vector space can be reduced to a basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_30`, `Module.Basis.ofSpan`, `Module.Basis.ofSpan_subset`
- **Two.II.1.19**, p.126 [LA-080]: Linear dependence lemma: a dependent list has some vk in the span of earlier vectors, and removing it leaves the span unchanged. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_19`
- **Two.II.1.20**, p.126 [LA-079]: Any subset of a linearly independent set is independent; any superset of a linearly dependent set is dependent. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_II_1_20`, `LinearIndepOn.mono`, `LinearIndependent.comp`
- **Two.II.1.maximal**, p.127 [LA-078]: A linearly independent set is maximal (no independent proper superset) iff it spans the whole space. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_II_1_maximal`

#### Section Two.III

- **Two.III.1.1**, p.131 [LA-084]: A basis of V is a list that is linearly independent and spans V. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_26`, `Module.Basis`, `Module.Basis.mk`
- **Two.III.1.5**, p.132 [LA-085]: Standard bases: e_1..e_n of F^n, and 1,z,...,z^m for P_m(F). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_27`
- **Two.III.1.7**, p.132 [LA-085]: Standard bases: e_1..e_n of F^n, and 1,z,...,z^m for P_m(F). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_27`
- **Two.III.1.8**, p.132 [LA-095]: The trivial space has the empty basis and dimension 0. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_III_1_8`, `Module.Basis.empty`, `Module.finrank_zero_of_subsingleton`, `finrank_bot`
- **Two.III.1.9**, p.132 [LA-085]: Standard bases: e_1..e_n of F^n, and 1,z,...,z^m for P_m(F). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_27`
- **Two.III.1.12**, p.133 [LA-086]: A list is a basis iff every vector can be written uniquely as a linear combination of it. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_28`, `Module.Basis.mk`
- **Two.III.1.13**, p.134 [LA-181]: The matrix of a vector with respect to a basis is the column of its coordinates. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_73`, `Module.Basis.equivFun`
- **Two.III.1.18**, p.135 [LA-182]: Relative to a basis B, a linear relationship a1 v1+...+ak vk = 0 holds among vectors iff the same relationship holds among their coordinate columns. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_1_18`
- **Two.III.2.1**, p.139 [LA-066]: A vector space is finite-dimensional if some list of vectors spans it. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_9`, `Module.Finite`, `FiniteDimensional`, `Submodule.fg_def`
- **Two.III.2.3**, p.140 [LA-092]: Exchange Lemma: if B is a basis and v = sum c_i b_i with c_i nonzero, replacing b_i by v gives another basis. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_2_3`
- **Two.III.2.4**, p.141 [LA-091]: Any two bases of a finite-dimensional vector space have the same length. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_34`, `Module.finrank_eq_card_basis`, `Module.Basis.mk_eq_rank`
- **Two.III.2.5**, p.141 [LA-093]: The dimension of a finite-dimensional vector space is the length of any basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_35`, `Module.finrank`, `Module.rank`
- **Two.III.2.6**, p.141 [LA-094]: dim F^n = n and dim P_m(F) = m+1, plus dimensions of some concrete subspaces of F^3. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_36`
- **Two.III.2.7**, p.141 [LA-094]: dim F^n = n and dim P_m(F) = m+1, plus dimensions of some concrete subspaces of F^3. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_36`
- **Two.III.2.9**, p.141 [LA-095]: The trivial space has the empty basis and dimension 0. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_III_1_8`, `Module.Basis.empty`, `Module.finrank_zero_of_subsingleton`, `finrank_bot`
- **Two.III.2.10**, p.142 [LA-082]: In a vector space, the length of any linearly independent list is at most the length of any spanning list. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_22`, `linearIndependent_le_span`, `linearIndependent_le_span'`, `LinearIndependent.finite_of_le_span_finite`
- **Two.III.2.11**, p.142 [LA-099]: The subspaces of R^3 are exactly the zero subspace, the lines through the origin, the planes through the origin, and R^3 itself. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_2_11`
- **Two.III.2.12**, p.142 [LA-089]: Every linearly independent list in a finite-dimensional space extends to a basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_32`, `Module.Basis.extend`, `Module.Basis.sumExtend`, `Module.Basis.subset_extend`
- **Two.III.2.13**, p.142 [LA-087]: Every spanning list in a vector space can be reduced to a basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_30`, `Module.Basis.ofSpan`, `Module.Basis.ofSpan_subset`
- **Two.III.2.14**, p.142 [LA-097]: In a finite-dimensional space, a linearly independent list of length dim V is a basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_38`, `LinearIndependent.span_eq_top_of_card_eq_finrank`, `basisOfLinearIndependentOfCardEqFinrank`
- **Two.III.3.1**, p.146 [LA-154]: Column rank is the dimension of the span of the columns; row rank is that of the rows. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_52`, `Matrix.rank`, `Matrix.cRank`, `Matrix.rank_eq_finrank_span_cols`
- **Two.III.3.3**, p.146 [LA-155]: Row operations do not change the row space of a matrix, so row-equivalent matrices have equal row spaces and equal row rank. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_3`
- **Two.III.3.4**, p.147 [LA-156]: The nonzero rows of an echelon form matrix form a linearly independent set. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_4`
- **Two.III.3.5**, p.147 [LA-157]: Gauss's Method applied to a matrix produces a basis for its row space, namely the nonzero rows of the echelon form. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_5`
- **Two.III.3.6**, p.147 [LA-154]: Column rank is the dimension of the span of the columns; row rank is that of the rows. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_52`, `Matrix.rank`, `Matrix.cRank`, `Matrix.rank_eq_finrank_span_cols`
- **Two.III.3.8**, p.148 [LA-159]: The transpose $A^t$ has $(A^t)_{k,j}=A_{j,k}$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_54`, `Matrix.transpose`, `Matrix.transpose_apply`, `Matrix.transpose_transpose`
- **Two.III.3.10**, p.149 [LA-158]: Row operations do not change the column rank of a matrix. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_10`, `UndergradKB.LinearAlgebra.rank_eq_of_rowEquivalent`
- **Two.III.3.11**, p.150 [LA-161]: Column rank equals row rank. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_57`, `Matrix.rank_transpose`, `Matrix.rank_eq_finrank_span_row`
- **Two.III.3.12**, p.150 [LA-162]: The rank of a matrix is its column rank. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_58`, `Matrix.rank`, `Matrix.cRank_toNat_eq_rank`, `Matrix.rank_eq_finrank_span_cols`
- **Two.III.3.13**, p.150 [LA-120]: Fundamental theorem of linear maps (rank-nullity): $\dim V=\dim\operatorname{null}T+\dim\operatorname{range}T$ for finite-dimensional V. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_21`, `LinearMap.finrank_range_add_finrank_ker`, `LinearMap.rank_range_add_rank_ker`
- **Two.III.3.14**, p.151 [LA-201]: For an n by n matrix A these are equivalent: rank n, nonsingular, rows independent, columns independent, every system with matrix A has exactly one solution. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_3_14`
- **Two.III.4.1**, p.154 [LA-052]: The sum of subspaces V1+...+Vm is the set of all sums v1+...+vm with vk in Vk. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_36`, `UndergradKB.LinearAlgebra.Course.axler_1_36_finite`, `Submodule.add_eq_sup`, `Submodule.mem_sup`
- **Two.III.4.7**, p.156 [LA-057]: The concatenation of sequences of vectors adjoins them into a single sequence. — *in Mathlib* — `Fin.append`
- **Two.III.4.8**, p.156 [LA-058]: If V = W1+...+Wk with bases Bi of Wi, these are equivalent: decompositions are unique; the concatenation of the Bi is a basis of V; nonzero vectors from different Wi satisfy only trivial relations. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Two_III_4_8`
- **Two.III.4.9**, p.157 [LA-059]: A collection of subspaces is independent if no nonzero vector of any Wi is a linear combination of vectors from the other subspaces. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_III_4_9`, `iSupIndep`
- **Two.III.4.10**, p.158 [LA-054]: The sum V1+...+Vm is direct, written with circled plus, if each element has exactly one expression as a sum of vectors from the Vk. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_41`, `DirectSum.IsInternal`, `iSupIndep`, `DirectSum.Decomposition`
- **Two.III.4.13**, p.158 [LA-226]: A sum of finite-dimensional subspaces is direct iff the dimension of the sum equals the sum of the dimensions. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_3_94`
- **Two.III.4.14**, p.158 [LA-060]: Two subspaces whose direct sum is V are called complements. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Two_III_4_14`, `UndergradKB.LinearAlgebra.Course.hefferon_Two_III_4_14_iff`, `IsCompl`, `Submodule.exists_isCompl`
- **Two.III.4.15**, p.158 [LA-056]: For subspaces U and W, U+W is direct iff U intersect W is {0}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_46`, `UndergradKB.LinearAlgebra.Course.axler_1_46_isCompl`, `DirectSum.isInternal_submodule_iff_isCompl`, `Submodule.disjoint_def`

## Topic-Fields

1 items; 1 with a Lean name; 1 in Mathlib.

- **Topic-Fields.1**, p.163 [LA-029]: A field is a set with addition and multiplication that are commutative, associative, distributive, with identities and additive and multiplicative inverses; examples are R, Q, C and the two-element set. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Fields_1`, `Field`, `Semifield`

## Topic-Voting

3 items; 3 with a Lean name; 1 proved proved here; 2 in Mathlib.

- **Topic-Voting.2**, p.171 [LA-375]: For a finite-dimensional subspace $U$, $V=U\oplus U^\perp$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_49`, `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`, `Submodule.sup_orthogonal_of_hasOrthogonalProjection`, `Submodule.exists_add_mem_mem_orthogonal`
- **Topic-Voting.1**, p.173 [LA-605]: Voting-paradox necessary condition: after cancelling opposite preference orders, a majority cycle can occur only if the three remaining sets of preference lists all have the same spin. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Voting_1`
- **Topic-Voting.Ex6**, p.174 [LA-374]: $U^\perp$ is a subspace, $\{0\}^\perp=V$, $V^\perp=\{0\}$, $U\cap U^\perp\subseteq\{0\}$, and $G\subseteq H$ implies $H^\perp\subseteq G^\perp$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_48`, `Submodule.orthogonal`, `Submodule.bot_orthogonal_eq_top`, `Submodule.top_orthogonal_eq_bot`

## Topic-DimAnalysis

2 items; 1 with a Lean name; 1 proved proved here; 1 not a result.

- **Topic-DimAnalysis.1**, p.177 [LA-606]: Buckingham's Theorem: a complete relationship among quantities with dimensional formulas can be rewritten as f of a complete set of dimensionless products equal to zero. — *not a result* — –
- **Topic-DimAnalysis.2**, p.178 [LA-607]: The dimensionless products of given quantities form a vector space (multiplication as addition, raising to a power as scalar multiplication); a complete set is a basis, found as a solution space of a homogeneous system. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_DimAnalysis_2`, `UndergradKB.LinearAlgebra.dimMonomial`

## Chapter Three

98 items; 98 with a Lean name; 29 proved proved here; 69 in Mathlib.


#### Section Three.I

- **Three.I.1.3**, p.185 [LA-174]: An isomorphism is an invertible linear map; two spaces are isomorphic if an isomorphism exists between them. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_69`, `LinearEquiv`, `Nonempty`
- **Three.I.1.6**, p.187 [LA-177]: Being isomorphic is an equivalence relation on vector spaces (identity is an isomorphism, inverses and composites of isomorphisms are isomorphisms). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_I_2_2`
- **Three.I.1.7**, p.187 [LA-175]: An automorphism is an isomorphism of a vector space with itself. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_I_1_7`, `LinearEquiv`, `LinearEquiv.automorphismGroup`, `LinearMap.GeneralLinearGroup`
- **Three.I.1.10**, p.189 [LA-110]: Every linear map sends $0$ to $0$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_10`, `map_zero`, `LinearMap.map_zero`
- **Three.I.1.11**, p.189 [LA-103]: A map between vector spaces is linear iff it preserves linear combinations of two vectors iff it preserves finite linear combinations (induction on the number of summands). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_I_1_11`
- **Three.I.2.1**, p.193 [LA-176]: The inverse of an isomorphism is again an isomorphism (the inverse map is linear). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_I_2_1`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_I_2_1_inverse`, `LinearEquiv.symm`, `LinearMap.inverse`
- **Three.I.2.2**, p.194 [LA-177]: Being isomorphic is an equivalence relation on vector spaces (identity is an isomorphism, inverses and composites of isomorphisms are isomorphisms). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_I_2_2`
- **Three.I.2.3**, p.195 [LA-178]: Finite-dimensional spaces over F are isomorphic iff they have the same dimension. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_70`, `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`, `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`, `LinearEquiv.finrank_eq`
- **Three.I.2.4**, p.195 [LA-178]: Finite-dimensional spaces over F are isomorphic iff they have the same dimension. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_70`, `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`, `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`, `LinearEquiv.finrank_eq`
- **Three.I.2.5**, p.195 [LA-183]: For a basis B of an n-dimensional space V, the coordinate map Rep_B sending a vector to its coefficient column is an isomorphism V to R^n. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_I_2_5`, `Module.Basis.equivFun`
- **Three.I.2.8**, p.197 [LA-184]: Each finite-dimensional vector space is isomorphic to exactly one R^n (n its dimension). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_I_2_8`, `LinearEquiv.finrank_eq`, `Module.finrank_fintype_fun_eq_card`, `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`

#### Section Three.II

- **Three.II.1.1**, p.201 [LA-102]: A linear map $T:V\to W$ is a function that is additive and homogeneous: $T(u+v)=Tu+Tv$, $T(\lambda v)=\lambda Tv$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_1`, `LinearMap`, `IsLinearMap`
- **Three.II.1.4**, p.202 [LA-104]: The zero map and the identity operator are linear maps (differentiation, integration, multiplication by x^2, shifts etc. are further examples). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_3`, `LinearMap.id`, `LinearMap.id_apply`, `LinearMap.zero_apply`
- **Three.II.1.6**, p.203 [LA-110]: Every linear map sends $0$ to $0$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_10`, `map_zero`, `LinearMap.map_zero`
- **Three.II.1.7**, p.203 [LA-103]: A map between vector spaces is linear iff it preserves linear combinations of two vectors iff it preserves finite linear combinations (induction on the number of summands). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_I_1_11`
- **Three.II.1.9**, p.203 [LA-105]: Linear map lemma: for a basis $v_1..v_n$ of V and any $w_1..w_n$ in W there is exactly one linear map with $Tv_k=w_k$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_4`, `Module.Basis.constr`, `Module.Basis.constr_basis`, `Module.Basis.ext`
- **Three.II.1.10**, p.204 [LA-105]: Linear map lemma: for a basis $v_1..v_n$ of V and any $w_1..w_n$ in W there is exactly one linear map with $Tv_k=w_k$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_4`, `Module.Basis.constr`, `Module.Basis.constr_basis`, `Module.Basis.ext`
- **Three.II.1.12**, p.205 [LA-267]: An operator is a linear map from a vector space to itself. — *in Mathlib* — `Module.End`
- **Three.II.1.15**, p.205 [LA-104]: The zero map and the identity operator are linear maps (differentiation, integration, multiplication by x^2, shifts etc. are further examples). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_3`, `LinearMap.id`, `LinearMap.id_apply`, `LinearMap.zero_apply`
- **Three.II.1.17**, p.205 [LA-107]: The set $\mathcal L(V,W)$ of linear maps with pointwise operations is a vector space. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_6`, `LinearMap.module`, `LinearMap.addCommGroup`, `LinearMap.addCommMonoid`
- **Three.II.2.1**, p.210 [LA-117]: The range of a linear map is a subspace of the codomain. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_18`, `LinearMap.range`
- **Three.II.2.2**, p.210 [LA-119]: The rank of a linear map is the dimension of its range space and its nullity is the dimension of its null space. — *proved proved here* — `UndergradKB.LinearAlgebra.nullity`, `UndergradKB.LinearAlgebra.hefferon_Three_II_2_2`, `UndergradKB.LinearAlgebra.hefferon_Three_II_2_11`
- **Three.II.2.10**, p.214 [LA-113]: The null space of a linear map is a subspace of the domain. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_13`, `LinearMap.ker`
- **Three.II.2.11**, p.214 [LA-119]: The rank of a linear map is the dimension of its range space and its nullity is the dimension of its null space. — *proved proved here* — `UndergradKB.LinearAlgebra.nullity`, `UndergradKB.LinearAlgebra.hefferon_Three_II_2_2`, `UndergradKB.LinearAlgebra.hefferon_Three_II_2_11`
- **Three.II.2.14**, p.215 [LA-120]: Fundamental theorem of linear maps (rank-nullity): $\dim V=\dim\operatorname{null}T+\dim\operatorname{range}T$ for finite-dimensional V. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_21`, `LinearMap.finrank_range_add_finrank_ker`, `LinearMap.rank_range_add_rank_ker`
- **Three.II.2.17**, p.216 [LA-122]: The rank of a linear map is at most the dimension of the domain, with equality iff the nullity is zero. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_II_2_17`
- **Three.II.2.18**, p.216 [LA-123]: A linear map sends a linearly dependent family to a linearly dependent family. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_II_2_18`, `LinearIndependent.of_comp`
- **Three.II.2.20**, p.217 [LA-124]: For a linear map on an n-dimensional space the following are equivalent: injective; has a linear inverse from its range; nullity 0; rank n; carries a basis to a basis of the range. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_II_2_20`
- **Three.II.2.u1**, p.217 [LA-125]: A one-to-one linear map is an isomorphism from its domain onto its range. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_II_2_u1`, `LinearEquiv.ofInjective`
- **Three.II.2.37**, p.219 [LA-126]: A linear map is one-to-one iff it carries linearly independent sets to linearly independent sets (exercise cited in the text). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_II_2_37`

#### Section Three.III

- **Three.III.1.2**, p.224 [LA-131]: The matrix of a linear map with respect to bases of V and W: column $k$ holds the coordinates of $Tv_k$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_31`, `LinearMap.toMatrix`, `LinearMap.toMatrix_apply`, `Matrix.toLin`
- **Three.III.1.5**, p.225 [LA-186]: M(Tv) = M(T) M(v): applying a map corresponds to matrix times coordinate column. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_76`, `LinearMap.toMatrix_mulVec_repr`, `Matrix.repr_toLin`
- **Three.III.1.6**, p.225 [LA-150]: The matrix-vector product of an m-by-n matrix and an n-vector has i-th entry the dot product of row i with the vector. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_III_1_6`, `Matrix.mulVec`, `dotProduct`, `Matrix.mulVec_eq_sum`
- **Three.III.1.u1**, p.229 [LA-151]: A matrix times a column vector is a linear combination of the columns of the matrix with the vector entries as coefficients. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_50`, `Matrix.mulVec_eq_sum`
- **Three.III.2.2**, p.234 [LA-179]: Once bases are fixed, M sends L(V,W) isomorphically onto the space of m-by-n matrices. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_71`, `LinearMap.toMatrix`, `Matrix.toLin`, `LinearMap.toMatrix_toLin`
- **Three.III.2.4**, p.235 [LA-187]: dim range T equals the column rank of M(T) (independent of bases). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_78`, `Matrix.rank_eq_finrank_range_toLin`, `Matrix.rank`, `Matrix.toLin_toMatrix`
- **Three.III.2.u1**, p.235 [LA-132]: Every linear map $F^n\to F^m$ is given by a matrix of scalars (formula in the examples, proved in the exercises); the standard-basis matrix recovers the map. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_ex3A_3`, `LinearMap.toMatrix'`, `Matrix.toLin'`, `Matrix.toLin'_toMatrix'`
- **Three.III.2.6**, p.236 [LA-188]: A linear map represented by a matrix is onto iff the matrix rank equals its number of rows, and one-to-one iff the rank equals its number of columns. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_III_2_6`
- **Three.III.2.7**, p.237 [LA-166]: A linear map is nonsingular iff it is an isomorphism (one-to-one and onto); otherwise it is singular. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_III_2_7`, `UndergradKB.LinearAlgebra.nonsingular_iff_ker_eq_bot`
- **Three.III.2.9**, p.237 [LA-189]: A nonsingular map is represented by a square matrix, and a square matrix represents nonsingular maps iff it is a nonsingular (invertible) matrix. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_III_2_9`, `UndergradKB.LinearAlgebra.hefferon_Three_III_2_9_matrix`

#### Section Three.IV

- **Three.IV.1.3**, p.243 [LA-133]: Matrix addition and scalar multiplication are entrywise. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_34`, `Matrix.add_apply`, `Matrix.smul_apply`
- **Three.IV.1.4**, p.244 [LA-134]: The matrix of a sum or a scalar multiple of linear maps is the sum or scalar multiple of the matrices. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_35`, `LinearMap.toMatrix`
- **Three.IV.1.6**, p.244 [LA-135]: The zero matrix has all entries zero; it represents the zero map with respect to any bases. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_1_6`, `Matrix.zero_apply`, `map_zero`, `LinearMap.toMatrix`
- **Three.IV.1.7**, p.244 [LA-135]: The zero matrix has all entries zero; it represents the zero map with respect to any bases. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_1_6`, `Matrix.zero_apply`, `map_zero`, `LinearMap.toMatrix`
- **Three.IV.2.1**, p.246 [LA-108]: Product of linear maps $ST$ is composition $S\circ T$ and is again linear. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_7`, `LinearMap.comp`, `LinearMap.comp_apply`, `Module.End.mul_eq_comp`
- **Three.IV.2.3**, p.247 [LA-141]: Matrix multiplication: $(AB)_{j,k}=\sum_r A_{j,r}B_{r,k}$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_41`, `Matrix.mul_apply`, `Matrix.mul_apply'`
- **Three.IV.2.7**, p.248 [LA-142]: The matrix of a composite $ST$ is the product of the matrices $\mathcal M(S)\mathcal M(T)$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_43`, `LinearMap.toMatrix_comp`, `LinearMap.toMatrix_mul`, `Matrix.toLin_mul`
- **Three.IV.2.9**, p.250 [LA-144]: Matrix multiplication is not commutative: AB differs from BA in general, and BA may not even be defined. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_2_9`
- **Three.IV.2.10**, p.250 [LA-144]: Matrix multiplication is not commutative: AB differs from BA in general, and BA may not even be defined. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_2_9`
- **Three.IV.2.11**, p.250 [LA-144]: Matrix multiplication is not commutative: AB differs from BA in general, and BA may not even be defined. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_2_9`
- **Three.IV.2.12**, p.250 [LA-143]: Matrix multiplication is associative and distributes over matrix addition on both sides. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_2_12`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_2_13`, `Matrix.mul_assoc`, `Matrix.mul_add`
- **Three.IV.2.13**, p.250 [LA-143]: Matrix multiplication is associative and distributes over matrix addition on both sides. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_2_12`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_2_13`, `Matrix.mul_assoc`, `Matrix.mul_add`
- **Three.IV.3.1**, p.255 [LA-145]: Multiplying any matrix by a zero matrix, on either side, gives a zero matrix. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_1`, `Matrix.zero_mul`, `Matrix.mul_zero`
- **Three.IV.3.2**, p.255 [LA-147]: A unit matrix (matrix unit) has a single entry 1 in position (i,j) and zeros elsewhere. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_2`, `Matrix.single`
- **Three.IV.3.u1**, p.255 [LA-148]: Multiplying on the left by the unit matrix (i,j) copies row j of the multiplicand into row i of the result; multiplying on the right copies column i into column j. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_u1`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_u1'`, `Matrix.single_mul_apply_same`, `Matrix.single_mul_apply_of_ne`
- **Three.IV.3.7**, p.256 [LA-149]: Column $k$ of $AB$ equals $A$ times column $k$ of $B$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_48`, `Matrix.col_mul_eq_mulVec_col`
- **Three.IV.3.8**, p.257 [LA-191]: The main diagonal of a square matrix runs from upper left to lower right. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_8`, `Matrix.diag`
- **Three.IV.3.9**, p.257 [LA-190]: The identity matrix has 1 on the diagonal and 0 elsewhere; M(I) is the identity matrix in any basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_79`, `Matrix.one_apply`, `LinearMap.toMatrix_id`, `Matrix.diagonal`
- **Three.IV.3.10**, p.257 [LA-192]: The identity matrix is a two-sided multiplicative identity for matrix multiplication. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_10`, `Matrix.one_mul`, `Matrix.mul_one`
- **Three.IV.3.11**, p.258 [LA-190]: The identity matrix has 1 on the diagonal and 0 elsewhere; M(I) is the identity matrix in any basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_79`, `Matrix.one_apply`, `LinearMap.toMatrix_id`, `Matrix.diagonal`
- **Three.IV.3.12**, p.258 [LA-193]: A diagonal matrix is a square matrix whose entries off the main diagonal are all 0. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_12`, `Matrix.diagonal`, `Matrix.IsDiag`
- **Three.IV.3.13**, p.258 [LA-194]: Multiplying a matrix on the left by a diagonal matrix rescales its rows; multiplying on the right rescales its columns. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_13`, `Matrix.diagonal_mul`, `Matrix.mul_diagonal`
- **Three.IV.3.14**, p.258 [LA-195]: A permutation matrix is a square matrix with a single 1 in each row and each column and 0 elsewhere. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_14`, `Equiv.Perm.permMatrix`, `PEquiv.toMatrix`, `Matrix.permMatrixHom`
- **Three.IV.3.15**, p.259 [LA-196]: Multiplying on the left by a permutation matrix permutes the rows of a matrix; multiplying on the right permutes its columns. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_15`, `PEquiv.toMatrix_toPEquiv_mul`, `PEquiv.mul_toMatrix_toPEquiv`, `Matrix.swap_mul_apply_left`
- **Three.IV.3.19**, p.260 [LA-197]: The elementary reduction matrices are obtained from the identity by one Gaussian operation: scale row i by k nonzero, swap rows i and j, or add k times row i to row j. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_3_19`, `UndergradKB.LinearAlgebra.IsElementary`
- **Three.IV.3.20**, p.260 [LA-198]: Left multiplication by an elementary reduction matrix performs the corresponding row operation (scaling, swapping, or row combination) on any matrix. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_20_scale`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_20_swap`, `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_3_20_add`, `Matrix.transvection_mul_apply_same`
- **Three.IV.3.23**, p.261 [LA-199]: For any matrix H there are elementary reduction matrices whose product applied to H gives its reduced echelon form. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_3_23`
- **Three.IV.4.1**, p.265 [LA-200]: A square matrix is invertible if some square matrix is a two-sided inverse; (A^{-1})^{-1}=A and (AC)^{-1}=C^{-1}A^{-1}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_80`, `Matrix.inv`, `Matrix.mul_inv_rev`, `Matrix.nonsing_inv_nonsing_inv`
- **Three.IV.4.2**, p.265 [LA-202]: If a matrix has both a left inverse and a right inverse matrix then they are equal. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_4_2`, `left_inv_eq_right_inv`, `Matrix.left_inv_eq_left_inv`, `Matrix.right_inv_eq_left_inv`
- **Three.IV.4.3**, p.266 [LA-203]: A square matrix is invertible if and only if it is nonsingular (the homogeneous system it defines has only the zero solution). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_IV_4_3`, `Matrix.mulVec_injective_iff_isUnit`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.exists_mulVec_eq_zero_iff`
- **Three.IV.4.4**, p.266 [LA-200]: A square matrix is invertible if some square matrix is a two-sided inverse; (A^{-1})^{-1}=A and (AC)^{-1}=C^{-1}A^{-1}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_80`, `Matrix.inv`, `Matrix.mul_inv_rev`, `Matrix.nonsing_inv_nonsing_inv`
- **Three.IV.4.7**, p.268 [LA-204]: A matrix is invertible iff it is a product of elementary reduction matrices; the inverse is obtained by applying the same Gauss-Jordan row steps to the identity. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_4_7`
- **Three.IV.4.11**, p.269 [LA-205]: The 2x2 matrix with rows (a,b) and (c,d) is invertible iff ad-bc is nonzero, and then its inverse is (1/(ad-bc)) times the matrix with rows (d,-b) and (-c,a). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_IV_4_11`

#### Section Three.V

- **Three.V.1.1**, p.272 [LA-207]: The change of basis matrix for bases B and D of V is the matrix of the identity map from B-coordinates to D-coordinates (columns are the D-coordinates of the vectors of B). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_V_1_1`, `Module.Basis.toMatrix`, `LinearMap.toMatrix_id_eq_basis_toMatrix`
- **Three.V.1.3**, p.273 [LA-209]: The change of basis matrix converts coordinates: Rep_{B,D}(id) times Rep_B(v) equals Rep_D(v); conversely a matrix that converts B-coordinates to D-coordinates for all v is that matrix. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_1_3`
- **Three.V.1.5**, p.274 [LA-210]: A matrix changes bases (from a given basis B to some basis) iff it is nonsingular; equivalently a matrix is nonsingular iff it represents the identity map for some pair of bases. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_1_5`
- **Three.V.1.6**, p.275 [LA-210]: A matrix changes bases (from a given basis B to some basis) iff it is nonsingular; equivalently a matrix is nonsingular iff it represents the identity map for some pair of bases. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_1_5`
- **Three.V.2.1**, p.277 [LA-211]: Change of basis: A = C^{-1} B C where C is the matrix of the identity between the two bases. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_84`, `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`, `Module.Basis.toMatrix_mul_toMatrix_flip`
- **Three.V.2.4**, p.280 [LA-212]: Same-sized matrices H and H-hat are matrix equivalent if H-hat = PHQ for some nonsingular P and Q. — *proved proved here* — `UndergradKB.LinearAlgebra.MatrixEquivalent`, `UndergradKB.LinearAlgebra.hefferon_Three_V_2_4`
- **Three.V.2.5**, p.280 [LA-213]: Matrix equivalent matrices represent the same linear map with respect to appropriate pairs of bases. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_2_5`
- **Three.V.2.7**, p.281 [LA-214]: Rank normal form: an m by n matrix of rank k is matrix equivalent to the matrix with k ones on the leading diagonal and zeros elsewhere. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_2_7`, `UndergradKB.LinearAlgebra.rankNormalForm`
- **Three.V.2.9**, p.282 [LA-215]: Two same-sized matrices are matrix equivalent iff they have the same rank (rank classifies equivalence classes). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_2_9`
- **Three.V.2.u1**, p.282 [LA-216]: For a linear map of rank k there are bases B and D in which it sends the first k basis vectors of B to those of D and the rest to 0 (every map is a coordinate projection). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_2_u1`, `UndergradKB.LinearAlgebra.exists_adapted_bases`

#### Section Three.VI

- **Three.VI.1.1**, p.286 [LA-380]: For $u\ne0$, projection onto $\mathrm{span}(u)$ is $v\mapsto\frac{\langle v,u\rangle}{\lVert u\rVert^2}u$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_56`, `Submodule.starProjection_singleton`, `Submodule.starProjection_unit_singleton`
- **Three.VI.1.17**, p.289 [LA-383]: Closest point: for $u\in U$, $\lVert v-P_Uv\rVert\le\lVert v-u\rVert$, with equality iff $u=P_Uv$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_61`, `Submodule.starProjection_minimal`, `Submodule.norm_eq_iInf_iff_inner_eq_zero`, `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`
- **Three.VI.2.1**, p.290 [LA-356]: Vectors v_1,...,v_k in R^n are mutually orthogonal when the dot product of any two distinct ones is 0. — *in Mathlib* — `Pairwise`, `inner`, `Orthonormal`, `Submodule.IsOrtho`
- **Three.VI.2.2**, p.290 [LA-355]: Orthonormal lists are linearly independent. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_25`, `Orthonormal.linearIndependent`
- **Three.VI.2.3**, p.290 [LA-360]: An orthonormal list of length $\dim V$ is an orthonormal basis. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_28`, `basisOfOrthonormalOfCardEqFinrank`, `Orthonormal.linearIndependent`
- **Three.VI.2.5**, p.291 [LA-357]: An orthogonal basis of a vector space is a basis whose vectors are mutually orthogonal. — *proved proved here* — `UndergradKB.LinearAlgebra.IsOrthogonalBasis`, `UndergradKB.LinearAlgebra.IsOrthogonalBasis.exists_orthonormalBasis`
- **Three.VI.2.7**, p.292 [LA-362]: Gram-Schmidt: from a linearly independent list produce an orthonormal list with the same span at each stage. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_32`, `InnerProductSpace.gramSchmidt`, `InnerProductSpace.gramSchmidtNormed`, `InnerProductSpace.gramSchmidt_orthogonal`
- **Three.VI.2.22**, p.294 [LA-361]: For an orthonormal basis: $v=\sum\langle v,e_k\rangle e_k$, Parseval $\lVert v\rVert^2=\sum\lvert\langle v,e_k\rangle\rvert^2$, and $\langle u,v\rangle=\sum\langle u,e_k\rangle\overline{\langle v,e_k\rangle}$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_30`, `OrthonormalBasis.sum_repr'`, `OrthonormalBasis.sum_repr`, `OrthonormalBasis.sum_sq_norm_inner_right`
- **Three.VI.3.1**, p.296 [LA-370]: For V = M direct sum N, the projection of v = m + n into M along N is m (the M-component). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_VI_3_1`, `Submodule.projection`, `Submodule.projectionOnto`, `LinearMap.linearProjOfIsCompl`
- **Three.VI.3.4**, p.298 [LA-372]: The orthogonal complement $U^\perp$ of a set $U$ is the set of vectors orthogonal to every element of $U$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_46`, `Submodule.orthogonal`, `Submodule.mem_orthogonal`, `Submodule.mem_orthogonal'`
- **Three.VI.3.7**, p.299 [LA-375]: For a finite-dimensional subspace $U$, $V=U\oplus U^\perp$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_49`, `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`, `Submodule.sup_orthogonal_of_hasOrthogonalProjection`, `Submodule.exists_add_mem_mem_orthogonal`
- **Three.VI.3.8**, p.300 [LA-382]: If the columns of A form a basis of a subspace M of R^n then orthogonal projection into M is v -> A (A^T A)^(-1) A^T v. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_VI_3_8`
- **Three.VI.3.14**, p.302 [LA-383]: Closest point: for $u\in U$, $\lVert v-P_Uv\rVert\le\lVert v-u\rVert$, with equality iff $u=P_Uv$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_61`, `Submodule.starProjection_minimal`, `Submodule.norm_eq_iInf_iff_inner_eq_zero`, `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`
- **Three.VI.3.22**, p.303 [LA-373]: A vector is orthogonal to every member of a set iff it is orthogonal to every member of the span of that set. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_VI_3_22`, `Submodule.isOrtho_span`, `Submodule.mem_orthogonal`, `Submodule.mem_orthogonal'`
- **Three.VI.3.28**, p.304 [LA-371]: A projection is a linear map t:V->V with t composed with t equal to t; every such t is the projection onto its range along its null space. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Three_VI_3_28`, `LinearMap.IsProj`, `LinearMap.isProj_iff_isIdempotentElem`, `LinearMap.IsIdempotentElem.eq_projection`

## Topic-LineOfBestFit

2 items; 2 with a Lean name; 1 proved proved here; 1 in Mathlib.

- **Topic-LineOfBestFit.1**, p.307 [LA-387]: $x=T^\dagger b$ minimizes $\lVert Tx-b\rVert$, and among minimizers it has least norm. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_6_70`
- **Topic-LineOfBestFit.Ex9**, p.310 [LA-383]: Closest point: for $u\in U$, $\lVert v-P_Uv\rVert\le\lVert v-u\rVert$, with equality iff $u=P_Uv$. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_6_61`, `Submodule.starProjection_minimal`, `Submodule.norm_eq_iInf_iff_inner_eq_zero`, `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`

## Topic-Geometry

2 items; 2 with a Lean name; 1 proved proved here; 1 in Mathlib.

- **Topic-Geometry.1**, p.312 [LA-214]: Rank normal form: an m by n matrix of rank k is matrix equivalent to the matrix with k ones on the leading diagonal and zeros elsewhere. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Three_V_2_7`, `UndergradKB.LinearAlgebra.rankNormalForm`
- **Topic-Geometry.2**, p.314 [LA-217]: A linear map sends every line of R^n (not necessarily through the origin) to a line or a single point. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Geometry_2`, `AffineSubspace.map`, `AffineSubspace.map_span`, `LinearMap.toAffineMap`

## Topic-MagicSquares

3 items; 3 with a Lean name; 3 proved proved here.

- **Topic-MagicSquares.1**, p.319 [LA-137]: An n by n matrix is magic if all rows, columns and both diagonals sum to the same number; the magic squares, and those with magic number 0, each form a subspace of the n by n matrices. — *proved proved here* — `UndergradKB.LinearAlgebra.MagicSquares.magicSquares`, `UndergradKB.LinearAlgebra.MagicSquares.zeroMagicSquares`, `UndergradKB.LinearAlgebra.MagicSquares.mem_magicSquares_iff`, `UndergradKB.LinearAlgebra.MagicSquares.mem_zeroMagicSquares_iff`
- **Topic-MagicSquares.3**, p.319 [LA-139]: The space of n by n magic squares has dimension one more than the zero-magic-number subspace (trace is onto R), giving n^2-2n for n at least 3. — *proved proved here* — `UndergradKB.LinearAlgebra.MagicSquares.hefferon_MagicSquares_3`
- **Topic-MagicSquares.2**, p.320 [LA-138]: For n at least 3 the n by n magic squares with magic number 0 form a space of dimension n^2-2n-1 (the 2n+2 linear constraints have rank 2n+1). — *proved proved here* — `UndergradKB.LinearAlgebra.MagicSquares.hefferon_MagicSquares_2`

## Topic-Markov

1 items; 1 with a Lean name; 1 in Mathlib.

- **Topic-Markov.1**, p.324 [LA-140]: A probability vector has nonnegative entries summing to 1; a transition (stochastic) matrix has nonnegative entries with each column summing to 1, and the chain updates p(n+1) = M p(n). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Markov_1`, `Matrix.colStochastic`, `stdSimplex`, `Matrix.sum_mulVec_of_mem_colStochastic`

## Topic-Orthonormal

6 items; 6 with a Lean name; 4 proved proved here; 2 in Mathlib.

- **Topic-Orthonormal.1**, p.329 [LA-418]: A map f of the plane is distance-preserving (a rigid motion or isometry) if it preserves the distance between all pairs of points; two plane figures are congruent if such a map carries one onto the other. — *in Mathlib* — `Isometry`, `IsometryEquiv`, `Congruent`
- **Topic-Orthonormal.6**, p.329 [LA-419]: Distance-preserving maps of the plane preserve collinearity, betweenness, triangles and circles. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Orthonormal_6`
- **Topic-Orthonormal.2**, p.330 [LA-420]: A distance-preserving map of the plane fixing the origin is linear, so every distance-preserving map of the plane is a distance-preserving linear map plus a translation. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Orthonormal_2`, `Isometry.affineIsometryOfStrictConvexSpace`, `IsometryEquiv.toRealAffineIsometryEquiv`, `IsometryEquiv.toRealLinearIsometryEquivOfMapZero`
- **Topic-Orthonormal.3**, p.331 [LA-415]: For S:V->W equivalent: S isometry; S*S = I; S preserves inner products; S sends an orthonormal list to an orthonormal list; columns of its matrix are orthonormal. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_7_49`
- **Topic-Orthonormal.4**, p.331 [LA-425]: For a square matrix Q equivalent: unitary; rows orthonormal; columns orthonormal; Q* is unitary; Q is invertible with Q^-1 = Q*; etc. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_7_57`
- **Topic-Orthonormal.5**, p.332 [LA-421]: A 2x2 orthonormal matrix with first column (a,b) is a rotation (rows (a,-b),(b,a)) or a reflection (rows (a,b),(b,-a)); every rigid motion is a rotation or reflection followed by a translation. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Orthonormal_5`, `UndergradKB.LinearAlgebra.orthonormal_two_by_two`

## Chapter Four

29 items; 29 with a Lean name; 7 proved proved here; 22 in Mathlib.


#### Section Four.I

- **Four.I.0.1**, p.336 [LA-542]: Determinant formulas for small sizes: a for 1x1, ad-bc for 2x2, and the six-term sum aei+bfg+cdh-hfa-idb-gec for 3x3 (the permutation expansion specializes to them). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_I_3_13`, `Matrix.det_fin_one`, `Matrix.det_fin_two`, `Matrix.det_fin_two_of`
- **Four.I.2.1**, p.342 [LA-543]: An n x n determinant function (of the rows) is one unchanged by adding a multiple of one row to another, negated by a row swap, scaled by scaling a row, and equal to 1 on the identity. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Four_I_2_1`, `UndergradKB.LinearAlgebra.IsDetFunction`
- **Four.I.2.2**, p.342 [LA-529]: Swapping two inputs of an alternating form negates the value; more generally permuting inputs multiplies by the sign. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_30`, `AlternatingMap.map_swap`, `AlternatingMap.map_perm`
- **Four.I.2.4**, p.342 [LA-556]: Row and column operations: equal rows or columns give 0, swapping negates, scaling scales, adding a multiple of another row/column preserves det. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_57`, `Matrix.det_zero_of_row_eq`, `Matrix.det_zero_of_column_eq`, `Matrix.det_permute`
- **Four.I.2.7**, p.344 [LA-544]: For each n there is at most one function on n x n real matrices satisfying the four determinant conditions (its value is forced by Gauss's Method). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Four_I_2_7`, `UndergradKB.LinearAlgebra.IsDetFunction.eq_det`
- **Four.I.3.2**, p.348 [LA-525]: An m-linear form on V is a map V^m -> F linear in each slot; a multilinear form is an m-linear form for some m. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_24`, `MultilinearMap`
- **Four.I.3.3**, p.348 [LA-546]: Columns map v1..vn to det(v1 ... vn) is an alternating n-linear form on F^n. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_45`, `Module.Basis.det`, `Matrix.det_updateCol_add`, `Matrix.det_updateCol_smul`
- **Four.I.3.7**, p.351 [LA-530]: A permutation of {1..m} is a list containing each of 1..m once; perm m denotes the set of them. — *in Mathlib* — `Equiv.Perm`
- **Four.I.3.7b**, p.351 [LA-533]: The permutation matrix P_phi of an n-permutation phi has as rows the unit row vectors iota_phi(1),...,iota_phi(n). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_I_3_7`, `Equiv.Perm.permMatrix`, `Matrix.permMatrixHom`
- **Four.I.3.12**, p.352 [LA-547]: Leibniz formula: det A = sum over permutations of sign times A_{j1,1}...A_{jn,n}. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_46`, `Matrix.det_apply`, `Matrix.det_apply'`
- **Four.I.3.13**, p.352 [LA-542]: Determinant formulas for small sizes: a for 1x1, ad-bc for 2x2, and the six-term sum aei+bfg+cdh-hfa-idb-gec for 3x3 (the permutation expansion specializes to them). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_I_3_13`, `Matrix.det_fin_one`, `Matrix.det_fin_two`, `Matrix.det_fin_two_of`
- **Four.I.3.14**, p.353 [LA-545]: For each n an n x n determinant function exists: the signed permutation sum d(T)=sum sgn(phi) t_{1,phi(1)}...t_{n,phi(n)} satisfies the four conditions. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_I_3_14`, `Matrix.det`, `Matrix.detRowAlternating`, `Matrix.det_apply`
- **Four.I.3.15**, p.353 [LA-555]: det A^t = det A, det T' = det T (dual), det T* = det T (adjoint). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_9_56_transpose`, `UndergradKB.LinearAlgebra.axler_9_56_dual`, `UndergradKB.LinearAlgebra.axler_9_56_adjoint`, `UndergradKB.LinearAlgebra.hefferon_Four_I_3_15`
- **Four.I.3.16**, p.353 [LA-556]: Row and column operations: equal rows or columns give 0, swapping negates, scaling scales, adding a multiple of another row/column preserves det. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_57`, `Matrix.det_zero_of_row_eq`, `Matrix.det_zero_of_column_eq`, `Matrix.det_permute`

#### Section Four.II

- **Four.II.1.0**, p.355 [LA-579]: The signed size of the box formed by columns v1..vn is det(v1..vn) (area of parallelogram = x1y2-x2y1); its volume is the absolute value of the determinant. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_II_1_3`, `MeasureTheory.Measure.addHaar_parallelepiped`, `Module.Basis.det`, `Module.Basis.addHaar`

#### Section Four.I

- **Four.I.4.1**, p.357 [LA-531]: The sign of a permutation is (-1)^N, N the number of inversions. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_32`, `Equiv.Perm.sign`
- **Four.I.4.4**, p.358 [LA-532]: Swapping two entries of a permutation changes its sign. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_34`, `Equiv.Perm.sign_swap`, `Equiv.Perm.sign_mul`
- **Four.I.4.5**, p.359 [LA-534]: A permutation matrix with an odd (even) number of inversions needs an odd (even) number of row swaps to reach I, so det P_phi = sgn(phi) is well defined. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Four_I_4_5`, `UndergradKB.LinearAlgebra.inversions`, `UndergradKB.LinearAlgebra.swapRows`, `UndergradKB.LinearAlgebra.det_permMatrix_eq_pow_inversions`
- **Four.I.4.7**, p.359 [LA-531]: The sign of a permutation is (-1)^N, N the number of inversions. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_32`, `Equiv.Perm.sign`
- **Four.I.4.9**, p.359 [LA-545]: For each n an n x n determinant function exists: the signed permutation sum d(T)=sum sgn(phi) t_{1,phi(1)}...t_{n,phi(n)} satisfies the four conditions. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_I_3_14`, `Matrix.det`, `Matrix.detRowAlternating`, `Matrix.det_apply`
- **Four.I.4.10**, p.362 [LA-555]: det A^t = det A, det T' = det T (dual), det T* = det T (adjoint). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_9_56_transpose`, `UndergradKB.LinearAlgebra.axler_9_56_dual`, `UndergradKB.LinearAlgebra.axler_9_56_adjoint`, `UndergradKB.LinearAlgebra.hefferon_Four_I_3_15`

#### Section Four.II

- **Four.II.1.1**, p.365 [LA-578]: The box (parallelepiped) formed by v1..vn in R^n is the set of combinations t1 v1+...+tn vn with each t_i in the closed interval [0,1]. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_II_1_1`, `parallelepiped`, `Module.Basis.parallelepiped`
- **Four.II.1.3**, p.367 [LA-579]: The signed size of the box formed by columns v1..vn is det(v1..vn) (area of parallelogram = x1y2-x2y1); its volume is the absolute value of the determinant. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_II_1_3`, `MeasureTheory.Measure.addHaar_parallelepiped`, `Module.Basis.det`, `Module.Basis.addHaar`
- **Four.II.1.5**, p.368 [LA-549]: Determinant is multiplicative for operators and for matrices. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_49`, `LinearMap.det_comp`, `Matrix.det_mul`
- **Four.II.1.7**, p.369 [LA-550]: An operator is invertible iff its determinant is nonzero, and det(T^{-1}) = 1/det T. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_50`, `UndergradKB.LinearAlgebra.Course.axler_9_50_inv`, `LinearMap.isUnit_iff_isUnit_det`, `LinearMap.det_eq_zero_iff_ker_ne_bot`

#### Section Four.III

- **Four.III.1.2**, p.374 [LA-557]: The i,j minor of an n x n matrix is the matrix with row i and column j deleted; the i,j cofactor is (-1)^{i+j} times the determinant of the minor. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Four_III_1_2`, `UndergradKB.LinearAlgebra.minorMatrix`, `UndergradKB.LinearAlgebra.cofactor`
- **Four.III.1.5**, p.375 [LA-558]: Laplace expansion: the determinant equals the sum of entries of any row i (or column j) times their cofactors. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Four_III_1_5`
- **Four.III.1.8**, p.376 [LA-559]: The adjoint (adjugate) of a square matrix T is the transpose of its matrix of cofactors. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_III_1_8`, `Matrix.adjugate`, `Matrix.adjugate_apply`, `Matrix.adjugate_def`
- **Four.III.1.9**, p.376 [LA-560]: T adj(T) = adj(T) T = det(T) I; hence if det T is nonzero then T^{-1} = adj(T)/det(T). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Four_III_1_9`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`, `Matrix.inv_def`

## Topic-Cramer

1 items; 1 with a Lean name; 1 in Mathlib.

- **Topic-Cramer.1**, p.380 [LA-561]: Cramer's Rule: if det A is nonzero, A x = b has the unique solution x_i = det(B_i)/det(A), B_i being A with column i replaced by b. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Cramer_1`, `Matrix.cramer`, `Matrix.cramer_apply`, `Matrix.mulVec_cramer`

## Topic-Speed

2 items; 2 with a Lean name; 2 not a result.

- **Topic-Speed.1**, p.382 [LA-562]: The permutation expansion has n! terms, while row reduction computes a determinant in about n^3 arithmetic operations (so reduction is far faster). — *not a result* — `Fintype.card_perm`
- **Topic-Speed.2**, p.384 [LA-562]: The permutation expansion has n! terms, while row reduction computes a determinant in about n^3 arithmetic operations (so reduction is far faster). — *not a result* — `Fintype.card_perm`

## Topic-Chio

1 items; 1 with a Lean name; 1 proved proved here.

- **Topic-Chio.1**, p.387 [LA-563]: Chio's method: if a_{1,1} is nonzero, det A = det(C)/a_{1,1}^{n-2}, where C has i,j entry the 2x2 determinant of rows 1,i+1 and columns 1,j+1. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Chio_1`, `UndergradKB.LinearAlgebra.chioMatrix`

## Topic-Projective

9 items; 9 with a Lean name; 7 proved proved here; 2 in Mathlib.

- **Topic-Projective.1**, p.393 [LA-564]: The projective plane: a point is a nonzero vector of R^3 up to nonzero scalar (a line through the origin); any representative is a homogeneous coordinate vector. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Projective_1`, `Projectivization`, `Projectivization.mk`, `Projectivization.rep`
- **Topic-Projective.2**, p.395 [LA-565]: A projective line is given by a nonzero row vector L up to scalar; the point v lies on L iff the dot product L.v is zero (independent of representatives). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_2`, `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_3`, `UndergradKB.LinearAlgebra.Incident`
- **Topic-Projective.3**, p.395 [LA-565]: A projective line is given by a nonzero row vector L up to scalar; the point v lies on L iff the dot product L.v is zero (independent of representatives). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_2`, `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_3`, `UndergradKB.LinearAlgebra.Incident`
- **Topic-Projective.4**, p.396 [LA-566]: In the projective plane two distinct points lie on exactly one line. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Projective_4`, `Projectivization.line_unique`, `Projectivization.line_unique'`
- **Topic-Projective.5**, p.396 [LA-567]: Duality Principle: interchanging point and line in any true statement of projective plane geometry gives another true statement. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_5`, `UndergradKB.LinearAlgebra.exists_unique_line`, `UndergradKB.LinearAlgebra.incident_comm`
- **Topic-Projective.6**, p.396 [LA-571]: The Euclidean plane z=1 embeds in the projective plane; the remaining (equatorial) points are ideal points forming the line at infinity, where parallel lines meet. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_6`, `UndergradKB.LinearAlgebra.affinePoint`, `UndergradKB.LinearAlgebra.affineLine`, `UndergradKB.LinearAlgebra.lineAtInfinity`
- **Topic-Projective.7**, p.397 [LA-568]: Three projective points are collinear iff the determinant of representative column vectors is zero iff those vectors are linearly dependent; dually three lines are concurrent iff row vectors are dependent. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_7`
- **Topic-Projective.8**, p.397 [LA-570]: Desargues' Theorem: if two triangles are in perspective from a point, the three intersections of corresponding sides are collinear. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_8`
- **Topic-Projective.9**, p.398 [LA-569]: Frame lemma: four projective points, no three collinear, have representatives and a basis B of R^3 in which they are e1, e2, e3, and e1+e2+e3. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Projective_9`

## Topic-Graphics

6 items; 6 with a Lean name; 6 proved proved here.

- **Topic-Graphics.1**, p.402 [LA-572]: A 3x3 matrix acts on homogeneous coordinate vectors, independent of the representative; normalize by dividing by the third coordinate (a,b,c) to (a/c,b/c) to read off the plane point. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_2`, `UndergradKB.LinearAlgebra.dehomogenize`
- **Topic-Graphics.2**, p.403 [LA-572]: A 3x3 matrix acts on homogeneous coordinate vectors, independent of the representative; normalize by dividing by the third coordinate (a,b,c) to (a/c,b/c) to read off the plane point. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_2`, `UndergradKB.LinearAlgebra.dehomogenize`
- **Topic-Graphics.3**, p.404 [LA-573]: Translation by (tx,ty), which is not linear on R^2, is the 3x3 matrix [[1,0,tx],[0,1,ty],[0,0,1]] acting on homogeneous coordinates, so affine motions compose by matrix multiplication. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_3`, `UndergradKB.LinearAlgebra.translationMatrix`, `UndergradKB.LinearAlgebra.homogeneousMatrix`
- **Topic-Graphics.4**, p.404 [LA-574]: Rotation, axis scaling, reflection in y=x or y=-x, and shear are given by 3x3 matrices on homogeneous coordinates, e.g. rotation [[cos,-sin,0],[sin,cos,0],[0,0,1]]. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_4`, `UndergradKB.LinearAlgebra.rotationMatrix`, `UndergradKB.LinearAlgebra.scalingMatrix`, `UndergradKB.LinearAlgebra.reflectDiagMatrix`
- **Topic-Graphics.5**, p.405 [LA-574]: Rotation, axis scaling, reflection in y=x or y=-x, and shear are given by 3x3 matrices on homogeneous coordinates, e.g. rotation [[cos,-sin,0],[sin,cos,0],[0,0,1]]. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_4`, `UndergradKB.LinearAlgebra.rotationMatrix`, `UndergradKB.LinearAlgebra.scalingMatrix`, `UndergradKB.LinearAlgebra.reflectDiagMatrix`
- **Topic-Graphics.6**, p.406 [LA-573]: Translation by (tx,ty), which is not linear on R^2, is the 3x3 matrix [[1,0,tx],[0,1,ty],[0,0,1]] acting on homogeneous coordinates, so affine motions compose by matrix multiplication. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Graphics_3`, `UndergradKB.LinearAlgebra.translationMatrix`, `UndergradKB.LinearAlgebra.homogeneousMatrix`

## Chapter Five

64 items; 64 with a Lean name; 34 proved proved here; 30 in Mathlib.


#### Section Five.I

- **Five.I.1.1**, p.408 [LA-069]: Setting the degree of the zero polynomial to minus infinity makes deg(fg) = deg f + deg g hold for all polynomials. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_I_1_1`, `Polynomial.degree_mul`
- **Five.I.1.2**, p.408 [LA-258]: Division algorithm: for s nonzero there are unique q, r with p = s q + r and deg r < deg s. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_4_9`
- **Five.I.1.4**, p.409 [LA-259]: Dividing p(x) by x - lambda leaves the constant remainder p(lambda). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_I_1_4`, `Polynomial.mod_X_sub_C_eq_C_eval`, `Polynomial.modByMonic_X_sub_C_eq_C_eval`
- **Five.I.1.5**, p.409 [LA-255]: lambda is a zero of p iff p(z) = (z-lambda) q(z) for a polynomial q of degree one less. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_4_6`, `Polynomial.dvd_iff_isRoot`, `Polynomial.mul_divByMonic_eq_iff_isRoot`
- **Five.I.1.6**, p.409 [LA-265]: Over R, constants and linear polynomials are irreducible, a quadratic is irreducible iff its discriminant is negative, and no polynomial of degree 3 or more is irreducible. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_I_1_6`
- **Five.I.1.7**, p.409 [LA-266]: A nonconstant real polynomial factors uniquely as c prod(x-lambda_j) prod(x^2+b_k x+c_k) with b_k^2 < 4c_k. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_4_16`
- **Five.I.1.mult**, p.409 [LA-256]: The multiplicity of a root lambda of p is the largest n such that (x - lambda)^n divides p. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_I_1_mult`, `Polynomial.rootMultiplicity`, `Polynomial.pow_rootMultiplicity_dvd`
- **Five.I.1.irr**, p.409 [LA-264]: A real polynomial is irreducible over the reals if it is not a product of two real polynomials of lower degree. — *in Mathlib* — `Irreducible`, `Polynomial.irreducible_of_degree_eq_one`
- **Five.I.1.11**, p.410 [LA-261]: Fundamental theorem of algebra, second version: a nonconstant complex polynomial factors uniquely as c(z-l1)...(z-lm). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_4_13`, `IsAlgClosed.card_roots_eq_natDegree`, `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`, `Complex.isAlgClosed`
- **Five.I.1.cx**, p.410 [LA-025]: Complex numbers are ordered pairs of reals a+bi with i^2=-1; C is the set of all of them. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_1`, `Complex`, `Complex.I`, `Complex.ext`
- **Five.I.2.arith**, p.410 [LA-026]: Addition and multiplication on C are commutative and associative, have identities 0 and 1, distribute, and every element has an additive inverse and each nonzero element a multiplicative inverse. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_1_3`, `Complex.instField`
- **Five.I.2.stdbasis**, p.411 [LA-085]: Standard bases: e_1..e_n of F^n, and 1,z,...,z^m for P_m(F). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_2_27`

#### Section Five.II

- **Five.II.intro**, p.412 [LA-211]: Change of basis: A = C^{-1} B C where C is the matrix of the identity between the two bases. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_3_84`, `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`, `Module.Basis.toMatrix_mul_toMatrix_flip`
- **Five.II.1.2**, p.414 [LA-218]: Square matrices T and T-hat are similar if T-hat = P T P^{-1} for some nonsingular P (the matrices of one operator in two bases). — *proved proved here* — `UndergradKB.LinearAlgebra.Similar`, `UndergradKB.LinearAlgebra.hefferon_Five_II_1_2`, `UndergradKB.LinearAlgebra.similar_toMatrix`
- **Five.II.1.4**, p.414 [LA-220]: The zero matrix and the identity matrix are each similar only to themselves. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_II_1_4`
- **Five.II.1.15**, p.414 [LA-219]: Similarity of square matrices is reflexive, symmetric and transitive, so an equivalence relation. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_II_1_15`, `IsConj.refl`, `IsConj.symm`, `IsConj.trans`
- **Five.II.1.equiv**, p.415 [LA-221]: Similar matrices are matrix equivalent, but equivalent square matrices need not be similar (the identity and a nonsingular non-identity matrix are equivalent, not similar). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_II_1_equiv`
- **Five.II.2.1**, p.418 [LA-308]: An operator is diagonalizable if it has a diagonal matrix in some basis. — *proved proved here* — `UndergradKB.LinearAlgebra.IsDiagonalizable`, `UndergradKB.LinearAlgebra.isDiag_toMatrix_iff`, `UndergradKB.LinearAlgebra.IsDiagonalizableMatrix`, `UndergradKB.LinearAlgebra.hefferon_Five_II_2_1`
- **Five.II.2.3**, p.418 [LA-314]: The nilpotent shift (a,b,c) to (b,c,0) on F^3 is not diagonalizable. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_5_57`, `UndergradKB.LinearAlgebra.shiftLeft3`, `UndergradKB.LinearAlgebra.hefferon_Five_II_2_3`
- **Five.II.2.4**, p.419 [LA-313]: Diagonalizable iff V has an eigenbasis iff V is the direct sum of the eigenspaces iff the eigenspace dimensions add up to dim V. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_5_55`, `UndergradKB.LinearAlgebra.axler_5_55_c`, `UndergradKB.LinearAlgebra.hefferon_Five_II_2_4`
- **Five.II.3.1**, p.422 [LA-270]: Eigenvalue: a scalar lambda such that Tv = lambda v for some nonzero v. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_5`, `Module.End.HasEigenvalue`, `Module.End.hasEigenvalue_iff`
- **Five.II.3.5**, p.423 [LA-272]: A square matrix T has eigenvalue lambda with eigenvector z (nonzero) when T z = lambda z. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_II_3_5`
- **Five.II.3.6**, p.423 [LA-584]: Similar matrices have the same eigenvalues, but eigenvectors change with the basis (an eigenvector of T goes to P times it for T-hat). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_II_3_6`, `UndergradKB.LinearAlgebra.hasEigenvector_conj`
- **Five.II.3.eigsim**, p.423 [LA-584]: Similar matrices have the same eigenvalues, but eigenvectors change with the basis (an eigenvector of T goes to P times it for T-hat). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_II_3_6`, `UndergradKB.LinearAlgebra.hasEigenvector_conj`

#### Section Five.III

- **Five.III.1.pow**, p.424 [LA-277]: Powers T^m of an operator (T^0 = I, negative powers for invertible T). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_13`, `Module.End.pow_apply`, `Module.End`

#### Section Five.II

- **Five.II.3.7**, p.425 [LA-551]: lambda is an eigenvalue of T iff det(lambda I - T) = 0. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_51`, `Module.End.hasEigenvalue_iff_isRoot_charpoly`, `LinearMap.eval_charpoly`
- **Five.II.3.9**, p.426 [LA-582]: Characteristic polynomial of T is z -> det(zI - T); over C it equals the product of (z - lambda_k)^{d_k}. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_9_62`, `UndergradKB.LinearAlgebra.axler_9_63`, `UndergradKB.LinearAlgebra.hefferon_Five_II_3_9`
- **Five.II.3.10**, p.426 [LA-284]: Every operator on a nonzero finite-dimensional complex vector space has an eigenvalue. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_19`, `Module.End.exists_eigenvalue`
- **Five.II.3.35**, p.426 [LA-583]: The characteristic polynomial of a matrix is unchanged by similarity, so the characteristic polynomial of a map does not depend on the basis used. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_II_3_35`, `Matrix.charpoly_units_conj`, `LinearMap.charpoly_toMatrix`, `LinearMap.charpoly`
- **Five.II.3.12**, p.427 [LA-309]: Eigenspace E(lambda,T) = null(T - lambda I). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_52`, `Module.End.eigenspace`, `Module.End.eigenspace_def`
- **Five.II.3.13**, p.427 [LA-309]: Eigenspace E(lambda,T) = null(T - lambda I). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_52`, `Module.End.eigenspace`, `Module.End.eigenspace_def`
- **Five.II.3.13**, p.428 [LA-311]: Each eigenvalue has geometric multiplicity at least 1 and at most its algebraic multiplicity. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_II_3_13`, `LinearMap.finrank_eigenspace_le`, `Module.End.HasEigenvalue`, `Module.End.hasEigenvalue_iff`
- **Five.II.3.17**, p.428 [LA-310]: The algebraic multiplicity of an eigenvalue is its exponent in the characteristic polynomial; its geometric multiplicity is the dimension of its eigenspace. — *proved proved here* — `UndergradKB.LinearAlgebra.algebraicMultiplicity`, `UndergradKB.LinearAlgebra.geometricMultiplicity`, `UndergradKB.LinearAlgebra.geometricMultiplicity_le_algebraicMultiplicity`, `UndergradKB.LinearAlgebra.algebraicMultiplicity_eq_finrank_maxGenEigenspace`
- **Five.II.3.mult**, p.428 [LA-311]: Each eigenvalue has geometric multiplicity at least 1 and at most its algebraic multiplicity. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_II_3_13`, `LinearMap.finrank_eigenspace_le`, `Module.End.HasEigenvalue`, `Module.End.hasEigenvalue_iff`
- **Five.II.3.18**, p.429 [LA-275]: Eigenvectors for distinct eigenvalues form a linearly independent list. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_11`, `Module.End.eigenvectors_linearIndependent`, `Module.End.eigenvectors_linearIndependent'`, `Module.End.eigenspaces_iSupIndep`
- **Five.II.3.20**, p.429 [LA-315]: An operator with dim V distinct eigenvalues is diagonalizable. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_5_58`

#### Section Five.III

- **Five.III.1.4**, p.435 [LA-459]: For an operator t the ranges of t^j descend and the null spaces ascend, strictly until a first power k at which both stabilize, with k at most dim V. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_III_1_4`
- **Five.III.1.8**, p.437 [LA-460]: On an n-dimensional space the generalized range space is range(t^n) and the generalized null space is null(t^n). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_III_1_8`
- **Five.III.1.12**, p.438 [LA-098]: A subspace U of a finite-dimensional V with dim U = dim V equals V. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_2_39`, `Submodule.eq_top_of_finrank_eq`, `Submodule.eq_of_le_of_finrank_eq`
- **Five.III.2.1**, p.438 [LA-462]: The restriction of t to its generalized range space R-infinity(t) is one-to-one (hence an automorphism). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_III_2_1`
- **Five.III.2.2**, p.439 [LA-461]: V is the direct sum of null T^(dim V) and range T^(dim V) (Fitting decomposition). — *proved proved here* — `UndergradKB.LinearAlgebra.axler_8_5`, `UndergradKB.LinearAlgebra.hefferon_Five_III_2_2`, `UndergradKB.LinearAlgebra.isCompl_ker_pow_range_pow`
- **Five.III.2.7**, p.440 [LA-467]: Definition: an operator is nilpotent if some power of it is zero. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_8_14`, `IsNilpotent`
- **Five.III.2.index**, p.440 [LA-468]: The index of nilpotency of a nilpotent map or matrix is the least power that is zero. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_III_2_index`, `nilpotencyClass`, `IsNilpotent`
- **Five.III.2.11**, p.441 [LA-475]: A t-string generated by v is the list v, t v, ..., t^{k-1} v with t^k v = 0; a t-string basis is a basis formed by concatenating disjoint t-strings. — *proved proved here* — `UndergradKB.LinearAlgebra.IsStringBasis`, `UndergradKB.LinearAlgebra.exists_string_basis`
- **Five.III.2.15**, p.442 [LA-476]: If a space has a t-string basis, the index of nilpotency of t equals the length of the longest string. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_III_2_15`
- **Five.III.2.16**, p.444 [LA-495]: Every nilpotent operator has a Jordan basis. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_8_45`, `UndergradKB.LinearAlgebra.exists_string_basis`
- **Five.III.2.17**, p.445 [LA-496]: Every nilpotent matrix is similar to a matrix of zeros with blocks of subdiagonal ones, unique up to the order of blocks, giving a canonical form for nilpotent similarity classes. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_III_2_17`, `UndergradKB.LinearAlgebra.hefferon_Five_III_2_17_unique`

#### Section Five.IV

- **Five.IV.1.1**, p.450 [LA-278]: Evaluating a polynomial p at an operator T gives p(T) = a0 I + a1 T + ... + am T^m. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_14`, `Polynomial.aeval`, `Polynomial.aeval_def`
- **Five.IV.1.intro**, p.450 [LA-279]: Every square matrix or transformation is annihilated by a nonzero polynomial (degree at most n^2 by counting dimensions of the matrix space). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Five_IV_1_intro`, `UndergradKB.LinearAlgebra.Course.hefferon_Five_IV_1_intro_map`, `IsIntegral.of_finite`, `LinearMap.aeval_self_charpoly`
- **Five.IV.1.4**, p.451 [LA-288]: Minimal polynomial of an operator: the monic polynomial of smallest degree that kills T. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_24`, `minpoly`
- **Five.IV.1.5**, p.451 [LA-287]: For finite-dimensional V and an operator T there is a unique monic polynomial of least degree annihilating T, and its degree is at most dim V. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_5_22`, `UndergradKB.LinearAlgebra.natDegree_minpoly_le_finrank`
- **Five.IV.1.7**, p.452 [LA-281]: (pq)(T) = p(T) q(T), hence p(T) and q(T) commute. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_17`, `Polynomial.aeval_mul`
- **Five.IV.1.8**, p.453 [LA-490]: The minimal polynomial and characteristic polynomial of a map or square matrix have the same roots (the eigenvalues): minimal polynomial divides the characteristic one and each exponent q_i satisfies 1 <= q_i <= p_i. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_IV_1_8`
- **Five.IV.1.9**, p.453 [LA-585]: Cayley-Hamilton: q(T)=0 for the characteristic polynomial q of T (any real or complex space). — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_9_64`, `LinearMap.aeval_self_charpoly`, `Matrix.aeval_self_charpoly`
- **Five.IV.1.10**, p.455 [LA-290]: q(T) = 0 iff q is a polynomial multiple of the minimal polynomial. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_29`, `minpoly.dvd_iff`, `minpoly.dvd`, `minpoly.aeval`
- **Five.IV.1.11**, p.455 [LA-289]: Zeros of the minimal polynomial are exactly the eigenvalues; over C it is a product of linear factors over all eigenvalues. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_5_27a`, `UndergradKB.LinearAlgebra.axler_5_27b`
- **Five.IV.2.1**, p.458 [LA-470]: A nilpotent operator has 0 as its only eigenvalue; over C, if 0 is the only eigenvalue then T is nilpotent. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_8_17_a`, `UndergradKB.LinearAlgebra.axler_8_17_b`, `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_1`
- **Five.IV.2.2**, p.459 [LA-471]: The map t - lambda is nilpotent iff lambda is the only eigenvalue of t (on a nontrivial space). — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_2`, `UndergradKB.LinearAlgebra.hasEigenvalue_of_isNilpotent_sub`
- **Five.IV.2.3**, p.459 [LA-472]: If T - lambda I is similar to N via P, then T is similar to N + lambda I via the same P. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_3`
- **Five.IV.2.6**, p.462 [LA-492]: A Jordan block: a square matrix with constant diagonal lambda, subdiagonal entries 1 and zeros elsewhere (Hefferon puts the ones below the diagonal); its basis strings are Jordan chains. — *proved proved here* — `UndergradKB.LinearAlgebra.jordanBlockLower`, `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_6`
- **Five.IV.2.8**, p.464 [LA-497]: Jordan form: over C every operator has a Jordan basis. — *proved proved here* — `UndergradKB.LinearAlgebra.axler_8_46`
- **Five.IV.2.9**, p.466 [LA-498]: The Jordan form of a complex matrix is unique up to the order of the blocks (blocks sorted by eigenvalue and decreasing length), so it is a canonical form for similarity. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_9`, `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_9_matrix`
- **Five.IV.2.10**, p.466 [LA-268]: A subspace U is invariant under T when T maps U into U. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.axler_5_2`, `Module.End.invtSubmodule`, `Module.End.mem_invtSubmodule`
- **Five.IV.2.11**, p.466 [LA-493]: A subspace is t-invariant iff it is (t - lambda)-invariant for every scalar lambda; hence N-infinity(t - lambda_i) and R-infinity(t - lambda_i) are (t - lambda_j)-invariant. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Five_IV_2_11`

## Topic-Powers

2 items; 2 with a Lean name; 2 proved proved here.

- **Topic-Powers.1**, p.474 [LA-608]: Method of powers: for T with distinct eigenvalues and a strictly dominant ∣lambda_1∣, T^k v / lambda_1^k tends to c_1 zeta_1 when c_1 is nonzero, so norm ratios tend to ∣lambda_1∣ at geometric rate ∣lambda_2/lambda_1∣. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Powers_1`
- **Topic-Powers.2**, p.475 [LA-608]: Method of powers: for T with distinct eigenvalues and a strictly dominant ∣lambda_1∣, T^k v / lambda_1^k tends to c_1 zeta_1 when c_1 is nonzero, so norm ratios tend to ∣lambda_1∣ at geometric rate ∣lambda_2/lambda_1∣. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Powers_1`

## Topic-Recurrence

9 items; 9 with a Lean name; 4 proved proved here; 5 in Mathlib.

- **Topic-Recurrence.1**, p.485 [LA-612]: Closed form (Binet) for the Fibonacci numbers: F(n) = (phi^n - psi^n)/sqrt 5 with phi, psi the roots of x^2 - x - 1. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Recurrence_1`, `Real.coe_fib_eq`, `Real.coe_fib_eq'`
- **Topic-Recurrence.2**, p.486 [LA-609]: The solutions of a homogeneous linear recurrence of order k form a k-dimensional subspace, isomorphic to R^k by taking the first k values. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Topic_Recurrence_2`, `LinearRecurrence.solSpace`, `LinearRecurrence.solSpace_rank`, `LinearRecurrence.mkSol`
- **Topic-Recurrence.3**, p.487 [LA-610]: The companion matrix of a recurrence has characteristic polynomial equal (up to sign) to the polynomial associated with the recurrence. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Recurrence_3`, `UndergradKB.LinearAlgebra.recurrenceCompanion`
- **Topic-Recurrence.4**, p.488 [LA-611]: If the associated polynomial has distinct roots r_1,...,r_k then the sequences r_i^n are independent solutions, so every solution is c_1 r_1^n + ... + c_k r_k^n. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Recurrence_4`
- **Topic-Recurrence.5**, p.489 [LA-613]: For a nonhomogeneous linear recurrence, every solution is a particular solution plus a solution of the associated homogeneous recurrence. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Topic_Recurrence_5`, `UndergradKB.LinearAlgebra.IsNonhomSolution`
- **Appendix.2**, p.503 [LA-168]: A function has a right inverse iff it is onto. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Appendix_2`, `Function.surjective_iff_hasRightInverse`, `Function.Surjective.hasRightInverse`
- **Appendix.1**, p.504 [LA-167]: A function has a left inverse iff it is one-to-one. — *proved proved here* — `UndergradKB.LinearAlgebra.hefferon_Appendix_1`
- **Appendix.3**, p.504 [LA-169]: A function has a two-sided inverse (is a correspondence) iff it is both one-to-one and onto; the inverse is unique and compositions of correspondences are correspondences. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Appendix_3`, `UndergradKB.LinearAlgebra.Course.hefferon_Appendix_3_unique`, `UndergradKB.LinearAlgebra.Course.hefferon_Appendix_3_comp`, `Function.bijective_iff_has_inverse`
- **Appendix.4**, p.505 [LA-170]: Every equivalence relation determines a partition into classes and every partition arises from an equivalence relation, and these correspond bijectively. — *in Mathlib* — `UndergradKB.LinearAlgebra.Course.hefferon_Appendix_4`, `Setoid.isPartition_classes`, `Setoid.mkClasses`, `Setoid.mkClasses_classes`
