/-
==============================================================================
 SkewonThm1Thm2.lean — Theorems 1 and 2, general symbolic proofs, core Lean 4
==============================================================================

 Paper: Solonko, Molozhavenko, Rakhuba,
        "Muon on the Stiefel Manifold Admits an Exact Closed-Form Update"
        (arXiv:2608.06218v1)

 Fully general (universally quantified over all dimensions n, p, q, all
 X ∈ St(n,p) = {X : XᵀX = I}, all skew Y, all tangent B, all directions M),
 self-contained (core Lean 4, no Mathlib), no `sorry`, no `native_decide`.

 CONVENTIONS.  Entries are integers and factors of ½ are cleared: the skew
 part ½(MXᵀ − XMᵀ) appears as MXᵀ − XMᵀ and objectives are doubled — each
 cleared statement is algebraically equivalent to the paper's.  All proofs
 use only commutative-ring reasoning and hence hold verbatim over ℝ.

 ── THEOREM 1 (direct sum 𝒜ⁿ = L_X ⊕ K_X) — proven WITHOUT assumptions ──
   Y = Ỹ + Y_ker                                      (thm1_decomposition)
   Y_ker·X = 0                                        (thm1_Yker_kills_X)
   Ỹ·X = Y·X                                     (thm1_Ytilde_same_tangent)
   Ỹ, Y_ker ∈ 𝒜ⁿ                         (thm1_Ytilde_skew, thm1_Yker_skew)
   ⟨Ỹ, Y_ker⟩ = 0                                    (thm1_orthogonality)
   p(p−1) + 2p(n−p) + (n−p)(n−p−1) = n(n−1)       (thm1_dimension_count)
 plus the §2 lemmas Theorem 2 builds on:
   Y skew ⟹ YX ∈ T_X St(n,p)                    (skew_mul_mem_tangent)
   ⟨MXᵀ−XMᵀ, Y⟩ = 2⟨M, YX⟩ for skew Y          (objective_reformulation)
   2⟨N,V⟩ = ⟨N, V−Vᵀ⟩ for skew N        (objective_sees_only_skew_part)

 ── THEOREM 2 (Equivalence of Optima) — DKW assumed, the rest proven ──
 The spectral norm cannot exist over ℤ, so it enters as an abstract
 predicate `nb Z` ("‖Z‖₂ ≤ 1") about which exactly THREE facts are assumed
 as named hypotheses, each a standard property of ‖·‖₂ over ℝ:
   norm_mulL : UᵀU = I → ‖U·Z‖₂ ≤ ‖Z‖₂   (unitary invariance, left)
   norm_mulR : UᵀU = I → ‖Z·U‖₂ ≤ ‖Z‖₂   (unitary invariance, right)
   dkw       : the DAVIS–KAHAN–WEINBERGER completion (the paper's
               Proposition 3) combined with the proof's skew-symmetrization
               step: for skew A and any K with ‖[A; K]‖₂ ≤ 1 there is a
               SKEW C with ‖[[A, −Kᵀ], [K, C]]‖₂ ≤ 1.
 The orthonormal complement X⊥ is supplied as data with its algebraic
 relations (XᵀX = I, X⊥ᵀX⊥ = I, XᵀX⊥ = 0, XXᵀ + X⊥X⊥ᵀ = I); over ℝ it
 exists by basis extension.  Everything else is PROVEN:
   the family Y(C) = Ỹ(B) + Y_ker(C), all skew        (liftT_skew, family_skew)
   Y(C)·X = B for every C                  (liftT_maps_to, family_maps_to)
   XᵀB is skew for tangent B (the (1,1) block)     (tangent_head_skew)
   ⟨MXᵀ−XMᵀ, Y_ker(C)⟩ = 0                     (thm2_kernel_invariance)
   Q = [X X⊥] satisfies QᵀQ = QQᵀ = I; [A; K] = QᵀB; the completed block
   conjugates back to a skew, feasible Y with Y·X = B     (thm2_backward)
   feasibility & objective transfer of Y ↦ Y·X            (thm2_forward)
   THE EQUIVALENCE: both problems attain exactly the same objective
   values, hence identical minima             (thm2_value_equivalence)

 Infrastructure: finite sums over Fin (linearity, Fubini, delta collapse);
 matrices as Fin n → Fin p → ℤ with a verified lemma library (associativity,
 transposes, Frobenius adjunctions ⟨A,BC⟩ = ⟨BᵀA,C⟩ = ⟨ACᵀ,B⟩); block
 matrices ([A B], [A; B], 2×2 blocks, sum splitting over Fin (p+q)).

 Verified with Lean 4.15.0 (core only).  Run:  lean SkewonThm1Thm2.lean
 Axiom audit at end: only Lean's standard foundational axioms.
==============================================================================
-/

/- Part 1: finite sums over Fin n, with the lemma library needed for matrix algebra. -/

def fsum : {n : Nat} → (Fin n → Int) → Int
  | 0,     _ => 0
  | _ + 1, f => fsum (fun i => f i.castSucc) + f (Fin.last _)

@[simp] theorem fsum_zero_fn {n : Nat} : fsum (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fsum, ih]

theorem fsum_add {n : Nat} (f g : Fin n → Int) :
    fsum (fun i => f i + g i) = fsum f + fsum g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fsum, ih]; omega

theorem fsum_neg {n : Nat} (f : Fin n → Int) :
    fsum (fun i => -(f i)) = -(fsum f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fsum, ih]; omega

theorem fsum_sub {n : Nat} (f g : Fin n → Int) :
    fsum (fun i => f i - g i) = fsum f - fsum g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fsum, ih]; omega

theorem fsum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    fsum (fun i => c * f i) = c * fsum f := by
  induction n with
  | zero => simp [fsum]
  | succ n ih => simp [fsum, ih, Int.mul_add]

theorem fsum_mul_right {n : Nat} (c : Int) (f : Fin n → Int) :
    fsum (fun i => f i * c) = fsum f * c := by
  induction n with
  | zero => simp [fsum]
  | succ n ih => simp [fsum, ih, Int.add_mul]

theorem fsum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    fsum f = fsum g := by
  have : f = g := funext h
  rw [this]

/-- Fubini for double finite sums. -/
theorem fsum_comm {n m : Nat} (f : Fin n → Fin m → Int) :
    fsum (fun i => fsum (fun j => f i j)) = fsum (fun j => fsum (fun i => f i j)) := by
  induction n with
  | zero => simp [fsum]
  | succ n ih =>
    show fsum (fun i => fsum (f i.castSucc)) + fsum (f (Fin.last n))
        = fsum (fun j => fsum (fun i => f i j))
    rw [ih, ← fsum_add]
    exact fsum_congr (fun j => rfl)

/-- Kronecker-delta collapse: summing `f` against the indicator of `j` gives `f j`. -/
theorem fsum_delta {n : Nat} (j : Fin n) (f : Fin n → Int) :
    fsum (fun i => if i = j then f i else 0) = f j := by
  induction n with
  | zero => exact absurd j.isLt (by omega)
  | succ n ih =>
    show fsum (fun i : Fin n => if i.castSucc = j then f i.castSucc else 0)
        + (if Fin.last n = j then f (Fin.last n) else 0) = f j
    by_cases hj : j = Fin.last n
    · subst hj
      have h1 : ∀ i : Fin n, (if i.castSucc = Fin.last n then f i.castSucc else 0) = 0 := by
        intro i
        have : i.castSucc ≠ Fin.last n := by
          simp [Fin.ext_iff]; omega
        simp [this]
      rw [fsum_congr h1]
      simp
    · have hlt : j.val < n := by
        have := j.isLt
        simp [Fin.ext_iff] at hj
        omega
      let j' : Fin n := ⟨j.val, hlt⟩
      have hjj : j = j'.castSucc := by simp [Fin.ext_iff, j']
      have h2 : ∀ i : Fin n, (if i.castSucc = j then f i.castSucc else 0)
          = (if i = j' then (fun k : Fin n => f k.castSucc) i else 0) := by
        intro i
        have : (i.castSucc = j) ↔ (i = j') := by
          simp [Fin.ext_iff, j']
        simp only [this]
      rw [fsum_congr h2, ih j' (fun k => f k.castSucc)]
      have hne : Fin.last n ≠ j'.castSucc := by
        simp [Fin.ext_iff, j']; omega
      simp [hne, hjj]
/- Part 2: matrices over ℤ as functions Fin n → Fin p → Int, with the
   general-purpose lemma library. All lemmas are universally quantified
   over dimensions and entries. -/

def Mat (n p : Nat) := Fin n → Fin p → Int

namespace Mat

theorem ext {n p : Nat} {A B : Mat n p} (h : ∀ i j, A i j = B i j) : A = B :=
  funext fun i => funext fun j => h i j

def add {n p : Nat} (A B : Mat n p) : Mat n p := fun i j => A i j + B i j
def sub {n p : Nat} (A B : Mat n p) : Mat n p := fun i j => A i j - B i j
def neg {n p : Nat} (A : Mat n p) : Mat n p := fun i j => -(A i j)
def zero (n p : Nat) : Mat n p := fun _ _ => 0
def T {n p : Nat} (A : Mat n p) : Mat p n := fun i j => A j i
def mul {n m p : Nat} (A : Mat n m) (B : Mat m p) : Mat n p :=
  fun i j => fsum (fun k => A i k * B k j)
def eye (n : Nat) : Mat n n := fun i j => if i = j then 1 else 0
def frob {n p : Nat} (A B : Mat n p) : Int :=
  fsum (fun i => fsum (fun j => A i j * B i j))

infixl:65 " ⬝+ " => add
infixl:65 " ⬝- " => sub
infixl:70 " ⬝* " => mul

/-- A is skew-symmetric. -/
def IsSkew {n : Nat} (A : Mat n n) : Prop := A.T = A.neg
/-- A is symmetric. -/
def IsSym {n : Nat} (A : Mat n n) : Prop := A.T = A
/-- X has orthonormal columns: X ∈ St(n,p). -/
def OnStiefel {n p : Nat} (X : Mat n p) : Prop := X.T ⬝* X = eye p

-- ---------------------------------------------------------------------------
-- Additive structure
-- ---------------------------------------------------------------------------

theorem add_comm {n p : Nat} (A B : Mat n p) : A ⬝+ B = B ⬝+ A :=
  ext fun i j => by simp [add]; omega

theorem add_assoc {n p : Nat} (A B C : Mat n p) :
    (A ⬝+ B) ⬝+ C = A ⬝+ (B ⬝+ C) :=
  ext fun i j => by simp [add]; omega

theorem sub_eq_add_neg {n p : Nat} (A B : Mat n p) : A ⬝- B = A ⬝+ B.neg :=
  ext fun i j => by simp [sub, add, neg]; omega

theorem add_zero {n p : Nat} (A : Mat n p) : A ⬝+ zero n p = A :=
  ext fun i j => by simp [add, zero]

theorem add_neg_self {n p : Nat} (A : Mat n p) : A ⬝+ A.neg = zero n p :=
  ext fun i j => by simp [add, neg, zero]; omega

theorem neg_neg {n p : Nat} (A : Mat n p) : A.neg.neg = A :=
  ext fun i j => by simp [neg]

-- ---------------------------------------------------------------------------
-- Multiplication
-- ---------------------------------------------------------------------------

theorem mul_assoc {n m p q : Nat} (A : Mat n m) (B : Mat m p) (C : Mat p q) :
    (A ⬝* B) ⬝* C = A ⬝* (B ⬝* C) := by
  apply ext; intro i j
  show fsum (fun l => fsum (fun k => A i k * B k l) * C l j)
     = fsum (fun k => A i k * fsum (fun l => B k l * C l j))
  calc fsum (fun l => fsum (fun k => A i k * B k l) * C l j)
      = fsum (fun l => fsum (fun k => A i k * B k l * C l j)) := by
        exact fsum_congr fun l => (fsum_mul_right _ _).symm
    _ = fsum (fun k => fsum (fun l => A i k * B k l * C l j)) := fsum_comm _
    _ = fsum (fun k => A i k * fsum (fun l => B k l * C l j)) := by
        refine fsum_congr fun k => ?_
        rw [← fsum_mul_left]
        exact fsum_congr fun l => by rw [Int.mul_assoc]

theorem mul_add {n m p : Nat} (A : Mat n m) (B C : Mat m p) :
    A ⬝* (B ⬝+ C) = (A ⬝* B) ⬝+ (A ⬝* C) := by
  apply ext; intro i j
  show fsum (fun k => A i k * (B k j + C k j)) = _
  rw [show (fun k => A i k * (B k j + C k j))
        = (fun k => A i k * B k j + A i k * C k j) from
      funext fun k => Int.mul_add ..]
  exact fsum_add _ _

theorem add_mul {n m p : Nat} (A B : Mat n m) (C : Mat m p) :
    (A ⬝+ B) ⬝* C = (A ⬝* C) ⬝+ (B ⬝* C) := by
  apply ext; intro i j
  show fsum (fun k => (A i k + B i k) * C k j) = _
  rw [show (fun k => (A i k + B i k) * C k j)
        = (fun k => A i k * C k j + B i k * C k j) from
      funext fun k => Int.add_mul ..]
  exact fsum_add _ _

theorem neg_mul {n m p : Nat} (A : Mat n m) (B : Mat m p) :
    A.neg ⬝* B = (A ⬝* B).neg := by
  apply ext; intro i j
  show fsum (fun k => -(A i k) * B k j) = -(fsum fun k => A i k * B k j)
  rw [show (fun k => -(A i k) * B k j) = (fun k => -(A i k * B k j)) from
      funext fun k => Int.neg_mul ..]
  exact fsum_neg _

theorem mul_neg {n m p : Nat} (A : Mat n m) (B : Mat m p) :
    A ⬝* B.neg = (A ⬝* B).neg := by
  apply ext; intro i j
  show fsum (fun k => A i k * -(B k j)) = -(fsum fun k => A i k * B k j)
  rw [show (fun k => A i k * -(B k j)) = (fun k => -(A i k * B k j)) from
      funext fun k => Int.mul_neg ..]
  exact fsum_neg _

theorem mul_sub {n m p : Nat} (A : Mat n m) (B C : Mat m p) :
    A ⬝* (B ⬝- C) = (A ⬝* B) ⬝- (A ⬝* C) := by
  rw [sub_eq_add_neg, mul_add, mul_neg, ← sub_eq_add_neg]

theorem sub_mul {n m p : Nat} (A B : Mat n m) (C : Mat m p) :
    (A ⬝- B) ⬝* C = (A ⬝* C) ⬝- (B ⬝* C) := by
  rw [sub_eq_add_neg, add_mul, neg_mul, ← sub_eq_add_neg]

theorem zero_mul {n m p : Nat} (B : Mat m p) : (zero n m) ⬝* B = zero n p := by
  apply ext; intro i j
  show fsum (fun k => (0 : Int) * B k j) = 0
  simp

theorem mul_zero {n m p : Nat} (A : Mat n m) : A ⬝* (zero m p) = zero n p := by
  apply ext; intro i j
  show fsum (fun k => A i k * 0) = 0
  simp

theorem mul_eye {n m : Nat} (A : Mat n m) : A ⬝* eye m = A := by
  apply ext; intro i j
  show fsum (fun k => A i k * (if k = j then 1 else 0)) = A i j
  have h : ∀ k, A i k * (if k = j then 1 else 0) = if k = j then A i k else 0 := by
    intro k; by_cases hk : k = j <;> simp [hk]
  rw [fsum_congr h]
  exact fsum_delta j (fun k => A i k)

theorem eye_mul {n m : Nat} (A : Mat n m) : eye n ⬝* A = A := by
  apply ext; intro i j
  show fsum (fun k => (if i = k then 1 else 0) * A k j) = A i j
  have h : ∀ k, (if i = k then 1 else 0) * A k j = if k = i then A k j else 0 := by
    intro k
    by_cases hk : k = i
    · simp [hk]
    · have : ¬(i = k) := fun h' => hk h'.symm
      simp [hk, this]
  rw [fsum_congr h]
  exact fsum_delta i (fun k => A k j)

-- ---------------------------------------------------------------------------
-- Transpose
-- ---------------------------------------------------------------------------

theorem T_T {n p : Nat} (A : Mat n p) : A.T.T = A := rfl

theorem T_add {n p : Nat} (A B : Mat n p) : (A ⬝+ B).T = A.T ⬝+ B.T := rfl

theorem T_sub {n p : Nat} (A B : Mat n p) : (A ⬝- B).T = A.T ⬝- B.T := rfl

theorem T_neg {n p : Nat} (A : Mat n p) : A.neg.T = A.T.neg := rfl

theorem T_eye {n : Nat} : (eye n).T = eye n := by
  apply ext; intro i j
  show (if j = i then (1:Int) else 0) = (if i = j then 1 else 0)
  by_cases h : i = j
  · simp [h]
  · have h' : ¬ j = i := fun hji => h hji.symm
    simp [h, h']

theorem T_mul {n m p : Nat} (A : Mat n m) (B : Mat m p) :
    (A ⬝* B).T = B.T ⬝* A.T := by
  apply ext; intro i j
  show fsum (fun k => A j k * B k i) = fsum (fun k => B k i * A j k)
  exact fsum_congr fun k => Int.mul_comm ..

-- ---------------------------------------------------------------------------
-- Frobenius inner product ⟨A,B⟩ = tr(AᵀB)
-- ---------------------------------------------------------------------------

theorem frob_comm {n p : Nat} (A B : Mat n p) : frob A B = frob B A := by
  unfold frob
  exact fsum_congr fun i => fsum_congr fun j => Int.mul_comm ..

theorem frob_T_T {n p : Nat} (A B : Mat n p) : frob A.T B.T = frob A B := by
  unfold frob
  exact fsum_comm _

theorem frob_add_right {n p : Nat} (A B C : Mat n p) :
    frob A (B ⬝+ C) = frob A B + frob A C := by
  unfold frob add
  rw [← fsum_add]
  refine fsum_congr fun i => ?_
  rw [← fsum_add]
  exact fsum_congr fun j => Int.mul_add ..

theorem frob_sub_right {n p : Nat} (A B C : Mat n p) :
    frob A (B ⬝- C) = frob A B - frob A C := by
  unfold frob sub
  rw [← fsum_sub]
  refine fsum_congr fun i => ?_
  rw [← fsum_sub]
  exact fsum_congr fun j => Int.mul_sub ..

theorem frob_sub_left {n p : Nat} (A B C : Mat n p) :
    frob (A ⬝- B) C = frob A C - frob B C := by
  rw [frob_comm, frob_sub_right, frob_comm A C, frob_comm B C]

theorem frob_add_left {n p : Nat} (A B C : Mat n p) :
    frob (A ⬝+ B) C = frob A C + frob B C := by
  rw [frob_comm, frob_add_right, frob_comm A C, frob_comm B C]

theorem frob_neg_right {n p : Nat} (A B : Mat n p) :
    frob A B.neg = -(frob A B) := by
  unfold frob neg
  rw [← fsum_neg]
  refine fsum_congr fun i => ?_
  rw [← fsum_neg]
  exact fsum_congr fun j => Int.mul_neg ..

theorem frob_neg_left {n p : Nat} (A B : Mat n p) :
    frob A.neg B = -(frob A B) := by
  rw [frob_comm, frob_neg_right, frob_comm]

theorem frob_zero_left {n p : Nat} (B : Mat n p) : frob (zero n p) B = 0 := by
  unfold frob zero
  simp

/-- Adjunction L1:  ⟨A, B·C⟩ = ⟨Bᵀ·A, C⟩. -/
theorem frob_mul_right {n m p : Nat} (A : Mat n p) (B : Mat n m) (C : Mat m p) :
    frob A (B ⬝* C) = frob (B.T ⬝* A) C := by
  unfold frob mul T
  -- LHS = Σ_i Σ_j A i j * Σ_k B i k * C k j
  -- RHS = Σ_k Σ_j (Σ_i B i k * A i j) * C k j
  calc fsum (fun i => fsum (fun j => A i j * fsum (fun k => B i k * C k j)))
      = fsum (fun i => fsum (fun j => fsum (fun k => A i j * (B i k * C k j)))) := by
        exact fsum_congr fun i => fsum_congr fun j => (fsum_mul_left _ _).symm
    _ = fsum (fun i => fsum (fun k => fsum (fun j => A i j * (B i k * C k j)))) := by
        exact fsum_congr fun i => fsum_comm _
    _ = fsum (fun k => fsum (fun i => fsum (fun j => A i j * (B i k * C k j)))) :=
        fsum_comm _
    _ = fsum (fun k => fsum (fun j => fsum (fun i => A i j * (B i k * C k j)))) := by
        exact fsum_congr fun k => fsum_comm _
    _ = fsum (fun k => fsum (fun j => fsum (fun i => B i k * A i j) * C k j)) := by
        refine fsum_congr fun k => fsum_congr fun j => ?_
        rw [← fsum_mul_right]
        refine fsum_congr fun i => ?_
        rw [Int.mul_comm (B i k) (A i j), Int.mul_assoc]

/-- Adjunction L2:  ⟨A, B·C⟩ = ⟨A·Cᵀ, B⟩.  Derived from L1 and transposes. -/
theorem frob_mul_left {n m p : Nat} (A : Mat n p) (B : Mat n m) (C : Mat m p) :
    frob A (B ⬝* C) = frob (A ⬝* C.T) B := by
  calc frob A (B ⬝* C)
      = frob A.T (B ⬝* C).T := (frob_T_T ..).symm
    _ = frob A.T (C.T ⬝* B.T) := by rw [T_mul]
    _ = frob (C.T.T ⬝* A.T) B.T := frob_mul_right ..
    _ = frob (C ⬝* A.T) B.T := by rw [T_T]
    _ = frob (C ⬝* A.T).T B.T.T := (frob_T_T ..).symm
    _ = frob (A.T.T ⬝* C.T) B.T.T := by rw [T_mul, T_T]
    _ = frob (A ⬝* C.T) B := by rw [T_T, T_T]

/-- ⟨S, K⟩ = 0 whenever S is symmetric and K is skew-symmetric
    (the subspaces 𝒮ⁿ and 𝒜ⁿ are Frobenius-orthogonal). -/
theorem frob_sym_skew {n : Nat} {S K : Mat n n}
    (hS : IsSym S) (hK : IsSkew K) : frob S K = 0 := by
  have h1 : frob S K = frob S.T K.T := (frob_T_T ..).symm
  rw [hS, hK, frob_neg_right] at h1
  omega

end Mat
/- Part 3: block structure. Embeddings Fin p, Fin q → Fin (p+q), splitting of
   sums, horizontal concatenation [A B], and J = [[0, I_p], [−I_p, 0]]. -/

def inl {p q : Nat} (i : Fin p) : Fin (p + q) := ⟨i.val, by omega⟩
def inr {p q : Nat} (j : Fin q) : Fin (p + q) := ⟨p + j.val, by omega⟩

theorem inl_castSucc {p q : Nat} (i : Fin p) :
    (inl (q := q) i).castSucc = inl (q := q + 1) i := by
  simp [inl, Fin.ext_iff]

theorem inr_castSucc {p q : Nat} (j : Fin q) :
    (inr (p := p) j).castSucc = inr (p := p) j.castSucc := by
  simp [inr, Fin.ext_iff]

theorem last_eq_inr {p q : Nat} :
    Fin.last (p + q) = inr (p := p) (Fin.last q) := by
  simp [inr, Fin.last, Fin.ext_iff]

/-- Split a sum over Fin (p+q) into its two blocks. -/
theorem fsum_split {p q : Nat} (f : Fin (p + q) → Int) :
    fsum f = fsum (fun i : Fin p => f (inl i)) + fsum (fun j : Fin q => f (inr j)) := by
  induction q with
  | zero =>
    show fsum f = fsum (fun i : Fin p => f (inl i)) + 0
    have h : (fun i : Fin p => f (inl i)) = f := funext fun i => rfl
    rw [h]
    omega
  | succ q ih =>
    show fsum (fun i : Fin (p + q) => f i.castSucc) + f (Fin.last (p + q)) = _
    rw [ih (fun i => f i.castSucc)]
    show fsum (fun i : Fin p => f (inl i).castSucc)
        + fsum (fun j : Fin q => f (inr j).castSucc) + f (Fin.last (p + q)) = _
    have h1 : (fun i : Fin p => f (inl i).castSucc) = (fun i : Fin p => f (inl i)) := by
      funext i; rw [inl_castSucc]
    have h2 : (fun j : Fin q => f (inr j).castSucc)
        = (fun j : Fin q => (fun t : Fin (q + 1) => f (inr t)) j.castSucc) := by
      funext j; rw [inr_castSucc]
    rw [h1, h2, last_eq_inr]
    show _ = fsum (fun i : Fin p => f (inl i)) + fsum (fun t : Fin (q+1) => f (inr t))
    show _ = fsum (fun i : Fin p => f (inl i))
        + (fsum (fun j : Fin q => (fun t : Fin (q+1) => f (inr t)) j.castSucc)
           + (fun t : Fin (q+1) => f (inr t)) (Fin.last q))
    simp only []
    omega

/-- Case analysis: every index of Fin (p+q) is inl or inr. -/
theorem inl_or_inr {p q : Nat} (l : Fin (p + q)) :
    (∃ l' : Fin p, l = inl l') ∨ (∃ l' : Fin q, l = inr l') := by
  by_cases h : l.val < p
  · exact Or.inl ⟨⟨l.val, h⟩, by simp [inl, Fin.ext_iff]⟩
  · refine Or.inr ⟨⟨l.val - p, by omega⟩, ?_⟩
    simp [inr, Fin.ext_iff]; omega

namespace Mat

/-- Horizontal concatenation [A B] : n × (p+q). -/
def hcat {n p q : Nat} (A : Mat n p) (B : Mat n q) : Mat n (p + q) :=
  fun i k => if h : k.val < p then A i ⟨k.val, h⟩ else B i ⟨k.val - p, by omega⟩

theorem hcat_inl {n p q : Nat} (A : Mat n p) (B : Mat n q) (i : Fin n) (k : Fin p) :
    hcat A B i (inl k) = A i k := by
  simp [hcat, inl]

theorem hcat_inr {n p q : Nat} (A : Mat n p) (B : Mat n q) (i : Fin n) (k : Fin q) :
    hcat A B i (inr k) = B i k := by
  have h : ¬ (p + k.val < p) := by omega
  simp [hcat, inr, h]
  congr 1
  apply Fin.ext
  show p + k.val - p = k.val
  omega

/-- Block computation:  [U V] · [A B]ᵀ = U·Aᵀ + V·Bᵀ. -/
theorem hcat_mul_hcat_T {n m p q : Nat}
    (U : Mat n p) (V : Mat n q) (A : Mat m p) (B : Mat m q) :
    (hcat U V) ⬝* (hcat A B).T = (U ⬝* A.T) ⬝+ (V ⬝* B.T) := by
  apply ext; intro i j
  show fsum (fun l => hcat U V i l * hcat A B j l) = _
  rw [fsum_split (fun l => hcat U V i l * hcat A B j l)]
  have h1 : (fun l : Fin p => hcat U V i (inl l) * hcat A B j (inl l))
      = (fun l : Fin p => U i l * A j l) := by
    funext l; rw [hcat_inl, hcat_inl]
  have h2 : (fun l : Fin q => hcat U V i (inr l) * hcat A B j (inr l))
      = (fun l : Fin q => V i l * B j l) := by
    funext l; rw [hcat_inr, hcat_inr]
  rw [h1, h2]
  rfl

end Mat
/- Part 3b: vertical concatenation, 2×2 block matrices, and the block
   computation lemmas needed for Theorem 2's change of basis Q = [X X⊥]. -/

namespace Mat

/-- Vertical concatenation [A; B] : (p+q) × m. -/
def vcat {p q m : Nat} (A : Mat p m) (B : Mat q m) : Mat (p + q) m :=
  fun l j => if h : l.val < p then A ⟨l.val, h⟩ j else B ⟨l.val - p, by omega⟩ j

theorem vcat_inl {p q m : Nat} (A : Mat p m) (B : Mat q m) (k : Fin p) (j : Fin m) :
    vcat A B (inl k) j = A k j := by
  simp [vcat, inl]

theorem vcat_inr {p q m : Nat} (A : Mat p m) (B : Mat q m) (k : Fin q) (j : Fin m) :
    vcat A B (inr k) j = B k j := by
  have h : ¬ (p + k.val < p) := by omega
  have h2 : p + k.val - p = k.val := by omega
  simp [vcat, inr, h, h2]

/-- [A B]ᵀ = [Aᵀ; Bᵀ]. -/
theorem hcat_T {n p q : Nat} (A : Mat n p) (B : Mat n q) :
    (hcat A B).T = vcat A.T B.T := by
  apply ext; intro l i
  show hcat A B i l = vcat A.T B.T l i
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · rw [hcat_inl, vcat_inl]; rfl
  · rw [hcat_inr, vcat_inr]; rfl

/-- [A; B]ᵀ = [Aᵀ Bᵀ]. -/
theorem vcat_T {p q m : Nat} (A : Mat p m) (B : Mat q m) :
    (vcat A B).T = hcat A.T B.T := by
  apply ext; intro i l
  show vcat A B l i = hcat A.T B.T i l
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · rw [vcat_inl, hcat_inl]; rfl
  · rw [vcat_inr, hcat_inr]; rfl

/-- [U; V]·Z = [U·Z; V·Z]. -/
theorem vcat_mul {p q n m : Nat} (U : Mat p n) (V : Mat q n) (Z : Mat n m) :
    (vcat U V) ⬝* Z = vcat (U ⬝* Z) (V ⬝* Z) := by
  apply ext; intro l j
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · show fsum (fun k => vcat U V (inl l') k * Z k j) = vcat (U ⬝* Z) (V ⬝* Z) (inl l') j
    rw [vcat_inl]
    exact fsum_congr fun k => by rw [vcat_inl]
  · show fsum (fun k => vcat U V (inr l') k * Z k j) = vcat (U ⬝* Z) (V ⬝* Z) (inr l') j
    rw [vcat_inr]
    exact fsum_congr fun k => by rw [vcat_inr]

/-- Z·[A B] = [Z·A  Z·B]. -/
theorem mul_hcat {s n m r : Nat} (Z : Mat s n) (A : Mat n m) (B : Mat n r) :
    Z ⬝* (hcat A B) = hcat (Z ⬝* A) (Z ⬝* B) := by
  apply ext; intro i l
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · show fsum (fun k => Z i k * hcat A B k (inl l')) = hcat (Z ⬝* A) (Z ⬝* B) i (inl l')
    rw [hcat_inl]
    exact fsum_congr fun k => by rw [hcat_inl]
  · show fsum (fun k => Z i k * hcat A B k (inr l')) = hcat (Z ⬝* A) (Z ⬝* B) i (inr l')
    rw [hcat_inr]
    exact fsum_congr fun k => by rw [hcat_inr]

/-- [U V]·[A; B] = U·A + V·B  (the inner-block sum splits). -/
theorem hcat_mul_vcat {n p q m : Nat}
    (U : Mat n p) (V : Mat n q) (A : Mat p m) (B : Mat q m) :
    (hcat U V) ⬝* (vcat A B) = (U ⬝* A) ⬝+ (V ⬝* B) := by
  apply ext; intro i j
  show fsum (fun l => hcat U V i l * vcat A B l j) = _
  rw [fsum_split (fun l => hcat U V i l * vcat A B l j)]
  have h1 : (fun l : Fin p => hcat U V i (inl l) * vcat A B (inl l) j)
      = fun l => U i l * A l j := funext fun l => by rw [hcat_inl, vcat_inl]
  have h2 : (fun l : Fin q => hcat U V i (inr l) * vcat A B (inr l) j)
      = fun l => V i l * B l j := funext fun l => by rw [hcat_inr, vcat_inr]
  rw [h1, h2]
  rfl

/-- 2×2 block matrix [[A, B], [C, D]]. -/
def block2 {p q m r : Nat} (A : Mat p m) (B : Mat p r) (C : Mat q m) (D : Mat q r) :
    Mat (p + q) (m + r) := hcat (vcat A C) (vcat B D)

/-- [U; V]·[A B] = [[UA, UB], [VA, VB]]. -/
theorem vcat_mul_hcat {p q n m r : Nat}
    (U : Mat p n) (V : Mat q n) (A : Mat n m) (B : Mat n r) :
    (vcat U V) ⬝* (hcat A B) = block2 (U ⬝* A) (U ⬝* B) (V ⬝* A) (V ⬝* B) := by
  rw [mul_hcat, vcat_mul, vcat_mul]
  rfl

-- Entry lemmas for 2×2 blocks.

theorem block2_ll {p q m r : Nat} (A : Mat p m) (B : Mat p r) (C : Mat q m)
    (D : Mat q r) (i : Fin p) (j : Fin m) :
    block2 A B C D (inl i) (inl j) = A i j := by
  unfold block2; rw [hcat_inl, vcat_inl]

theorem block2_lr {p q m r : Nat} (A : Mat p m) (B : Mat p r) (C : Mat q m)
    (D : Mat q r) (i : Fin p) (j : Fin r) :
    block2 A B C D (inl i) (inr j) = B i j := by
  unfold block2; rw [hcat_inr, vcat_inl]

theorem block2_rl {p q m r : Nat} (A : Mat p m) (B : Mat p r) (C : Mat q m)
    (D : Mat q r) (i : Fin q) (j : Fin m) :
    block2 A B C D (inr i) (inl j) = C i j := by
  unfold block2; rw [hcat_inl, vcat_inr]

theorem block2_rr {p q m r : Nat} (A : Mat p m) (B : Mat p r) (C : Mat q m)
    (D : Mat q r) (i : Fin q) (j : Fin r) :
    block2 A B C D (inr i) (inr j) = D i j := by
  unfold block2; rw [hcat_inr, vcat_inr]

/-- [[I, 0], [0, I]] = I. -/
theorem block2_eye {p q : Nat} :
    block2 (eye p) (zero p q) (zero q p) (eye q) = eye (p + q) := by
  apply ext; intro l m
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩ <;>
    rcases inl_or_inr m with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · rw [block2_ll]
    show (if l' = m' then (1:Int) else 0) = (if inl l' = inl m' then 1 else 0)
    by_cases h : l' = m'
    · subst h; simp
    · have hv : ¬ ((inl (q := q) l') = inl m') := by
        intro hc
        exact h (Fin.ext (by simpa [inl, Fin.ext_iff] using hc))
      simp [h, hv]
  · rw [block2_lr]
    have hv : ¬ ((inl (q := q) l') = inr (p := p) m') := by
      have := l'.isLt
      simp [inl, inr, Fin.ext_iff]; omega
    show (0:Int) = (if inl l' = inr m' then 1 else 0)
    simp [hv]
  · rw [block2_rl]
    have hv : ¬ ((inr (p := p) l') = inl (q := q) m') := by
      have := m'.isLt
      simp [inl, inr, Fin.ext_iff]; omega
    show (0:Int) = (if inr l' = inl m' then 1 else 0)
    simp [hv]
  · rw [block2_rr]
    show (if l' = m' then (1:Int) else 0) = (if inr l' = inr m' then 1 else 0)
    by_cases h : l' = m'
    · subst h; simp
    · have hv : ¬ ((inr (p := p) l') = inr m') := by
        intro hc
        refine h (Fin.ext ?_)
        have := (Fin.ext_iff).mp hc
        simp [inr] at this
        omega
      simp [h, hv]

-- Pointwise characterization of skewness (helpers).

theorem isSkew_apply {n : Nat} {A : Mat n n} (h : IsSkew A) (i j : Fin n) :
    A j i = -(A i j) := congrFun (congrFun h i) j

theorem isSkew_of {n : Nat} {A : Mat n n} (h : ∀ i j, A j i = -(A i j)) :
    IsSkew A := ext fun i j => h i j

/-- The DKW-shaped block matrix [[A, −Kᵀ], [K, C]] is skew whenever A and C
    are. -/
theorem block2_dkw_skew {p q : Nat} {A : Mat p p} {C : Mat q q} (K : Mat q p)
    (hA : IsSkew A) (hC : IsSkew C) :
    IsSkew (block2 A (K.T.neg) K C) := by
  apply isSkew_of
  intro l m
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩ <;>
    rcases inl_or_inr m with ⟨m', rfl⟩ | ⟨m', rfl⟩
  · rw [block2_ll, block2_ll]
    exact isSkew_apply hA l' m'
  · rw [block2_rl, block2_lr]
    show K m' l' = -(-(K m' l'))
    omega
  · rw [block2_lr, block2_rl]
    rfl
  · rw [block2_rr, block2_rr]
    exact isSkew_apply hC l' m'

end Mat
/- Part 4: the results of Solonko–Molozhavenko–Rakhuba (arXiv:2608.06218),
   stated and proven in FULL GENERALITY: for all dimensions n, p, all
   X ∈ St(n,p), all skew-symmetric Y, and all directions M.

   Convention: entries are integers and statements involving the factor ½
   are stated in an equivalent cleared-denominator form (e.g. the skew part
   ½(MXᵀ − XMᵀ) appears as MXᵀ − XMᵀ, and objectives are doubled
   accordingly). Every proof below uses only commutative-ring reasoning and
   is therefore valid verbatim over ℝ. -/

namespace Mat

section PaperResults

variable {n p : Nat}

-- ===========================================================================
-- Section 2 of the paper: setting up the Skewon problem
-- ===========================================================================

/-- §2, feasibility:  if Y ∈ 𝒜ⁿ and X ∈ St(n,p), then Y·X lies in the
    tangent space T_X St(n,p) = {B : XᵀB + BᵀX = 0}  (definition (3)).
    Note: skewness of Y suffices; X ∈ St(n,p) is not even needed here. -/
theorem skew_mul_mem_tangent (X : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    (X.T ⬝* (Y ⬝* X)) ⬝+ ((Y ⬝* X).T ⬝* X) = zero p p := by
  have h1 : (Y ⬝* X).T ⬝* X = ((X.T ⬝* Y) ⬝* X).neg := by
    rw [T_mul, hY, mul_neg, neg_mul]
  rw [h1, ← mul_assoc]
  exact add_neg_self _

/-- §2, equivalence of the objectives in (4) and (5), cleared of ½:
      ⟨M Xᵀ − X Mᵀ, Y⟩ = 2·⟨M, Y X⟩       for every skew Y.
    (The left side is ⟨2·skew(MXᵀ), Y⟩.) -/
theorem objective_reformulation (X M : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    frob ((M ⬝* X.T) ⬝- (X ⬝* M.T)) Y = 2 * frob M (Y ⬝* X) := by
  have hMX : frob M (Y ⬝* X) = frob (M ⬝* X.T) Y := frob_mul_left ..
  have hXM : frob (X ⬝* M.T) Y = -(frob (M ⬝* X.T) Y) := by
    calc frob (X ⬝* M.T) Y
        = frob (X ⬝* M.T).T Y.T := (frob_T_T ..).symm
      _ = frob (M.T.T ⬝* X.T) Y.neg := by rw [T_mul, hY]
      _ = frob (M ⬝* X.T) Y.neg := by rw [T_T]
      _ = -(frob (M ⬝* X.T) Y) := frob_neg_right ..
  rw [frob_sub_left, hMX, hXM]
  omega

/-- §2, tightness of the relaxation (5) → (6): a skew-symmetric objective
    matrix only sees the skew part of Y, in cleared form:
      2·⟨N, V⟩ = ⟨N, V − Vᵀ⟩     for skew N and ARBITRARY V.
    (V − Vᵀ = 2·skew(V); together with `frob_sym_skew` this is the
    Frobenius-orthogonality 𝒮ⁿ ⟂ 𝒜ⁿ used throughout §2.) -/
theorem objective_sees_only_skew_part (N V : Mat n n) (hN : IsSkew N) :
    2 * frob N V = frob N (V ⬝- V.T) := by
  have h : frob N V.T = -(frob N V) := by
    calc frob N V.T
        = frob N.T V.T.T := by rw [← frob_T_T N.T V.T.T, T_T, T_T]
      _ = frob N.neg V := by rw [hN, T_T]
      _ = -(frob N V) := frob_neg_left ..
  rw [frob_sub_right, h]
  omega

-- ===========================================================================
-- Theorem 1: direct sum decomposition  𝒜ⁿ = L_X ⊕ K_X
-- ===========================================================================

/-- The L_X component of Y (Eq. (8)), built from B = Y·X:
    Ỹ = B Xᵀ − X Bᵀ − X (Xᵀ B) Xᵀ. -/
def Ytilde (X : Mat n p) (Y : Mat n n) : Mat n n :=
  (((Y ⬝* X) ⬝* X.T) ⬝- (X ⬝* (Y ⬝* X).T)) ⬝- ((X ⬝* (X.T ⬝* (Y ⬝* X))) ⬝* X.T)

/-- The K_X component of Y (Eq. (9)):  Y_ker = (I − XXᵀ) Y (I − XXᵀ). -/
def Yker (X : Mat n p) (Y : Mat n n) : Mat n n :=
  ((eye n ⬝- (X ⬝* X.T)) ⬝* Y) ⬝* (eye n ⬝- (X ⬝* X.T))

-- Canonical forms in terms of the atoms P := X·Xᵀ.

theorem Ytilde_eq (X : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    Ytilde X Y =
      ((Y ⬝* (X ⬝* X.T)) ⬝+ ((X ⬝* X.T) ⬝* Y))
        ⬝- (((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T)) := by
  unfold Ytilde
  have e1 : (Y ⬝* X) ⬝* X.T = Y ⬝* (X ⬝* X.T) := mul_assoc ..
  have e2 : X ⬝* (Y ⬝* X).T = (((X ⬝* X.T) ⬝* Y)).neg := by
    rw [T_mul, hY, mul_neg, mul_neg, ← mul_assoc]
  have e3 : (X ⬝* (X.T ⬝* (Y ⬝* X))) ⬝* X.T
      = ((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T) := by
    rw [← mul_assoc X X.T, ← mul_assoc (X ⬝* X.T) Y X,
        mul_assoc ((X ⬝* X.T) ⬝* Y) X X.T]
  rw [e1, e2, e3]
  apply ext; intro i j
  simp only [add, sub, neg]
  omega

theorem Yker_eq (X : Mat n p) (Y : Mat n n) :
    Yker X Y =
      ((Y ⬝- (Y ⬝* (X ⬝* X.T))) ⬝- ((X ⬝* X.T) ⬝* Y))
        ⬝+ (((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T)) := by
  unfold Yker
  rw [sub_mul, eye_mul, mul_sub, mul_eye, sub_mul]
  apply ext; intro i j
  simp only [add, sub]
  omega

/-- Theorem 1, decomposition:  Y = Ỹ + Y_ker  (for every skew Y). -/
theorem thm1_decomposition (X : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    Ytilde X Y ⬝+ Yker X Y = Y := by
  rw [Ytilde_eq X Y hY, Yker_eq X Y]
  apply ext; intro i j
  simp only [add, sub]
  omega

/-- Theorem 1, claim 1:  Y_ker · X = 0  (needs X ∈ St(n,p)). -/
theorem thm1_Yker_kills_X (X : Mat n p) (Y : Mat n n) (hX : OnStiefel X) :
    Yker X Y ⬝* X = zero n p := by
  unfold Yker
  have hPX : (eye n ⬝- (X ⬝* X.T)) ⬝* X = zero n p := by
    rw [sub_mul, eye_mul, mul_assoc, hX, mul_eye]
    apply ext; intro i j
    simp [sub, zero]
  rw [mul_assoc, hPX, mul_zero]

/-- Theorem 1, claim 2:  Ỹ · X = Y · X  (the two components induce the same
    tangent vector). -/
theorem thm1_Ytilde_same_tangent (X : Mat n p) (Y : Mat n n)
    (hX : OnStiefel X) (hY : IsSkew Y) :
    Ytilde X Y ⬝* X = Y ⬝* X := by
  have h := congrArg (fun Z => Z ⬝* X) (thm1_decomposition X Y hY)
  simp only at h
  rw [add_mul, thm1_Yker_kills_X X Y hX, add_zero] at h
  exact h

/-- Theorem 1, membership:  Y_ker ∈ 𝒜ⁿ. -/
theorem thm1_Yker_skew (X : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    IsSkew (Yker X Y) := by
  unfold IsSkew Yker
  have hPsym : (eye n ⬝- (X ⬝* X.T)).T = eye n ⬝- (X ⬝* X.T) := by
    rw [T_sub, T_eye, T_mul, T_T]
  rw [T_mul, T_mul, hPsym, hY, neg_mul, mul_neg, ← mul_assoc]

/-- Theorem 1, membership:  Ỹ ∈ 𝒜ⁿ. -/
theorem thm1_Ytilde_skew (X : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    IsSkew (Ytilde X Y) := by
  unfold IsSkew
  rw [Ytilde_eq X Y hY]
  have hA1 : (Y ⬝* (X ⬝* X.T)).T = (((X ⬝* X.T) ⬝* Y)).neg := by
    rw [T_mul, T_mul, T_T, hY, mul_neg]
  have hA2 : ((X ⬝* X.T) ⬝* Y).T = ((Y ⬝* (X ⬝* X.T))).neg := by
    rw [T_mul, T_mul, T_T, hY, neg_mul]
  have hA3 : (((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T)).T
      = ((((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T))).neg := by
    rw [T_mul, hA2, T_mul, T_T, mul_neg, ← mul_assoc]
  rw [T_sub, T_add, hA1, hA2, hA3]
  apply ext; intro i j
  simp only [add, sub, neg]
  omega

/-- Theorem 1, orthogonality of the two subspaces:  ⟨Ỹ, Y_ker⟩ = 0
    (with respect to the Frobenius inner product; needs X ∈ St(n,p)). -/
theorem thm1_orthogonality (X : Mat n p) (Y : Mat n n)
    (hX : OnStiefel X) (hY : IsSkew Y) :
    frob (Ytilde X Y) (Yker X Y) = 0 := by
  have hPsym : (eye n ⬝- (X ⬝* X.T)).T = eye n ⬝- (X ⬝* X.T) := by
    rw [T_sub, T_eye, T_mul, T_T]
  have hPX : (eye n ⬝- (X ⬝* X.T)) ⬝* X = zero n p := by
    rw [sub_mul, eye_mul, mul_assoc, hX, mul_eye]
    apply ext; intro i j
    simp [sub, zero]
  have hXTP : X.T ⬝* (eye n ⬝- (X ⬝* X.T)) = zero p n := by
    have h := congrArg T hPX
    rw [T_mul, hPsym] at h
    rw [h]
    apply ext; intro i j
    simp [T, zero]
  have hPXXT : (eye n ⬝- (X ⬝* X.T)) ⬝* (X ⬝* X.T) = zero n n := by
    rw [← mul_assoc, hPX, zero_mul]
  have hXXTP : (X ⬝* X.T) ⬝* (eye n ⬝- (X ⬝* X.T)) = zero n n := by
    rw [mul_assoc, hXTP, mul_zero]
  -- ⟨Ỹ, P·(Y·P)⟩ = ⟨P·Ỹ, Y·P⟩ = ⟨(P·Ỹ)·P, Y⟩,  and (P·Ỹ)·P = 0.
  have step1 : frob (Ytilde X Y) (Yker X Y)
      = frob (((eye n ⬝- (X ⬝* X.T)) ⬝* Ytilde X Y) ⬝* (eye n ⬝- (X ⬝* X.T))) Y := by
    calc frob (Ytilde X Y) (Yker X Y)
        = frob (Ytilde X Y) ((eye n ⬝- (X ⬝* X.T)) ⬝* (Y ⬝* (eye n ⬝- (X ⬝* X.T)))) := by
          unfold Yker; rw [mul_assoc]
      _ = frob ((eye n ⬝- (X ⬝* X.T)).T ⬝* Ytilde X Y) (Y ⬝* (eye n ⬝- (X ⬝* X.T))) :=
          frob_mul_right ..
      _ = frob ((eye n ⬝- (X ⬝* X.T)) ⬝* Ytilde X Y) (Y ⬝* (eye n ⬝- (X ⬝* X.T))) := by
          rw [hPsym]
      _ = frob (((eye n ⬝- (X ⬝* X.T)) ⬝* Ytilde X Y) ⬝* (eye n ⬝- (X ⬝* X.T)).T) Y :=
          frob_mul_left ..
      _ = frob (((eye n ⬝- (X ⬝* X.T)) ⬝* Ytilde X Y) ⬝* (eye n ⬝- (X ⬝* X.T))) Y := by
          rw [hPsym]
  have step2 : ((eye n ⬝- (X ⬝* X.T)) ⬝* Ytilde X Y) ⬝* (eye n ⬝- (X ⬝* X.T))
      = zero n n := by
    rw [Ytilde_eq X Y hY]
    have t1 : ((eye n ⬝- (X ⬝* X.T)) ⬝* (Y ⬝* (X ⬝* X.T))) ⬝* (eye n ⬝- (X ⬝* X.T))
        = zero n n := by
      rw [mul_assoc (eye n ⬝- (X ⬝* X.T)) (Y ⬝* (X ⬝* X.T)) (eye n ⬝- (X ⬝* X.T)),
          mul_assoc Y (X ⬝* X.T) (eye n ⬝- (X ⬝* X.T)), hXXTP, mul_zero, mul_zero]
    have t2 : ((eye n ⬝- (X ⬝* X.T)) ⬝* ((X ⬝* X.T) ⬝* Y)) ⬝* (eye n ⬝- (X ⬝* X.T))
        = zero n n := by
      rw [← mul_assoc (eye n ⬝- (X ⬝* X.T)) (X ⬝* X.T) Y, hPXXT, zero_mul, zero_mul]
    have t3 : ((eye n ⬝- (X ⬝* X.T)) ⬝* (((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T)))
          ⬝* (eye n ⬝- (X ⬝* X.T)) = zero n n := by
      rw [← mul_assoc (eye n ⬝- (X ⬝* X.T)) ((X ⬝* X.T) ⬝* Y) (X ⬝* X.T),
          ← mul_assoc (eye n ⬝- (X ⬝* X.T)) (X ⬝* X.T) Y, hPXXT,
          zero_mul, zero_mul, zero_mul]
    rw [mul_sub (eye n ⬝- (X ⬝* X.T)) ((Y ⬝* (X ⬝* X.T)) ⬝+ ((X ⬝* X.T) ⬝* Y))
          (((X ⬝* X.T) ⬝* Y) ⬝* (X ⬝* X.T)),
        mul_add (eye n ⬝- (X ⬝* X.T)) (Y ⬝* (X ⬝* X.T)) ((X ⬝* X.T) ⬝* Y),
        sub_mul, add_mul, t1, t2, t3]
    apply ext; intro i j
    simp [add, sub, zero]
  rw [step1, step2]
  exact frob_zero_left Y

end PaperResults
end Mat
/- Part 6: THEOREM 2 (Equivalence of Optima).

   The spectral norm does not exist over ℤ, so it enters as an abstract
   predicate `nb Z` ("‖Z‖₂ ≤ 1") about which we assume exactly three facts,
   each a standard property of ‖·‖₂ over ℝ:

     norm_mulL : ‖U·Z‖₂ ≤ ‖Z‖₂ for column-orthonormal U   (UᵀU = I)
     norm_mulR : ‖Z·U‖₂ ≤ ‖Z‖₂ for column-orthonormal U   (UᵀU = I)
     dkw       : the Davis–Kahan–Weinberger norm-preserving completion
                 (the paper's Proposition 3), combined with the
                 skew-symmetrization step of the paper's proof: given a
                 skew A and any K with ‖[A; K]‖₂ ≤ 1, there is a SKEW C
                 with ‖[[A, −Kᵀ], [K, C]]‖₂ ≤ 1.

   Everything else — the family Y(C), Y(C)·X = B, skewness, the kernel
   component's invisibility to the objective, the change of basis with
   Q = [X X⊥], and the value equivalence of the two problems — is proven
   below by pure ring algebra, universally quantified.

   The orthonormal complement X⊥ is supplied as data with its defining
   algebraic relations (XᵀX = I, X⊥ᵀX⊥ = I, XᵀX⊥ = 0, XXᵀ + X⊥X⊥ᵀ = I);
   over ℝ such an X⊥ always exists by basis extension. -/

namespace Mat

theorem frob_zero_right {n p : Nat} (A : Mat n p) : frob A (zero n p) = 0 := by
  rw [frob_comm]
  exact frob_zero_left A

/-- Skewness is preserved by sums. -/
theorem isSkew_add {n : Nat} {A B : Mat n n} (hA : IsSkew A) (hB : IsSkew B) :
    IsSkew (A ⬝+ B) := by
  unfold IsSkew
  rw [T_add, hA, hB]
  apply ext; intro i j
  simp only [add, neg]
  omega

/-- Congruence by any Q preserves skewness:  Z skew ⟹ Q·Z·Qᵀ skew. -/
theorem conj_skew {n m : Nat} (Q : Mat n m) {Z : Mat m m} (hZ : IsSkew Z) :
    IsSkew ((Q ⬝* Z) ⬝* Q.T) := by
  unfold IsSkew
  rw [T_mul, T_mul, T_T, hZ, neg_mul, mul_neg, ← mul_assoc]

/-- Recovering the block form: Qᵀ·(Q·Z·Qᵀ)·Q = Z when QᵀQ = I
    (the similarity relation used in the paper's proof display). -/
theorem conj_recover {n m : Nat} (Q : Mat n m) (Z : Mat m m)
    (hQTQ : Q.T ⬝* Q = eye m) :
    (Q.T ⬝* ((Q ⬝* Z) ⬝* Q.T)) ⬝* Q = Z := by
  rw [mul_assoc Q.T ((Q ⬝* Z) ⬝* Q.T) Q, mul_assoc (Q ⬝* Z) Q.T Q, hQTQ,
      mul_eye, ← mul_assoc Q.T Q Z, hQTQ, eye_mul]

section Thm2

variable {n p q : Nat}

-- ---------------------------------------------------------------------------
-- The family Y(C) = Ỹ(B) + Y_ker(C) of the paper's proof (algebraic part).
-- ---------------------------------------------------------------------------

/-- The lift of a tangent vector B into 𝒜ⁿ (the Ỹ∗ of the proof of Thm 2,
    Eq. (8) evaluated at B):  Ỹ(B) = B Xᵀ − X Bᵀ − X (Xᵀ B) Xᵀ. -/
def liftT (X B : Mat n p) : Mat n n :=
  ((B ⬝* X.T) ⬝- (X ⬝* B.T)) ⬝- ((X ⬝* (X.T ⬝* B)) ⬝* X.T)

/-- From tangency  XᵀB + BᵀX = 0  we get  BᵀX = −(XᵀB). -/
theorem tangent_flip (X B : Mat n p)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) :
    B.T ⬝* X = (X.T ⬝* B).neg := by
  apply ext; intro i j
  have h := congrFun (congrFun hBt i) j
  simp only [add, zero] at h
  simp only [neg]
  omega

/-- Tangency makes A := XᵀB skew-symmetric (the (1,1) block of QᵀY Q). -/
theorem tangent_head_skew (X B : Mat n p)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) :
    IsSkew (X.T ⬝* B) := by
  unfold IsSkew
  rw [T_mul, T_T]
  exact tangent_flip X B hBt

/-- The lift is skew-symmetric (Y(C) ∈ 𝒜ⁿ, C = 0 part). -/
theorem liftT_skew (X B : Mat n p)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) :
    IsSkew (liftT X B) := by
  unfold IsSkew liftT
  have hBTX := tangent_flip X B hBt
  have h1 : (B ⬝* X.T).T = X ⬝* B.T := by rw [T_mul, T_T]
  have h2 : (X ⬝* B.T).T = B ⬝* X.T := by rw [T_mul, T_T]
  have h3 : ((X ⬝* (X.T ⬝* B)) ⬝* X.T).T
      = (((X ⬝* (X.T ⬝* B)) ⬝* X.T)).neg := by
    rw [T_mul, T_mul, T_T, T_mul, T_T, hBTX, neg_mul, mul_neg, ← mul_assoc]
  rw [T_sub, T_sub, h1, h2, h3]
  apply ext; intro i j
  simp only [sub, neg]
  omega

/-- The lift maps back to B:  Ỹ(B) · X = B  (needs X ∈ St(n,p) and B ∈ T_X). -/
theorem liftT_maps_to (X B : Mat n p) (hX : OnStiefel X)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) :
    liftT X B ⬝* X = B := by
  unfold liftT
  have hBTX := tangent_flip X B hBt
  have e1 : (B ⬝* X.T) ⬝* X = B := by
    rw [mul_assoc, hX, mul_eye]
  have e2 : (X ⬝* B.T) ⬝* X = (X ⬝* (X.T ⬝* B)).neg := by
    rw [mul_assoc, hBTX, mul_neg]
  have e3 : ((X ⬝* (X.T ⬝* B)) ⬝* X.T) ⬝* X = X ⬝* (X.T ⬝* B) := by
    rw [mul_assoc, hX, mul_eye]
  rw [sub_mul, sub_mul, e1, e2, e3]
  apply ext; intro i j
  simp only [sub, neg]
  omega

/-- The paper's whole family maps to B:  Y(C)·X = (Ỹ(B) + Y_ker(C))·X = B
    for EVERY C  (Y_ker(C) := (I−XXᵀ)C(I−XXᵀ) from Theorem 1). -/
theorem family_maps_to (X B : Mat n p) (C : Mat n n) (hX : OnStiefel X)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) :
    (liftT X B ⬝+ Yker X C) ⬝* X = B := by
  rw [add_mul, liftT_maps_to X B hX hBt, thm1_Yker_kills_X X C hX]
  apply ext; intro i j
  simp only [add, zero]
  omega

/-- Every member of the family lies in 𝒜ⁿ  (for skew C). -/
theorem family_skew (X B : Mat n p) (C : Mat n n)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) (hC : IsSkew C) :
    IsSkew (liftT X B ⬝+ Yker X C) :=
  isSkew_add (liftT_skew X B hBt) (thm1_Yker_skew X C hC)

-- ---------------------------------------------------------------------------
-- Kernel invariance: the display  ½⟨MXᵀ − XMᵀ, Y_ker⟩ = ⟨M, Y_ker X⟩ = 0.
-- ---------------------------------------------------------------------------

/-- The kernel component is invisible to the Skewon objective
    (cleared form:  ⟨MXᵀ − XMᵀ, Y_ker(C)⟩ = 0 for skew C). -/
theorem thm2_kernel_invariance (X M : Mat n p) (C : Mat n n)
    (hX : OnStiefel X) (hC : IsSkew C) :
    frob ((M ⬝* X.T) ⬝- (X ⬝* M.T)) (Yker X C) = 0 := by
  rw [objective_reformulation X M (Yker X C) (thm1_Yker_skew X C hC),
      thm1_Yker_kills_X X C hX, frob_zero_right]
  omega

-- ---------------------------------------------------------------------------
-- The abstract spectral-norm layer (the ONLY assumed facts).
-- ---------------------------------------------------------------------------

variable (nb : ∀ {a b : Nat}, Mat a b → Prop)

/-- FORWARD direction of Theorem 2 (Remark 4): the map Y ↦ Y·X sends the
    Skewon feasible set into the SMP feasible set with equal (doubled)
    objective.  Only `norm_mulR` (‖Y·X‖₂ ≤ ‖Y‖₂ for X ∈ St) is assumed. -/
theorem thm2_forward
    (norm_mulR : ∀ {a b c : Nat} (Z : Mat a b) (U : Mat b c),
      U.T ⬝* U = eye c → nb Z → nb (Z ⬝* U))
    (X M : Mat n p) (Y : Mat n n) (hX : OnStiefel X)
    (hY : IsSkew Y) (hYn : nb Y) :
    ((X.T ⬝* (Y ⬝* X)) ⬝+ ((Y ⬝* X).T ⬝* X) = zero p p)
    ∧ nb (Y ⬝* X)
    ∧ frob ((M ⬝* X.T) ⬝- (X ⬝* M.T)) Y = 2 * frob M (Y ⬝* X) :=
  ⟨skew_mul_mem_tangent X Y hY,
   norm_mulR Y X hX hYn,
   objective_reformulation X M Y hY⟩

/-- BACKWARD direction of Theorem 2: every SMP-feasible B is Y·X for some
    Skewon-feasible Y — the Davis–Kahan–Weinberger construction.

    Assumed: `norm_mulL`, `norm_mulR` (unitary invariance of ‖·‖₂), and
    `dkw` = the paper's Proposition 3 + skew-symmetrization.  The
    orthonormal complement X⊥ is supplied with its algebraic relations.

    Everything else — that the completed block matrix conjugated back by
    Q = [X X⊥] is skew, has norm ≤ 1, and maps to B — is PROVEN. -/
theorem thm2_backward
    (norm_mulL : ∀ {a b c : Nat} (U : Mat a b) (Z : Mat b c),
      U.T ⬝* U = eye b → nb Z → nb (U ⬝* Z))
    (norm_mulR : ∀ {a b c : Nat} (Z : Mat a b) (U : Mat b c),
      U.T ⬝* U = eye c → nb Z → nb (Z ⬝* U))
    (dkw : ∀ {p' q' : Nat} (A : Mat p' p') (K : Mat q' p'),
      IsSkew A → nb (vcat A K) →
      ∃ C : Mat q' q', IsSkew C ∧ nb (block2 A (K.T.neg) K C))
    (X : Mat n p) (Xp : Mat n q)
    (hX : OnStiefel X) (hXp : OnStiefel Xp)
    (hXXp : X.T ⬝* Xp = zero p q)
    (hcomplete : (X ⬝* X.T) ⬝+ (Xp ⬝* Xp.T) = eye n)
    (B : Mat n p)
    (hBt : (X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p)
    (hBn : nb B) :
    ∃ Y : Mat n n, IsSkew Y ∧ nb Y ∧ Y ⬝* X = B := by
  -- Notation: Q = [X X⊥], A = XᵀB (skew by tangency), K = X⊥ᵀB.
  have hXpX : Xp.T ⬝* X = zero q p := by
    have h := congrArg T hXXp
    rw [T_mul, T_T] at h
    rw [h]
    rfl
  have hQQT : (hcat X Xp) ⬝* (hcat X Xp).T = eye n := by
    rw [hcat_mul_hcat_T]
    exact hcomplete
  have hQTQ : (hcat X Xp).T ⬝* (hcat X Xp) = eye (p + q) := by
    rw [hcat_T, vcat_mul_hcat, hX, hXp, hXXp, hXpX]
    exact block2_eye
  have hA : IsSkew (X.T ⬝* B) := tangent_head_skew X B hBt
  -- ‖[A; K]‖₂ ≤ 1 because [A; K] = Qᵀ·B and ‖Qᵀ‖₂ = 1 (rows orthonormal).
  have hQTB : (hcat X Xp).T ⬝* B = vcat (X.T ⬝* B) (Xp.T ⬝* B) := by
    rw [hcat_T, vcat_mul]
  have hstack : nb (vcat (X.T ⬝* B) (Xp.T ⬝* B)) := by
    rw [← hQTB]
    exact norm_mulL (hcat X Xp).T B (by rw [T_T]; exact hQQT) hBn
  -- The Davis–Kahan–Weinberger completion (assumed), in skew form.
  obtain ⟨C, hCskew, hYhatn⟩ := dkw (X.T ⬝* B) (Xp.T ⬝* B) hA hstack
  -- The solution:  Y := Q · [[A, −Kᵀ], [K, C]] · Qᵀ.
  refine ⟨((hcat X Xp) ⬝* block2 (X.T ⬝* B) ((Xp.T ⬝* B).T.neg) (Xp.T ⬝* B) C)
            ⬝* (hcat X Xp).T, ?_, ?_, ?_⟩
  · -- skewness: block is skew, congruence preserves skewness
    exact conj_skew (hcat X Xp) (block2_dkw_skew (Xp.T ⬝* B) hA hCskew)
  · -- ‖Y‖₂ ≤ 1: multiply the completed block by isometries on both sides
    refine norm_mulR _ (hcat X Xp).T (by rw [T_T]; exact hQQT) ?_
    exact norm_mulL (hcat X Xp) _ hQTQ hYhatn
  · -- Y·X = B: the block computation of the paper, done symbolically
    have hQTX : (hcat X Xp).T ⬝* X = vcat (eye p) (zero q p) := by
      rw [hcat_T, vcat_mul, hX, hXpX]
    have hblock : block2 (X.T ⬝* B) ((Xp.T ⬝* B).T.neg) (Xp.T ⬝* B) C
          ⬝* vcat (eye p) (zero q p)
        = vcat (X.T ⬝* B) (Xp.T ⬝* B) := by
      show hcat (vcat (X.T ⬝* B) (Xp.T ⬝* B)) (vcat ((Xp.T ⬝* B).T.neg) C)
            ⬝* vcat (eye p) (zero q p) = _
      rw [hcat_mul_vcat, mul_eye, mul_zero]
      apply ext; intro i j
      simp only [add, zero]
      omega
    have hreassemble :
        (hcat X Xp) ⬝* vcat (X.T ⬝* B) (Xp.T ⬝* B) = B := by
      rw [hcat_mul_vcat, ← mul_assoc, ← mul_assoc, ← add_mul, hcomplete,
          eye_mul]
    rw [mul_assoc, hQTX, mul_assoc, hblock, hreassemble]

-- ---------------------------------------------------------------------------
-- Theorem 2, value equivalence: both problems achieve exactly the same
-- objective values, hence identical minimum objective values.
-- ---------------------------------------------------------------------------

/-- THEOREM 2 (Equivalence of Optima), value form.  For every v, the (doubled)
    Skewon objective ⟨MXᵀ − XMᵀ, Y⟩ attains v on its feasible set
    {Y ∈ 𝒜ⁿ : ‖Y‖₂ ≤ 1} iff the (doubled) SMP objective 2⟨M, B⟩ attains v on
    its feasible set {B ∈ T_X St(n,p) : ‖B‖₂ ≤ 1}.  In particular the two
    problems have identical minimum objective values, and optima correspond
    under Y ↦ Y·X (forward) and the DKW completion (backward). -/
theorem thm2_value_equivalence
    (norm_mulL : ∀ {a b c : Nat} (U : Mat a b) (Z : Mat b c),
      U.T ⬝* U = eye b → nb Z → nb (U ⬝* Z))
    (norm_mulR : ∀ {a b c : Nat} (Z : Mat a b) (U : Mat b c),
      U.T ⬝* U = eye c → nb Z → nb (Z ⬝* U))
    (dkw : ∀ {p' q' : Nat} (A : Mat p' p') (K : Mat q' p'),
      IsSkew A → nb (vcat A K) →
      ∃ C : Mat q' q', IsSkew C ∧ nb (block2 A (K.T.neg) K C))
    (X : Mat n p) (Xp : Mat n q)
    (hX : OnStiefel X) (hXp : OnStiefel Xp)
    (hXXp : X.T ⬝* Xp = zero p q)
    (hcomplete : (X ⬝* X.T) ⬝+ (Xp ⬝* Xp.T) = eye n)
    (M : Mat n p) (v : Int) :
    (∃ Y : Mat n n, IsSkew Y ∧ nb Y
        ∧ frob ((M ⬝* X.T) ⬝- (X ⬝* M.T)) Y = v)
    ↔ (∃ B : Mat n p, ((X.T ⬝* B) ⬝+ (B.T ⬝* X) = zero p p) ∧ nb B
        ∧ 2 * frob M B = v) := by
  constructor
  · rintro ⟨Y, hY, hYn, hv⟩
    refine ⟨Y ⬝* X, skew_mul_mem_tangent X Y hY, norm_mulR Y X hX hYn, ?_⟩
    rw [← objective_reformulation X M Y hY]
    exact hv
  · rintro ⟨B, hBt, hBn, hv⟩
    obtain ⟨Y, hY, hYn, hYX⟩ :=
      thm2_backward nb norm_mulL norm_mulR dkw X Xp hX hXp hXXp hcomplete
        B hBt hBn
    refine ⟨Y, hY, hYn, ?_⟩
    rw [objective_reformulation X M Y hY, hYX]
    exact hv

end Thm2
end Mat
/- Part 7: Theorem 1's dimension count. -/

/-- Theorem 1, dimension count (cleared of the /2):
      p(p−1) + 2·p(n−p) + (n−p)(n−p−1) = n(n−1)
    i.e.  dim L_X + dim K_X = dim 𝒜ⁿ  with
    dim L_X = p(p−1)/2 + p(n−p) and dim K_X = (n−p)(n−p−1)/2.
    Proven as a ring identity over ℤ, for ALL n, p. -/
theorem thm1_dimension_count (n p : Int) :
    p * (p - 1) + 2 * (p * (n - p)) + (n - p) * (n - p - 1) = n * (n - 1) := by
  have h1 : p * (p - 1) = p * p - p := by
    rw [Int.mul_sub, Int.mul_one]
  have h2 : p * (n - p) = p * n - p * p := by
    rw [Int.mul_sub]
  have h3 : (n - p) * (n - p - 1) = (n - p) * (n - p) - (n - p) := by
    rw [Int.mul_sub, Int.mul_one]
  have h4 : (n - p) * (n - p) = n * n - p * n - p * n + p * p := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm n p]
    omega
  have h5 : n * (n - 1) = n * n - n := by
    rw [Int.mul_sub, Int.mul_one]
  rw [h1, h2, h3, h4, h5]
  omega


-- ============================================================================
-- Axiom audit: every theorem depends only on Lean's standard foundational
-- axioms (propext, Quot.sound, Classical.choice via decidability instances) —
-- no `sorry`, no `native_decide`/`ofReduceBool`.
-- ============================================================================
#print axioms Mat.thm1_decomposition
#print axioms Mat.thm1_Yker_kills_X
#print axioms Mat.thm1_Ytilde_same_tangent
#print axioms Mat.thm1_Ytilde_skew
#print axioms Mat.thm1_Yker_skew
#print axioms Mat.thm1_orthogonality
#print axioms thm1_dimension_count
#print axioms Mat.skew_mul_mem_tangent
#print axioms Mat.objective_reformulation
#print axioms Mat.liftT_skew
#print axioms Mat.liftT_maps_to
#print axioms Mat.family_maps_to
#print axioms Mat.family_skew
#print axioms Mat.thm2_kernel_invariance
#print axioms Mat.thm2_forward
#print axioms Mat.thm2_backward
#print axioms Mat.thm2_value_equivalence
