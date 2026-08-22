/-
==============================================================================
 SkewonSymbolic.lean — GENERAL SYMBOLIC VERIFICATION in core Lean 4
==============================================================================

 Paper: Solonko, Molozhavenko, Rakhuba,
        "Muon on the Stiefel Manifold Admits an Exact Closed-Form Update"
        (arXiv:2608.06218v1)

 Unlike an instance-based check, every theorem below is UNIVERSALLY
 QUANTIFIED: over all dimensions n, p, all X ∈ St(n,p) = {X : XᵀX = I},
 all skew-symmetric Y, and all gradient directions M. No numeric examples,
 no `native_decide` — pure structural proofs from first principles.

 The file is fully self-contained (core Lean 4 only, no Mathlib):
   Part 1  finite sums over `Fin n` (linearity, Fubini, delta collapse)
   Part 2  matrices as `Fin n → Fin p → ℤ` with a verified lemma library
           (associativity, transposes, Frobenius adjunctions ⟨A,BC⟩=⟨BᵀA,C⟩)
   Part 3  block matrices: [A B] concatenation, J = [[0,I],[−I,0]], sum
           splitting over Fin (p+q)
   Part 4  §2 + Theorem 1 of the paper, in full generality
   Part 5  Proposition 2, Algorithm 2, dimension count, nonnegativity

 CONVENTIONS
 - Entries live in ℤ and factors of ½ are cleared: the skew part
   ½(MXᵀ − XMᵀ) appears as MXᵀ − XMᵀ, projections/objectives are doubled.
   Each cleared statement is algebraically equivalent to the paper's.
 - Every proof uses only commutative-ring reasoning (+, −, ×, distributivity,
   commutativity), so each identity is valid verbatim over ℝ — ℤ is used
   because core Lean ships a complete integer lemma set and `omega`.

 WHAT IS PROVEN (all fully general)
 - §2 feasibility: Y skew ⟹ YX ∈ T_X St(n,p)          (skew_mul_mem_tangent)
 - §2 objective equivalence (4)↔(5)↔(6):
     ⟨MXᵀ−XMᵀ, Y⟩ = 2⟨M, YX⟩ for skew Y               (objective_reformulation)
     2⟨N,V⟩ = ⟨N, V−Vᵀ⟩ for skew N, any V     (objective_sees_only_skew_part)
     ⟨S,K⟩ = 0 for S sym, K skew                            (frob_sym_skew)
 - Theorem 1 (𝒜ⁿ = L_X ⊕ K_X), all algebraic claims:
     Y = Ỹ + Y_ker                                     (thm1_decomposition)
     Y_ker·X = 0                                       (thm1_Yker_kills_X)
     Ỹ·X = Y·X                                    (thm1_Ytilde_same_tangent)
     Ỹ, Y_ker ∈ 𝒜ⁿ                        (thm1_Ytilde_skew, thm1_Yker_skew)
     ⟨Ỹ, Y_ker⟩ = 0                                   (thm1_orthogonality)
     p(p−1) + 2p(n−p) + (n−p)(n−p−1) = n(n−1)      (thm1_dimension_count)
 - Proposition 2 (boundary witness B̂ ∝ −P_X M):
     Xᵀ(2P_X M) = XᵀM − MᵀX,  tangency of P_X M      (X_T_mul_proj2, proj2_tangent)
     ‖2P_X M‖_F² = 2⟨M, 2P_X M⟩  (self-adjointness)   (proj2_self_adjoint)
     ⟨M, P_X M⟩ ≥ 0, witness objective ≤ 0    (proj2_inner_nonneg, witness_nonpositive)
 - Algorithm 2 / Eq. (13):  [−X M]·J·[−X M]ᵀ = MXᵀ − XMᵀ,
     for ALL X, M                                    (alg2_factorization)

 WHAT CANNOT BE DONE SYMBOLICALLY HERE (needs spectral analysis):
 - Prop 1's closed form Y* = −msign(N) and value −‖N‖_*  (needs SVD existence
   and von Neumann-type trace inequalities over ℝ)
 - Theorem 2's Davis–Kahan–Weinberger completion argument (spectral norms)
 - Proposition 4's singular-value statement, Theorem 3's convergence
 These require Mathlib-level real analysis; the algebraic skeleton they rest
 on (everything above) is what is verified here.

 Verified with: Lean 4.15.0 (core only). Run:  lean SkewonSymbolic.lean
 Axiom audit at end of file: proofs depend only on Lean's standard
 foundational axioms (propext, Quot.sound, Classical.choice) — no `sorry`,
 no `native_decide`/compiler trust.
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

/-- J = [[0, I_p], [−I_p, 0]] ∈ 𝒜^{2p}  (Section 4 of the paper). -/
def Jmat (p : Nat) : Mat (p + p) (p + p) := fun k l =>
  if k.val < p then (if l.val = k.val + p then 1 else 0)
  else (if l.val + p = k.val then -1 else 0)

theorem Jmat_inl {p : Nat} (k : Fin p) (l : Fin (p + p)) :
    Jmat p (inl k) l = (if l.val = k.val + p then 1 else 0) := by
  simp [Jmat, inl, k.isLt]

theorem Jmat_inr {p : Nat} (k : Fin p) (l : Fin (p + p)) :
    Jmat p (inr k) l = (if l.val + p = p + k.val then -1 else 0) := by
  have h : ¬ (p + k.val < p) := by omega
  simp [Jmat, inr, h]

/-- Block computation:  [A B] · J = [−B  A]. -/
theorem hcat_mul_J {n p : Nat} (A B : Mat n p) :
    (hcat A B) ⬝* Jmat p = hcat B.neg A := by
  apply ext; intro i l
  show fsum (fun k => hcat A B i k * Jmat p k l) = hcat B.neg A i l
  rw [fsum_split (fun k => hcat A B i k * Jmat p k l)]
  rcases inl_or_inr l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · -- target column in the left block: result is −B i l'
    have h1 : ∀ k : Fin p, hcat A B i (inl k) * Jmat p (inl k) (inl l') = 0 := by
      intro k
      rw [Jmat_inl]
      have : ¬ ((inl (q := p) l').val = k.val + p) := by
        have := l'.isLt; simp [inl]; omega
      simp [this]
    have h2 : ∀ k : Fin p, hcat A B i (inr k) * Jmat p (inr k) (inl l')
        = (if k = l' then -(B i k) else 0) := by
      intro k
      rw [Jmat_inr, hcat_inr]
      have hiff : ((inl (q := p) l').val + p = p + k.val) ↔ (k = l') := by
        simp [inl, Fin.ext_iff]; omega
      by_cases hk : k = l'
      · subst hk
        have hc : (inl (q := p) k).val + p = p + k.val := by simp [inl]; omega
        simp [hc]
      · have : ¬ ((inl (q := p) l').val + p = p + k.val) := by
          rw [hiff]; exact hk
        simp [this, hk]
    rw [fsum_congr h1, fsum_congr h2, fsum_delta l' (fun k => -(B i k))]
    simp [hcat_inl, neg]
  · -- target column in the right block: result is A i l'
    have h1 : ∀ k : Fin p, hcat A B i (inl k) * Jmat p (inl k) (inr l')
        = (if k = l' then A i k else 0) := by
      intro k
      rw [Jmat_inl, hcat_inl]
      have hiff : ((inr (p := p) l').val = k.val + p) ↔ (k = l') := by
        simp [inr, Fin.ext_iff]; omega
      by_cases hk : k = l'
      · subst hk
        have hc : (inr (p := p) k).val = k.val + p := by simp [inr]; omega
        simp [hc]
      · have : ¬ ((inr (p := p) l').val = k.val + p) := by rw [hiff]; exact hk
        simp [this, hk]
    have h2 : ∀ k : Fin p, hcat A B i (inr k) * Jmat p (inr k) (inr l') = 0 := by
      intro k
      rw [Jmat_inr]
      have : ¬ ((inr (p := p) l').val + p = p + k.val) := by
        have := k.isLt; simp [inr]; omega
      simp [this]
    rw [fsum_congr h1, fsum_congr h2, fsum_delta l' (fun k => A i k)]
    simp [hcat_inr]

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
/- Part 5: Proposition 2, Algorithm 2, and the dimension count of Theorem 1. -/

-- Nonnegativity infrastructure (for Proposition 2).

theorem fsum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ fsum f := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    show 0 ≤ fsum (fun i => f i.castSucc) + f (Fin.last n)
    have h1 := ih (f := fun i => f i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have := Int.mul_nonneg h' h'
    have hme : -a * -a = a * a := by
      rw [Int.neg_mul_neg]
    omega

namespace Mat

/-- ‖A‖_F² = ⟨A, A⟩ ≥ 0. -/
theorem frob_self_nonneg {n p : Nat} (A : Mat n p) : 0 ≤ frob A A := by
  unfold frob
  refine fsum_nonneg (fun i => fsum_nonneg (fun j => sq_nonneg _))

section Prop2

variable {n p : Nat}

/-- Twice the projection onto the tangent space (Eq. (2)):
    2·P_X(G) = 2G − X(XᵀG + GᵀX). -/
def proj2 (X G : Mat n p) : Mat n p :=
  (G ⬝+ G) ⬝- (X ⬝* ((X.T ⬝* G) ⬝+ (G.T ⬝* X)))

/-- Key computation:  Xᵀ·(2 P_X M) = XᵀM − MᵀX  (twice the skew part of XᵀM).
    Needs X ∈ St(n,p). -/
theorem X_T_mul_proj2 (X M : Mat n p) (hX : OnStiefel X) :
    X.T ⬝* proj2 X M = (X.T ⬝* M) ⬝- (M.T ⬝* X) := by
  unfold proj2
  rw [mul_sub, mul_add, ← mul_assoc X.T X ((X.T ⬝* M) ⬝+ (M.T ⬝* X)), hX,
      eye_mul]
  apply ext; intro i j
  simp only [add, sub]
  omega

/-- Proposition 2 / §2: the projected gradient direction is tangent:
    Xᵀ(P_X M) + (P_X M)ᵀ X = 0  (stated for 2·P_X M). -/
theorem proj2_tangent (X M : Mat n p) (hX : OnStiefel X) :
    (X.T ⬝* proj2 X M) ⬝+ ((proj2 X M).T ⬝* X) = zero p p := by
  have h1 : (proj2 X M).T ⬝* X = (X.T ⬝* proj2 X M).T := by
    rw [T_mul, T_T]
  rw [h1, X_T_mul_proj2 X M hX, T_sub, T_mul, T_mul, T_T, T_T]
  apply ext; intro i j
  simp only [add, sub, T, zero]
  omega

/-- The matrix S₊ = XᵀM + MᵀX is symmetric. -/
theorem splus_sym (X M : Mat n p) : IsSym ((X.T ⬝* M) ⬝+ (M.T ⬝* X)) := by
  unfold IsSym
  rw [T_add, T_mul, T_mul, T_T, T_T]
  exact add_comm ..

/-- The matrix S₋ = XᵀM − MᵀX is skew-symmetric. -/
theorem sminus_skew (X M : Mat n p) : IsSkew ((X.T ⬝* M) ⬝- (M.T ⬝* X)) := by
  unfold IsSkew
  rw [T_sub, T_mul, T_mul, T_T, T_T]
  apply ext; intro i j
  simp only [sub, neg]
  omega

/-- Proposition 2, self-adjointness of the projection at M:
      ‖2·P_X M‖_F² = 2·⟨M, 2·P_X M⟩
    equivalently ⟨M, P_X M⟩ = ‖P_X M‖_F², the key identity behind the
    boundary witness B̂ = −P_X M / ‖P_X M‖₂. Needs X ∈ St(n,p). -/
theorem proj2_self_adjoint (X M : Mat n p) (hX : OnStiefel X) :
    frob (proj2 X M) (proj2 X M) = 2 * frob M (proj2 X M) := by
  -- ⟨2P M, 2P M⟩ − 2⟨M, 2P M⟩ = ⟨2P M − 2M, 2P M⟩ = −⟨X·S₊, 2P M⟩
  have key : frob (X ⬝* ((X.T ⬝* M) ⬝+ (M.T ⬝* X))) (proj2 X M) = 0 := by
    have h1 : frob (X ⬝* ((X.T ⬝* M) ⬝+ (M.T ⬝* X))) (proj2 X M)
        = frob (proj2 X M) (X ⬝* ((X.T ⬝* M) ⬝+ (M.T ⬝* X))) := frob_comm ..
    have h2 : frob (proj2 X M) (X ⬝* ((X.T ⬝* M) ⬝+ (M.T ⬝* X)))
        = frob (X.T ⬝* proj2 X M) ((X.T ⬝* M) ⬝+ (M.T ⬝* X)) := frob_mul_right ..
    have h3 : frob (X.T ⬝* proj2 X M) ((X.T ⬝* M) ⬝+ (M.T ⬝* X))
        = frob ((X.T ⬝* M) ⬝+ (M.T ⬝* X)) (X.T ⬝* proj2 X M) := frob_comm ..
    have h4 : frob ((X.T ⬝* M) ⬝+ (M.T ⬝* X)) (X.T ⬝* proj2 X M) = 0 := by
      rw [X_T_mul_proj2 X M hX]
      exact frob_sym_skew (splus_sym X M) (sminus_skew X M)
    omega
  have expand : frob (proj2 X M) (proj2 X M)
      = frob ((M ⬝+ M)) (proj2 X M)
        - frob (X ⬝* ((X.T ⬝* M) ⬝+ (M.T ⬝* X))) (proj2 X M) := by
    rw [← frob_sub_left]
    rfl
  have haddM : frob (M ⬝+ M) (proj2 X M)
      = frob M (proj2 X M) + frob M (proj2 X M) := frob_add_left ..
  omega

/-- Proposition 2, nonnegativity:  ⟨M, P_X M⟩ ≥ 0, i.e. the SMP witness
    B̂ ∝ −P_X M has objective ⟨M, B̂⟩ ≤ 0 (Eq. (7) has value ≤ 0). -/
theorem proj2_inner_nonneg (X M : Mat n p) (hX : OnStiefel X) :
    0 ≤ frob M (proj2 X M) := by
  have h1 := proj2_self_adjoint X M hX
  have h2 := frob_self_nonneg (proj2 X M)
  omega

/-- The witness direction −P_X M achieves a nonpositive SMP objective. -/
theorem witness_nonpositive (X M : Mat n p) (hX : OnStiefel X) :
    frob M (proj2 X M).neg ≤ 0 := by
  rw [frob_neg_right]
  have := proj2_inner_nonneg X M hX
  omega

end Prop2

section Alg2

variable {n p : Nat}

/-- Algorithm 2 / Eq. (13):  with C = [−X  M] and J = [[0,I],[−I,0]],
      C · J · Cᵀ = M Xᵀ − X Mᵀ  (= 2·skew(M Xᵀ)).
    This is the low-rank factorization that lets msign(skew(MXᵀ)) be computed
    from the 2p-column matrix C. Holds for ALL X, M (Stiefel not needed). -/
theorem alg2_factorization (X M : Mat n p) :
    ((hcat X.neg M) ⬝* Jmat p) ⬝* (hcat X.neg M).T
      = (M ⬝* X.T) ⬝- (X ⬝* M.T) := by
  rw [hcat_mul_J, hcat_mul_hcat_T]
  have h1 : M.neg ⬝* X.neg.T = M ⬝* X.T := by
    rw [T_neg, mul_neg, neg_mul, neg_neg]
  have h2 : X.neg ⬝* M.T = (X ⬝* M.T).neg := neg_mul ..
  rw [h1, h2, ← sub_eq_add_neg]

/-- The factorization target is indeed skew-symmetric. -/
theorem alg2_target_skew (X M : Mat n p) :
    IsSkew ((M ⬝* X.T) ⬝- (X ⬝* M.T)) := by
  unfold IsSkew
  rw [T_sub, T_mul, T_mul, T_T, T_T]
  apply ext; intro i j
  simp only [sub, neg]
  omega

end Alg2

end Mat

section DimensionCount

/-- Theorem 1, dimension count (cleared of the /2):
      p(p−1) + 2·p(n−p) + (n−p)(n−p−1) = n(n−1)
    i.e.  dim L_X + dim K_X = dim 𝒜ⁿ  with
    dim L_X = p(p−1)/2 + p(n−p) and dim K_X = (n−p)(n−p−1)/2.
    Proven as a ring identity over ℤ, for ALL n p (not just n ≥ p). -/
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

end DimensionCount


-- ============================================================================
-- Axiom audit: every theorem depends only on Lean's standard foundational
-- axioms (propext, Quot.sound; Classical.choice enters one proof through a
-- decidability instance) — no `sorry`, no `native_decide`/`ofReduceBool`.
-- ============================================================================
#print axioms Mat.skew_mul_mem_tangent
#print axioms Mat.objective_reformulation
#print axioms Mat.objective_sees_only_skew_part
#print axioms Mat.frob_sym_skew
#print axioms Mat.thm1_decomposition
#print axioms Mat.thm1_Yker_kills_X
#print axioms Mat.thm1_Ytilde_same_tangent
#print axioms Mat.thm1_Ytilde_skew
#print axioms Mat.thm1_Yker_skew
#print axioms Mat.thm1_orthogonality
#print axioms thm1_dimension_count
#print axioms Mat.X_T_mul_proj2
#print axioms Mat.proj2_tangent
#print axioms Mat.proj2_self_adjoint
#print axioms Mat.proj2_inner_nonneg
#print axioms Mat.witness_nonpositive
#print axioms Mat.alg2_factorization
#print axioms Mat.alg2_target_skew
