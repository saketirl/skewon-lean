/-
==============================================================================
 CompSkewonThm1.lean — Theorem 1 for the COMPOSITION-PRESERVING Skewon
                       analog (ComposedSkewon), core Lean 4
==============================================================================

 Setting.  In attention, what encodes a task is not W_q or W_k alone but
 their compositions  M = W_qᵀW_k  and  N = W_o·W_v.  ComposedSkewon
 preserves the SPECTRUM of the composition P = A·B by moving the factors
 along a two-sided rotation orbit:

     A ← R_L·A,   B ← B·R_R      (R_Lᵀ R_L = I,  R_R R_Rᵀ = I)
  ⟹  P ← R_L·P·R_R              (singular values of P exactly preserved)

 with generators Y, Z skew and retraction R = polar(I + ηY) (Newton–
 Schulz; NO Cayley transform, NO matrix inverse anywhere).

 WHAT IS PROVEN (universally quantified over all shapes and all A, B,
 G_P, skew Y, Z; entries ℤ, factors of ½ cleared, ring reasoning only —
 valid verbatim over ℝ):

 ── Factor updates realize composition orbits ──
   (R·A)·B = R·(A·B),  A·(B·R) = (A·B)·R    (left/right_rotation_acts)
   exact Gram/spectrum invariance:
     left-only:   ((R·A)·B)ᵀ((R·A)·B) = PᵀP           (comp_left_exact_gram)
     two-sided:   Gram conjugates by R_R               (comp_two_sided_conj)

 ── OVER-RIGIDITY: exact product preservation is the WRONG problem ──
   the gauge  dA = A·X, dB = −X·B  preserves P exactly:
     (A·X)·B − A·(X·B) = 0                             (gauge_kills_comp)
   and for ANY loss that reaches A, B only through P (G_A = G_P·Bᵀ,
   G_B = Aᵀ·G_P), the objective is IDENTICALLY ZERO along the gauge:
     ⟨G_A, A·X⟩ − ⟨G_B, X·B⟩ = 0  for all X          (gauge_zero_objective)
   ⟹ constraining to exact product preservation leaves no first-order
   descent direction; the correct relaxation is the two-sided orbit.

 ── The faced problem = two independent simplified Skewon LMOs ──
   factor-level objective = composition-level objective:
     ⟨G_P·Bᵀ, Y·A⟩ = ⟨G_P, Y·P⟩                    (left_factor_objective)
     ⟨Aᵀ·G_P, B·Z⟩ = ⟨G_P, P·Z⟩                   (right_factor_objective)
   Skewon reformulations at the composition:
     ⟨G_P·Pᵀ − P·G_Pᵀ, Y⟩ = 2⟨G_P, Y·P⟩            (left via GramOrbit)
     ⟨Pᵀ·G_P − G_Pᵀ·P, Z⟩ = 2⟨G_P, P·Z⟩         (right_reformulation)
   the msign arguments the IMPLEMENTATION computes from factor gradients
   equal the composition-level ones:
     (G_P·Bᵀ)·Aᵀ = G_P·Pᵀ,   Bᵀ·(Aᵀ·G_P) = Pᵀ·G_P   (msign_args_match)
   VALUE EQUIVALENCE with separated trust regions P_L, P_R (arbitrary
   predicates — no spectral-norm facts needed, same witnesses):
     min 2⟨G_P, Y·P + P·Z⟩  ≡  min ⟨N_L, Y⟩ + ⟨N_R, Z⟩,
     N_L = G_P·Pᵀ − P·G_Pᵀ,  N_R = Pᵀ·G_P − G_Pᵀ·P   (comp_lmo_equivalence)
   and the sum splits into two INDEPENDENT problems     (comp_lmo_separates)

 Consequence: the optimal generators are the two independent Skewon
 closed forms  Y* = −msign(skew(G_A·Aᵀ)),  Z* = −msign(skew(Bᵀ·G_B))
 (Prop 1 of arXiv:2608.06218 applied twice) — exactly what
 frozen_residual_ubv/composed_skewon.py implements, with polar
 (Newton–Schulz) retraction and no Cayley/inverse.

 Self-contained: core Lean 4, no Mathlib, no `sorry`, no `native_decide`.
 Verified with Lean 4.15.0.  Run:  lean CompSkewonThm1.lean
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

/- The §2 objective-reformulation lemma of the paper, valid at a GENERAL
   first argument (orthonormality never used) — from SkewonThm1Thm2.lean. -/

namespace Mat

theorem objective_reformulation {n p : Nat} (X M : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
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


section CompOrbit

variable {m r n : Nat}

-- ===========================================================================
-- Factor-level rotations realize composition-level orbits
-- ===========================================================================

/-- Rotating the left factor rotates the composition:  (R·A)·B = R·(A·B). -/
theorem left_rotation_acts (R : Mat m m) (A : Mat m r) (B : Mat r n) :
    (R ⬝* A) ⬝* B = R ⬝* (A ⬝* B) :=
  mul_assoc R A B

/-- Rotating the right factor rotates the composition:  A·(B·R) = (A·B)·R. -/
theorem right_rotation_acts (A : Mat m r) (B : Mat r n) (R : Mat n n) :
    A ⬝* (B ⬝* R) = (A ⬝* B) ⬝* R :=
  (mul_assoc A B R).symm

/-- The per-leg Gram is exactly preserved by the left step: (R·A)ᵀ(R·A) = AᵀA.
    (ComposedSkewon preserves BOTH per-leg Grams and composition spectrum.) -/
theorem factor_gram_exact (R : Mat m m) (A : Mat m r)
    (hR : R.T ⬝* R = eye m) :
    (R ⬝* A).T ⬝* (R ⬝* A) = A.T ⬝* A := by
  rw [T_mul, mul_assoc, ← mul_assoc R.T R A, hR, eye_mul]

/-- EXACT invariance, left-only step: the Gram of the COMPOSITION is exactly
    preserved when only the left factor is rotated. -/
theorem comp_left_exact_gram (R : Mat m m) (A : Mat m r) (B : Mat r n)
    (hR : R.T ⬝* R = eye m) :
    ((R ⬝* A) ⬝* B).T ⬝* ((R ⬝* A) ⬝* B) = (A ⬝* B).T ⬝* (A ⬝* B) := by
  rw [left_rotation_acts]
  exact factor_gram_exact R (A ⬝* B) hR

/-- EXACT invariance, two-sided step: the Gram of the composition is
    orthogonally conjugated by R_R — for orthogonal R_R this is a
    similarity, so the eigenvalues of PᵀP (the squared singular values of
    P = A·B) are exactly preserved. -/
theorem comp_two_sided_conj (RL : Mat m m) (RR : Mat n n)
    (A : Mat m r) (B : Mat r n) (hL : RL.T ⬝* RL = eye m) :
    ((RL ⬝* A) ⬝* (B ⬝* RR)).T ⬝* ((RL ⬝* A) ⬝* (B ⬝* RR))
      = (RR.T ⬝* ((A ⬝* B).T ⬝* (A ⬝* B))) ⬝* RR := by
  have hform : (RL ⬝* A) ⬝* (B ⬝* RR) = (RL ⬝* (A ⬝* B)) ⬝* RR := by
    rw [← mul_assoc (RL ⬝* A) B RR, left_rotation_acts]
  have hgram := factor_gram_exact RL (A ⬝* B) hL
  calc ((RL ⬝* A) ⬝* (B ⬝* RR)).T ⬝* ((RL ⬝* A) ⬝* (B ⬝* RR))
      = ((RL ⬝* (A ⬝* B)) ⬝* RR).T ⬝* ((RL ⬝* (A ⬝* B)) ⬝* RR) := by
        rw [hform]
    _ = (RR.T ⬝* (RL ⬝* (A ⬝* B)).T) ⬝* ((RL ⬝* (A ⬝* B)) ⬝* RR) := by
        rw [T_mul]
    _ = RR.T ⬝* ((RL ⬝* (A ⬝* B)).T ⬝* ((RL ⬝* (A ⬝* B)) ⬝* RR)) :=
        mul_assoc ..
    _ = RR.T ⬝* (((RL ⬝* (A ⬝* B)).T ⬝* (RL ⬝* (A ⬝* B))) ⬝* RR) := by
        rw [← mul_assoc ((RL ⬝* (A ⬝* B)).T) (RL ⬝* (A ⬝* B)) RR]
    _ = RR.T ⬝* (((A ⬝* B).T ⬝* (A ⬝* B)) ⬝* RR) := by rw [hgram]
    _ = (RR.T ⬝* ((A ⬝* B).T ⬝* (A ⬝* B))) ⬝* RR := (mul_assoc ..).symm

/-- Frobenius norm of the composition is exactly invariant under the
    two-sided step:  ‖(R_L·A)·(B·R_R)‖²_F = ‖A·B‖²_F. -/
theorem comp_frobenius_invariant (RL : Mat m m) (RR : Mat n n)
    (A : Mat m r) (B : Mat r n)
    (hL : RL.T ⬝* RL = eye m) (hR : RR ⬝* RR.T = eye n) :
    frob ((RL ⬝* A) ⬝* (B ⬝* RR)) ((RL ⬝* A) ⬝* (B ⬝* RR))
      = frob (A ⬝* B) (A ⬝* B) := by
  have hform : (RL ⬝* A) ⬝* (B ⬝* RR) = (RL ⬝* (A ⬝* B)) ⬝* RR := by
    rw [← mul_assoc (RL ⬝* A) B RR, left_rotation_acts]
  rw [hform]
  have s1 : frob ((RL ⬝* (A ⬝* B)) ⬝* RR) ((RL ⬝* (A ⬝* B)) ⬝* RR)
      = frob (RL ⬝* (A ⬝* B)) (RL ⬝* (A ⬝* B)) := by
    rw [frob_mul_left ((RL ⬝* (A ⬝* B)) ⬝* RR) (RL ⬝* (A ⬝* B)) RR,
        mul_assoc (RL ⬝* (A ⬝* B)) RR RR.T, hR, mul_eye]
  rw [s1, frob_mul_right (RL ⬝* (A ⬝* B)) RL (A ⬝* B),
      ← mul_assoc RL.T RL (A ⬝* B), hL, eye_mul]

-- ===========================================================================
-- OVER-RIGIDITY: exact product preservation is the wrong problem
-- ===========================================================================

/-- The gauge direction (dA = A·X, dB = −X·B) preserves the product exactly
    to first order:  (A·X)·B − A·(X·B) = 0  for EVERY X. -/
theorem gauge_kills_comp (A : Mat m r) (X : Mat r r) (B : Mat r n) :
    ((A ⬝* X) ⬝* B) ⬝- (A ⬝* (X ⬝* B)) = zero m n := by
  rw [mul_assoc]
  apply ext; intro i j
  simp only [sub, zero]
  omega

/-- ZERO GRADIENT along the gauge: if the loss reaches the factors only
    through the composition (chain rule:  G_A = G_P·Bᵀ,  G_B = Aᵀ·G_P),
    then the first-order loss change along (dA, dB) = (A·X, −X·B) is
    identically zero for EVERY X:
      ⟨G_A, A·X⟩ − ⟨G_B, X·B⟩ = 0.
    Hence constraining updates to preserve the product EXACTLY leaves no
    first-order descent direction — the correct relaxation is the
    two-sided orbit below. -/
theorem gauge_zero_objective (A : Mat m r) (B : Mat r n) (GP : Mat m n)
    (X : Mat r r) :
    frob (GP ⬝* B.T) (A ⬝* X) - frob (A.T ⬝* GP) (X ⬝* B) = 0 := by
  have h1 : frob (GP ⬝* B.T) (A ⬝* X) = frob (A.T ⬝* (GP ⬝* B.T)) X :=
    frob_mul_right ..
  have h2 : frob (A.T ⬝* GP) (X ⬝* B) = frob ((A.T ⬝* GP) ⬝* B.T) X :=
    frob_mul_left ..
  rw [h1, h2, mul_assoc A.T GP B.T]
  omega

-- ===========================================================================
-- The faced problem = two independent simplified Skewon LMOs
-- ===========================================================================

/-- Factor-level objective = composition-level objective (left step):
    ⟨G_P·Bᵀ, Y·A⟩ = ⟨G_P, Y·(A·B)⟩.  The gradient the implementation gets
    from autograd on the factor sees exactly the composition objective. -/
theorem left_factor_objective (A : Mat m r) (B : Mat r n) (GP : Mat m n)
    (Y : Mat m m) :
    frob (GP ⬝* B.T) (Y ⬝* A) = frob GP (Y ⬝* (A ⬝* B)) := by
  calc frob (GP ⬝* B.T) (Y ⬝* A)
      = frob GP ((Y ⬝* A) ⬝* B) := (frob_mul_left GP (Y ⬝* A) B).symm
    _ = frob GP (Y ⬝* (A ⬝* B)) := by rw [mul_assoc]

/-- Factor-level objective = composition-level objective (right step):
    ⟨Aᵀ·G_P, B·Z⟩ = ⟨G_P, (A·B)·Z⟩. -/
theorem right_factor_objective (A : Mat m r) (B : Mat r n) (GP : Mat m n)
    (Z : Mat n n) :
    frob (A.T ⬝* GP) (B ⬝* Z) = frob GP ((A ⬝* B) ⬝* Z) := by
  calc frob (A.T ⬝* GP) (B ⬝* Z)
      = frob GP (A ⬝* (B ⬝* Z)) := (frob_mul_right GP A (B ⬝* Z)).symm
    _ = frob GP ((A ⬝* B) ⬝* Z) := by rw [← mul_assoc]

/-- Right-orbit Skewon reformulation at the composition (cleared of ½):
    ⟨Pᵀ·G_P − G_Pᵀ·P, Z⟩ = 2⟨G_P, P·Z⟩  for skew Z — the mirror of the
    left reformulation `objective_reformulation P G_P Y`. -/
theorem right_reformulation (P GP : Mat m n) (Z : Mat n n) (hZ : IsSkew Z) :
    frob ((P.T ⬝* GP) ⬝- (GP.T ⬝* P)) Z = 2 * frob GP (P ⬝* Z) := by
  have base := objective_reformulation P.T GP.T Z hZ
  rw [T_T, T_T] at base
  have hswap : frob GP.T (Z ⬝* P.T) = frob GP (P ⬝* Z.T) := by
    have h1 : (P ⬝* Z.T).T = Z ⬝* P.T := by rw [T_mul, T_T]
    rw [← h1, frob_T_T]
  have hneg : frob GP (P ⬝* Z.T) = -(frob GP (P ⬝* Z)) := by
    rw [hZ, mul_neg, frob_neg_right]
  rw [hswap, hneg] at base
  have hflip : frob ((P.T ⬝* GP) ⬝- (GP.T ⬝* P)) Z
      = -(frob ((GP.T ⬝* P) ⬝- (P.T ⬝* GP)) Z) := by
    rw [frob_sub_left, frob_sub_left]
    omega
  rw [hflip, base]
  omega

/-- The msign arguments computed by the IMPLEMENTATION from factor
    gradients equal the composition-level ones (left):
    G_A·Aᵀ = (G_P·Bᵀ)·Aᵀ = G_P·Pᵀ. -/
theorem msign_args_match_left (A : Mat m r) (B : Mat r n) (GP : Mat m n) :
    (GP ⬝* B.T) ⬝* A.T = GP ⬝* (A ⬝* B).T := by
  rw [T_mul, mul_assoc]

/-- The msign arguments match (right):  Bᵀ·G_B = Bᵀ·(Aᵀ·G_P) = Pᵀ·G_P. -/
theorem msign_args_match_right (A : Mat m r) (B : Mat r n) (GP : Mat m n) :
    B.T ⬝* (A.T ⬝* GP) = (A ⬝* B).T ⬝* GP := by
  rw [T_mul, mul_assoc]

/-- THE TWO PROBLEMS ARE THE SAME (value form).  For ANY trust-region
    predicates P_L, P_R on the two generators and every value v, the faced
    problem  min 2⟨G_P, Y·P + P·Z⟩  over {Y, Z skew, P_L Y, P_R Z}  and
    the simplified pair of Skewon LMOs
      min ⟨N_L, Y⟩ + ⟨N_R, Z⟩,   N_L = G_P·Pᵀ − P·G_Pᵀ,
                                  N_R = Pᵀ·G_P − G_Pᵀ·P
    attain v simultaneously — via the SAME witnesses.  No spectral-norm
    facts are needed. -/
theorem comp_lmo_equivalence (P GP : Mat m n)
    (PL : Mat m m → Prop) (PR : Mat n n → Prop) (v : Int) :
    (∃ (Y : Mat m m) (Z : Mat n n), IsSkew Y ∧ IsSkew Z ∧ PL Y ∧ PR Z ∧
        2 * frob GP ((Y ⬝* P) ⬝+ (P ⬝* Z)) = v)
    ↔ (∃ (Y : Mat m m) (Z : Mat n n), IsSkew Y ∧ IsSkew Z ∧ PL Y ∧ PR Z ∧
        frob ((GP ⬝* P.T) ⬝- (P ⬝* GP.T)) Y
          + frob ((P.T ⬝* GP) ⬝- (GP.T ⬝* P)) Z = v) := by
  have key : ∀ (Y : Mat m m) (Z : Mat n n), IsSkew Y → IsSkew Z →
      frob ((GP ⬝* P.T) ⬝- (P ⬝* GP.T)) Y
        + frob ((P.T ⬝* GP) ⬝- (GP.T ⬝* P)) Z
      = 2 * frob GP ((Y ⬝* P) ⬝+ (P ⬝* Z)) := by
    intro Y Z hY hZ
    rw [frob_add_right, objective_reformulation P GP Y hY,
        right_reformulation P GP Z hZ]
    omega
  constructor
  · rintro ⟨Y, Z, hY, hZ, hPL, hPR, hv⟩
    exact ⟨Y, Z, hY, hZ, hPL, hPR, by rw [key Y Z hY hZ]; exact hv⟩
  · rintro ⟨Y, Z, hY, hZ, hPL, hPR, hv⟩
    exact ⟨Y, Z, hY, hZ, hPL, hPR, by rw [← key Y Z hY hZ]; exact hv⟩

/-- SEPARATION: the joint problem splits into two INDEPENDENT Skewon LMOs
    (the objective is a sum and the constraints do not couple Y and Z), so
    each is solved by its own closed form  Y* = −msign(N_L),
    Z* = −msign(N_R). -/
theorem comp_lmo_separates (NL : Mat m m) (NR : Mat n n)
    (PL : Mat m m → Prop) (PR : Mat n n → Prop) (v : Int) :
    (∃ (Y : Mat m m) (Z : Mat n n), IsSkew Y ∧ IsSkew Z ∧ PL Y ∧ PR Z ∧
        frob NL Y + frob NR Z = v)
    ↔ (∃ v1 v2 : Int, v1 + v2 = v
        ∧ (∃ Y : Mat m m, IsSkew Y ∧ PL Y ∧ frob NL Y = v1)
        ∧ (∃ Z : Mat n n, IsSkew Z ∧ PR Z ∧ frob NR Z = v2)) := by
  constructor
  · rintro ⟨Y, Z, hY, hZ, hPL, hPR, hv⟩
    exact ⟨frob NL Y, frob NR Z, hv, ⟨Y, hY, hPL, rfl⟩, ⟨Z, hZ, hPR, rfl⟩⟩
  · rintro ⟨v1, v2, hsum, ⟨Y, hY, hPL, h1⟩, ⟨Z, hZ, hPR, h2⟩⟩
    exact ⟨Y, Z, hY, hZ, hPL, hPR, by rw [h1, h2]; exact hsum⟩

end CompOrbit
end Mat

-- ============================================================================
-- Axiom audit: only Lean's standard foundational axioms — no `sorry`,
-- no `native_decide`/`ofReduceBool`.
-- ============================================================================
#print axioms Mat.left_rotation_acts
#print axioms Mat.right_rotation_acts
#print axioms Mat.factor_gram_exact
#print axioms Mat.comp_left_exact_gram
#print axioms Mat.comp_two_sided_conj
#print axioms Mat.comp_frobenius_invariant
#print axioms Mat.gauge_kills_comp
#print axioms Mat.gauge_zero_objective
#print axioms Mat.left_factor_objective
#print axioms Mat.right_factor_objective
#print axioms Mat.right_reformulation
#print axioms Mat.msign_args_match_left
#print axioms Mat.msign_args_match_right
#print axioms Mat.comp_lmo_equivalence
#print axioms Mat.comp_lmo_separates
