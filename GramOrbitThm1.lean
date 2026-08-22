/-
==============================================================================
 GramOrbitThm1.lean — Theorem 1 for the GRAM-PRESERVING Skewon analog
                      (OrbitMuon), general symbolic proofs, core Lean 4
==============================================================================

 Setting.  In the Stiefel/Skewon problem (arXiv:2608.06218) the weight X is
 orthonormal.  In the Gram-preserving analog ("OrbitMuon") the weight
 W ∈ R^{n×p} is a GENERAL matrix, moved along the left rotation orbit
 W ← R·W (RᵀR = I), which preserves the Gram matrix WᵀW exactly.  The
 update step solves, for a gradient G:

   (FACED PROBLEM)   min ⟨G, Δ⟩  over first-order Gram-preserving
                     directions Δ (i.e. ΔᵀW + WᵀΔ = 0), realized as
                     Δ = Y·W with a skew generator Y in a trust region.

   (SIMPLIFIED)      min ⟨N, Y⟩  over skew Y in the same trust region,
                     with N = skew(G·Wᵀ)  — the plain Skewon LMO,
                     solved in closed form by Y* = −msign(N).

 WHAT IS PROVEN (universally quantified over all n, p, all W, G, all
 skew Y; entries in ℤ with factors of ½ cleared; ring reasoning only,
 hence valid verbatim over ℝ):

 ── The two problems are THE SAME ──
   exact preservation:  RᵀR = I → (RW)ᵀ(RW) = WᵀW      (orbit_exact_gram)
   Y skew → (YW)ᵀW + Wᵀ(YW) = 0                       (orbit_tangent_gram)
   ⟨GWᵀ − WGᵀ, Y⟩ = 2⟨G, YW⟩ for skew Y        (objective_reformulation_W)
   value equivalence for ANY trust region P on Y      (gram_lmo_equivalence)
   direction sets coincide (full-rank W):
     {YW : Y skew} = {Δ : ΔᵀW + WᵀΔ = 0}                (direction_set_eq)
   NOTE: W is NOT assumed orthonormal anywhere above except where the
   factorization W = X·H is explicitly hypothesized.

 ── THEOREM 1 (direct sum 𝒜ⁿ = L_W ⊕ K_W) ──
 With W = X·H, X ∈ St(n,p), H invertible (the polar/QR factorization of a
 full-column-rank W; existence over ℝ is standard, H supplied with its
 inverse H' as data):
   Y = Ỹ + Y_ker                                      (thm1_decomposition)
   Y_ker·W = 0                                       (thm1W_Yker_kills_W)
   Ỹ·W = Y·W                                          (thm1W_same_action)
   K_W = K_X:  Y·W = 0  ↔  Y·X = 0                   (thm1W_kernel_char)
   Ỹ, Y_ker ∈ 𝒜ⁿ                        (thm1_Ytilde_skew, thm1_Yker_skew)
   ⟨Ỹ, Y_ker⟩ = 0                                    (thm1_orthogonality)
   kernel invisible to the objective:
     ⟨GWᵀ − WGᵀ, Y_ker(C)⟩ = 0                        (kernel_invisible_W)
   every Gram-tangent Δ is realized by the orbit      (gram_tangent_realized)
   dim L_W + dim K_W = dim 𝒜ⁿ:
     (2np − p(p+1)) + (n−p)(n−p−1) = n(n−1)      (thm1W_dimension_count)

 Consequence: optimizing ⟨G, Δ⟩ over Gram-preserving directions with the
 generator trust region ‖Y‖₂ ≤ 1 is EXACTLY the Skewon LMO on
 N = skew(GWᵀ); the kernel component K_W neither moves W nor changes the
 objective, so Y* = −msign(N) (Prop 1 of the paper) is optimal here too.

 Self-contained: core Lean 4, no Mathlib, no `sorry`, no `native_decide`.
 Infrastructure (Parts 1–2) is the verified matrix library shared with
 SkewonThm1Thm2.lean.  Axiom audit at end of file.
 Verified with Lean 4.15.0.  Run:  lean GramOrbitThm1.lean
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

/- The Stiefel-case machinery (verbatim from SkewonThm1Thm2.lean): §2
   lemmas, the L_X/K_X decomposition of Theorem 1, and the tangent
   lift.  These are reused because the orbit decomposition lives in
   the SAME subspaces L_X, K_X once W = X·H is factored. -/

namespace Mat

section GramOrbit

variable {n p : Nat}

theorem frob_zero_right (A : Mat n p) : frob A (zero n p) = 0 := by
  rw [frob_comm]
  exact frob_zero_left A

/-- Skewness is preserved by sums. -/
theorem isSkew_add {A B : Mat n n} (hA : IsSkew A) (hB : IsSkew B) :
    IsSkew (A ⬝+ B) := by
  unfold IsSkew
  rw [T_add, hA, hB]
  apply ext; intro i j
  simp only [add, neg]
  omega

/-- Congruence by any Q preserves skewness:  Z skew ⟹ Q·Z·Qᵀ skew. -/

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

-- ===========================================================================
-- THE GRAM-PRESERVING ORBIT PROBLEM (OrbitMuon), general W
-- ===========================================================================

/-- EXACT Gram preservation under the retraction: for any rotation R with
    RᵀR = I and ANY W,  (R·W)ᵀ(R·W) = WᵀW.  (This is why OrbitMuon retracts
    with a polar/Cayley orthogonal factor: the constraint holds exactly,
    not just to first order.) -/
theorem orbit_exact_gram (R : Mat n n) (W : Mat n p) (hR : R.T ⬝* R = eye n) :
    (R ⬝* W).T ⬝* (R ⬝* W) = W.T ⬝* W := by
  rw [T_mul, mul_assoc, ← mul_assoc R.T R W, hR, eye_mul]

/-- First-order Gram preservation: for skew Y the direction Δ = Y·W
    satisfies the Gram-tangency condition ΔᵀW + WᵀΔ = 0, for ANY W —
    orthonormality is never used (this is `skew_mul_mem_tangent` read at a
    general weight matrix). -/
theorem orbit_tangent_gram (W : Mat n p) (Y : Mat n n) (hY : IsSkew Y) :
    (W.T ⬝* (Y ⬝* W)) ⬝+ ((Y ⬝* W).T ⬝* W) = zero p p :=
  skew_mul_mem_tangent W Y hY

/-- The objective transfer at a GENERAL weight W (the heart of the
    reduction):  ⟨G·Wᵀ − W·Gᵀ, Y⟩ = 2⟨G, Y·W⟩  for skew Y.
    (`objective_reformulation` never used orthonormality of its first
    argument; here we state it at W to make that explicit.) -/
theorem objective_reformulation_W (W G : Mat n p) (Y : Mat n n)
    (hY : IsSkew Y) :
    frob ((G ⬝* W.T) ⬝- (W ⬝* G.T)) Y = 2 * frob G (Y ⬝* W) :=
  objective_reformulation W G Y hY

/-- THE TWO PROBLEMS ARE THE SAME (value form).  For ANY trust-region
    predicate P on the generator (e.g. ‖Y‖₂ ≤ 1) and every value v, the
    faced problem  min 2⟨G, Y·W⟩  and the simplified Skewon LMO
    min ⟨G·Wᵀ − W·Gᵀ, Y⟩  attain v on {Y skew, P Y} simultaneously —
    indeed via the SAME witness Y.  Hence identical optimal values and
    identical argmins; no spectral-norm facts are needed at all. -/
theorem gram_lmo_equivalence (W G : Mat n p) (P : Mat n n → Prop) (v : Int) :
    (∃ Y : Mat n n, IsSkew Y ∧ P Y ∧ 2 * frob G (Y ⬝* W) = v)
    ↔ (∃ Y : Mat n n, IsSkew Y ∧ P Y ∧
        frob ((G ⬝* W.T) ⬝- (W ⬝* G.T)) Y = v) := by
  constructor
  · rintro ⟨Y, hY, hP, hv⟩
    exact ⟨Y, hY, hP, by rw [objective_reformulation_W W G Y hY]; exact hv⟩
  · rintro ⟨Y, hY, hP, hv⟩
    exact ⟨Y, hY, hP, by rw [← objective_reformulation_W W G Y hY]; exact hv⟩

-- ===========================================================================
-- THEOREM 1 for the orbit:  W = X·H with X ∈ St(n,p), H invertible
-- (polar/QR factorization of a full-column-rank W; the inverse H' is
-- supplied as data with H·H' = H'·H = I).  The subspaces are the SAME
-- L_X, K_X as in the Stiefel case — Ytilde/Yker and their intrinsic
-- properties (decomposition, skewness, orthogonality) are the theorems
-- above; here we transport the ACTION statements from X to W.
-- ===========================================================================

/-- Theorem 1 (orbit), claim 1:  Y_ker · W = 0. -/
theorem thm1W_Yker_kills_W (X : Mat n p) (H : Mat p p) (W : Mat n p)
    (Y : Mat n n) (hX : OnStiefel X) (hW : W = X ⬝* H) :
    Yker X Y ⬝* W = zero n p := by
  rw [hW, ← mul_assoc, thm1_Yker_kills_X X Y hX, zero_mul]

/-- Theorem 1 (orbit), claim 2:  Ỹ · W = Y · W  (the two components induce
    the same orbit direction at W). -/
theorem thm1W_same_action (X : Mat n p) (H : Mat p p) (W : Mat n p)
    (Y : Mat n n) (hX : OnStiefel X) (hY : IsSkew Y) (hW : W = X ⬝* H) :
    Ytilde X Y ⬝* W = Y ⬝* W := by
  rw [hW, ← mul_assoc, ← mul_assoc, thm1_Ytilde_same_tangent X Y hX hY]

/-- The kernels coincide:  K_W = K_X, i.e.  Y·W = 0  ↔  Y·X = 0.
    (Right-invertibility of H is what encodes full column rank of W;
    this is where it is used.) -/
theorem thm1W_kernel_char (X : Mat n p) (H H' : Mat p p) (W : Mat n p)
    (Y : Mat n n) (hW : W = X ⬝* H) (hHH' : H ⬝* H' = eye p) :
    Y ⬝* W = zero n p ↔ Y ⬝* X = zero n p := by
  constructor
  · intro h
    have h' : (Y ⬝* X) ⬝* H = zero n p := by
      rw [hW, ← mul_assoc] at h
      exact h
    calc Y ⬝* X = (Y ⬝* X) ⬝* eye p := (mul_eye _).symm
      _ = (Y ⬝* X) ⬝* (H ⬝* H') := by rw [hHH']
      _ = ((Y ⬝* X) ⬝* H) ⬝* H' := (mul_assoc ..).symm
      _ = zero n p ⬝* H' := by rw [h']
      _ = zero n p := zero_mul H'
  · intro h
    rw [hW, ← mul_assoc, h, zero_mul]

/-- The kernel component is invisible to the orbit objective:
    ⟨G·Wᵀ − W·Gᵀ, Y_ker(C)⟩ = 0  for every skew C.  Optimization may
    therefore be restricted to L_X without loss. -/
theorem kernel_invisible_W (X : Mat n p) (H : Mat p p) (W G : Mat n p)
    (C : Mat n n) (hX : OnStiefel X) (hW : W = X ⬝* H) (hC : IsSkew C) :
    frob ((G ⬝* W.T) ⬝- (W ⬝* G.T)) (Yker X C) = 0 := by
  rw [objective_reformulation_W W G (Yker X C) (thm1_Yker_skew X C hC),
      thm1W_Yker_kills_W X H W C hX hW, frob_zero_right]
  omega

/-- SURJECTIVITY: every first-order Gram-preserving direction Δ at a
    full-column-rank W is realized by the orbit — there is a skew Y with
    Y·W = Δ (explicitly, Y = Ỹ(Δ·H⁻¹) via the Theorem-1 lift).  Together
    with `orbit_tangent_gram` this shows the faced problem's feasible
    directions and the orbit directions are the SAME set. -/
theorem gram_tangent_realized (X : Mat n p) (H H' : Mat p p) (W Δ : Mat n p)
    (hX : OnStiefel X) (hW : W = X ⬝* H)
    (hHH' : H ⬝* H' = eye p) (hH'H : H' ⬝* H = eye p)
    (hΔ : (W.T ⬝* Δ) ⬝+ (Δ.T ⬝* W) = zero p p) :
    ∃ Y : Mat n n, IsSkew Y ∧ Y ⬝* W = Δ := by
  -- Gram-tangency at W transports to Stiefel-tangency of B := Δ·H' at X.
  have hΔ' : (H.T ⬝* (X.T ⬝* Δ)) ⬝+ ((Δ.T ⬝* X) ⬝* H) = zero p p := by
    have h := hΔ
    rw [hW, T_mul, mul_assoc H.T X.T Δ, ← mul_assoc Δ.T X H] at h
    exact h
  have h2 : ((H'.T ⬝* (H.T ⬝* (X.T ⬝* Δ))) ⬝* H')
      ⬝+ ((H'.T ⬝* ((Δ.T ⬝* X) ⬝* H)) ⬝* H') = zero p p := by
    have hz : (H'.T ⬝* ((H.T ⬝* (X.T ⬝* Δ)) ⬝+ ((Δ.T ⬝* X) ⬝* H))) ⬝* H'
        = zero p p := by
      rw [hΔ', mul_zero, zero_mul]
    rw [mul_add, add_mul] at hz
    exact hz
  have e1 : (H'.T ⬝* (H.T ⬝* (X.T ⬝* Δ))) ⬝* H' = (X.T ⬝* Δ) ⬝* H' := by
    rw [← mul_assoc H'.T H.T (X.T ⬝* Δ), ← T_mul H H', hHH', T_eye, eye_mul]
  have e2 : (H'.T ⬝* ((Δ.T ⬝* X) ⬝* H)) ⬝* H' = H'.T ⬝* (Δ.T ⬝* X) := by
    rw [mul_assoc H'.T ((Δ.T ⬝* X) ⬝* H) H', mul_assoc (Δ.T ⬝* X) H H',
        hHH', mul_eye]
  have hBt : (X.T ⬝* (Δ ⬝* H')) ⬝+ ((Δ ⬝* H').T ⬝* X) = zero p p := by
    rw [e1, e2] at h2
    rw [← mul_assoc X.T Δ H', T_mul Δ H', mul_assoc H'.T Δ.T X]
    exact h2
  refine ⟨liftT X (Δ ⬝* H'), liftT_skew X _ hBt, ?_⟩
  rw [hW, ← mul_assoc, liftT_maps_to X _ hX hBt, mul_assoc, hH'H, mul_eye]

/-- THE DIRECTION SETS COINCIDE (the faced problem over Gram-preserving Δ
    and the simplified problem over skew generators optimize over the same
    set):  {Y·W : Y ∈ 𝒜ⁿ}  =  {Δ : ΔᵀW + WᵀΔ = 0}  for full-column-rank W. -/
theorem direction_set_eq (X : Mat n p) (H H' : Mat p p) (W Δ : Mat n p)
    (hX : OnStiefel X) (hW : W = X ⬝* H)
    (hHH' : H ⬝* H' = eye p) (hH'H : H' ⬝* H = eye p) :
    (∃ Y : Mat n n, IsSkew Y ∧ Y ⬝* W = Δ)
    ↔ (W.T ⬝* Δ) ⬝+ (Δ.T ⬝* W) = zero p p := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact orbit_tangent_gram W Y hY
  · exact gram_tangent_realized X H H' W Δ hX hW hHH' hH'H

end GramOrbit
end Mat
/- Dimension count for the orbit decomposition. -/

/-- Theorem 1 (orbit), dimension count (cleared of the /2):
      (2np − p(p+1)) + (n−p)(n−p−1) = n(n−1)
    i.e.  dim L_W + dim K_W = dim 𝒜ⁿ  with
    dim L_W = np − p(p+1)/2  (= the dimension of the Gram-tangent space
    {Δ : ΔᵀW + WᵀΔ = 0}, a symmetric p×p constraint on an n×p matrix)
    and dim K_W = (n−p)(n−p−1)/2.  Proven as a ring identity over ℤ. -/
theorem thm1W_dimension_count (n p : Int) :
    (2 * (n * p) - p * (p + 1)) + (n - p) * (n - p - 1) = n * (n - 1) := by
  have h1 : p * (p + 1) = p * p + p := by
    rw [Int.mul_add, Int.mul_one]
  have h2 : (n - p) * (n - p - 1) = (n - p) * (n - p) - (n - p) := by
    rw [Int.mul_sub, Int.mul_one]
  have h3 : (n - p) * (n - p) = n * n - p * n - p * n + p * p := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm n p]
    omega
  have h4 : n * (n - 1) = n * n - n := by
    rw [Int.mul_sub, Int.mul_one]
  have h5 : n * p = p * n := Int.mul_comm n p
  rw [h1, h2, h3, h4, h5]
  omega

-- ============================================================================
-- Axiom audit: every theorem depends only on Lean's standard foundational
-- axioms — no `sorry`, no `native_decide`/`ofReduceBool`.
-- ============================================================================
#print axioms Mat.orbit_exact_gram
#print axioms Mat.orbit_tangent_gram
#print axioms Mat.objective_reformulation_W
#print axioms Mat.gram_lmo_equivalence
#print axioms Mat.thm1_decomposition
#print axioms Mat.thm1W_Yker_kills_W
#print axioms Mat.thm1W_same_action
#print axioms Mat.thm1W_kernel_char
#print axioms Mat.thm1_Ytilde_skew
#print axioms Mat.thm1_Yker_skew
#print axioms Mat.thm1_orthogonality
#print axioms Mat.kernel_invisible_W
#print axioms Mat.gram_tangent_realized
#print axioms Mat.direction_set_eq
#print axioms thm1W_dimension_count
