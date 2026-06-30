import Mathlib
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedRCasesPattern false

open Set

universe u

namespace OMinimal

abbrev Rn (R : Type u) (n : Nat) := Fin n → R

def IsFiniteUnionOfPointsAndIntervals [LinearOrder R] (A : Set R) : Prop :=
  ∃ L : List (Set R),
    (∀ I ∈ L,
      (∃ a, I = ({a} : Set R)) ∨
      (∃ a b, I = Ioo a b) ∨
      (∃ a, I = Iio a) ∨
      (∃ a, I = Ioi a) ∨
      I = univ) ∧
    A = ⋃ I ∈ L, I

structure OMinimalStructure
    (R : Type u) [LinearOrder R]
    [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R] where
  S : (n : Nat) → Set (Rn R n) → Prop

  -- axiom (1): Boolean algebra on Rⁿ
  empty_mem : ∀ n, S n ∅
  union_mem : ∀ {n} {A B : Set (Rn R n)}, S n A → S n B → S n (A ∪ B)
  compl_mem : ∀ {n} {A : Set (Rn R n)}, S n A → S n Aᶜ

  -- axiom (2): cylinder closure
  right_cylinder_mem :
    ∀ {n} {A : Set (Rn R n)},
      S n A →
      S (n + 1)
        {x : Rn R (n + 1) | (fun i : Fin n => x (Fin.castSucc i)) ∈ A}

  left_cylinder_mem :
    ∀ {n} {B : Set (Rn R n)},
      S n B →
      S (n + 1)
        {x : Rn R (n + 1) | (fun i : Fin n => x (Fin.succ i)) ∈ B}

  -- axiom (3): diagonals
  diagonal_mem :
    ∀ {n} (i j : Fin n), i < j →
      S n {x : Rn R n | x i = x j}

  -- axiom (4): usual last-coordinate projection
  proj_mem :
    ∀ {n} {A : Set (Rn R (n + 1))},
      S (n + 1) A →
      S n {x : Rn R n | ∃ y : R, Fin.snoc x y ∈ A}

  -- axiom (5): points and order
  point_mem : ∀ r : R, S 1 {x : Rn R 1 | x 0 = r}
  order_mem : S 2 {x : Rn R 2 | x 0 < x 1}

  -- axiom (6): o-minimality on R
  ominimal :
    ∀ A : Set (Rn R 1),
      S 1 A ↔ IsFiniteUnionOfPointsAndIntervals {r : R | (fun _ : Fin 1 => r) ∈ A}

variable {R : Type u} [LinearOrder R]
  [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R]

variable (M : OMinimalStructure R)

theorem inter_mem {n} {A B : Set (Rn R n)} (hA : M.S n A) (hB : M.S n B) : M.S n (A ∩ B) := by
  rw [inter_eq_compl_compl_union_compl]
  exact M.compl_mem (M.union_mem (M.compl_mem hA) (M.compl_mem hB))

theorem theorem_i (n : Nat) : M.S n ∅ := M.empty_mem n

theorem theorem_ii {n} {A B : Set (Rn R n)} (hA : M.S n A) (hB : M.S n B) : M.S n (A ∪ B) :=
  M.union_mem hA hB

theorem theorem_iii {n} {A B : Set (Rn R n)} (hA : M.S n A) (hB : M.S n B) : M.S n (A ∩ B) := by
  have h : M.S n ((Aᶜ ∪ Bᶜ)ᶜ) := M.compl_mem (M.union_mem (M.compl_mem hA) (M.compl_mem hB))
  simpa [compl_union] using h

theorem theorem_iv {n} {A : Set (Rn R n)} (hA : M.S n A) : M.S n Aᶜ := M.compl_mem hA

theorem theorem_v {n} (i j : Fin n) (hij : i < j) : M.S n {x : Rn R n | x i = x j} :=
  M.diagonal_mem i j hij

theorem theorem_x : M.S 2 {x : Rn R 2 | x 0 < x 1} := M.order_mem

theorem theorem_xi (A : Set (Rn R 1)) :
    M.S 1 A ↔ IsFiniteUnionOfPointsAndIntervals {r : R | (fun _ : Fin 1 => r) ∈ A} :=
  M.ominimal A

-- Helper lemmas
def projLast {n : ℕ} : Set (Rn R (n + 1)) → Set (Rn R n) :=
  fun A => {x | ∃ y : R, Fin.snoc x y ∈ A}

def projBlock (n : ℕ) : ∀ m : ℕ, Set (Rn R (n + m)) → Set (Rn R n)
| Nat.zero, A => {x : Rn R n | (fun (k : Fin (n + 0)) => x (Fin.cast (Nat.add_zero n).symm k)) ∈ A}
| Nat.succ m, A => projBlock n m (projLast A)

@[simp] lemma projBlock_zero {n : ℕ} (A : Set (Rn R (n + 0))) :
    projBlock n Nat.zero A = {x : Rn R n | (fun (k : Fin (n + 0)) => x (Fin.cast (Nat.add_zero n).symm k)) ∈ A} := rfl

@[simp] lemma projBlock_succ {n m : ℕ} (A : Set (Rn R (n + Nat.succ m))) :
    projBlock n (Nat.succ m) A = projBlock n m (projLast A) := rfl

theorem right_cylinder_iter_mem {n m} {A : Set (Rn R n)} (hA : M.S n A) :
    M.S (n + m) {z : Rn R (n + m) | (fun i : Fin n => z (Fin.castAdd m i)) ∈ A} := by
  induction m with
  | zero => exact hA
  | succ m ih => exact M.right_cylinder_mem ih

lemma cast_mem {n1 n2 : ℕ} (heq : n1 = n2) {A : Set (Rn R n1)} (hA : M.S n1 A) :
    M.S n2 {z : Rn R n2 | (fun i : Fin n1 => z (Fin.cast heq i)) ∈ A} := by
  subst heq
  have h_eq : {z : Rn R n1 | (fun i : Fin n1 => z (Fin.cast rfl i)) ∈ A} = A := by ext z; rfl
  exact h_eq ▸ hA

theorem left_cylinder_iter_mem {n m} {B : Set (Rn R m)} (hB : M.S m B) :
    M.S (n + m) {z : Rn R (n + m) | (fun j : Fin m => z (Fin.natAdd n j)) ∈ B} := by
  induction n with
  | zero =>
      have heq : 0 + m = m := Nat.zero_add m
      have hcast := cast_mem M heq.symm hB
      have h_eq : {z : Rn R (0 + m) | (fun j : Fin m => z (Fin.natAdd 0 j)) ∈ B} =
                  {z : Rn R (0 + m) | (fun i : Fin m => z (Fin.cast heq.symm i)) ∈ B} := by
        ext z
        change (fun j : Fin m => z (Fin.natAdd 0 j)) ∈ B ↔ (fun i : Fin m => z (Fin.cast heq.symm i)) ∈ B
        have h_fun : (fun j : Fin m => z (Fin.natAdd 0 j)) = (fun i : Fin m => z (Fin.cast heq.symm i)) := by
          funext j; congr 1; ext; simp [Fin.natAdd, Fin.cast]
        rw [h_fun]
      rw [h_eq]
      exact hcast
  | succ n ih =>
      have h1 := M.left_cylinder_mem ih
      have heq : n + m + 1 = n + 1 + m := by omega
      have hcast := cast_mem M heq h1
      have h_eq : {z : Rn R (n + 1 + m) | (fun j => z (Fin.natAdd (n + 1) j)) ∈ B} =
                  {z : Rn R (n + 1 + m) | (fun i => z (Fin.cast heq i)) ∈ {x | (fun i_1 => x (Fin.succ i_1)) ∈ {z_1 | (fun j => z_1 (Fin.natAdd n j)) ∈ B}}} := by
        ext z
        change (fun j : Fin m => z (Fin.natAdd (n + 1) j)) ∈ B ↔ (fun j : Fin m => z (Fin.cast heq (Fin.succ (Fin.natAdd n j)))) ∈ B
        have h_fun : (fun j : Fin m => z (Fin.natAdd (n + 1) j)) =
                     (fun j : Fin m => z (Fin.cast heq (Fin.succ (Fin.natAdd n j)))) := by
          funext j; congr 1; ext; simp [Fin.natAdd, Fin.succ, Fin.cast]; omega
        rw [h_fun]
      rw [h_eq]
      exact hcast

theorem definable_projBlock {n m : ℕ} {A : Set (Rn R (n + m))} (hA : M.S (n + m) A) :
    M.S n (projBlock n m A) := by
  induction m with
  | zero =>
      have heq : n = n + 0 := (Nat.add_zero n).symm
      exact cast_mem M heq hA
  | succ m ih => exact ih (M.proj_mem hA)

theorem prod_univ_right_mem {n m} {A : Set (Rn R n)} (hA : M.S n A) :
    M.S (n + m) {z : Rn R (n + m) | (fun i : Fin n => z (Fin.castAdd m i)) ∈ A} :=
  right_cylinder_iter_mem (M := M) hA

theorem prod_univ_left_mem {n m} {B : Set (Rn R m)} (hB : M.S m B) :
    M.S (n + m) {z : Rn R (n + m) | (fun j : Fin m => z (Fin.natAdd n j)) ∈ B} :=
  left_cylinder_iter_mem (M := M) hB

theorem prod_mem_helper {n m} {A : Set (Rn R n)} {B : Set (Rn R m)} (hA : M.S n A) (hB : M.S m B) :
    M.S (n + m) ({z : Rn R (n + m) | (fun i : Fin n => z (Fin.castAdd m i)) ∈ A} ∩
                 {z : Rn R (n + m) | (fun j : Fin m => z (Fin.natAdd n j)) ∈ B}) := by
  exact inter_mem M (prod_univ_right_mem M hA) (prod_univ_left_mem M hB)

theorem block_proj_mem {n m : ℕ} {A : Set (Rn R (n + m))} (hA : M.S (n + m) A) :
    M.S n (projBlock n m A) :=
  definable_projBlock (M := M) hA

theorem one_last_proj_mem {n} {A : Set (Rn R (n + 1))} (hA : M.S (n + 1) A) :
    M.S n {x : Rn R n | ∃ y : R, Fin.snoc x y ∈ A} :=
  M.proj_mem hA

theorem univ_mem {n : ℕ} : M.S n (Set.univ : Set (Rn R n)) := by
  have h : M.S n (∅ᶜ : Set (Rn R n)) := M.compl_mem (M.empty_mem n)
  simpa using h

lemma mem_foldr_inter {α : Type u} (L : List (Set α)) (z : α) :
    z ∈ L.foldr (· ∩ ·) Set.univ ↔ ∀ A ∈ L, z ∈ A := by
  induction L with
  | nil => simp
  | cons A L ih => simp [ih]

theorem finite_inter_mem {n : ℕ} (L : List (Set (Rn R n))) (hL : ∀ A ∈ L, M.S n A) :
    M.S n (L.foldr (· ∩ ·) Set.univ) := by
  induction L with
  | nil => simpa using univ_mem (M := M)
  | cons A L ih =>
      simp only [List.foldr_cons]
      exact inter_mem M (hL A (by simp)) (ih (by intro B hB; exact hL B (by simp [hB])))

lemma mem_projBlock_iff {n m : ℕ} {A : Set (Rn R (n + m))} {x : Rn R n} :
    x ∈ projBlock n m A ↔
      ∃ y : Rn R m, (fun k : Fin (n + m) =>
        if h : k.1 < n then x ⟨k.1, h⟩ else y ⟨k.1 - n, by omega⟩) ∈ A := by
  induction m with
  | zero =>
      constructor
      · intro hx
        refine ⟨fun i => Fin.elim0 i, ?_⟩
        have h_fun : (fun (k : Fin (n + 0)) => if h : k.1 < n then x ⟨k.1, h⟩ else (fun i => Fin.elim0 i) ⟨k.1 - n, by omega⟩) =
                     (fun (k : Fin (n + 0)) => x (Fin.cast (Nat.add_zero n).symm k)) := by
          funext k
          have hk : k.1 < n := by omega
          simp [hk]
        change _ ∈ A
        rwa [h_fun]
      · rintro ⟨y, hy⟩
        have h_fun : (fun (k : Fin (n + 0)) => if h : k.1 < n then x ⟨k.1, h⟩ else y ⟨k.1 - n, by omega⟩) =
                     (fun (k : Fin (n + 0)) => x (Fin.cast (Nat.add_zero n).symm k)) := by
          funext k
          have hk : k.1 < n := by omega
          simp [hk]
        change _ ∈ A
        rwa [h_fun] at hy
  | succ m ih =>
      constructor
      · intro hx
        simp only [projBlock_succ] at hx
        rcases ih.mp hx with ⟨y, hy⟩
        simp only [projLast, mem_setOf_eq] at hy
        rcases hy with ⟨r, hr⟩
        refine ⟨Fin.snoc y r, ?_⟩
        have h_fun : (fun (k : Fin (n + m + 1)) => if h : k.1 < n then x ⟨k.1, h⟩ else (Fin.snoc y r) ⟨k.1 - n, by omega⟩) =
                     (Fin.snoc (fun (k' : Fin (n + m)) => if h : k'.1 < n then x ⟨k'.1, h⟩ else y ⟨k'.1 - n, by omega⟩) r) := by
          funext k
          by_cases hk : k.1 < n
          · have h_last : k.1 < n + m := by omega
            simp [hk, h_last, Fin.snoc]
          · by_cases h_last : k.1 < n + m
            · simp [hk, h_last, Fin.snoc]
            · have heq : k.1 = n + m := by omega
              simp only [hk, h_last, Fin.snoc, dif_neg, not_false_eq_true]
              congr 1; ext; omega
        change _ ∈ A
        rwa [h_fun]
      · rintro ⟨y, hy⟩
        simp only [projBlock_succ, projLast, mem_setOf_eq]
        apply ih.mpr
        refine ⟨fun j : Fin m => y (Fin.castSucc j), y (Fin.last m), ?_⟩
        have h_fun : (Fin.snoc (fun (k' : Fin (n + m)) => if h : k'.1 < n then x ⟨k'.1, h⟩ else y (Fin.castSucc ⟨k'.1 - n, by omega⟩)) (y (Fin.last m))) =
                     (fun (k : Fin (n + m + 1)) => if h : k.1 < n then x ⟨k.1, h⟩ else y ⟨k.1 - n, by omega⟩) := by
          funext k
          by_cases hk : k.1 < n
          · have h_last : k.1 < n + m := by omega
            simp [hk, h_last, Fin.snoc]
          · by_cases h_last : k.1 < n + m
            · simp [hk, h_last, Fin.snoc]
            · have heq : k.1 = n + m := by omega
              simp only [hk, h_last, Fin.snoc, dif_neg, not_false_eq_true]
              congr 1; ext; omega
        change _ ∈ A
        rwa [h_fun]

theorem graph_of_reindex_mem {n m : ℕ} (σ : Fin n → Fin m) :
    M.S (m + n) {z : Rn R (m + n) | ∀ i : Fin n, z (Fin.castAdd n (σ i)) = z (Fin.natAdd m i)} := by
  let D : Fin n → Set (Rn R (m + n)) :=
    fun i => {z : Rn R (m + n) | z (Fin.castAdd n (σ i)) = z (Fin.natAdd m i)}
  have hD : ∀ i : Fin n, M.S (m + n) (D i) := by
    intro i
    exact M.diagonal_mem (Fin.castAdd n (σ i)) (Fin.natAdd m i) (Nat.lt_add_right i.1 (σ i).isLt)
  let L : List (Set (Rn R (m + n))) := List.ofFn D
  have hL : ∀ A ∈ L, M.S (m + n) A := by
    intro A hA
    rcases List.mem_ofFn.mp hA with ⟨i, rfl⟩
    exact hD i
  have hfold : M.S (m + n) (L.foldr (· ∩ ·) Set.univ) := finite_inter_mem M L hL
  have h_eq : {z : Rn R (m + n) | ∀ i : Fin n, z (Fin.castAdd n (σ i)) = z (Fin.natAdd m i)} = L.foldr (· ∩ ·) Set.univ := by
    ext z
    rw [mem_foldr_inter]
    constructor
    · intro hz A hA
      rcases List.mem_ofFn.mp hA with ⟨i, rfl⟩
      exact hz i
    · intro hz i
      apply hz
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact h_eq.symm ▸ hfold

theorem reindex_mem {n m} {A : Set (Rn R n)} (σ : Fin n → Fin m) (hA : M.S n A) :
    M.S m {x : Rn R m | (fun i : Fin n => x (σ i)) ∈ A} := by
  let C : Set (Rn R (m + n)) :=
    {z : Rn R (m + n) | (fun j : Fin n => z (Fin.natAdd m j)) ∈ A} ∩
    {z : Rn R (m + n) | ∀ i : Fin n, z (Fin.castAdd n (σ i)) = z (Fin.natAdd m i)}
  have hC : M.S (m + n) C := inter_mem M (prod_univ_left_mem M hA) (graph_of_reindex_mem M σ)
  have hp : M.S m (projBlock n m C) := block_proj_mem M (n := m) (m := n) hC
  have h_eq : {x : Rn R m | (fun i : Fin n => x (σ i)) ∈ A} = projBlock m n C := by
    ext x
    rw [mem_projBlock_iff]
    constructor
    · intro hx
      refine ⟨fun i : Fin n => x (σ i), ?_⟩
      constructor
      · have h_fun : (fun j : Fin n => (fun (k : Fin (m + n)) => if h : k.1 < m then x ⟨k.1, h⟩ else (fun (i : Fin n) => x (σ i)) ⟨k.1 - m, by omega⟩) (Fin.natAdd m j)) = (fun i : Fin n => x (σ i)) := by
          funext j
          have hj : ¬((Fin.natAdd m j).1 < m) := by
            have := j.isLt; simp [Fin.natAdd]; omega
          simp [Fin.natAdd, hj]
        change _ ∈ A
        rwa [h_fun]
      · intro i
        have h1 : (Fin.castAdd n (σ i)).1 < m := (σ i).isLt
        have h2 : ¬((Fin.natAdd m i).1 < m) := by
          have := i.isLt; simp [Fin.natAdd]; omega
        simp [Fin.castAdd, Fin.natAdd, h1, h2]
    · rintro ⟨y, hyA, hg⟩
      have H : (fun i : Fin n => x (σ i)) = (fun j : Fin n => y j) := by
        funext i
        have h_eval := hg i
        have h1 : (Fin.castAdd n (σ i)).1 < m := (σ i).isLt
        have h2 : ¬((Fin.natAdd m i).1 < m) := by
          have := i.isLt; simp [Fin.natAdd]; omega
        simp only [Fin.castAdd, Fin.natAdd, h1, h2, dif_pos, dif_neg, not_false_eq_true] at h_eval
        exact h_eval
      have hyA_simp : (fun j : Fin n => y j) ∈ A := by
        have h_fun : (fun (j : Fin n) => (fun (k : Fin (m + n)) => if h : k.1 < m then x ⟨k.1, h⟩ else y ⟨k.1 - m, by omega⟩) (Fin.natAdd m j)) = (fun j => y j) := by
          funext j
          have hj : ¬((Fin.natAdd m j).1 < m) := by
            have := j.isLt; simp [Fin.natAdd]; omega
          simp only [Fin.natAdd, hj, dif_neg, not_false_eq_true]
          congr 1; ext; omega
        change (fun j : Fin n => (fun (k : Fin (m + n)) => if h : k.1 < m then x ⟨k.1, h⟩ else y ⟨k.1 - m, by omega⟩) (Fin.natAdd m j)) ∈ A at hyA
        rwa [h_fun] at hyA
      rwa [H]
  exact h_eq.symm ▸ hp
-- End of helper lemmas

theorem theorem_vi {n m} {A : Set (Rn R n)} {B : Set (Rn R m)} (hA : M.S n A) (hB : M.S m B) :
    M.S (n + m) {x : Rn R (n + m) |
      (fun i : Fin n => x (Fin.castAdd m i)) ∈ A ∧
      (fun j : Fin m => x (Fin.natAdd n j)) ∈ B} := by
  exact inter_mem M (right_cylinder_iter_mem M hA) (left_cylinder_iter_mem M hB)

theorem theorem_ix {n m} {A : Set (Rn R (n + m))} (hA : M.S (n + m) A) :
    M.S n {x : Rn R n | ∃ z : Rn R (n + m), z ∈ A ∧ ∀ i : Fin n, z (Fin.castAdd m i) = x i} := by
  have hb := block_proj_mem M hA
  have h_eq : {x : Rn R n | ∃ z : Rn R (n + m), z ∈ A ∧ ∀ i : Fin n, z (Fin.castAdd m i) = x i} = projBlock n m A := by
    ext x
    rw [mem_projBlock_iff]
    constructor
    · rintro ⟨z, hzA, hzx⟩
      refine ⟨fun k => z (Fin.natAdd n k), ?_⟩
      have H : (fun (k : Fin (n + m)) => if h : k.1 < n then x ⟨k.1, h⟩ else z (Fin.natAdd n ⟨k.1 - n, by omega⟩)) = z := by
        funext k
        by_cases hk : k.1 < n
        · have := hzx ⟨k.1, hk⟩
          simp [hk]
          have h1 : z (Fin.castAdd m ⟨k.1, hk⟩) = z k := by congr 1; ext; simp [Fin.castAdd]
          rw [h1] at this
          exact this.symm
        · simp only [hk, dif_neg, not_false_eq_true]
          congr 1; ext; simp [Fin.natAdd]; omega
      change _ ∈ A
      rwa [H]
    · rintro ⟨y, hy⟩
      refine ⟨fun k => if hk : k.1 < n then x ⟨k.1, hk⟩ else y ⟨k.1 - n, by omega⟩, hy, ?_⟩
      intro i
      have hk : (Fin.castAdd m i).1 < n := i.isLt
      simp [hk, Fin.castAdd]
  exact h_eq.symm ▸ hb

theorem theorem_viii {n m} {A : Set (Rn R n)} (σ : Fin n → Fin m) (hA : M.S n A) :
    M.S m {x : Rn R m | (fun i : Fin n => x (σ i)) ∈ A} := by
  exact reindex_mem M σ hA

theorem theorem_vii {n} {A : Set (Rn R (n + 1))} (hA : M.S (n + 1) A) :
    M.S n {x : Rn R n | ∃ y : R, (Fin.snoc x y) ∈ A} := by
  have h := theorem_ix M (m := 1) hA
  have h_eq : {x : Rn R n | ∃ z : Rn R (n + 1), z ∈ A ∧ ∀ i : Fin n, z (Fin.castAdd 1 i) = x i} = {x : Rn R n | ∃ y : R, (Fin.snoc x y) ∈ A} := by
    ext x
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨z, hzA, hzx⟩
      refine ⟨z (Fin.last n), ?_⟩
      have H : Fin.snoc x (z (Fin.last n)) = z := by
        funext k
        by_cases hk : k.1 < n
        · have := hzx ⟨k.1, hk⟩
          have h1 : z (Fin.castAdd 1 ⟨k.1, hk⟩) = z k := by congr 1; ext; simp [Fin.castAdd]
          rw [h1] at this
          simp [Fin.snoc, hk]
          exact this.symm
        · have hk_eq : k.1 = n := by omega
          simp only [Fin.snoc, hk, dif_neg, not_false_eq_true]
          congr 1; ext; omega
      change _ ∈ A
      rwa [H]
    · rintro ⟨y, hy⟩
      refine ⟨Fin.snoc x y, hy, ?_⟩
      intro i
      have hk : (Fin.castAdd 1 i).1 < n := i.isLt
      simp [Fin.castAdd, hk, Fin.snoc]
      congr 1; ext; rfl
  exact h_eq ▸ h

end OMinimal