import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

universe u

namespace OMinimal

def setEmpty {A : Type u} : Set A :=
  fun _ => False

def setUnion {A : Type u} (X Y : Set A) : Set A :=
  fun a => X a \/ Y a

def setInter {A : Type u} (X Y : Set A) : Set A :=
  fun a => X a /\ Y a

def setCompl {A : Type u} (X : Set A) : Set A :=
  fun a => Not (X a)

abbrev Power (R : Type u) (n : Nat) := Fin n -> R

namespace Power

variable {R : Type u}

def left {n m : Nat} (z : Power R (n + m)) : Power R n :=
  fun i => z (Fin.castAdd m i)

def right {n m : Nat} (z : Power R (n + m)) : Power R m :=
  fun j => z (Fin.natAdd n j)

def deleteCoord {n : Nat} (k : Fin (n + 1)) (z : Power R (n + 1)) : Power R n :=
  fun i => z (Fin.succAbove k i)

def coord1 (x : Power R 1) : R :=
  x 0

def coord2_0 (x : Power R 2) : R :=
  x 0

def coord2_1 (x : Power R 2) : R :=
  x 1

def append {n m : Nat} (x : Power R n) (y : Power R m) : Power R (n + m) :=
  Fin.append x y

@[simp] theorem left_append {n m : Nat} (x : Power R n) (y : Power R m) :
    left (append x y) = x := by
  funext i
  simp [left, append]

@[simp] theorem right_append {n m : Nat} (x : Power R n) (y : Power R m) :
    right (append x y) = y := by
  funext i
  simp [right, append]

end Power

structure DenseLinearOrderNoEndpoints (R : Type u) where
  lt : R -> R -> Prop
  irrefl : forall x : R, Not (lt x x)
  trans : forall {x y z : R}, lt x y -> lt y z -> lt x z
  trichotomy : forall x y : R,
      (lt x y /\ Not (lt y x) /\ Not (x = y)) \/
      (x = y /\ Not (lt x y) /\ Not (lt y x)) \/
      (lt y x /\ Not (lt x y) /\ Not (x = y))
  dense : forall {x y : R}, lt x y -> exists z : R, lt x z /\ lt z y
  no_left_endpoint : forall x : R, exists y : R, lt y x
  no_right_endpoint : forall x : R, exists y : R, lt x y

inductive Endpoint (R : Type u) where
  | negInf : Endpoint R
  | finite : R -> Endpoint R
  | posInf : Endpoint R

namespace Endpoint

variable {R : Type u}

def lt (D : DenseLinearOrderNoEndpoints R) : Endpoint R -> Endpoint R -> Prop
  | Endpoint.negInf, Endpoint.negInf => False
  | Endpoint.negInf, Endpoint.finite _ => True
  | Endpoint.negInf, Endpoint.posInf => True
  | Endpoint.finite _, Endpoint.negInf => False
  | Endpoint.finite a, Endpoint.finite b => D.lt a b
  | Endpoint.finite _, Endpoint.posInf => True
  | Endpoint.posInf, _ => False

end Endpoint

def pointSet {R : Type u} (a : R) : Set (Power R 1) :=
  fun x => Power.coord1 x = a

def openInterval {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) : Set (Power R 1) :=
  fun x => Endpoint.lt D a (Endpoint.finite (Power.coord1 x)) /\
           Endpoint.lt D (Endpoint.finite (Power.coord1 x)) b

inductive FiniteUnionOfPointsAndIntervals {R : Type u}
    (D : DenseLinearOrderNoEndpoints R) : Set (Power R 1) -> Prop where
  | empty :
      FiniteUnionOfPointsAndIntervals D (setEmpty : Set (Power R 1))
  | point (a : R) :
      FiniteUnionOfPointsAndIntervals D (pointSet a)
  | interval (a b : Endpoint R) :
      FiniteUnionOfPointsAndIntervals D (openInterval D a b)
  | union {A B : Set (Power R 1)} :
      FiniteUnionOfPointsAndIntervals D A ->
      FiniteUnionOfPointsAndIntervals D B ->
      FiniteUnionOfPointsAndIntervals D (setUnion A B)

structure OMinimalStructure {R : Type u} (D : DenseLinearOrderNoEndpoints R) where
  S : (n : Nat) -> Set (Set (Power R n))

  empty_mem : forall n : Nat, S n (setEmpty : Set (Power R n))
  union_mem : forall {n : Nat} {A B : Set (Power R n)},
    S n A -> S n B -> S n (setUnion A B)
  inter_mem : forall {n : Nat} {A B : Set (Power R n)},
    S n A -> S n B -> S n (setInter A B)
  compl_mem : forall {n : Nat} {A : Set (Power R n)},
    S n A -> S n (setCompl A)

  diagonal_mem : forall {n : Nat} (i j : Fin n),
    i < j -> S n (fun x : Power R n => x i = x j)

  product_mem : forall {n m : Nat} {A : Set (Power R n)} {B : Set (Power R m)},
    S n A -> S m B ->
      S (n + m) (fun z : Power R (n + m) =>
        A (Power.left z) /\ B (Power.right z))

  project_mem : forall {n : Nat} (k : Fin (n + 1)) {A : Set (Power R (n + 1))},
    S (n + 1) A ->
      S n (fun y : Power R n =>
        exists x : Power R (n + 1), A x /\ Power.deleteCoord k x = y)

  reindex_mem : forall {n m : Nat} (sigma : Fin n -> Fin m) {A : Set (Power R n)},
    S n A -> S m (fun x : Power R m => A (fun i : Fin n => x (sigma i)))

  existsLast_mem : forall {n m : Nat} {A : Set (Power R (n + m))},
    S (n + m) A ->
      S n (fun x : Power R n => exists y : Power R m, A (Power.append x y))

  lt_mem :
    S 2 (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p))

  ominimal : forall A : Set (Power R 1),
    S 1 A <-> FiniteUnionOfPointsAndIntervals D A

namespace OMinimalStructure

variable {R : Type u} {D : DenseLinearOrderNoEndpoints R}

def Definable (M : OMinimalStructure D) {n : Nat} (A : Set (Power R n)) : Prop :=
  M.S n A

def FunctionGraph {m n : Nat} {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    Set (Power R (m + n)) :=
  fun z => exists hx : A (Power.left z),
    Power.right z = (f (Subtype.mk (Power.left z) hx)).1

def compGIndex {a b c : Nat} (i : Fin (a + b)) : Fin ((a + c) + b) :=
  if h : (i : Nat) < a then
    Fin.castAdd b (Fin.castAdd c (Fin.mk (i : Nat) h))
  else
    Fin.natAdd (a + c) (Fin.mk ((i : Nat) - a) (by omega))

def compHIndex {a b c : Nat} (i : Fin (b + c)) : Fin ((a + c) + b) :=
  if h : (i : Nat) < b then
    Fin.natAdd (a + c) (Fin.mk (i : Nat) h)
  else
    Fin.castAdd b (Fin.natAdd a (Fin.mk ((i : Nat) - b) (by omega)))

def compGArg {a b c : Nat} (xyz : Power R ((a + c) + b)) : Power R (a + b) :=
  fun i => xyz (compGIndex (a := a) (b := b) (c := c) i)

def compHArg {a b c : Nat} (xyz : Power R ((a + c) + b)) : Power R (b + c) :=
  fun i => xyz (compHIndex (a := a) (b := b) (c := c) i)

theorem compGArg_append {a b c : Nat}
    (xz : Power R (a + c)) (y : Power R b) :
    compGArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y) =
      Power.append (Power.left xz) y := by
  funext i
  change (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i) =
    (Power.append (Power.left xz) y) i
  by_cases h : (i : Nat) < a
  · let ia : Fin a := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd b ia := by
      ext
      simp [ia]
    have hidx : compGIndex (a := a) (b := b) (c := c) i =
        Fin.castAdd b (Fin.castAdd c ia) := by
      simp [compGIndex, h, ia]
    calc
      (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.castAdd b (Fin.castAdd c ia)) := by
              rw [hidx]
      _ = xz (Fin.castAdd c ia) := by
              simp [Power.append]
      _ = Power.left xz ia := by
              simp [Power.left]
      _ = (Power.append (Power.left xz) y) (Fin.castAdd b ia) := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) i := by
              rw [hi]
  · let jb : Fin b := Fin.mk ((i : Nat) - a) (by omega)
    have hi : i = Fin.natAdd a jb := by
      ext
      simp [jb]
      omega
    have hidx : compGIndex (a := a) (b := b) (c := c) i =
        Fin.natAdd (a + c) jb := by
      simp [compGIndex, h, jb]
    calc
      (Power.append xz y) (compGIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.natAdd (a + c) jb) := by
              rw [hidx]
      _ = y jb := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) (Fin.natAdd a jb) := by
              simp [Power.append]
      _ = (Power.append (Power.left xz) y) i := by
              rw [hi]

theorem compHArg_append {a b c : Nat}
    (xz : Power R (a + c)) (y : Power R b) :
    compHArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y) =
      Power.append y (Power.right xz) := by
  funext i
  change (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i) =
    (Power.append y (Power.right xz)) i
  by_cases h : (i : Nat) < b
  · let ib : Fin b := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd c ib := by
      ext
      simp [ib]
    have hidx : compHIndex (a := a) (b := b) (c := c) i =
        Fin.natAdd (a + c) ib := by
      simp [compHIndex, h, ib]
    calc
      (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.natAdd (a + c) ib) := by
              rw [hidx]
      _ = y ib := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) (Fin.castAdd c ib) := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) i := by
              rw [hi]
  · let jc : Fin c := Fin.mk ((i : Nat) - b) (by omega)
    have hi : i = Fin.natAdd b jc := by
      ext
      simp [jc]
      omega
    have hidx : compHIndex (a := a) (b := b) (c := c) i =
        Fin.castAdd b (Fin.natAdd a jc) := by
      simp [compHIndex, h, jc]
    calc
      (Power.append xz y) (compHIndex (a := a) (b := b) (c := c) i)
          = (Power.append xz y) (Fin.castAdd b (Fin.natAdd a jc)) := by
              rw [hidx]
      _ = xz (Fin.natAdd a jc) := by
              simp [Power.append]
      _ = Power.right xz jc := by
              simp [Power.right]
      _ = (Power.append y (Power.right xz)) (Fin.natAdd b jc) := by
              simp [Power.append]
      _ = (Power.append y (Power.right xz)) i := by
              rw [hi]

def RelationComp {m n p : Nat}
    (G : Set (Power R (m + n))) (H : Set (Power R (n + p))) :
    Set (Power R (m + p)) :=
  fun xz => exists y : Power R n,
    G (Power.append (Power.left xz) y) /\
    H (Power.append y (Power.right xz))

theorem relation_comp_mem
    (M : OMinimalStructure D)
    {a b c : Nat}
    {G : Set (Power R (a + b))} {H : Set (Power R (b + c))}
    (hG : M.S (a + b) G) (hH : M.S (b + c) H) :
    M.S (a + c) (RelationComp (R := R) (m := a) (n := b) (p := c) G H) := by
  have hG' :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          G (compGArg (R := R) (a := a) (b := b) (c := c) xyz)) := by
    simpa [compGArg] using
      (M.reindex_mem
        (fun i : Fin (a + b) => compGIndex (a := a) (b := b) (c := c) i)
        hG)
  have hH' :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          H (compHArg (R := R) (a := a) (b := b) (c := c) xyz)) := by
    simpa [compHArg] using
      (M.reindex_mem
        (fun i : Fin (b + c) => compHIndex (a := a) (b := b) (c := c) i)
        hH)
  have hBoth :
      M.S ((a + c) + b)
        (fun xyz : Power R ((a + c) + b) =>
          G (compGArg (R := R) (a := a) (b := b) (c := c) xyz) /\
          H (compHArg (R := R) (a := a) (b := b) (c := c) xyz)) :=
    M.inter_mem hG' hH'
  have hProj :
      M.S (a + c)
        (fun xz : Power R (a + c) =>
          exists y : Power R b,
            G (compGArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y)) /\
            H (compHArg (R := R) (a := a) (b := b) (c := c) (Power.append xz y))) :=
    M.existsLast_mem hBoth
  simpa [RelationComp, compGArg_append, compHArg_append] using hProj

theorem relationComp_functionGraph_eq {m n p : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)} {C : Set (Power R p)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y})
    (g : {y : Power R n // B y} -> {z : Power R p // C z}) :
    RelationComp (R := R)
      (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f)
      (FunctionGraph (R := R) (m := n) (n := p) (A := B) (B := C) g)
    =
    FunctionGraph (R := R) (m := m) (n := p) (A := A) (B := C)
      (fun x => g (f x)) := by
  funext xz
  apply propext
  constructor
  · intro h
    rcases h with ⟨y, hf, hg⟩
    have hf' : exists hx : A (Power.left xz),
        y = (f (Subtype.mk (Power.left xz) hx)).1 := by
      simpa [FunctionGraph] using hf
    have hg' : exists hy : B y,
        Power.right xz = (g (Subtype.mk y hy)).1 := by
      simpa [FunctionGraph] using hg
    rcases hf' with ⟨hx, hfy⟩
    rcases hg' with ⟨hy, hgz⟩
    refine ⟨hx, ?_⟩
    have hsub : (Subtype.mk y hy : {y : Power R n // B y}) =
        f (Subtype.mk (Power.left xz) hx) := by
      apply Subtype.ext
      exact hfy
    simpa [FunctionGraph, hsub] using hgz
  · intro h
    rcases h with ⟨hx, hxz⟩
    let y : Power R n := (f (Subtype.mk (Power.left xz) hx)).1
    have hfProof :
        FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
          (Power.append (Power.left xz) y) := by
      have hfCore : exists hx0 : A (Power.left xz),
          y = (f (Subtype.mk (Power.left xz) hx0)).1 := by
        exact Exists.intro hx rfl
      simpa [FunctionGraph] using hfCore
    have hgProof :
        FunctionGraph (R := R) (m := n) (n := p) (A := B) (B := C) g
          (Power.append y (Power.right xz)) := by
      have hy : B y := by
        simpa [y] using (f (Subtype.mk (Power.left xz) hx)).2
      have hsub : (Subtype.mk y hy : {y : Power R n // B y}) =
          f (Subtype.mk (Power.left xz) hx) := by
        apply Subtype.ext
        rfl
      have hgCore : exists hy0 : B y,
          Power.right xz = (g (Subtype.mk y hy0)).1 := by
        refine Exists.intro hy ?_
        simpa [y, hsub] using hxz
      simpa [FunctionGraph] using hgCore
    exact Exists.intro y (And.intro hfProof hgProof)

structure DefinableFunction (M : OMinimalStructure D) {m n : Nat}
    (A : Set (Power R m)) (B : Set (Power R n)) where
  domain_mem : M.S m A
  codomain_mem : M.S n B
  toFun : {x : Power R m // A x} -> {y : Power R n // B y}
  graph_mem :
    M.S (m + n) (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) toFun)

def DefinableFunction.comp
    (M : OMinimalStructure D)
    {m n p : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)} {C : Set (Power R p)}
    (g : DefinableFunction M B C)
    (f : DefinableFunction M A B) :
    DefinableFunction M A C where
  domain_mem := f.domain_mem
  codomain_mem := g.codomain_mem
  toFun := fun x => g.toFun (f.toFun x)
  graph_mem := by
    have hrel :=
      relation_comp_mem (R := R) (D := D) M
        (G := FunctionGraph (R := R) (m := m) (n := n)
          (A := A) (B := B) f.toFun)
        (H := FunctionGraph (R := R) (m := n) (n := p)
          (A := B) (B := C) g.toFun)
        f.graph_mem g.graph_mem
    have heq :=
      relationComp_functionGraph_eq (R := R)
        (A := A) (B := B) (C := C) f.toFun g.toFun
    rw [heq] at hrel
    exact hrel


/-
Image of a definable function.

The graph of a function f : A -> B is stored in coordinates (x,y), where
x has length m and y has length n.  The image is the projection onto the
second block, so before applying the block-projection axiom existsLast_mem
we reindex the graph into coordinates (y,x).
-/

def FunctionImage {m n : Nat} {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    Set (Power R n) :=
  fun y => exists x : Power R m, exists hx : A x,
    y = (f (Subtype.mk x hx)).1

/--
The image of a function whose codomain is `B` is contained in `B`.
-/
theorem functionImage_subset_codomain {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : {x : Power R m // A x} -> {y : Power R n // B y}) :
    FunctionImage (R := R) (A := A) (B := B) f <= B := by
  intro y hy
  rcases hy with ⟨x, hx, hxy⟩
  rw [hxy]
  exact (f (Subtype.mk x hx)).2

/--
Index map implementing the block swap `(y,x) |-> (x,y)`.

The domain of the index map is the coordinate set of `(x,y)`, namely
`Fin (m+n)`.  The codomain is the coordinate set of `(y,x)`, namely
`Fin (n+m)`.  If an index lies in the first `m` coordinates, then it is an
`x`-coordinate and must be read from the right block of `(y,x)`.  Otherwise
it is a `y`-coordinate and must be read from the left block.
-/
def imageGraphIndex {m n : Nat} (i : Fin (m + n)) : Fin (n + m) :=
  if h : (i : Nat) < m then
    Fin.natAdd n (Fin.mk (i : Nat) h)
  else
    Fin.castAdd m (Fin.mk ((i : Nat) - m) (by omega))

/--
Given a tuple in coordinates `(y,x)`, read it as a tuple in coordinates `(x,y)`.
-/
def imageGraphArg {m n : Nat} (yx : Power R (n + m)) : Power R (m + n) :=
  fun i => yx (imageGraphIndex (m := m) (n := n) i)

/--
On an explicitly appended tuple, the block swap has the expected value.
-/
theorem imageGraphArg_append {m n : Nat}
    (y : Power R n) (x : Power R m) :
    imageGraphArg (R := R) (m := m) (n := n) (Power.append y x) =
      Power.append x y := by
  funext i
  change (Power.append y x) (imageGraphIndex (m := m) (n := n) i) =
    (Power.append x y) i
  by_cases h : (i : Nat) < m
  · let im : Fin m := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd n im := by
      ext
      simp [im]
    have hidx : imageGraphIndex (m := m) (n := n) i = Fin.natAdd n im := by
      simp [imageGraphIndex, h, im]
    calc
      (Power.append y x) (imageGraphIndex (m := m) (n := n) i)
          = (Power.append y x) (Fin.natAdd n im) := by
              rw [hidx]
      _ = x im := by
              simp [Power.append]
      _ = (Power.append x y) (Fin.castAdd n im) := by
              simp [Power.append]
      _ = (Power.append x y) i := by
              rw [hi]
  · let jn : Fin n := Fin.mk ((i : Nat) - m) (by omega)
    have hi : i = Fin.natAdd m jn := by
      ext
      simp [jn]
      omega
    have hidx : imageGraphIndex (m := m) (n := n) i = Fin.castAdd m jn := by
      simp [imageGraphIndex, h, jn]
    calc
      (Power.append y x) (imageGraphIndex (m := m) (n := n) i)
          = (Power.append y x) (Fin.castAdd m jn) := by
              rw [hidx]
      _ = y jn := by
              simp [Power.append]
      _ = (Power.append x y) (Fin.natAdd m jn) := by
              simp [Power.append]
      _ = (Power.append x y) i := by
              rw [hi]

/--
If the graph of `f : A -> B` is definable, then the image of `f` is definable.
This is the graph-projection version of the main mathematical statement.
-/
theorem functionImage_mem_of_graph_mem
    (M : OMinimalStructure D)
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    {f : {x : Power R m // A x} -> {y : Power R n // B y}}
    (hGraph : M.S (m + n)
      (FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f)) :
    M.S n (FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f) := by
  have hSwap :
      M.S (n + m)
        (fun yx : Power R (n + m) =>
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (imageGraphArg (R := R) (m := m) (n := n) yx)) := by
    simpa [imageGraphArg] using
      (M.reindex_mem
        (fun i : Fin (m + n) => imageGraphIndex (m := m) (n := n) i)
        hGraph)
  have hProj :
      M.S n
        (fun y : Power R n => exists x : Power R m,
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (imageGraphArg (R := R) (m := m) (n := n) (Power.append y x))) := by
    simpa using (M.existsLast_mem (n := n) (m := m) hSwap)
  have hProj' :
      M.S n
        (fun y : Power R n => exists x : Power R m,
          FunctionGraph (R := R) (m := m) (n := n) (A := A) (B := B) f
            (Power.append x y)) := by
    simpa [imageGraphArg_append] using hProj
  simpa [FunctionImage, FunctionGraph] using hProj'

/--
Main image theorem for `DefinableFunction`:
if `f : A -> B` is definable, then its image is a definable subset of `R^n`.
-/
theorem functionImage_mem
    (M : OMinimalStructure D)
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    M.S n (FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f.toFun) := by
  exact functionImage_mem_of_graph_mem (R := R) (D := D) M f.graph_mem

/--
The image of a `DefinableFunction`, as a named set.
-/
def DefinableFunction.image
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) : Set (Power R n) :=
  FunctionImage (R := R) (m := m) (n := n) (A := A) (B := B) f.toFun

/--
The named image of a definable function is definable.
-/
theorem DefinableFunction.image_mem
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    M.S n (f.image) := by
  simpa [DefinableFunction.image] using
    functionImage_mem (R := R) (D := D) M f

/--
The named image of a definable function is contained in its codomain.
-/
theorem DefinableFunction.image_subset_codomain
    {M : OMinimalStructure D}
    {m n : Nat}
    {A : Set (Power R m)} {B : Set (Power R n)}
    (f : DefinableFunction M A B) :
    f.image <= B := by
  simpa [DefinableFunction.image] using
    functionImage_subset_codomain (R := R) (A := A) (B := B) f.toFun



/-
Continuity of a one-variable definable function.

Usual interval definition, for a function f : I -> R and x in I:
for every open interval (a,b) containing f(x), there are c < x < d such that
for every y in I, if c < y < d then f(y) lies in (a,b).

Using the graph G of f, this becomes:
x is continuous iff x is in I and there do not exist a,b,v such that
G(x,v), a < v < b, and no interval (c,d) around x works.

A pair c,d works iff c < x < d and there is no counterexample y,w with
y in I, c < y < d, G(y,w), and w outside (a,b).

The set-theoretic operations used below are only finite intersections,
complements, and existential projections. Universal quantifiers and implications
are rewritten using complement and existential quantification.
-/

def setUniv {A : Type u} : Set A :=
  setCompl setEmpty


def Lt1 (D : DenseLinearOrderNoEndpoints R) (x y : Power R 1) : Prop :=
  D.lt (Power.coord1 x) (Power.coord1 y)

def ContinuousAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  forall a b v : Power R 1,
    G (Power.append x v) ->
    Lt1 D a v -> Lt1 D v b ->
    exists c d : Power R 1,
      Lt1 D c x /\ Lt1 D x d /\
      forall y w : Power R 1,
        I y ->
        Lt1 D c y -> Lt1 D y d ->
        G (Power.append y w) ->
        Lt1 D a w /\ Lt1 D w b

theorem setUniv_mem (M : OMinimalStructure D) (n : Nat) :
    M.S n (setUniv : Set (Power R n)) := by
  exact M.compl_mem (M.empty_mem n)

def pairIndex {n : Nat} (i j : Fin n) : Fin 2 -> Fin n :=
  fun k => if (k : Nat) = 0 then i else j

def HoldsAt {n m : Nat} (A : Set (Power R n)) (sigma : Fin n -> Fin m) :
    Set (Power R m) :=
  fun z => A (fun i : Fin n => z (sigma i))

def DomainOn {n : Nat} (I : Set (Power R 1)) (i : Fin n) : Set (Power R n) :=
  HoldsAt I (fun _ : Fin 1 => i)

def GraphOn {n : Nat} (G : Set (Power R 2)) (i j : Fin n) : Set (Power R n) :=
  HoldsAt G (pairIndex i j)

def LtOn (D : DenseLinearOrderNoEndpoints R) {n : Nat} (i j : Fin n) :
    Set (Power R n) :=
  HoldsAt (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p))
    (pairIndex i j)

theorem holdsAt_mem (M : OMinimalStructure D)
    {n m : Nat} {A : Set (Power R n)} (sigma : Fin n -> Fin m)
    (hA : M.S n A) :
    M.S m (HoldsAt A sigma) := by
  simpa [HoldsAt] using M.reindex_mem sigma hA

theorem domainOn_mem (M : OMinimalStructure D)
    {n : Nat} {I : Set (Power R 1)} (hI : M.S 1 I) (i : Fin n) :
    M.S n (DomainOn I i) := by
  simpa [DomainOn] using
    (holdsAt_mem (R := R) (D := D) M (fun _ : Fin 1 => i) hI)

theorem graphOn_mem (M : OMinimalStructure D)
    {n : Nat} {G : Set (Power R 2)} (hG : M.S 2 G) (i j : Fin n) :
    M.S n (GraphOn G i j) := by
  simpa [GraphOn] using
    (holdsAt_mem (R := R) (D := D) M (pairIndex i j) hG)

theorem ltOn_mem (M : OMinimalStructure D)
    {n : Nat} (i j : Fin n) :
    M.S n (LtOn D i j) := by
  simpa [LtOn] using
    (holdsAt_mem (R := R) (D := D) M (pairIndex i j) M.lt_mem)

def ValueIntervalAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (a w b : Fin n) : Set (Power R n) :=
  setInter (LtOn D a w) (LtOn D w b)

def NeighbourhoodAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (c x d : Fin n) : Set (Power R n) :=
  setInter (LtOn D c x) (LtOn D x d)

def CoreAt (D : DenseLinearOrderNoEndpoints R)
    {n : Nat} (G : Set (Power R 2)) (x a b v : Fin n) : Set (Power R n) :=
  setInter (GraphOn G x v) (ValueIntervalAt D a v b)

theorem valueIntervalAt_mem (M : OMinimalStructure D)
    {n : Nat} (a w b : Fin n) :
    M.S n (ValueIntervalAt D a w b) := by
  exact M.inter_mem (ltOn_mem (R := R) (D := D) M a w)
    (ltOn_mem (R := R) (D := D) M w b)

theorem neighbourhoodAt_mem (M : OMinimalStructure D)
    {n : Nat} (c x d : Fin n) :
    M.S n (NeighbourhoodAt D c x d) := by
  exact M.inter_mem (ltOn_mem (R := R) (D := D) M c x)
    (ltOn_mem (R := R) (D := D) M x d)

theorem coreAt_mem (M : OMinimalStructure D)
    {n : Nat} {G : Set (Power R 2)} (hG : M.S 2 G) (x a b v : Fin n) :
    M.S n (CoreAt D G x a b v) := by
  exact M.inter_mem (graphOn_mem (R := R) (D := D) M hG x v)
    (valueIntervalAt_mem (R := R) (D := D) M a v b)

-- Variables in arity 8 are ordered as x,a,b,v,c,d,y,w.
def Counter8 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 8) :=
  setInter
    (setInter
      (setInter
        (setInter
          (DomainOn I (6 : Fin 8))
          (LtOn D (4 : Fin 8) (6 : Fin 8)))
        (LtOn D (6 : Fin 8) (5 : Fin 8)))
      (GraphOn G (6 : Fin 8) (7 : Fin 8)))
    (setCompl (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)))

theorem counter8_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 8 (Counter8 D I G) := by
  have hDomain : M.S 8 (DomainOn I (6 : Fin 8)) :=
    domainOn_mem (R := R) (D := D) M hI (6 : Fin 8)
  have hcy : M.S 8 (LtOn D (4 : Fin 8) (6 : Fin 8)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 8) (6 : Fin 8)
  have hyd : M.S 8 (LtOn D (6 : Fin 8) (5 : Fin 8)) :=
    ltOn_mem (R := R) (D := D) M (6 : Fin 8) (5 : Fin 8)
  have hGraph : M.S 8 (GraphOn G (6 : Fin 8) (7 : Fin 8)) :=
    graphOn_mem (R := R) (D := D) M hG (6 : Fin 8) (7 : Fin 8)
  have hInside : M.S 8 (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)) :=
    valueIntervalAt_mem (R := R) (D := D) M (1 : Fin 8) (7 : Fin 8) (2 : Fin 8)
  have hNotInside : M.S 8 (setCompl (ValueIntervalAt D (1 : Fin 8) (7 : Fin 8) (2 : Fin 8))) :=
    M.compl_mem hInside
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem hDomain hcy)
        hyd)
      hGraph)
    hNotInside

-- Variables in arity 6 are ordered as x,a,b,v,c,d.
def CounterExists6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  fun z => exists yw : Power R 2,
    Counter8 D I G (Power.append z yw)

theorem counterExists6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (CounterExists6 D I G) := by
  simpa [CounterExists6] using
    (M.existsLast_mem (n := 6) (m := 2)
      (counter8_mem (R := R) (D := D) M hI hG))

def Good6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  setInter
    (setInter
      (CoreAt D G (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6))
      (NeighbourhoodAt D (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)))
    (setCompl (CounterExists6 D I G))

theorem good6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (Good6 D I G) := by
  have hCore : M.S 6 (CoreAt D G (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)) :=
    coreAt_mem (R := R) (D := D) M hG (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)
  have hNhd : M.S 6 (NeighbourhoodAt D (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (4 : Fin 6) (0 : Fin 6) (5 : Fin 6)
  have hNoCounter : M.S 6 (setCompl (CounterExists6 D I G)) :=
    M.compl_mem (counterExists6_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem (M.inter_mem hCore hNhd) hNoCounter

-- Variables in arity 4 are ordered as x,a,b,v.
def GoodExists4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  fun z => exists cd : Power R 2,
    Good6 D I G (Power.append z cd)

theorem goodExists4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (GoodExists4 D I G) := by
  simpa [GoodExists4] using
    (M.existsLast_mem (n := 4) (m := 2)
      (good6_mem (R := R) (D := D) M hI hG))

def Bad4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  setInter
    (CoreAt D G (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
    (setCompl (GoodExists4 D I G))

theorem bad4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (Bad4 D I G) := by
  have hCore : M.S 4 (CoreAt D G (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) :=
    coreAt_mem (R := R) (D := D) M hG (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
  have hNoGood : M.S 4 (setCompl (GoodExists4 D I G)) :=
    M.compl_mem (goodExists4_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hCore hNoGood

def BadPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists abv : Power R 3,
    Bad4 D I G (Power.append x abv)

theorem badPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (BadPoint1 D I G) := by
  simpa [BadPoint1] using
    (M.existsLast_mem (n := 1) (m := 3)
      (bad4_mem (R := R) (D := D) M hI hG))

def ContinuousPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (setCompl (BadPoint1 D I G))

theorem continuousPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (ContinuousPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hBad : M.S 1 (BadPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    badPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem (M.compl_mem hBad)


/-
Local constancy of a one-variable definable function.

Usual interval definition, for a function f : I -> R and x in I:
f is locally constant at x if there is an open interval (c,d) containing x
such that for every y in I, if c < y < d then f(y) = f(x).

Using the graph G of f, this can be written without mentioning f directly:
x is locally constant iff x is in I and there exist c,d,v such that
G(x,v), c < x < d, and there is no counterexample y,w satisfying
I(y), c < y < d, G(y,w), and w is not equal to v.

Again, the set-theoretic operations below are finite intersections,
complements, and existential projections.
-/

def LocallyConstantAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d v : Power R 1,
    G (Power.append x v) /\
    Lt1 D c x /\ Lt1 D x d /\
    forall y w : Power R 1,
      I y ->
      Lt1 D c y -> Lt1 D y d ->
      G (Power.append y w) ->
      v = w

def EqOn {n : Nat} (i j : Fin n) : Set (Power R n) :=
  fun z => z i = z j

theorem eqOn_mem_of_lt (M : OMinimalStructure D)
    {n : Nat} (i j : Fin n) (hij : i < j) :
    M.S n (EqOn (R := R) i j) := by
  simpa [EqOn] using M.diagonal_mem i j hij

-- Variables in arity 6 are ordered as x,c,d,v,y,w.
def LocalConstCounter6 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 6) :=
  setInter
    (setInter
      (setInter
        (setInter
          (DomainOn I (4 : Fin 6))
          (LtOn D (1 : Fin 6) (4 : Fin 6)))
        (LtOn D (4 : Fin 6) (2 : Fin 6)))
      (GraphOn G (4 : Fin 6) (5 : Fin 6)))
    (setCompl (EqOn (R := R) (3 : Fin 6) (5 : Fin 6)))

theorem localConstCounter6_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 6 (LocalConstCounter6 D I G) := by
  have hDomain : M.S 6 (DomainOn I (4 : Fin 6)) :=
    domainOn_mem (R := R) (D := D) M hI (4 : Fin 6)
  have hcy : M.S 6 (LtOn D (1 : Fin 6) (4 : Fin 6)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 6) (4 : Fin 6)
  have hyd : M.S 6 (LtOn D (4 : Fin 6) (2 : Fin 6)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 6) (2 : Fin 6)
  have hGraph : M.S 6 (GraphOn G (4 : Fin 6) (5 : Fin 6)) :=
    graphOn_mem (R := R) (D := D) M hG (4 : Fin 6) (5 : Fin 6)
  have hEq : M.S 6 (EqOn (R := R) (3 : Fin 6) (5 : Fin 6)) :=
    eqOn_mem_of_lt (R := R) (D := D) M (3 : Fin 6) (5 : Fin 6) (by decide)
  have hNeq : M.S 6 (setCompl (EqOn (R := R) (3 : Fin 6) (5 : Fin 6))) :=
    M.compl_mem hEq
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem hDomain hcy)
        hyd)
      hGraph)
    hNeq

-- Variables in arity 4 are ordered as x,c,d,v.
def LocalConstCounterExists4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  fun z => exists yw : Power R 2,
    LocalConstCounter6 D I G (Power.append z yw)

theorem localConstCounterExists4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (LocalConstCounterExists4 D I G) := by
  simpa [LocalConstCounterExists4] using
    (M.existsLast_mem (n := 4) (m := 2)
      (localConstCounter6_mem (R := R) (D := D) M hI hG))

def LocalConstGood4 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 4) :=
  setInter
    (setInter
      (GraphOn G (0 : Fin 4) (3 : Fin 4))
      (NeighbourhoodAt D (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)))
    (setCompl (LocalConstCounterExists4 D I G))

theorem localConstGood4_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 4 (LocalConstGood4 D I G) := by
  have hGraph : M.S 4 (GraphOn G (0 : Fin 4) (3 : Fin 4)) :=
    graphOn_mem (R := R) (D := D) M hG (0 : Fin 4) (3 : Fin 4)
  have hNhd : M.S 4 (NeighbourhoodAt D (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 4) (0 : Fin 4) (2 : Fin 4)
  have hNoCounter : M.S 4 (setCompl (LocalConstCounterExists4 D I G)) :=
    M.compl_mem (localConstCounterExists4_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem (M.inter_mem hGraph hNhd) hNoCounter

def LocalConstGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cdv : Power R 3,
    LocalConstGood4 D I G (Power.append x cdv)

theorem localConstGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (LocalConstGoodPoint1 D I G) := by
  simpa [LocalConstGoodPoint1] using
    (M.existsLast_mem (n := 1) (m := 3)
      (localConstGood4_mem (R := R) (D := D) M hI hG))

def LocallyConstantPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (LocalConstGoodPoint1 D I G)

theorem locallyConstantPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyConstantPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (LocalConstGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    localConstGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood


/-
Local monotonicity of a one-variable definable function.

We use the non-strict convention:
locally monotone increasing means locally nondecreasing, and
locally monotone decreasing means locally nonincreasing.

For the graph G of f, x is locally increasing iff x is in I and there are
c,d with c < x < d such that there is no bad pair y0,y1 in I with
c < y0 < d, c < y1 < d, y0 < y1, G(y0,w0), G(y1,w1), and w1 < w0.

The decreasing version has the same definition except that the bad value
inequality is w0 < w1.

As above, the set-theoretic operations used below are finite intersections,
complements, and existential projections.
-/

def LocallyIncreasingAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d : Power R 1,
    Lt1 D c x /\ Lt1 D x d /\
    forall y0 y1 w0 w1 : Power R 1,
      I y0 -> I y1 ->
      Lt1 D c y0 -> Lt1 D y0 d ->
      Lt1 D c y1 -> Lt1 D y1 d ->
      G (Power.append y0 w0) ->
      G (Power.append y1 w1) ->
      Lt1 D y0 y1 ->
      Not (Lt1 D w1 w0)

def LocallyDecreasingAtOnGraph (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) (x : Power R 1) : Prop :=
  I x /\
  exists c d : Power R 1,
    Lt1 D c x /\ Lt1 D x d /\
    forall y0 y1 w0 w1 : Power R 1,
      I y0 -> I y1 ->
      Lt1 D c y0 -> Lt1 D y0 d ->
      Lt1 D c y1 -> Lt1 D y1 d ->
      G (Power.append y0 w0) ->
      G (Power.append y1 w1) ->
      Lt1 D y0 y1 ->
      Not (Lt1 D w0 w1)

-- Variables in arity 7 are ordered as x,c,d,y0,y1,w0,w1.
def MonotoneBaseCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter
    (setInter
      (setInter
        (setInter
          (setInter
            (setInter
              (setInter
                (setInter
                  (DomainOn I (3 : Fin 7))
                  (DomainOn I (4 : Fin 7)))
                (LtOn D (1 : Fin 7) (3 : Fin 7)))
              (LtOn D (3 : Fin 7) (2 : Fin 7)))
            (LtOn D (1 : Fin 7) (4 : Fin 7)))
          (LtOn D (4 : Fin 7) (2 : Fin 7)))
        (GraphOn G (3 : Fin 7) (5 : Fin 7)))
      (GraphOn G (4 : Fin 7) (6 : Fin 7)))
    (LtOn D (3 : Fin 7) (4 : Fin 7))

theorem monotoneBaseCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonotoneBaseCounter7 D I G) := by
  have hI0 : M.S 7 (DomainOn I (3 : Fin 7)) :=
    domainOn_mem (R := R) (D := D) M hI (3 : Fin 7)
  have hI1 : M.S 7 (DomainOn I (4 : Fin 7)) :=
    domainOn_mem (R := R) (D := D) M hI (4 : Fin 7)
  have hcy0 : M.S 7 (LtOn D (1 : Fin 7) (3 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 7) (3 : Fin 7)
  have hy0d : M.S 7 (LtOn D (3 : Fin 7) (2 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (3 : Fin 7) (2 : Fin 7)
  have hcy1 : M.S 7 (LtOn D (1 : Fin 7) (4 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (1 : Fin 7) (4 : Fin 7)
  have hy1d : M.S 7 (LtOn D (4 : Fin 7) (2 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (4 : Fin 7) (2 : Fin 7)
  have hGraph0 : M.S 7 (GraphOn G (3 : Fin 7) (5 : Fin 7)) :=
    graphOn_mem (R := R) (D := D) M hG (3 : Fin 7) (5 : Fin 7)
  have hGraph1 : M.S 7 (GraphOn G (4 : Fin 7) (6 : Fin 7)) :=
    graphOn_mem (R := R) (D := D) M hG (4 : Fin 7) (6 : Fin 7)
  have hy0y1 : M.S 7 (LtOn D (3 : Fin 7) (4 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (3 : Fin 7) (4 : Fin 7)
  exact M.inter_mem
    (M.inter_mem
      (M.inter_mem
        (M.inter_mem
          (M.inter_mem
            (M.inter_mem
              (M.inter_mem
                (M.inter_mem hI0 hI1)
                hcy0)
              hy0d)
            hcy1)
          hy1d)
        hGraph0)
      hGraph1)
    hy0y1

def MonoIncCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter (MonotoneBaseCounter7 D I G) (LtOn D (6 : Fin 7) (5 : Fin 7))

def MonoDecCounter7 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 7) :=
  setInter (MonotoneBaseCounter7 D I G) (LtOn D (5 : Fin 7) (6 : Fin 7))

theorem monoIncCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonoIncCounter7 D I G) := by
  have hBase : M.S 7 (MonotoneBaseCounter7 D I G) :=
    monotoneBaseCounter7_mem (R := R) (D := D) M hI hG
  have hBad : M.S 7 (LtOn D (6 : Fin 7) (5 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (6 : Fin 7) (5 : Fin 7)
  exact M.inter_mem hBase hBad

theorem monoDecCounter7_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 7 (MonoDecCounter7 D I G) := by
  have hBase : M.S 7 (MonotoneBaseCounter7 D I G) :=
    monotoneBaseCounter7_mem (R := R) (D := D) M hI hG
  have hBad : M.S 7 (LtOn D (5 : Fin 7) (6 : Fin 7)) :=
    ltOn_mem (R := R) (D := D) M (5 : Fin 7) (6 : Fin 7)
  exact M.inter_mem hBase hBad

-- Variables in arity 3 are ordered as x,c,d.
def MonoIncCounterExists3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  fun z => exists yyww : Power R 4,
    MonoIncCounter7 D I G (Power.append z yyww)

def MonoDecCounterExists3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  fun z => exists yyww : Power R 4,
    MonoDecCounter7 D I G (Power.append z yyww)

theorem monoIncCounterExists3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoIncCounterExists3 D I G) := by
  simpa [MonoIncCounterExists3] using
    (M.existsLast_mem (n := 3) (m := 4)
      (monoIncCounter7_mem (R := R) (D := D) M hI hG))

theorem monoDecCounterExists3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoDecCounterExists3 D I G) := by
  simpa [MonoDecCounterExists3] using
    (M.existsLast_mem (n := 3) (m := 4)
      (monoDecCounter7_mem (R := R) (D := D) M hI hG))

def MonoIncGood3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  setInter
    (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3))
    (setCompl (MonoIncCounterExists3 D I G))

def MonoDecGood3 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 3) :=
  setInter
    (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3))
    (setCompl (MonoDecCounterExists3 D I G))

theorem monoIncGood3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoIncGood3 D I G) := by
  have hNhd : M.S 3 (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
  have hNoCounter : M.S 3 (setCompl (MonoIncCounterExists3 D I G)) :=
    M.compl_mem (monoIncCounterExists3_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hNhd hNoCounter

theorem monoDecGood3_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 3 (MonoDecGood3 D I G) := by
  have hNhd : M.S 3 (NeighbourhoodAt D (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) :=
    neighbourhoodAt_mem (R := R) (D := D) M (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
  have hNoCounter : M.S 3 (setCompl (MonoDecCounterExists3 D I G)) :=
    M.compl_mem (monoDecCounterExists3_mem (R := R) (D := D) M hI hG)
  exact M.inter_mem hNhd hNoCounter

def MonoIncGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cd : Power R 2,
    MonoIncGood3 D I G (Power.append x cd)

def MonoDecGoodPoint1 (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => exists cd : Power R 2,
    MonoDecGood3 D I G (Power.append x cd)

theorem monoIncGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (MonoIncGoodPoint1 D I G) := by
  simpa [MonoIncGoodPoint1] using
    (M.existsLast_mem (n := 1) (m := 2)
      (monoIncGood3_mem (R := R) (D := D) M hI hG))

theorem monoDecGoodPoint1_mem (M : OMinimalStructure D)
    {I : Set (Power R 1)} {G : Set (Power R 2)}
    (hI : M.S 1 I) (hG : M.S 2 G) :
    M.S 1 (MonoDecGoodPoint1 D I G) := by
  simpa [MonoDecGoodPoint1] using
    (M.existsLast_mem (n := 1) (m := 2)
      (monoDecGood3_mem (R := R) (D := D) M hI hG))

def LocallyIncreasingPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (MonoIncGoodPoint1 D I G)

def LocallyDecreasingPoints (D : DenseLinearOrderNoEndpoints R)
    (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  setInter I (MonoDecGoodPoint1 D I G)

theorem locallyIncreasingPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyIncreasingPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (MonoIncGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    monoIncGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood

theorem locallyDecreasingPoints_mem (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (LocallyDecreasingPoints D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hGood : M.S 1 (MonoDecGoodPoint1 D I
      (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :=
    monoDecGoodPoint1_mem (R := R) (D := D) M f.domain_mem f.graph_mem
  exact M.inter_mem f.domain_mem hGood


theorem empty_definable (M : OMinimalStructure D) (n : Nat) :
    Definable M (setEmpty : Set (Power R n)) :=
  M.empty_mem n

theorem order_definable (M : OMinimalStructure D) :
    Definable M (fun p : Power R 2 => D.lt (Power.coord2_0 p) (Power.coord2_1 p)) :=
  M.lt_mem

end OMinimalStructure

end OMinimal
