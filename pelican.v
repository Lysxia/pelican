Require Import List.
Require Import Nat.
Require Import Tactics.
Require Import Program.
Require Import Setoid.
Require Import SetoidClass.
Require Import Relation_Definitions.

(** * Parametric types **)

(** Type syntax. T,U,V *)
Inductive type :=
| TyUnit : type
| TyZero : type (* Empty. *)
| TyArr  : type -> type -> type (* Functions. *)
| TyProduct : type -> type -> type
| TySum : type -> type -> type
| TyAlpha : type. (* A single type parameter. *)

Infix ":->" := TyArr (at level 30, right associativity) : type_scope.

Definition t := TyAlpha :-> TyAlpha.
Definition t2 := TyProduct (TyAlpha :-> TyAlpha) TyAlpha.
Print t2.

(** Interpretation of a type as a Set,
    parameterized by the interpretation of Alpha. *)
Fixpoint sem (K : Set) (T : type) : Set :=
  match T with
  | TyAlpha => K
  | TyProduct T1 T2 => sem K T1 * sem K T2
  | TySum T1 T2 => sem K T1 + sem K T2
  | T :-> U => sem K T -> sem K U
  | TyUnit => unit
  | TyZero => Empty_set
  end.

Fixpoint sem_eq (K : Set) (R : K -> K -> Prop)
         (T : type) : sem K T -> sem K T -> Prop :=
  match T with
  | TyUnit => fun _ _ => True
  | TyZero => fun _ _ => True
  | T :-> U =>
    fun x y =>
      forall r s, sem_eq K R T r s -> sem_eq K R U (x r) (y s)
  | TyProduct T1 T2 =>
    fun x y =>
      let (x1, x2) := x in
      let (y1, y2) := y in
      sem_eq K R T1 x1 y1 /\ sem_eq K R T2 x2 y2
  | TySum T1 T2 =>
    fun x y =>
      match x, y with
      | inl x1, inl y1 => sem_eq K R T1 x1 y1
      | inr x2, inr y2 => sem_eq K R T2 x2 y2
      | _, _ => False
      end
  | TyAlpha => R
  end.

(*
Inductive sem_eq (K : Set) (R : K -> K -> Prop)
  : forall (T : type), sem K T -> sem K T -> Prop :=
| SEqAlpha : forall x y, R x y -> sem_eq K R TyAlpha x y
| SEqProduct : forall T1 T2 x1 x2 y1 y2,
    sem_eq K R T1 x1 y1 ->
    sem_eq K R T2 x2 y2 ->
    sem_eq K R (TyProduct T1 T2) (x1, x2) (y1, y2)
| SEqLeft : forall T1 T2 x1 y1,
    sem_eq K R T1 x1 y1 ->
    sem_eq K R (TySum T1 T2) (inl x1) (inl y1)
| SEqRight : forall T1 T2 x2 y2,
    sem_eq K R T2 x2 y2 ->
    sem_eq K R (TySum T1 T2) (inr x2) (inr y2)
| SEqFun : forall T U x y,
    (forall r s, sem_eq K R T r s -> sem_eq K R U (x r) (y s)) ->
    sem_eq K R (T :-> U) x y.
 *)

(** * Paths in values

    We will define a type of "paths" that, given a value of
    type T, leads to a leaf of type alpha.
    We actually do this on the semantic level:
    given a value of type sem K T, a path leads to a leaf of
    type K. *)

(** Choices. C

    To make sure paths remain valid, we must restrict values
    of sum types. A "choice" chooses one alternative for
    every occurence of a sum type. *)
Inductive choice
          {K : Set}
  : type -> Set :=
| CAlpha : choice TyAlpha
| CProduct : forall {T1} {T2},
    choice T1 -> choice T2 -> choice (TyProduct T1 T2)
| CLeft : forall {T1 T2}, choice T1 -> choice (TySum T1 T2)
| CRight : forall {T1 T2}, choice T2 -> choice (TySum T1 T2)
| CUnit : choice TyUnit
| CArrow : forall {T U}, (sem K T -> choice U) -> choice (T :-> U).
  (* For functions, we make one choice for every argument. *)

(* Paths. p *)
Inductive path
          (K : Set)
  : forall (T : type), choice T -> Set :=

(* We're at a leaf. *)
| PHere : path K TyAlpha CAlpha

(* Given a pair, a path goes into either component. *)
| PFst : forall T1 T2 (C1 : choice T1) (C2 : choice T2),
    path K T1 C1 -> path K (TyProduct T1 T2) (CProduct C1 C2)
| PSnd : forall T1 T2 (C1 : choice T1) (C2 : choice T2),
    path K T2 C2 -> path K (TyProduct T1 T2) (CProduct C1 C2)

(* For sums, the choice allows only one alternative. *)
| PLeft : forall T1 T2 (C1 : choice T1),
    path K T1 C1 -> path K (TySum T1 T2) (CLeft C1)
| PRight : forall T1 T2 (C2 : choice T2),
    path K T2 C2 -> path K (TySum T1 T2) (CRight C2)

(* A path in a function specifies an argument to continue. *)
| PFun : forall T U (c : sem K T -> choice U),
    forall (t : sem K T), path K U (c t) -> path K (T :-> U) (CArrow c).

Arguments PHere [K].
Arguments PFst [K T1 T2 C1 C2] _.
Arguments PSnd [K T1 T2 C1 C2] p.
Arguments PLeft [K T1 T2 C1] p.
Arguments PRight [K T1 T2 C2] p.
Arguments PFun [K T U c] t p.

(** Isomorphism between A and B. *)
Inductive iso (A : Set) (B : Set) : Set :=
| Iso : forall (constr : B -> A) (destr : A -> B),
    (forall a, constr (destr a) = a) ->
    (forall b, destr (constr b) = b) ->
    iso A B.

Definition to {A} {B} (i : iso A B) : A -> B :=
  match i with
  | Iso _ _ _ destr _ _ => destr
  end.

Definition from {A} {B} (i : iso A B) : B -> A :=
  match i with
  | Iso _ _ constr _ _ _ => constr
  end.

(** We want to interpret [T] at the type of its own paths.
    But it seems unlikely that we can have literally
    [K = path K T C]; isomorphism is the next best thing.

    The poorly chosen name of [initial] refers to the fact
    that this somehow corresponds to an initial algebra
    construction. *)
Definition initial (K : Set) (T : type) (C : choice T) : Type :=
  iso K (path K T C).

(** The predicate [chosen T C x] states that
    a value [x : sem K T] matches the given [choice]. *)
Inductive chosen
          {K : Set}
  : forall (T : type), choice T -> sem K T -> Set :=
| ChUnit : chosen TyUnit CUnit tt
| ChProduct : forall T1 T2 C1 C2 x1 x2,
    chosen T1 C1 x1 -> chosen T2 C2 x2 -> chosen (TyProduct T1 T2) (CProduct C1 C2) (x1, x2)
| ChLeft : forall T1 T2 C1 x1,
    chosen T1 C1 x1 -> chosen (TySum T1 T2) (CLeft C1) (inl x1)
| ChRight : forall T1 T2 C2 x2,
    chosen T2 C2 x2 -> chosen (TySum T1 T2) (CRight C2) (inr x2)
| ChArrow : forall T U c x,
    (forall t, chosen U (c t) (x t)) -> chosen (T :-> U) (CArrow c) x
| ChAlpha : forall x, chosen TyAlpha CAlpha x.

Arguments ChProduct [K T1 T2 C1 C2 x1 x2] _ _.
Arguments ChLeft [K T1 T2 C1 x1] _.
Arguments ChRight [K T1 T2 C2 x2] _.
Arguments ChArrow [K T U c x] _.
Arguments ChAlpha [K] _.

(** Given a path [p : path K T C] and a (chosen) value [x : sem K T],
    we can follow the path to a leaf of type [K]. *)
Fixpoint index {K : Set} {T : type} {C : choice T} {x : sem K T} (k : chosen T C x) (p : path K T C) : K :=
  match p in path _ T C return forall x, chosen T C x -> K with
  | PHere =>
    fun _ k =>
      match
        k in chosen _ CAlpha x
        return K
      with
      | ChAlpha x => x
      end
  | PFun t p1 =>
    fun _ k =>
      match
        k in chosen _ (@CArrow _ T U c) r
        return forall t, path K U (c t) -> K
      with
      | ChArrow k1 => fun t p1 => index (k1 t) p1
      end t p1
  | @PFst _ T1 _ C1 _ p1 =>
    fun _ k1 =>
      match
        k1 in chosen _ (@CProduct _ T1 _ C1 _) r
        return path _ T1 C1 -> K
      with
      | ChProduct k1 _ => fun p1 => index k1 p1
      end p1
  | @PSnd _ _ T2 _ C2 p2 =>
    fun _ k =>
      match
        k in chosen _ (@CProduct _ _ T2 _ C2) r
        return path K T2 C2 -> K
      with
      | ChProduct _ k2 =>
        fun p2 => index k2 p2
      end p2
  | @PLeft _ T1 _ C1 p1 =>
    fun _ k =>
      match
        k in chosen _ (@CLeft _ T1 _ C1) r
        return path K T1 C1 -> K
      with
      | ChLeft k1 => fun p1 => index k1 p1
      end p1
  | @PRight _ _ T2 C2 p2 =>
    fun _ k =>
      match
        k in chosen _ (@CRight _ _ T2 C2) r
        return path K T2 C2 -> K
      with
      | ChRight k2 => fun p2 => index k2 p2
      end p2
  end x k.

(** A property that should be satisfied by values produced
    by our generator (to be defined): every leaf encodes
    the path to itself. *)
Definition generates {K : Set} {T : type} {C : choice T} (i : initial K T C) (x : sem K T) (k : chosen T C x) :=
  forall (p : path K T C), index k p = from i p.

Inductive variance : Set :=
| CO : variance
| CONTRA : variance.

Definition covary (co : variance) : variance :=
  match co with
  | CO => CONTRA
  | CONTRA => CO
  end.

Inductive variant : variance -> type -> Set :=
| VAlpha : variant CO TyAlpha
| VUnit : forall co, variant co TyUnit
| VZero : forall co, variant co TyZero
| VProduct : forall co {T1 T2},
    variant co T1 -> variant co T2 -> variant co (TyProduct T1 T2)
| VSum : forall co {T1 T2},
    variant co T1 -> variant co T2 -> variant co (TySum T1 T2)
| VArrow : forall co {T U},
    variant (covary co) T ->
    variant co U ->
    variant co (T :-> U).

Definition switch {U : Type} (co : variance) (K : U) (H : U) :=
  match co with
  | CO => K
  | CONTRA => H
  end.

Lemma switch_covary :
  forall {U : Type} (co : variance),
    switch (covary co) = (fun (K H : U) => switch co H K).
Proof.
  intros.
  destruct co; auto.
Qed.

Fixpoint map_co
         {K H : Set} {T : type} {co : variance}
         (v : variant co T) (f : K -> H)
  : sem (switch co K H) T ->
    sem (switch co H K) T :=
  match
    v in variant co T
    return sem (switch co K H) T -> sem (switch co H K) T
  with
  | VAlpha => f
  | VUnit _ => fun x => x
  | VZero _ => fun x => x
  | VProduct _ v1 v2 =>
    fun x =>
      match x with
      | (x1, x2) => (map_co v1 f x1, map_co v2 f x2)
      end
  | VSum _ v1 v2 =>
    fun x =>
      match x with
      | inl x1 => inl (map_co v1 f x1)
      | inr x2 => inr (map_co v2 f x2)
      end
  | @VArrow co T U v1 v2 =>
    fun x =>
      let comap := eq_rect
                     (switch (covary co))
                     (fun sw => sem (sw K H) T -> sem (sw H K) T)
                     (map_co v1 f)
                     (fun K H => switch co H K)
                     (switch_covary co)
      in fun t => map_co v2 f (x (comap t))
  end.

Definition covariant := variant CO.

Inductive project
          {K : Set} {B : Set} (f : K -> B)
  : forall (T : type) (C : @choice K T),
    (path K T C -> B) ->
    sem K T ->
    sem B T ->
    Set :=
| ProjAlpha : forall x y, project f TyAlpha CAlpha (fun PHere => y) x y
| ProjUnit : project f TyUnit CUnit (fun p => match p with end) tt tt
| ProjProduct : forall T1 T2 C1 C2 g1 g2 x1 x2 y1 y2,
    project f T1 C1 g1 x1 y1 -> project f T2 C2 g2 x2 y2 ->
    project f (TyProduct T1 T2) (CProduct C1 C2)
            (fun p =>
               match
                 p in path _ _ (@CProduct _ T1 T2 C1 C2)
                 return forall A,
                   (path _ T1 C1 -> A) -> (path _ T2 C2 -> A) -> A
               with
               | PFst p1 => fun _ g1 _ => g1 p1
               | PSnd p2 => fun _ _ g2 => g2 p2
               end _ g1 g2) (x1, x2) (y1, y2)
| ProjLeft : forall T1 T2 C1 g1 x1 y1,
    project f T1 C1 g1 x1 y1 ->
    project f (TySum T1 T2) (CLeft C1)
            (fun p =>
               match
                 p in path _ _ (@CLeft _ T1 _ C1)
                 return forall A, (path _ T1 C1 -> A) -> A
               with
               | PLeft p1 => fun _ g1 => g1 p1
               end _ g1) (inl x1) (inl y1)
| ProjRight : forall T1 T2 C2 g2 x2 y2,
    project f T2 C2 g2 x2 y2 ->
    project f (TySum T1 T2) (CRight C2)
            (fun p =>
               match
                 p in path _ _ (@CRight _ _ T2 C2)
                 return forall A, (path _ T2 C2 -> A) -> A
               with
               | PRight p2 => fun _ g2 => g2 p2
               end _ g2) (inr x2) (inr y2)
| ProjArrow : forall T U c g x y (v : covariant T),
    (forall (t : sem K T),
        project f U (c t) (g t) (x t) (y (map_co v f t))) ->
    project f (T :-> U) (CArrow c)
            (fun p =>
               match
                 p in path _ _ (@CArrow _ T U c)
                 return forall A, (forall t, path _ U (c t) -> A) -> A
               with
               | PFun t pf => fun _ g => g t pf
               end _ g) x y.

(** * Properties of test case generators *)

(** Ordering between individual inputs.
    [x] subsumes [y] if [x] distinguishes polymorphic functions
    better than [y]. *)
Definition
  subsumes {K H : Set} {T : type} (S : Set -> Set)
  (x : sem K T) (y : sem H T) : Prop :=
  forall (f g : forall {L}, sem L T -> S L), f x = g x -> f y = g y.

(** Completeness.
    Every possible input [y] is subsumed
    by a generated test case [x]. *)
Definition
  complete (T : type) (S : Set -> Set)
  (Generated : forall K, sem K T -> Prop) : Prop :=
  forall H (y : sem H T), exists K x, Generated K x /\ subsumes S x y.

(** Canonicity properties. *)

(** Optimality of a test case.
    Every generated test case [x] is as general as possible:
    if another [y] subsumes [x], then [x] also subsumes [y]. *)
Definition
  optimality (T : type) (S : Set -> Set)
  (Generated : forall K, sem K T -> Prop) : Prop :=
  forall K x, Generated K x -> forall H (y : sem H T), subsumes S x y -> subsumes S y x.

(** Non-redundancy.
    Generated test cases don't subsume each other. *)
Definition
  non_redundant (T : type) (S : Set -> Set)
  (Generated : forall K, sem K T -> Prop) : Prop :=
  forall K x H y, Generated K x -> Generated H y -> subsumes S x y -> JMeq x y.

(*  
Inductive generate (K : Set) (T : type) (C : choice T) (x : 
*)
