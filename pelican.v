Require Import List.
Require Import Nat.

Inductive type :=
| TyUnit : type
| TyZero : type
| TyArr  : type -> type -> type
| TyProduct : type -> type -> type
| TySum : type -> type -> type
| TyAlpha : type.

Infix ":->" := TyArr (at level 30, right associativity) : type_scope.

Definition t := TyAlpha :-> TyAlpha.
Definition t2 := TyProduct (TyAlpha :-> TyAlpha) TyAlpha.
Print t2.

Fixpoint sem (K : Set) (T : type) : Set :=
  match T with
  | TyAlpha => K
  | TyProduct T1 T2 => sem K T1 * sem K T2
  | TySum T1 T2 => sem K T1 + sem K T2
  | T :-> U => sem K T -> sem K U
  | TyUnit => unit
  | TyZero => Empty_set
  end.

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

Inductive path
          (K : Set)
  : forall (T : type), choice T -> Set :=
| PHere : path K TyAlpha CAlpha
| PFst : forall T1 T2 (C1 : choice T1) (C2 : choice T2),
    path K T1 C1 -> path K (TyProduct T1 T2) (CProduct C1 C2)
| PSnd : forall T1 T2 (C1 : choice T1) (C2 : choice T2),
    path K T2 C2 -> path K (TyProduct T1 T2) (CProduct C1 C2)
| PLeft : forall T1 T2 (C1 : choice T1),
    path K T1 C1 -> path K (TySum T1 T2) (CLeft C1)
| PRight : forall T1 T2 (C2 : choice T2),
    path K T2 C2 -> path K (TySum T1 T2) (CRight C2)
| PFun : forall T U (c : sem K T -> choice U),
    forall (t : sem K T), path K U (c t) -> path K (T :-> U) (CArrow c).

Arguments PHere [K].
Arguments PFst [K T1 T2 C1 C2] _.
Arguments PSnd [K T1 T2 C1 C2] p.
Arguments PLeft [K T1 T2 C1] p.
Arguments PRight [K T1 T2 C2] p.
Arguments PFun [K T U c] t p.

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

Definition initial (K : Set) (T : type) (C : choice T) : Type :=
  iso K (path K T C).

Inductive chosen
          {K : Set}
  : forall (T : type), @choice K T -> sem K T -> Prop :=
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

Fixpoint index {K : Set} {T : type} {C : choice T} {x : sem K T} (k : chosen T C x) (p : path K T C) : K. Admitted.
  (* :=
  match p, k with
  | PHere, ChAlpha x => x
  | PFun t p1, ChArrow k1 => index (k1 t) p1
  | PFst p1, ChProduct k1 _ => index k1 p1
  | PSnd p1, ChProduct _ k2 => index k2 p1
  | PLeft p1, ChLeft k1 => index k1 p1
  | PRight p1, ChRight k2 => index k2 p1
  | _, _ => _
  end.
   *)

Definition generates {K : Set} {T : type} {C : choice T} (i : initial K T C) (x : sem K T) (k : chosen T C x) :=
  forall (p : path K T C), index k p = from i p.
  

(*  
Inductive generate (K : Set) (T : type) (C : choice T) (x : 
*)
