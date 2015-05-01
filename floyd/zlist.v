Require Import floyd.base.

Open Scope Z.

Section ZLIST.

Fixpoint force_lengthn {A} n (xs: list A) (default: A) :=
  match n, xs with
  | O, _ => nil
  | S n0, nil => default :: force_lengthn n0 nil default
  | S n0, hd :: tl => hd :: force_lengthn n0 tl default
  end.

Class Zlist (A: Type) (default: A) : Type := mkZlist {
  zlist: Z -> Z -> Type;
  zl_concat: forall {lo mid hi}, zlist lo mid -> zlist mid hi -> zlist lo hi;
  zl_sublist: forall {lo hi} lo' hi', zlist lo hi -> zlist lo' hi';
  zl_shift: forall {lo hi} lo' hi', zlist lo hi -> zlist lo' hi';
  zl_singlton: forall i, A -> zlist i (i + 1);
  zl_empty: forall i, zlist i i;
  zl_default: forall lo hi, zlist lo hi;
  zl_nth: forall {lo hi}, Z -> zlist lo hi -> A
}.

Global Arguments zlist A {_} {_} _ _.

Instance list_zlist (A: Type) (default: A) : Zlist A default.
  apply (mkZlist A default (fun _ _ => list A)).
  + exact (fun lo mid hi l1 l2 => (force_lengthn (nat_of_Z (mid - lo)) l1 default) ++ l2).
  + exact (fun lo hi  lo' hi' l => if zle lo lo' then skipn (nat_of_Z (lo' - lo)) l else nil).
  + exact (fun lo hi  lo' hi' l => l).
  + exact (fun i v => v :: nil).
  + exact (fun _ => nil).
  + exact (fun _ _ => nil).
  + exact (fun lo hi i l => if zle lo i then Znth (i - lo) l default else default).
Defined.

Definition zl_equiv {A d} `{Zlist A d} {lo hi} (l1 l2: zlist A lo hi) : Prop :=
  forall i, lo <= i < hi -> zl_nth i l1 = zl_nth i l2.

Notation "A '===' B" := (zl_equiv A B) (at level 80, no associativity).

Class Zlist_Correct {A d} `(Zlist A d) : Type := mkZlistCorrect {
  zl_concat_correct:
    forall lo mid hi i (l1: zlist A lo mid) (l2: zlist A mid hi),
    lo <= mid <= hi ->
    lo <= i < hi ->
    zl_nth i (zl_concat l1 l2) = if zlt i mid then zl_nth i l1 else zl_nth i l2;
  zl_sublist_correct:
    forall lo hi lo' hi' i (l: zlist A lo hi),
    lo <= lo' ->
    lo' <= i < hi' ->
    hi' <= hi ->
    zl_nth i (zl_sublist lo' hi' l) = zl_nth i l;
  zl_shift_correct:
    forall lo hi lo' hi' i (l: zlist A lo hi) mv,
    lo - lo' = mv ->
    hi - hi' = mv ->
    lo' <= i < hi' ->
    zl_nth i (zl_shift lo' hi' l) = zl_nth (i + mv) l;
  zl_default_correct:
    forall lo hi i,
    lo <= i < hi ->
    zl_nth i (zl_default lo hi) = d;
  zl_concat_assoc:
    forall lo i1 i2 hi (l1: zlist A lo i1) (l2: zlist A i1 i2) (l3: zlist A i2 hi),
    lo <= i1 /\ i1 <= i2 /\ i2 <= hi ->
    zl_concat l1 (zl_concat l2 l3) === zl_concat (zl_concat l1 l2) l3;
  zl_concat_sub:
    forall lo mid hi (l: zlist A lo hi),
    lo <= mid <= hi ->
    zl_concat (zl_sublist lo mid l) (zl_sublist mid hi l) === l;
  zl_sub_sub:
    forall lo hi lo' hi' lo'' hi'' (l: zlist A lo hi),
    lo <= lo' <= lo'' ->
    hi'' <= hi' <= hi ->
    lo'' <= hi'' ->
    zl_sublist lo'' hi'' (zl_sublist lo' hi' l) === zl_sublist lo'' hi'' l
}.

Instance list_zlist_correct (A: Type) (default: A) : Zlist_Correct (list_zlist A default).
admit.
Defined.

End ZLIST.

(*
Module Type Zlist.

Parameter list : Z -> Z -> Type.
Parameter app : forall {lo mid hi}, list lo mid -> list mid hi -> list lo hi.
Parameter sublist: forall {lo hi} lo' hi', list lo hi -> list lo' hi'.
Parameter singlton: forall i 
*)
