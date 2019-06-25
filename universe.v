
(** 
To ensure that our definitions are predicative, we try to ensure that our development compiles
when we replace uses of Prop by Type. Therefore, we use the notation [univ] which can be defined
as either Prop or Type, depending on how much we trust impredicativity on a given day!
*)

Notation "[univ]" := Prop.

Notation "! x" := (not x)%type (at level 75, right associativity).
Notation "T # U" := (T /\ U)%type (at level 80, right associativity).
Notation "T [+] U" := (T \/ U)%type (at level 80, right associativity).

Notation "{ a : T $ P }" :=
  (exists (a : T), P)
    (at level 0, a at level 99).

Notation projDep1 := proj1_sig.


Notation "injL( a )" := (or_introl a) (at level 0).
Notation "injR( a )" := (or_intror a) (at level 0).
Notation "exI( a , b )" := (ex_intro _ a b) (at level 0).