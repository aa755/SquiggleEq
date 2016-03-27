(* MathClasses or Extlib may habe a much richer theory and implementation *)
Require Import Coq.Classes.DecidableClass.



Class Deq T := deceq :> forall (a b:T), Decidable (a=b).

Require Import list.

Class VarType (T:Type) `{Deq T} (ClassType : Type) := {
(* There can be different classes of variables, e.g. one for types, and one for terms.
We need to put this in the interface, because substitution may need to rename bound variables,
and we would like to preserve variable classes when renaming bould variables.*)
  varClass : T -> ClassType;

(* [original] is a mechanism to pass extra information to [fresh]. 
  For example, we often want the fresh replacement names to be close to original names.
  In such cases, [length original=n]. The correctness properties of [fresh] ignore this input *)
  fresh : forall (avoid : list T) (n:nat)  (c : option ClassType) (original : list T), list T;

(* Is it important to pick a more efficient variant of [nat]? This not a concern after extraction.
Even inside Coq the output is a list which will be built one element at a time. So [nat] should not
be the bottleneck*)

  freshCorrect: forall (avoid : list T) (oc: option ClassType) (n:nat) (original : list T), 
    let lf:= (fresh avoid n oc original) in
      no_repeats lf 
      /\ disjoint lf avoid
      /\ (forall c, oc = Some c -> forall v, In v lf -> varClass v = c); 
}. 