(* MathClasses or Extlib may habe a much richer theory and implementation *)
Require Import Coq.Classes.DecidableClass.

Instance DecConj A B (_: Decidable A) (_ :Decidable B) : Decidable (A /\ B).
Proof.
  exists (andb (decide A) (decide B)).
  unfold decide.
  destruct H.
  destruct H0.
  rewrite Bool.andb_true_iff.
  unfold DecidableClass.Decidable_witness. tauto.
Defined.


Instance DecEqPair (A B : Type) (H1 : forall x y:A, Decidable (x=y))
(H2 :forall x y:B, Decidable (x=y))
 : (forall x y:(A*B), Decidable (x=y)).
Proof.
  intros ? ?. destruct x. destruct y.
  exists (decide (a=a0 /\ b = b0)).
  rewrite Decidable_spec.
  split; intros H; auto; inversion H; auto.
  congruence.
Defined.

Class Deq T := deceq :> forall (a b:T), Decidable (a=b).

Require Import list.

Class VarType (T:Type) `{Deq T}:= {
  varClass : T -> nat;

(* [original] is a mechanism to pass extra information to [fresh]. 
  For example, we often want the fresh replacement names to be close to original names.
  In such cases, [length original=n]. The correctness properties of [fresh] ignore this input *)
  fresh : forall (avoid : list T) (n:nat) (original : list T), list T;

(* Is it important to pick a more efficient variant of [nat]? This not a concern after extraction.
Even inside Coq the output is a list which will be built one element at a time. So [nat] should not
be the bottleneck*)

  freshCorrect: forall (avoid : list T) (n:nat) (original : list T), 
    let lf:= (fresh avoid n original) in
      no_repeats lf /\ disjoint lf avoid;

}.