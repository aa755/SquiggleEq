
Require Import list.

Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import tactics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.

Class GenericTermSig : Type :=
{
  CanonicalOp : Set;
  NonCanonicalOp  : Set;
  OpBindingsCan : CanonicalOp -> list nat;
  OpBindingsNCan : NonCanonicalOp -> list nat;
  canonical_dec : forall x y : CanonicalOp, {x = y} + {x <> y};
  ncanonical_dec : forall x y : NonCanonicalOp, {x = y} + {x <> y}
}.

Section opids.
Context {gts : GenericTermSig}.

Inductive Opid : Set :=
 | Can  : CanonicalOp -> Opid
 | NCan : NonCanonicalOp -> Opid.

Definition OpBindings (op : Opid) : list nat :=
 match op with
 | Can c   => OpBindingsCan c
 | NCan nc => OpBindingsNCan nc
 end.


Tactic Notation "dopid" ident(o) "as" simple_intropattern(I) ident(c) :=
  destruct o as I;
  [ Case_aux c "Can"
  | Case_aux c "NCan"
  ].


Lemma opid_dec : forall x y : Opid, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x; destruct y;
  try destruct c; try destruct c0;
  try destruct n; try destruct n0;
  try destruct c; try destruct c0;
  try destruct a; try destruct a0;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).
  destruct (canonical_dec c c0); subst; [left|right];
     auto. intro Hc. inversion Hc. auto.
  destruct (ncanonical_dec n n0); subst; [left|right];
     auto. intro Hc. inversion Hc. auto.
Qed.

End opids.
