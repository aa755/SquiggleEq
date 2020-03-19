Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.
Require Import list.

Require Import Recdef.
Require Import Eqdep_dec.
Require Import varInterface.
Require Import terms.
Require Import terms2.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** Here are some handy definitions that will
    reduce the verbosity of some of our later definitions
*)
Require Import alphaeq.
Require Import substitution.

Generalizable Variable Opid.

Section terms2Generic.

  Context {NVar VarClass Opid:Set} {deqnvar : Deq NVar}
          {varcl freshv} {varclass: @VarType NVar VarClass deqnvar varcl freshv} 
`{hdeq: Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).

(* WTerm was in Type, which can sometimes be problematic.
Also, Definitions are not template polymorphic. So there are 2 choices:
Make NTerm universe polymporphic. Currently it is template polymorphic. 
Then there is the choice in this file, which is to duplicate some definitions (of types) *)

Definition WTermSet :Set := { t : NTerm  | wf_term t }.
Definition WBTermSet : Set := { bt : BTerm | wf_bterm bt }.


Definition subst_wftset (t : WTermSet) (v : NVar) (u : WTermSet) : WTermSet :=
  let (a,x) := t in
  let (b,y) := u in
  exist wf_term (subst a v b) (subst_preserves_wf_term a v b x y).

End terms2Generic.
