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

Generalizable Variable Opid.

Section terms.


Context `{Deq Opid} {gts : GenericTermSig Opid}.

Inductive DTerm : Type :=
| vterm: N (* generalize over N?*) -> DTerm
| oterm: Opid -> list DBTerm -> DTerm
with DBTerm : Type :=
| bterm: N -> DTerm -> DBTerm.

Definition isvar (t : DTerm) :=
  match t with
    | vterm _ => true
    | _ => false
  end.


Definition getOpid (n: DTerm) : option Opid :=
match n with
| vterm _ => None
| oterm o _ => Some o
end. 


(*Notation "x # b" := (bterm [x] b) (at level 70, right associativity).
(*Check [[ btermO (vterm(nvar 0))]] *)
(* Notation "< N >" := (btermO N). *)
Notation "\\ f" :=
  (oterm (Can NLambda) [[f]]) (at level 70, right associativity).

*)


(* ------ CONSTRUCTORS ------ *)


(* --- primitives --- *)


(* end hide *)
(** %\noindent% Whenever we talk about the [NTerm] of a [BTerm], this is
what we would mean:

*)
Definition get_nt  (bt: DBTerm ) : DTerm :=
 match bt with
 | bterm _ nt => nt
 end.

Definition num_bvars  (bt: DBTerm ) : N :=
 match bt with
 | bterm n _ => n
 end.

(** % \noindent \\* % We define
    a predicate [nt_wf] on [NTerm] such that
    [nt_wf nt] asserts that [nt] is a well-formed term.  %\\* %
*)
Inductive nt_wf: DTerm -> [univ] :=
| wfvt: forall nv : N, nt_wf (vterm nv)
| wfot: forall (o: Opid) (lnt: list DBTerm),
        (forall l, LIn l lnt -> bt_wf l)
         -> map (num_bvars) lnt 
            = map N.of_nat (OpBindings o)
         -> nt_wf (oterm o lnt)
with bt_wf : DBTerm -> [univ] :=
| wfbt : forall (lnv : N) (nt: DTerm),
         nt_wf nt -> bt_wf (bterm lnv nt).

Open Scope N_scope.

(** Just decidability of equality on variables suffices for these definitions.
  The full [VarType] may not be needed until [ssubst]*)
Inductive fvars_below : N -> DTerm -> Prop :=
| var_below: forall i j, j < i -> fvars_below i (vterm j)
| ot_below: forall i (o: Opid) (lnt: list DBTerm),
  (forall l, LIn l lnt -> bt_wf l)
  -> map (num_bvars) lnt 
      = map N.of_nat (OpBindings o)
  -> fvars_below i (oterm o lnt)
with fvars_below_bt : N->DBTerm -> Prop :=
| bt_below : forall (i n : N) (nt: DTerm),
         fvars_below (n+i) nt -> fvars_below_bt i (bterm n nt).


End terms.

Fixpoint subst_aux {Opid:Type}(v:DTerm) k (e:@DTerm Opid): @DTerm Opid:=
match e with
| vterm i => 
  match N.compare i k with
  | Lt => vterm i
  | Eq => v
  | Gt => vterm (i - 1)%N
  end
| oterm o lbt => oterm o (map (subst_aux_bt v k) lbt)
end
with subst_aux_bt {Opid:Type} (v:@DTerm Opid) k (e:@DBTerm Opid): @DBTerm Opid:=
match e with
| bterm m t => bterm m (subst_aux v (m+k) t)%N
end.




Section DBToNamed.
Context {NVar VarClass} `{VarType NVar VarClass} `{Deq Opid} {gts : GenericTermSig Opid}.
Definition all_vars (t:@NTerm NVar Opid) : list NVar := free_vars t ++ bound_vars t.

End DBToNamed.



