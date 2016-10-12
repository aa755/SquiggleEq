Require Export varInterface.
Require Export terms.
Require Export terms2.
Require Export substitution.
Require Export alphaeq.

(* Move these to appropriate earlier
files. These were placed here
to avoid recompiling all files *)

Section Vars.
Context {V VC} `{VarType V VC}.

Definition freshVar  (o : VC) (lx : list V) : V.
Proof.
  pose proof (freshCorrect 1 (Some o) lx nil) as Hfr. simpl in Hfr.
  apply  proj1, proj2, proj2 in Hfr.
  apply (listHead (freshVars 1 (Some o) lx nil)).
  rewrite Hfr. constructor.
Defined.
End Vars.

Require Import List.

Fixpoint tmap {V1 V2 O1 O2  :Type} (fv: V1 -> V2) (fo : O1 -> O2) (t : @NTerm V1 O1) 
  : (@NTerm V2 O2) :=
match t with
| vterm v =>  vterm (fv v)
| oterm o lbt => oterm (fo o) (map (tmap_bterm fv fo) lbt)
end
with 
tmap_bterm {V1 V2 O1 O2  :Type} (fv: V1 -> V2) (fo : O1 -> O2) (t : @BTerm V1 O1) 
  : (@BTerm V2 O2) :=
match t with
| bterm lv nt => bterm (map fv lv) (tmap fv fo nt)
end.

Definition tvmap {V1 V2 O  :Type} (fv: V1 -> V2) : (@NTerm V1 O) -> (@NTerm V2 O) :=
tmap fv id.


