Require Import UsefulTypes.

Require Import Coq.Arith.Arith Coq.NArith.BinNat
  Coq.Strings.String Coq.Lists.List Coq.omega.Omega
  Coq.Program.Program Coq.micromega.Psatz.


Require Import varInterface.
Section NClasses.

Require Import list.
Require Import DecidableClass.

Variable numClasses : N.
Open Scope N_scope.

Hypothesis numClassesPos: decide (0 < numClasses)%N=true.

Let class := decSubtype (fun n => (n<numClasses)%N).

(* nobody should match on the proof *)
Lemma modDecPos p: decide (p mod numClasses < numClasses) = true.
Proof.
  apply N.ltb_lt.
  apply N.mod_lt.
  apply N.neq_0_lt_0.
  setoid_rewrite Decidable_spec in numClassesPos.
  assumption.
Qed.

Local Instance varClassN : VarClass N class.
Proof using numClasses numClassesPos.
  intros p.
  exists (p mod numClasses).
  apply modDecPos.
Defined.



Definition freshVarsNAux (n:nat) 
  (c : N) (avoid original : list N) : list N :=
let maxn := N.succ (NLmax avoid  0) in
List.map (fun x => (numClasses*x)+c)%N (seq N.succ (maxn) n).


Local Instance freshVarsN : FreshVars N class:=
fun (n:nat) 
  (c : option class) (avoid original : list N)
=>
let c : N :=
  match c with
  |Some c => proj1_sig c
  |None => 0%N
  end in
  freshVarsNAux n c avoid original.


Lemma seq_NMax : forall a v avoid n,
 LIn a (seq N.succ (NLmax avoid 0) n)
 -> LIn v avoid
 -> (v <= a)%N.
Proof using.
  clear.
  intros ? ? ? ? Hin1 Hina.
  apply in_seq_Nplus in Hin1.
  pose proof (NLmax_le v avoid  (Hina)).
  lia.
Qed.

Require Import tactics.

Lemma freshVarsNCorrect:
forall (n : nat) (oc : option class) (avoid original : list N),
let lf := freshVarsN n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : class, oc = Some c -> forall v : N, In v lf -> varClassN v = c).
Proof.
  intros.
  pose proof numClassesPos as numClassesPosb.
  setoid_rewrite Decidable_spec in numClassesPosb.
  split;[split;[|split]|]; subst lf; simpl; unfold freshVarsN,freshVarsNAux.
- apply NoDupInjectiveMap;[|apply seq_NoDup].
  setoid_rewrite Decidable_spec in numClassesPos.
  destruct oc; [destruct c as [c p]|];
  unfold injective_fun; intros;
  cpx; inversion H; simpl in *; auto;
  [apply N.ltb_lt in p |];
    [apply N.ltb_lt in p |]; try nia.

- intros ? Hin Hinc.
  apply in_map_iff in Hin. exrepnd.
  rename Hin1 into Hin.
  rewrite seq_shift in Hin.
  apply in_map_iff in Hin. exrepnd. subst.
  rename a0 into t.
  pose proof (seq_NMax _ _ avoid _ Hin2 Hinc) as Hin.
  subst. apply in_seq_Nplus in Hin2.
   destruct oc as [c | ]; 
  [destruct c as [c p]|]; simpl in *;
  [apply N.ltb_lt in p |]; try nia.
- rewrite map_length. rewrite seq_length. refl. 
- intros ? ?. subst. intros ? Hin. simpl.
  apply in_map_iff in Hin.
  exrepnd.
  subst.
  unfold varClassN.
  apply decSubtypeProofIrr.
  simpl.
  destruct c as [c p]; simpl in *. clear Hin1.
  apply N.ltb_lt in p.
  rewrite N.add_comm.
  rewrite N.mul_comm.
  rewrite N.mod_add;[| lia].
  clear a.
  rewrite N.mod_small; lia.
Qed.

Local Instance vartypeN : VarType N class.
  apply Build_VarType.
  exact freshVarsNCorrect.
Defined.

End NClasses.
