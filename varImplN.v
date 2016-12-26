Require Import UsefulTypes.

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.


Require Import varInterface.
Section NClasses.

Variable numClasses : N.
Open Scope N_scope.

Hypothesis numClassesPos: 0 < numClasses.

Let class := (sig (fun n => N.ltb n numClasses = true)).

Global Instance varClassN : VarClass N class.
Proof using numClasses numClassesPos.
intros p.
exists (p mod numClasses).
apply N.ltb_lt.
apply N.mod_lt.
apply N.neq_0_lt_0.
assumption.
Defined.


Require Import list.

Definition freshVarsNAux (n:nat) 
  (c : N) (avoid original : list N) : list N :=
let maxn := NLmax avoid  0 in
List.map (fun x => (numClasses*x)+c)%N (seq N.succ (maxn) n).


Global Instance freshVarsN : FreshVars N class:=
fun (n:nat) 
  (c : option class) (avoid original : list N)
=>
let c : N :=
  match c with
  |Some c => proj1_sig c
  |None => 0%N
  end in
  freshVarsNAux n c avoid original.

Require Import tactics.

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


Lemma freshVarsNCorrect:
forall (n : nat) (oc : option class) (avoid original : list N),
let lf := freshVarsN n oc avoid original in
(NoDup lf /\ list.disjoint lf avoid /\ Datatypes.length lf = n) /\
(forall c : class, oc = Some c -> forall v : N, In v lf -> varClassN v = c).
Proof.
  intros.
  split;[split;[|split]|]; subst lf; simpl; unfold freshVarsN,freshVarsNAux.
- apply NoDupInjectiveMap;[|apply seq_NoDup].
  destruct oc; [destruct c as [c p]|];
  unfold injective_fun; intros;
  cpx; inversion H; simpl in *; auto;
  [apply N.ltb_lt in p |];
    [apply N.ltb_lt in p |]; try nia.

- intros ? Hin Hinc.
  apply in_map_iff in Hin. exrepnd.
  pose proof (seq_NMax _ t avoid _ Hin1 Hinc) as Hin.
  subst. apply in_seq_Nplus in Hin1.
   destruct oc as [c | ]; 
  [destruct c as [c p]|]; simpl in *;
  [apply N.ltb_lt in p |]; try nia.
- rewrite map_length. rewrite seq_length. refl. 
- intros ? ?. subst. intros ? Hin. simpl.
  apply in_map_iff in Hin.
  exrepnd.
  subst.
  unfold varClassP.
  destruct c; refl.
Qed.

Global Instance vartypePos : VarType positive bool.
  apply Build_VarType.
  exact freshVarsPosCorrect.
Defined.
