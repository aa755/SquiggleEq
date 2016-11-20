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
Require Import substitution.

Generalizable Variables Opid Name.

Section terms.


Context `{Deq Name} `{Deq Opid} {gts : GenericTermSig Opid}.

Inductive DTerm : Type :=
| vterm: N (* generalize over N?*) -> DTerm
| oterm: Opid -> list DBTerm -> DTerm
with DBTerm : Type :=
| bterm: list Name -> DTerm -> DBTerm.
(* binders have names, but only for readability.*)

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


Definition get_nt  (bt: DBTerm ) : DTerm :=
 match bt with
 | bterm _ nt => nt
 end.

Definition get_bvars  (bt: DBTerm ) : list Name :=
 match bt with
 | bterm n _ => n
 end.

Definition num_bvars  (bt: DBTerm ) : nat := length (get_bvars bt).

Inductive nt_wf: DTerm -> [univ] :=
| wfvt: forall nv : N, nt_wf (vterm nv)
| wfot: forall (o: Opid) (lnt: list DBTerm),
        (forall l, LIn l lnt -> bt_wf l)
         -> map (num_bvars) lnt 
            = (OpBindings o)
         -> nt_wf (oterm o lnt)
with bt_wf : DBTerm -> [univ] :=
| wfbt : forall (lnv : list Name) (nt: DTerm),
         nt_wf nt -> bt_wf (bterm lnv nt).

Open Scope N_scope.

(* move to list.v *)
Definition NLength {A:Type} (lv: list A) : N := N.of_nat (length lv).

(** Just decidability of equality on variables suffices for these definitions.
  The full [VarType] may not be needed until [ssubst]*)
Inductive fvars_below : N -> DTerm -> Prop :=
| var_below: forall i j, j < i -> fvars_below i (vterm j)
| ot_below: forall i (o: Opid) (lnt: list DBTerm),
  (forall l, In l lnt -> fvars_below_bt i l)
  -> fvars_below i (oterm o lnt)
with fvars_below_bt : N->DBTerm -> Prop :=
| bt_below : forall (i : N) (lv: list Name) (nt: DTerm),
  fvars_below (NLength lv +i) nt -> fvars_below_bt i (bterm lv nt).


End terms.

Fixpoint subst_aux {Opid Name:Type}(v:DTerm) k (e:@DTerm Opid Name)
  : @DTerm Opid Name:=
match e with
| vterm i => 
  match N.compare i k with
  | Lt => vterm i
  | Eq => v
  | Gt => vterm (i - 1)%N
  end
| oterm o lbt => oterm o (map (subst_aux_bt v k) lbt)
end
with subst_aux_bt {Opid Name:Type} (v:@DTerm Opid Name) 
    k (e:@DBTerm Opid Name): @DBTerm Opid Name:=
match e with
| bterm m t => bterm m (subst_aux v (NLength m+k) t)%N
end.

Require Import ExtLib.Data.Map.FMapPositive.

Definition lookupNDef {Name:Type} (def: Name) (names : pmap Name) (var:N) : Name :=
  opExtract def (pmap_lookup (N.succ_pos var) names).

Definition insertN {Name:Type} (names : pmap Name) (nvar:N*Name): pmap Name :=
  let (var,name) := nvar in
  pmap_insert (N.succ_pos var) name names.

Definition insertNs {Name:Type} (names : pmap Name) (nvars: list (N*Name)): pmap Name :=
fold_left insertN nvars names.

Open Scope N_scope.

Fixpoint fromDB {Name Opid NVar : Type} (defn: Name) (mkVar : (N * Name) -> NVar) 
  (max : N) 
  (names: pmap Name) (e:@DTerm Name Opid) {struct e}
  : (@NTerm NVar Opid) :=
match e with
| vterm n => terms.vterm (mkVar (max-n-1,lookupNDef defn names (max-n-1)))
| oterm o lbt => terms.oterm o (map (fromDB_bt defn mkVar max names) lbt)
end
with fromDB_bt {Name Opid NVar : Type} (defn: Name) (mkVar : (N * Name) -> NVar) 
  (max : N) 
  (names: pmap Name) (e:@DBTerm Name Opid) {struct e}
    : (@BTerm NVar Opid) :=
match e with
| bterm ln dt => 
    let len := length ln in
    let vars := (seq N.succ max len) in
    let nvars := (combine vars ln) in
    let names := insertNs names nvars in
    let bvars := map mkVar nvars in
    terms.bterm bvars (fromDB defn mkVar (max+ N.of_nat len) names dt)
end.

(* copied from terms2.v *)
Fixpoint size {NVar Opid:Type} (t : @DTerm NVar Opid) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => S (addl (map (@size_bterm NVar _) bterms))
  end
 with size_bterm {NVar Opid:Type} (bt: @DBTerm NVar Opid) :nat :=
  match bt with
  | bterm lv nt => @size NVar Opid nt
  end.

Require Import Coq.Unicode.Utf8.

Section DBToNamed.

Context {Name NVar VarClass : Type} {deqv vcc fvv}
  `{vartyp: @VarType NVar VarClass deqv vcc fvv} `{deqo: Deq Opid} {gts : GenericTermSig Opid} (def:Name).

(* copied from terms2.v *)
Lemma size_subterm2 :
  forall (o:Opid) (lb : list DBTerm) (b : DBTerm) ,
    LIn b lb
    ->  (size_bterm b <  @size Name _ (oterm o lb))%nat.
Proof using.
  simpl. induction lb; intros ? Hin; inverts Hin as; simpl; try omega.
  intros Hin. apply IHlb in Hin; omega.
Qed.

Lemma size_subterm3 :
  forall (o:Opid) (lb : list DBTerm) (nt : DTerm) (lv : list Name) ,
    In (bterm lv nt) lb
    ->  (size nt <  size (oterm o lb))%nat.
Proof using.
 introv X.
 apply size_subterm2 with (o:=o) in X. auto.
Qed.


Lemma NTerm_better_ind3 :
  forall P : (@DTerm Name Opid) -> Type,
    (forall n : N, P (vterm n))
    -> (forall (o : Opid) (lbt : list DBTerm),
          (forall (nt: DTerm),
              (size nt < size (oterm o lbt))%nat
              -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : DTerm, P t.
Proof using.
 intros P Hvar Hbt.
 assert (forall n t, size t = n -> P t) as Hass.
 Focus 2. intros. apply Hass with (n := size t) ; eauto; fail.
 
 induction n as [n Hind] using comp_ind_type.
 intros t Hsz.
 destruct t.
 apply Hvar.
 apply Hbt. introv Hs.
 apply Hind with (m := size nt) ; auto.
 subst.
 assert(size nt < size (oterm o l))%nat; auto.
Qed.


Lemma NTerm_better_ind2 :
  forall P : (@DTerm Name Opid) -> Type,
    (forall n : N, P (vterm n))
    -> (forall (o : Opid) (lbt : list DBTerm),
          (forall (nt nt': DTerm) (lv: list Name),
             (LIn (bterm lv nt) lbt)
              -> (size nt' <= size nt)%nat
              -> P nt'
          )
          -> P (oterm o lbt)
       )
    -> forall t : DTerm, P t.
Proof using.
 intros P Hvar Hbt.
 apply  NTerm_better_ind3; eauto.
 intros ? ? H.
 apply Hbt.
 intros ? ? ? Hin Hs. apply H.
 eapply le_lt_trans;[apply Hs|].
 eapply size_subterm3; eauto.
Qed.

(* TODO: this is structurally recursive use fix to make it compute *)
Lemma NTerm_BTerm_ind :
  forall (PN :  (@DTerm Name Opid) -> Type) (PB : DBTerm -> Type),
    (forall n : N, PN (vterm n))
    -> (forall (o : Opid) (lbt : list DBTerm),
          (forall b,
             (LIn b lbt) -> PB b
          )
          -> PN (oterm o lbt)
       )
    -> (forall (lv: list Name) (nt : DTerm),
          PN nt -> PB (bterm lv nt)
       )
    -> ((forall t : DTerm, PN t) *  (forall t : DBTerm, PB t)).
Proof using.
   introv Hv Hind Hb.
   assert (forall A B, A -> (A -> B) -> (A*B)) as H by tauto.
   apply H; clear H.
- apply  NTerm_better_ind2; auto. 
   introv Hx. apply Hind. introv Hin. destruct b. eauto.
- intro Hnt. intro b. destruct b. eauto.
Qed.

  Lemma pmap_lookup_insert_neq {T}
  : ∀ (m : pmap T) (k : positive) (v : T) (k' : positive),
      k ≠ k' →
        pmap_lookup k' (pmap_insert k v m) = pmap_lookup k' m.
  Proof.
    intros.
    remember (pmap_lookup k' m).
    destruct o; [
      apply pmap_lookup_insert_Some_neq; intuition |
      apply pmap_lookup_insert_None_neq; intuition].
  Qed.

  Lemma lookupNDef_insert_neq {T}
  : ∀ (m : pmap T) (k : N) (def : T) (p : N*T),
      fst p ≠ k →
        lookupNDef def (insertN m p) k = lookupNDef def m k.
  Proof.
    intros. unfold lookupNDef, insertN. f_equal. destruct p.
    apply pmap_lookup_insert_neq. intros Hc.
    apply injectiveNsuccpos in Hc. contradiction.
  Qed.

  (* move to a pmap file? *)
  Lemma lookupNDef_insert_eq {T}
  : ∀ (m : pmap T) (def : T) (p : N*T),
        lookupNDef def (insertN m p) (fst p) = snd p.
  Proof.
    intros.  unfold lookupNDef, insertN.
    destruct p. simpl. rewrite pmap_lookup_insert_eq.
    refl.
  Qed.

  Lemma lookupNDef_inserts_neq {T}
  : ∀ (k : N)  (def : T) (p : list (N*T)) (m : pmap T),
      disjoint (map fst p) [k] →
        lookupNDef def (insertNs m p) k = lookupNDef def m k.
  Proof.
    intros ? ? ?. induction p;[reflexivity| intros ? Hd].
    simpl in *. apply disjoint_cons_l in Hd.
    rewrite IHp;[| tauto].
    apply lookupNDef_insert_neq; auto. simpl in *.
    rewrite N.eq_sym_iff in Hd. tauto.
  Qed.

  Lemma lookupNDef_inserts_eq {T}
  : ∀ k (def : T) (p : list (N*T)) (m : pmap T),
    In k (map fst p)
    -> exists v, lookupNDef def (insertNs m p) k = v /\ In (k,v) p.
  Proof.
    intros ? ?. induction p; simpl; auto;[ tauto |].
    intros ? Hin.
    destruct (in_dec N.eq_dec k (map fst p)) as [Hd | Hd].
  - eapply IHp with (m:=(insertN m a)) in Hd.
    exrepnd. eexists; eauto.
  - dorn Hin;[| tauto]. subst. rewrite lookupNDef_inserts_neq; 
      [| repeat disjoint_reasoning; auto].
    rewrite lookupNDef_insert_eq. exists (snd a); cpx.
  Qed.


  Variable mkNVar: (N * Name) -> NVar.
  Variable getId: NVar -> N.
  Hypothesis getIdCorr: forall p n, getId (mkNVar (p,n)) = p.


Let fvarsProp (n:N) names (vars : list NVar): Prop := 
lforall
(fun v => 
let id := (getId v) in
  (id <  n)%N 
  /\ v = mkNVar (id,(lookupNDef def names id))
) vars.

Require Import Nsatz.
Require Import Psatz.

Let fromDB := (@fromDB Name Opid NVar def mkNVar).
Let fromDB_bt:= (@fromDB_bt Name Opid NVar def mkNVar).

Lemma fromDB_fvars: 
  (forall (s : DTerm) (n:N),
    fvars_below n s
    -> forall names, fvarsProp n names (@free_vars _ _ Opid (fromDB n names s)))
  *
  (forall (s : DBTerm) (n:N),
    fvars_below_bt n s
    -> forall names, fvarsProp n names (@free_vars_bterm _ _ Opid (fromDB_bt n names s))).
Proof using getIdCorr.
  apply NTerm_BTerm_ind; unfold fvarsProp.
- intros n nv Hfb ? ? Hin.
  simpl in *. rewrite or_false_r  in Hin. subst.
  repeat rewrite getIdCorr in *. split; [ | refl].
  inverts Hfb.
  lia.
- intros ? ? Hind n Hfb ? ? Hin.
  simpl in *. rewrite flat_map_map in Hin.
  apply in_flat_map in Hin.
  exrepnd. unfold compose in *. simpl in *.
  inverts Hfb.
  apply Hind in Hin0; eauto.
- intros ? ? Hind n Hfb ? ? Hin.
  simpl in *.
  rewrite N.add_comm in Hin.
  apply in_remove_nvars in Hin. repnd.
  invertsn Hfb.
  apply Hind in Hin0; [ | assumption].
  clear Hind Hfb. exrepnd.
  rewrite Hin0.
  rewrite Hin0 in Hin.
  rewrite Hin0 in Hin1.
  clear Hin0.
  repeat rewrite getIdCorr in *.
  pose proof (N.ltb_spec0 (getId a) n) as Hc.
  destruct (getId a <? n); invertsn Hc;[ clear Hin Hin1 | ].
  + split;[ assumption |]. 
    rewrite lookupNDef_inserts_neq; auto.
    rewrite <- combine_map_fst;[| rewrite seq_length; refl].
    intros ? Hin Hinc. apply in_seq_Nplus in Hin.
    apply in_single in Hinc. subst. lia.
  + provefalse. apply Hin. apply in_map.
    clear Hin. apply N.nlt_ge in Hc.
    rewrite N.add_comm in Hin1.
    pose proof (conj Hc Hin1) as Hcc. rewrite <- in_seq_Nplus in Hcc.
    clear Hc Hin1.
    pose proof (combine_map_fst (seq N.succ n (length lv)) lv 
      (seq_length _ _ _ _)) as He.
    rewrite He in Hcc.
    apply lookupNDef_inserts_eq with (m:=names) (def0:=def) in Hcc.
    exrepnd. rewrite Hcc1. assumption.
Qed.


Definition subst_aux_list : DTerm -> (list DTerm) -> (@DTerm Name Opid) :=
  fold_right  (fun v e => subst_aux v 0 e).

Definition subst_aux_bt_list : DBTerm -> (list DTerm) -> (@DBTerm Name Opid) :=
  fold_right  (fun v e => subst_aux_bt v 0 e).

Fixpoint subst_aux_list2_aux (e: DTerm)  (l:list DTerm) (n:N): (@DTerm Name Opid) :=
match l with
| [] => e
| h::tl => subst_aux_list2_aux (subst_aux h n e) tl (N.pred n)
end.

Fixpoint subst_aux_bt_list2_aux (e: DBTerm)  (l:list DTerm) (n:N): (@DBTerm Name Opid) :=
match l with
| [] => e
| h::tl => subst_aux_bt_list2_aux (subst_aux_bt h n e) tl (N.pred n)
end.

Definition subst_aux_list2 (e: DTerm)  (l:list DTerm): (@DTerm Name Opid) :=
  subst_aux_list2_aux e l (N.pred (NLength l)).

Definition subst_aux_bt_list2 (e: DBTerm)  (l:list DTerm): (@DBTerm Name Opid) :=
  subst_aux_bt_list2_aux e l (N.pred (NLength l)).

(*
Lemma  fold_left_right_rev:
  ∀ (A B : Type) (f : A → B → B) (l : list A) (i : B),
  fold_right f i l = fold_left (λ (x : B) (y : A), f y x) (rev l) i.
Proof.
  intros.
  rewrite <- (rev_involutive l) at 1.
  apply fold_left_rev_right.
Qed.

*)
(*
Lemma subst_aux_list_same_aux  (l:list DTerm):
let len := NLength l in
(forall (e:DTerm), 
  fvars_below len e
  -> subst_aux_list e l = subst_aux_list2 e l)
*
(forall (e:DBTerm), 
  fvars_below_bt len e
  -> subst_aux_bt_list e l = subst_aux_bt_list2 e l).
simpl.
Proof.
  induction l; [tauto |].
  unfold subst_aux_list.
  unfold subst_aux_list.
  apply NTerm_BTerm_ind.
- unfold subst_aux_list. intros ? Hfb.
  rewrite fold_left_right_rev. simpl.
  SearchAbout fold_right rev. 

 intros ? Hfb. simpl.
  simpl.
*)
Local Opaque N.sub.
Local Opaque N.add.
Open Scope N_scope.
Lemma fromDB_ssubst:
  forall (v : DTerm),
  let var n names : NVar := (mkNVar (n,lookupNDef def names n)) in
  (forall (e : DTerm) (nf:N) names,
    fvars_below 1 e
    -> fromDB 1 names (subst_aux v 0 e)
       = substitution.ssubst_aux 
            (fromDB 1 names e) [(var 0%N names,fromDB 0%N names v)])
  *
  (forall (e : DBTerm) names,
    fvars_below_bt 1 e
    -> fromDB_bt 1 names (subst_aux_bt v 0 e)
       = substitution.ssubst_bterm_aux 
            (fromDB_bt 1 names e) [(var 0 names,fromDB 0 names v)]).
Proof using.
  intros. apply NTerm_BTerm_ind; unfold fvarsProp.
- intros ? ? ? Hfb. simpl.
  inverts Hfb.
  remember (n ?= 0) as nc. symmetry in Heqnc. destruct nc.
  + rewrite N.compare_eq_iff in Heqnc. subst. unfold var.
    assert (1 - 0 - 1 = 0)%N as Heq by lia.
    rewrite Heq.
    autorewrite with SquiggleEq. admit (* alpha equal *).
  + rewrite N.compare_lt_iff in Heqnc. lia.
  + rewrite N.compare_gt_iff in Heqnc. lia.
- admit.
- intros ? ? ? ? Hfb. simpl. unfold fromDB_bt. simpl.
  f_equal;[]. unfold var.
  rewrite (fun v vars => proj2 (assert_memvar_false v vars));[| admit].
  SearchAbout memvar false.

Lemma fromDB_ssubst:
  forall (v : DTerm),
  let var n names : NVar := (mkNVar (n,lookupNDef def names n)) in
(* exp_wf 0 ls : not needed for proof, but needed for sbst to be meaningful *)
  (forall (e : DTerm) (nf:N) names, (* ns cant be 0 because it increased during recursion *)
    fvars_below nf e
    -> fromDB (nf -1)%N names (subst_aux v (nf -1)%N e)
       = substitution.ssubst_aux 
            (fromDB nf names e) [(var 0%N names,fromDB 0%N names v)])
  *
  (forall (e : DBTerm) (nf ns:N) names,
    fvars_below_bt nf e
    -> fromDB_bt nf names (subst_aux_bt v ns e)
       = substitution.ssubst_bterm_aux 
            (fromDB_bt nf names e) [(var (nf - ns - 1)%N names,fromDB nf names v)]).
Proof using.
  intros. apply NTerm_BTerm_ind; unfold fvarsProp.
- intros ? ? ? Hfb. simpl.
  inverts Hfb.
  remember (n ?= nf -1) as nc. symmetry in Heqnc. destruct nc.
  + rewrite N.compare_eq_iff in Heqnc. subst. unfold var.
    assert (nf - (nf - 1) - 1 = 0)%N as Heq by lia.
    rewrite Heq.
    autorewrite with SquiggleEq. admit. (* alpha *)
  + rewrite N.compare_lt_iff in Heqnc. unfold fromDB. simpl.
    rewrite not_eq_beq_var_false; auto.
    *  
 unfold var.
    intros Hc. apply (f_equal getId) in Hc.
    repeat rewrite getIdCorr in Hc.
    assert (ns < nf) by admit. lia.
  + rewrite N.compare_gt_iff in Heqnc. unfold fromDB. simpl.
    rewrite not_eq_beq_var_false; auto. unfold var.
    intros Hc. apply (f_equal getId) in Hc.
    repeat rewrite getIdCorr in Hc.
SearchAbout beq_var false.
    rewrite .


End DBToNamed. 




