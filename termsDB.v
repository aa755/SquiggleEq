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
Require Import Nsatz.
Require Import Psatz.
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

Lemma NLength_length {A:Type} (lv: list A) : 
  N.to_nat (NLength lv)
  = length lv.
Proof using.
  unfold NLength.
  lia.
Qed.

Hint Rewrite @NLength_length : list.
Hint Rewrite @NLength_length : SquiggleEq.


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


Fixpoint binderDepth {NVar Opid:Type} (t : @DTerm NVar Opid) : nat :=
  match t with
  | vterm _ => 0
  | oterm op bterms => (maxl (map (@binderDepth_bt NVar _) bterms))
  end
 with binderDepth_bt {NVar Opid:Type} (bt: @DBTerm NVar Opid) :nat :=
  match bt with
  | bterm lv nt => length lv +  @binderDepth NVar Opid nt
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
  Proof using.
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
  Proof using.
    intros. unfold lookupNDef, insertN. f_equal. destruct p.
    apply pmap_lookup_insert_neq. intros Hc.
    apply injectiveNsuccpos in Hc. contradiction.
  Qed.

  (* move to a pmap file? *)
  Lemma lookupNDef_insert_eq {T}
  : ∀ (m : pmap T) (def : T) (p : N*T),
        lookupNDef def (insertN m p) (fst p) = snd p.
  Proof using.
    intros.  unfold lookupNDef, insertN.
    destruct p. simpl. rewrite pmap_lookup_insert_eq.
    refl.
  Qed.

  Lemma lookupNDef_inserts_neq {T}
  : ∀ (k : N)  (def : T) (p : list (N*T)) (m : pmap T),
      disjoint (map fst p) [k] →
        lookupNDef def (insertNs m p) k = lookupNDef def m k.
  Proof using.
    intros ? ? ?. induction p;[reflexivity| intros ? Hd].
    simpl in *. apply disjoint_cons_l in Hd.
    rewrite IHp;[| tauto].
    apply lookupNDef_insert_neq; auto. simpl in *.
    rewrite N.eq_sym_iff in Hd. tauto.
  Qed.

  Lemma lookupNDef_inserts_neq_seq {T}
  : ∀ (k : N)  (def : T) (m : pmap T) len lv n,
  k < n →
  lookupNDef def (insertNs m (combine (seq N.succ n len) lv)) k
  = lookupNDef def m k.
  Proof using.
    intros. apply lookupNDef_inserts_neq.
    intros  ? Hin Hinc.
    apply in_single_iff in Hinc. subst.
    apply in_map_iff in Hin. exrepnd. subst.
    simpl. apply in_combine in Hin1. repnd.
    apply in_seq_Nplus in Hin0.
    repnd. simpl in *. lia.
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


Lemma mkNVarInj1 : forall i1 i2 n1 n2,
  i1 <> i2
  -> mkNVar (i1, n1) ≠ mkNVar (i2, n2).
Proof using getId getIdCorr.
  intros ? ? ? ? Heq.
  intros Hc. apply (f_equal getId) in Hc.
  repeat rewrite getIdCorr in Hc.
  contradiction.
Qed.

Local Opaque N.sub.
Local Opaque N.add.
Open Scope N_scope.

Lemma InMkVarCombine : forall i n li ln,
length li = length ln
-> LIn (mkNVar (i, n)) (map mkNVar (combine li ln))
-> LIn i li.
Proof using getIdCorr getId.
  intros ? ? ? ? Hl Hin.
  apply in_map_iff in Hin.
  exrepnd. apply (f_equal getId) in Hin0.
  repeat rewrite getIdCorr in Hin0. subst.
  eapply in_combine_l; eauto.
Qed.

Lemma InMkVarCombine2 : forall i n li ln,
length li = length ln
-> ¬ LIn i li
-> ¬ LIn (mkNVar (i, n)) (map mkNVar (combine li ln)).
Proof using getIdCorr getId.
  intros ? ? ? ? Hl Hin Hc. apply InMkVarCombine in Hc; auto.
Qed.


Lemma InMkVarCombine3 : forall a li ln,
length li = length ln
-> LIn a (map mkNVar (combine li ln))
-> LIn (getId a) li.
Proof using getIdCorr getId.
  intros ? ? ? Hl Hin.
  apply in_map_iff in Hin. exrepnd. subst.
  apply in_combine_l in Hin1.
  rewrite getIdCorr. assumption.
Qed.

Let fvarsProp (n:N) names (vars : list NVar): Prop := 
lforall
(fun v => 
let id := (getId v) in
  (id <  n)%N 
  /\ v = mkNVar (id,(lookupNDef def names id))
) vars.



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
    rewrite lookupNDef_inserts_neq_seq; auto.
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

Let bvarsProp (n:N) (md:nat) (vars : list NVar): Prop := 
lforall
(fun v => 
let id := (getId v) in
  (n <= id < n + N.of_nat md)%N
) vars.

Lemma fromDB_bvars: 
  (forall (s : DTerm) (n:N) names, 
    bvarsProp n (binderDepth s) (@bound_vars _ _ Opid (fromDB n names s)))
  *
  (forall (s : DBTerm) (n:N) names, 
    bvarsProp n (binderDepth_bt s) (@bound_vars_bterm _ _ Opid (fromDB_bt n names s))).
Proof using getIdCorr.
  clear fvarsProp.
  apply NTerm_BTerm_ind; unfold bvarsProp.
- intros n nv ? ? Hin. simpl in Hin. contradiction.
- intros ? ? Hind n  ? ? Hin.
  simpl in *. rewrite flat_map_map in Hin.
  apply in_flat_map in Hin.
  exrepnd. unfold compose in *. simpl in *.
  apply Hind in Hin0; eauto.
  dands; [tauto | ]. apply proj2 in Hin0.
  apply (in_map binderDepth_bt) in Hin1.
  apply maxl_prop in Hin1. lia.
- intros ? ? Hind n ? ? Hin.
  simpl in *.
  apply in_app_or in Hin.
  dorn Hin.
  + apply InMkVarCombine3 in Hin;[| apply seq_length].
    rewrite in_seq_Nplus in Hin. lia.
  + apply Hind in Hin. clear Hind. lia.
Qed.


Lemma fromDB_all_vars: forall (s : DTerm) (n:N),
  fvars_below n s
  -> forall names, 
  lforall 
    (fun v => getId v < n + N.of_nat (binderDepth s)) 
    (@all_vars _ _ Opid (fromDB n names s)).
Proof using getIdCorr.
  intros. intros ? Hin.
  apply in_app_or in Hin.
  dorn Hin.
- apply (fst fromDB_fvars) in Hin; trivial;[].
  simpl in *. repnd. rewrite Hin.
  rewrite getIdCorr.
  lia.
- apply (fst fromDB_bvars) in Hin; trivial;[].
  simpl in *. repnd. tauto.
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


Require Import alphaeq.

Infix "≡" := alpha_eq (at level 100).

Open Scope program_scope.
Infix "∘≡" := alpha_eq_bterm (at level 100).

Let var names n : NVar := (mkNVar (n,lookupNDef def names n)).

(*
Lemma fromDBHigherAlpha : 
(forall v (n1 n2 : N) names1 names2,
fvars_below 0 v
-> fromDB n2 names2 v
   ≡ fromDB n1 names1 v)
*
(forall v (n1 n2 : N) names1 names2,
fvars_below_bt 0 v
-> fromDB_bt n2 names2 v
   ∘≡ fromDB_bt n1 names1 v).
Proof.
  clear fvarsProp.
  apply NTerm_BTerm_ind.
- intros. inverts H. lia.
- admit.
- intros.  inverts H0. unfold fromDB_bt.
  simpl.
*)

Definition NbinderDepth (v:@DTerm Name Opid) := N.of_nat (binderDepth v).

(* comes up again and again *)
Lemma lengthMapCombineSeq n2 lv:
length (map mkNVar (combine (seq N.succ n2 (length lv)) lv)) = length lv.
Proof using.
  repeat rewrite map_length, length_combine_eq; 
    repeat rewrite seq_length; refl.
Qed.

Lemma getIdMkVar x:
getId (mkNVar x) = fst x.
Proof using getId getIdCorr.
  destruct x. simpl.
  apply getIdCorr.
Qed.


Lemma mapGetIdMkVar  {T} lvn f:
(map (λ x : T, getId (mkNVar (f x))) lvn)
=(map (λ x : T, fst (f x)) lvn).
Proof using getId getIdCorr.
  intros.
  Fail rewrite getIdMkVar.
  Fail setoid_rewrite getIdMkVar.
  apply map_ext.
  intros.
  rewrite getIdMkVar. refl.
Qed.


(* Move to list.v *)
  Lemma seq_NoDup len start : NoDup (seq N.succ start len).
  Proof using getIdCorr getId.
    clear.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq_Nplus. intros (H,_).
    lia.
  Qed.

  Lemma mapGetIdMapMkVarCombine n1 lv:
    (map getId (map mkNVar (combine (seq N.succ n1 (length lv)) lv)))
    = (seq N.succ n1 (length lv)).
  Proof using getIdCorr.
    rewrite map_map. unfold compose. simpl.
    rewrite mapGetIdMkVar.
    rewrite <- combine_map_fst2;[| rewrite seq_length; refl].
    refl.
  Qed.
    


Lemma NoDupMapCombineSeq n1 lv:
NoDup (map mkNVar (combine (seq N.succ n1 (length lv)) lv)).
Proof using getId getIdCorr.
  apply (NoDup_map_inv getId).
  rewrite map_map. unfold compose. simpl.
  rewrite mapGetIdMkVar.
  rewrite <- combine_map_fst2;[| rewrite seq_length; refl].
  apply seq_NoDup.
Qed.

(* Move to list.v *)
Lemma flat_map_single {A B:Type} (f: A->B) (l:list A) :
flat_map (fun x => [f x]) l
= map f l.
Proof using.
  induction l;auto.
Qed.


Lemma fromDBHigherAlphaAux : 
let vr n1 n2 names1 names2 nf :=
 map 
    (fun n => (var names2 (n2+n-nf), terms.vterm (var names1 (n1+n-nf))))
    (seq N.succ 0 (N.to_nat nf)) in
(forall v (nf n1 n2 : N) names1 names2,
fvars_below nf v
-> n2+ N.of_nat (binderDepth v) +  nf <= n1
-> nf <= n2
-> ssubst_aux (fromDB n2 names2 v) (vr n1 n2 names1 names2 nf)
   ≡ fromDB n1 names1 v) *

(forall v (nf n1 n2 : N) names1 names2,
fvars_below_bt nf v
-> n2+ N.of_nat (binderDepth_bt v) +  nf <= n1
-> nf <= n2
-> ssubst_bterm_aux (fromDB_bt n2 names2 v) (vr n1 n2 names1 names2 nf)
   ∘≡ fromDB_bt n1 names1 v)
.
Proof using.
  intro.
  apply NTerm_BTerm_ind.
- intros ? ? ? ? ? ? Hfb H1le H2le. simpl.
  invertsn Hfb. simpl.
  dsub_find sss; symmetry in Heqsss.
  + apply sub_find_some in Heqsss.
    unfold vr in Heqsss.
    apply List.in_map_iff in Heqsss.
    exrepnd. rewrite in_seq_Nplus in Heqsss0.
    rewrite Nnat.N2Nat.id in Heqsss0.
    unfold var in Heqsss1. pose proof Heqsss1 as Hs.
    apply (f_equal fst) in Hs.
    apply (f_equal getId) in Hs.
    simpl in Hs.
    repeat rewrite getIdCorr in Hs.
    repnd.
    assert (x=nf-n-1) by lia. subst.
    inverts Heqsss1. unfold fromDB. simpl.
    replace ((n1 + (nf - n - 1) - nf)) with (n1-n-1) by lia.
    refl.
  + provefalse. apply sub_find_none2 in Heqsss.
    apply Heqsss. unfold vr, dom_sub, lmap.dom_lmap, var.
    rewrite map_map. unfold compose. simpl.
    apply List.in_map_iff.
    exists (nf - n - 1).
    rewrite in_seq_Nplus.
    replace ((n2 + (nf - n - 1) - nf)) with (n2-n-1) by lia.
    dands; trivial; lia.

- intros ? ? Hind ? ?  ? ? ? Hfb H1le H2le.  unfold fromDB. simpl.
  repeat rewrite map_map.
  apply alpha_eq_map_bt.
  unfold compose. simpl in *.
  invertsn Hfb.
  intros ? Hin. apply Hind; auto.
  apply (in_map binderDepth_bt) in Hin.
  apply maxl_prop in Hin. lia.

- intros ? ? Hind ? ? ? ? ? Hfb H1le H2le.
  unfold fromDB_bt.
  invertsn Hfb. simpl in H1le.
  fold (@NLength Name lv).
  pose proof Hfb as Hfbb.
  Local Opaque var. simpl.
  apply Hind with 
    (names1:= insertNs names1 (combine (seq N.succ n1 (length lv)) lv))
    (names2:= insertNs names2 (combine (seq N.succ n2 (length lv)) lv))
    (n1:= n1 + NLength lv)
    (n2:= n2 + NLength lv)
    in Hfb; unfold NLength; try lia;[].
  clear Hind.
  simpl.
  unfold fromDB in Hfb.
  Fail Fail rewrite <- Hfb. (* we can rewrite here if we want *)
  rewrite sub_filter_disjoint1.
  Focus 2.
    unfold vr. unfold dom_sub, lmap.dom_lmap.
    rewrite map_map. unfold compose.
    Local Transparent var. simpl. unfold var.
    apply disjoint_map with (f:= getId).
    rewrite mapGetIdMapMkVarCombine.
    repeat rewrite map_map. unfold compose.
    rewrite mapGetIdMkVar. simpl.
    intros ? Hin Hinc. rewrite in_seq_Nplus in Hinc.
    apply in_map_iff in Hin. exrepnd.
    rewrite in_seq_Nplus in Hin1. lia.

  fold (NLength lv).
  unfold vr.
  unfold vr in Hfb.
  rewrite Nnat.N2Nat.inj_add in Hfb.
  rewrite NLength_length in Hfb.
  rewrite plus_comm in Hfb.
  rewrite Nseq_add in Hfb.
  do 1 rewrite Nnat.N2Nat.id in Hfb.
  rewrite N.add_0_l in Hfb.
  assert (forall k n, (k + NLength lv + n - (NLength lv + nf))
          = k+n-nf) as Heq by (intros;lia).
  erewrite map_ext in Hfb;[| intros; do 2 rewrite Heq; refl].
  rewrite map_app in Hfb.
  apply prove_alpha_bterm3;
    [ repeat rewrite lengthMapCombineSeq; refl
      | apply NoDupMapCombineSeq
      | 
      |
    ].
  + clear Hfb.
    apply (disjoint_map getId).
    rewrite mapGetIdMapMkVarCombine.
    intros ? Hin Hinc.
    rewrite in_seq_Nplus in Hinc.
    apply in_map_iff in Hin.
    exrepnd.
    apply allvars_ssubst_aux in Hin1.
    simpl in Hin1.
    rewrite N.add_comm in Hfbb.
    dorn Hin1.
    * apply fromDB_all_vars in Hin1;[| admit (*fvars_below mono*)]. subst.
      unfold NLength in Hin1.
      lia.
    * exrepnd. subst. clear Hin3.
      apply in_map_iff in Hin2.
      exrepnd. inverts Hin0.
      rewrite in_seq_Nplus in Hin2.
      unfold var in Hin1.
      apply (in_map getId) in Hin1.
      simpl in Hin1. rewrite getIdCorr in Hin1.
      rewrite or_false_r in Hin1.
      lia.
  + rewrite (fst ssubst_aux_app_simpl_nb).
    * admit.
    * setoid_rewrite disjoint_sub_as_flat_map.
      unfold range. repeat rewrite flat_map_map.
      unfold compose. simpl.
      apply (disjoint_map getId).
      rewrite flat_map_single. rewrite map_map.
      unfold compose. simpl. unfold var.
      rewrite mapGetIdMkVar. simpl.
      intros ? Hin Hinc.
      apply in_map_iff in Hin. exrepnd.
      subst. apply in_map_iff in Hinc. exrepnd.
      apply fromDB_bvars in Hinc1. exrepnd. subst.
      clear Hfb.
      rewrite in_seq_Nplus in Hin1. subst.
      unfold NLength in *.
      lia.
 
  Focus 4.
  Focus 4.
    simpl. apply disjoint_bv_vars.
  (* need (n2 + binderDepth nt +  (NLength lv) <= n1) *)
    admit. 
  Focus 3.
    simpl. (* need (n2 + binderDepth nt +  (NLength lv)  <= n1 -nf) *)
    admit.
  Focus 2.
    unfold range. repeat rewrite flat_map_map.
    unfold compose. simpl.
    admit. (* easy : flat map of nil is nil *)
   (* need (n2 + NLength lv  <= n1 -nf)  for ssubst_sub to be identity *)
    admit.
  Focus 3.
    (* need (n2 + binderDepth nt +  (NLength lv)  <= n1 -nf),
      the vars coming from substitution are already disjoint *)
    admit.


  admit (* easy *).

SearchAbout disjoint_bv_sub var_ren.
  SearchAbout alpha_eq_bterm.
  SearchAbout ssubst app.
  SearchAbout ssubst_aux all_vars.
  SearchAbout ssubst_aux app.

 (* add this assumption to the statement *)

    (* the substitution in Hfb has more pairs. split it into 2 parts,
      one of which has size (length lv). use it for al_term with chained
      substitutions with common middle.
      see alphaeq.change_bvars_alpha_spec_aux for an example,
      or other lemmas in alphaeq.v whose conclusion is alpha equality
      but dont have any alpha equality hypotheses. *)
 
Admitted.
SearchAbout alpha_eq_bterm var_ren.

Lemma fromDBHigherAlpha : forall v (n1 n2 : N) names1 names2,
fvars_below 0 v
-> fromDB n2 names2 v
   ≡ fromDB n1 names1 v.
Proof.
  intros ? ? ? ? ? Hfb.
  pose proof (fst fromDBHigherAlphaAux v 0 
    ((N.max n1 n2)+NbinderDepth v) n1 names2 names1 Hfb)  as H1b.
  simpl in H1b.
  rewrite ssubst_aux_nil in H1b.
  unfold NbinderDepth in H1b. simpl in *.
  rewrite H1b; try lia;[].

  symmetry. clear H1b.
  (* do the same on the other side *)
  pose proof (fst fromDBHigherAlphaAux v 0 
    ((N.max n1 n2)+NbinderDepth v) n2 names2 names2 Hfb)  as H1b.
  simpl in H1b.
  rewrite ssubst_aux_nil in H1b.
  unfold NbinderDepth in H1b. simpl in *.
  rewrite H1b; try lia;[].
  refl.
Qed.


Lemma fromDB_ssubst:
  forall (v : DTerm),
  fvars_below 0 v
  ->
  (forall (e : DTerm) (nf:N) names,
    fvars_below (1+nf) e
    -> fromDB (1+nf) names (subst_aux v nf e)
       ≡
       substitution.ssubst_aux 
            (fromDB (1+nf) names e) [(var names 0,fromDB (1+nf) names v)])
  *
  (forall (e : DBTerm) (nf:N) names,
    fvars_below_bt (1+nf) e
    -> fromDB_bt (1+nf) names (subst_aux_bt v nf e)
       ∘≡ substitution.ssubst_bterm_aux 
            (fromDB_bt (1+nf) names e) [(var names 0,fromDB (1+nf) names v)]).
Proof using gts getIdCorr getId fvarsProp deqo.
  intros ? H0fb. intros. apply NTerm_BTerm_ind; unfold fvarsProp.
- intros ? ? ? Hfb. simpl.
  inverts Hfb.
  remember (n ?= nf) as nc. symmetry in Heqnc. destruct nc.
  + rewrite N.compare_eq_iff in Heqnc. subst.
    replace (1 + nf - nf - 1) with 0  by lia.
    rewrite <- beq_var_refl. refl.
  + rewrite N.compare_lt_iff in Heqnc.
    unfold fromDB. simpl.
    replace (1 + nf - n - 1)  with (nf -n) by lia.
    rewrite not_eq_beq_var_false;[refl|].
    unfold var. apply mkNVarInj1. lia. 
  + rewrite N.compare_gt_iff in Heqnc. lia.
- intros ? ? Hind ? ? Hfb. unfold fromDB. simpl.
  repeat rewrite map_map.
  apply alpha_eq_map_bt.
   unfold compose. simpl.
  invertsn Hfb.
(* info eauto : *)
  intros ? Hee0.
  apply Hind.
   exact Hee0.
   apply Hfb.
    exact Hee0.

- intros ? ? Hind ? ? Hfb. simpl. unfold fromDB_bt. simpl.
  f_equal;[]. unfold var.
  rewrite (fun v vars => proj2 (assert_memvar_false v vars));
    [| apply InMkVarCombine2;
        [ apply seq_length | rewrite in_seq_Nplus; lia]
    ].
  rewrite <- N.add_assoc.
  unfold fromDB in Hind.
  invertsn Hfb. fold (NLength lv).
  replace (NLength lv + nf) with (nf + NLength lv) by lia.
  replace ((NLength lv + (1 + nf))) with (1 + (nf + NLength lv)) in Hfb by lia.
  rewrite Hind by assumption.
  apply alpha_eq_bterm_congr. unfold var.
  rewrite lookupNDef_inserts_neq_seq by lia.
  apply (fst subst_aux_alpha_sub). simpl.
  dands; trivial;[]. fold fromDB.
  apply fromDBHigherAlpha; auto; try lia.
Qed.


End DBToNamed.




