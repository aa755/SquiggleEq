
Require Export terms.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** Here are some handy definitions that will
    reduce the verbosity of some of our later definitions
*)

Section terms2Generic.

Context {gts : GenericTermSig}.

Definition nobnd (f:NTerm) := bterm [] f.


(** %\noindent \\*% We define similar abstractions for other [Opid]s.
    This document does not show them. As mentioned before, one can click
    at the hyperlinked filename that is closest above to open a
    webpage that shows complete contents of this file.
*)

(* begin hide *)

Lemma fold_nobnd :
  forall t, bterm [] t = nobnd t.
Proof.
  unfold nobnd; auto.
Qed.


(*
Definition mk_esquash (R : NTerm) :=
  oterm (Can NEsquash) [nobnd R].
*)

(* begin hide *)


(* Picks a variable that is not in the set of free variables of a given term *)
Definition newvar (t : NTerm) := fresh_var (free_vars t).

Fixpoint free_vars_list terms :=
  match terms with
    | [] => []
    | t :: ts => free_vars t ++ free_vars_list ts
  end.

Definition newvarlst (ts : list NTerm) := fresh_var (free_vars_list ts).

Definition newvars (n : nat) (ts : list NTerm) :=
  fresh_distinct_vars n (free_vars_list ts).

Definition newvars2 terms :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
    (v1, v2).

Definition newvars3 terms :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
    (v1, v2, v3).

Definition newvars4 terms :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
    (v1, v2, v3, v4).

Definition newvars5 terms :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
  let v5 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4]) in
    (v1, v2, v3, v4, v5).

Definition newvars6 terms :=
  let v1 := newvarlst terms in
  let v2 := newvarlst (terms ++ [mk_var v1]) in
  let v3 := newvarlst (terms ++ [mk_var v1, mk_var v2]) in
  let v4 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3]) in
  let v5 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4]) in
  let v6 := newvarlst (terms ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4, mk_var v5]) in
    (v1, v2, v3, v4, v5, v6).




(* ------ SIMPLE OPERATORS ON TERMS ------ *)

(*
Fixpoint depth (t : NTerm) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => lsum map depth_bterm bterms
  end
 with depth_bterm (lv : list NVar) (nt : NTerm) :=
  match bt with
  | bterm lv nt => depth nt
  end.
*)

End terms2Generic.


Fixpoint size {gts : GenericTermSig} (t : NTerm) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => S (addl (map size_bterm bterms))
  end
 with size_bterm {gts : GenericTermSig} (bt: BTerm) :=
  match bt with
  | bterm lv nt => size nt
  end.

Fixpoint wft {gts : GenericTermSig} (t : NTerm) : bool :=
  match t with
    | vterm _ => true
    | oterm o bts =>
      andb (beq_list eq_nat_dec (map (num_bvars) bts) (OpBindings o))
           (ball (map wftb bts))
  end
with wftb {gts : GenericTermSig} (bt : BTerm) : bool :=
  match bt with
    | bterm vars t => wft t
  end.

Section terms3Generic.

Context {gts : GenericTermSig}.

(* ------ INDUCTION ON TERMS ------ *)


Lemma size_subterm2 :
  forall (o:Opid) (lb : list BTerm) (b : BTerm) ,
    LIn b lb
    ->  size_bterm b <  size (oterm o lb).
Proof.
  simpl. induction lb; intros ? Hin; inverts Hin as; simpl; try omega.
  intros Hin. apply IHlb in Hin; omega.
Qed.

Lemma size_subterm3 :
  forall (o:Opid) (lb : list BTerm) (nt : NTerm) (lv : list NVar) ,
    LIn (bterm lv nt) lb
    ->  size nt <  size (oterm o lb).
Proof.
 introv X.
 apply size_subterm2 with (o:=o) in X. auto.
Qed.



Lemma NTerm_better_ind2 :
  forall P : NTerm -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt nt': NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt)
              -> size nt' <= size nt
              -> P nt'
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 intros P Hvar Hbt.
 assert (forall n t, size t = n -> P t) as Hass.
 Focus 2. intros. apply Hass with (n := size t) ; eauto; fail.
 
 induction n as [n Hind] using comp_ind_type.
 intros t Hsz.
 destruct t.
 apply Hvar.
 apply Hbt. introv Hin Hs.
 apply Hind with (m := size nt') ; auto.
 subst.
 assert(size nt < size (oterm o l)) by
   (apply size_subterm3 with lv ; auto).
 omega.
Qed.

Lemma NTerm_better_ind :
  forall P : NTerm -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt : NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt) -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof.
 introv Hv Hind. apply  NTerm_better_ind2; auto. 
 introv Hx. apply Hind. introv Hin. eapply Hx in Hin; eauto. 
Qed.


Tactic Notation "nterm_ind" ident(h) ident(c) :=
  induction h using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].


Lemma num_bvars_on_bterm :
  forall l n,
    num_bvars (bterm l n) = length l.
Proof.
  unfold num_bvars; simpl; sp.
Qed.



Definition wf_term t := wft t = true.

Definition wf_bterm bt := wftb bt = true.

Lemma wf_term_proof_irrelevance :
  forall t,
  forall x y : wf_term t,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition wf_term_extract :=
  fun (t : NTerm) (x : wf_term t) =>
    match x return (x = match x with
                          | eq_refl => eq_refl (wft t)
                        end)
    with
      | eq_refl => eq_refl eq_refl
    end.

(*
Definition wf_term_extract1 :=
  fun (t : NTerm) (x : wf_term t) =>
    match x in _ = b return match b with
                     | true => x = eq_refl (wft t)
                   end
    with
      | eq_refl => eq_refl eq_refl
    end.

Lemma wf_term_extract2 :
  forall t : NTerm,
  forall x : wf_term t,
    x = eq_refl (wft t).
*)

(*Lemma yyy : forall A (x : A) (pf : x = x), pf = eq_refl x.
Lemma xxx : forall t (x : wft t = true), x = eq_refl (wft t).*)

Lemma nt_wf_eq :
  forall t,
    nt_wf t <=> wf_term t.
Proof.
  unfold wf_term.
  nterm_ind t as [|o lbt ind] Case; simpl; intros.

  - Case "vterm".
    split; sp.

  - Case "oterm".
    split_iff SCase.

    + SCase "->"; intro w.
      inversion w; subst.
      allrw.
      rewrite beq_list_refl; simpl.
      trw ball_true; sp.
      alltrewrite in_map_iff; sp; subst.
      apply_in_hyp wf; destruct wf; allsimpl.
      discover; sp.

    + SCase "<-"; sp.
      remember (beq_list eq_nat_dec (map num_bvars lbt) (OpBindings o)).
      destruct b; allsimpl; sp.
      alltrewrite ball_true.
      constructor; sp.
      destruct l.
      apply_in_hyp e.
      constructor.
      apply e.
      apply_hyp.
      alltrewrite in_map_iff.
      exists (bterm l n); simpl; sp.

      remember (OpBindings o).
      clear Heql.
      revert l Heqb.
      induction lbt; allsimpl.
      destruct l; allsimpl; sp.
      destruct l; allsimpl; sp.
      destruct (eq_nat_dec (num_bvars a) n); subst; sp.
      apply cons_eq.
      apply IHlbt; sp.
      apply ind with (lv := lv); sp.
Qed.

Lemma nt_wf_implies :
  forall t, nt_wf t -> wf_term t.
Proof.
  sp; apply nt_wf_eq; sp.
Qed.

Lemma wf_term_eq :
  forall t, wf_term t <=> nt_wf t.
Proof.
  intro; generalize (nt_wf_eq t); sp.
  symm; auto.
Qed.

Lemma bt_wf_eq :
  forall bt, bt_wf bt <=> wf_bterm bt.
Proof.
  sp; split; intro w.
  inversion w; subst; unfold wf_bterm; simpl.
  fold (wf_term nt).
  apply wf_term_eq; auto.
  destruct bt; allunfold wf_bterm; allsimpl.
  fold (wf_term n) in w.
  constructor.
  apply nt_wf_eq; auto.
Qed.

(*
Inductive nt_wfb (t:NTerm) : bool :=
 match t with
 | vterm _ => true
 | bterm _ rt => nt_wfb rt
 | oterm o lnt : (eq map (num_bvars) lnt  OpBindings o).
*)

Definition closedb (t : NTerm) := nullb (free_vars(t)).
Definition closed_bt (bt : BTerm) := free_vars_bterm bt = [].


(* end hide *)
Definition isprogram_bt (bt : BTerm) := closed_bt bt # bt_wf bt.

(** Our definition [isprog] below is is logically equivalent to [isprogram],
    but unlike [isprogram], it is easy to prove that
    for any [t], all members(proofs) of [isprog t] are equal.
    An interested reader can look at the lemma
    %\coqexternalref{UIP\_dec}
    {http://coq.inria.fr/distrib/8.4pl2/stdlib/Coq.Logic.Eqdep\_dec}
    {\coqdocdefinition{UIP\_dec}}% from that standard library.
    As mentioned before, clicking on the lemma name in 
    the previous sentence should open
    the corresponding webpage of the Coq standard library.
    Instead, one can also look at the lemma [isprog_eq] below and
    safely ignore these technicalites.

*)
Definition isprog (t : NTerm) := (nullb (free_vars t) && wft t) = true.
(* begin hide *)

Definition isprog_bt (bt : BTerm) :=
  (nullb (free_vars_bterm bt) && wftb bt) = true.

Definition isprog_vars (vs : list NVar) (t : NTerm) :=
  (sub_vars (free_vars t) vs && wft t) = true.

Lemma closed_nt :
  forall op bts,
    closed (oterm op bts)
    <=>
    forall bt, LIn bt bts -> closed_bt bt.
Proof.
  sp; unfold closed, closed_bt; simpl; trw flat_map_empty; split; sp.
Qed.

Lemma closed_nt0 : forall o nt, closed (oterm o [bterm [] nt]) -> closed nt.
Proof.
  intros. unfold closed in H. simpl in H. apply app_eq_nil in H. repnd.
  clears_last. rewrite remove_var_nil in H0. auto.
Qed.

Lemma closed_null_free_vars :
  forall t,
    closed t <=> null (free_vars t).
Proof.
  unfold closed; sp.
  trw null_iff_nil; sp.
Qed.

Lemma isprog_proof_irrelevance :
  forall t,
  forall x y : isprog t,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma isprog_vars_proof_irrelevance :
  forall t vs,
  forall x y : isprog_vars vs t,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.


Require Export tactics.
Lemma isprogram_eq :
  forall t,
    isprogram t <=> isprog t.
Proof.
  unfold isprog, isprogram.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    split; sp. allunfold closed; allsimpl; sp.
    compute in *. sp.

  - Case "oterm".
    split_iff SCase.

    + SCase "->".
      intros i; destruct i as [ cl wf ].
      inversion cl; subst.
      inversion wf; subst.
      repeat (rw andb_eq_true).
      rewrite fold_assert.
      allrw <- null_iff_nil.
      rw ball_map_true.
      rw assert_nullb; sp.

      rewrite fold_assert.
      rw assert_beq_list; auto.

      destruct x; allsimpl.
      fold (wf_term n).
      apply wf_term_eq.
      apply_in_hyp p; inversion p; subst; sp.

    + SCase "<-"; intros.
      repeat (allrewrite andb_true); repd.
      allrw fold_assert.
      allrw assert_nullb.
      allrw null_iff_nil.
      allrw assert_beq_list.
      allrw ball_map_true; sp.
      constructor; sp.
      apply_in_hyp p.
      destruct l; allsimpl.
      constructor.
      allfold (wf_term n).
      apply wf_term_eq; auto.
Qed.

Lemma isprogram_implies :
  forall t, isprogram t -> isprog t.
Proof.
  sp; apply isprogram_eq; sp.
Qed.

Lemma isprog_implies :
  forall t : NTerm, isprog t -> isprogram t.
Proof.
  sp; apply isprogram_eq; sp.
Qed.

(* end hide *)
Lemma isprog_eq :
  forall t, isprog t <=> isprogram t.
Proof.
  intro; symm; apply isprogram_eq; auto.
Qed.
(* begin hide *)

Lemma isprogram_bt_eq :
  forall bt,
    isprogram_bt bt <=> isprog_bt bt.
Proof.
  intro; unfold isprogram_bt, isprog_bt, closed_bt; split; sp.
  allrw; simpl.
  fold (wf_bterm bt).
  apply bt_wf_eq; auto.
  alltrewrite andb_eq_true; sp.
  allrewrite fold_assert.
  alltrewrite assert_nullb.
  alltrewrite null_iff_nil; sp.
  destruct bt; constructor.
  alltrewrite andb_eq_true; sp; allsimpl.
  allfold (wf_term n).
  apply nt_wf_eq; auto.
Qed.

Lemma isprog_vars_eq :
  forall t vs,
    isprog_vars vs t <=> subvars (free_vars t) vs # nt_wf t.
Proof.
  unfold isprog_vars; sp.
  rw andb_eq_true.
  rw nt_wf_eq; sp.
Qed.

Lemma isprog_vars_if_isprog :
  forall vs t, isprog t -> isprog_vars vs t.
Proof.
  introv ip.
  rw isprog_vars_eq.
  rw isprog_eq in ip.
  destruct ip; sp.
  allunfold closed; allrw; sp.
Qed.

Lemma isprog_vars_app_l :
  forall t vs1 vs2,
    isprog_vars vs2 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof.
  sp; alltrewrite isprog_vars_eq; sp.
  alltrewrite subvars_eq.
  apply subset_app_l; sp.
Qed.

Definition areprograms ts := forall t, LIn t ts -> isprogram t.

Lemma areprograms_nil : areprograms [].
Proof.
  unfold areprograms; simpl; sp.
Qed.

Lemma areprograms_snoc :
  forall t ts,
    areprograms (snoc ts t) <=> areprograms ts # isprogram t.
Proof.
  unfold areprograms; sp; split; sp; try (apply_hyp; rw in_snoc; sp).
  alltrewrite in_snoc; sp; subst; sp.
Qed.

Lemma areprograms_cons :
  forall t ts, areprograms (t :: ts) <=> isprogram t # areprograms ts.
Proof.
  unfold areprograms; sp; simpl; split; sp; subst; sp.
Qed.

Lemma areprograms_app :
  forall ts1 ts2,
    areprograms (ts1 ++ ts2) <=> areprograms ts1 # areprograms ts2.
Proof.
  unfold areprograms; sp; split; sp.
  apply_hyp; rw in_app_iff; sp.
  apply_hyp; rw in_app_iff; sp.
  alltrewrite in_app_iff; sp.
Qed.

Lemma isprogram_vterm :
  forall v, isprogram (vterm v) <=> False.
Proof.
  unfold isprogram, closed; simpl; sp; split; sp.
Qed.

(*
Ltac repnd :=
  repeat match goal with
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
         end.
*)

Theorem isprogram_ot_iff :
  forall o bts,
    isprogram (oterm o bts)
    <=>
    (map num_bvars bts = OpBindings o
     # forall bt, LIn bt bts -> isprogram_bt bt).
Proof.
  intros. sp_iff Case.

  - Case "->".
    intros Hisp.
    unfold isprogram in Hisp. repnd.
    inverts Hisp0 as Hflat. inverts Hisp.
    split;auto. intros bt Hin.
    unfold isprogram_bt.
    rw flat_map_empty in Hflat.
    apply_in_hyp p; sp.

  - Case "<-".
    intros eq; destruct eq as [Hmap Hstclose].
    unfold isprogram, closed.

    split; try (constructor); auto;
    try (simpl; apply flat_map_empty);
    intros a ain;
    apply Hstclose in ain; inversion ain; sp.
Qed.

Theorem nt_wf_ot_implies :
  forall lv o nt1 bts,
    nt_wf (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof. intros ? ? ? ? Hwf Hin. inverts Hwf as Hwf Hmap.
  assert (bt_wf (bterm lv nt1)) as Hbf by (apply Hwf; auto).
  inverts Hbf. auto.
Qed.


Lemma newvar_prop :
  forall t, ! LIn (newvar t) (free_vars t).
Proof.
  unfold newvar; sp.
  allapply fresh_var_not_in; sp.
Qed.

Lemma newvar_not_in_free_vars :
  forall t,
    ! LIn nvarx (free_vars t)
    -> newvar t = nvarx.
Proof.
  sp.
  unfold newvar.
  apply fresh_var_nvarx; sp.
Qed.

Lemma newvar_prog :
  forall t,
    isprog t
    -> newvar t = nvarx.
Proof.
  sp.
  unfold newvar.
  apply isprog_eq in H.
  inversion H.
  unfold closed in H0.
  rewrite H0; sp.
Qed.



(** A value is a program with a canonical operator *)
Inductive isvalue : NTerm -> [univ] :=
  | isvl : forall (c : CanonicalOp) (bts : list BTerm ),
           isprogram (oterm (Can c) bts)
           -> isvalue (oterm (Can c) bts).


Inductive isovalue : NTerm -> Prop :=
  | isovl : forall (c : CanonicalOp) (bts : list BTerm),
              nt_wf (oterm (Can c) bts)
              -> isovalue (oterm (Can c) bts).

Lemma isvalue_closed :
  forall t, isvalue t -> closed t.
Proof.
  introv isv; inversion isv.
  allunfold isprogram; sp.
  unfold isprogram in *.
  tauto.
Qed.

Lemma isvalue_program :
  forall t, isvalue t -> isprogram t.
Proof.
  introv isv; inversion isv; sp.
Qed.

(* ------ programs ------ *)

Definition WTerm  := { t : NTerm  | wf_term t }.
Definition WBTerm := { bt : BTerm | wf_bterm bt }.

(* end hide *)

(*
  (* first of all, isprog is NOT a boolean. also, the reader will
    be left wondering what UIP_dec is*)

  where [isprog] is the Boolean version of [isprogram]
  (using a Boolean version of [isprogram] makes it easy to prove that
  closed terms are equal by proving that the underlying [NTerm]s are
  equals using [UIP_dec]).  

*)

(**

  The [CTerm] type below is useful in compactly stating definitions
  that are only meaningful for closed terms. A [CTerm] is a pair
  of an [NTerm] [t] and a proof that [t] is closed.
  This [CTerm] type will be handy in compactly 
  defining the Nuprl type system where types are defined as partial
  equivalence relations on closed terms.
  
*)

Definition CTerm  := { t : NTerm  | isprog t }.
Definition get_cterm (t : CTerm) := let (a,_) := t in a.

(* begin hide *)

Definition BCTerm := { bt : BTerm | isprog_bt bt }.

(* end hide *)

(**

  We also define a type of terms that specifies what are the possible
  free variables of its inhabitants.  A term is a [(CVTerm vs)] term
  if the set of its free variables is a subset of [vs].  This type is
  also useful to define the Nuprl type system.  For example, to define
  a closed family of types such as a closed function type of the form
  $\NUPRLfunction{x}{A}{\NUPRLsuba{B}{z}{x}}$, $A$ has to be closed
  and the free variables of $B$ can only be $z$.

*)

Definition CVTerm (vs : list NVar) := { t : NTerm | isprog_vars vs t }.

(* begin hide *)

Definition CVTerm3 := forall a b c, CVTerm [a;b;c].


Definition mk_cvterm (vs : list NVar) (t : NTerm) (p : isprog_vars vs t) :=
  exist (isprog_vars vs) t p.



Definition get_wterm (t : WTerm) := let (a,_) := t in a.
Definition get_cvterm (vs : list NVar) (t : CVTerm vs) := let (a,_) := t in a.
Definition get_bcterm (bt : BCTerm) := let (a,_) := bt in a.

Definition selectbt (bts: list BTerm) (n:nat) : BTerm :=
  nth n bts (bterm [] (vterm nvarx)).

Definition isnoncan (t: NTerm):=
match t with
| vterm _ => False
| oterm o _ => match o with
               | Can _ => False
               | NCan _ => True
               end
end.
Lemma wf_cterm :
  forall t, wf_term (get_cterm t).
Proof.
  introv; (  repeat match goal with
           | [ H : CTerm |- _ ] => destruct H
           | [ H : CVTerm _ |- _ ] => destruct H
         end
); simpl.
  allrw isprog_eq; unfold isprogram in *; repnd; allrw nt_wf_eq; sp.
Qed.

End terms3Generic.

Ltac irr_step :=
  match goal with
    | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_proof_irrelevance; subst
    | [ H1 : isprog_vars ?vs ?a, H2 : isprog_vars ?vs ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_vars_proof_irrelevance; subst
  end.

Ltac irr := repeat irr_step.

Ltac destruct_cterms :=
  repeat match goal with
           | [ H : CTerm |- _ ] => destruct H
           | [ H : CVTerm _ |- _ ] => destruct H
         end.

Ltac dest_cterm H :=
  let t := type of H in
  match goal with
    | [ x : CTerm |- _ ] =>
      match t with
        | context[x] => destruct x
      end
    | [ x : CVTerm _ |- _ ] =>
      match t with
        | context[x] => destruct x
      end
  end.

(** A faster version of destruct_cterms.  We avoid destructing all of them. *)
Ltac dest_cterms H := repeat (dest_cterm H).

Ltac clear_deps h :=
  repeat match goal with
           | [ H : context[h] |- _ ] => clear H
         end.
Tactic Notation "nterm_ind" ident(h) ident(c) :=
  induction h using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].


Ltac fold_terms_step :=
  match goal with
    | [ |- context[bterm [] ?x] ] => fold (nobnd x)
    | [ |- context[vterm ?v] ] => fold (mk_var v)
  end.

Ltac fold_terms := repeat fold_terms_step.


Ltac boolvar_step :=
  match goal with
    | [ |- context[beq_var ?v ?v] ] => rw <- beq_var_refl
    | [ |- context[memvar ?v ?s] ] =>
        let name := fresh "b" in
          remember (memvar v s) as name;
        match goal with
          | [ H : name = memvar v s |- _ ] =>
              symmetry in H;
              destruct name;
              [ rewrite fold_assert in H;
                  trw_h assert_memvar H;
                  simpl in H
              | trw_h not_of_assert H;
                  trw_h assert_memvar H;
                  simpl in H
              ]
        end
    | [ |- context[beq_var ?v1 ?v2] ] =>
        let name := fresh "b" in
          remember (beq_var v1 v2) as name;
        match goal with
          | [ H : name = beq_var v1 v2 |- _ ] =>
            destruct name;
              [ apply beq_var_true in H; subst
              | apply beq_var_false in H
              ]
        end
    | [ H : context[beq_var ?v ?v] |- _ ] => rw <- beq_var_refl in H
  end.

Ltac boolvar := repeat boolvar_step.
Ltac unfold_all_mk :=
       allunfold mk_var
       ;allunfold nobnd.


Hint Immediate wf_cterm : wf.
Hint Constructors isvalue.
Hint Constructors nt_wf bt_wf.

Ltac rwselectbt :=
match goal with
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite <- H1 in H2
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite H1 in H2
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n  |-  context [selectbt ?lbt ?n] ] => rewrite <- H1
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  |-  context [selectbt ?lbt ?n] ] => rewrite H1
end.

Tactic Notation "ntermd" ident(h) "as" simple_intropattern(I)  ident(c) :=
  destruct h as I;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].
Ltac prove_or := 
  try (left;cpx;fail);
  try (right;cpx;fail);
  try (left;left;cpx;fail);
  try (left;right;cpx;fail);
  try (right;left;cpx;fail);
  try (right;right;cpx;fail).

Ltac fold_selectbt :=
match goal with
[ |- context [nth ?n ?lbt (bterm [] (vterm nvarx))] ] =>
  fold (selectbt lbt n)
end.

Ltac d_isnoncan H := 
  match type of H with
    isnoncan ?t => let tlbt := fresh t "lbt" in let tnc := fresh t "nc" in
              let tt := fresh "temp" in 
              destruct t as [tt|tt tlbt];[inverts H as H; fail|];
              destruct tt as [tt|tnc]; [inverts H as H; fail|]
  end.


Section terms4Generic.

Context {gts : GenericTermSig}.

Lemma cterm_eq :
  forall t u,
    get_cterm t = get_cterm u
    -> t = u.
Proof.
  introv; destruct_cterms; simpl; sp; subst.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma cvterm_eq :
  forall vs t u,
    get_cvterm vs t = get_cvterm vs u
    -> t = u.
Proof.
  introv; destruct_cterms; simpl; sp; subst.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.



Lemma free_vars_cterm :
  forall t, free_vars (get_cterm t) = [].
Proof.
  introv; destruct_cterms; simpl.
  allrw isprog_eq; unfold isprogram in *; repnd; allrw; sp.
Qed.

Definition mk_cterm (t : NTerm) (p : isprogram t) :=
  exist isprog t (isprogram_implies t p).

Definition mk_ct (t : NTerm) (p : isprog t) := exist isprog t p.

Definition mk_wterm (t : NTerm) (p : wf_term t) := exist wf_term t p.

Definition mk_wterm' (t : NTerm) (p : nt_wf t) :=
  exist wf_term t (nt_wf_implies t p).

Definition iscvalue (t : CTerm) : Type :=
  isvalue (get_cterm t).

Lemma mk_cv_pf :
  forall vs t,
    isprog_vars vs (get_cterm t).
Proof.
  destruct t; simpl.
  rw isprog_eq in i; destruct i.
  rw isprog_vars_eq; simpl; sp.
  allunfold closed.
  allrw; sp.
Qed.

(** From a closed term, we can always make a term whose variables
 * are contained in vs: *)
Definition mk_cv (vs : list NVar) (t : CTerm) : CVTerm vs :=
  exist (isprog_vars vs) (get_cterm t) (mk_cv_pf vs t).


Lemma programs_bt_to_program :
  forall bts : list BCTerm,
  forall op,
    map (fun bt => num_bvars (get_bcterm bt)) bts = OpBindings op
    -> isprogram (oterm op (map get_bcterm bts)).
Proof.
  sp; unfold isprogram; sp.
  allrw closed_nt; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- isprogram_bt_eq in i.
  inversion i; sp.
  constructor; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- isprogram_bt_eq in i.
  inversion i; sp.
  rewrite <- H.
  rewrite map_map; unfold compose; sp.
Qed.

(* ---------------------------------------------------- *)


Definition list_rel {A} {B} (R : A -> B -> Prop) (ll : list A) (lr : list B) :=
  (length ll = length lr)
  #
  forall p1  p2 , LIn (p1, p2) (combine ll lr)
                  -> R p1 p2.

(** gets the nth element of a list of bterms. if n is out of range, it returns the variable x
*)

(* Howe defines T(L) as B_0(L) (no bterm constructor)
  and T_0(L) as closed terms of T(L)
  so, a term T_0(L) cannot have the vterm constructor
 at the root
 This a superset of T_0(L)
*)
Inductive not_vbterm: NTerm -> Type :=
  | nvbo : forall (op : Opid) (bts : list BTerm ),
           not_vbterm (oterm op bts).

(** this should not be required anymore. a closed NTerm is automatically not_vbterm. Proof below*)
Definition not_vbtermb (t : NTerm) : bool :=
  match t with
  | oterm _ _ => true
  | _ => false
  end.

Theorem closed_notvb : forall t: NTerm , (closed t) -> (not_vbterm t).
Proof.
  intros ? Hclose. destruct t.
  unfold closed in Hclose. simpl in Hclose.
  inversion Hclose. constructor.
Qed.

Theorem selectbt_in :
  forall n bts,
    n < length bts -> LIn (selectbt bts n) bts.
Proof.
  intros. unfold selectbt.
  apply nth_in; auto.
Qed.

Lemma selectbt_cons :
  forall bt bts n,
    selectbt (bt :: bts) n = if beq_nat n 0 then bt else selectbt bts (n - 1).
Proof.
  unfold selectbt; simpl; sp.
  destruct n; simpl; sp.
  destruct n; simpl; sp.
Qed.

Lemma isvalue_wf :
  forall c bts,
    isvalue (oterm (Can c) bts)
    -> map num_bvars bts = OpBindings (Can c).
Proof. intros ? ?  Hval.
 inverts Hval as Hpr. inverts Hpr as Hclose Hwf.
 inverts Hwf; auto.
Qed.


Lemma isvalue_wf2: forall c bts,
  (isvalue (oterm (Can c) bts))
  -> length bts= length(OpBindings (Can c)).
Proof. intros ? ?  Hval. apply isvalue_wf in Hval.
 (* fequalhyp H length.  why does this fail*)

 assert (length (map num_bvars bts) = length (OpBindings (Can c)))
   as Hlen by (rewrite Hval; reflexivity) .
 rewrite map_length in Hlen. auto.
Qed.


Lemma isprogram_wf3: forall o bts,
  (isprogram (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof. intros ? ?  Hprog. apply isprogram_ot_iff  in Hprog. repnd.
 intros ? Hlt.
assert(nth n (map num_bvars bts) 0= nth n (OpBindings o) 0)
  as Hnth by (rewrite Hprog0; reflexivity).
 unfold selectbt.
 instlemma (@map_nth BTerm nat num_bvars
  bts (bterm [] (vterm nvarx))) as Hmapn.
 assert((num_bvars (bterm [] (vterm nvarx))) =0).
 compute; auto . rewrite H in Hmapn. rewrite Hmapn in Hnth. auto.
Qed.

Lemma isvalue_wf3: forall o bts,
  (isvalue (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof. intros ? ?  Hval ? Hlt.
 inverts Hval as Hprog. apply isprogram_wf3 with (n:=n) in Hprog ; auto.
Qed.

Theorem var_not_prog : forall v,  (isprogram (vterm v)) -> void.
Proof.
  unfold not. intros v Hpr.
  inversion Hpr as [Hclose ?].
  unfold closed in Hclose. simpl in Hclose. inversion Hclose.
Qed.

Lemma implies_isprogram_bt :
  forall bts,
    (forall l : BTerm, LIn l bts -> bt_wf l)
    -> flat_map free_vars_bterm bts = []
    -> forall bt : BTerm, LIn bt bts -> isprogram_bt bt.
Proof.
  intros bts Hbf Hflat ? Hin.
  unfold isprogram_bt, closed_bt; split; auto.
  rw flat_map_empty in Hflat. apply Hflat; auto.
Qed.

Theorem ntbf_wf :
  forall nt, (bt_wf (bterm [] nt)) -> nt_wf nt.
Proof.
  introv Hin. inverts Hin. auto.
Qed.

Lemma implies_isprogram_bt0 :
  forall t ,
    isprogram (t)
    -> isprogram_bt (bterm [] t).
Proof.
  unfold isprogram_bt, closed_bt, isprogram, closed; simpl; sp.
Qed.

Theorem is_program_ot_bts0 :
  forall o nt,
    isprogram nt
    -> OpBindings o = [0]
    -> isprogram (oterm o [bterm [] nt]).
Proof.
  introv Hpr Hop. unfold isprogram in *. repnd.
  split;auto. unfold closed. simpl.
  rewrite app_nil_r. rewrite remove_var_nil. sp.
  constructor; sp; allsimpl; sp; subst; sp.
Qed.

Theorem is_program_ot_nth_nobnd :
  forall o nt1 bts,
    isprogram (oterm o  bts)
    -> LIn (bterm [] nt1) bts
    -> isprogram nt1.
Proof. intros ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  apply Hisp in Hin. inverts Hin as Hclose Hbf. inverts Hbf.
  unfold closed_bt in Hclose. simpl in Hclose.
  rewrite remove_var_nil in Hclose. split; auto.
Qed.

Theorem is_program_ot_fst_nobnd :
  forall o nt1 bts,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1.
Proof.
  intros ? ? ? Hisp.
  apply is_program_ot_nth_nobnd with (nt1:=nt1) in Hisp; sp.
Qed.

Theorem is_program_ot_snd_nobnd :
  forall o bt1 nt2 bts, isprogram (oterm o ((bt1)::(bterm [] nt2):: bts))
   -> isprogram nt2.
Proof. intros ? ? ? ? Hisp.
  apply is_program_ot_nth_nobnd with (nt1:=nt2) in Hisp; simpl; sp.
Qed.


Theorem is_program_ot_subst1 :
  forall o nt1 bts nt1r,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1r
    -> isprogram (oterm o ((bterm [] nt1r):: bts)).
Proof. intros ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. unfold closed in Hclos. simpl in Hclos.
    apply app_eq_nil in Hclos. repnd.  rewrite remove_var_nil in Hclos0.
    inverts Hispst as Hclosst Hispst. unfold closed in Hclosst.
    rewrite remove_var_nil. rewrite Hclosst. rewrite Hclos. split;auto.
    invertsn Hisp. constructor;auto.
    intros ? Hin. inverts Hin. constructor; auto.
    apply Hisp. right; auto.
Qed.

Theorem is_program_ot_subst2 :
  forall o bt1 nt2 bts nt2r,
    isprogram (oterm o (bt1::(bterm [] nt2):: bts))
    -> isprogram nt2r
    -> isprogram (oterm o (bt1::(bterm [] nt2r):: bts)).
Proof. intros ? ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. inverts Hispst as Hclosst Hwfst.
    allunfold closed. simpl.
    unfold closed in Hclos. allsimpl.
   simpl_vlist. rewrite Hclosst. rewrite Hclos0.
   simpl. split;auto.
   inverts Hisp as Hisp Hm. constructor;simpl; auto.
   intros ? Hin. dorn Hin;subst;auto. apply Hisp; auto.
   left; auto.
   dorn Hin; subst; auto.
   apply Hisp. right;right;auto.
Qed.


Theorem is_program_ot_nth_wf :
  forall lv o nt1 bts,
    isprogram (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof. intros ? ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  assert (isprogram_bt (bterm lv nt1)) as Hass by (apply Hisp; auto).
  inverts Hass as Hass Hbt. inversion Hbt; auto.
Qed.

Lemma combine_vars_map_sp :
  forall vars,
    combine vars (map vterm vars) = map (fun v => (v, vterm v)) vars.
Proof.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.

Lemma combine_vars_map :
  forall A,
  forall f : NVar -> A,
  forall vars,
    combine vars (map f vars) = map (fun v => (v, f v)) vars.
Proof.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.


Theorem in_selectbt: forall bt bts,  LIn bt bts ->
    {n : nat $ n < length bts # selectbt bts n = bt}.
Proof.
  intros ? ? Hin. induction bts. inverts Hin.
  invertsn Hin.
  - exists 0. split; simpl; auto. omega.
  - destruct IHbts; auto. exists (S x). repnd.
    split; simpl; try omega. auto.
Qed.

(**useful for rewriting in complicated formulae*)
Theorem ntot_wf_iff: forall o bts, nt_wf (oterm o bts)
    <=> map num_bvars bts = OpBindings o # forall n : nat,
     n < length bts -> bt_wf (selectbt bts n).
Proof. introv. sp_iff Case; introv H.
  Case "->". inverts H as Hbf Hmap. split; auto.
    introv Hlt. apply Hbf. apply selectbt_in; auto.
  Case "<-". repnd. constructor; auto.
    introv Hin. apply in_selectbt in Hin.
    exrepnd. rw <- Hin0;auto.
Qed.

(**useful for rewriting in complicated formulae*)
Theorem bt_wf_iff: forall lv nt, bt_wf (bterm lv nt)
    <=> nt_wf nt.
Proof. sp_iff Case; introv H.
  Case "->". inverts H as Hwf;  auto.
  Case "<-".  constructor; auto.
Qed.


Definition nvarxbt := bterm [] (vterm nvarx) .

Lemma wf_cvterm :
  forall vs : list NVar,
  forall t : CVTerm vs,
    wf_term (get_cvterm vs t).
Proof.
  destruct t; simpl.
  rw isprog_vars_eq in i; sp.
  rw wf_term_eq; sp.
Qed.

Lemma isprogram_get_cterm :
  forall a, isprogram (get_cterm a).
Proof.
  destruct a; sp; simpl.
  rw isprogram_eq; sp.
Qed.


Lemma oterm_eq :
  forall o1 o2 l1 l2,
    o1 = o2
    -> l1 = l2
    -> oterm o1 l1 = oterm o2 l2.
Proof.
  sp; allrw; sp.
Qed.

Lemma bterm_eq :
  forall l1 l2 n1 n2,
    l1 = l2
    -> n1 = n2
    -> bterm l1 n1 = bterm l2 n2.
Proof.
  sp; allrw; sp.
Qed.

Theorem selectbt_map : forall lbt n (f: BTerm -> BTerm) ,
  n<length lbt
  -> selectbt (map f lbt) n = f (selectbt lbt n).
Proof.
  induction lbt; introv Hlt. inverts Hlt.
  simpl. destruct n; subst. reflexivity.
  unfold selectbt in *. allsimpl.
  assert (n < (length lbt)) by omega.
  auto.
Qed.


Theorem eq_maps_bt: forall (B : Type) (f : BTerm -> B) 
  (g : BTerm -> B) (la lc : list BTerm),
  length la = length lc 
  -> (forall n : nat, n < length la 
       -> f (selectbt la n) = g (selectbt lc n)) 
  -> map f la = map g lc.
Proof. unfold selectbt. introv H2 H3. apply eq_maps2 in H3; auto. 
Qed.

Lemma vterm_inj: injective_fun vterm.
Proof.
    introv Hf. inverts Hf. auto.
Qed.

Lemma map_eq_lift_vterm:  forall lvi lvo, 
  map vterm lvi = map vterm lvo -> lvi = lvo.
Proof.
 intros.
  apply map_eq_injective with (f:=vterm); auto.
  exact vterm_inj.
Qed.

Lemma deq_nterm : Deq NTerm.
Proof.
  intros ?.
  nterm_ind1 x as [v1 | o1 lbt1 Hind] Case; intros.

  - Case "vterm".
    destruct y as [v2 | o lbt2]; [  | right; intro Hc; inverts Hc].
    destruct (deq_nvar v1 v2); subst;
    [ left; auto; fail
    | right; intro Hc; inverts Hc; sp
    ].

  - Case "oterm".
    destruct y as [v2 | o2 lbt2]; [ right; intro Hc; inverts Hc | ].
    destruct (opid_dec o1 o2); subst; [  | right; intro Hc; inverts Hc;sp].
    assert ((lbt1=lbt2) + (lbt1 <> lbt2)) as Hbt.
    Focus 2.
    dorn Hbt; subst; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    revert lbt2.
    induction lbt1.
    destruct lbt2; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    destruct lbt2;  [ right; intro Hc; inverts Hc; fail | ].
    destruct a as [lv1 nt1]. destruct b as [lv2 nt2].
    lapply (IHlbt1);
      [ | introv Hin; apply Hind with (lv:=lv); eauto; right; auto].
    intro bdec.
    destruct (bdec lbt2); subst; [  | right; intro Hc; inverts Hc;sp;fail ].
    destruct (list_eq_dec deq_nvar lv1 lv2);
      subst; [ | right; intro Hc; inverts Hc;sp;fail ].
    destruct (Hind nt1 lv2 (injL(eq_refl _) ) nt2); subst;
    [left; auto |  right; intro Hc; inverts Hc;sp ].
Defined.

Lemma lin_lift_vterm :
  forall v lv,
    LIn v lv <=> LIn (vterm v) (map vterm lv).
Proof.
  induction lv; [sp | ]. simpl.
  rw <- IHlv; split; intros hp; try (dorn hp); sp; subst; sp.
  inverts hp. sp.
Qed.


Lemma map_removevars:
forall lvi lvr,
  map vterm (remove_nvars lvi lvr)
  = diff deq_nterm (map vterm lvi) (map vterm lvr).
Proof.
  intros. apply map_diff_commute.
  introv Hc. inverts Hc. auto.
Qed.

Definition all_vars_bt bt := free_vars_bterm bt ++ bound_vars_bterm bt.

Lemma all_vars_ot : forall o lbt, all_vars (oterm o lbt) =
  flat_map all_vars_bt lbt.
Proof.
  intros. unfold all_vars. simpl. unfold all_vars_bt.
Abort. (** they are only equal as bags*)


Theorem nil_remove_nvars_iff: forall l1 l2 : list NVar,
   (remove_nvars l1 l2) = [] <=> (forall x : NVar, LIn x l2 -> LIn x l1).
Proof.
  intros. rw <- null_iff_nil. apply null_remove_nvars.
Qed.

Theorem nil_rv_single_iff: forall lv v ,
   (remove_nvars lv [v]) = [] <=> (LIn v lv).
Proof.
  intros. rw <- null_iff_nil. rw null_remove_nvars.
  split; intro Hyp.
  apply Hyp. left. auto.
  introv Hin. apply in_list1 in Hin; subst; auto.
Qed.

Theorem selectbt_eq_in:  forall lv nt lbt n,
  bterm lv nt = selectbt lbt n
  -> n < length lbt
  -> LIn (bterm lv nt) lbt.
Proof.
  introv Heq Hlt. rw Heq.
  apply selectbt_in; trivial.
Qed.

Lemma flat_map_closed_terms:
  forall lnt, lforall closed lnt
    -> flat_map free_vars lnt = [].
Proof.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. trivial.
Qed.

Lemma flat_map_progs:
  forall lnt, lforall isprogram lnt
    -> flat_map free_vars lnt = [].
Proof.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. introv Hin.
  apply Hfr in Hin. inverts Hin. auto.
Qed.

Theorem disjoint_lbt_bt :
  forall vs lbt lv nt,
    disjoint vs (flat_map bound_vars_bterm lbt)
    -> LIn (bterm lv nt) lbt
    -> disjoint vs lv.
Proof.
  introv Hink1 Hin.
  apply disjoint_sym in Hink1; rw disjoint_flat_map_l in Hink1.
  apply Hink1 in Hin.
  simpl in Hin. rw disjoint_app_l in Hin.
  repnd; apply disjoint_sym. trivial.
Qed.



Definition selectnt (n:nat) (lnt : list NTerm): NTerm :=
  nth n lnt (vterm nvarx).

Lemma deq_bterm : Deq BTerm.
Proof.
  intros btx bty. destruct btx as [lvx ntx].
  destruct bty as [lvy nty].
  destruct (deq_nterm ntx nty);
  destruct (deq_list deq_nvar lvx lvy); subst;sp;
  right; introv Heq;
  inverts Heq; cpx.
Qed.


Inductive nt_wf2 : NTerm -> [univ] :=
  | wfvt2 : forall nv : NVar, nt_wf2 (vterm nv)
  | wfot2 : forall (o : Opid) (lnt : list BTerm),
            length lnt = length (OpBindings o)
           -> (forall n, n < (length lnt) ->
                num_bvars (selectbt lnt n) = nth n (OpBindings o) 0
                # bt_wf2 (selectbt lnt n))
           -> nt_wf2 (oterm o lnt)
  with bt_wf2 : BTerm -> [univ] :=
    wfbt2 : forall (lnv : list NVar) (nt : NTerm),
           nt_wf2 nt -> bt_wf2 (bterm lnv nt).

(** mainly for convenience in proofs *)
Theorem  selectbt_in2:  forall (n : nat) (bts : list BTerm),
  n < length bts -> { bt : BTerm & (LIn bt bts # (selectbt bts n)=bt) }.
Proof.
  intros. exists (selectbt bts n).
  split;auto. apply selectbt_in; trivial.
Defined.

Lemma nt_wf_nt_wf2 : forall t, (nt_wf t) <=> (nt_wf2 t).
Proof.
    assert (0= num_bvars (bterm [] (vterm nvarx))) as XX by auto.
  nterm_ind1 t as [?| o lbt Hind] Case; split; introv Hyp; sp.
  - inverts Hyp as Hl Hyp. constructor. apply_length Hyp;sp.
    introv hlt. unfold selectbt. rw <- Hyp.
    rw XX. rw  map_nth; sp;[].
    fold (selectbt lbt n).
    pose proof (selectbt_in2 n lbt hlt) as Hbt.
    exrepnd. destruct bt as [lv nt].
    applydup Hind in Hbt1.
    rw Hbt0. constructor.
    apply Hl in Hbt1. inverts Hbt1.
    sp3.
  - inverts Hyp as Hl Hyp. constructor.
    + introv Hin. apply in_selectbt in Hin; auto;[].
      exrepnd. applydup Hyp in Hin1.
      rw Hin0 in Hin2. destruct l as [lv nt].
      constructor. exrepnd. invertsn Hin2.
      applysym selectbt_in in Hin1. rw Hin0 in Hin1.
      apply Hind in Hin1. sp3.
    + eapply (tiff_snd (eq_list2 _ 0 _ _)). rw map_length.
      split; auto;[]. introv Hlt. apply Hyp in Hlt.
      repnd. rw <- Hlt0.
      rw XX. rw  map_nth. sp.
Qed.



Definition bin_rel_nterm :=
  binrel_list  (vterm nvarx).

Theorem isprogram_ot_implies_eauto2 :
  forall o bts,
    isprogram (oterm o bts)
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n)).
Proof.
  introv Hp Hlt. apply isprogram_ot_iff in Hp.
  apply selectbt_in in Hlt. exrepnd.
  eauto with slow.
Qed.


Lemma isprogram_bt_nobnd :
  forall t ,
    isprogram_bt (bterm [] t)
    -> isprogram (t).
Proof.
  unfold isprogram_bt, closed_bt, isprogram, closed; intros ?  Hxx;  spc; allsimpl.
  match goal with
  [H: (bt_wf _) |- _ ] => inverts H
  end.
  assumption.
Qed.


Lemma free_vars_list_app :
  forall ts1 ts2,
    free_vars_list (ts1 ++ ts2)
    = free_vars_list ts1 ++ free_vars_list ts2.
Proof.
  induction ts1; simpl; sp.
  rw IHts1; simpl.
  rw app_assoc; sp.
Qed.



Lemma isprog_ntwf_eauto : forall t, isprogram t -> nt_wf t.
Proof. unfold isprogram. spc.
Qed.

Theorem isprogram_ot_if_eauto :
  forall o bts,
    map num_bvars bts = OpBindings o
    -> (forall bt, LIn bt bts -> isprogram_bt bt)
    -> isprogram (oterm o bts).
Proof.
 intros. apply isprogram_ot_iff;spc.
Qed.


Lemma isprogramd :
  forall v, isprogram v
  -> {o : Opid $ {lbt : list BTerm $ v = oterm o lbt}}.
Proof.
  introv Hpr.
  invertsn Hpr.
  destruct v; inverts Hpr.
  eexists; eexists ; eauto.
Qed.


Lemma isprogram_noncan:
  forall v, isprogram v
  -> (isvalue v [+] isnoncan v).
Proof.
  introv Hp. applydup isprogramd in Hp.
  exrepnd. subst.
  destruct o; cpx.
Qed.

Lemma fold_combine : forall {A B} (v:A) (t:B), 
  [(v,t)] = (combine [v] [t]).
Proof.
  intros. simpl. auto.
Qed.

Lemma nvarx_nvary : nvarx <> nvary.
Proof.
  allunfold nvarx.
  allunfold nvary.
  introv Hinc.
  inverts Hinc.
Qed.


Lemma noncan_not_value : forall e,
  isnoncan e
  -> isvalue e
  -> False.
Proof.
  introv Hisnc Hisv.
  destruct e as [?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
  inverts Hisv.
Qed.

Theorem isprogram_ot_if_eauto2 :
  forall o bts,
    map num_bvars bts = OpBindings o
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n))
    -> isprogram (oterm o bts).
Proof.
  introv Hn Hp. apply isprogram_ot_iff; dands; spcf.
  introv Hin. apply in_selectbt in Hin. exrepnd.
  eauto with slow.
  rw <- Hin0.
  eauto with slow.  
Qed.


Lemma newvars5_prop :
  forall v1 v2 v3 v4 v5 terms,
    (v1, v2, v3, v4, v5) = newvars5 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms ++ [v1])
       # !LIn v3 (free_vars_list terms ++ [v1, v2])
       # !LIn v4 (free_vars_list terms ++ [v1, v2, v3])
       # !LIn v5 (free_vars_list terms ++ [v1, v2, v3, v4]).
Proof.
  introv eq.
  unfold newvars5 in eq; cpx.
  unfold newvarlst; simpl; allrw free_vars_list_app; simpl.
  dands; apply fresh_var_not_in.
Qed.

Lemma newvars5_prop2 :
  forall v1 v2 v3 v4 v5 terms,
    (v1, v2, v3, v4, v5) = newvars5 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !LIn v3 (free_vars_list terms)
       # !LIn v4 (free_vars_list terms)
       # !LIn v5 (free_vars_list terms)
       # !v1 = v2
       # !v1 = v3
       # !v1 = v4
       # !v1 = v5
       # !v2 = v3
       # !v2 = v4
       # !v2 = v5
       # !v3 = v4
       # !v3 = v5
       # !v4 = v5.
Proof.
  introv eq.
  apply newvars5_prop in eq; repnd.
  allrw in_app_iff; allsimpl.
  repeat (apply not_over_or in eq; repnd).
  repeat (apply not_over_or in eq1; repnd).
  repeat (apply not_over_or in eq2; repnd).
  repeat (apply not_over_or in eq3; repnd).
  sp.
Qed.

Lemma newvars2_prop :
  forall v1 v2 terms,
    (v1, v2) = newvars2 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms ++ [v1]).
Proof.
  introv eq.
  unfold newvars2 in eq; cpx.
  unfold newvarlst; simpl; allrw free_vars_list_app; simpl.
  dands; apply fresh_var_not_in.
Qed.

Lemma newvars2_prop2 :
  forall v1 v2 terms,
    (v1, v2) = newvars2 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !v1 = v2.
Proof.
  introv eq.
  apply newvars2_prop in eq; repnd.
  allrw in_app_iff; allsimpl.
  repeat (apply not_over_or in eq; repnd).
  sp.
Qed.


Lemma closed_implies:
  forall t,
    closed t -> (forall x, !LIn x (free_vars t)).
Proof.
  introv cl.
  unfold closed in cl.
  allrw; simpl; try (complete sp).
Qed.

(** newvar on closed terms *)
Definition cnewvar (t : CTerm) := newvar (proj1_sig t).

Lemma cnewvar_eq :
  forall t, cnewvar t = nvarx.
Proof.
  destruct t; unfold cnewvar, newvar; simpl.
  rw isprog_eq in i.
  inversion i.
  unfold closed in H.
  rewrite H.
  unfold fresh_var; sp.
Qed.

Lemma isprog_vars_cvterm_var :
  forall v : NVar,
  forall t : CTerm,
    isprog_vars [v] (proj1_sig t).
Proof.
  destruct t; unfold cnewvar.
  rw isprog_vars_eq; simpl.
  rw isprog_eq in i.
  inversion i; sp.
  unfold closed in H.
  rewrite H; sp.
Qed.

Lemma isprog_vars_cvterm_newvar :
  forall t : CTerm,
    isprog_vars [cnewvar t] (proj1_sig t).
Proof.
  sp; apply isprog_vars_cvterm_var.
Qed.

(** Builds, from a closed term t, a term that has at most one free variable,
 * namely v, which we know not to be in t.
 * The term is the same.  Only the proof of closeness changes. *)
Definition cvterm_var (v : NVar) (t : CTerm) : CVTerm [v] :=
  exist (isprog_vars [v])
        (proj1_sig t)
        (isprog_vars_cvterm_var v t).

Definition cvterm_newvar (t : CTerm) : CVTerm [cnewvar t] :=
  cvterm_var (cnewvar t) t.

Lemma mk_cv_as_cvterm_var :
  forall v t, mk_cv [v] t = cvterm_var v t.
Proof.
  intros.
  destruct_cterms.
  unfold mk_cv, cvterm_var, get_cterm; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_vars_cvterm_var v (exist (fun t : NTerm => isprog t) x i)); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

End terms4Generic.


Hint Resolve isprogram_ot_if_eauto : slow.
Hint Immediate nvarx_nvary : slow.
Hint Immediate isprogram_get_cterm.
Hint Resolve isprog_implies : isprog.
Hint Extern 100 (LIn _ _) => complete (simpl; sp) : isprog.
Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.
Hint Resolve deq_bterm.
Hint Immediate deq_nterm.
Hint Immediate isprogram_get_cterm.
Hint Resolve isprog_ntwf_eauto : slow.
Tactic Notation "disjoint_reasoningv" :=
  (allunfold all_vars); repeat( progress disjoint_reasoning).
Ltac destruct_bterms:=
repeat match goal with
[bt : BTerm |- _] =>
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  destruct bt as [btlv btnt]
end.
