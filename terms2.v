(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** Here are some handy definitions that will
    reduce the verbosity of some of our later definitions
*)

Definition mk_lam (v : NVar) (b : NTerm) :=
  oterm (Can NLambda) [bterm [v] b].
Definition nobnd (f:NTerm) := bterm [] f.


Definition mk_apply (f a : NTerm) :=
  oterm (NCan NApply) [nobnd f , nobnd a].

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

Definition mk_integer n := oterm (Can (Nint n)) [].

Definition mk_nat (n : nat) := mk_integer (Z_of_nat n).

Definition mk_uni n := oterm (Can (NUni n)) [].

Definition mk_tuni n := oterm (Can NTUni) [nobnd n].

Definition mk_base  := oterm (Can NBase)  [].
Definition mk_int   := oterm (Can NInt)   [].
Definition mk_axiom := oterm (Can NAxiom) [].

Definition mk_inl x := oterm (Can NInl) [nobnd x].
Definition mk_inr x := oterm (Can NInr) [nobnd x].

Definition mk_pair a b := oterm (Can NPair) [nobnd a , nobnd b].

Definition mk_sup a b := oterm (Can NSup) [nobnd a , nobnd b].

Definition mk_union T1 T2 := oterm (Can NUnion) [nobnd T1, nobnd T2].

Definition mk_approx a b := oterm (Can NApprox) [nobnd a , nobnd b].
Definition mk_cequiv a b := oterm (Can NCequiv) [nobnd a , nobnd b].

Definition mk_compute a b n := oterm (Can NCompute) [nobnd a , nobnd b , nobnd n].

Definition mk_equality t1 t2 T :=
  oterm (Can NEquality) [nobnd t1,nobnd t2,nobnd T].

Definition mk_tequality t1 t2 :=
  oterm (Can NTEquality) [nobnd t1,nobnd t2].

Definition mk_can_test test a b c :=
  oterm (NCan (NCanTest test)) [nobnd a,nobnd b,nobnd c].

Definition mk_ispair   := mk_can_test CanIspair.
Definition mk_isint    := mk_can_test CanIsint.
Definition mk_isinl    := mk_can_test CanIsinl.
Definition mk_isinr    := mk_can_test CanIsinr.
Definition mk_isaxiom  := mk_can_test CanIsaxiom.
Definition mk_islambda := mk_can_test CanIslambda.
Definition mk_isatom   := mk_can_test CanIsatom.

Definition mk_rec (v : NVar) (T : NTerm) :=
  oterm (Can NRec) [bterm [v] T].

Definition mk_image (T : NTerm) (f : NTerm) :=
  oterm (Can NImage) [nobnd T, nobnd f].

Definition mk_function (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NFunction) [nobnd T1, bterm [v] T2].

Definition mk_product (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NProduct) [nobnd T1, bterm [v] T2].

Definition mk_set (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NSet) [nobnd T1, bterm [v] T2].

Definition mk_quotient (T1 : NTerm) (v1 v2 : NVar) (T2 : NTerm) :=
  oterm (Can NQuotient) [nobnd T1, bterm [v1,v2] T2].

Definition mk_isect (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NIsect) [nobnd T1, bterm [v] T2].

Definition mk_disect (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NDIsect) [nobnd T1, bterm [v] T2].

Definition mk_eisect (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NEIsect) [nobnd T1, bterm [v] T2].

Definition mk_w (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NW) [nobnd T1, bterm [v] T2].

Definition mk_m (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NM) [nobnd T1, bterm [v] T2].

Definition mk_pw
           (P : NTerm)
           (ap : NVar) (A : NTerm)
           (bp : NVar) (ba : NVar) (B : NTerm)
           (cp : NVar) (ca : NVar) (cb : NVar) (C : NTerm)
           (p : NTerm) :=
  oterm (Can NPW)
        [ nobnd P,
          bterm [ap] A,
          bterm [bp; ba] B,
          bterm [cp; ca; cb] C,
          nobnd p
        ].

Definition mk_pm
           (P : NTerm)
           (ap : NVar) (A : NTerm)
           (bp : NVar) (ba : NVar) (B : NTerm)
           (cp : NVar) (ca : NVar) (cb : NVar) (C : NTerm)
           (p : NTerm) :=
  oterm (Can NPM)
        [ nobnd P,
          bterm [ap] A,
          bterm [bp; ba] B,
          bterm [cp; ca; cb] C,
          nobnd p
        ].

Definition mk_spread (t1 : NTerm) (u v : NVar) (t2 : NTerm) :=
  oterm (NCan NSpread) [nobnd t1, bterm [u, v] t2].

Definition mk_dsup (t1 : NTerm) (u v : NVar) (t2 : NTerm) :=
  oterm (NCan NDsup) [nobnd t1, bterm [u, v] t2].

Definition mk_decide (t : NTerm) (u : NVar) (t1 : NTerm) (v : NVar) (t2 : NTerm) :=
  oterm (NCan NDecide) [nobnd t, bterm [u] t1, bterm [v] t2].

Definition mk_cbv (t1 : NTerm) (v : NVar) (t2 : NTerm) :=
  oterm (NCan NCbv) [nobnd t1, bterm [v] t2].

Definition mk_pertype (R : NTerm) :=
  oterm (Can NEPertype) [nobnd R].

Definition mk_ipertype (R : NTerm) :=
  oterm (Can NIPertype) [nobnd R].

Definition mk_spertype (R : NTerm) :=
  oterm (Can NSPertype) [nobnd R].

Definition mk_partial (T : NTerm) :=
  oterm (Can NPartial) [nobnd T].

Definition mk_admiss (T : NTerm) :=
  oterm (Can NAdmiss) [nobnd T].

Definition mk_mono (T : NTerm) :=
  oterm (Can NMono) [nobnd T].

Definition mk_less (a b c d : NTerm) :=
  oterm (NCan (NCompOp CompOpLess)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_int_eq (a b c d : NTerm) :=
  oterm (NCan (NCompOp CompOpInteq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_atom_eq (a b c d : NTerm) :=
  oterm (NCan (NCompOp CompOpAtomeq)) [nobnd a, nobnd b, nobnd c, nobnd d].

Definition mk_add a b := oterm (NCan (NArithOp ArithOpAdd)) [nobnd a, nobnd b].
Definition mk_mul a b := oterm (NCan (NArithOp ArithOpMul)) [nobnd a, nobnd b].
Definition mk_sub a b := oterm (NCan (NArithOp ArithOpSub)) [nobnd a, nobnd b].
Definition mk_div a b := oterm (NCan (NArithOp ArithOpDiv)) [nobnd a, nobnd b].
Definition mk_rem a b := oterm (NCan (NArithOp ArithOpRem)) [nobnd a, nobnd b].

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


(* --- non primitives --- *)

Definition mk_id := mk_lam nvarx (mk_var nvarx).

Definition mk_bottom := mk_fix mk_id.
Definition mk_bot := mk_bottom.

Definition mk_false := mk_approx mk_axiom mk_bot.
Definition mk_true  := mk_approx mk_axiom mk_axiom.

Definition mk_void  := mk_false.
Definition mk_unit  := mk_true.

Definition mk_btrue  := mk_inl mk_axiom.
Definition mk_bfalse := mk_inr mk_axiom.

Definition mk_ite a b c :=
  mk_decide a (newvar b) b (newvar c) c.

Definition mk_tt := mk_btrue.
Definition mk_ff := mk_bfalse.

Definition mk_pi1 t := mk_spread t nvarx nvary (mk_var nvarx).
Definition mk_pi2 t := mk_spread t nvarx nvary (mk_var nvary).

Definition mk_outl t := mk_decide t nvarx (mk_var nvarx) nvary mk_bot.
Definition mk_outr t := mk_decide t nvarx mk_bot nvary (mk_var nvary).

Definition mk_halts t := mk_approx mk_axiom (mk_cbv t nvarx mk_axiom).

Definition mk_uall   := mk_isect.
Definition mk_all    := mk_function.
Definition mk_exists := mk_product.

Definition mk_top := mk_isect mk_false nvarx mk_false.

Definition mk_member t T := mk_equality t t T.

Definition mk_type t := mk_tequality t t.

Definition mk_bool := mk_union mk_unit mk_unit.

Definition mk_apply2 R x y := mk_apply (mk_apply R x) y.

Definition mk_apply3 f a b c :=
  mk_apply (mk_apply (mk_apply f a) b) c.

Definition mk_apply4 f a b c d :=
  mk_apply (mk_apply (mk_apply (mk_apply f a) b) c) d.

Definition mk_squash T := mk_image T (mk_lam nvarx mk_axiom).

Definition mk_lam3 v1 v2 v3 b := mk_lam v1 (mk_lam v2 (mk_lam v3 b)).

Definition mk_less_than a b := mk_less a b mk_true mk_false.

Definition mk_or A B := mk_union A B.

Definition mk_zero := mk_nat 0.
Definition mk_one  := mk_nat 1.
Definition mk_two  := mk_nat 2.

(*
Definition mk_fun (T1 : NTerm) (T2 : NTerm) :=
  oterm (Can NFunction) [nobnd T1, bterm [v] T2].

Definition mk_product (T1 : NTerm) (v : NVar) (T2 : NTerm) :=
  oterm (Can NProduct) [nobnd T1, bterm [v] T2].
*)



(* --- foldings --- *)

Lemma fold_lam :
  forall v b, oterm (Can NLambda) [bterm [v] b] = mk_lam v b.
Proof. sp. Qed.

Lemma fold_apply :
  forall a b, oterm (NCan NApply) [ nobnd a, nobnd b ] = mk_apply a b.
Proof. sp. Qed.

Lemma fold_decide :
  forall d x f y g,
    oterm (NCan NDecide) [nobnd d, bterm [x] f, bterm [y] g]
    = mk_decide d x f y g.
Proof. sp. Qed.

Lemma fold_spread :
  forall a x y b,
    oterm (NCan NSpread) [nobnd a, bterm [x,y] b]
    = mk_spread a x y b.
Proof. sp. Qed.

Lemma fold_dsup :
  forall a x y b,
    oterm (NCan NDsup) [nobnd a, bterm [x,y] b]
    = mk_dsup a x y b.
Proof. sp. Qed.

Lemma fold_approx :
  forall a b, oterm (Can NApprox) [ nobnd a, nobnd b ] = mk_approx a b.
Proof. sp. Qed.

Lemma fold_cequiv :
  forall a b, oterm (Can NCequiv) [ nobnd a, nobnd b ] = mk_cequiv a b.
Proof. sp. Qed.

Lemma fold_pertype :
  forall a, oterm (Can NEPertype) [ nobnd a ] = mk_pertype a.
Proof. sp. Qed.

Lemma fold_ipertype :
  forall a, oterm (Can NIPertype) [ nobnd a ] = mk_ipertype a.
Proof. sp. Qed.

Lemma fold_spertype :
  forall a, oterm (Can NSPertype) [ nobnd a ] = mk_spertype a.
Proof. sp. Qed.

Lemma fold_tuni :
  forall a, oterm (Can NTUni) [ nobnd a ] = mk_tuni a.
Proof. sp. Qed.

Lemma fold_admiss :
  forall a, oterm (Can NAdmiss) [ nobnd a ] = mk_admiss a.
Proof. sp. Qed.

Lemma fold_mono :
  forall a, oterm (Can NMono) [ nobnd a ] = mk_mono a.
Proof. sp. Qed.

Lemma fold_partial :
  forall a, oterm (Can NPartial) [ nobnd a ] = mk_partial a.
Proof. sp. Qed.

(*
Lemma fold_esquash :
  forall a, oterm (Can NEsquash) [ nobnd a ] = mk_esquash a.
Proof.
  sp.
Qed.
*)

Lemma fold_compute :
  forall a b n,
    oterm (Can NCompute) [ nobnd a, nobnd b, nobnd n ]
    = mk_compute a b n.
Proof.
  sp.
Qed.

Lemma fold_equality :
  forall a b c,
    oterm (Can NEquality) [ nobnd a, nobnd b, nobnd c ]
    = mk_equality a b c.
Proof.
  sp.
Qed.

Lemma fold_tequality :
  forall a b,
    oterm (Can NTEquality) [ nobnd a, nobnd b ]
    = mk_tequality a b.
Proof.
  sp.
Qed.

Lemma fold_base :
  oterm (Can NBase) [] = mk_base.
Proof.
  sp.
Qed.

Lemma fold_member :
  forall t T,
    mk_equality t t T = mk_member t T.
Proof.
  sp.
Qed.

Lemma fold_mk_type :
  forall t,
    mk_tequality t t = mk_type t.
Proof.
  sp.
Qed.

Lemma fold_cbv :
  forall t1 v t2,
    oterm (NCan NCbv) [nobnd t1, bterm [v] t2] = mk_cbv t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_halts :
  forall t,
    mk_approx mk_axiom (mk_cbv t nvarx mk_axiom) = mk_halts t.
Proof.
  sp.
Qed.

Lemma fold_function :
  forall t1 v t2,
    oterm (Can NFunction) [nobnd t1, bterm [v] t2] = mk_function t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_isect :
  forall t1 v t2,
    oterm (Can NIsect) [nobnd t1, bterm [v] t2] = mk_isect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_disect :
  forall t1 v t2,
    oterm (Can NDIsect) [nobnd t1, bterm [v] t2] = mk_disect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_eisect :
  forall t1 v t2,
    oterm (Can NEIsect) [nobnd t1, bterm [v] t2] = mk_eisect t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_w :
  forall t1 v t2,
    oterm (Can NW) [nobnd t1, bterm [v] t2] = mk_w t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_m :
  forall t1 v t2,
    oterm (Can NM) [nobnd t1, bterm [v] t2] = mk_m t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_pw :
  forall P ap A bp ba B cp ca cb C p,
    oterm (Can NPW)
          [nobnd P,
           bterm [ap] A,
           bterm [bp,ba] B,
           bterm [cp,ca,cb] C,
           nobnd p
          ]
    = mk_pw P ap A bp ba B cp ca cb C p.
Proof.
  sp.
Qed.

Lemma fold_pm :
  forall P ap A bp ba B cp ca cb C p,
    oterm (Can NPM)
          [nobnd P,
           bterm [ap] A,
           bterm [bp,ba] B,
           bterm [cp,ca,cb] C,
           nobnd p
          ]
    = mk_pm P ap A bp ba B cp ca cb C p.
Proof.
  sp.
Qed.

Lemma fold_product :
  forall t1 v t2,
    oterm (Can NProduct) [nobnd t1, bterm [v] t2] = mk_product t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_set :
  forall t1 v t2,
    oterm (Can NSet) [nobnd t1, bterm [v] t2] = mk_set t1 v t2.
Proof.
  sp.
Qed.

Lemma fold_quotient :
  forall t1 v1 v2 t2,
    oterm (Can NQuotient) [nobnd t1, bterm [v1;v2] t2] = mk_quotient t1 v1 v2 t2.
Proof.
  sp.
Qed.

Lemma fold_pair :
  forall a b, oterm (Can NPair) [ nobnd a, nobnd b ] = mk_pair a b.
Proof.
  sp.
Qed.

Lemma fold_ispair :
  forall a b c,
    oterm (NCan (NCanTest CanIspair)) [ nobnd a, nobnd b, nobnd c ]
    = mk_ispair a b c.
Proof.
  sp.
Qed.

Lemma fold_sup :
  forall a b, oterm (Can NSup) [ nobnd a, nobnd b ] = mk_sup a b.
Proof.
  sp.
Qed.



(* ------ SIMPLE CHECKERS ON TERMS ------ *)

Definition ispair (t : NTerm) :=
  match t with
    | (| a , b |) => true
    | _ => false
  end.

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

Fixpoint size (t : NTerm) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => S (addl (map size_bterm bterms))
  end
 with size_bterm (bt: BTerm) :=
  match bt with
  | bterm lv nt => size nt
  end.



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

Definition IsTypeOpid (opid : Opid) : bool :=
  match opid with
  | Can (NUni _)   => true
  | Can NTUni      => true
  | Can NEquality  => true
  | Can NTEquality => true
  | Can NInt       => true
  | Can NAtom      => true
  | Can NBase      => true
  | Can NFunction  => true
  | Can NProduct   => true
  | Can NSet       => true
  | Can NQuotient  => true
  | Can NIsect     => true
  | Can NDIsect    => true
  | Can NEIsect    => true
  | Can NW         => true
  | Can NEPertype  => true
  | Can NIPertype  => true
  | Can NSPertype  => true
  | Can NPartial   => true
  | Can NUnion     => true
  | Can NApprox    => true
  | Can NCequiv    => true
  | Can NCompute   => true
  | Can NRec       => true
  | Can NImage     => true
  | _ => false
  end.

Definition IsType (t : NTerm) : bool :=
  match t with
  | vterm _ => false
  | oterm opid _ => IsTypeOpid opid
  end.


Lemma num_bvars_on_bterm :
  forall l n,
    num_bvars (bterm l n) = length l.
Proof.
  unfold num_bvars; simpl; sp.
Qed.

Fixpoint wft (t : NTerm) : bool :=
  match t with
    | vterm _ => true
    | oterm o bts =>
      andb (beq_list eq_nat_dec (map (num_bvars) bts) (OpBindings o))
           (ball (map wftb bts))
  end
with wftb (bt : BTerm) : bool :=
  match bt with
    | bterm vars t => wft t
  end.

Hint Constructors nt_wf bt_wf.

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

Ltac irr_step :=
  match goal with
    | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_proof_irrelevance; subst
    | [ H1 : isprog_vars ?vs ?a, H2 : isprog_vars ?vs ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_vars_proof_irrelevance; subst
  end.

Ltac irr := repeat irr_step.

Lemma isprogram_eq :
  forall t,
    isprogram t <=> isprog t.
Proof.
  unfold isprog, isprogram.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    split; sp. allunfold closed; allsimpl; sp.

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

Definition mk_vsubtype A v B := mk_member mk_id (mk_function A v B).
Definition mk_subtype A B := mk_vsubtype A (newvar B) B.

(* non-dependent function type *)
Definition mk_fun A B := mk_function A (newvar B) B.
(* non-dependent uniform function type *)
Definition mk_ufun A B := mk_isect A (newvar B) B.
(* non-dependent extensional uniform function type *)
Definition mk_eufun A B := mk_eisect A (newvar B) B.
(* non-dependent product type *)
Definition mk_prod A B := mk_product A (newvar B) B.

Definition mk_iff a b := mk_prod (mk_fun a b) (mk_fun b a).

Definition mk_not P := mk_fun P mk_void.

Definition mk_le a b := mk_not (mk_less_than b a).

Definition mk_tnat := mk_set mk_int nvary (mk_le mk_zero (mk_var nvary)).

Definition mk_nat_sub n :=
  mk_set mk_tnat nvarx (mk_less_than (mk_var nvarx) n).

Definition mk_dec P := mk_or P (mk_not P).

Definition mk_plus1 n := mk_add n mk_one.


(** A value is a program with a canonical operator *)
Inductive isvalue : NTerm -> Type :=
  | isvl : forall (c : CanonicalOp) (bts : list BTerm ),
           isprogram (oterm (Can c) bts)
           -> isvalue (oterm (Can c) bts).

Hint Constructors isvalue.

Inductive isovalue : NTerm -> Prop :=
  | isovl : forall (c : CanonicalOp) (bts : list BTerm),
              nt_wf (oterm (Can c) bts)
              -> isovalue (oterm (Can c) bts).

Lemma isvalue_closed :
  forall t, isvalue t -> closed t.
Proof.
  introv isv; inversion isv.
  allunfold isprogram; sp.
Qed.

Lemma isvalue_program :
  forall t, isvalue t -> isprogram t.
Proof.
  introv isv; inversion isv; sp.
Qed.

Lemma isvalue_mk_lam :
  forall v b, isprog_vars [v] b -> isvalue (mk_lam v b).
Proof.
  intros; repeat constructor; simpl; sp; subst.
  rw isprog_vars_eq in H; sp.
  unfold closed; simpl; rewrite app_nil_r.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_eq.
  allrw subset_singleton_r.

  unfold subset in H0; allsimpl.
  apply_in_hyp p; sp.
  rw isprog_vars_eq in H; sp.
Qed.

Lemma isvalue_mk_int : isvalue mk_int.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprogram_int : isprogram mk_int.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprog_int : isprog mk_int.
Proof.
  repeat constructor.
Qed.

Theorem wf_int : wf_term mk_int.
Proof.
  sp.
Qed.

Lemma isprogram_mk_integer : forall n : Z, isprogram (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isprog_mk_integer' : forall n : Z, isprog (mk_integer n).
Proof.
  repeat constructor.
Qed.

Definition isprog_mk_integer : forall n : Z, isprog (mk_integer n)
  := fun _ => eq_refl.

Lemma isvalue_mk_integer : forall n : Z, isvalue (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma isovalue_mk_integer : forall n : Z, isovalue (mk_integer n).
Proof.
  repeat constructor. intros; allsimpl; sp.
Qed.

Lemma wf_mk_integer' : forall n : Z, wf_term (mk_integer n).
Proof.
  sp.
Qed.

Definition wf_mk_integer : forall n : Z, wf_term (mk_integer n)
  := fun _ => eq_refl.

Lemma isprogram_mk_nat : forall n : nat, isprogram (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isprogram_mk_integer.
Qed.

Lemma isprog_mk_nat' : forall n : nat, isprog (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isprog_mk_integer.
Qed.

Definition isprog_mk_nat : forall n : nat, isprog (mk_nat n)
  := fun _ => eq_refl.

Lemma isvalue_mk_nat : forall n : nat, isvalue (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isvalue_mk_integer.
Qed.

Lemma isovalue_mk_nat : forall n : nat, isovalue (mk_nat n).
Proof.
  unfold mk_nat.
  intros; apply isovalue_mk_integer.
Qed.

Lemma wf_mk_nat' : forall n : nat, wf_term (mk_nat n).
Proof.
  sp.
Qed.

Definition wf_mk_nat : forall n : nat, wf_term (mk_nat n)
  := fun _ => eq_refl.

Lemma isprogram_mk_uni : forall n : nat, isprogram (mk_uni n).
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isprog_mk_uni : forall n : nat, isprog (mk_uni n).
Proof.
  repeat constructor.
Qed.

Lemma isvalue_mk_uni : forall n : nat, isvalue (mk_uni n).
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma wf_mk_uni : forall n : nat, wf_term (mk_uni n).
Proof.
  sp.
Qed.

Lemma wf_mk_var : forall v, wf_term (mk_var v).
Proof.
  sp.
Qed.

Lemma isprogram_axiom : isprogram mk_axiom.
Proof.
  repeat constructor; simpl; sp.
Qed.

Theorem isprog_axiom : isprog mk_axiom.
Proof.
  repeat constructor.
Qed.

Theorem isvalue_axiom : isvalue mk_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem wf_axiom : wf_term mk_axiom.
Proof.
  sp.
Qed.

Theorem isprogram_base : isprogram mk_base.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem isprog_base : isprog mk_base.
Proof.
  repeat constructor.
Qed.

Lemma isvalue_base : isvalue mk_base.
Proof.
  repeat constructor; simpl; sp.
Qed.

Lemma wf_base : wf_term mk_base.
Proof.
  sp.
Qed.

Hint Immediate isvalue_mk_int.
Hint Immediate isprogram_int.
Hint Immediate isprog_int.
Hint Immediate wf_int.
Hint Immediate isvalue_axiom.
Hint Immediate isprogram_axiom.
Hint Immediate isprog_axiom.
Hint Immediate wf_axiom.
Hint Immediate isvalue_base.
Hint Immediate isprogram_base.
Hint Immediate isprog_base.
Hint Immediate wf_base.

Theorem wf_pertype :
  forall a, wf_term a -> wf_term (mk_pertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Lemma isprogram_pertype :
  forall a, isprogram a -> isprogram (mk_pertype a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw nt_wf_eq.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_pertype_iff :
  forall a, isprogram a <=> isprogram (mk_pertype a).
Proof.
  intros; split; intro i.
  apply isprogram_pertype; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_pertype :
  forall a, isprog a -> isprog (mk_pertype a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_pertype; auto.
Qed.

Theorem wf_partial :
  forall a, wf_term a -> wf_term (mk_partial a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_partial :
  forall a, isprogram a -> isprogram (mk_partial a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_partial_iff :
  forall a, isprogram a <=> isprogram (mk_partial a).
Proof.
  intros; split; intro i.
  apply isprogram_partial; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_partial :
  forall a, isprog a -> isprog (mk_partial a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_partial; auto.
Qed.

Theorem isprogram_admiss :
  forall a, isprogram a -> isprogram (mk_admiss a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_admiss_iff :
  forall a, isprogram a <=> isprogram (mk_admiss a).
Proof.
  intros; split; intro i.
  apply isprogram_admiss; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_admiss :
  forall a, isprog a -> isprog (mk_admiss a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_admiss; auto.
Qed.

Theorem isprogram_mono :
  forall a, isprogram a -> isprogram (mk_mono a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw nt_wf_eq.
  apply wf_partial; sp.
Qed.

Lemma isprogram_mono_iff :
  forall a, isprogram a <=> isprogram (mk_mono a).
Proof.
  intros; split; intro i.
  apply isprogram_mono; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_mono :
  forall a, isprog a -> isprog (mk_mono a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_mono; auto.
Qed.

Theorem wf_ipertype :
  forall a, wf_term a -> wf_term (mk_ipertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_ipertype :
  forall a, isprogram a -> isprogram (mk_ipertype a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_ipertype_iff :
  forall a, isprogram a <=> isprogram (mk_ipertype a).
Proof.
  intros; split; intro i.
  apply isprogram_ipertype; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_ipertype :
  forall a, isprog a -> isprog (mk_ipertype a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_ipertype; auto.
Qed.

Theorem wf_ipertype_iff :
  forall a, wf_term a <=> wf_term (mk_ipertype a).
Proof.
  intros; split; intro i.
  apply wf_ipertype; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_ipertype :
  forall f vs,
    isprog_vars vs (mk_ipertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- wf_term_eq.
  allrw <- wf_ipertype_iff; split; sp.
Qed.

Theorem wf_spertype :
  forall a, wf_term a -> wf_term (mk_spertype a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_spertype :
  forall a, isprogram a -> isprogram (mk_spertype a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_spertype_iff :
  forall a, isprogram a <=> isprogram (mk_spertype a).
Proof.
  intros; split; intro i.
  apply isprogram_spertype; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Theorem isprog_spertype :
  forall a, isprog a -> isprog (mk_spertype a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_spertype; auto.
Qed.

Theorem wf_spertype_iff :
  forall a, wf_term a <=> wf_term (mk_spertype a).
Proof.
  intros; split; intro i.
  apply wf_spertype; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_spertype :
  forall f vs,
    isprog_vars vs (mk_spertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- wf_term_eq.
  allrw <- wf_spertype_iff; split; sp.
Qed.

Lemma wf_tuni :
  forall a, wf_term a -> wf_term (mk_tuni a).
Proof.
  introv h.
  apply nt_wf_eq; apply nt_wf_eq in h.
  intros; inversion h; subst;
  constructor; allsimpl; sp;
  subst; auto; simpl; constructor; auto.
Qed.

Lemma isprogram_tuni :
  forall a, isprogram a -> isprogram (mk_tuni a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl; sp.
  apply nt_wf_eq.
  allrw nt_wf_eq.
  apply wf_pertype; sp.
Qed.

Lemma isprogram_tuni_iff :
  forall a, isprogram a <=> isprogram (mk_tuni a).
Proof.
  intros; split; intro i.
  apply isprogram_tuni; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprog_tuni :
  forall a, isprog a -> isprog (mk_tuni a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_tuni; auto.
Qed.

Theorem wf_tuni_iff :
  forall a, wf_term a <=> wf_term (mk_tuni a).
Proof.
  intros; split; intro i.
  apply wf_tuni; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_tuni :
  forall f vs,
    isprog_vars vs (mk_tuni f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- wf_term_eq.
  allrw <- wf_tuni_iff; split; sp.
Qed.

(*
Theorem wf_esquash :
  forall a, wf_term a -> wf_term (mk_esquash a).
Proof.
  intros.
  apply nt_wf_eq; apply nt_wf_eq in H.
  intros; inversion H; subst;
  constructor; allsimpl; sp;
  subst; auto; constructor; auto.
Qed.

Theorem isprogram_esquash :
  forall a, isprogram a -> isprogram (mk_esquash a).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  rewrite X0; simpl.
  rewrite remove_nvars_nil_r; sp.
  apply nt_wf_eq.
  apply nt_wf_eq in X.
  apply wf_pertype; sp.
Qed.

Theorem isprog_esquash :
  forall a, isprog a -> isprog (mk_esquash a).
Proof.
  sp.
  allrw isprog_eq.
  apply isprogram_esquash; auto.
Qed.
*)

Theorem wf_image :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_image a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_image_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_image a b).
Proof.
  intros; split; intro k.
  apply wf_image; sp.
  allrw <- nt_wf_eq.
  inversion k as [|i j u w]; subst; allsimpl.
  generalize (u (nobnd a)) (u (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; subst; inversion i2; subst; sp.
Qed.

Lemma isprogram_image :
  forall a b, isprogram a -> isprogram b -> isprogram (mk_image a b).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw nt_wf_eq.
  apply wf_image; sp.
Qed.

Lemma isprogram_image_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_image a b).
Proof.
  sp; split; intro k; try (apply isprogram_image; sp).
  inversion k as [c w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [ | o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)) (i (nobnd b)); intros e1 e2.
  dest_imp e1 hyp.
  dest_imp e2 hyp.
  inversion e1; subst.
  inversion e2; subst; sp.
Qed.

Theorem isprog_image :
  forall a b, isprog a -> isprog b -> isprog (mk_image a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_image; auto.
Qed.

Theorem wf_apply :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_apply a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_apply :
  forall a b, isprogram a -> isprogram b -> isprogram (mk_apply a b).
Proof.
  sp; allunfold isprogram; sp.
  unfold closed.
  simpl.
  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold closed.
  allrw; simpl.
  rewrite remove_nvars_nil_r; sp.
  allrw nt_wf_eq.
  apply wf_apply; sp.
Qed.

Lemma isprogram_apply_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_apply a b).
Proof.
  sp; split; intro k; try (apply isprogram_apply; sp).
  inversion k as [c w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repd.
  unfold isprogram, closed; allrw.
  inversion w as [ | o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)) (i (nobnd b)); intros e1 e2.
  dest_imp e1 hyp.
  dest_imp e2 hyp.
  inversion e1; subst.
  inversion e2; subst; sp.
Qed.

Theorem isprog_apply :
  forall a b, isprog a -> isprog b -> isprog (mk_apply a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_apply; auto.
Qed.

Theorem wf_apply2 :
  forall f a b, wf_term f -> wf_term a -> wf_term b -> wf_term (mk_apply2 f a b).
Proof.
  unfold mk_apply2; sp.
  repeat (apply wf_apply); auto.
Qed.

Theorem isprogram_apply2 :
  forall f a b,
    isprogram f -> isprogram a -> isprogram b -> isprogram (mk_apply2 f a b).
Proof.
  unfold mk_apply2; sp.
  repeat (apply isprogram_apply); auto.
Qed.

Theorem isprog_apply2 :
  forall f a b, isprog f -> isprog a -> isprog b -> isprog (mk_apply2 f a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_apply2; auto.
Qed.

Theorem closed_approx :
  forall a b, closed a -> closed b -> closed (mk_approx a b).
Proof.
  intros.
  allunfold closed; unfold mk_approx; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_cequiv :
  forall a b, closed a -> closed b -> closed (mk_cequiv a b).
Proof.
  intros.
  allunfold closed; unfold mk_cequiv; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_union :
  forall a b, closed a -> closed b -> closed (mk_union a b).
Proof.
  intros.
  allunfold closed; unfold mk_union; simpl.
  allrw; simpl; auto.
Qed.

Theorem closed_compute :
  forall a b n, closed a -> closed b -> closed n -> closed (mk_compute a b n).
Proof.
  intros.
  allunfold closed; unfold mk_compute; simpl.
  allrw; simpl; sp.
Qed.

Theorem wf_approx :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_approx a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_approx_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_approx a b).
Proof.
  sp; split; intros k.
  apply wf_approx; sp.
  allrw wf_term_eq.
  inversion k as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)); generalize (i (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; inversion i2; sp.
Qed.

Lemma isprogram_isinl :
  forall a b c,
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_isinl a b c).
Proof.
  introv ipa ipb ipc.
  allunfold isprogram; repnd; allunfold closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_isinl_iff :
  forall a b c,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_isinl a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_isinl; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_isinl :
  forall a b c,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_isinl a b c).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_isinl; auto.
Qed.

Lemma isprogram_isinr :
  forall a b c,
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_isinr a b c).
Proof.
  introv ipa ipb ipc.
  allunfold isprogram; repnd; allunfold closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_isinr_iff :
  forall a b c,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_isinr a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_isinr; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_isinr :
  forall a b c,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_isinr a b c).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_isinr; auto.
Qed.

Lemma isprogram_ispair :
  forall a b c,
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_ispair a b c).
Proof.
  introv ipa ipb ipc.
  allunfold isprogram; repnd; allunfold closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma isprogram_ispair_iff :
  forall a b c,
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_ispair a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_ispair; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Theorem isprog_ispair :
  forall a b c,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_ispair a b c).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_ispair; auto.
Qed.

Lemma isprogram_approx :
  forall a b, isprogram a -> isprogram b -> isprogram (mk_approx a b).
Proof.
  intros. allunfold isprogram. repnd. split. apply closed_approx; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Lemma isprogram_approx_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_approx a b).
Proof.
  intros; split; intro i.
  apply isprogram_approx; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Theorem isprog_approx :
  forall a b, isprog a -> isprog b -> isprog (mk_approx a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_approx; auto.
Qed.

Theorem wf_cequiv :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_cequiv a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem isprogram_cequiv :
  forall a b, isprogram a -> isprogram b -> isprogram (mk_cequiv a b).
Proof.
  intros. allunfold isprogram. repnd. split. apply closed_cequiv; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Lemma isprogram_cequiv_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_cequiv a b).
Proof.
  intros; split; intro i.
  apply isprogram_cequiv; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Theorem isprog_cequiv :
  forall a b, isprog a -> isprog b -> isprog (mk_cequiv a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_cequiv; auto.
Qed.

Theorem isprogram_union :
  forall a b, isprogram a -> isprogram b -> isprogram (mk_union a b).
Proof.
  intros. allunfold isprogram. repnd. split. apply closed_union; auto.
  constructor; auto. intros ? Hin.
  inverts Hin  as [Hgarbage | Hin]; subst;
  try (constructor;auto).
  inversion Hin.
Qed.

Theorem isprog_union :
  forall a b, isprog a -> isprog b -> isprog (mk_union a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_union; auto.
Qed.

Theorem isprogram_compute :
  forall a b n,
    isprogram a -> isprogram b -> isprogram n -> isprogram (mk_compute a b n).
Proof.
  unfold isprogram, closed; sp; simpl; allrw; allsimpl; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Theorem isprog_compute :
  forall a b n, isprog a -> isprog b -> isprog n -> isprog (mk_compute a b n).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_compute; auto.
Qed.

Theorem isvalue_approx :
  forall a b, isprogram a -> isprogram b -> isvalue (mk_approx a b).
Proof.
 intros. constructor. fold (mk_approx a b).
 apply isprogram_approx; auto.
Qed.

Theorem isovalue_approx :
  forall a b, nt_wf a -> nt_wf b -> isovalue (mk_approx a b).
Proof.
 intros. constructor. fold (mk_approx a b).
 allrw nt_wf_eq.
 apply wf_approx; auto.
Qed.

Theorem isvalue_cequiv :
  forall a b, isprogram a -> isprogram b -> isvalue (mk_cequiv a b).
Proof.
 intros. constructor.
 apply isprogram_cequiv; auto.
Qed.

Theorem isovalue_cequiv :
  forall a b, nt_wf a -> nt_wf b -> isovalue (mk_cequiv a b).
Proof.
 intros. constructor.
 allrw nt_wf_eq.
 apply wf_approx; auto.
Qed.

Theorem isvalue_union :
  forall a b, isprogram a -> isprogram b -> isvalue (mk_union a b).
Proof.
 intros. constructor.
 apply isprogram_union; auto.
Qed.

Theorem isvalue_image :
  forall a b, isprogram a -> isprogram b -> isvalue (mk_image a b).
Proof.
  intros; constructor; apply isprogram_image; auto.
Qed.

Theorem isvalue_pertype :
  forall a, isprogram a -> isvalue (mk_pertype a).
Proof.
 intros; constructor; apply isprogram_pertype; auto.
Qed.

Theorem isvalue_partial :
  forall a, isprogram a -> isvalue (mk_partial a).
Proof.
 intros; constructor; apply isprogram_partial; auto.
Qed.

Theorem isvalue_ipertype :
  forall a, isprogram a -> isvalue (mk_ipertype a).
Proof.
 intros. constructor. fold (mk_ipertype a).
 apply isprogram_ipertype; auto.
Qed.

Theorem isvalue_spertype :
  forall a, isprogram a -> isvalue (mk_spertype a).
Proof.
 intros. constructor. fold (mk_spertype a).
 apply isprogram_spertype; auto.
Qed.

Theorem isvalue_tuni :
  forall a, isprogram a -> isvalue (mk_tuni a).
Proof.
 intros; constructor; apply isprogram_tuni; auto.
Qed.

(*
Theorem isvalue_esquash :
  forall a, isprogram a -> isvalue (mk_esquash a).
Proof.
 intros. constructor. fold (mk_esquash a).
 apply isprogram_esquash; auto.
Qed.
*)

Lemma wf_equality :
  forall a b T, wf_term a -> wf_term b -> wf_term T -> wf_term (mk_equality a b T).
Proof.
  intros a b T; repeat (rw <- nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_equality_iff :
  forall a b T, (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_equality a b T).
Proof.
  sp; split; intros.
  apply wf_equality; sp.
  inversion H.
  allrw andb_true; sp.
Qed.

Lemma wf_equality_iff2 :
  forall a b T, wf_term (mk_equality a b T) <=> (wf_term a # wf_term b # wf_term T).
Proof.
  intros; rw wf_equality_iff; sp.
Qed.

Lemma wf_member :
  forall a T, wf_term a -> wf_term T -> wf_term (mk_member a T).
Proof.
  sp; unfold mk_member; apply wf_equality; sp.
Qed.

Lemma wf_member_iff :
  forall a T, (wf_term a # wf_term T) <=> wf_term (mk_member a T).
Proof.
  sp; split; intro i.
  apply wf_member; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd T)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_member_iff2 :
  forall a T, wf_term (mk_member a T) <=> (wf_term a # wf_term T).
Proof.
  intros; rw wf_member_iff; sp.
Qed.

Lemma wf_tequality :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_tequality a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_tequality_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_tequality a b).
Proof.
  sp; split; intros.
  apply wf_tequality; sp.
  inversion H.
  allrw andb_true; sp.
Qed.

Lemma wf_tequality_iff2 :
  forall a b, wf_term (mk_tequality a b) <=> (wf_term a # wf_term b).
Proof.
  intros; rw wf_tequality_iff; sp.
Qed.

Lemma wf_type :
  forall a, wf_term a -> wf_term (mk_type a).
Proof.
  sp; apply wf_tequality; sp.
Qed.

Lemma wf_type_iff :
  forall a, wf_term a <=> wf_term (mk_type a).
Proof.
  sp; split; intro i.
  apply wf_type; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  inversion i1; subst; sp.
Qed.

Lemma wf_type_iff2 :
  forall a, wf_term (mk_type a) <=> wf_term a.
Proof.
  intros; rw <- wf_type_iff; sp.
Qed.

Lemma wf_lam :
  forall v b, wf_term b -> wf_term (mk_lam v b).
Proof.
  intros v b; repeat (rw <- nt_wf_eq).
  intros ntb; inversion ntb; subst; constructor; allsimpl; sp; subst; constructor; sp.
Qed.

Lemma wf_lam_iff :
  forall v b, (wf_term b) <=> wf_term (mk_lam v b).
Proof.
  sp; split; intro i; try (apply wf_lam; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e ]; subst; allsimpl.
  generalize (k (bterm [v] b)); intros j.
  dest_imp j hyp; sp.
  inversion j; subst; sp.
Qed.

Lemma wf_id :
  wf_term mk_id.
Proof.
  apply wf_lam; sp.
Qed.
Hint Immediate wf_id.

Lemma wf_squash :
  forall T, wf_term (mk_squash T) <=> wf_term T.
Proof.
  intro; unfold mk_squash; rw <- wf_image_iff.
  rw <- wf_lam_iff; split; sp.
Qed.

Theorem wf_function :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_function a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_function_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_function a v b).
Proof.
  sp; split; intro i; try (apply wf_function; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_subtype :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_subtype a b).
Proof.
  sp; unfold mk_subtype, mk_vsubtype.
  apply wf_member; sp.
  apply wf_function; sp.
Qed.

Lemma wf_subtype_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_subtype a b).
Proof.
  sp; split; intro.
  apply wf_subtype; sp.
  unfold mk_subtype, mk_vsubtype in H.
  allrw <- wf_member_iff; repd.
  allrw <- wf_function_iff; sp.
Qed.

Lemma wf_halts :
  forall a, wf_term a -> wf_term (mk_halts a).
Proof.
  sp; unfold mk_halts.
  allrw wf_term_eq.
  constructor; repeat (allsimpl; sp; subst; repeat constructor).
Qed.

Lemma wf_halts_iff :
  forall a, wf_term a <=> wf_term (mk_halts a).
Proof.
  sp; split; intro i.
  apply wf_halts; sp.
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst.
  generalize (k (nobnd (mk_cbv a nvarx mk_axiom))); allsimpl; intro j.
  dest_imp j hyp.
  inversion j as [ lnv nt u ]; subst.
  inversion u as [ | o lnt p q ]; subst; allsimpl.
  generalize (p (nobnd a)); intro r.
  dest_imp r hyp.
  inversion r; subst; sp.
Qed.

Lemma isprogram_equality :
  forall a b T,
    isprogram a
    -> isprogram b
    -> isprogram T
    -> isprogram (mk_equality a b T).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold isprogram; allunfold closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_equality_iff :
  forall a b c, (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_equality a b c).
Proof.
  intros; split; intro i.
  apply isprogram_equality; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_equality :
  forall a b T,
    isprog a
    -> isprog b
    -> isprog T
    -> isprog (mk_equality a b T).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_equality; auto.
Qed.

Lemma isvalue_equality : forall a b T,
  isprogram (mk_equality a b T) -> isvalue (mk_equality a b T).
Proof.
 intros.
 constructor.
 allunfold mk_equality; auto.
Qed.

Lemma isprogram_member :
  forall t T,
    isprogram t
    -> isprogram T
    -> isprogram (mk_member t T).
Proof.
  unfold mk_member; sp.
  apply isprogram_equality; sp.
Qed.

Lemma isprog_member :
  forall t T,
    isprog t
    -> isprog T
    -> isprog (mk_member t T).
Proof.
  unfold mk_member; sp; apply isprog_equality; sp.
Qed.

Lemma isprogram_tequality :
  forall a b,
    isprogram a
    -> isprogram b
    -> isprogram (mk_tequality a b).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold isprogram; allunfold closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_tequality_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_tequality a b).
Proof.
  intros; split; intro i.
  apply isprogram_tequality; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_tequality :
  forall a b, isprog a -> isprog b -> isprog (mk_tequality a b).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_tequality; auto.
Qed.

Lemma isvalue_tequality :
  forall a b, isprogram (mk_tequality a b) -> isvalue (mk_tequality a b).
Proof.
 intros.
 constructor.
 allunfold mk_tequality; auto.
Qed.

Lemma isprogram_type :
  forall t, isprogram t -> isprogram (mk_type t).
Proof.
  unfold mk_type; sp.
  apply isprogram_tequality; sp.
Qed.

Lemma isprog_type :
  forall t, isprog t -> isprog (mk_type t).
Proof.
  unfold mk_type; sp; apply isprog_tequality; sp.
Qed.

Lemma isprogram_cbv :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_cbv a v b).
Proof.
  sp.
  repeat constructor; sp.
  unfold closed; simpl.
  rw remove_nvars_nil_l.
  rewrite app_nil_r.
  rw app_eq_nil_iff; sp.
  allunfold isprogram; allunfold closed; sp.
  allrw subvars_eq.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allsimpl; sp; subst.
  constructor; allunfold isprogram; sp.
  constructor; sp.
Qed.

Lemma isprogram_cbv_iff :
  forall a v b,
    isprogram (mk_cbv a v b)
    <=> isprogram a
        # subvars (free_vars b) [v]
        # nt_wf b.
Proof.
  sp; split; intros i.
  inversion i as [ cl w ].
  inversion w as [| o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); simpl; intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst.
  inversion cl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  unfold isprogram, closed.
  onerw app_eq_nil_iff; repd; allrw; sp.
  allrw <- null_iff_nil.
  allrw null_remove_nvars; allsimpl.
  rw subvars_eq.
  unfold subset; sp; simpl.
  try (complete (apply_in_hyp p; sp)).
  apply isprogram_cbv; sp.
Qed.

Lemma isprog_cbv :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_cbv a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_cbv; sp.
Qed.

Lemma isprogram_halts :
  forall t,
    isprogram t
    -> isprogram (mk_halts t).
Proof.
  unfold mk_halts; sp.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_cbv; sp.
  allrw nt_wf_eq; apply wf_axiom.
Qed.

Lemma isprog_halts :
  forall t,
    isprog t
    -> isprog (mk_halts t).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_halts; sp.
Qed.

Lemma wf_cbv :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_cbv a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_cbv_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_cbv a v b).
Proof.
  sp; split; intros i.
  apply wf_cbv; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma wf_isect :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_isect a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_isect_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_isect a v b).
Proof.
  sp; split; intro i; try (apply wf_isect; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_isect :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_isect a v b).
Proof.
  sp.
  unfold isprogram, mk_isect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_isect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_isect a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_isect; sp.
Qed.

Lemma isprog_isect_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_isect a v b).
Proof.
  introv; split; intro k; try (apply isprog_isect; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_disect :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_disect a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_disect_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_disect a v b).
Proof.
  sp; split; intro i; try (apply wf_disect; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_disect :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_disect a v b).
Proof.
  sp.
  unfold isprogram, mk_disect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_disect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_disect a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_disect; sp.
Qed.

Lemma isprog_disect_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_disect a v b).
Proof.
  introv; split; intro k; try (apply isprog_disect; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_eisect :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_eisect a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_eisect_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_eisect a v b).
Proof.
  sp; split; intro i; try (apply wf_eisect; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_eisect :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_eisect a v b).
Proof.
  sp.
  unfold isprogram, mk_eisect, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_eisect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_eisect a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_eisect; sp.
Qed.

Lemma isprog_eisect_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_eisect a v b).
Proof.
  introv; split; intro k; try (apply isprog_eisect; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_set :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_set a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_set_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_set a v b).
Proof.
  sp; split; intro i; try (apply wf_set; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_set :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_set a v b).
Proof.
  sp.
  unfold isprogram, mk_set, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_set :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_set a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_set; sp.
Qed.

Lemma isprog_set_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_set a v b).
Proof.
  introv; split; intro k; try (apply isprog_set; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma wf_quotient :
  forall a v1 v2 b, wf_term a -> wf_term b -> wf_term (mk_quotient a v1 v2 b).
Proof.
  intros a v1 v2 B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Theorem wf_quotient_iff :
  forall a v1 v2 b, (wf_term a # wf_term b) <=> wf_term (mk_quotient a v1 v2 b).
Proof.
  sp; split; intro i; try (apply wf_quotient; sp).
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v1,v2] b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_quotient :
  forall a v1 v2 b,
  isprogram a
  -> subvars (free_vars b) [v1,v2]
  -> nt_wf b
  -> isprogram (mk_quotient a v1 v2 b).
Proof.
  sp.
  unfold isprogram, mk_quotient, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_prop; discover; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_quotient :
  forall a v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_quotient a v1 v2 b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_quotient; sp.
Qed.

Lemma isprog_quotient_iff :
  forall a v1 v2 b,
    (isprog a # isprog_vars [v1,v2] b)
    <=> isprog (mk_quotient a v1 v2 b).
Proof.
  introv; split; intro k; try (apply isprog_quotient; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v1,v2] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v1 x); destruct (eq_var_dec v2 x); sp.
  right; right; right; allsimpl; sp.
Qed.

Lemma wf_w :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_w a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_w_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_w a v b).
Proof.
  sp; split; intro i; try (apply wf_w; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_w :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_w a v b).
Proof.
  sp.
  unfold isprogram, mk_w, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_w :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_w a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_w; sp.
Qed.

Lemma isprog_w_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_w a v b).
Proof.
  introv; split; intro k; try (apply isprog_w; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.


Lemma wf_m :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_m a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_m_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_m a v b).
Proof.
  sp; split; intro i; try (apply wf_m; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprogram_m :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_m a v b).
Proof.
  sp.
  unfold isprogram, mk_m, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_m :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_m a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_m; sp.
Qed.


Lemma wf_pw :
  forall P ap A bp ba B cp ca cb C p,
    wf_term P
    -> wf_term A
    -> wf_term B
    -> wf_term C
    -> wf_term p
    -> wf_term (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  introv wP wA wB wC wp; repeat (rw <- nt_wf_eq).
  inversion wP; inversion wA; inversion wB; inversion wC; inversion wp; constructor; sp;
  allsimpl; sp; subst; unfold num_bvars; simpl; sp;
  constructor; sp; rw nt_wf_eq; sp.
Qed.

Lemma wf_pw_iff :
  forall P ap A bp ba B cp ca cb C p,
    (wf_term P
     # wf_term A
     # wf_term B
     # wf_term C
     # wf_term p)
    <=> wf_term (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp; split; intro i; try (apply wf_pw; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd P))
             (k (bterm [ap] A))
             (k (bterm [bp,ba] B))
             (k (bterm [cp,ca,cb] C))
             (k (nobnd p));
    intros i1 i2 i3 i4 i5.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  dest_imp i3 hyp; try (complete sp).
  dest_imp i4 hyp; try (complete sp).
  dest_imp i5 hyp; try (complete sp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst; sp.
Qed.

Lemma isprogram_pw :
  forall P ap A bp ba B cp ca cb C p,
    isprogram P
    -> subvars (free_vars A) [ap]
    -> nt_wf A
    -> subvars (free_vars B) [bp, ba]
    -> nt_wf B
    -> subvars (free_vars C) [cp, ca, cb]
    -> nt_wf C
    -> isprogram p
    -> isprogram (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  unfold isprogram, mk_pw, closed; simpl; sp.

  allrw <- null_iff_nil.
  allrw null_app.
  allrw remove_nvars_nil_l.
  allrw <- closed_null_free_vars.
  allrw null_nil_iff.
  allunfold isprogram; sp;
  try (complete (rw null_remove_nvars; simpl; sp;
                 allrw subvars_prop; allsimpl;
                 discover; sp)).

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_pw :
  forall P ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog p
    -> isprog (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_pw; sp.
Qed.


Lemma wf_pm :
  forall P ap A bp ba B cp ca cb C p,
    wf_term P
    -> wf_term A
    -> wf_term B
    -> wf_term C
    -> wf_term p
    -> wf_term (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  introv wP wA wB wC wp; repeat (rw <- nt_wf_eq).
  inversion wP; inversion wA; inversion wB; inversion wC; inversion wp; constructor; sp;
  allsimpl; sp; subst; unfold num_bvars; simpl; sp;
  constructor; sp; rw nt_wf_eq; sp.
Qed.

Lemma wf_pm_iff :
  forall P ap A bp ba B cp ca cb C p,
    (wf_term P
     # wf_term A
     # wf_term B
     # wf_term C
     # wf_term p)
    <=> wf_term (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp; split; intro i; try (apply wf_pm; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd P))
             (k (bterm [ap] A))
             (k (bterm [bp,ba] B))
             (k (bterm [cp,ca,cb] C))
             (k (nobnd p));
    intros i1 i2 i3 i4 i5.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  dest_imp i3 hyp; try (complete sp).
  dest_imp i4 hyp; try (complete sp).
  dest_imp i5 hyp; try (complete sp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst; sp.
Qed.

Lemma isprogram_pm :
  forall P ap A bp ba B cp ca cb C p,
    isprogram P
    -> subvars (free_vars A) [ap]
    -> nt_wf A
    -> subvars (free_vars B) [bp, ba]
    -> nt_wf B
    -> subvars (free_vars C) [cp, ca, cb]
    -> nt_wf C
    -> isprogram p
    -> isprogram (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  unfold isprogram, mk_pw, closed; simpl; sp.

  allrw <- null_iff_nil.
  allrw null_app.
  allrw remove_nvars_nil_l.
  allrw <- closed_null_free_vars.
  allrw null_nil_iff.
  allunfold isprogram; sp;
  try (complete (rw null_remove_nvars; simpl; sp;
                 allrw subvars_prop; allsimpl;
                 discover; sp)).

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_pm :
  forall P ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog p
    -> isprog (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_pm; sp.
Qed.


Lemma isprogram_function :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_function a v b).
Proof.
  sp.
  unfold isprogram, mk_function, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_function :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_function a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_function; sp.
Qed.

Lemma isprog_function_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_function a v b).
Proof.
  introv; split; intro k; try (apply isprog_function; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_product :
  forall a v b,
  isprogram a
  -> subvars (free_vars b) [v]
  -> nt_wf b
  -> isprogram (mk_product a v b).
Proof.
  sp.
  unfold isprogram, mk_product, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw remove_nvars_nil_l).
  rw <- closed_null_free_vars.
  rw null_nil_iff.
  allunfold isprogram; sp.
  rw null_remove_nvars; simpl; sp; left.
  allrw subvars_prop.
  apply_in_hyp p; allsimpl; sp.

  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_product :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isprog (mk_product a v b).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_product; sp.
Qed.

Lemma isprog_product_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_product a v b).
Proof.
  introv; split; intro k; try (apply isprog_product; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (autodimp i1 hyp).
  repeat (autodimp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_lam :
  forall v b,
    isprog_vars [v] b
    -> isprogram (mk_lam v b).
Proof.
  sp.
  allrw isprog_vars_eq; sp.
  constructor.
  unfold closed; simpl.
  rw app_nil_r.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
  allrw subvars_eq.
  allrw subset_singleton_r.
  apply_in_hyp p; sp.
  constructor; allsimpl; sp; subst.
  constructor; sp.
Qed.

Lemma isprog_lam :
  forall v b,
    isprog_vars [v] b
    -> isprog (mk_lam v b).
Proof.
  sp; allrw isprog_eq; apply isprogram_lam; sp.
Qed.

Lemma isprog_id :
  isprog mk_id.
Proof.
  unfold mk_id; sp; apply isprog_lam.
Qed.

Hint Immediate isprog_id.

Lemma isprog_vsubtype :
  forall a v b,
    isprog a
    -> isprog b
    -> isprog (mk_vsubtype a v b).
Proof.
  unfold mk_vsubtype; sp.
  apply isprog_member; sp.
  apply isprog_function; sp.
  allrw isprog_eq.
  inversion H0.
  allunfold closed.
  allrw isprog_vars_eq; simpl.
  allrw; sp.
Qed.

Lemma isprog_subtype :
  forall a b,
    isprog a
    -> isprog b
    -> isprog (mk_subtype a b).
Proof.
  unfold mk_subtype; sp.
  apply isprog_member.
  apply isprog_lam.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp; simpl.
  apply isprog_function; sp.
  allrw isprog_eq.
  inversion H0.
  allunfold closed.
  rw isprog_vars_eq; sp.
  allrw; sp.
Qed.

Lemma isprog_fun :
  forall a b,
    isprog a
    -> isprog b
    -> isprog (mk_fun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_function; sp.
  allrw isprog_vars_eq; sp; simpl.
  allrw isprog_eq.
  inversion ipb.
  allunfold closed.
  allrw; sp.
  allrw isprog_eq; allunfold isprogram; sp.
Qed.

Lemma isprog_ufun :
  forall a b,
    isprog a
    -> isprog b
    -> isprog (mk_ufun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_isect; sp.
  allrw isprog_vars_eq; sp; simpl.
  allrw isprog_eq.
  inversion ipb.
  allunfold closed.
  allrw; sp.
  allrw isprog_eq; allunfold isprogram; sp.
Qed.

Lemma isprog_eufun :
  forall a b,
    isprog a
    -> isprog b
    -> isprog (mk_eufun a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_eisect; sp.
  allrw isprog_vars_eq; sp; simpl.
  allrw isprog_eq.
  inversion ipb.
  allunfold closed.
  allrw; sp.
  allrw isprog_eq; allunfold isprogram; sp.
Qed.

Lemma isprog_prod :
  forall a b,
    isprog a
    -> isprog b
    -> isprog (mk_prod a b).
Proof.
  unfold mk_fun; introv ipa ipb.
  apply isprog_product; sp.
  allrw isprog_vars_eq; sp; simpl.
  allrw isprog_eq.
  inversion ipb.
  allunfold closed.
  allrw; sp.
  allrw isprog_eq; allunfold isprogram; sp.
Qed.

Lemma wf_rec :
  forall v a, wf_term a -> wf_term (mk_rec v a).
Proof.
  intros v a; repeat (rw <- nt_wf_eq).
  intros nta; inversion nta; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_rec :
  forall v a,
    subvars (free_vars a) [v]
    -> nt_wf a
    -> isprogram (mk_rec v a).
Proof.
  sp.
  unfold isprogram, mk_rec, closed; simpl; sp.

  rw <- null_iff_nil.
  repeat (rw null_app).
  rw null_nil_iff.
  allrw subvars_prop; allsimpl; sp.
  rw null_remove_nvars; simpl; sp.
  constructor; simpl; allunfold isprogram; sp; subst; constructor; sp.
Qed.

Lemma isprog_rec :
  forall v a,
    isprog_vars [v] a
    -> isprog (mk_rec v a).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.
  apply isprogram_rec; sp.
Qed.

Theorem wf_product :
  forall a v b, wf_term a -> wf_term b -> wf_term (mk_product a v b).
Proof.
  intros a v B; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_int_implies :
  forall bterms,
    isprogram (oterm (Can NInt) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [ cl w ].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil; allsimpl.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_nat_implies :
  forall bterms n,
    isprogram (oterm (Can (Nint n)) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_base_implies :
  forall bterms,
    isprogram (oterm (Can NBase) bterms)
    -> bterms = [].
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [| o lnt k e]; subst; allsimpl.
  allrw <- null_iff_nil.
  allrw null_map.
  allrw null_iff_nil; auto.
Qed.

Lemma isprogram_approx_implies :
  forall bterms,
    isprogram (oterm (Can NApprox) bterms)
    -> {a, b : NTerm $
         bterms = [nobnd a, nobnd b]}.
Proof.
  introv isp; inversion isp as [cl w].
  inversion w as [|o lnt k e]; subst; allsimpl.
  destruct bterms; allsimpl; sp.
  destruct bterms; allsimpl; sp.
  destruct bterms; allsimpl; sp.
  destruct b; destruct b0; allunfold num_bvars; allsimpl.
  inversion e as [len].
  rewrite len in H.
  repeat (allrw length0; subst; allsimpl).
  unfold nobnd.
  exists n n0; auto.
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

Definition get_wterm (t : WTerm) := let (a,_) := t in a.
Definition get_cvterm (vs : list NVar) (t : CVTerm vs) := let (a,_) := t in a.
Definition get_bcterm (bt : BCTerm) := let (a,_) := bt in a.

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

Lemma wf_cterm :
  forall t, wf_term (get_cterm t).
Proof.
  introv; destruct_cterms; simpl.
  allrw isprog_eq; allunfold isprogram; repnd; allrw nt_wf_eq; sp.
Qed.
Hint Immediate wf_cterm : wf.

Lemma free_vars_cterm :
  forall t, free_vars (get_cterm t) = [].
Proof.
  introv; destruct_cterms; simpl.
  allrw isprog_eq; allunfold isprogram; repnd; allrw; sp.
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

Ltac clear_deps h :=
  repeat match goal with
           | [ H : context[h] |- _ ] => clear H
         end.

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

Definition mkc_int : CTerm :=
  exist isprog mk_int isprog_int.
Definition mkw_int : WTerm :=
  exist wf_term mk_int wf_int.

Definition mkc_integer (n : Z) : CTerm :=
  exist isprog (mk_integer n) (isprog_mk_integer n).
Definition mkw_integer (n : Z) : WTerm :=
  exist wf_term (mk_integer n) (wf_mk_integer n).

Lemma mkc_integer_eq :
  forall a b,
    mkc_integer a = mkc_integer b
    -> a = b.
Proof.
  unfold mkc_integer; sp.
  inversion H; sp.
Qed.

Definition mkc_nat (n : nat) : CTerm :=
  exist isprog (mk_nat n) (isprog_mk_nat n).
Definition mkw_nat (n : nat) : WTerm :=
  exist wf_term (mk_nat n) (wf_mk_nat n).

Definition mkc_uni (i : nat) : CTerm :=
  exist isprog (mk_uni i) (isprog_mk_uni i).
Definition mkw_uni (i : nat) : WTerm :=
  exist wf_term (mk_uni i) (wf_mk_uni i).

Lemma mkc_uni_eq :
  forall a b,
    mkc_uni a = mkc_uni b
    -> a = b.
Proof.
  unfold mkc_uni; sp.
  inversion H; sp.
Qed.

Definition mkc_base : CTerm :=
  exist isprog mk_base isprog_base.
Definition mkw_base : WTerm :=
  exist wf_term mk_base wf_base.

Definition mkc_axiom : CTerm :=
  exist isprog mk_axiom isprog_axiom.
Definition mkw_axiom : WTerm :=
  exist wf_term mk_axiom wf_axiom.

Lemma isprogram_pair :
  forall a b,
    isprogram a
    -> isprogram b
    -> isprogram (mk_pair a b).
Proof.
  introv pa pb.
  inversion pa; inversion pb.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_pair :
  forall a b, isprog a -> isprog b -> isprog (mk_pair a b).
Proof.
  sp; allrw isprog_eq; apply isprogram_pair; sp.
Qed.

Definition mkc_pair (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_pair a b) (isprog_pair a b x y).

Theorem wf_sup :
  forall a b, wf_term a -> wf_term b -> wf_term (mk_sup a b).
Proof.
  intros a b; repeat (rw <- nt_wf_eq).
  intros nta ntb; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma isprogram_sup :
  forall a b,
    isprogram a
    -> isprogram b
    -> isprogram (mk_sup a b).
Proof.
  introv pa pb.
  inversion pa; inversion pb.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprogram_sup_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_sup a b).
Proof.
  intros; split; intro i.
  apply isprogram_sup; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_sup :
  forall a b, isprog a -> isprog b -> isprog (mk_sup a b).
Proof.
  sp; allrw isprog_eq; apply isprogram_sup; sp.
Qed.

Definition mkc_sup (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_sup a b) (isprog_sup a b x y).

Lemma mkc_sup_eq :
  forall a b c d,
    mkc_sup a b = mkc_sup c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkc_sup.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_pair_eq :
  forall a b c d,
    mkc_pair a b = mkc_pair c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkc_pair.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_union (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_union a b) (isprog_union a b x y).

Lemma mkc_union_eq :
  forall A1 A2 B1 B2,
    mkc_union A1 A2 = mkc_union B1 B2
    -> A1 = B1 # A2 = B2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i2 = i0) by apply isprog_proof_irrelevance; subst; sp.
  assert (i1 = i) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Lemma isprog_unit : isprog mk_unit.
Proof.
  sp.
Qed.

Hint Immediate isprog_unit.

Definition mkc_bool : CTerm :=
  exist isprog mk_bool (isprog_union mk_unit mk_unit isprog_unit isprog_unit).

Lemma isprogram_inl :
  forall a, isprogram a -> isprogram (mk_inl a).
Proof.
  introv pa.
  inversion pa.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_inl :
  forall a, isprog a -> isprog (mk_inl a).
Proof.
  sp; allrw isprog_eq; apply isprogram_inl; sp.
Qed.

Definition mkc_inl (t : CTerm) : CTerm :=
  let (a,x) := t in exist isprog (mk_inl a) (isprog_inl a x).

Lemma isprogram_inr :
  forall a, isprogram a -> isprogram (mk_inr a).
Proof.
  introv pa.
  inversion pa.
  constructor; simpl.

  unfold closed; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allunfold closed; allrw; simpl; sp.

  constructor; simpl; sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_inr :
  forall a, isprog a -> isprog (mk_inr a).
Proof.
  sp; allrw isprog_eq; apply isprogram_inr; sp.
Qed.

Definition mkc_inr (t : CTerm) : CTerm :=
  let (a,x) := t in exist isprog (mk_inr a) (isprog_inr a x).

Lemma mkc_inl_eq :
  forall a b,
    mkc_inl a = mkc_inl b
    -> a = b.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_inr_eq :
  forall a b,
    mkc_inr a = mkc_inr b
    -> a = b.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_pertype (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_pertype a) (isprog_pertype a x).
Definition mkw_pertype (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_pertype a) (wf_pertype a x).

Lemma mkc_pertype_eq :
  forall R1 R2, mkc_pertype R1 = mkc_pertype R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_partial (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_partial a) (isprog_partial a x).
Definition mkw_partial (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_partial a) (wf_partial a x).

Lemma mkc_partial_eq :
  forall R1 R2, mkc_partial R1 = mkc_partial R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_ipertype (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_ipertype a) (isprog_ipertype a x).
Definition mkw_ipertype (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_ipertype a) (wf_ipertype a x).

Lemma mkc_ipertype_eq :
  forall R1 R2, mkc_ipertype R1 = mkc_ipertype R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_spertype (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_spertype a) (isprog_spertype a x).
Definition mkw_spertype (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_spertype a) (wf_spertype a x).

Lemma mkc_spertype_eq :
  forall R1 R2, mkc_spertype R1 = mkc_spertype R2 -> R1 = R2.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_tuni (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_tuni a) (isprog_tuni a x).

Lemma mkc_tuni_eq :
  forall R1 R2, mkc_tuni R1 = mkc_tuni R2 -> R1 = R2.
Proof.
  introv h.
  destruct_cterms; allsimpl.
  inversion h; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

(*
Definition mkc_esquash (R : CTerm) : CTerm :=
  let (a,x) := R in
    exist isprog (mk_esquash a) (isprog_esquash a x).
Definition mkw_esquash (R : WTerm) : WTerm :=
  let (a,x) := R in
    exist wf_term (mk_esquash a) (wf_esquash a x).

Lemma mkc_esquash_eq :
  forall R1 R2, mkc_esquash R1 = mkc_esquash R2 -> R1 = R2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
*)

Definition mkc_isinl (t1 t2 t3 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isinl a b c) (isprog_isinl a b c x y z).

Lemma mkc_isinl_eq :
  forall a b c d e f,
    mkc_isinl a b c = mkc_isinl d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i4 = i1) by apply isprog_proof_irrelevance; subst.
  assert (i3 = i0) by apply isprog_proof_irrelevance; subst; sp.
  assert (i2 = i) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_isinr (t1 t2 t3 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isinr a b c) (isprog_isinr a b c x y z).

Lemma mkc_isinr_eq :
  forall a b c d e f,
    mkc_isinr a b c = mkc_isinr d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i4 = i1) by apply isprog_proof_irrelevance; subst.
  assert (i3 = i0) by apply isprog_proof_irrelevance; subst; sp.
  assert (i2 = i) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_ispair (t1 t2 t3 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_ispair a b c) (isprog_ispair a b c x y z).

Lemma mkc_ispair_eq :
  forall a b c d e f,
    mkc_ispair a b c = mkc_ispair d e f
    -> a = d # b = e # c = f.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i4 = i1) by apply isprog_proof_irrelevance; subst.
  assert (i3 = i0) by apply isprog_proof_irrelevance; subst; sp.
  assert (i2 = i) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mk_approx_c (t1 t2 : CTerm) : NTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    mk_approx a b.
Definition mkc_approx (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_approx a b) (isprog_approx a b x y).
Definition mkw_approx (t1 t2 : WTerm) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_approx a b) (wf_approx a b x y).
Lemma mkw_approx_eq :
  forall a b c d,
    mkw_approx a b = mkw_approx c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkw_approx.
  inversion H; subst.
  assert (w1 = w) by apply wf_term_proof_irrelevance; subst.
  assert (w0 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_approx_eq :
  forall a b c d,
    mkc_approx a b = mkc_approx c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkc_approx.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_cequiv (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_cequiv a b) (isprog_cequiv a b x y).
Definition mkw_cequiv (t1 t2 : WTerm) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_cequiv a b) (wf_cequiv a b x y).
Lemma mkw_cequiv_eq :
  forall a b c d,
    mkw_cequiv a b = mkw_cequiv c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkw_cequiv.
  inversion H; subst.
  assert (w1 = w) by apply wf_term_proof_irrelevance; subst.
  assert (w0 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_cequiv_eq :
  forall a b c d,
    mkc_cequiv a b = mkc_cequiv c d
    -> a = c # b = d.
Proof.
  intros.
  destruct a, b, c, d.
  allunfold mkc_cequiv.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_compute (t1 t2 n : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := n in
    exist isprog (mk_compute a b c) (isprog_compute a b c x y z).
Lemma mkc_compute_eq :
  forall a b c d n m,
    mkc_compute a b n = mkc_compute c d m
    -> a = c # b = d # n = m.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i4 = i2) by apply isprog_proof_irrelevance; subst.
  assert (i3 = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_image (T F : CTerm) : CTerm :=
  let (t,x) := T in
  let (f,y) := F in
    exist isprog (mk_image t f) (isprog_image t f x y).

Lemma mkc_image_eq :
  forall A1 A2 f1 f2,
    mkc_image A1 f1 = mkc_image A2 f2
    -> A1 = A2 # f1 = f2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

(* end hide *)

(**

  Using the [CVTerm] and [CTerm] types we can define useful
  abstraction to build closed versions of the various terms of our
  computation system.  For example, given a variable [v] and a term in
  [CVTerm [v]], we can build a closed lambda abstraction.  As an other
  example, given two closed terms, we can build a closed application
  term.

 *)

Definition mkc_lam (v : NVar) (b : CVTerm [v]) : CTerm :=
  let (t,x) := b in
  exist isprog (mk_lam v t) (isprog_lam v t x).

Definition mkc_apply (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_apply a b) (isprog_apply a b x y).

(* begin hide *)

Lemma mkc_apply_eq :
  forall t1 t2 t3 t4,
    mkc_apply t1 t2 = mkc_apply t3 t4 -> t1 = t3 # t2 = t4.
Proof.
  introv e; destruct_cterms; allsimpl.
  inversion e; subst.
  irr; sp.
Qed.

Definition mkw_apply (t1 t2 : WTerm) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_apply a b) (wf_apply a b x y).

Definition mkc_apply2 (t0 t1 t2 : CTerm) : CTerm :=
  let (f,z) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_apply2 f a b) (isprog_apply2 f a b z x y).

Lemma mkc_apply2_eq :
  forall t0 t1 t2,
    mkc_apply2 t0 t1 t2 = mkc_apply (mkc_apply t0 t1) t2.
Proof.
  intros; destruct_cterms; allsimpl; unfold mk_apply2.
  rewrite dep_pair_eq
          with
          (eq0 := eq_refl)
          (pb := isprog_apply (mk_apply x1 x0) x (isprog_apply x1 x0 i1 i0) i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Theorem wf_apply3 :
  forall f a b c,
    wf_term f
    -> wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term (mk_apply3 f a b c).
Proof.
  unfold mk_apply3; sp.
  repeat (apply wf_apply); auto.
Qed.

Theorem isprogram_apply3 :
  forall f a b c,
    isprogram f
    -> isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_apply3 f a b c).
Proof.
  unfold mk_apply3; sp.
  repeat (apply isprogram_apply); auto.
Qed.

Theorem isprog_apply3 :
  forall f a b c,
    isprog f
    -> isprog a
    -> isprog b
    -> isprog c
    -> isprog (mk_apply3 f a b c).
Proof.
  sp; allrw isprog_eq.
  apply isprogram_apply3; auto.
Qed.

Definition mkc_apply3 (t0 t1 t2 t3 : CTerm) : CTerm :=
  let (f,u) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_apply3 f a b c) (isprog_apply3 f a b c u x y z).

Lemma mkc_apply3_eq :
  forall t0 t1 t2 t3,
    mkc_apply3 t0 t1 t2 t3 = mkc_apply (mkc_apply (mkc_apply t0 t1) t2) t3.
Proof.
  intros; destruct_cterms; allsimpl; unfold mk_apply3.
  rewrite dep_pair_eq
          with
          (eq0 := eq_refl)
          (pb := isprog_apply (mk_apply (mk_apply x2 x1) x0)
                              x
                              (isprog_apply (mk_apply x2 x1)
                                            x0
                                            (isprog_apply x2 x1 i2 i1) i0) i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

(*Definition mkw_apply2 (t0 t1 t2 : WTerm) : WTerm :=
  let (f,z) := t0 in
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist wf_term (mk_apply2 f a b) (wf_apply2 f a b z x y).*)

Definition mkc_equality (t1 t2 T : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist isprog (mk_equality a b c) (isprog_equality a b c x y z).
Definition mkw_equality (t1 t2 T : WTerm) : WTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist wf_term (mk_equality a b c) (wf_equality a b c x y z).
Lemma mkw_equality_eq :
  forall a b c d T U,
    mkw_equality a b T = mkw_equality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold mkw_equality.
  inversion H; subst.
  assert (w1 = w) by apply wf_term_proof_irrelevance; subst.
  assert (w0 = w2) by apply wf_term_proof_irrelevance; subst.
  assert (w3 = w4) by apply wf_term_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_equality_eq :
  forall a b c d T U,
    mkc_equality a b T = mkc_equality c d U
    -> a = c # b = d # T = U.
Proof.
  intros.
  destruct a, b, c, d, T, U.
  allunfold mkc_equality.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst.
  assert (i3 = i4) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_member (t T : CTerm) : CTerm :=
  let (a,x) := t in
  let (b,y) := T in
    exist isprog (mk_member a b) (isprog_member a b x y).

Lemma fold_mkc_member :
  forall t T,
    mkc_equality t t T = mkc_member t T.
Proof.
  unfold mkc_member, mkc_equality, mk_member; sp; destruct t; destruct T.
  rewrite dep_pair_eq with (eq0 := eq_refl) (pb := isprog_member x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_tequality (t1 t2 : CTerm) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_tequality a b) (isprog_tequality a b x y).

Lemma mkc_tequality_eq :
  forall a b c d,
    mkc_tequality a b = mkc_tequality c d
    -> a = c # b = d.
Proof.
  intros.
  destruct_cterms.
  allunfold mkc_tequality.
  inversion H; subst.
  assert (i = i1) by apply isprog_proof_irrelevance; subst.
  assert (i0 = i2) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Definition mkc_type (t : CTerm) : CTerm :=
  let (a,x) := t in exist isprog (mk_type a) (isprog_type a x).

Lemma fold_mkc_type :
  forall t, mkc_tequality t t = mkc_type t.
Proof.
  unfold mkc_type, mkc_tequality, mk_type; sp; destruct t.
  rewrite dep_pair_eq with (eq0 := eq_refl) (pb := isprog_type x i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_cbv (t1 : CTerm) (v : NVar) (t2 : CVTerm [v]) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_cbv a v b) (isprog_cbv a v b x y).

Definition mkc_halts (t : CTerm) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_halts a) (isprog_halts a x).

Lemma isprog_vars_axiom :
  forall v,
    isprog_vars [v] mk_axiom.
Proof.
  unfold isprog_vars; sp.
Qed.

Definition mkcv_axiom (v : NVar) : CVTerm [v] :=
  exist (isprog_vars [v]) mk_axiom (isprog_vars_axiom v).

Lemma fold_mkc_halts :
  forall t,
    mkc_approx mkc_axiom (mkc_cbv t nvarx (mkcv_axiom nvarx)) = mkc_halts t.
Proof.
  unfold mkc_halts, mkc_approx, mk_halts; destruct t; simpl.
  rewrite dep_pair_eq with (eq0 := eq_refl) (pb := isprog_halts x i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma isprogram_spread :
  forall a v1 v2 b,
    isprogram a
    -> subvars (free_vars b) [v1,v2]
    -> nt_wf b
    -> isprogram (mk_spread a v1 v2 b).
Proof.
  unfold isprogram, closed; introv ipa sv ntb; repnd; simpl.
  allrw; simpl.
  allrw subvars_prop; allsimpl.
  allrw app_nil_r.
  rw <- null_iff_nil; rw null_remove_nvars.
  dands.

  introv i.
  apply sv in i; sp.

  constructor; simpl.

  introv e; repdors; subst; try (complete sp).
  constructor; sp.

  constructor.
Qed.

Lemma isprog_spread :
  forall a v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_spread a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw isprog_eq.
  allrw isprog_vars_eq.
  apply isprogram_spread; sp.
Qed.

Definition mkc_spread
           (t1 : CTerm)
           (v1 v2 : NVar)
           (t2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x1) := t1 in
  let (b,x2) := t2 in
    exist isprog (mk_spread a v1 v2 b) (isprog_spread a v1 v2 b x1 x2).

Lemma mkc_spread_eq1 :
  forall a1 x1 y1 b1 a2 x2 y2 b2,
    mkc_spread a1 x1 y1 b1 = mkc_spread a2 x2 y2 b2
    -> a1 = a2 # x1 = x2 # y1 = y2.
Proof.
  introv e.
  destruct a1, a2, b1, b2.
  allunfold mkc_spread.
  inversion e; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_spread_eq2 :
  forall a x y b1 b2,
    mkc_spread a x y b1 = mkc_spread a x y b2
    -> b1 = b2.
Proof.
  introv e.
  destruct a, b1, b2.
  allunfold mkc_spread.
  inversion e; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Lemma isprogram_dsup :
  forall a v1 v2 b,
    isprogram a
    -> subvars (free_vars b) [v1,v2]
    -> nt_wf b
    -> isprogram (mk_dsup a v1 v2 b).
Proof.
  unfold isprogram, closed; introv ipa sv ntb; repnd; simpl.
  allrw; simpl.
  allrw subvars_prop; allsimpl.
  allrw app_nil_r.
  rw <- null_iff_nil; rw null_remove_nvars.
  dands.

  introv i.
  apply sv in i; sp.

  constructor; simpl.

  introv e; repdors; subst; try (complete sp).
  constructor; sp.

  constructor.
Qed.

Lemma isprog_dsup :
  forall a v1 v2 b,
    isprog a
    -> isprog_vars [v1,v2] b
    -> isprog (mk_dsup a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw isprog_eq.
  allrw isprog_vars_eq.
  apply isprogram_dsup; sp.
Qed.

Definition mkc_dsup
           (t1 : CTerm)
           (v1 v2 : NVar)
           (t2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x1) := t1 in
  let (b,x2) := t2 in
    exist isprog (mk_dsup a v1 v2 b) (isprog_dsup a v1 v2 b x1 x2).



Lemma isprogram_decide :
  forall a v1 a1 v2 a2,
    isprogram a
    -> subvars (free_vars a1) [v1]
    -> nt_wf a1
    -> subvars (free_vars a2) [v2]
    -> nt_wf a2
    -> isprogram (mk_decide a v1 a1 v2 a2).
Proof.
  unfold isprogram, closed; introv ipa sv1 nt1 sv2 nt2; repnd; simpl.
  allrw; simpl.
  allrw subvars_eq.
  unfold subset in sv1, sv2; sp.
  assert (remove_nvars [v1] (free_vars a1) = []) as eq1.
  rw <- null_iff_nil; rw null_remove_nvars; introv ia1.
  apply sv1 in ia1; sp.
  assert (remove_nvars [v2] (free_vars a2) = []) as eq2.
  rw <- null_iff_nil; rw null_remove_nvars; introv ia2.
  apply sv2 in ia2; sp.
  rw eq1; rw eq2; sp.
  repeat (constructor; simpl; sp; subst).
Qed.

Lemma isprog_decide :
  forall a v1 a1 v2 a2,
    isprog a
    -> isprog_vars [v1] a1
    -> isprog_vars [v2] a2
    -> isprog (mk_decide a v1 a1 v2 a2).
Proof.
  introv ipa ipa1 ipa2.
  allrw isprog_eq.
  allrw isprog_vars_eq.
  apply isprogram_decide; sp.
Qed.

Definition mkc_decide
           (t : CTerm)
           (v1 : NVar)
           (t1 : CVTerm [v1])
           (v2 : NVar)
           (t2 : CVTerm [v2]) : CTerm :=
  let (a,x) := t in
  let (a1,x1) := t1 in
  let (a2,x2) := t2 in
    exist isprog (mk_decide a v1 a1 v2 a2) (isprog_decide a v1 a1 v2 a2 x x1 x2).

Definition mkc_ite (a b c : CTerm) :=
  let (t1,x1) := a in
  let (t2,x2) := b in
  let (t3,x3) := c in
  exist isprog
        (mk_decide t1 nvarx t2 nvarx t3)
        (isprog_decide t1 nvarx t2 nvarx t3
                       x1
                       (isprog_vars_if_isprog [nvarx] t2 x2)
                       (isprog_vars_if_isprog [nvarx] t3 x3)).

Lemma mkc_ite_eq_mkc_decide :
  forall a b c,
    mkc_ite a b c = mkc_decide a nvarx (mk_cv [nvarx] b) nvarx (mk_cv [nvarx] c).
Proof.
  intros.
  destruct_cterms; allsimpl.
  rewrite dep_pair_eq
          with
          (eq0 := eq_refl)
            (pb := isprog_decide x1 nvarx x0 nvarx x i1
                                 (mk_cv_pf [nvarx] (exist (fun t : NTerm => isprog t) x0 i0))
                                 (mk_cv_pf [nvarx] (exist (fun t : NTerm => isprog t) x i))); sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_isect (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_isect a v b) (isprog_isect a v b x y).
Definition mkw_isect (T1 : WTerm) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_isect a v b) (wf_isect a v b x y).
Lemma mkw_isect_eq :
  forall a1 v1 b1 a2 v2 b2,
    mkw_isect a1 v1 b1 = mkw_isect a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkw_isect.
  inversion H; subst.
  assert (w = w0) by apply wf_term_proof_irrelevance; subst.
  assert (w1 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_isect_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_isect a1 v1 b1 = mkc_isect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_isect.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_isect_eq2 :
  forall a v b1 b2,
    mkc_isect a v b1 = mkc_isect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_isect.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_uall := mkc_isect.

Definition mkc_eisect (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_eisect a v b) (isprog_eisect a v b x y).

Lemma mkc_eisect_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_eisect a1 v1 b1 = mkc_eisect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_eisect.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_eisect_eq2 :
  forall a v b1 b2,
    mkc_eisect a v b1 = mkc_eisect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_eisect.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_disect (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_disect a v b) (isprog_disect a v b x y).
Definition mkw_disect (T1 : WTerm) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_disect a v b) (wf_disect a v b x y).
Lemma mkw_disect_eq :
  forall a1 v1 b1 a2 v2 b2,
    mkw_disect a1 v1 b1 = mkw_disect a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkw_disect.
  inversion H; subst.
  assert (w = w0) by apply wf_term_proof_irrelevance; subst.
  assert (w1 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_disect_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_disect a1 v1 b1 = mkc_disect a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_disect.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_disect_eq2 :
  forall a v b1 b2,
    mkc_disect a v b1 = mkc_disect a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_disect.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_set (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_set a v b) (isprog_set a v b x y).

Lemma mkc_set_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_set a1 v1 b1 = mkc_set a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_set.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_set_eq2 :
  forall a v b1 b2,
    mkc_set a v b1 = mkc_set a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_set.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_quotient (T1 : CTerm) (v1 v2 : NVar) (T2 : CVTerm [v1,v2]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_quotient a v1 v2 b) (isprog_quotient a v1 v2 b x y).

Lemma mkc_quotient_eq1 :
  forall a1 v1 u1 b1 a2 v2 u2 b2,
    mkc_quotient a1 v1 u1 b1 = mkc_quotient a2 v2 u2 b2
    -> a1 = a2 # v1 = v2 # u1 = u2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_quotient.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_quotient_eq2 :
  forall a v1 v2 b1 b2,
    mkc_quotient a v1 v2 b1 = mkc_quotient a v1 v2 b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_quotient.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_w (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_w a v b) (isprog_w a v b x y).
Definition mkw_w (T1 : WTerm) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_w a v b) (wf_w a v b x y).
Lemma mkw_w_eq :
  forall a1 v1 b1 a2 v2 b2,
    mkw_w a1 v1 b1 = mkw_w a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkw_w.
  inversion H; subst.
  assert (w = w0) by apply wf_term_proof_irrelevance; subst.
  assert (w1 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_w_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_w a1 v1 b1 = mkc_w a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_w.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_w_eq2 :
  forall a v b1 b2,
    mkc_w a v b1 = mkc_w a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_w.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_m (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_m a v b) (isprog_m a v b x y).
Definition mkw_m (T1 : WTerm) (v : NVar) (T2 : WTerm) : WTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_m a v b) (wf_w a v b x y).
Lemma mkw_m_eq :
  forall a1 v1 b1 a2 v2 b2,
    mkw_m a1 v1 b1 = mkw_m a2 v2 b2
    -> a1 = a2 # v1 = v2 # b1 = b2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkw_m.
  inversion H; subst.
  assert (w = w0) by apply wf_term_proof_irrelevance; subst.
  assert (w1 = w2) by apply wf_term_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_m_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_m a1 v1 b1 = mkc_m a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_w.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_m_eq2 :
  forall a v b1 b2,
    mkc_m a v b1 = mkc_m a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_w.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.



Definition mkc_pw
           (P : CTerm)
           (ap : NVar) (A : CVTerm [ap])
           (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
           (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
           (p : CTerm) : CTerm :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist isprog
          (mk_pw tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_pw tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).


Lemma mkc_pw_eq1 :
  forall P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    mkc_pw P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
    = mkc_pw P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
    -> P1 = P2
       # p1 = p2
       # ap1 = ap2
       # bp1 = bp2
       # ba1 = ba2
       # cp1 = cp2
       # ca1 = ca2
       # cb1 = cb2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma mkc_pw_eq2 :
  forall P ap bp ba cp ca cb p A1 B1 C1 A2 B2 C2,
    mkc_pw P ap A1 bp ba B1 cp ca cb C1 p
    = mkc_pw P ap A2 bp ba B2 cp ca cb C2 p
    -> A1 = A2 # B1 = B2 # C1 = C2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma isprog_vars_pw :
  forall vs P ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp, ba] B
    -> isprog_vars [cp, ca, cb] C
    -> isprog_vars vs p
    -> isprog_vars vs (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  allrw isprog_eq.
  allrw isprog_vars_eq; sp.

  simpl.
  allunfold isprogram; repnd.
  allrw subvars_app_l; allrw remove_nvars_nil_l; allrw; sp;
  allrw subvars_prop; introv i; allrw in_remove_nvars; allrw in_single_iff;
  repnd; discover; allrw in_single_iff; sp.

  constructor; simpl; sp; subst; constructor; sp.
  allunfold isprogram; sp.
Qed.

Definition mkc_pw_vs
             (vs : list NVar)
             (P : CTerm)
             (ap : NVar) (A : CVTerm [ap])
             (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
             (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
             (p : CVTerm vs) : CVTerm vs :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist (isprog_vars vs)
          (mk_pw tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_vars_pw vs tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).

Definition mkc_pm
           (P : CTerm)
           (ap : NVar) (A : CVTerm [ap])
           (bp : NVar) (ba : NVar) (B : CVTerm [bp, ba])
           (cp : NVar) (ca : NVar) (cb : NVar) (C : CVTerm [cp, ca, cb])
           (p : CTerm) : CTerm :=
  let (tP,wP) := P in
  let (tA,wA) := A in
  let (tB,wB) := B in
  let (tC,wC) := C in
  let (tp,wp) := p in
    exist isprog
          (mk_pm tP ap tA bp ba tB cp ca cb tC tp)
          (isprog_pm tP ap tA bp ba tB cp ca cb tC tp wP wA wB wC wp).

Lemma mkc_pm_eq1 :
  forall P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
         P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2,
    mkc_pm P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1
    = mkc_pm P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2
    -> P1 = P2
       # p1 = p2
       # ap1 = ap2
       # bp1 = bp2
       # ba1 = ba2
       # cp1 = cp2
       # ca1 = ca2
       # cb1 = cb2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.

Lemma mkc_pm_eq2 :
  forall P ap bp ba cp ca cb p A1 B1 C1 A2 B2 C2,
    mkc_pm P ap A1 bp ba B1 cp ca cb C1 p
    = mkc_pm P ap A2 bp ba B2 cp ca cb C2 p
    -> A1 = A2 # B1 = B2 # C1 = C2.
Proof.
  introv e.
  destruct_cterms; allsimpl.
  inversion e; subst; irr; sp.
Qed.


Definition mkc_function (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_function a v b) (isprog_function a v b x y).
Definition mkw_function (T1 : WTerm) (v : NVar) (T2 : WTerm) :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_function a v b) (wf_function a v b x y).

Lemma mkc_function_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_function a1 v1 b1 = mkc_function a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_function.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_function_eq2 :
  forall a v b1 b2,
    mkc_function a v b1 = mkc_function a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_function.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Definition mkc_product (T1 : CTerm) (v : NVar) (T2 : CVTerm [v]) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist isprog (mk_product a v b) (isprog_product a v b x y).
Definition mkw_product (T1 : WTerm) (v : NVar) (T2 : WTerm) :=
  let (a,x) := T1 in
  let (b,y) := T2 in
    exist wf_term (mk_product a v b) (wf_product a v b x y).

Lemma mkc_product_eq1 :
  forall a1 v1 b1 a2 v2 b2,
    mkc_product a1 v1 b1 = mkc_product a2 v2 b2
    -> a1 = a2 # v1 = v2.
Proof.
  intros.
  destruct a1, a2, b1, b2.
  allunfold mkc_product.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.
Lemma mkc_product_eq2 :
  forall a v b1 b2,
    mkc_product a v b1 = mkc_product a v b2
    -> b1 = b2.
Proof.
  intros.
  destruct a, b1, b2.
  allunfold mkc_product.
  inversion H; subst.
  assert (i0 = i1) by apply isprog_vars_proof_irrelevance; subst; sp.
Qed.

Lemma isprog_vars_var :
  forall v, isprog_vars [v] (mk_var v).
Proof.
  sp.
  rw isprog_vars_eq; simpl; sp.
Qed.

Definition mkc_var (v : NVar) : CVTerm [v] :=
  exist (isprog_vars [v]) (mk_var v) (isprog_vars_var v).

Definition mkc_vsubtype (T1 : CTerm) (v : NVar) (T2 : CTerm) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
  exist isprog (mk_vsubtype a v b) (isprog_vsubtype a v b x y).

Definition mkc_subtype (T1 : CTerm) (T2 : CTerm) : CTerm :=
  let (a,x) := T1 in
  let (b,y) := T2 in
  exist isprog (mk_subtype a b) (isprog_subtype a b x y).

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

Definition mkc_fun (A B : CTerm) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_fun a b) (isprog_fun a b x y).

Lemma fold_mkc_fun :
  forall A B,
    mkc_function A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_fun A B.
Proof.
  unfold mkc_fun, mk_fun, cnewvar; destruct A, B; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_fun x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_ufun (A B : CTerm) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_ufun a b) (isprog_ufun a b x y).

Lemma fold_mkc_ufun :
  forall A B,
    mkc_isect A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_ufun A B.
Proof.
  unfold mkc_ufun, mk_ufun, cnewvar; destruct A, B; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_ufun x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_eufun (A B : CTerm) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_eufun a b) (isprog_eufun a b x y).

Lemma fold_mkc_eufun :
  forall A B,
    mkc_eisect A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_eufun A B.
Proof.
  unfold mkc_eufun, mk_eufun, cnewvar; destruct A, B; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_eufun x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_prod (A B : CTerm) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_prod a b) (isprog_prod a b x y).

Lemma fold_mkc_prod :
  forall A B,
    mkc_product A (cnewvar B) (mk_cv [cnewvar B] B)
    = mkc_prod A B.
Proof.
  unfold mkc_prod, mk_prod, cnewvar; destruct A, B; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_prod x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_iff a b := mkc_prod (mkc_fun a b) (mkc_fun b a).

Definition mkc_id := mkc_lam nvarx (mkc_var nvarx).

Definition mkc_squash T := mkc_image T (mkc_lam nvarx (mk_cv [nvarx] mkc_axiom)).

Lemma get_cterm_mkc_squash :
  forall T, get_cterm (mkc_squash T) = mk_squash (get_cterm T).
Proof.
  intro; destruct_cterms; sp.
Qed.


Lemma isprogram_fix :
  forall t, isprogram t -> isprogram (mk_fix t).
Proof.
  introv isp.
  repeat constructor; simpl; sp; subst.
  unfold closed; simpl.
  rewrite remove_nvars_nil_l.
  rewrite app_nil_r.
  inversion isp as [cl w]; sp.
  inversion isp; sp.
Qed.

Lemma isprog_fix :
  forall t, isprog t -> isprog (mk_fix t).
Proof.
  intro; repeat (rw isprog_eq); sp.
  apply isprogram_fix; sp.
Qed.

Lemma isprogram_bot :
  isprogram mk_bot.
Proof.
  unfold mk_bot, mk_bottom.
  apply isprogram_fix.
  apply isprogram_lam; simpl.
  apply isprog_vars_var.
Qed.

Lemma isprog_bot :
  isprog mk_bot.
Proof.
  rw isprog_eq.
  apply isprogram_bot.
Qed.

Lemma isprogram_mk_false :
  isprogram mk_false.
Proof.
  unfold mk_false.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_bot.
Qed.

Hint Immediate isprogram_mk_false.

Lemma isprog_mk_false :
  isprog mk_false.
Proof.
  rw isprog_eq.
  apply isprogram_mk_false.
Qed.

Lemma wf_mk_false :
  wf_term mk_false.
Proof.
  sp.
Qed.

Definition mkc_false :=
  exist isprog mk_false isprog_mk_false.

Definition mkc_bot :=
  exist isprog mk_bot isprog_bot.

Definition mkc_fix (t : CTerm) :=
  let (a,x) := t in
    exist isprog (mk_fix a) (isprog_fix a x).

Lemma mkc_bot_eq :
  mkc_bot = mkc_fix mkc_id.
Proof.
  unfold mkc_bot, mkc_fix, mk_bot, mk_bottom; simpl.
  rewrite dep_pair_eq with (eq0 := eq_refl)
          (pb := isprog_fix (mk_lam nvarx (mk_var nvarx))
                            (isprog_lam nvarx (mk_var nvarx) (isprog_vars_var nvarx))); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma mkc_false_eq :
  mkc_false = mkc_approx mkc_axiom mkc_bot.
Proof.
  unfold mkc_false, mkc_approx, mk_false; simpl.
  rewrite dep_pair_eq with (eq0 := eq_refl) (pb := isprog_approx mk_axiom mk_bot isprog_axiom isprog_bot); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Theorem isprogram_void : isprogram mk_void.
Proof.
  unfold mk_void; apply isprogram_mk_false.
Qed.

Theorem isprog_void : isprog mk_void.
Proof.
  unfold mk_void; apply isprog_mk_false.
Qed.

Theorem wf_void : wf_term mk_void.
Proof.
  sp.
Qed.

Definition mkc_void : CTerm := exist isprog mk_void isprog_void.

Definition mkc_unit : CTerm := exist isprog mk_unit isprog_unit.

Lemma mkc_unit_eq : mkc_unit = mkc_approx mkc_axiom mkc_axiom.
Proof.
  unfold mkc_unit, mkc_approx, mk_unit, mk_true; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_approx mk_axiom mk_axiom isprog_axiom isprog_axiom); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

(*
Lemma isprogram_void_implies :
  forall bterms,
    isprogram (oterm (Can NVoid) bterms)
    -> bterms = [].
Proof.
  sp; allunfold isprogram; sp.
  inversion X; subst; allsimpl.
  allrw <- null_iff_nil; allsimpl.
  allrw null_map; sp.
Qed.
*)

Lemma fold_mkc_vsubtype :
  forall A v B,
    mkc_member mkc_id (mkc_function A v (cvterm_var v B))
    = mkc_vsubtype A v B.
Proof.
  unfold mkc_vsubtype, mk_vsubtype; destruct A, B; simpl.
  fold mk_id.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_vsubtype x v x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma fold_mkc_subtype :
  forall A B,
    mkc_member mkc_id (mkc_function A (cnewvar B) (cvterm_newvar B))
    = mkc_subtype A B.
Proof.
  unfold mkc_subtype, mk_subtype, cnewvar; destruct A, B; simpl.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := isprog_subtype x x0 i i0); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition mkc_rec (v : NVar) (t : CVTerm [v]) :=
  let (a,x) := t in
    exist isprog (mk_rec v a) (isprog_rec v a x).
Definition mkw_rec (v : NVar) (t : WTerm) :=
  let (a,x) := t in
    exist wf_term (mk_rec v a) (wf_rec v a x).

Definition isvalue_wft (t : WTerm) :=
  let (a,_) := t in isvalue a.

Definition isovalue_wft (t : WTerm) :=
  let (a,_) := t in isovalue a.

Lemma isvalue_wft_mkw_approx :
  forall t, isvalue_wft (mkw_approx t t).
Proof.
  unfold isvalue_wft, mkw_approx; sp.
  destruct t; simpl.
  apply isvalue_approx.
Abort.

Lemma iscvalue_mkc_nat : forall n : nat, iscvalue (mkc_nat n).
Proof.
  repeat constructor; sp; allsimpl; sp.
Qed.

Theorem iscvalue_mkc_uni : forall i : nat, iscvalue (mkc_uni i).
Proof.
  repeat constructor; sp; allsimpl; sp.
Qed.

Lemma isvalue_wft_mkw_int : isvalue_wft mkw_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isovalue_wft_mkw_int : isovalue_wft mkw_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma iscvalue_mkc_int : iscvalue mkc_int.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Lemma isovalue_wft_mkw_axiom : isovalue_wft mkw_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem iscvalue_mkc_axiom : iscvalue mkc_axiom.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Theorem iscvalue_mkc_base : iscvalue mkc_base.
Proof.
  repeat constructor. intros. allsimpl; sp.
Qed.

Hint Immediate iscvalue_mkc_nat.
Hint Immediate iscvalue_mkc_uni.
Hint Immediate iscvalue_mkc_int.
Hint Immediate iscvalue_mkc_axiom.
Hint Immediate iscvalue_mkc_base.

Lemma isovalue_wft_mkw_approx :
  forall t1 t2, isovalue_wft (mkw_approx t1 t2).
Proof.
  intro; destruct t1; destruct t2; simpl.
  apply isovalue_approx; allrw nt_wf_eq; auto.
Qed.

Lemma iscvalue_mkc_approx :
  forall t1 t2, iscvalue (mkc_approx t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_approx; allrw isprog_eq; auto.
Qed.

Lemma isovalue_wft_mkw_cequiv :
  forall t1 t2, isovalue_wft (mkw_cequiv t1 t2).
Proof.
  intro; destruct t1; destruct t2; simpl.
  apply isovalue_cequiv; allrw nt_wf_eq; auto.
Qed.

Lemma iscvalue_mkc_cequiv :
  forall t1 t2, iscvalue (mkc_cequiv t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_cequiv; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_union :
  forall t1 t2, iscvalue (mkc_union t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_union; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_image :
  forall t1 t2, iscvalue (mkc_image t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_image; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_pertype :
  forall t, iscvalue (mkc_pertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_pertype; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_partial :
  forall t, iscvalue (mkc_partial t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_partial; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_ipertype :
  forall t, iscvalue (mkc_ipertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_ipertype; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_spertype :
  forall t, iscvalue (mkc_spertype t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_spertype; allrw isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_tuni :
  forall t, iscvalue (mkc_tuni t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_tuni; allrw isprog_eq; auto.
Qed.

(*
Lemma iscvalue_mkc_esquash :
  forall t, iscvalue (mkc_esquash t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_esquash; allrw isprog_eq; auto.
Qed.
*)

Lemma mkw_integer_eq_nat :
  forall n,
    mkw_integer (Z.of_nat n) = mkw_nat n.
Proof.
  sp.
Qed.

Lemma iscvalue_mkc_equality :
  forall t1 t2 T, iscvalue (mkc_equality t1 t2 T).
Proof.
  intro; destruct t1; destruct t2; destruct T; unfold iscvalue; simpl.
  apply isvalue_equality; allrw isprog_eq; auto.
  apply isprogram_equality; sp.
Qed.

Lemma isvalue_function :
  forall a v b, isprogram (mk_function a v b) -> isvalue (mk_function a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_product :
  forall a v b, isprogram (mk_product a v b) -> isvalue (mk_product a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_isect :
  forall a v b, isprogram (mk_isect a v b) -> isvalue (mk_isect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_eisect :
  forall a v b, isprogram (mk_eisect a v b) -> isvalue (mk_eisect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_disect :
  forall a v b, isprogram (mk_disect a v b) -> isvalue (mk_disect a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_set :
  forall a v b, isprogram (mk_set a v b) -> isvalue (mk_set a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_w :
  forall a v b, isprogram (mk_w a v b) -> isvalue (mk_w a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_m :
  forall a v b, isprogram (mk_m a v b) -> isvalue (mk_m a v b).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_pw :
  forall P ap A bp ba B cp ca cb C p,
    isprogram (mk_pw P ap A bp ba B cp ca cb C p)
    -> isvalue (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp; constructor; sp.
Qed.

Lemma isvalue_pm :
  forall P ap A bp ba B cp ca cb C p,
    isprogram (mk_pm P ap A bp ba B cp ca cb C p)
    -> isvalue (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp; constructor; sp.
Qed.

Lemma implies_isvalue_function :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_function a v b).
Proof.
  sp.
  apply isvalue_function.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_function; sp.
Qed.

Lemma implies_isvalue_product :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_product a v b).
Proof.
  sp.
  apply isvalue_product.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_product; sp.
Qed.

Lemma implies_isvalue_isect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_isect a v b).
Proof.
  sp.
  apply isvalue_isect.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_isect; sp.
Qed.

Lemma implies_isvalue_eisect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_eisect a v b).
Proof.
  sp.
  apply isvalue_eisect.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_eisect; sp.
Qed.

Lemma implies_isvalue_disect :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_disect a v b).
Proof.
  sp.
  apply isvalue_disect.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_disect; sp.
Qed.

Lemma implies_isvalue_set :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_set a v b).
Proof.
  sp.
  apply isvalue_set.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_set; sp.
Qed.

Lemma implies_isvalue_w :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_w a v b).
Proof.
  sp.
  apply isvalue_w.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_w; sp.
Qed.

Lemma implies_isvalue_m :
  forall a v b,
    isprog a
    -> isprog_vars [v] b
    -> isvalue (mk_m a v b).
Proof.
  sp.
  apply isvalue_m.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_m; sp.
Qed.

Lemma implies_isvalue_pw :
  forall P ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp,ba] B
    -> isprog_vars [cp,ca,cb] C
    -> isprog p
    -> isvalue (mk_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  apply isvalue_pw.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_pw; sp.
Qed.

Lemma implies_isvalue_pm :
  forall P ap A bp ba B cp ca cb C p,
    isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp,ba] B
    -> isprog_vars [cp,ca,cb] C
    -> isprog p
    -> isvalue (mk_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp.
  apply isvalue_pm.
  allrw isprog_vars_eq; sp.
  allrw isprog_eq.
  apply isprogram_pm; sp.
Qed.

Lemma iscvalue_mkc_function :
  forall a v b, iscvalue (mkc_function a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_function; sp.
Qed.
Hint Immediate iscvalue_mkc_function.

Lemma iscvalue_mkc_product :
  forall a v b, iscvalue (mkc_product a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_product; sp.
Qed.
Hint Immediate iscvalue_mkc_product.

Lemma iscvalue_mkc_isect :
  forall a v b, iscvalue (mkc_isect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_isect; sp.
Qed.
Hint Immediate iscvalue_mkc_isect.

Lemma iscvalue_mkc_eisect :
  forall a v b, iscvalue (mkc_eisect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_eisect; sp.
Qed.
Hint Immediate iscvalue_mkc_eisect.

Lemma iscvalue_mkc_disect :
  forall a v b, iscvalue (mkc_disect a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_disect; sp.
Qed.
Hint Immediate iscvalue_mkc_disect.

Lemma iscvalue_mkc_set :
  forall a v b, iscvalue (mkc_set a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_set; sp.
Qed.
Hint Immediate iscvalue_mkc_set.

Lemma iscvalue_mkc_w :
  forall a v b, iscvalue (mkc_w a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_w; sp.
Qed.
Hint Immediate iscvalue_mkc_w.

Lemma iscvalue_mkc_m :
  forall a v b, iscvalue (mkc_m a v b).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_m; sp.
Qed.
Hint Immediate iscvalue_mkc_m.

Lemma iscvalue_mkc_pw :
  forall P ap A bp ba B cp ca cb C p, iscvalue (mkc_pw P ap A bp ba B cp ca cb C p).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_pw; sp.
Qed.
Hint Immediate iscvalue_mkc_pw.

Lemma iscvalue_mkc_pm :
  forall P ap A bp ba B cp ca cb C p, iscvalue (mkc_pm P ap A bp ba B cp ca cb C p).
Proof.
  sp; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_pm; sp.
Qed.
Hint Immediate iscvalue_mkc_pm.



(* ---------------------------------------------------- *)


Definition list_rel {A} {B} (R : A -> B -> Prop) (ll : list A) (lr : list B) :=
  (length ll = length lr)
  #
  forall p1  p2 , LIn (p1, p2) (combine ll lr)
                  -> R p1 p2.

(** gets the nth element of a list of bterms. if n is out of range, it returns the variable x
*)
Definition selectbt (bts: list BTerm) (n:nat) : BTerm :=
  nth n bts (bterm [] (vterm nvarx)).

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

(*
Theorem isprogram_bt_iff : forall  (bt:BTerm ) , (isprogram_bt bt) <=>
forall (lnt : list NTerm) ,
    (forall nt: NTerm, (LIn nt lnt) -> isprogram nt)
   -> isprogram (apply_bterm  bt lnt ).
 intros. destruct bt as [lv nt].
 induction nt as [v| c bts] using NTerm_better_ind;
  [ Case_aux Case "vterm"
  | Case_aux Case "oterm"
  ].
 remember (memberb eq_var_dec v lv) as vinlv.
 destruct vinlv. fold assert () in Heqvinlv.
 sp_iff SCase.
  SCase "->".
   intros Hisp ? Hin.

*)




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
  introv Hpr Hop. allunfold isprogram. repnd. split;auto. unfold closed. simpl.
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

Hint Immediate isprogram_get_cterm.

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
  allunfold selectbt. allsimpl.
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
Hint Immediate deq_nterm.

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

Tactic Notation "disjoint_reasoningv" :=
  (allunfold all_vars); repeat( progress disjoint_reasoning).

Lemma isprog_vars_top :
  forall vs, isprog_vars vs mk_top.
Proof.
  intro; rw isprog_vars_eq; simpl.
  repeat (rw remove_nvars_nil_l); repeat (rw app_nil_r); sp.
  rw nt_wf_eq; sp.
Qed.
Hint Immediate isprog_vars_top.

Lemma isprog_vars_mk_false :
  forall vs, isprog_vars vs mk_false.
Proof.
  intro; rw isprog_vars_eq; simpl.
  repeat (rw remove_nvars_nil_l); repeat (rw app_nil_r); sp.
  rw nt_wf_eq; sp.
Qed.
Hint Immediate isprog_vars_mk_false.

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

Hint Resolve deq_bterm.

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

Lemma isprog_vars_decide :
  forall vs a v1 a1 v2 a2,
    isprog_vars vs a
    -> isprog_vars (v1 :: vs) a1
    -> isprog_vars (v2 :: vs) a2
    -> isprog_vars vs (mk_decide a v1 a1 v2 a2).
Proof.
  introv ipa ipa1 ipa2.
  allrw isprog_vars_eq; allsimpl.
  allrw subvars_eq.
  unfold subset in ipa, ipa1, ipa2; exrepd; sp.
  unfold subset; introv i.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff;
  allsimpl; sp;
  discover; sp; subst; sp.
  repeat (constructor; simpl; sp; subst).
Qed.

Lemma isprog_vars_spread :
  forall vs a v1 v2 b,
    isprog_vars vs a
    -> isprog_vars (v1 :: v2 :: vs) b
    -> isprog_vars vs (mk_spread a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allsimpl.
  allrw subvars_prop; repnd.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  dands.

  introv i.
  allrw in_app_iff.
  allrw in_remove_nvars; allsimpl.
  repdors; sp.
  allrw not_over_or; repnd.
  discover; sp.

  constructor; simpl; try (constructor).
  sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_vars_dsup :
  forall vs a v1 v2 b,
    isprog_vars vs a
    -> isprog_vars (v1 :: v2 :: vs) b
    -> isprog_vars vs (mk_dsup a v1 v2 b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allsimpl.
  allrw subvars_prop; repnd.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  dands.

  introv i.
  allrw in_app_iff.
  allrw in_remove_nvars; allsimpl.
  repdors; sp.
  allrw not_over_or; repnd.
  discover; sp.

  constructor; simpl; try (constructor).
  sp; subst; sp; constructor; sp.
Qed.

Lemma isprog_vars_cons :
  forall v vs t, isprog_vars vs t -> isprog_vars (v :: vs) t.
Proof.
  introv ip.
  allrw isprog_vars_eq.
  allrw subvars_eq; sp.
Qed.

Definition mkc_ite_vars (vs : list NVar) (a b c : CVTerm vs) :=
  let (t1,x1) := a in
  let (t2,x2) := b in
  let (t3,x3) := c in
  exist (isprog_vars vs)
        (mk_decide t1 nvarx t2 nvarx t3)
        (isprog_vars_decide
           vs
           t1 nvarx t2 nvarx t3
           x1
           (isprog_vars_cons nvarx vs t2 x2)
           (isprog_vars_cons nvarx vs t3 x3)).

Definition mkc_lamc v t := mkc_lam v (mk_cv [v] t).

Theorem isvalue_inl :
  forall a, isprogram a -> isvalue (mk_inl a).
Proof.
 intros. constructor. fold (mk_inl a).
 apply isprogram_inl; auto.
Qed.

Lemma iscvalue_mkc_inl :
  forall t, iscvalue (mkc_inl t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_inl; allrw isprog_eq; auto.
Qed.

Theorem isvalue_inr :
  forall a, isprogram a -> isvalue (mk_inr a).
Proof.
 intros. constructor. fold (mk_inr a).
 apply isprogram_inr; auto.
Qed.

Lemma iscvalue_mkc_inr :
  forall t, iscvalue (mkc_inr t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_inr; allrw isprog_eq; auto.
Qed.

Theorem isvalue_sup :
  forall a b, isprogram a -> isprogram b -> isvalue (mk_sup a b).
Proof.
 intros. constructor. fold (mk_sup a b).
 apply isprogram_sup; auto.
Qed.

Lemma iscvalue_mkc_sup :
  forall t1 t2, iscvalue (mkc_sup t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_sup; allrw isprog_eq; auto.
Qed.

Definition is_inl t :=
  match get_cterm t with
    | vterm _ => false
    | oterm (Can NInl) _ => true
    | oterm _ _ => false
  end.

Definition is_inr t :=
  match get_cterm t with
    | vterm _ => false
    | oterm (Can NInr) _ => true
    | oterm _ _ => false
  end.

Lemma get_cterm_mkc_void :
  get_cterm mkc_void = mk_void.
Proof.
  unfold mkc_void; simpl; sp.
Qed.

Lemma isprogram_mk_bot :
  isprogram mk_bot.
Proof.
  repeat constructor; allsimpl; sp; subst.
  repeat constructor; simpl; sp; subst.
  repeat constructor.
Qed.

Hint Immediate isprogram_mk_bot.

Lemma isvalue_mk_void :
  isvalue mk_void.
Proof.
  apply isvalue_approx; sp.
  apply isprogram_axiom.
  apply isprogram_mk_bot.
Qed.

Hint Immediate isvalue_mk_void.

Ltac fold_terms_step :=
  match goal with
    | [ |- context[oterm (Can NAxiom) []] ] => fold mk_axiom
    | [ |- context[mk_approx mk_axiom mk_axiom] ] => fold mk_true
    | [ |- context[mk_approx mk_axiom mk_bot] ] => fold mk_false
    | [ |- context[mk_lam nvarx (mk_var nvarx)] ] => fold mk_id
    | [ |- context[mk_fix mk_id] ] => fold mk_bottom
    | [ |- context[mk_bottom] ] => fold mk_bot
    | [ |- context[bterm [] ?x] ] => fold (nobnd x)
    | [ |- context[vterm ?v] ] => fold (mk_var v)
    | [ |- context[oterm (Can NLambda) [bterm [?v] ?t]] ] => fold (mk_lam v t)
    | [ |- context[oterm (Can NApprox) [nobnd ?a, nobnd ?b]] ] => fold (mk_approx a b)
    | [ |- context[oterm (NCan NDecide) [nobnd ?d, bterm [?x] ?f, bterm [?y] ?g]] ] => fold (mk_decide d x f y g)
    | [ |- context[oterm (NCan NFix) [nobnd ?x]] ] => unfold nobnd; fold (mk_fix x); try (fold nobnd)
  end.

Ltac fold_terms := repeat fold_terms_step.

Definition mkc_idv v := mkc_lam v (mkc_var v).
Definition mkc_botv v := mkc_fix (mkc_idv v).
Definition mkc_voidv v := mkc_approx mkc_axiom (mkc_botv v).

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

Lemma wf_apply_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_apply a b).
Proof.
  introv; split; intro i.
  apply wf_apply; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)); intros k1 k2.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  inversion k1; subst.
  inversion k2; subst; sp.
Qed.

Lemma wf_apply2_iff :
  forall a b c, (wf_term a # wf_term b # wf_term c) <=> wf_term (mk_apply2 a b c).
Proof.
  introv.
  unfold mk_apply2.
  allrw <- wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_apply :
  forall f a vs,
    isprog_vars vs (mk_apply f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  rw subvars_app_l.
  allrw <- wf_term_eq.
  allrw <- wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_apply2 :
  forall f a b vs,
    isprog_vars vs (mk_apply2 f a b)
    <=>
    (isprog_vars vs f # isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  allrw <- wf_term_eq.
  allrw <- wf_apply2_iff; split; sp.
Qed.

Theorem wf_pertype_iff :
  forall a, wf_term a <=> wf_term (mk_pertype a).
Proof.
  intros; split; intro i.
  apply wf_pertype; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_pertype :
  forall f vs,
    isprog_vars vs (mk_pertype f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- wf_term_eq.
  allrw <- wf_pertype_iff; split; sp.
Qed.

Theorem wf_partial_iff :
  forall a, wf_term a <=> wf_term (mk_partial a).
Proof.
  intros; split; intro i.
  apply wf_partial; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intro j.
  repeat (dest_imp j hyp).
  inversion j; subst; sp.
Qed.

Lemma isprog_vars_partial :
  forall f vs,
    isprog_vars vs (mk_partial f) <=> isprog_vars vs f.
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  allrw <- wf_term_eq.
  allrw <- wf_partial_iff; split; sp.
Qed.

Lemma isprog_vars_weak_l :
  forall vs v t,
    isprog_vars vs t -> isprog_vars (snoc vs v) t.
Proof.
  introv i.
  allrw isprog_vars_eq; sp.
  apply subvars_snoc_weak; sp.
Qed.

Lemma isprog_vars_weak_r :
  forall vs v,
    isprog_vars (snoc vs v) (mk_var v).
Proof.
  introv.
  allrw isprog_vars_eq; sp; allsimpl.
  rw subvars_singleton_l; rw in_snoc; sp.
Qed.
Hint Immediate isprog_vars_weak_r.

Lemma subset_snoc_swap_r :
  forall T vs vs1 vs2 (v : T),
    subset vs (snoc vs1 v ++ vs2)
    <=>
    subset vs (snoc (vs1 ++ vs2) v).
Proof.
  introv; unfold subset; split; intro s; introv i;
  apply s in i; allrw in_snoc; allrw in_app_iff; allrw in_snoc; sp.
Qed.

Lemma subvars_snoc_swap_r :
  forall vs vs1 vs2 v,
    subvars vs (snoc vs1 v ++ vs2)
    <=>
    subvars vs (snoc (vs1 ++ vs2) v).
Proof.
  introv.
  allrw subvars_eq.
  apply subset_snoc_swap_r; sp.
Qed.

Lemma isprog_vars_snoc_swap :
  forall vs1 vs2 v t,
    isprog_vars (snoc vs1 v ++ vs2) t
    <=>
    isprog_vars (snoc (vs1 ++ vs2) v) t.
Proof.
  introv.
  allrw isprog_vars_eq; split; intro i; repnd; sp.
  apply subvars_snoc_swap_r; sp.
  apply subvars_snoc_swap_r; sp.
Qed.

Lemma isprog_vars_lam :
  forall vs v b,
    isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_lam v b).
Proof.
  introv ipv.
  allrw isprog_vars_eq; simpl.
  rw app_nil_r.
  allrw subvars_prop; sp.
  allrw in_remove_nvars; allrw in_single_iff; allsimpl; sp.
  apply_in_hyp p; sp.
  constructor; simpl; sp; subst.
  constructor; sp.
Qed.

Lemma isprog_vars_isect :
  forall vs a v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_isect a v b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_eisect :
  forall vs a v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_eisect a v b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_base :
  forall vs, isprog_vars vs mk_base.
Proof.
  intros.
  rw isprog_vars_eq; simpl; sp.
  constructor; simpl; sp.
Qed.
Hint Immediate isprog_vars_base.

Lemma isprog_vars_equality :
  forall vs a b T,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs T
    -> isprog_vars vs (mk_equality a b T).
Proof.
  introv ipa ipb ipt.
  allrw isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_tequality :
  forall vs a b,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_tequality a b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_mk_var :
  forall vs v, LIn v vs -> isprog_vars vs (mk_var v).
Proof.
  intros.
  rw isprog_vars_eq; simpl; rw subvars_singleton_l; sp.
Qed.

Lemma isvalue_mk_unit :
  isvalue mk_unit.
Proof.
  apply isvalue_approx; sp; apply isprogram_axiom.
Qed.
Hint Immediate isvalue_mk_unit.

Lemma mkc_void_eq_mkc_false :
  mkc_void = mkc_false.
Proof.
  unfold mkc_void, mkc_false.
  rewrite dep_pair_eq with (eq0 := eq_refl)
          (pb := isprog_mk_false); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma iscvalue_mkc_false :
  iscvalue mkc_false.
Proof.
  unfold iscvalue, mkc_false; simpl; sp.
Qed.
Hint Immediate iscvalue_mkc_false.

Lemma isprogram_mk_true :
  isprogram mk_true.
Proof.
  unfold mk_true.
  apply isprogram_approx.
  apply isprogram_axiom.
  apply isprogram_axiom.
Qed.
Hint Immediate isprogram_mk_true.

Lemma isprog_mk_true :
  isprog mk_true.
Proof.
  rw isprog_eq.
  apply isprogram_mk_true.
Qed.
Hint Immediate isprog_mk_true.

Definition mkc_true := exist isprog mk_true isprog_mk_true.

Lemma iscvalue_mkc_true :
  iscvalue mkc_true.
Proof.
  unfold iscvalue, mkc_true; simpl; sp.
Qed.
Hint Immediate iscvalue_mkc_false.

Definition mkc_top := mkc_isect mkc_false nvarx (mk_cv [nvarx] mkc_false).

Lemma get_cterm_mkc_top :
  get_cterm mkc_top = mk_top.
Proof. sp. Qed.

Lemma mkc_true_eq :
  mkc_true = mkc_approx mkc_axiom mkc_axiom.
Proof.
  unfold mkc_true, mkc_approx, mk_true; simpl.
  rewrite dep_pair_eq with (eq0 := eq_refl) (pb := isprog_approx mk_axiom mk_axiom isprog_axiom isprog_axiom); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Ltac rwselectbt :=
match goal with
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite <- H1 in H2
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite H1 in H2
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n  |-  context [selectbt ?lbt ?n] ] => rewrite <- H1
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  |-  context [selectbt ?lbt ?n] ] => rewrite H1
end.

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
  unfold isprogram_bt, closed_bt, isprogram, closed; introns Hxx;  spc; allsimpl.
  inverts Hxx;sp.
Qed.

Lemma mkc_unit_eq_mkc_true :
  mkc_unit = mkc_true.
Proof.
  unfold mkc_unit, mkc_true.
  rewrite dep_pair_eq with (eq0 := eq_refl)
          (pb := isprog_mk_true); auto.
  apply UIP_dec.
  apply bool_dec.
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


Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.
Lemma isprog_ntwf_eauto : forall t, isprogram t -> nt_wf t.
Proof. unfold isprogram. spc.
Qed.
Hint Resolve isprog_ntwf_eauto : slow.

Theorem isprogram_ot_if_eauto :
  forall o bts,
    map num_bvars bts = OpBindings o
    -> (forall bt, LIn bt bts -> isprogram_bt bt)
    -> isprogram (oterm o bts).
Proof.
 intros. apply isprogram_ot_iff;spc.
Qed.

Definition isnoncan (t: NTerm):=
match t with
| vterm _ => False
| oterm o _ => match o with
               | Can _ => False
               | NCan _ => True
               end
end.

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






Ltac d_isnoncan H := 
  match type of H with
    isnoncan ?t => let tlbt := fresh t "lbt" in let tnc := fresh t "nc" in
              let tt := fresh "temp" in 
              destruct t as [tt|tt tlbt];[inverts H as H; fail|];
              destruct tt as [tt|tnc]; [inverts H as H; fail|]
  end.

Hint Resolve isprogram_fix : slow.

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

Hint Immediate nvarx_nvary : slow.

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

Hint Resolve isprogram_ot_if_eauto : slow.

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

Lemma mkc_inl_inr_eq :
  forall a b, mkc_inl a = mkc_inr b -> False.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H.
Qed.

Lemma mkc_inr_inl_eq :
  forall a b, mkc_inr a = mkc_inl b -> False.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H.
Qed.

Lemma closed_implies:
  forall t,
    closed t -> (forall x, !LIn x (free_vars t)).
Proof.
  introv cl.
  unfold closed in cl.
  allrw; simpl; try (complete sp).
Qed.

Lemma isprog_lam_iff :
  forall v b,
    isprog_vars [v] b <=> isprog (mk_lam v b).
Proof.
  introv; split; intro k.
  apply isprog_lam; sp.
  allrw isprog_eq.
  rw isprog_vars_eq.
  unfold isprogram in k; repnd.
  inversion k as [| o lnt j meq ]; allsimpl; subst.
  generalize (j (bterm [v] b)); intro u; dest_imp u hyp.
  inversion u; subst; sp.
  generalize (closed_implies (mk_lam v b) k0); intro i.
  rw subvars_prop; introv y.
  allsimpl.
  destruct (eq_var_dec v x); sp.
  allrw app_nil_r.
  generalize (i x); intro p.
  allrw in_remove_nvars; allrw in_single_iff.
  provefalse.
  apply p; sp.
Qed.

Lemma isprog_vars_lam_iff :
  forall v b vs,
    isprog_vars vs (mk_lam v b) <=> isprog_vars (vs ++ [v]) b.
Proof.
  introv; split; intro k; allrw isprog_vars_eq; allrw nt_wf_eq; repnd; dands;
  allrw <- wf_lam_iff; try (complete sp); allsimpl; allrw app_nil_r; allrw subvars_prop;
  introv i.

  rw in_app_iff; rw in_single_iff.
  destruct (eq_var_dec v x); sp.
  generalize (k0 x).
  rw in_remove_nvars; rw in_single_iff; intro j.
  dest_imp j hyp.

  rw in_remove_nvars in i; rw in_single_iff in i; repnd.
  generalize (k0 x); intro j; dest_imp j hyp.
  rw in_app_iff in j; rw in_single_iff in j; sp.
Qed.

Lemma isprog_vars_isect_iff :
  forall vs a v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_isect a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_isect; sp.
  allrw isprog_vars_eq; allrw nt_wf_eq.
  allrw <- wf_isect_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_eisect_iff :
  forall vs a v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_eisect a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_eisect; sp.
  allrw isprog_vars_eq; allrw nt_wf_eq.
  allrw <- wf_eisect_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_equality_iff :
  forall vs a b T,
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs T)
    <=> isprog_vars vs (mk_equality a b T).
Proof.
  introv; split; intro k.
  apply isprog_vars_equality; sp.
  allrw isprog_vars_eq; allsimpl; allrw nt_wf_eq.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw <- wf_equality_iff.
  allrw subvars_app_l; sp.
Qed.

Lemma isprog_vars_tequality_iff :
  forall vs a b,
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_tequality a b).
Proof.
  introv; split; intro k.
  apply isprog_vars_tequality; sp.
  allrw isprog_vars_eq; allsimpl; allrw nt_wf_eq.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw <- wf_tequality_iff.
  allrw subvars_app_l; sp.
Qed.

Theorem isprog_pertype_iff :
  forall a, isprog a <=> isprog (mk_pertype a).
Proof.
  introv; split; intro k.
  apply isprog_pertype; sp.
  allrw isprog_eq; allunfold isprogram; allrw nt_wf_eq.
  allrw <- wf_pertype_iff; sp.
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_vars_base_iff :
  forall vs, isprog_vars vs mk_base <=> True.
Proof.
  intros.
  rw isprog_vars_eq; simpl; sp; split; sp.
  constructor; simpl; sp.
Qed.

Lemma isprog_vars_var_if :
  forall v vs, LIn v vs -> isprog_vars vs (mk_var v).
Proof.
  sp.
  rw isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp.
Qed.

Lemma isprog_vars_var_if2 :
  forall v vs, LIn v vs -> isprog_vars vs (mk_var v) <=> True.
Proof.
  sp.
  rw isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp.
Qed.

Lemma isprog_vars_var_iff :
  forall v vs, LIn v vs <=> isprog_vars vs (mk_var v).
Proof.
  sp.
  rw isprog_vars_eq; simpl; sp.
  rw subvars_singleton_l; sp; split; sp.
Qed.

Lemma isprog_vars_app1 :
  forall t vs1 vs2,
    isprog_vars vs1 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof.
  sp; alltrewrite isprog_vars_eq; sp.
  alltrewrite subvars_eq.
  apply subset_app_r; sp.
Qed.

Lemma isprog_vars_cons_if2 :
  forall v vs t,
    isprog_vars (v :: vs) t
    -> !LIn v (free_vars t)
    -> isprog_vars vs t.
Proof.
  introv ip ni.
  allrw isprog_vars_eq.
  allrw subvars_prop; sp.
  discover; allsimpl; sp; subst; sp.
Qed.

Lemma isprog_vars_cons_app1 :
  forall vs1 vs2 t,
    isprog_vars (vs1 ++ vs2) t
    -> (forall v, LIn v vs2 -> !LIn v (free_vars t))
    -> isprog_vars vs1 t.
Proof.
  introv ip ni.
  allrw isprog_vars_eq.
  allrw subvars_prop; sp.
  discover.
  allrw in_app_iff; sp.
  discover; sp.
Qed.

Ltac unfold_all_mk :=
       allunfold mk_apply
       ;allunfold mk_bottom
       ;allunfold mk_fix
       ;allunfold mk_id
       ;allunfold mk_lam
       ;allunfold mk_var
       ;allunfold mk_sup
       ;allunfold mk_equality
       ;allunfold mk_tequality
       ;allunfold mk_cequiv
       ;allunfold mk_inl
       ;allunfold mk_inr
       ;allunfold mk_pair
       ;allunfold mk_sup
       ;allunfold mk_int
       ;allunfold mk_uni
       ;allunfold mk_equality
       ;allunfold mk_base
       ;allunfold mk_fun
       ;allunfold mk_set
       ;allunfold mk_quotient
       ;allunfold mk_isect
       ;allunfold mk_disect
       ;allunfold mk_w
       ;allunfold mk_m
       ;allunfold mk_pw
       ;allunfold mk_pm
       ;allunfold mk_pertype
       ;allunfold mk_ipertype
       ;allunfold mk_spertype
       ;allunfold mk_tuni
       ;allunfold mk_partial
       ;allunfold mk_union
       ;allunfold mk_approx
       ;allunfold mk_cequiv
       ;allunfold mk_compute
       ;allunfold mk_rec
       ;allunfold mk_image
       ;allunfold mk_admiss
       ;allunfold mk_mono
       ;allunfold nobnd.

Lemma isprogram_inl_iff :
  forall a, isprogram a <=> isprogram (mk_inl a).
Proof.
  intros; split; intro i.
  apply isprogram_inl; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprogram_inr_iff :
  forall a, isprogram a <=> isprogram (mk_inr a).
Proof.
  intros; split; intro i.
  apply isprogram_inr; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)); intros i1.
  dest_imp i1 hyp.
  unfold isprogram; allrw.
  inversion i1; subst; sp.
Qed.

Lemma isprogram_union_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_union a b).
Proof.
  intros; split; intro i.
  apply isprogram_union; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_m_iff :
  forall a v b,
    (isprog a # isprog_vars [v] b)
    <=> isprog (mk_m a v b).
Proof.
  introv; split; intro k; try (apply isprog_m; sp).
  allrw isprog_eq; allrw isprog_vars_eq.
  inversion k as [c w].
  inversion w as [| o lnt j e ]; subst.
  generalize (j (nobnd a)) (j (bterm [v] b)); intros i1 i2; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  unfold isprogram.
  inversion c as [p]; allrw remove_nvars_nil_l; allrw app_nil_r.
  inversion i1; inversion i2; subst.
  rw app_eq_nil_iff in p; sp; subst; sp.
  rw subvars_prop; simpl; introv i; allrw in_app_iff; allrw in_remove_nvars.
  allrw in_single_iff.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma isprogram_pair_iff :
  forall a b, (isprogram a # isprogram b) <=> isprogram (mk_pair a b).
Proof.
  intros; split; intro i.
  apply isprogram_pair; sp.
  inversion i as [cl w].
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)); intros i1 i2.
  dest_imp i1 hyp; dest_imp i2 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; subst; sp.
Qed.

Definition mkc_admiss (R : CTerm) : CTerm :=
  let (a,x) := R in
  exist isprog (mk_admiss a) (isprog_admiss a x).

Theorem isvalue_admiss :
  forall a, isprogram a -> isvalue (mk_admiss a).
Proof.
 intros; constructor; apply isprogram_admiss; auto.
Qed.

Lemma iscvalue_mkc_admiss :
  forall t, iscvalue (mkc_admiss t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_admiss; allrw isprog_eq; auto.
Qed.

Definition mkc_mono (R : CTerm) : CTerm :=
  let (a,x) := R in
  exist isprog (mk_mono a) (isprog_mono a x).

Theorem isvalue_mono :
  forall a, isprogram a -> isvalue (mk_mono a).
Proof.
 intros; constructor; apply isprogram_mono; auto.
Qed.

Lemma iscvalue_mkc_mono :
  forall t, iscvalue (mkc_mono t).
Proof.
  intro; destruct t; unfold iscvalue; simpl.
  apply isvalue_mono; allrw isprog_eq; auto.
Qed.

Lemma wf_cequiv_iff :
  forall a b, (wf_term a # wf_term b) <=> wf_term (mk_cequiv a b).
Proof.
  sp; split; intros k.
  apply wf_cequiv; sp.
  allrw wf_term_eq.
  inversion k as [| o lnt i meq ]; subst; allsimpl.
  generalize (i (nobnd a)); generalize (i (nobnd b)); intros i1 i2.
  dest_imp i1 hyp.
  dest_imp i2 hyp.
  inversion i1; inversion i2; sp.
Qed.

Definition mkc_or A B := mkc_union A B.
Definition mkc_not P := mkc_fun P mkc_void.

Lemma wf_fun :
  forall A B, wf_term (mk_fun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw wf_term_eq in w.
  inversion w as [ | o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw nt_wf_eq; sp.

  rw <- nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw nt_wf_eq; sp.
Qed.

Lemma wf_ufun :
  forall A B, wf_term (mk_ufun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw wf_term_eq in w.
  inversion w as [ | o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw nt_wf_eq; sp.

  rw <- nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw nt_wf_eq; sp.
Qed.

Lemma wf_eufun :
  forall A B, wf_term (mk_eufun A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw wf_term_eq in w.
  inversion w as [ | o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw nt_wf_eq; sp.

  rw <- nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw nt_wf_eq; sp.
Qed.

Lemma wf_prod :
  forall A B, wf_term (mk_prod A B) <=> (wf_term A # wf_term B).
Proof.
  introv.
  split; intro w.

  rw wf_term_eq in w.
  inversion w as [ | o l bw e ]; subst.
  generalize (bw (nobnd A)) (bw (bterm [newvar B] B)); intros bw1 bw2; clear bw.
  dest_imp bw1 hyp.
  dest_imp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw nt_wf_eq; sp.

  rw <- nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw nt_wf_eq; sp.
Qed.

Lemma wf_not :
  forall A, wf_term (mk_not A) <=> wf_term A.
Proof.
  introv.
  rw wf_fun; split; sp.
Qed.

Ltac destruct_bterms:=
repeat match goal with
[bt : BTerm |- _] =>
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  destruct bt as [btlv btnt]
end.

Lemma mkc_admiss_eq :
  forall T1 T2, mkc_admiss T1 = mkc_admiss T2 -> T1 = T2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.

Lemma mkc_mono_eq :
  forall T1 T2, mkc_mono T1 = mkc_mono T2 -> T1 = T2.
Proof.
  intros.
  destruct_cterms; allsimpl.
  inversion H; subst.
  assert (i = i0) by apply isprog_proof_irrelevance; subst; sp.
Qed.



Lemma wf_less :
  forall a b c d,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> wf_term (mk_less a b c d).
Proof.
  introv; repeat (rw <- nt_wf_eq).
  intros nta ntb ntc ntd; inversion nta; inversion ntb; inversion ntc; inversion ntd; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_less_iff :
  forall a b c d,
    (wf_term a # wf_term b # wf_term c # wf_term d) <=> wf_term (mk_less a b c d).
Proof.
  introv; split; intro i.
  apply wf_less; sp.
  allrw wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)) (k (nobnd d)); intros k1 k2 k3 k4.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  repeat (dest_imp k3 hyp).
  repeat (dest_imp k4 hyp).
  inversion k1; subst.
  inversion k2; subst.
  inversion k3; subst.
  inversion k4; subst; sp.
Qed.

Lemma isprog_vars_less :
  forall a b c d vs,
    isprog_vars vs (mk_less a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- wf_term_eq).
  allrw <- wf_less_iff; split; sp.
Qed.

Lemma isprog_vars_function :
  forall vs a v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_function a v b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_function_iff :
  forall vs a v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_function a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_function; sp.
  allrw isprog_vars_eq; allrw nt_wf_eq.
  allrw <- wf_function_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_cons_newvar :
  forall b vs,
    isprog_vars (newvar b :: vs) b <=> isprog_vars vs b.
Proof.
  introv; split; intro k.

  allrw isprog_vars_eq.
  allrw subvars_prop; repnd; dands; auto.
  introv i.
  applydup k0 in i; simpl in i0; repdors; subst; auto.
  apply newvar_prop in i; sp.

  apply isprog_vars_cons; sp.
Qed.

Lemma isprog_vars_fun :
  forall vs a b,
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_fun a b).
Proof.
  introv.
  rw <- isprog_vars_function_iff.
  rw isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_ufun :
  forall vs a b,
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_ufun a b).
Proof.
  introv.
  rw <- isprog_vars_isect_iff.
  rw isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_eufun :
  forall vs a b,
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_eufun a b).
Proof.
  introv.
  rw <- isprog_vars_eisect_iff.
  rw isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_product :
  forall vs a v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_product a v b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Theorem wf_product_iff :
  forall a v b, (wf_term a # wf_term b) <=> wf_term (mk_product a v b).
Proof.
  sp; split; intro i; try (apply wf_product; sp).
  allrw wf_term_eq.
  inversion i as [ | o lnt k e ]; subst; allsimpl.
  generalize (k (nobnd a)) (k (bterm [v] b)); intros i1 i2.
  dest_imp i1 hyp; try (complete sp).
  dest_imp i2 hyp; try (complete sp).
  inversion i1; inversion i2; subst; sp.
Qed.

Lemma isprog_vars_product_iff :
  forall vs a v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_product a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_product; sp.
  allrw isprog_vars_eq; allrw nt_wf_eq.
  allrw <- wf_product_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_prod :
  forall vs a b,
    (isprog_vars vs a # isprog_vars vs b)
    <=> isprog_vars vs (mk_prod a b).
Proof.
  introv.
  rw <- isprog_vars_product_iff.
  rw isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_set :
  forall vs a v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_set a v b).
Proof.
  introv ipa ipb.
  allrw isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Lemma isprog_vars_set_iff :
  forall vs a v b,
    (isprog_vars vs a # isprog_vars (v :: vs) b)
    <=> isprog_vars vs (mk_set a v b).
Proof.
  introv; split; intro k.
  apply isprog_vars_set; sp.
  allrw isprog_vars_eq; allrw nt_wf_eq.
  allrw <- wf_set_iff; repnd.
  allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; sp.
  provesv; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_void_iff :
  forall vs, isprog_vars vs mk_void <=> True.
Proof.
  introv; split; intro k; auto.
Qed.

Lemma isprog_vars_true_iff :
  forall vs, isprog_vars vs mk_true <=> True.
Proof.
  introv; split; intro k; auto.
  rw isprog_vars_eq; sp.
  constructor; sp.
  allsimpl; sp; subst; repeat constructor; simpl; sp.
Qed.

Lemma isprog_vars_false_iff :
  forall vs, isprog_vars vs mk_false <=> True.
Proof.
  introv; split; intro k; auto.
Qed.

Lemma isprog_vars_le :
  forall a b vs,
    isprog_vars vs (mk_le a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv; unfold mk_le.
  rw <- isprog_vars_fun.
  rw isprog_vars_void_iff.
  rw isprog_vars_less.
  rw isprog_vars_false_iff.
  rw isprog_vars_true_iff.
  split; sp.
Qed.

Lemma isprog_tnat : isprog mk_tnat.
Proof.
  rw <- isprog_set_iff.
  rw isprog_vars_le; sp.
Qed.

Definition mkc_tnat := exist isprog mk_tnat isprog_tnat.

Lemma free_vars_fun :
  forall a b, free_vars (mk_fun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma free_vars_ufun :
  forall a b, free_vars (mk_ufun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma free_vars_eufun :
  forall a b, free_vars (mk_eufun a b) = free_vars a ++ free_vars b.
Proof.
  introv; simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r.
  assert (disjoint (free_vars b) [newvar b]) as disj.
  apply disjoint_sym.
  rw disjoint_singleton_l.
  apply newvar_prop.
  rw remove_nvars_unchanged in disj.
  rw disj; auto.
Qed.

Lemma isprogram_mk_zero :
  isprogram mk_zero.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_zero.

Lemma isprog_mk_zero :
  isprog mk_zero.
Proof.
  rw isprog_eq.
  apply isprogram_mk_zero.
Qed.
Hint Immediate isprog_mk_zero.

Definition mkc_zero := exist isprog mk_zero isprog_mk_zero.

Definition mk_eta_pair t := mk_pair (mk_pi1 t) (mk_pi2 t).

Lemma free_vars_mk_pertype :
  forall A,
    free_vars (mk_pertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_ipertype :
  forall A,
    free_vars (mk_ipertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_spertype :
  forall A,
    free_vars (mk_spertype A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma free_vars_mk_tuni :
  forall A,
    free_vars (mk_tuni A) = free_vars A.
Proof.
  introv.
  simpl.
  rw remove_nvars_nil_l.
  rw app_nil_r; auto.
Qed.

Lemma wf_isaxiom :
  forall a b c, wf_term (mk_isaxiom a b c) <=> (wf_term a # wf_term b # wf_term c).
Proof.
  sp; split; intro k.

  inversion k.
  allrw andb_true; sp.

  unfold wf_term; simpl.
  allrw andb_true; sp.
Qed.

Lemma nt_wf_isaxiom :
  forall a b c, nt_wf (mk_isaxiom a b c) <=> (nt_wf a # nt_wf b # nt_wf c).
Proof.
  introv.
  allrw nt_wf_eq.
  apply wf_isaxiom.
Qed.

Lemma isprog_vars_isaxiom :
  forall vs a b c,
    isprog_vars vs (mk_isaxiom a b c)
    <=>
    (isprog_vars vs a
     # isprog_vars vs b
     # isprog_vars vs c).
Proof.
  introv; split; intro k; repnd; allrw isprog_vars_eq; allsimpl;
  allrw remove_nvars_nil_l; allrw app_nil_r;
  allrw subvars_app_l; allrw nt_wf_isaxiom; sp.
Qed.

Lemma isprog_vars_halts :
  forall vs a, isprog_vars vs (mk_halts a) <=> isprog_vars vs a.
Proof.
  introv.
  allrw isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw nt_wf_eq.
  allrw <- wf_halts_iff; sp.
Qed.

Lemma isprog_ipertype_iff :
  forall a, isprog a <=> isprog (mk_ipertype a).
Proof.
  introv; split; intro k.
  apply isprog_ipertype; sp.
  allrw isprog_eq; allunfold isprogram; allrw nt_wf_eq.
  allrw <- wf_ipertype_iff; sp.
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_spertype_iff :
  forall a, isprog a <=> isprog (mk_spertype a).
Proof.
  introv; split; intro k.
  apply isprog_spertype; sp.
  allrw isprog_eq; allunfold isprogram; allrw nt_wf_eq.
  allrw <- wf_spertype_iff; sp.
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma isprog_tuni_iff :
  forall a, isprog a <=> isprog (mk_tuni a).
Proof.
  introv; split; intro k.
  apply isprog_tuni; sp.
  allrw isprog_eq; allunfold isprogram; allrw nt_wf_eq.
  allrw <- wf_tuni_iff; sp.
  allunfold closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r; sp.
Qed.

Lemma wf_pair :
  forall a b, wf_term (mk_pair a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw nt_wf_eq; sp.
Qed.

Lemma wf_spread :
  forall a v1 v2 b,
    wf_term (mk_spread a v1 v2 b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw wf_term_eq in w.
  inversion w as [ | o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  allrw nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw nt_wf_eq; sp.
Qed.

Lemma wf_ispair :
  forall a b T, wf_term a -> wf_term b -> wf_term T -> wf_term (mk_ispair a b T).
Proof.
  intros a b T; repeat (rw <- nt_wf_eq).
  intros nta ntb ntt; inversion nta; inversion ntb; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_ispair_iff :
  forall a b T, (wf_term a # wf_term b # wf_term T) <=> wf_term (mk_ispair a b T).
Proof.
  sp; split; intros.
  apply wf_ispair; sp.
  inversion H.
  allrw andb_true; sp.
Qed.

Lemma isprog_pi1 :
  forall t, isprog t -> isprog (mk_pi1 t).
Proof.
  introv ip.
  apply isprog_spread; sp.
Qed.

Lemma isprog_pi2 :
  forall t, isprog t -> isprog (mk_pi2 t).
Proof.
  introv ip.
  apply isprog_spread; sp.
Qed.

Lemma isprog_eta_pair :
  forall t, isprog t -> isprog (mk_eta_pair t).
Proof.
  introv ip.
  unfold mk_eta_pair.
  apply isprog_pair.
  apply isprog_pi1; auto.
  apply isprog_pi2; auto.
Qed.

Definition mkc_eta_pair (t : CTerm) :=
  let (a,p) := t in exist isprog (mk_eta_pair a) (isprog_eta_pair a p).

Lemma fold_pi1 :
  forall t, mk_spread t nvarx nvary (mk_var nvarx) = mk_pi1 t.
Proof. sp. Qed.

Lemma fold_pi2 :
  forall t, mk_spread t nvarx nvary (mk_var nvary) = mk_pi2 t.
Proof. sp. Qed.

Lemma fold_eta_pair :
  forall t, mk_pair (mk_pi1 t) (mk_pi2 t) = mk_eta_pair t.
Proof. sp. Qed.

Lemma wf_pi1 :
  forall t, wf_term (mk_pi1 t) <=> wf_term t.
Proof.
  introv.
  rw wf_spread; split; sp.
Qed.

Lemma wf_pi2 :
  forall t, wf_term (mk_pi2 t) <=> wf_term t.
Proof.
  introv.
  rw wf_spread; split; sp.
Qed.

Lemma wf_eta_pair :
  forall t, wf_term (mk_eta_pair t) <=> wf_term t.
Proof.
  introv.
  unfold mk_eta_pair.
  rw wf_pair.
  rw wf_pi1.
  rw wf_pi2.
  split; sp.
Qed.

Lemma isprogram_spread_iff :
  forall a v1 v2 b,
    (isprogram a
     # subvars (free_vars b) [v1,v2]
     # nt_wf b)
    <=> isprogram (mk_spread a v1 v2 b).
Proof.
  introv; split; intro isp; repnd.
  apply isprogram_spread; auto.
  inversion isp as [cl wf].
  inversion wf as [ | o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1,v2] b)); clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  unfold closed in cl; simpl in cl; rw remove_nvars_nil_l in cl; rw app_nil_r in cl.
  apply app_eq_nil in cl; repnd.
  allfold (closed a).
  dands; auto.
  constructor; sp.
  rw subvars_prop; introv i.
  rw nil_remove_nvars_iff in cl.
  apply cl in i; sp.
Qed.

Lemma isprogram_pi1 :
  forall t, isprogram (mk_pi1 t) <=> isprogram t.
Proof.
  introv.
  rw <- isprogram_spread_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  rw subvars_cons_l; sp.
Qed.

Lemma isprogram_pi2 :
  forall t, isprogram (mk_pi2 t) <=> isprogram t.
Proof.
  introv.
  rw <- isprogram_spread_iff; simpl; split; intro i; repnd; auto.
  dands; auto.
  rw subvars_cons_l; sp.
Qed.

Lemma isprogram_eta_pair :
  forall t, isprogram (mk_eta_pair t) <=> isprogram t.
Proof.
  introv.
  rw <- isprogram_pair_iff.
  rw isprogram_pi1.
  rw isprogram_pi2.
  split; sp.
Qed.

Lemma iscvalue_mkc_tequality :
  forall t1 t2, iscvalue (mkc_tequality t1 t2).
Proof.
  intro; destruct t1; destruct t2; unfold iscvalue; simpl.
  apply isvalue_tequality; allrw isprog_eq; auto.
  apply isprogram_tequality; sp.
Qed.

Lemma isprog_pw_iff :
  forall P ap A bp ba B cp ca cb C p,
    isprog (mk_pw P ap A bp ba B cp ca cb C p)
           <=> (isprog P
                # isprog_vars [ap] A
                # isprog_vars [bp, ba] B
                # isprog_vars [cp, ca, cb] C
                # isprog p).
Proof.
  introv; split; intro isp.

  rw isprog_eq in isp.
  inversion isp as [ cl wf ].
  inversion wf as [| o lnt j e ]; subst.
  generalize (j (nobnd P))
             (j (bterm [ap] A))
             (j (bterm [bp,ba] B))
             (j (bterm [cp,ca,cb] C))
             (j (nobnd p)); clear j;
    intros i1 i2 i3 i4 i5; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  repeat (dest_imp i3 hyp).
  repeat (dest_imp i4 hyp).
  repeat (dest_imp i5 hyp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst.
  unfold closed in cl; simpl in cl; allrw remove_nvars_nil_l; allrw app_nil_r.
  rw <- null_iff_nil in cl.
  allrw null_app; repnd.
  allrw null_remove_nvars_subvars.
  allrw null_iff_nil.
  dands.
  rw isprog_eq; constructor; sp.
  rw isprog_vars_eq; sp.
  rw isprog_vars_eq; sp.
  rw isprog_vars_eq; sp.
  rw isprog_eq; constructor; sp.

  apply isprog_pw; sp.
Qed.

Lemma isprog_pm_iff :
  forall P ap A bp ba B cp ca cb C p,
    isprog (mk_pm P ap A bp ba B cp ca cb C p)
           <=> (isprog P
                # isprog_vars [ap] A
                # isprog_vars [bp, ba] B
                # isprog_vars [cp, ca, cb] C
                # isprog p).
Proof.
  introv; split; intro isp.

  rw isprog_eq in isp.
  inversion isp as [ cl wf ].
  inversion wf as [| o lnt j e ]; subst.
  generalize (j (nobnd P))
             (j (bterm [ap] A))
             (j (bterm [bp,ba] B))
             (j (bterm [cp,ca,cb] C))
             (j (nobnd p)); clear j;
    intros i1 i2 i3 i4 i5; allsimpl.
  repeat (dest_imp i1 hyp).
  repeat (dest_imp i2 hyp).
  repeat (dest_imp i3 hyp).
  repeat (dest_imp i4 hyp).
  repeat (dest_imp i5 hyp).
  inversion i1; inversion i2; inversion i3; inversion i4; inversion i5; subst.
  unfold closed in cl; simpl in cl; allrw remove_nvars_nil_l; allrw app_nil_r.
  rw <- null_iff_nil in cl.
  allrw null_app; repnd.
  allrw null_remove_nvars_subvars.
  allrw null_iff_nil.
  dands.
  rw isprog_eq; constructor; sp.
  rw isprog_vars_eq; sp.
  rw isprog_vars_eq; sp.
  rw isprog_vars_eq; sp.
  rw isprog_eq; constructor; sp.

  apply isprog_pm; sp.
Qed.


(* --- isprog hints --- *)
Hint Resolve isprog_lam : isprog.
Hint Resolve isprog_vars_lam : isprog.
Hint Resolve isprog_vars_isect : isprog.
Hint Resolve isprog_vars_base : isprog.
Hint Resolve isprog_vars_equality : isprog.
Hint Resolve isprog_vars_var_if : isprog.
Hint Resolve isprog_vars_if_isprog : isprog.
Hint Extern 100 (LIn _ _) => complete (simpl; sp) : isprog.
Hint Resolve isprog_implies : isprog.

(* end hide *)
