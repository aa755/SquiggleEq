
Require Export Recdef.
Require Export Eqdep_dec.
Require Export opid.
Require Export varInterface.


Section terms.
Context {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig}.

Inductive NTerm : Type :=
| vterm: NVar -> NTerm
| oterm: Opid -> list BTerm -> NTerm
with BTerm : Type :=
| bterm: (list NVar) -> NTerm -> BTerm.

(*
  The [Opid] type contains one element corresponding to every operator
  of the language, e.g. lambda abstraction, funtion application,
  dependent function type constructor. As a more concrete example,
  the [Can NLambda] is the element of [Opid] that represents lambda
  abstractions.
  To construct a bound term([BTerm]), we need a list of variables and
  an [NTerm] (see the [bterm] constructor). As a concrete example,
   $ \lambda x.x$ is represented in this type
  as [(oterm  (Can NLambda) (bterm [nvarx] (vterm nvarx)))].
*)

(**
  It is a mutually inductive definition that simultaneously defines terms
  and bound terms. As mentioned before, the [vterm] constructor
  takes an [NVar] and constructs an [NTerm]. The other constructor([oterm])
  takes an [Opid] and a list of bound terms ([BTerm]s) and constructs an [NTerm].
  Note that not all members of [NTerm] are meaningful(well-formed).
  For example, the [Opid] corresponding to lambda abstractions must be
  provided with exactly one bound term as argument. Moreover, that
  bound term must have exactly one bound variable. So, we have a function
  [OpBindings] in type [Opid -> list nat] that specifies both the
  number of arguments and the number of bound variables in each argument([BTerm]).
  We will use it soon to define the subcollection of well-formed terms.
*)

(* begin hide *)
(*
Scheme NTerm_mut := Induction for NTerm Sort Prop
with BTerm_mut := Induction for BTerm Sort Prop.
*)

(*
Definition term_rel := NTerm -> NTerm -> Type.
*)

Definition iscanonical (t : NTerm) :=
  match t with
    | oterm (Can _) _ => true
    | _ => false
  end.

Definition isvar (t : NTerm) :=
  match t with
    | vterm _ => true
    | _ => false
  end.

Definition isvariable (t : NTerm) :=
  match t with
    | vterm _ => True
    | _ => False
  end.


(*Notation "x # b" := (bterm [x] b) (at level 70, right associativity).
(*Check [[ btermO (vterm(nvar 0))]] *)
(* Notation "< N >" := (btermO N). *)
Notation "\\ f" :=
  (oterm (Can NLambda) [[f]]) (at level 70, right associativity).

*)


(* ------ CONSTRUCTORS ------ *)


(* --- primitives --- *)

Definition mk_var (nv : NVar) := vterm nv.

(* end hide *)
(** %\noindent% Whenever we talk about the [NTerm] of a [BTerm], this is
what we would mean:

*)
Definition get_nt  (bt: BTerm ) : NTerm :=
 match bt with
 | bterm lv nt => nt
 end.

Definition get_vars  (bt: BTerm ) : list NVar :=
 match bt with
 | bterm lv nt => lv
 end.

Definition num_bvars (bt : BTerm) := length (get_vars bt).

(** % \noindent \\* % We define
    a predicate [nt_wf] on [NTerm] such that
    [nt_wf nt] asserts that [nt] is a well-formed term.  %\\* %
*)
Inductive nt_wf: NTerm -> [univ] :=
| wfvt: forall nv : NVar, nt_wf (vterm nv)
| wfot: forall (o: Opid) (lnt: list BTerm),
        (forall l, LIn l lnt -> bt_wf l)
         -> map (num_bvars) lnt 
            = OpBindings o
         -> nt_wf (oterm o lnt)
with bt_wf : BTerm -> [univ] :=
| wfbt : forall (lnv : list NVar) (nt: NTerm),
         nt_wf nt -> bt_wf (bterm lnv nt).

(*  For example, the Opid [(Can NLambda)] takes only one [BTerm] an that [BTerm]
  must have exactly one bound variable.
  Hence [OpBindings (Can NLambda) = [1]]. *)

(** % \noindent \\* %
  The only interesting case here is for the [oterm] case. The
  [wfot] constructor requires
  that the number of bound variables of the bound terms in the list
  match the signature ([OpBindings o]) of the corresponding operator [o].
  
  % \noindent \\* % We abstract the [Opid]s into two categories, canonical
    and noncanonical.

  [
    Inductive Opid : Set :=

     | Can  : CanonicalOp -> Opid

     | NCan : NonCanonicalOp -> Opid.

  ]
% \noindent \\* % This distinction is important from the point of view of computation
    and simplifies many definitions and properties about computation and
    also makes them more easily extensible.
    Nuprl has a lazy computation system and
    an [NTerm] is in normal(canonical) form if its outermost [Opid] is a [CanonicalOp].
    No further computation is performed on terms in canonical form.
    For example, lambda abstraction are constructed by the following [Opid] :

% \noindent \\* % [Can NLambda] 

% \noindent \\* % We have [OpBindings (Can NLambda) = [1]].

    
    On the other hand, an [NTerm] whose outermost [Opid] is a [NonCanonicalOp] is
    not in normal form and can compute to some other term, or to an error.
    An an  example, terms denoting function applications are constructed by the
    following [Opid]:
% \noindent \\* % [NCan NApply] 

% \noindent \\* % We have [OpBindings (NCan NApply) = [0,0]].


    The only restriction in defining [CanonicalOp] and [NonCanonicalOp] is 
    that the equality in these types should be decidable.
    We will soon show the full-blown definition of
    the [Opid]s of Nuprl.
    Before that, we define functions that compute the free variables and
    bound variables of a term.
    Note how these functions have just two cases 
    and are robust against addition/deletion of new operators([Opid]s) to the 
    language.
    If we had defined [NTerm] in the usual way(with one constructor for each [Opid]),
    these definitions would be of the form of a long pattern match with one case for each [Opid].
    However, these definitions only care about the binding structure.
    We will reap more benefits of this uniformity when we define substitution and alpha equality
    in the next subsection.
*)


End terms.
(* closing the section because there is a problem with
  simpl and sections and mutual fixpoints
https://coq.inria.fr/bugs/show_bug.cgi?id=3343  
   *) 

(* --- variables --- *)
Fixpoint free_vars {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig}  
  (t:NTerm) {struct t}: list NVar :=
  match t with
  | vterm v => [v]
  | oterm op bts => flat_map (@free_vars_bterm NVar _ _ _ _)  bts
  end
 with free_vars_bterm {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig}  (bt : BTerm)
  {struct bt} : list NVar :=
  match bt with
  | bterm  lv nt => remove_nvars lv (free_vars nt)
  end.

Fixpoint bound_vars {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig} (t : NTerm) : list NVar :=
  match t with
  | vterm v => []
  | oterm op bts => flat_map (@bound_vars_bterm NVar VarClass _ _ _ _)  bts
  end
 with bound_vars_bterm {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig} {gts : GenericTermSig} (bt : BTerm ) 
  :list NVar :=
  match bt with
  | bterm lv nt => lv ++ bound_vars nt
  end.

Section termsCont.
Context {NVar VarClass} `{VarType NVar VarClass} {gts : GenericTermSig}.
Definition all_vars t := free_vars t ++ bound_vars t.

Definition closed (t : NTerm) := free_vars t = [].
(* Howe's T_0(L) *)
Definition isprogram (t : NTerm) := closed t # nt_wf t.

End termsCont.