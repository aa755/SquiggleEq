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


Require Export BinInt.
Require Export list.
Require Export Coq.ZArith.ZArith_dec.
(** printing Z  $\mathbb{Z}$ #Z# *)

(* ------ operators ------ *)
(** Here are the Canonical [Opid]s of Nuprl:

*)

(* canonical forms of the computation system *)

 Inductive CanonicalOp : Set :=
 (**  %\noindent \\*% Firstly, here are the ones that can be thought
  of data constructors. [NInl], [NInr], [NPair]
  [Nint] correspond to fairly standard
  data constructors in Martin
  Lof's theories. [NAxiom] is the unique canonical
  inhabitant logically fundamental types
  of Nuprl's type system that denote true propositions and for which no
  evidence is required.
  [NSup] is the canonical form representing
  members of the W types of Nuprl.
    %\bigskip%



  *)
 | NLambda   : CanonicalOp
 | NAxiom    : CanonicalOp
 | NInl      : CanonicalOp
 | NInr      : CanonicalOp
 | NPair     : CanonicalOp
 | NSup      : CanonicalOp
 | Nint      : Z -> CanonicalOp
 | NTok      : String.string -> CanonicalOp
 (** %\noindent \\*% Like Martin Lof's theories, types are also
  first class terms and can be computed with.
  There is a [CanonicalOp] for each type constructor.
  Here are the [CanonicalOp]s that correspond to
  type constructors. The meanings of most of these types
  will be formally defined in the Chapter %\ref{chapter:type_system}%
  A few of these type-constructors are not currently in use 
  (e.g. \coqdocconstructor{NRec}), but they are there for the
  possibility of future experimentation.
    %\bigskip%


  *)
 | NUni       : nat -> CanonicalOp
 | NTUni      : CanonicalOp
 | NEquality  : CanonicalOp
 | NTEquality : CanonicalOp
 | NInt       : CanonicalOp
 | NAtom      : CanonicalOp
 | NBase      : CanonicalOp
 | NFunction  : CanonicalOp
 | NProduct   : CanonicalOp
 | NSet       : CanonicalOp
 | NQuotient  : CanonicalOp
 | NIsect     : CanonicalOp
 | NDIsect    : CanonicalOp
 | NEIsect    : CanonicalOp
 | NW         : CanonicalOp
 | NM         : CanonicalOp
 | NPW        : CanonicalOp
 | NPM        : CanonicalOp
 | NEPertype  : CanonicalOp (* extensional *)
 | NIPertype  : CanonicalOp (* intensional *)
 | NSPertype  : CanonicalOp (* intensional with a strong equality *)
 | NPartial   : CanonicalOp
 | NUnion     : CanonicalOp
 | NApprox    : CanonicalOp
 | NCequiv    : CanonicalOp
 | NCompute   : CanonicalOp
 | NRec       : CanonicalOp
 | NImage     : CanonicalOp
 | NAdmiss    : CanonicalOp
 | NMono      : CanonicalOp.
(* | NEsquash  : CanonicalOp (* extensional squash *)*)

(** %\noindent \\*% Now we define the binding structure for each
    [CanonicalOp]. Recall that the the length of
    [OpBindingsCan c] represents
    the number of arguments([BTerm]s) required
    to form an [NTerm] using this the [CanonicalOp] [c].
    The $i^{th}$ element [OpBindingsCan c] represents
    the number of bound variables in the $i^{th}$ argument.

*)
Definition OpBindingsCan (c : CanonicalOp) : list nat :=
  match c with
  | NLambda    => [1]
  | NAxiom     => []
  | NInl       => [0]
  | NInr       => [0]
  | NPair      => [0,0]
  | NSup       => [0,0]
  | Nint _     => []
  | NUni _     => []
  | NTUni      => [0]
  | NTok _     => []
  | NEquality  => [0,0,0]
  | NTEquality => [0,0]
  | NInt       => []
  | NBase      => []
  | NAtom      => []
  | NFunction  => [0,1]
  | NProduct   => [0,1]
  | NSet       => [0,1]
  | NIsect     => [0,1]
  | NDIsect    => [0,1]
  | NEIsect    => [0,1]
  | NW         => [0,1]
  | NM         => [0,1]
  | NPW        => [0,1,2,3,0]
  | NPM        => [0,1,2,3,0]
  | NEPertype  => [0]
  | NIPertype  => [0]
  | NSPertype  => [0]
  | NPartial   => [0]
  | NUnion     => [0,0]
  | NApprox    => [0,0]
  | NCequiv    => [0,0]
  | NCompute   => [0,0,0]
  | NRec       => [1]
  | NImage     => [0,0]
  | NQuotient  => [0,2]
  | NAdmiss    => [0]
  | NMono      => [0]
  end.
(*  | NEsquash  => [0]*)

(** %\noindent \\*% Now, we will define non-canonical [Opid]s of Nuprl.
    Intuitively, these represent the elimination forms
    corresponding to some of the canonical terms of Nuprl.
    For example, [NApply] represents the elimination form
    for the [CanonicalOp] [NLambda].
    Notably, there are no elimination forms
    for the [CanonicalOp]s that represent
    type constructors. We also have some arithmetic
    and comparison operators on numbers.
    We will define 3 more parameters for defining
    the type [NonCanonicalOp].

 *)

Inductive ArithOp : Set :=
 | ArithOpAdd : ArithOp
 | ArithOpMul : ArithOp
 | ArithOpSub : ArithOp
 | ArithOpDiv : ArithOp
 | ArithOpRem : ArithOp.



Inductive ComparisonOp : Set :=
 | CompOpLess   : ComparisonOp
 | CompOpInteq  : ComparisonOp
 | CompOpAtomeq : ComparisonOp.

(*
  This is repeating CanonicalOp, can't we just use CanonicalOp.
  If we were to use CanonicalOp, one issue might be that there will
  be a infinite number of ways to build isint: isint (int 0),
  isint (int 1)...
*)

(** %\noindent \\*% The following type parametrizes some [NonCanonicalOp]s
    that test the head normal form of a term.

 *)

Inductive CanonicalTest : Set :=
 | CanIspair   : CanonicalTest
 | CanIssup    : CanonicalTest
 | CanIsaxiom  : CanonicalTest
 | CanIslambda : CanonicalTest
 | CanIsint    : CanonicalTest
 | CanIsinl    : CanonicalTest
 | CanIsinr    : CanonicalTest
 | CanIsatom   : CanonicalTest.

(** %\noindent \\*% Finally, here are the noncanonical [Opid]s of Nuprl:
    

 *)

Inductive NonCanonicalOp : Set :=
 | NApply    : NonCanonicalOp
 | NFix      : NonCanonicalOp
 | NSpread   : NonCanonicalOp
 | NDsup     : NonCanonicalOp
 | NDecide   : NonCanonicalOp
 | NCbv      : NonCanonicalOp
 | NCompOp   : ComparisonOp  -> NonCanonicalOp
 | NArithOp  : ArithOp       -> NonCanonicalOp
 | NCanTest  : CanonicalTest -> NonCanonicalOp.

Definition OpBindingsNCan (nc : NonCanonicalOp) : list nat :=
  match nc with
  | NApply     => [0,0]
  | NFix       => [0]
  | NSpread    => [0,2]
  | NDsup      => [0,2]
  | NDecide    => [0,1,1]
  | NCbv       => [0,1]
  | NCompOp  _ => [0,0,0,0]
  | NArithOp _ => [0,0]
  | NCanTest _ => [0,0,0]
  end.

(**  %\noindent \\*% [NFix] represents the fixpoint combinator.
    [NSpread] is the elimination form for [NPair].
    The first argument of [NSpread] is supposed to be
    a [BTerm] with no bound variables such that the underlying
    [NTerm] converges to something with head [Opid] as [NPair].
    The second argument is a [BTerm] with two bound
    variables. These variables indicate the positions
    where the two components of the pair will be
    substituted in. The binding structure of the other
    [NonCanonicalOp]s can be understood similarly.
    More details will be available later when we define
    the computation system in the next chapter.

    [NDecide] is the elimination form for [NInl] and [NInr].
    [NCbv] the call-by-value variant of application.
    It evaluates its first argument down to a value before
    substituting it into the second argument that is a bound
    term with one bound variable.

*)

(* begin hide *)
Inductive Opid : Set :=
 | Can  : CanonicalOp -> Opid
 | NCan : NonCanonicalOp -> Opid.
(* end hide *)

(** %\noindent \\*% The following function defines
    the binding structure of any [Opid].
    It was used in the definition of
    [nt_wf].


*)
Definition OpBindings (op : Opid) : list nat :=
 match op with
 | Can c   => OpBindingsCan c
 | NCan nc => OpBindingsNCan nc
 end.

(* begin hide *)

Tactic Notation "dopid" ident(o) "as" simple_intropattern(I) ident(c) :=
  destruct o as I;
  [ Case_aux c "Can"
  | Case_aux c "NCan"
  ].


Tactic Notation "dopid_noncan" ident(onc) ident(c) :=
  destruct onc;
  [ Case_aux c "NApply"
  | Case_aux c "NFix"
  | Case_aux c "NSpread"
  | Case_aux c "NDsup"
  | Case_aux c "NDecide"
  | Case_aux c "NCbv"
  | Case_aux c "NCompOp"
  | Case_aux c "NArithOp"
  | Case_aux c "NCanTest"
  ].



(* end hide *)

(** The only requirement for defining [CanonicalOp]
    and [NonCanonicalOp] is that equality
    must be decidable in these types.
    We prove the folowing lemma by straightforward
    case analysis.

 *)

Lemma canonical_dec : forall x y : CanonicalOp, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x; destruct y;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).

  assert ({z < z0} + {z > z0} + {z = z0})%Z as h by (apply Z_dec).
  destruct h as [ h | h ]; subst.
  destruct h as [ h | h ]; sp; right; sp; inversion H; omega.
  left; sp.

  assert ({s = s0} + {s <> s0}) as h by (apply String.string_dec).
  destruct h as [ h | h ]; subst; sp.
  right; intro x; inversion x; sp.

  assert ({n < n0} + {n = n0} + {n0 < n}) as h by (apply lt_eq_lt_dec).
  destruct h as [ h | h ].
  destruct h as [ h | h ]; subst; sp.
  right; intro x; inversion x; omega.
  right; intro x; inversion x; omega.
Qed.

Lemma opid_dec : forall x y : Opid, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x; destruct y;
  try destruct c; try destruct c0;
  try destruct n; try destruct n0;
  try destruct c; try destruct c0;
  try destruct a; try destruct a0;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).

  assert ({z < z0} + {z > z0} + {z = z0})%Z as h by (apply Z_dec).
  destruct h as [ h | h ]; subst.
  destruct h as [ h | h ]; sp; right; sp; inversion H; omega.
  left; sp.

  assert ({s = s0} + {s <> s0}) as h by (apply String.string_dec).
  destruct h as [ h | h ]; subst; sp.
  right; intro x; inversion x; sp.

  assert ({n < n0} + {n = n0} + {n0 < n}) as h by (apply lt_eq_lt_dec).
  destruct h as [ h | h ].
  destruct h as [ h | h ]; subst; sp.
  right; intro x; inversion x; omega.
  right; intro x; inversion x; omega.
Qed.

(* begin hide *)