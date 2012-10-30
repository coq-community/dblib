Set Implicit Arguments.
Require Export Coq.Program.Equality.
Require Import DblibTactics.
Require Import DeBruijn.
Require Import Environments.

(* ---------------------------------------------------------------------------- *)

(* The syntax of System F types. *)

Inductive ty :=
  | TyVar: nat -> ty
  | TyArrow: ty -> ty -> ty
  | TyForall: ty -> ty.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of types. *)

Instance Var_ty : Var ty := {
  var := TyVar (* avoid eta-expansion *)
}.

Fixpoint traverse_ty (f : nat -> nat -> ty) l T :=
  match T with
  | TyVar x =>
      f l x
  | TyArrow T1 T2 =>
      TyArrow (traverse_ty f l T1) (traverse_ty f l T2)
  | TyForall T =>
      TyForall (traverse_ty f (1 + l) T)
  end.

Instance Traverse_ty : Traverse ty ty := {
  traverse := traverse_ty
}.

Instance TraverseVarInjective_ty : @TraverseVarInjective ty _ ty _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_ty : @TraverseFunctorial ty _ ty _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_ty : @TraverseRelative ty ty _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_ty : @TraverseIdentifiesVar ty _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_ty : @TraverseVarIsIdentity ty _ ty _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The syntax of terms. *)

Inductive term :=
  | TVar: nat -> term
  | TAbs: term -> term
  | TApp: term -> term -> term
  | TTyAbs: term -> term
  | TTyApp: term -> ty -> term.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of terms: term variables in terms. *)

Instance Var_term : Var term := {
  var := TVar (* avoid eta-expansion *)
}.

Fixpoint traverse_term_term (f : nat -> nat -> term) l t :=
  match t with
  | TVar x =>
      f l x
  | TAbs t =>
      TAbs (traverse_term_term f (1 + l) t)
  | TApp t1 t2 =>
      TApp (traverse_term_term f l t1) (traverse_term_term f l t2)
  | TTyAbs t =>
      TTyAbs (traverse_term_term f l t)
  | TTyApp t T =>
      TTyApp (traverse_term_term f l t) T
  end.

Instance Traverse_term_term : Traverse term term := {
  traverse := traverse_term_term
}.

Instance TraverseVarInjective_term_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_term_term : @TraverseFunctorial term _ term _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_term_term : @TraverseRelative term term _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_term_term : @TraverseIdentifiesVar term _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_term_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of terms: type variables in terms. *)

Fixpoint traverse_type_term (f : nat -> nat -> ty) l t :=
  match t with
  | TVar x =>
      TVar x
  | TAbs t =>
      TAbs (traverse_type_term f l t)
  | TApp t1 t2 =>
      TApp (traverse_type_term f l t1) (traverse_type_term f l t2)
  | TTyAbs t =>
      TTyAbs (traverse_type_term f (1 + l) t)
  | TTyApp t T =>
      TTyApp (traverse_type_term f l t) (traverse f l T)
                            (* could be: traverse_ty f l T *)
  end.

Instance Traverse_type_term : Traverse ty term := {
  traverse := traverse_type_term
}.

Instance TraverseVarInjective_type_term : @TraverseVarInjective ty _ term _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_type_term : @TraverseFunctorial ty _ term _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_type_term : @TraverseRelative ty term _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseVarIsIdentity_type_term : @TraverseVarIsIdentity ty _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* We now have two [lift] functions over terms: one that inserts a new type
   variable, and one that inserts a new term variable. There is ambiguity,
   so we cannot rely purely on overloading (Coq would make an arbitrary choice
   for us). Instead, we give two distinct names to these functions. *)

(* Note that we must use Notations here, as opposed to Definitions, as the
   tactics [simpl_lift_goal] and [simpl_subst_goal] will otherwise be
   blocked. *)

Notation shift_type_term :=
  (@lift term (@Lift_Traverse ty Var_ty term Traverse_type_term) 1).

Notation shift_term_term :=
  (@lift term (@Lift_Traverse term Var_term term Traverse_term_term) 1).

(* Note that this ambiguity problem does not arise with [subst], because the
   type of the thing that we are substituting in tells us whether a type
   variable or a term variable is being replaced. *)

(* ---------------------------------------------------------------------------- *)

(* Reduction semantics. *)

Inductive red : term -> term -> Prop :=
  | RedBeta:
      forall t1 t2,
      red (TApp (TAbs t1) t2)
          (subst t2 0 t1)
  | RedTyBeta:
      forall t T,
      red (TTyApp (TTyAbs t) T)
          (subst T 0 t)
  | RedContextTAbs:
      forall t1 t2,
      red t1 t2 ->
      red (TAbs t1) (TAbs t2)
  | RedContextTAppLeft:
      forall t1 t2 t,
      red t1 t2 ->
      red (TApp t1 t) (TApp t2 t)
  | RedContextTAppRight:
      forall t1 t2 t,
      red t1 t2 ->
      red (TApp t t1) (TApp t t2)
  | RedContextTTyAbs:
      forall t1 t2,
      red t1 t2 ->
      red (TTyAbs t1) (TTyAbs t2)
  | RedContextTTyApp:
      forall t1 t2 T,
      red t1 t2 ->
      red (TTyApp t1 T) (TTyApp t2 T).

(* ---------------------------------------------------------------------------- *)

(* The typing judgement of System F. *)

Inductive j : env ty -> term -> ty -> Prop :=
  | JVar:
      forall E x T,
      lookup x E = Some T ->
      j E (TVar x) T
  | JAbs:
      forall E t T1 T2,
      j (insert 0 T1 E) t T2 ->
      j E (TAbs t) (TyArrow T1 T2)
  | JApp:
      forall E t1 t2 T1 T2,
      j E t1 (TyArrow T1 T2) ->
      j E t2 T1 ->
      j E (TApp t1 t2) T2
  | JTyAbs:
      forall E t T,
      j (map (shift 0) E) t T ->
      j E (TTyAbs t) (TyForall T)
  | JTyApp:
      forall E t T U U',
      j E t (TyForall T) ->
      (* an explicit equality facilitates the use of this axiom by [eauto] *)
      subst U 0 T = U' -> 
      j E (TTyApp t U) U'.

Hint Constructors j : j.

(* ---------------------------------------------------------------------------- *)

(* Type preservation. *)

Lemma term_weakening:
  forall E t T,
  j E t T ->
  forall x U E',
  insert x U E = E' ->
  j E' (shift_term_term x t) T.
Proof.
  induction 1; intros; subst; simpl_lift_goal; econstructor;
  eauto with lookup_insert insert_insert map_insert.
Qed.

Lemma type_weakening:
  forall E t T,
  j E t T ->
  forall x E' t' T',
  map (shift x) E = E' ->
  shift_type_term x t = t' ->
  shift x T = T' ->
  j E' t' T'.
Proof.
  induction 1; intros; subst; simpl_lift_goal;
  econstructor;
  eauto using lookup_map_some, map_map_exchange
  with simpl_lift_goal lift_lift lift_subst map_insert.
Qed.

Lemma term_substitution:
  forall E x t2 T1 T2,
  j (insert x T1 E) t2 T2 ->
  forall t1,
  j E t1 T1 ->
  j E (subst t1 x t2) T2.
Proof.
  do 5 intro; intro h; dependent induction h; intros;
  try solve [
    simpl_subst_goal;
    econstructor;
    eauto using term_weakening, type_weakening with insert_insert map_insert
  ].
  (* Case TVar. *) 
  simpl_subst_goal. unfold subst_idx. dblib_by_cases; lookup_insert_all; eauto with j.

  simpl_subst_goal.
  (* We are dead! [subst t1 _ (TTyAbs _)] does not have the expected behavior. It should shift [t1]. *)
  econstructor.
  eapply IHh. eauto with map_insert.
  eapply type_weakening.
  eauto. eauto.
Abort.

