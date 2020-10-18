Require Import ssreflect.

From Dblib Require Import DeBruijn.

Module weird_traverse1.
  Inductive term : Set :=
  | TAbs : term -> term
  | TApp : term -> term -> term
  | TVar : nat -> term.

  Instance Var_term : Var term := {var := TVar}.

  Fixpoint id (t : term) : term :=
    match t with
    | TAbs t => TAbs (id t)
    | TApp t1 t2 => TApp (id t1) (id t2)
    | TVar n => TVar n
    end.

  Lemma id_id : forall t, id t = t.
  Proof using. elim; cbn; congruence. Qed.

  Definition traverse_term (f : nat -> nat -> term) (l : nat) (t : term) : term :=
    (fix aux l t { struct t } :=
       match t with
       | TAbs t => TAbs (aux (S l) t)
       | TApp t1 t2 => TApp (aux l t1) (aux l t2)
       | TVar n => f l n
       end) l (id t).

  Instance Traverse_term : Traverse term term :=
    {traverse := traverse_term}.

  Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
    constructor.
    prove_traverse_var_injective.
  Fail Qed.
  Abort.

  Instance Traverse_term_functorial : @TraverseFunctorial term _ term _.
    constructor.
    prove_traverse_functorial.
  Fail Qed.
  Abort.

  Instance TraverseRelative_term : @TraverseRelative term term _.
    constructor.
    prove_traverse_relative.
  Fail Qed.
  Abort.

  Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
    constructor.
    prove_traverse_identifies_var.
  Qed.

  Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
    constructor.
    prove_traverse_var_is_identity.
  Fail Qed.
  Abort.
End weird_traverse1.
