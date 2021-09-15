Set Implicit Arguments.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import Lia.

(* A hint for invoking [f_equal] as part of [eauto] search. *)

Create HintDb f_equal.

#[export] Hint Extern 2 => f_equal : f_equal.

(* Hints for invoking omega on arithmetic subgoals. *)

Create HintDb lia.

#[export] Hint Extern 1 (_ = _ :> nat) => reflexivity : lia.
#[export] Hint Extern 3 (_ = _ :> nat) => lia : lia.
#[export] Hint Extern 3 (_ <> _ :> nat) => lia : lia.
#[export] Hint Extern 3 (_ < _) => lia : lia.
#[export] Hint Extern 3 (_ > _) => lia : lia.
#[export] Hint Extern 3 (_ <= _) => lia : lia.
#[export] Hint Extern 3 (_ >= _) => lia : lia.

(* Dealing with integer comparisons. *)

Ltac dblib_intro_case_clear :=
  let h := fresh in
  intro h; case h; clear h.

Ltac dblib_inspect_cases :=
  match goal with
  | |- context [le_gt_dec ?n ?n'] =>
      case (le_gt_dec n n')
  | h: context [le_gt_dec ?n ?n'] |- _ =>
      revert h; case (le_gt_dec n n'); intro h
  | |- context [eq_nat_dec ?n ?n'] =>
      case (eq_nat_dec n n')
  | h: context [eq_nat_dec ?n ?n'] |- _ =>
      revert h; case (eq_nat_dec n n'); intro h
  | |- context [(lt_eq_lt_dec ?n ?n')] =>
       case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]
  | h: context [(lt_eq_lt_dec ?n ?n')] |- _ =>
       revert h; case (lt_eq_lt_dec n n'); [ dblib_intro_case_clear | idtac ]; intro h
  end.

Ltac dblib_by_cases :=
  repeat dblib_inspect_cases; try solve [ intros; exfalso; lia ]; intros.

