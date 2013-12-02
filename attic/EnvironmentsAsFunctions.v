Set Implicit Arguments.
Require Import FunctionalExtensionality.
Require Import DblibTactics.
Require Import DeBruijn.

(* ---------------------------------------------------------------------------- *)

(* Environments map variables to data. *)

(* Environments are homogeneous -- there is only one kind of variables --
   and non-dependent -- variables do not occur within data. *)

(* We represent environments as functions of type [nat -> option A], as
   opposed to lists of type [list A], because functions are slightly more
   pleasant to work with than lists. In particular, their domain need not
   be contiguous, and this makes the definition of insertion more natural. *)

Definition env A :=
  nat -> option A.

(* ---------------------------------------------------------------------------- *)

(* Operations on environments. *)

(* The empty environment is undefined everywhere. *)

Definition empty A : env A :=
  fun y => None.

(* Environment lookup is just function application. *)

Definition lookup A (x : nat) (e : env A) : option A :=
  e x.

(* [insert x a e] inserts a new variable [x], associated with data [a], in the
   environment [e]. The pre-existing environment entries at index [x] and
   above are shifted up. Thus, [insert x] is closely analogous to [shift x]
   for terms. *)

Definition insert A (x : nat) (a : A) (e : env A) : env A :=
  fun y =>
    match lt_eq_lt_dec x y with
    | inleft (left _)  (* x < y *) => e (y - 1)
    | inleft (right _) (* x = y *) => Some a
    | inright _        (* x > y *) => e y
    end.

(* [remove x] is the inverse of [insert x a]. That is, [remove x e] destroys
   the variable [x] in the environment [e]. The variables at index [x + 1]
   and above are shifted down. Thus, [remove x] is closely analogous to
   [subst v x] for terms. *)

(* Experience suggests that it is good style to always work with [insert]
   and avoid using [remove]. This leads to simpler goals and proofs. *)

Definition remove A (x : nat) (e : env A) : env A :=
  fun y =>
    match le_gt_dec x y with
    | left _  (* x <= y *) => e (1 + y)
    | right _ (* x > y *)  => e y
    end.

(* [map f e] is the environment obtained by applying [f] to every datum
   in the environment [e]. *)

Definition map A (f : A -> A) (e : env A) :=
  fun y =>
    match e y with
    | None   => None
    | Some a => Some (f a)
    end.

(* ---------------------------------------------------------------------------- *)

(* Basic arithmetic simplifications. *)

Lemma one_plus_x_minus_one_left:
  forall x,
  (1 + x) - 1 = x.
Proof.
  intros. omega.
Qed.

Lemma one_plus_x_minus_one_right:
  forall x,
  x > 0 ->
  1 + (x - 1) = x.
Proof.
  intros. omega.
Qed.

Ltac one_plus_x_minus_one :=
  repeat rewrite one_plus_x_minus_one_left;
  repeat rewrite one_plus_x_minus_one_right by omega.
  (* I tried [autorewrite with ... using omega]; it does not work. *)

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [empty]. *)

Lemma lookup_empty_None:
  forall A x,
  lookup x (@empty A) = None.
Proof.
  unfold lookup, empty. reflexivity.
Qed.

Lemma lookup_empty_Some:
  forall A x (a : A),
  lookup x (@empty _) = Some a ->
  False.
Proof.
  unfold lookup, empty. intros. congruence.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [insert]. *)

Lemma lookup_insert_bingo:
  forall A x y (a : A) e,
  x = y ->
  lookup x (insert y a e) = Some a.
Proof.
  intros. subst. unfold lookup, insert. dblib_by_cases. reflexivity.
Qed.

Lemma lookup_insert_recent:
  forall A x y (a : A) e,
  x < y ->
  lookup x (insert y a e) = lookup x e.
Proof.
  intros. unfold lookup, insert. dblib_by_cases. reflexivity.
Qed.

Lemma lookup_insert_old:
  forall A x y (a : A) e,
  x > y ->
  lookup x (insert y a e) = lookup (x - 1) e.
Proof.
  intros. unfold lookup, insert. dblib_by_cases. reflexivity.
Qed.

Lemma lookup_shift_insert:
  forall A x y (a : A) e,
  lookup (shift y x) (insert y a e) = lookup x e.
Proof.
  intros. destruct_lift_idx.
  rewrite lookup_insert_old by omega. f_equal. omega.
  rewrite lookup_insert_recent by omega. reflexivity.
Qed.

Ltac lookup_insert :=
  first [
    rewrite lookup_insert_bingo by omega
  | rewrite lookup_insert_old by omega; one_plus_x_minus_one
  | rewrite lookup_insert_recent by omega
  | rewrite lookup_shift_insert
  ].

Ltac lookup_insert_all :=
  first [
    rewrite lookup_insert_bingo in * by omega
  | rewrite lookup_insert_old in * by omega; one_plus_x_minus_one
  | rewrite lookup_insert_recent in * by omega
  | rewrite lookup_shift_insert in *
  ].

Hint Extern 1 (lookup _ (insert _ _ _) = _) =>
  lookup_insert
: lookup_insert.

Hint Extern 1 (lookup _ _ = _) =>
  lookup_insert_all
: lookup_insert.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [map]. *)

Lemma lookup_map_some:
  forall A x (a : A) e f,
  lookup x e = Some a ->
  lookup x (map f e) = Some (f a).
Proof.
  unfold lookup, map. intros. case_eq (e x); intros; congruence.
Qed.

(* ---------------------------------------------------------------------------- *)

(* [insert] commutes itself, just like [lift] commutes with itself. *)

Lemma insert_insert:
  forall A k s (a b : A) e,
  k <= s ->
  insert k a (insert s b e) = insert (1 + s) b (insert k a e).
Proof.
  unfold insert. intros. extensionality y. dblib_by_cases; eauto with f_equal omega.
Qed.

(* Attempting to rewrite in both directions may seem redundant, because of the
   symmetry of the law [insert_insert]. It is not: because [omega] fails in
   the presence of meta-variables, rewriting in one direction may be possible
   while the other direction fails. *)

Ltac insert_insert :=
  first [
    rewrite insert_insert by omega; reflexivity
  | rewrite <- insert_insert by omega; reflexivity
  ].

Hint Extern 1 (insert _ _ (insert _ _ _) = _) =>
  insert_insert
: insert_insert.

Hint Extern 1 (_ = insert _ _ (insert _ _ _)) =>
  insert_insert
: insert_insert.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [remove] and [insert]. *)

Lemma remove_insert:
  forall A x (a : A) e,
  remove x (insert x a e) = e.
Proof.
  intros. unfold remove, insert. extensionality y.
  dblib_by_cases; eauto with f_equal omega.
Qed.

Lemma insert_remove_bingo:
  forall A x y (a : A) e,
  lookup x e = Some a ->
  y = x ->
  insert y a (remove x e) = e.
Proof.
  unfold lookup, remove, insert. intros. extensionality z.
  dblib_by_cases; eauto with f_equal omega; congruence.
Qed.

Lemma insert_remove_recent:
  forall A x y (a : A) e,
  y <= x ->
  insert y a (remove x e) = remove (1 + x) (insert y a e).
Proof.
  intros. unfold insert, remove. extensionality z.
  dblib_by_cases; eauto with f_equal omega.
Qed.

Lemma insert_remove_old:
  forall A x y (a : A) e,
  y >= x ->
  insert y a (remove x e) = remove x (insert (1 + y) a e).
Proof.
  intros. unfold insert, remove. extensionality z.
  dblib_by_cases; eauto with f_equal omega.
Qed.

Ltac insert_remove :=
  first [
    rewrite insert_remove_recent by omega; reflexivity
  | rewrite insert_remove_old by omega; reflexivity
  | rewrite <- insert_remove_recent by omega; reflexivity
  | rewrite <- insert_remove_old by omega; reflexivity
  ].

Hint Extern 1 (remove _ (insert _ _ _) = insert _ _ (remove _ _)) =>
  insert_remove
: insert_remove.

Hint Extern 1 (insert _ _ (remove _ _)= remove _ (insert _ _ _) ) =>
  insert_remove
: insert_remove.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [remove]. *)

Lemma lookup_remove:
  forall A x y (e : env A),
  lookup y (remove x e) = lookup (shift x y) e.
Proof.
  intros.  unfold lookup, remove. destruct_lift_idx; reflexivity.
Qed.

Lemma lookup_remove_old:
  forall A x y (e : env A),
  y >= x ->
  lookup y (remove x e) = lookup (1 + y) e.
Proof.
  intros. unfold lookup, remove. dblib_by_cases; eauto with f_equal omega.
Qed.

Lemma lookup_remove_recent:
  forall A x y (e : env A),
  y < x ->
  lookup y (remove x e) = lookup y e.
Proof.
  intros. unfold lookup, remove. dblib_by_cases; eauto with f_equal omega.
Qed.

Ltac lookup_remove :=
  first [
    rewrite lookup_remove_old by omega; one_plus_x_minus_one
  | rewrite lookup_remove_recent by omega
  ].

Hint Extern 1 (lookup _ (remove _ _) = _) =>
  lookup_remove
: lookup_remove.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [map] and [insert]. *)

Lemma map_insert:
  forall A f x (a : A) e,
  map f (insert x a e) = insert x (f a) (map f e).
Proof.
  unfold map, insert. intros. extensionality y. dblib_by_cases; eauto with f_equal omega.
Qed.

Ltac map_insert :=
  first [
    rewrite map_insert; reflexivity
  | rewrite <- map_insert; reflexivity
  ].  

Hint Extern 1 (map _ (insert _ _ _) = insert _ _ (map _ _)) =>
  map_insert
: map_insert.

Hint Extern 1 (insert _ _ (map _ _) = map _ (insert _ _ _)) =>
  map_insert
: map_insert.

(* ---------------------------------------------------------------------------- *)

(* [map] composes with itself. *)

Lemma map_map_fuse:
  forall A f g h e,
  (forall (d : A), f (g d) = h d) ->
  map f (map g e) = map h e.
Proof.
  intros. unfold map. extensionality y. case_eq (e y); congruence.
Qed.

Lemma map_map_exchange:
  forall A f1 f2 g1 g2 e,
  (forall (d : A), f1 (f2 d) = g1 (g2 d)) ->
  map f1 (map f2 e) = map g1 (map g2 e).
Proof.
  intros. unfold map. extensionality y. case_eq (e y); congruence.
Qed.

Lemma map_lift_map_lift:
  forall T k s wk ws (e : env T),
  forall `{Lift T},
  @LiftLift T _ ->
  k <= s ->
  map (lift wk k) (map (lift ws s) e) = map (lift ws (wk + s)) (map (lift wk k) e).
Proof.
  eauto using map_map_exchange, @lift_lift.
Qed.

Lemma map_map_vanish:
  forall A f g (e : env A),
  (forall x, f (g x) = x) ->
  map f (map g e) = e.
Proof.
  intros. unfold map. extensionality y. case_eq (e y); congruence.
Qed.

(* ---------------------------------------------------------------------------- *)

(* A definition of (an upper bound on) the length of an environment. *)

Definition length A (e : env A) (k : nat) :=
  forall x,
  k <= x ->
  lookup x e = None.

(* Every variable that is defined in the environment is less than the
   length of the environment. *)

Lemma defined_implies_below_length:
  forall A (e : env A) x k a,
  length e k ->
  lookup x e = Some a ->
  x < k.
Proof.
  intros.
  (* If [x < k] holds, the result is immediate. Consider the other case,
     [k <= x]. *)
  case (le_gt_dec k x); intro; try tauto.
  (* By definition of [length], [lookup x e] is [None]. *)
  assert (lookup x e = None). auto.
  (* We obtain a contradiction. *)
  congruence.
Qed.

Hint Resolve defined_implies_below_length : lift_idx_hints.

(* The empty environment has zero length. *)

Lemma length_empty:
  forall A k,
  length (@empty A) k.
Proof.
  repeat intro. apply lookup_empty_None.
Qed.

(* Extending an environment increments its length by one. *)

Lemma length_insert:
  forall A (e : env A) k a,
  length e k ->
  length (insert 0 a e) (1 + k).
Proof.
  unfold length; intros. lookup_insert. eauto with omega.
Qed.

Hint Resolve length_empty length_insert : length.

Hint Resolve length_insert : construction_closed.

(* ---------------------------------------------------------------------------- *)

(* A definition of when two environments agree up to length [k]. *)

Definition agree A (e1 e2 : env A) (k : nat) :=
  forall x,
  x < k ->
  lookup x e1 = lookup x e2.

(* A simple consequence of the definition. *)

Lemma agree_below:
  forall A (e1 e2 : env A) x a k,
  lookup x e1 = Some a ->
  length e1 k ->
  agree e1 e2 k ->
  lookup x e2 = Some a.
Proof.
  do 6 intro. intros hlookup ? ?.
  rewrite <- hlookup. symmetry.
  eauto using defined_implies_below_length.
Qed.

(* The empty environment agrees with every environment up to length [0]. *)

Lemma agree_empty:
  forall A (e : env A),
  agree (@empty _) e 0.
Proof.
  unfold agree. intros. elimtype False. omega.
Qed.

(* If two environments that agree up to [k] are extended with a new variable,
   then they agree up to [k+1]. *)

Lemma agree_insert:
  forall A (e1 e2 : env A) k,
  agree e1 e2 k ->
  forall x a,
  x <= k ->
  agree (insert x a e1) (insert x a e2) (1 + k).
Proof.
  unfold agree, lookup, insert. intros. dblib_by_cases; eauto with omega.
Qed.

Hint Resolve agree_below agree_empty agree_insert : agree.

(* ---------------------------------------------------------------------------- *)

(* Extending an environment with a list of bindings found in a pattern. *)

(* Note that we cannot define the concatenation of two environments, because
   we view environments as functions, so we do not have precise control over
   their domain. Only a list has finite domain. *)

(* Concatenation is just an iterated version of [insert 0]. *)

Fixpoint concat (A : Type) (e1 : env A) (e2 : list A) : env A :=
  match e2 with
  | nil =>
      e1
  | cons a e2 =>
      concat (insert 0 a e1) e2
  end.

(* Concatenation acts upon the length of the environment in an obvious
   manner. *)

Lemma length_concat:
  forall A (e2 : list A) (e1 : env A) n1 n,
  length e1 n1 ->
  n1 + List.length e2 = n ->
  length (concat e1 e2) n.
Proof.
  induction e2; simpl; intros.
  replace n with n1 by omega. assumption.
  eauto using length_insert with omega.
Qed.

Hint Resolve length_concat : length construction_closed.

(* If [e1] and [e2] agree up to depth [k], then, after extending them
   with a common suffix [e], they agree up to depth [k + length e]. *)

Lemma agree_concat:
  forall A (e : list A) (e1 e2 : env A) k n,
  agree e1 e2 k ->
  k + List.length e = n ->
  agree (concat e1 e) (concat e2 e) n.
Proof.
  induction e; simpl; intros.
  replace n with k by omega. assumption.
  eauto using agree_insert with omega.
Qed.

Hint Resolve agree_concat : agree.

(* Concatenation and insertion commute. *)

Lemma insert_concat:
  forall (A : Type) n x nx (a : A) e1 e2,
  List.length e2 = n ->
  n + x = nx ->
  insert nx a (concat e1 e2) = concat (insert x a e1) e2.
Proof.
  induction n; intros; subst; destruct e2; simpl in *; try discriminate; auto.
  rewrite insert_insert by omega.
  erewrite <- (IHn (1 + x)) by first [ congruence | eauto ].
  eauto with f_equal omega.
Qed.

(* [replicate n a] is a list of [n] elements, all of which are
   equal to [a]. *)

Fixpoint replicate (A : Type) (n : nat) (a : A) : list A :=
  match n with
  | 0 =>
      @nil _
  | S n =>
      cons a (replicate n a)
  end.

(* The list [replicate n a] has length [n]. *)

Lemma length_replicate:
  forall (A : Type) n (a : A),
  List.length (replicate n a) = n.
Proof.
  induction n; simpl; auto.
Qed.

(* A special case of [insert_concat]. *)

Lemma insert_concat_replicate:
  forall (A : Type) n x nx (a b : A) e1,
  n + x = nx ->
  insert nx a (concat e1 (replicate n b)) = concat (insert x a e1) (replicate n b).
Proof.
  eauto using insert_concat, length_replicate.
Qed.

(* [concat . (replicate . a)] is just an iterated version of [insert . a]. *)

Lemma concat_replicate_is_iterated_insert:
  forall (A : Type) n (a : A) e,
  insert n a (concat e (replicate n a)) =
  concat e (replicate (S n) a).
Proof.
  intros. simpl. eauto using insert_concat, length_replicate.
Qed.

Hint Resolve insert_concat length_replicate insert_concat_replicate
concat_replicate_is_iterated_insert : insert_concat.

(* A special case of [length_concat]. *)

Lemma length_concat_replicate:
  forall A (a : A) (e1 : env A) n1 n2 n,
  length e1 n1 ->
  n1 + n2 = n ->
  length (concat e1 (replicate n2 a)) n.
Proof.
  intros. eapply length_concat. eauto. rewrite length_replicate. eauto.
Qed.

Hint Resolve length_concat_replicate : length construction_closed.

(* ---------------------------------------------------------------------------- *)

(* Make some definitions opaque, so that Coq does not over-simplify in
   unexpected (and fragile) ways. *)

Global Opaque empty lookup insert remove map.

