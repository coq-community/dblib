Set Implicit Arguments.
Require Import List.
Opaque plus. (* avoid pesky reductions *)
Require Import DblibTactics.
Require Import DeBruijn.

(* ---------------------------------------------------------------------------- *)

(* Environments map variables to data. *)

(* Environments are homogeneous -- there is only one kind of variables --
   and non-dependent -- variables do not occur within data. *)

(* What should be the type of an environment? Multiple answers come to mind,
   such as [list A], [nat -> option A], [list (option A)], etc. The choice of
   a definition is guided by the desire that [lookup] and [insert] be total
   functions that satisfy a number of natural laws. In particular, if [insert]
   is a total function, then we cannot expect the domain of an environment to
   be contiguous. This rules out [list A]. Representing an environment by its
   lookup function, of type [nat -> option A], works, but does not allow
   defining [fold] over environments. In the end, representing an environment
   by a finite list of possibly-null entries seems to be a reasonable
   choice. *)

Definition env A :=
  list (option A).

(* What notion of equality over environments do we need? Extensional equality
   of the [lookup] functions seems to be the most natural notion. The
   predicate [agree], defined below, is a bounded version of this
   notion. Perhaps by chance, the basic laws that relate [lookup], [insert],
   and [map] are valid with respect to Leibniz equality, so we do not define
   extensional equality. *)

(* ---------------------------------------------------------------------------- *)

(* Operations on environments. *)

(* The empty environment is undefined everywhere. *)

Definition empty A : env A :=
  nil.

(* Environment lookup. *)

Fixpoint lookup A (x : nat) (e : env A) : option A :=
  match e, x with
  | nil, _ =>
      None
  | entry :: _, 0 =>
      entry
  | _ :: e, S x =>
      lookup x e
  end.

(* [insert x a e] inserts a new variable [x], associated with data [a], in the
   environment [e]. The pre-existing environment entries at index [x] and
   above are shifted up. Thus, [insert x] is closely analogous to [shift x]
   for terms. *)

(* [insert] inserts a non-null entry in the environment. We define it in terms
   of [raw_insert], which can also be used to insert a null entry. [raw_insert]
   is useful because it allows generating every environment (thus, it can be
   used in the formulation of an induction principle). *)

Fixpoint raw_insert A (x : nat) (o : option A) (e : env A) : env A :=
  match x, e with
  | 0, _ =>
      o :: e
  | S x, entry :: e =>
      entry :: raw_insert x o e
  | S x, nil =>
      None :: raw_insert x o e
  end.

Notation insert x a e :=
  (raw_insert x (Some a) e).

(* [map f e] is the environment obtained by applying [f] to every datum
   in the environment [e]. *)

Fixpoint map A B (f : A -> B) (e : env A) :=
  match e with
  | nil =>
      nil
  | None :: e =>
      None :: map f e
  | Some a :: e =>
      Some (f a) :: map f e
  end.

(* [fold f e accu] performs an iteration over all entries in the environment.
   Older entries are visited first: in other words, the initial accumulator
   should make sense at the toplevel, outside of the environment, and is
   pushed successively into every binding, so as to yield a final accumulator
   that makes sense inside this environment. *)

Fixpoint fold A B (f : option A -> B -> B) (e : env A) (accu : B) : B :=
  match e with
  | nil =>
      accu
  | o :: e =>
      f o (fold f e accu)
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
  repeat rewrite one_plus_x_minus_one_left in *;
  repeat rewrite one_plus_x_minus_one_right in * by omega.
  (* I tried [autorewrite with ... using omega]; it does not work. *)

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [empty]. *)

Lemma lookup_empty_None:
  forall A x,
  lookup x (@empty A) = None.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma lookup_empty_Some:
  forall A x (a : A),
  lookup x (@empty _) = Some a ->
  False.
Proof.
  destruct x; simpl; congruence.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [insert]. *)

Lemma lookup_insert_bingo:
  forall A x y (o : option A) e,
  x = y ->
  lookup x (raw_insert y o e) = o.
(* Hence, [lookup x (insert y a e) = Some a]. *)
Proof.
  induction x; intros; destruct y; destruct e; simpl; try solve [
    elimtype False; omega
  | eauto with omega
  ].
Qed.

Lemma lookup_insert_recent:
  forall A x y (o : option A) e,
  x < y ->
  lookup x (raw_insert y o e) = lookup x e.
(* Hence, [lookup x (insert y a e) = lookup x e]. *)
Proof.
  induction x; intros; destruct y; destruct e; simpl; try solve [
    elimtype False; omega
  | eauto with omega
  ].
  (* One troublesome case. *)
  erewrite <- lookup_empty_None. eauto with omega.
Qed.

Lemma lookup_insert_old:
  forall A x y (o : option A) e,
  x > y ->
  lookup x (raw_insert y o e) = lookup (x - 1) e.
(* Hence, [lookup x (insert y a e) = lookup (x - 1) e]. *)
Proof.
  (* Induction over [x], which is non-zero. *)
  induction x; intros; [ elimtype False; omega | replace (S x - 1) with x by omega ].
  (* Case analysis. *)
  destruct y; destruct e; simpl; try solve [ eauto ].
  (* One troublesome case. *)
  rewrite lookup_empty_None. erewrite <- lookup_empty_None. eauto with omega.
  (* Another troublesome case. *)
  destruct x; intros; [ elimtype False; omega | replace (S x - 1) with x in * by omega ].
  simpl lookup at 2.
  eauto with omega.
Qed.

Lemma lookup_shift_insert:
  forall A x y (o : option A) e,
  lookup (shift y x) (raw_insert y o e) = lookup x e.
(* Hence, [lookup (shift y x) (insert y a e) = lookup x e]. *)
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
    rewrite lookup_insert_bingo in * by omega;
    try match goal with h: Some _ = Some _ |- _ => injection h; intro; subst; clear h end
  | rewrite lookup_insert_old in * by omega; one_plus_x_minus_one
  | rewrite lookup_insert_recent in * by omega
  | rewrite lookup_shift_insert in *
  ].

Hint Extern 1 (lookup _ (raw_insert _ _ _) = _) =>
  lookup_insert
: lookup_insert.

Hint Extern 1 (lookup _ _ = _) =>
  lookup_insert_all
: lookup_insert.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [map] and [empty]. *)

Lemma map_empty:
  forall A B (f : A -> B),
  map f (@empty _) = @empty _.
Proof.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [lookup] and [map]. *)

Lemma lookup_map_some:
  forall A B x a e (f : A -> B),
  lookup x e = Some a ->
  lookup x (map f e) = Some (f a).
Proof.
  induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; try solve [
    congruence
  | eauto
  ].
Qed.

Lemma lookup_map_some_reverse:
  forall A B x b e (f : A -> B),
  lookup x (map f e) = Some b ->
  exists a,
  lookup x e = Some a /\ b = f a.
Proof.
  induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; try solve [
    congruence
  | eauto
  ].
  eexists. split. reflexivity. congruence.
Qed.

(* ---------------------------------------------------------------------------- *)

(* [insert] commutes with itself, just like [lift] commutes with itself. *)

Lemma insert_insert:
  forall A k s (a b : option A) e,
  k <= s ->
  raw_insert k a (raw_insert s b e) = raw_insert (1 + s) b (raw_insert k a e).
Proof.
  intros ? k s. generalize s k; clear s k. induction s; intros.
  (* Case [s = 0]. *)
  destruct k; [ | elimtype False; omega ]. reflexivity.
  (* Case [s > 0]. *)
  destruct k.
  (* Sub-case [k = 0]. *)
  reflexivity.
  (* Sub-case [k > 0]. *)
  destruct e; replace (1 + S s) with (S (1 + s)) by omega; simpl; f_equal; eauto with omega.
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

Hint Extern 1 (raw_insert _ _ (raw_insert _ _ _) = _) =>
  insert_insert
: insert_insert.

Hint Extern 1 (_ = raw_insert _ _ (raw_insert _ _ _)) =>
  insert_insert
: insert_insert.

(* ---------------------------------------------------------------------------- *)

(* Interaction between [map] and [insert]. *)

Lemma map_insert:
  forall A B (f : A -> B) x a e,
  map f (insert x a e) = insert x (f a) (map f e).
Proof.
  induction x; intros; destruct e; simpl; eauto.
  rewrite IHx. reflexivity.
  match goal with o: option _ |- _ => destruct o end; f_equal; eauto.
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

Lemma map_raw_insert:
  forall A B (f : A -> B) x e,
  map f (raw_insert x None e) = raw_insert x None (map f e).
Proof.
  induction x; intros; destruct e; simpl; eauto.
  rewrite IHx. reflexivity.
  match goal with o: option _ |- _ => destruct o end; f_equal; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* [map] composes with itself. *)

Lemma map_map_fuse:
  forall A B C (f : B -> C) (g : A -> B) h e,
  (forall (d : A), f (g d) = h d) ->
  map f (map g e) = map h e.
Proof.
  induction e; intros;
  try match goal with o: option _ |- _ => destruct o end;
  simpl; eauto with f_equal.
Qed.

Lemma map_map_exchange:
  forall A F G B (f1 : F -> B) (f2 : A -> F) (g1 : G -> B) (g2 : A -> G) e,
  (forall (d : A), f1 (f2 d) = g1 (g2 d)) ->
  map f1 (map f2 e) = map g1 (map g2 e).
Proof.
  induction e; intros;
  try match goal with o: option _ |- _ => destruct o end;
  simpl; eauto with f_equal.
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
  forall A B (f : B -> A) (g : A -> B) (e : env A),
  (forall x, f (g x) = x) ->
  map f (map g e) = e.
Proof.
  induction e; intros;
  try match goal with o: option _ |- _ => destruct o end;
  simpl; eauto with f_equal.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Properties of [fold]. *)

(* Interaction between [fold] and [empty]. *)

Lemma fold_empty:
  forall A B (f : option A -> B -> B) accu,
  fold f (@empty _) accu = accu.
Proof.
  reflexivity.
Qed.

(* Interaction between [fold] and [insert]. *)

Lemma fold_insert:
  forall A B (f : option A -> B -> B) o e accu,
  fold f (raw_insert 0 o e) accu = f o (fold f e accu).
Proof.
  reflexivity.
Qed.

(* An induction principle. In order to prove that a property [P] holds of
   [fold f e accu], it suffices to hold that it holds of the initial
   accumulator and that it is preserved by one iteration. The statement is
   expressed in terms of [empty] and [raw_insert], so the fact that
   environments are implemented as lists is not exposed. *)

Lemma fold_invariant:
  forall A B (P : env A -> B -> Prop) f accu,
  P (@empty _) accu ->
  (forall o e accu, P e accu -> P (raw_insert 0 o e) (f o accu)) ->
  forall e,
  P e (fold f e accu).
Proof.
  intros ? ? ? ? ? init step.
  induction e; simpl.
  eapply init.
  eapply step. eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The definitions and properties that follow should be independent of the
   details of the definitions of [empty], [lookup], [insert], and [map]. *)

Opaque empty lookup raw_insert map.

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
  forall A (e : env A) k o,
  length e k ->
  length (raw_insert 0 o e) (1 + k).
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
  forall x o,
  x <= k ->
  agree (raw_insert x o e1) (raw_insert x o e2) (1 + k).
Proof.
  unfold agree. do 8 intro. intros n ?.
  (* Reason by cases: [x = n], [x < n], [x > n]. *)
  case (le_gt_dec x n); [ case (eq_nat_dec x n) | ]; intros;
  (* In each case, [lookup_insert] simplifies the goal. *)
  do 2 lookup_insert; eauto with omega.
Qed.

Hint Resolve agree_below agree_empty agree_insert : agree.

(* ---------------------------------------------------------------------------- *)

(* A definition of when an environment subsumes another, up to a notion of
   subsumption on environment entries. *)

Section Subsume.

  Variable A : Type.

  Variable sub : A -> A -> Prop.

  Variable sub_reflexive:
    forall a,
    sub a a.

  Variable sub_transitive:
    forall a1 a2 a3,
    sub a1 a2 ->
    sub a2 a3 ->
    sub a1 a3.

  (* Subsumption is first extended to options. *)

  Definition osub (o1 o2 : option A) :=
    forall a2,
    o2 = Some a2 ->
    exists a1,
    o1 = Some a1 /\ sub a1 a2.

  Lemma osub_None:
    forall o,
    osub o None.
  Proof.
    unfold osub. congruence.
  Qed.

  Lemma osub_Some_Some:
    forall a1 a2,
    sub a1 a2 ->
    osub (Some a1) (Some a2).
  Proof.
    unfold osub. intros ? ? ? ? h. injection h; clear h; intro; subst; eauto.
  Qed.

  (* Then, it is extended pointwise to environments. *)

  Definition subsume (e1 e2 : env A) :=
    forall x,
    osub (lookup x e1) (lookup x e2).

  (* Subsumption of environments is reflexive and transitive. *)

  Lemma osub_reflexive:
    forall o,
    osub o o.
  Proof.
    unfold osub. eauto.
  Qed.

  Lemma subsume_reflexive:
    forall e,
    subsume e e.
  Proof.
    unfold subsume. eauto using osub_reflexive.
  Qed.

  Lemma osub_transitive:
    forall o1 o2 o3,
    osub o1 o2 ->
    osub o2 o3 ->
    osub o1 o3.
  Proof.
    unfold osub. intros ? ? ? hs1 hs2 a3 h3.
    generalize (hs2 _ h3); intros [ a2 [ h2 ? ]].
    generalize (hs1 _ h2); intros [ a1 [ h1 ? ]].
    eauto.
  Qed.

  Lemma subsume_transitive:
    forall e1 e2 e3,
    subsume e1 e2 ->
    subsume e2 e3 ->
    subsume e1 e3.
  Proof.
    unfold subsume. eauto using osub_transitive.
  Qed.

  (* Every environment subsumes the empty environment. *)

  Lemma subsume_empty:
    forall e,
    subsume e (@empty _).
  Proof.
    unfold subsume. intros. rewrite lookup_empty_None. apply osub_None.
  Qed.

  (* Extending two environments with a new variable preserves subsumption. *)

  Lemma subsume_insert:
    forall e1 e2,
    subsume e1 e2 ->
    forall x o1 o2,
    osub o1 o2 ->
    subsume (raw_insert x o1 e1) (raw_insert x o2 e2).
  Proof.
    unfold subsume. do 7 intro. intros n.
    (* Reason by cases: [x = n], [x < n], [x > n]. *)
    case (le_gt_dec x n); [ case (eq_nat_dec x n) | ]; intros;
    (* In each case, [lookup_insert] simplifies the goal. *)
    repeat lookup_insert; eauto.
  Qed.

  (* Applying a transformation [f] pointwise to two environments preserves
     environment subsumption, provided [f] preserves [sub]. *)

  Lemma subsume_map:
    forall f,
    (forall a1 a2, sub a1 a2 -> sub (f a1) (f a2)) ->
    forall e1 e2,
    subsume e1 e2 ->
    subsume (map f e1) (map f e2).
  Proof.
    intros ? hf ? ? hs. intros ? b2 hlm2.
    generalize (lookup_map_some_reverse _ _ _ hlm2); intros [ ? [ hl2 ? ]]. subst.
    generalize (hs _ _ hl2); intros [ a1 [ ? ? ]].
    eauto using lookup_map_some.
  Qed.

End Subsume.

Hint Resolve osub_reflexive osub_Some_Some subsume_reflexive
subsume_transitive subsume_empty subsume_insert subsume_map : subsume.

(* ---------------------------------------------------------------------------- *)

(* Extending an environment with a list of bindings found in a pattern. *)

(* Note that we cannot define the concatenation of two environments, because
   we view environments as total functions, so we do not have precise control
   over their domain. Only a list has finite domain. *)

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
  forall (A : Type) n x nx (o : option A) e1 e2,
  List.length e2 = n ->
  n + x = nx ->
  raw_insert nx o (concat e1 e2) = concat (raw_insert x o e1) e2.
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
  forall (A : Type) n x nx (a : option A) (b : A) e1,
  n + x = nx ->
  raw_insert nx a (concat e1 (replicate n b)) = concat (raw_insert x a e1) (replicate n b).
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

Global Opaque empty lookup raw_insert map.

