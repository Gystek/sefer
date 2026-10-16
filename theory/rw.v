Require Import List.
Import ListNotations.
Require Import Vector.

Definition compose {t u v : Type} (f : u -> v) (g : t -> u) : t -> v := fun x => f (g x).
Definition flip {t u v : Type} (f : t -> u -> v) := fun x y => f y x.

Definition bind {t u : Type} (x : option t) (f : t -> option u) : option u :=
  match x with
  | Some x => f x
  | None => None
  end.

Definition fmap {t u : Type} (f : t -> u) (x : option t) : option u :=
  bind x (compose Some f).
  
Definition some_if {t : Type} (p : t -> bool) (x : t) : option t :=
  if p x then Some x else None.

Definition unwrap_or {t : Type} (x : option t) (a : t) : t :=
  match x with
  | Some x => x
  | None => a
  end.

Inductive io (u t : Type) : Type :=
| next (e : u) (x : t)
| last (e : u)
| empty.

Class Iterable (t it : Type) := nextI : t -> io it t.

Definition sigma (t u : Type) { _ : Iterable t u } : Type := t -> io u t.

Definition output u : Type : Type := list u.
Definition yield {u : Type} (x : u) : output u := [x].
Definition eoo {u : Type} : output u := [].
Definition cmb {u : Type} (o : output u) (p : output u) : output u
  := o ++ p.

(*
 * The iterator-running function takes a maximum number of execution
 * steps for Rocq to know it does terminate.
 * There is no loss of generality due to universal quantification
 * of n whenever this function is called.
 *)
Fixpoint runN {t u : Type} {_ : Iterable t u } (x : t)  (n : nat) (i : sigma t u) {struct n} : output u :=
  match (n, i x) with
  | (0, _)
  | (_, empty _ _) => eoo
  | (S m, next _ _ e x') => cmb (yield e) (runN x' m i)
  | (_, last _ _ e) => yield e
  end.

Inductive filterk {t u : Type} { Hu : Iterable t u } :
  t -> (u -> bool) -> sigma t u -> sigma t u -> Prop :=
| f_empty : forall x p s s', s x = empty _ _
                             /\ s' x = empty _ _
                             -> filterk x p s s'
| f_last_f : forall x a p s s', s x = last _ _ a
                                /\ p a = false
                                /\ s' x = empty _ _
                                -> filterk x p s s'
| f_last_t : forall x a p s s', s x = last _ _ a
                                /\ p a = true
                                /\ s' x = last _ _ a
                                -> filterk x p s s'
| f_next_f : forall x x' a p s s', s x = next _ _ a x'
                                   /\ p a = false
                                   /\ filterk x' p s s'
                                   -> filterk x p s s'
| f_next_t : forall x x' a p s s', s x = next _ _ a x'
                                   /\ p a = true
                                   /\ s' x = next _ _ a x'
                                   /\ filterk x' p s s'
                                   -> filterk x p s s'.

(* b = δ p a *)
Definition filterR {t u : Type} { _ : Iterable t u }
  (p : u -> bool) (s : sigma t u) (s' : sigma t u) : Prop :=
  forall x : t, filterk x p s s'.

Inductive mapk {t u v : Type} { Hu : Iterable t u } { Hv : Iterable t v } :
  t -> (u -> v) -> sigma t u -> sigma t v -> Prop :=
| m_empty : forall x f s s', s x = empty _ _ /\ s' x = empty _ _ -> mapk x f s s'
| m_last : forall x a b f s s', s x = last _ _ a /\ f a = b /\ s' x = last _ _ b -> mapk x f s s'
| m_next : forall x x' a b f s s', s x = next _ _ a x'
                                   /\ s' x = next _ _ b x'
                                   /\ f a = b
                                   /\ mapk x' f s s'
                                   -> mapk x f s s'.

(* b = μ f a *)
Definition mapR {t u v : Type} { _ : Iterable t u  } { _ : Iterable t v }
  (f : u -> v) (s : sigma t u) (s' : sigma t v) : Prop :=
  forall x : t, mapk x f s s'.

Inductive filter_mapk {t u v : Type} { Hu : Iterable t u } { Hv : Iterable t v } :
  t -> (u -> option v) -> sigma t u -> sigma t v -> Prop :=
| fm_empty : forall x h s s', s x = empty _ _ /\ s' x = empty _ _ -> filter_mapk x h s s'
| fm_last_some : forall x a b h s s', s x = last _ _ a
                                      /\ h a = Some b
                                      /\ s' x = last _ _ b
                                      -> filter_mapk x h s s'
| fm_last_none : forall x a h s s', s x = last _ _ a
                                    /\ h a = None
                                    /\ s' x = empty _ _
                                    -> filter_mapk x h s s'
| fm_next_some : forall x x' a b h s s', s x = next _ _ a x'
                                         /\ h a = Some b
                                         /\ s' x = next _ _ b x'
                                         /\ filter_mapk x' h s s'
                                         -> filter_mapk x h s s'
| fm_next_none : forall x x' a h s s', s x = next _ _ a x'
                                       /\ h a = None
                                       /\ filter_mapk x' h s s'
                                       -> filter_mapk x h s s'.

(* b = δμ h a *)
Definition filter_mapR {t u v : Type} { _ : Iterable t u } { _ : Iterable t v }
  (h : u -> option v) (s : sigma t u) (s' : sigma t v) : Prop :=
  forall x : t, filter_mapk x h s s'.

Inductive duplicatek {t u : Type} { Hu : Iterable t u } (n : nat) { Hun : Iterable t (Vector.t u n) } :
  t -> sigma t u -> sigma t (Vector.t u n) -> Prop :=
| d_empty : forall x s s', s x = empty _ _ /\ s' x = empty _ _ -> duplicatek n x s s'
| d_last : forall x a s s', s x = last _ _ a
                            /\ s' x = last _ _ (Vector.const a n)
                            -> duplicatek n x s s'
| d_next : forall x x' a s s', s x = next _ _ a x'
                               /\ s' x = next _ _ (Vector.const a n) x'
                               /\ duplicatek n x' s s'
                               -> duplicatek n x s s'.

(* b = βn a *)
Definition duplicateR {t u : Type} { _ : Iterable t u } (n : nat) { _ : Iterable t (Vector.t u n) }
  (s : sigma t u) (s' : sigma t (Vector.t u n)) : Prop :=
  forall x : t, duplicatek n x s s'.

Inductive enumeratek {t u : Type} { Hu : Iterable t u } { HNu : Iterable t (nat * u) } :
  t -> nat -> sigma t u -> sigma t (nat * u) -> Prop :=
| e_empty : forall x n s s', s x = empty _ _ /\ s' x = empty _ _ -> enumeratek x n s s'
| e_last : forall x a n s s', s x = last _ _ a
                              /\ s' x = last _ _ (n, a)
                              -> enumeratek x n s s'
| e_next : forall x x' a n s s', s x = next _ _ a x'
                                 /\ s' x = next _ _ (n, a) x'
                                 /\ enumeratek x' (S n) s s'
                                 -> enumeratek x n s s'.

(* b = α a *)
Definition enumerateR {t u : Type} { _ : Iterable t u } { _ : Iterable t (nat * u) }
  (s : sigma t u) (s' : sigma t (nat * u)) : Prop :=
  forall x : t, enumeratek x 0 s s'.

Inductive iter_eq {t t' u : Type } { H : Iterable t u } { H' : Iterable t' u } :
  t -> t' -> sigma t u -> sigma t' u -> Prop :=
| ieq_empty : forall x y s s', s x = empty _ _ /\ s' y = empty _ _ -> iter_eq x y s s'
| ieq_last : forall x y a s s', s x = last _ _ a /\ s' y = last _ _ a -> iter_eq x y s s'
| ieq_next : forall x y x' y' a s s', s x = next _ _ a x'
                                      /\ s' y = next _ _ a y'
                                      /\ iter_eq x' y' s s'
                                      -> iter_eq x y s s'.

Inductive iter_pref {t t' u : Type} { H : Iterable t u } { H' : Iterable t' u } :
  t -> t' -> sigma t u -> sigma t' u -> option t' -> Prop :=
| ipf_empty : forall x y s s', s x = empty _ _ -> iter_pref x y s s' (Some y)
| ipf_last_last : forall x y a s s', s x = last _ _ a
                                     /\ s' y = last _ _ a
                                     -> iter_pref x y s s' None
| ipf_last_next : forall x y y' a s s', s x = last _ _ a
                                        /\ s' y = next _ _ a y'
                                        -> iter_pref x y s s' (Some y')
| ipf_next : forall x x' y y' a p s s', s x = next _ _ a x'
                                        /\ s' y = next _ _ a y'
                                        /\ iter_pref x' y' s s' p
                                        -> iter_pref x y s s' p.

Inductive flattenk {t t' u v : Type }
  { Ht'u : Iterable t' u } { Ht'v : Iterable t' v }
  { Htt't'u : Iterable t (t' * sigma t' u) }
  { Htv : Iterable t v } :
  t -> (sigma t' u -> sigma t' v) -> sigma t (t' * sigma t' u) -> sigma t v -> Prop :=
| fl_empty : forall x f s s', s x = empty _ _ /\ s' x = empty _ _ -> flattenk x f s s'
| fl_last : forall x y r f s s', s x = last _ _ (y, r)
                                    /\ iter_eq y x (f r) s'
                                    -> flattenk x f s s'
| fl_next : forall x x' y r f s s', s x = next _ _ (y, r) x'
                                    /\ iter_pref y x (f r) s' (Some x')
                                    /\ flattenk x' f s s'
                                    -> flattenk x f s s'.

(* b = ο f a *)
Definition flattenR {t t' u v : Type}
  { _ : Iterable t' u } { _ : Iterable t' v } { _ : Iterable t (t' * sigma t' u) } { _ : Iterable t v }
  (f : sigma t' u -> sigma t' v) (s : sigma t (t' * sigma t' u)) (s' : sigma t v) : Prop :=
  forall x : t, flattenk x f s s'.

Inductive intercalatek {t u : Type} { H : Iterable t u } :
  t -> u -> sigma t u -> sigma t u -> Prop :=
| i_empty : forall x i s s', s x = empty _ _ /\ s' x = empty _ _ -> intercalatek x i s s'
| i_last : forall x a i s s', s x = last _ _ a /\ s' x = last _ _ a -> intercalatek x i s s'
| i_next : forall x x' x'' a i s s', s x = next _ _ a x'
                                    /\ s' x = next _ _ i x''
                                    /\ s' x'' = next _ _ a x'
                                    /\ intercalatek x' i s s'
                                    -> intercalatek x i s s'.

(* b = ι i a *)
Definition intercalateR {t u : Type} { _ : Iterable t u }
  (i : u) (s : sigma t u) (s' : sigma t u) : Prop :=
  forall x : t, intercalatek x i s s'.

(* init_last l x' x iff l = x' ++ [x] *)
Inductive init_last {t : Type} : list t -> list t -> t -> Prop :=
| il_last : forall x, init_last [x] [] x
| il_cons : forall x y x' y', init_last x' y' y -> init_last (x :: x') (x :: y') y.

Lemma init_last_comp {t : Type} :
  forall x : t, forall x' l : list t, init_last l x' x <-> x' ++ [x] = l.
Proof.
  intros x x' l.
  split.
  - intros il.
    induction il as [| x y x' y'].
    + simpl. reflexivity.
    + simpl. rewrite IHil. reflexivity.
  - intros eq.
    induction eq.
    induction x' as [| a x'].
    + simpl. apply il_last.
    + simpl. apply il_cons. exact IHx'.
Qed.

Inductive reversed {t : Type} : list t -> list t -> Prop :=
| r_nil : reversed [] []
| r_cons : forall x y x' y', init_last y y' x /\ reversed x' y' -> reversed (x :: x') y.

(* b = ε a *)
Definition reverseR {t u : Type} { _ : Iterable t u }
  (a b : sigma t u) : Prop :=
  forall x : t, forall n : nat,
    reversed (runN x n a) (runN x n a).

(* b = Ø a *)
Definition failR {t u v : Type} { _ : Iterable t u } { _ : Iterable t v }
  (s : sigma t u) (s' : sigma t v) : Prop :=
  forall x : t, s' x = empty _ _.

(* y = π z k a *)
Inductive foldR {t u v : Type} { H : Iterable t u } :
  v -> (v -> u -> v) -> sigma t u -> t -> v -> Prop :=
| fd_empty : forall z k s x, s x = empty _ _ -> foldR z k s x z
| fd_last : forall z k s x a, s x = last _ _ a -> foldR z k s x (k z a)
| fd_next : forall z k s x x' a e, s x = next _ _ a x'
                                   /\ foldR (k z a) k s x' e
                                   -> foldR z k s x e.
