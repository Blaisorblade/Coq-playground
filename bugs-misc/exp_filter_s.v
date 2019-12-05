

Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.

Section str_def.

Variable A : Set.

CoInductive str (A: Set) : Set :=
  SCons: A -> str A ->  str A.

Definition hd (s : str A) : A :=
   match s with SCons _ x s' => x end.

Definition tl (s : str A) : str A :=
   match s with SCons _ x s' => s' end.

Definition str_decompose (s : str A) : str A:=
   match s with SCons _ x s' => SCons A x s' end.

Theorem st_dec_eq: forall (s : str A),  s = str_decompose s.
intros s; case s; auto.
Qed.


Ltac str_unfold term :=
apply trans_equal with (1 := st_dec_eq term).

Fixpoint str_decomp_n (n: nat) (s: str A){struct n}: str A :=
match n, s with
O, s' => s'|
S n', SCons _ x s' => SCons A x (str_decomp_n n' s')
end.

Print str_decomp_n.


Theorem str_decompose_n_lemma :
forall (n:nat)(s: str A), s = str_decomp_n n s.
induction n; intros.
simpl; trivial.
case s.
simpl; trivial.
intros.
rewrite <- IHn.
trivial.
Qed.

Section def_filter.
Variables (P : A ->  Prop) (P_dec : forall x,  ({ P x }) + ({ ~ P x })).

Inductive eventually_s : str A ->  Prop :=
  ev_b: forall x s, P x ->  eventually_s (SCons A x s)
 | ev_r: forall x s, ~ P x -> eventually_s s ->  eventually_s (SCons A x s) .


Definition eventually_s_inv:
 forall (s : str A),
 eventually_s s -> forall x s', s = SCons A x s' -> ~ P x ->  eventually_s s'.
intros s h. case h.
intros x s0 H x0 s' H0 H1. elim H1. injection H0. intros; subst x0; auto.
intros x s0 H3 H x0 s' H0 H1; injection H0; intros; subst s'; assumption.
Defined.



(*the following is slightly changed comapring with Bert05:*)

Fixpoint pre_filter_s (s : str A) (h : eventually_s s) {struct h} : A * str A
 :=
 match s as b return s = b ->  A*str A with
    SCons _ x s' =>
      fun heq =>
         match P_dec x with
           left _ => (x, s')
          | right hn => pre_filter_s s' (eventually_s_inv s h x s' heq hn)
         end
 end (refl_equal s).

Check pre_filter_s.

(*the following is generalised:*)

CoInductive infinite_s : str A ->  Prop :=
  al_cons:
    forall (s: str A) (h: eventually_s s),
     infinite_s (snd(pre_filter_s s h)) ->  infinite_s s.

(*the following is new:*)


Lemma infinite_eventually_s : forall s, infinite_s s -> eventually_s s.
intros s H; case H; auto.
Qed.


Scheme eventually_s_ind2 := Induction for eventually_s Sort Prop.

Lemma pre_filter_s_prf_irrelevant :
  forall s (h h':eventually_s s), pre_filter_s s h = pre_filter_s s h'.
induction h using eventually_s_ind2.
intros h0.
apply (eventually_s_ind2 (fun s' t =>
    match s' with SCons _ a b => b end = s ->
    match s' with SCons _ a b => a end = x ->
    pre_filter_s (SCons A x s) (ev_b x s p) = pre_filter_s s' t)); auto.
intros x0 s0 p0 Hs0 Hx0; subst s0 x0; simpl.
case (P_dec x); auto.
intros; contradiction.
intros; subst x0; contradiction.
intros h0.
apply (eventually_s_ind2 (fun s' t =>
    match s' with SCons _ a b => b end = s ->
    match s' with SCons _ a b => a end = x ->
    pre_filter_s (SCons A x s) (ev_r x s n h) = pre_filter_s s' t)); auto.
intros; subst x; contradiction.
intros x0 s0 Hn He Hr Hs0 Hx0; subst s0 x0; simpl.
case (P_dec x); auto.
Qed.

Lemma F_inf_reverse:
forall (s: str A)(h:eventually_s s),
infinite_s s -> infinite_s (snd (pre_filter_s s h)).
intros s h H'; inversion H'.
rewrite (pre_filter_s_prf_irrelevant s h h0); auto.

Qed.


Theorem infinite_always_s:
forall (s:str A) (h:infinite_s s), infinite_s (snd (pre_filter_s s (infinite_eventually_s s h))).
intros s h; case h.
intros s0 h0; case h0.
intros.
rewrite (pre_filter_s_prf_irrelevant (SCons A x s1) (infinite_eventually_s (SCons A x s1)
              (al_cons (SCons A x s1) (ev_b x s1 p) i)) (ev_b x s1 p)); auto.
intros.
rewrite (pre_filter_s_prf_irrelevant (SCons A x s1)(infinite_eventually_s (SCons A x s1)
              (al_cons (SCons A x s1) (ev_r x s1 n e) i))(ev_r x s1 n e)); auto.
Qed.

CoFixpoint filter (s : str A) : forall (h: infinite_s s), str A :=
  match s return infinite_s s -> str A with
  | SCons _ x s' =>
      fun h' : infinite_s (SCons A x s') =>
      SCons A
        (fst (pre_filter_s (SCons A x s')
              (infinite_eventually_s (SCons A x s') h')))
        (filter
           (snd (pre_filter_s (SCons A x s')
                 (infinite_eventually_s (SCons A x s') h')))
           (infinite_always_s (SCons A x s') h'))
  end.

(*CoFixpoint filter (s : str A): forall (h:infinite_s s), str A :=
  match s return infinite_s s -> str A with
  | SCons A x s' => fun h' : infinite_s (SCons A x s') =>
        SCons A (fst (pre_filter_s (SCons A x s') (infinite_eventually_s  (SCons A x s')  h'))) (filter (SCons A x s') (infinite_always_s (SCons A x s') h'))
   end.
*)

Lemma s_step1 : forall s x, infinite_s (SCons A x s) -> infinite_s s.
intros s x hf; inversion hf.
generalize H; clear H; dependent inversion h.
simpl.
case P_dec.
intros; auto.
intros; elim n; auto.
simpl.
case P_dec.
intros; auto.
intros; auto.
apply al_cons with e; assumption.
Qed.



CoInductive bisimilar:  str A -> str A -> Prop :=
|bisim: forall (a : A) (s s' : str A), bisimilar s s' -> bisimilar (SCons A a s)(SCons A a s').

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Operators_Properties.

Theorem Bisim_refl: forall (s : str A), bisimilar s s.
cofix H.
intros.
case s.
intros.
apply bisim.
apply H.
Qed.

Theorem Bisim_trans: forall (l u v: str A),
 bisimilar  l u -> bisimilar u v -> bisimilar l v.
cofix H.
intros l u v.
case l; case u; case v.
intros.
assert (a1 = a0).
inversion H0; auto.
assert (a = a0).
inversion H1; auto.
assert (a1 = a).
apply trans_equal with a0; auto.
rewrite H4.
apply bisim.
apply H with s0.
Guarded.
inversion H0; assumption.
inversion H1; assumption.
Qed.




Lemma misc3: forall (x: A) (s: str A) (H: eventually_s (SCons A x s)),   P x -> (x, s) = (pre_filter_s (SCons A x s) H).
intros x s h h0.
dependent inversion h.
apply trans_equal with (pre_filter_s (SCons A x s) h).
apply sym_equal.
unfold pre_filter_s.
dependent inversion h; case P_dec; auto;
intro; contradiction.
rewrite (pre_filter_s_prf_irrelevant (SCons A x s) (h)(ev_b x s p)); auto.
contradiction.
Qed.

Lemma misc3': forall (x:A) (s: str A) (H: eventually_s (SCons A x s)),  P x -> x = fst (pre_filter_s (SCons A x s) H).
intros.
assert ((x,s) = pre_filter_s (SCons A x s) H).
apply misc3; assumption.
rewrite <- H1; auto.
Qed.

Lemma misc3'': forall (x: A) (s: str A) (H: eventually_s (SCons A x s)),   P x ->  snd (pre_filter_s (SCons A x s) H) = s.
intros x s h h0.
assert ((x,s) = pre_filter_s (SCons A x s) h).
apply misc3; assumption.
rewrite <- H; auto.
Qed.
(*Lemma F_inf_step1_always: forall (x: A) (s: str A)(h: infinite_s (SCons A x s)), P x ->
 infinite_always_s h = s_step1 h.
*)


Lemma filter_prf_irrelevant :
  forall s s' (h : infinite_s s) (h':infinite_s s'), s = s' -> bisimilar (filter s h) (filter s' h').
cofix H.
intros [a s][a' s'] h h' Hss'; injection Hss'; clear Hss'; intros Hss' Haa'.
rewrite (st_dec_eq (filter (SCons A a s) h)); simpl.
rewrite (st_dec_eq (filter (SCons A a' s') h')); simpl.
assert (pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) h) = pre_filter_s (SCons A a' s') (infinite_eventually_s (SCons A a' s') h')).
generalize h'; clear h'; rewrite <- Haa'; rewrite <- Hss'; intros h'.
rewrite (pre_filter_s_prf_irrelevant (SCons A a s) (infinite_eventually_s (SCons A a s) h)
              (infinite_eventually_s (SCons A a s) h')); auto.
pattern (pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) h)) at 1; rewrite H0.
apply bisim.
apply H.
rewrite H0; auto.
Qed.

Lemma pre_filter_prf_irrelevant_neg: forall x s (h: eventually_s (SCons A x s)) (h': eventually_s s), ~ P x ->
pre_filter_s (SCons A x s)  h = pre_filter_s s h'.
intros x [a s] h h' n.
generalize (refl_equal (SCons A a s)).
intro q.
dependent inversion h.
contradiction.
simpl.
case P_dec.
intro; contradiction.
intro; apply pre_filter_s_prf_irrelevant.
Qed.



Lemma filter_prf_irrelevant_neg :
  forall (x:A) (s: str A) (h : infinite_s (SCons A x s)),  ~ P x ->
bisimilar (filter (SCons A x s) h) (filter s (s_step1 s x h)).
intros x [a s] h n.
rewrite (st_dec_eq (filter (SCons A x (SCons A a s)) h)); simpl str_decompose.
rewrite (st_dec_eq (filter (SCons A a s) (s_step1 (SCons A a s) x h))); simpl str_decompose.
assert (infinite_s (SCons A a s)).
apply s_step1 with x; assumption.
assert (eventually_s (SCons A a s)).
apply infinite_eventually_s; assumption.
assert (eventually_s (SCons A x (SCons A a s))).
apply infinite_eventually_s; assumption.
pattern (pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) (s_step1 (SCons A a s) x h))) at 1.
rewrite (pre_filter_s_prf_irrelevant (SCons A a s) (infinite_eventually_s (SCons A a s) (s_step1 (SCons A a s) x h)) H0).
assert (pre_filter_s (SCons A x (SCons A a s)) H1 = pre_filter_s (SCons A a s) H0).
apply pre_filter_prf_irrelevant_neg; assumption.
rewrite <- H2.
assert (pre_filter_s (SCons A x (SCons A a s)) (infinite_eventually_s (SCons A x (SCons A a s)) h) = pre_filter_s (SCons A x (SCons A a s)) H1).
apply pre_filter_s_prf_irrelevant.
rewrite <- H3.
apply bisim.
apply Bisim_trans with (filter
        (snd(pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) H)))
        (infinite_always_s (SCons A a s) H)).
apply filter_prf_irrelevant.
assert ((pre_filter_s (SCons A x (SCons A a s))
        (infinite_eventually_s (SCons A x (SCons A a s)) h)) =
     (pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) H))).
apply pre_filter_prf_irrelevant_neg; assumption.
rewrite H4; auto.
apply filter_prf_irrelevant.
assert ((pre_filter_s (SCons A a s) (infinite_eventually_s (SCons A a s) H))
     = (pre_filter_s (SCons A a s)
        (infinite_eventually_s (SCons A a s) (s_step1 (SCons A a s) x h)))).
apply pre_filter_s_prf_irrelevant.
rewrite H4; auto.
Qed.

Theorem filter_equation:
   forall (s : str A) (h : infinite_s s),
   bisimilar (filter s h)
     (match s return (infinite_s s -> str A) with
      | SCons _ x s' =>
          fun h0 : infinite_s (SCons A x s') =>
          match P_dec x return str A with
          | left _ => SCons A x (filter s' (s_step1 s' x h0))
          | right _ => filter s' (s_step1 s' x h0)
          end
      end h).
intros s h.
case h; intros.
induction h0 using eventually_s_ind2; case P_dec.
intro.
rewrite (st_dec_eq (filter (SCons A x s0) (al_cons (SCons A x s0) (ev_b x s0 p) i))); simpl.
assert ( x =
     (fst (pre_filter_s (SCons A x s0)
           (infinite_eventually_s (SCons A x s0)
              (al_cons (SCons A x s0) (ev_b x s0 p) i))))).
assert (eventually_s (SCons A x s0)).
apply ev_b; assumption.
assert (infinite_s (SCons A x s0)).
apply al_cons with H.
assert (pre_filter_s (SCons A x s0) H = pre_filter_s (SCons A x s0) (ev_b x s0 p)).
rewrite (pre_filter_s_prf_irrelevant (SCons A x s0)(H)
              (ev_b x s0 p)); auto.
rewrite H0; assumption.
apply trans_equal with (fst (pre_filter_s (SCons A x s0) H)).
generalize p0.
apply misc3'; auto.
rewrite (pre_filter_s_prf_irrelevant (SCons A x s0) (H)
              (infinite_eventually_s (SCons A x s0) (al_cons (SCons A x s0) (ev_b x s0 p) i))); auto.
rewrite <- H.
apply bisim.
apply filter_prf_irrelevant.
inversion i.
assert (eventually_s (SCons A x s0)).
apply ev_b; assumption.
apply trans_equal with (snd (pre_filter_s (SCons A x s0) H2)).
rewrite (pre_filter_s_prf_irrelevant (SCons A x s0) (infinite_eventually_s (SCons A x s0) (al_cons (SCons A x s0) (ev_b x s0 p) i)) (H2)); auto.
apply misc3''; auto.
intro; contradiction.
intro; contradiction.
intro.
apply filter_prf_irrelevant_neg; auto.
Qed.





End def_filter.

End str_def.


