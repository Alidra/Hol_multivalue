Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LE_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import SUM_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7210210 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7210211 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7210212 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7210211 m) (@lem7210210 m)). Qed.
Lemma lem7210213 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7210212 m n). Qed.
Lemma lem7210214 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7210215 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7210214 m n) (@lem7210213 m n)). Qed.
Lemma lem7210216 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7210215 m n p). Qed.
Lemma lem7210217 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7210219 (m : nat) : term7 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7210220 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem7210221 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem7210220 m) (@lem7210219 m)). Qed.
Lemma lem7210222 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem7210221 m n). Qed.
Lemma lem7210223 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem7210224 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem7210223 m n) (@lem7210222 m n)). Qed.
Lemma lem7210225 (m : nat) (n : nat) : (term10 m n) = ((term10 m n) = True).
Proof. exact (@lem7 (term10 m n)). Qed.
Lemma lem7210227 {_132081 : Type'} (f : _132081 -> real) : term11 _132081 f.
Proof. exact (@lem7071845 _132081 f). Qed.
Lemma lem7210228 {_132081 : Type'} (f : _132081 -> real) : (term11 _132081 f) = (term12 _132081 f).
Proof. exact (eq_refl (term11 _132081 f)). Qed.
Lemma lem7210229 {_132081 : Type'} (f : _132081 -> real) : term12 _132081 f.
Proof. exact (EQ_MP (@lem7210228 _132081 f) (@lem7210227 _132081 f)). Qed.
Lemma lem7210230 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term13 _132081 f g.
Proof. exact (@lem7210229 _132081 f g). Qed.
Lemma lem7210231 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term13 _132081 f g) = (term14 _132081 f g).
Proof. exact (eq_refl (term13 _132081 f g)). Qed.
Lemma lem7210232 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term14 _132081 f g.
Proof. exact (EQ_MP (@lem7210231 _132081 f g) (@lem7210230 _132081 f g)). Qed.
Lemma lem7210233 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) : term15 _132081 f g s.
Proof. exact (@lem7210232 _132081 f g s). Qed.
Lemma lem7210234 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term15 _132081 f g s) = (term16 _132081 f s g).
Proof. exact (eq_refl (term15 _132081 f g s)). Qed.
Lemma lem7210235 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term16 _132081 f s g.
Proof. exact (EQ_MP (@lem7210234 _132081 f s g) (@lem7210233 _132081 f g s)). Qed.
Lemma lem7210236 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term17 _132081 s f g) : term17 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7210237 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term17 _132081 s f g) : term18 _132081 f s g.
Proof. exact (@lem7210235 _132081 f s g (@lem7210236 _132081 s f g h1)). Qed.
Lemma lem7210238 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term18 _132081 f s g) = ((term18 _132081 f s g) = True).
Proof. exact (@lem7 (term18 _132081 f s g)). Qed.
Lemma lem7210239 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term17 _132081 s f g) : (term18 _132081 f s g) = True.
Proof. exact (EQ_MP (@lem7210238 _132081 f s g) (@lem7210237 _132081 s f g h1)). Qed.
Lemma lem7210264 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7210265 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem7210264 p q p' q'). Qed.
Lemma lem7210266 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem7210265 p q p'). Qed.
Lemma lem7210267 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term22 f m n g.
Proof. exact (@lem7210266 (term23 m n f g) (term24 f m n g)). Qed.
Lemma lem7210268 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) : term25 f m n g p'.
Proof. exact (@lem7210267 f m n g p'). Qed.
Lemma lem7210269 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) : (term25 f m n g p') = (term26 f m n g p').
Proof. exact (eq_refl (term25 f m n g p')). Qed.
Lemma lem7210270 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) : term26 f m n g p'.
Proof. exact (EQ_MP (@lem7210269 f m n g p') (@lem7210268 f m n g p')). Qed.
Lemma lem7210271 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) (q' : Prop) : term27 f m n g p' q'.
Proof. exact (@lem7210270 f m n g p' q'). Qed.
Lemma lem7210272 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) (q' : Prop) : (term27 f m n g p' q') = (term28 f m n g p' q').
Proof. exact (eq_refl (term27 f m n g p' q')). Qed.
Lemma lem7210273 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (p' : Prop) (q' : Prop) : term28 f m n g p' q'.
Proof. exact (EQ_MP (@lem7210272 f m n g p' q') (@lem7210271 f m n g p' q')). Qed.
Lemma lem7210309 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term23 m n f g) = (term23 m n f g).
Proof. exact (eq_refl (term23 m n f g)). Qed.
Lemma lem7210310 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (q' : Prop) : term29 m n f g q'.
Proof. exact (@lem7210273 f m n g (term23 m n f g) q'). Qed.
Lemma lem7210311 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (q' : Prop) : term30 m n f g q'.
Proof. exact (@lem7210310 m n f g q' (@lem7210309 m n f g)). Qed.
Lemma lem7210312 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term23 m n f g.
Proof. exact (h1). Qed.
Lemma lem7210313 (i : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term31 m n f g i.
Proof. exact (@lem7210312 m n f g h1 i). Qed.
Lemma lem7210314 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (i : nat) : (term31 m n f g i) = (term32 m n f g i).
Proof. exact (eq_refl (term31 m n f g i)). Qed.
Lemma lem7210315 (i : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term32 m n f g i.
Proof. exact (EQ_MP (@lem7210314 m n f g i) (@lem7210313 i m n f g h1)). Qed.
Lemma lem7210316 (m : nat) (i : nat) (n : nat) (h1 : term6 m i n) : term6 m i n.
Proof. exact (h1). Qed.
Lemma lem7210317 (f : nat -> real) (g : nat -> real) (m : nat) (i : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m i n) : term33 f g i.
Proof. exact (@lem7210315 i m n f g h1 (@lem7210316 m i n h2)). Qed.
Lemma lem7210318 (f : nat -> real) (g : nat -> real) (i : nat) : (term33 f g i) = ((term33 f g i) = True).
Proof. exact (@lem7 (term33 f g i)). Qed.
Lemma lem7210319 (f : nat -> real) (g : nat -> real) (m : nat) (i : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m i n) : (term33 f g i) = True.
Proof. exact (EQ_MP (@lem7210318 f g i) (@lem7210317 f g m i n h1 h2)). Qed.
Lemma lem7210326 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term34 _132081 f s g.
Proof. exact (fun h0 : term17 _132081 s f g => @lem7210239 _132081 s f g h0). Qed.
Lemma lem7210327 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : term35 f s g.
Proof. exact (@lem7210326 nat f s g). Qed.
Lemma lem7210328 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term36 f m n g.
Proof. exact (@lem7210327 f (dotdot m n) g). Qed.
Lemma lem7210332 (m : nat) (n : nat) : (term10 m n) = True.
Proof. exact (EQ_MP (@lem7210225 m n) (@lem7210224 m n)). Qed.
Lemma lem7210333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7210334 (m : nat) (n : nat) : (term37 m n) = (and True).
Proof. exact (MK_COMB (@lem7210333) (@lem7210332 m n)). Qed.
Lemma lem7210342 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7210343 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem7210342 p q p' q'). Qed.
Lemma lem7210344 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem7210343 p q p'). Qed.
Lemma lem7210345 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) : term38 m n f g x.
Proof. exact (@lem7210344 (term5 x m n) (term33 f g x)). Qed.
Lemma lem7210346 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : term39 m n f g x p'.
Proof. exact (@lem7210345 m n f g x p'). Qed.
Lemma lem7210347 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : (term39 m n f g x p') = (term40 m n f g x p').
Proof. exact (eq_refl (term39 m n f g x p')). Qed.
Lemma lem7210348 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) : term40 m n f g x p'.
Proof. exact (EQ_MP (@lem7210347 m n f g x p') (@lem7210346 m n f g x p')). Qed.
Lemma lem7210349 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term41 m n f g x p' q'.
Proof. exact (@lem7210348 m n f g x p' q'). Qed.
Lemma lem7210350 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : (term41 m n f g x p' q') = (term42 m n f g x p' q').
Proof. exact (eq_refl (term41 m n f g x p' q')). Qed.
Lemma lem7210351 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term42 m n f g x p' q'.
Proof. exact (EQ_MP (@lem7210350 m n f g x p' q') (@lem7210349 m n f g x p' q')). Qed.
Lemma lem7210353 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7210217 m p n) (@lem7210216 m n p)). Qed.
Lemma lem7210354 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7210353 m x n). Qed.
Lemma lem7210357 (f : nat -> real) (g : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term43 f g m x n q'.
Proof. exact (@lem7210351 m n f g x (term6 m x n) q'). Qed.
Lemma lem7210358 (f : nat -> real) (g : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term44 f g m x n q'.
Proof. exact (@lem7210357 f g m x n q' (@lem7210354 m x n)). Qed.
Lemma lem7210359 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (h1). Qed.
Lemma lem7210360 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem7210359 m x n h1)). Qed.
Lemma lem7210361 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem7210363 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le m x.
Proof. exact (proj1 (@lem7210359 m x n h1)). Qed.
Lemma lem7210364 (m : nat) (x : nat) : (Peano.le m x) = ((Peano.le m x) = True).
Proof. exact (@lem7 (Peano.le m x)). Qed.
Lemma lem7210367 (i : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term45 m n f g i.
Proof. exact (fun h0 : term6 m i n => @lem7210319 f g m i n h1 h0). Qed.
Lemma lem7210368 (x : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term45 m n f g x.
Proof. exact (@lem7210367 x m n f g h1). Qed.
Lemma lem7210372 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le m x) = True.
Proof. exact (EQ_MP (@lem7210364 m x) (@lem7210363 m x n h1)). Qed.
Lemma lem7210373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7210374 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term46 m x) = (and True).
Proof. exact (MK_COMB (@lem7210373) (@lem7210372 m x n h1)). Qed.
Lemma lem7210376 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem7210361 x n) (@lem7210360 m x n h1)). Qed.
Lemma lem7210377 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = (True /\ True).
Proof. exact (MK_COMB (@lem7210374 m x n h1) (@lem7210376 m x n h1)). Qed.
Lemma lem7210379 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7210380 : (True /\ True) = True.
Proof. exact (@lem7210379 True). Qed.
Lemma lem7210381 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = True.
Proof. exact (TRANS (@lem7210377 m x n h1) (@lem7210380)). Qed.
Lemma lem7210382 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : True = (term6 m x n).
Proof. exact (SYM (@lem7210381 m x n h1)). Qed.
Lemma lem7210383 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (EQ_MP (@lem7210382 m x n h1) (@lem0)). Qed.
Lemma lem7210384 (f : nat -> real) (g : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term23 m n f g) (h2 : term6 m x n) : (term33 f g x) = True.
Proof. exact (@lem7210368 x m n f g h1 (@lem7210383 m x n h2)). Qed.
Lemma lem7210385 (x : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term45 m n f g x.
Proof. exact (fun h0 : term6 m x n => @lem7210384 f g m x n h1 h0). Qed.
Lemma lem7210386 (f : nat -> real) (g : nat -> real) (m : nat) (x : nat) (n : nat) : term47 f g m x n.
Proof. exact (@lem7210358 f g m x n True). Qed.
Lemma lem7210387 (x : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term48 m n f g x) = (term49 m x n).
Proof. exact (@lem7210386 f g m x n (@lem7210385 x m n f g h1)). Qed.
Lemma lem7210389 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7210390 (m : nat) (x : nat) (n : nat) : (term49 m x n) = True.
Proof. exact (@lem7210389 (term6 m x n)). Qed.
Lemma lem7210391 (x : nat) (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term48 m n f g x) = True.
Proof. exact (TRANS (@lem7210387 x m n f g h1) (@lem7210390 m x n)). Qed.
Lemma lem7210392 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term50 m n f g) = term51.
Proof. exact (fun_ext (fun x : nat => @lem7210391 x m n f g h1)). Qed.
Lemma lem7210393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210394 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term52 m n f g) = term53.
Proof. exact (MK_COMB (@lem7210393) (@lem7210392 m n f g h1)). Qed.
Lemma lem7210396 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210397 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7210396 nat t). Qed.
Lemma lem7210398 : term53 = True.
Proof. exact (@lem7210397 True). Qed.
Lemma lem7210399 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term52 m n f g) = True.
Proof. exact (TRANS (@lem7210394 m n f g h1) (@lem7210398)). Qed.
Lemma lem7210400 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term56 m n f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7210334 m n) (@lem7210399 m n f g h1)). Qed.
Lemma lem7210402 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7210403 : (True /\ True) = True.
Proof. exact (@lem7210402 True). Qed.
Lemma lem7210404 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term56 m n f g) = True.
Proof. exact (TRANS (@lem7210400 m n f g h1) (@lem7210403)). Qed.
Lemma lem7210405 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : True = (term56 m n f g).
Proof. exact (SYM (@lem7210404 m n f g h1)). Qed.
Lemma lem7210406 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : term56 m n f g.
Proof. exact (EQ_MP (@lem7210405 m n f g h1) (@lem0)). Qed.
Lemma lem7210407 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term23 m n f g) : (term24 f m n g) = True.
Proof. exact (@lem7210328 f m n g (@lem7210406 m n f g h1)). Qed.
Lemma lem7210408 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term57 f m n g.
Proof. exact (fun h0 : term23 m n f g => @lem7210407 m n f g h0). Qed.
Lemma lem7210409 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : term58 m n f g.
Proof. exact (@lem7210311 m n f g True). Qed.
Lemma lem7210410 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term59 f m n g) = (term60 m n f g).
Proof. exact (@lem7210409 m n f g (@lem7210408 f m n g)). Qed.
Lemma lem7210412 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7210413 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term60 m n f g) = True.
Proof. exact (@lem7210412 (term23 m n f g)). Qed.
Lemma lem7210414 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term59 f m n g) = True.
Proof. exact (TRANS (@lem7210410 m n f g) (@lem7210413 m n f g)). Qed.
Lemma lem7210415 (f : nat -> real) (m : nat) (g : nat -> real) : (term61 f m g) = term51.
Proof. exact (fun_ext (fun n : nat => @lem7210414 f m n g)). Qed.
Lemma lem7210416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210417 (f : nat -> real) (m : nat) (g : nat -> real) : (term62 f m g) = term53.
Proof. exact (MK_COMB (@lem7210416) (@lem7210415 f m g)). Qed.
Lemma lem7210419 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210420 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7210419 nat t). Qed.
Lemma lem7210421 : term53 = True.
Proof. exact (@lem7210420 True). Qed.
Lemma lem7210422 (f : nat -> real) (m : nat) (g : nat -> real) : (term62 f m g) = True.
Proof. exact (TRANS (@lem7210417 f m g) (@lem7210421)). Qed.
Lemma lem7210423 (f : nat -> real) (g : nat -> real) : (term63 f g) = term51.
Proof. exact (fun_ext (fun m : nat => @lem7210422 f m g)). Qed.
Lemma lem7210424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210425 (f : nat -> real) (g : nat -> real) : (term64 f g) = term53.
Proof. exact (MK_COMB (@lem7210424) (@lem7210423 f g)). Qed.
Lemma lem7210427 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210428 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7210427 nat t). Qed.
Lemma lem7210429 : term53 = True.
Proof. exact (@lem7210428 True). Qed.
Lemma lem7210430 (f : nat -> real) (g : nat -> real) : (term64 f g) = True.
Proof. exact (TRANS (@lem7210425 f g) (@lem7210429)). Qed.
Lemma lem7210431 (f : nat -> real) : (term65 f) = term66.
Proof. exact (fun_ext (fun g : nat -> real => @lem7210430 f g)). Qed.
Lemma lem7210432 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210433 (f : nat -> real) : (term67 f) = term68.
Proof. exact (MK_COMB (@lem7210432) (@lem7210431 f)). Qed.
Lemma lem7210435 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210436 (t : Prop) : (term69 t) = t.
Proof. exact (@lem7210435 (nat -> real) t). Qed.
Lemma lem7210437 : term68 = True.
Proof. exact (@lem7210436 True). Qed.
Lemma lem7210438 (f : nat -> real) : (term67 f) = True.
Proof. exact (TRANS (@lem7210433 f) (@lem7210437)). Qed.
Lemma lem7210439 : term70 = term66.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210438 f)). Qed.
Lemma lem7210440 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210441 : term71 = term68.
Proof. exact (MK_COMB (@lem7210440) (@lem7210439)). Qed.
Lemma lem7210443 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210444 (t : Prop) : (term69 t) = t.
Proof. exact (@lem7210443 (nat -> real) t). Qed.
Lemma lem7210445 : term68 = True.
Proof. exact (@lem7210444 True). Qed.
Lemma lem7210446 : term71 = True.
Proof. exact (TRANS (@lem7210441) (@lem7210445)). Qed.
Lemma lem7210447 : True = term71.
Proof. exact (SYM (@lem7210446)). Qed.
Lemma lem7210448 : term71.
Proof. exact (EQ_MP (@lem7210447) (@lem0)). Qed.
