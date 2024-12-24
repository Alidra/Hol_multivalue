Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_LE_NUMSEG_term_abbrevs.
Require Import IN_NUMSEG_spec.
Require Import SUM_POS_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7216203 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7216204 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7216205 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7216204 m) (@lem7216203 m)). Qed.
Lemma lem7216206 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7216205 m n). Qed.
Lemma lem7216207 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7216208 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7216207 m n) (@lem7216206 m n)). Qed.
Lemma lem7216209 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7216208 m n p). Qed.
Lemma lem7216210 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7216220 {A : Type'} (f : A -> real) (s : A -> Prop) : term7 A f s.
Proof. exact (@lem7085797 A f s). Qed.
Lemma lem7216221 {A : Type'} (s : A -> Prop) (f : A -> real) : (term7 A f s) = (term8 A s f).
Proof. exact (eq_refl (term7 A f s)). Qed.
Lemma lem7216222 {A : Type'} (s : A -> Prop) (f : A -> real) : term8 A s f.
Proof. exact (EQ_MP (@lem7216221 A s f) (@lem7216220 A f s)). Qed.
Lemma lem7216223 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term9 A s f) : term9 A s f.
Proof. exact (h1). Qed.
Lemma lem7216224 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term9 A s f) : term10 A s f.
Proof. exact (@lem7216222 A s f (@lem7216223 A s f h1)). Qed.
Lemma lem7216225 {A : Type'} (s : A -> Prop) (f : A -> real) : (term10 A s f) = ((term10 A s f) = True).
Proof. exact (@lem7 (term10 A s f)). Qed.
Lemma lem7216226 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term9 A s f) : (term10 A s f) = True.
Proof. exact (EQ_MP (@lem7216225 A s f) (@lem7216224 A s f h1)). Qed.
Lemma lem7216247 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7216248 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem7216247 p q p' q'). Qed.
Lemma lem7216249 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem7216248 p q p'). Qed.
Lemma lem7216250 (m : nat) (n : nat) (f : nat -> real) : term14 m n f.
Proof. exact (@lem7216249 (term15 m n f) (term16 m n f)). Qed.
Lemma lem7216251 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term17 m n f p'.
Proof. exact (@lem7216250 m n f p'). Qed.
Lemma lem7216252 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : (term17 m n f p') = (term18 m n f p').
Proof. exact (eq_refl (term17 m n f p')). Qed.
Lemma lem7216253 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term18 m n f p'.
Proof. exact (EQ_MP (@lem7216252 m n f p') (@lem7216251 m n f p')). Qed.
Lemma lem7216254 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term19 m n f p' q'.
Proof. exact (@lem7216253 m n f p' q'). Qed.
Lemma lem7216255 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : (term19 m n f p' q') = (term20 m n f p' q').
Proof. exact (eq_refl (term19 m n f p' q')). Qed.
Lemma lem7216256 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term20 m n f p' q'.
Proof. exact (EQ_MP (@lem7216255 m n f p' q') (@lem7216254 m n f p' q')). Qed.
Lemma lem7216292 (m : nat) (n : nat) (f : nat -> real) : (term15 m n f) = (term15 m n f).
Proof. exact (eq_refl (term15 m n f)). Qed.
Lemma lem7216293 (m : nat) (n : nat) (f : nat -> real) (q' : Prop) : term21 m n f q'.
Proof. exact (@lem7216256 m n f (term15 m n f) q'). Qed.
Lemma lem7216294 (m : nat) (n : nat) (f : nat -> real) (q' : Prop) : term22 m n f q'.
Proof. exact (@lem7216293 m n f q' (@lem7216292 m n f)). Qed.
Lemma lem7216295 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term15 m n f.
Proof. exact (h1). Qed.
Lemma lem7216296 (p : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term23 m n f p.
Proof. exact (@lem7216295 m n f h1 p). Qed.
Lemma lem7216297 (m : nat) (n : nat) (f : nat -> real) (p : nat) : (term23 m n f p) = (term24 m n f p).
Proof. exact (eq_refl (term23 m n f p)). Qed.
Lemma lem7216298 (p : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term24 m n f p.
Proof. exact (EQ_MP (@lem7216297 m n f p) (@lem7216296 p m n f h1)). Qed.
Lemma lem7216299 (m : nat) (p : nat) (n : nat) (h1 : term6 m p n) : term6 m p n.
Proof. exact (h1). Qed.
Lemma lem7216300 (f : nat -> real) (m : nat) (p : nat) (n : nat) (h1 : term15 m n f) (h2 : term6 m p n) : term25 f p.
Proof. exact (@lem7216298 p m n f h1 (@lem7216299 m p n h2)). Qed.
Lemma lem7216301 (f : nat -> real) (p : nat) : (term25 f p) = ((term25 f p) = True).
Proof. exact (@lem7 (term25 f p)). Qed.
Lemma lem7216302 (f : nat -> real) (m : nat) (p : nat) (n : nat) (h1 : term15 m n f) (h2 : term6 m p n) : (term25 f p) = True.
Proof. exact (EQ_MP (@lem7216301 f p) (@lem7216300 f m p n h1 h2)). Qed.
Lemma lem7216309 {A : Type'} (s : A -> Prop) (f : A -> real) : term26 A s f.
Proof. exact (fun h0 : term9 A s f => @lem7216226 A s f h0). Qed.
Lemma lem7216310 (s : nat -> Prop) (f : nat -> real) : term27 s f.
Proof. exact (@lem7216309 nat s f). Qed.
Lemma lem7216311 (m : nat) (n : nat) (f : nat -> real) : term28 m n f.
Proof. exact (@lem7216310 (dotdot m n) f). Qed.
Lemma lem7216319 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7216320 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem7216319 p q p' q'). Qed.
Lemma lem7216321 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem7216320 p q p'). Qed.
Lemma lem7216322 (m : nat) (n : nat) (f : nat -> real) (x : nat) : term29 m n f x.
Proof. exact (@lem7216321 (term5 x m n) (term25 f x)). Qed.
Lemma lem7216323 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : term30 m n f x p'.
Proof. exact (@lem7216322 m n f x p'). Qed.
Lemma lem7216324 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : (term30 m n f x p') = (term31 m n f x p').
Proof. exact (eq_refl (term30 m n f x p')). Qed.
Lemma lem7216325 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) : term31 m n f x p'.
Proof. exact (EQ_MP (@lem7216324 m n f x p') (@lem7216323 m n f x p')). Qed.
Lemma lem7216326 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term32 m n f x p' q'.
Proof. exact (@lem7216325 m n f x p' q'). Qed.
Lemma lem7216327 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : (term32 m n f x p' q') = (term33 m n f x p' q').
Proof. exact (eq_refl (term32 m n f x p' q')). Qed.
Lemma lem7216328 (m : nat) (n : nat) (f : nat -> real) (x : nat) (p' : Prop) (q' : Prop) : term33 m n f x p' q'.
Proof. exact (EQ_MP (@lem7216327 m n f x p' q') (@lem7216326 m n f x p' q')). Qed.
Lemma lem7216330 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7216210 m p n) (@lem7216209 m n p)). Qed.
Lemma lem7216331 (m : nat) (x : nat) (n : nat) : (term5 x m n) = (term6 m x n).
Proof. exact (@lem7216330 m x n). Qed.
Lemma lem7216334 (f : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term34 f m x n q'.
Proof. exact (@lem7216328 m n f x (term6 m x n) q'). Qed.
Lemma lem7216335 (f : nat -> real) (m : nat) (x : nat) (n : nat) (q' : Prop) : term35 f m x n q'.
Proof. exact (@lem7216334 f m x n q' (@lem7216331 m x n)). Qed.
Lemma lem7216336 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (h1). Qed.
Lemma lem7216337 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem7216336 m x n h1)). Qed.
Lemma lem7216338 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem7216340 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : Peano.le m x.
Proof. exact (proj1 (@lem7216336 m x n h1)). Qed.
Lemma lem7216341 (m : nat) (x : nat) : (Peano.le m x) = ((Peano.le m x) = True).
Proof. exact (@lem7 (Peano.le m x)). Qed.
Lemma lem7216344 (p : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term36 m n f p.
Proof. exact (fun h0 : term6 m p n => @lem7216302 f m p n h1 h0). Qed.
Lemma lem7216345 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term36 m n f x.
Proof. exact (@lem7216344 x m n f h1). Qed.
Lemma lem7216349 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le m x) = True.
Proof. exact (EQ_MP (@lem7216341 m x) (@lem7216340 m x n h1)). Qed.
Lemma lem7216350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216351 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term37 m x) = (and True).
Proof. exact (MK_COMB (@lem7216350) (@lem7216349 m x n h1)). Qed.
Lemma lem7216353 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem7216338 x n) (@lem7216337 m x n h1)). Qed.
Lemma lem7216354 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = (True /\ True).
Proof. exact (MK_COMB (@lem7216351 m x n h1) (@lem7216353 m x n h1)). Qed.
Lemma lem7216356 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7216357 : (True /\ True) = True.
Proof. exact (@lem7216356 True). Qed.
Lemma lem7216358 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : (term6 m x n) = True.
Proof. exact (TRANS (@lem7216354 m x n h1) (@lem7216357)). Qed.
Lemma lem7216359 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : True = (term6 m x n).
Proof. exact (SYM (@lem7216358 m x n h1)). Qed.
Lemma lem7216360 (m : nat) (x : nat) (n : nat) (h1 : term6 m x n) : term6 m x n.
Proof. exact (EQ_MP (@lem7216359 m x n h1) (@lem0)). Qed.
Lemma lem7216361 (f : nat -> real) (m : nat) (x : nat) (n : nat) (h1 : term15 m n f) (h2 : term6 m x n) : (term25 f x) = True.
Proof. exact (@lem7216345 x m n f h1 (@lem7216360 m x n h2)). Qed.
Lemma lem7216362 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term36 m n f x.
Proof. exact (fun h0 : term6 m x n => @lem7216361 f m x n h1 h0). Qed.
Lemma lem7216363 (f : nat -> real) (m : nat) (x : nat) (n : nat) : term38 f m x n.
Proof. exact (@lem7216335 f m x n True). Qed.
Lemma lem7216364 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term39 m n f x) = (term40 m x n).
Proof. exact (@lem7216363 f m x n (@lem7216362 x m n f h1)). Qed.
Lemma lem7216366 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7216367 (m : nat) (x : nat) (n : nat) : (term40 m x n) = True.
Proof. exact (@lem7216366 (term6 m x n)). Qed.
Lemma lem7216368 (x : nat) (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term39 m n f x) = True.
Proof. exact (TRANS (@lem7216364 x m n f h1) (@lem7216367 m x n)). Qed.
Lemma lem7216369 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term41 m n f) = term42.
Proof. exact (fun_ext (fun x : nat => @lem7216368 x m n f h1)). Qed.
Lemma lem7216370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216371 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term43 m n f) = term44.
Proof. exact (MK_COMB (@lem7216370) (@lem7216369 m n f h1)). Qed.
Lemma lem7216373 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7216374 (t : Prop) : (term46 t) = t.
Proof. exact (@lem7216373 nat t). Qed.
Lemma lem7216375 : term44 = True.
Proof. exact (@lem7216374 True). Qed.
Lemma lem7216376 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term43 m n f) = True.
Proof. exact (TRANS (@lem7216371 m n f h1) (@lem7216375)). Qed.
Lemma lem7216377 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : True = (term43 m n f).
Proof. exact (SYM (@lem7216376 m n f h1)). Qed.
Lemma lem7216378 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : term43 m n f.
Proof. exact (EQ_MP (@lem7216377 m n f h1) (@lem0)). Qed.
Lemma lem7216379 (m : nat) (n : nat) (f : nat -> real) (h1 : term15 m n f) : (term16 m n f) = True.
Proof. exact (@lem7216311 m n f (@lem7216378 m n f h1)). Qed.
Lemma lem7216380 (m : nat) (n : nat) (f : nat -> real) : term47 m n f.
Proof. exact (fun h0 : term15 m n f => @lem7216379 m n f h0). Qed.
Lemma lem7216381 (m : nat) (n : nat) (f : nat -> real) : term48 m n f.
Proof. exact (@lem7216294 m n f True). Qed.
Lemma lem7216382 (m : nat) (n : nat) (f : nat -> real) : (term49 m n f) = (term50 m n f).
Proof. exact (@lem7216381 m n f (@lem7216380 m n f)). Qed.
Lemma lem7216384 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7216385 (m : nat) (n : nat) (f : nat -> real) : (term50 m n f) = True.
Proof. exact (@lem7216384 (term15 m n f)). Qed.
Lemma lem7216386 (m : nat) (n : nat) (f : nat -> real) : (term49 m n f) = True.
Proof. exact (TRANS (@lem7216382 m n f) (@lem7216385 m n f)). Qed.
Lemma lem7216387 (m : nat) (n : nat) : (term51 m n) = term52.
Proof. exact (fun_ext (fun f : nat -> real => @lem7216386 m n f)). Qed.
Lemma lem7216388 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7216389 (m : nat) (n : nat) : (term53 m n) = term54.
Proof. exact (MK_COMB (@lem7216388) (@lem7216387 m n)). Qed.
Lemma lem7216391 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7216392 (t : Prop) : (term55 t) = t.
Proof. exact (@lem7216391 (nat -> real) t). Qed.
Lemma lem7216393 : term54 = True.
Proof. exact (@lem7216392 True). Qed.
Lemma lem7216394 (m : nat) (n : nat) : (term53 m n) = True.
Proof. exact (TRANS (@lem7216389 m n) (@lem7216393)). Qed.
Lemma lem7216395 (m : nat) : (term56 m) = term42.
Proof. exact (fun_ext (fun n : nat => @lem7216394 m n)). Qed.
Lemma lem7216396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216397 (m : nat) : (term57 m) = term44.
Proof. exact (MK_COMB (@lem7216396) (@lem7216395 m)). Qed.
Lemma lem7216399 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7216400 (t : Prop) : (term46 t) = t.
Proof. exact (@lem7216399 nat t). Qed.
Lemma lem7216401 : term44 = True.
Proof. exact (@lem7216400 True). Qed.
Lemma lem7216402 (m : nat) : (term57 m) = True.
Proof. exact (TRANS (@lem7216397 m) (@lem7216401)). Qed.
Lemma lem7216403 : term58 = term42.
Proof. exact (fun_ext (fun m : nat => @lem7216402 m)). Qed.
Lemma lem7216404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7216405 : term59 = term44.
Proof. exact (MK_COMB (@lem7216404) (@lem7216403)). Qed.
Lemma lem7216407 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7216408 (t : Prop) : (term46 t) = t.
Proof. exact (@lem7216407 nat t). Qed.
Lemma lem7216409 : term44 = True.
Proof. exact (@lem7216408 True). Qed.
Lemma lem7216410 : term59 = True.
Proof. exact (TRANS (@lem7216405) (@lem7216409)). Qed.
Lemma lem7216411 : True = term59.
Proof. exact (SYM (@lem7216410)). Qed.
Lemma lem7216412 : term59.
Proof. exact (EQ_MP (@lem7216411) (@lem0)). Qed.
