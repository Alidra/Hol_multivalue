Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CONST_NUMSEG_term_abbrevs.
Require Import CARD_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import NSUM_CONST_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7044317 (m : nat) : term0 m.
Proof. exact (@lem5393502 m). Qed.
Lemma lem7044318 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7044319 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7044318 m) (@lem7044317 m)). Qed.
Lemma lem7044320 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7044319 m n). Qed.
Lemma lem7044321 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7044323 (m : nat) : term5 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7044324 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem7044325 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem7044324 m) (@lem7044323 m)). Qed.
Lemma lem7044326 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem7044325 m n). Qed.
Lemma lem7044327 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem7044328 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem7044327 m n) (@lem7044326 m n)). Qed.
Lemma lem7044329 (m : nat) (n : nat) : (term8 m n) = ((term8 m n) = True).
Proof. exact (@lem7 (term8 m n)). Qed.
Lemma lem7044331 {_127196 : Type'} (c : nat) : term9 _127196 c.
Proof. exact (@lem6940531 _127196 c). Qed.
Lemma lem7044332 {_127196 : Type'} (c : nat) : (term9 _127196 c) = (term10 _127196 c).
Proof. exact (eq_refl (term9 _127196 c)). Qed.
Lemma lem7044333 {_127196 : Type'} (c : nat) : term10 _127196 c.
Proof. exact (EQ_MP (@lem7044332 _127196 c) (@lem7044331 _127196 c)). Qed.
Lemma lem7044334 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term11 _127196 c s.
Proof. exact (@lem7044333 _127196 c s). Qed.
Lemma lem7044335 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term11 _127196 c s) = (term12 _127196 s c).
Proof. exact (eq_refl (term11 _127196 c s)). Qed.
Lemma lem7044336 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term12 _127196 s c.
Proof. exact (EQ_MP (@lem7044335 _127196 s c) (@lem7044334 _127196 c s)). Qed.
Lemma lem7044337 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem7044338 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term13 _127196 s c) = (term14 _127196 s c).
Proof. exact (@lem7044336 _127196 s c (@lem7044337 _127196 s h1)). Qed.
Lemma lem7044359 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term12 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem7044338 _127196 c s h0). Qed.
Lemma lem7044360 (s : nat -> Prop) (c : nat) : term15 s c.
Proof. exact (@lem7044359 nat s c). Qed.
Lemma lem7044361 (m : nat) (n : nat) (c : nat) : term16 m n c.
Proof. exact (@lem7044360 (dotdot m n) c). Qed.
Lemma lem7044363 (m : nat) (n : nat) : (term8 m n) = True.
Proof. exact (EQ_MP (@lem7044329 m n) (@lem7044328 m n)). Qed.
Lemma lem7044364 (m : nat) (n : nat) : True = (term8 m n).
Proof. exact (SYM (@lem7044363 m n)). Qed.
Lemma lem7044365 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem7044364 m n) (@lem0)). Qed.
Lemma lem7044366 (m : nat) (n : nat) (c : nat) : (term17 m n c) = (term18 m n c).
Proof. exact (@lem7044361 m n c (@lem7044365 m n)). Qed.
Lemma lem7044368 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem7044321 n m) (@lem7044320 m n)). Qed.
Lemma lem7044369 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem7044370 (n : nat) (m : nat) : (term19 m n) = (term20 n m).
Proof. exact (MK_COMB (@lem7044369) (@lem7044368 n m)). Qed.
Lemma lem7044371 (c : nat) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7044372 (n : nat) (m : nat) (c : nat) : (term18 m n c) = (term21 n m c).
Proof. exact (MK_COMB (@lem7044370 n m) (@lem7044371 c)). Qed.
Lemma lem7044373 (n : nat) (m : nat) (c : nat) : (term17 m n c) = (term21 n m c).
Proof. exact (TRANS (@lem7044366 m n c) (@lem7044372 n m c)). Qed.
Lemma lem7044374 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7044375 (n : nat) (m : nat) (c : nat) : (term22 m n c) = (term23 n m c).
Proof. exact (MK_COMB (@lem7044374) (@lem7044373 n m c)). Qed.
Lemma lem7044376 (n : nat) (m : nat) (c : nat) : (term21 n m c) = (term21 n m c).
Proof. exact (eq_refl (term21 n m c)). Qed.
Lemma lem7044377 (n : nat) (m : nat) (c : nat) : ((term17 m n c) = (term21 n m c)) = ((term21 n m c) = (term21 n m c)).
Proof. exact (MK_COMB (@lem7044375 n m c) (@lem7044376 n m c)). Qed.
Lemma lem7044379 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7044380 (x : nat) : (x = x) = True.
Proof. exact (@lem7044379 nat x). Qed.
Lemma lem7044381 (n : nat) (m : nat) (c : nat) : ((term21 n m c) = (term21 n m c)) = True.
Proof. exact (@lem7044380 (term21 n m c)). Qed.
Lemma lem7044382 (n : nat) (m : nat) (c : nat) : ((term17 m n c) = (term21 n m c)) = True.
Proof. exact (TRANS (@lem7044377 n m c) (@lem7044381 n m c)). Qed.
Lemma lem7044383 (m : nat) (c : nat) : (term24 m c) = term25.
Proof. exact (fun_ext (fun n : nat => @lem7044382 n m c)). Qed.
Lemma lem7044384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044385 (m : nat) (c : nat) : (term26 m c) = term27.
Proof. exact (MK_COMB (@lem7044384) (@lem7044383 m c)). Qed.
Lemma lem7044387 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044388 (t : Prop) : (term29 t) = t.
Proof. exact (@lem7044387 nat t). Qed.
Lemma lem7044389 : term27 = True.
Proof. exact (@lem7044388 True). Qed.
Lemma lem7044390 (m : nat) (c : nat) : (term26 m c) = True.
Proof. exact (TRANS (@lem7044385 m c) (@lem7044389)). Qed.
Lemma lem7044391 (c : nat) : (term30 c) = term25.
Proof. exact (fun_ext (fun m : nat => @lem7044390 m c)). Qed.
Lemma lem7044392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044393 (c : nat) : (term31 c) = term27.
Proof. exact (MK_COMB (@lem7044392) (@lem7044391 c)). Qed.
Lemma lem7044395 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044396 (t : Prop) : (term29 t) = t.
Proof. exact (@lem7044395 nat t). Qed.
Lemma lem7044397 : term27 = True.
Proof. exact (@lem7044396 True). Qed.
Lemma lem7044398 (c : nat) : (term31 c) = True.
Proof. exact (TRANS (@lem7044393 c) (@lem7044397)). Qed.
Lemma lem7044399 : term32 = term25.
Proof. exact (fun_ext (fun c : nat => @lem7044398 c)). Qed.
Lemma lem7044400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7044401 : term33 = term27.
Proof. exact (MK_COMB (@lem7044400) (@lem7044399)). Qed.
Lemma lem7044403 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7044404 (t : Prop) : (term29 t) = t.
Proof. exact (@lem7044403 nat t). Qed.
Lemma lem7044405 : term27 = True.
Proof. exact (@lem7044404 True). Qed.
Lemma lem7044406 : term33 = True.
Proof. exact (TRANS (@lem7044401) (@lem7044405)). Qed.
Lemma lem7044407 : True = term33.
Proof. exact (SYM (@lem7044406)). Qed.
Lemma lem7044408 : term33.
Proof. exact (EQ_MP (@lem7044407) (@lem0)). Qed.
