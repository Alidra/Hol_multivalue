Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_LMUL_term_abbrevs.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LEFT_SUB_DISTRIB_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1245296 (m : nat) : term0 m.
Proof. exact (@lem137035 m). Qed.
Lemma lem1245297 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245298 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1245297 m) (@lem1245296 m)). Qed.
Lemma lem1245299 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245298 m n). Qed.
Lemma lem1245300 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245301 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem1245300 n m) (@lem1245299 m n)). Qed.
Lemma lem1245302 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem1245301 n m p). Qed.
Lemma lem1245303 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem1245305 (m : nat) : term7 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1245306 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1245307 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1245306 m) (@lem1245305 m)). Qed.
Lemma lem1245308 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1245307 m n). Qed.
Lemma lem1245309 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1245310 (n : nat) (m : nat) : term10 n m.
Proof. exact (EQ_MP (@lem1245309 n m) (@lem1245308 m n)). Qed.
Lemma lem1245311 (n : nat) (m : nat) (p : nat) : term11 n m p.
Proof. exact (@lem1245310 n m p). Qed.
Lemma lem1245312 (n : nat) (m : nat) (p : nat) : (term11 n m p) = ((term12 m n p) = (term13 n m p)).
Proof. exact (eq_refl (term11 n m p)). Qed.
Lemma lem1245314 (n : nat) : term14 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245315 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1245316 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1245315 n) (@lem1245314 n)). Qed.
Lemma lem1245317 (n : nat) (m : nat) : term16 n m.
Proof. exact (@lem1245316 n m). Qed.
Lemma lem1245318 (n : nat) (m : nat) : (term16 n m) = ((term17 m n) = (term18 n m)).
Proof. exact (eq_refl (term16 n m)). Qed.
Lemma lem1245335 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (EQ_MP (@lem1245318 n m) (@lem1245317 n m)). Qed.
Lemma lem1245336 (p : nat) (n : nat) : (term17 n p) = (term18 p n).
Proof. exact (@lem1245335 p n). Qed.
Lemma lem1245337 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1245338 (m : nat) (p : nat) (n : nat) : (term19 m n p) = (term20 m p n).
Proof. exact (MK_COMB (@lem1245337 m) (@lem1245336 p n)). Qed.
Lemma lem1245340 (n : nat) (m : nat) (p : nat) : (term12 m n p) = (term13 n m p).
Proof. exact (EQ_MP (@lem1245312 n m p) (@lem1245311 n m p)). Qed.
Lemma lem1245341 (m : nat) (p : nat) (n : nat) : (term20 m p n) = (term21 m p n).
Proof. exact (@lem1245340 (Nat.sub n p) m (Nat.sub p n)). Qed.
Lemma lem1245343 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1245303 n m p) (@lem1245302 n m p)). Qed.
Lemma lem1245344 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245345 (n : nat) (m : nat) (p : nat) : (term22 m n p) = (term23 n m p).
Proof. exact (MK_COMB (@lem1245344) (@lem1245343 n m p)). Qed.
Lemma lem1245347 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1245303 n m p) (@lem1245302 n m p)). Qed.
Lemma lem1245348 (p : nat) (m : nat) (n : nat) : (term5 m p n) = (term6 p m n).
Proof. exact (@lem1245347 p m n). Qed.
Lemma lem1245349 (p : nat) (m : nat) (n : nat) : (term21 m p n) = (term24 p m n).
Proof. exact (MK_COMB (@lem1245345 n m p) (@lem1245348 p m n)). Qed.
Lemma lem1245350 (p : nat) (m : nat) (n : nat) : (term20 m p n) = (term24 p m n).
Proof. exact (TRANS (@lem1245341 m p n) (@lem1245349 p m n)). Qed.
Lemma lem1245351 (p : nat) (m : nat) (n : nat) : (term19 m n p) = (term24 p m n).
Proof. exact (TRANS (@lem1245338 m p n) (@lem1245350 p m n)). Qed.
Lemma lem1245352 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245353 (p : nat) (m : nat) (n : nat) : (term25 m n p) = (term26 p m n).
Proof. exact (MK_COMB (@lem1245352) (@lem1245351 p m n)). Qed.
Lemma lem1245355 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (EQ_MP (@lem1245318 n m) (@lem1245317 n m)). Qed.
Lemma lem1245356 (p : nat) (m : nat) (n : nat) : (term27 n m p) = (term24 p m n).
Proof. exact (@lem1245355 (Nat.mul m p) (Nat.mul m n)). Qed.
Lemma lem1245357 (p : nat) (m : nat) (n : nat) : ((term19 m n p) = (term27 n m p)) = ((term24 p m n) = (term24 p m n)).
Proof. exact (MK_COMB (@lem1245353 p m n) (@lem1245356 p m n)). Qed.
Lemma lem1245359 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245360 (x : nat) : (x = x) = True.
Proof. exact (@lem1245359 nat x). Qed.
Lemma lem1245361 (p : nat) (m : nat) (n : nat) : ((term24 p m n) = (term24 p m n)) = True.
Proof. exact (@lem1245360 (term24 p m n)). Qed.
Lemma lem1245362 (n : nat) (m : nat) (p : nat) : ((term19 m n p) = (term27 n m p)) = True.
Proof. exact (TRANS (@lem1245357 p m n) (@lem1245361 p m n)). Qed.
Lemma lem1245363 (n : nat) (m : nat) : (term28 n m) = term29.
Proof. exact (fun_ext (fun p : nat => @lem1245362 n m p)). Qed.
Lemma lem1245364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245365 (n : nat) (m : nat) : (term30 n m) = term31.
Proof. exact (MK_COMB (@lem1245364) (@lem1245363 n m)). Qed.
Lemma lem1245367 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245368 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1245367 nat t). Qed.
Lemma lem1245369 : term31 = True.
Proof. exact (@lem1245368 True). Qed.
Lemma lem1245370 (n : nat) (m : nat) : (term30 n m) = True.
Proof. exact (TRANS (@lem1245365 n m) (@lem1245369)). Qed.
Lemma lem1245371 (m : nat) : (term34 m) = term29.
Proof. exact (fun_ext (fun n : nat => @lem1245370 n m)). Qed.
Lemma lem1245372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245373 (m : nat) : (term35 m) = term31.
Proof. exact (MK_COMB (@lem1245372) (@lem1245371 m)). Qed.
Lemma lem1245375 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245376 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1245375 nat t). Qed.
Lemma lem1245377 : term31 = True.
Proof. exact (@lem1245376 True). Qed.
Lemma lem1245378 (m : nat) : (term35 m) = True.
Proof. exact (TRANS (@lem1245373 m) (@lem1245377)). Qed.
Lemma lem1245379 : term36 = term29.
Proof. exact (fun_ext (fun m : nat => @lem1245378 m)). Qed.
Lemma lem1245380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245381 : term37 = term31.
Proof. exact (MK_COMB (@lem1245380) (@lem1245379)). Qed.
Lemma lem1245383 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245384 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1245383 nat t). Qed.
Lemma lem1245385 : term31 = True.
Proof. exact (@lem1245384 True). Qed.
Lemma lem1245386 : term37 = True.
Proof. exact (TRANS (@lem1245381) (@lem1245385)). Qed.
Lemma lem1245387 : True = term37.
Proof. exact (SYM (@lem1245386)). Qed.
Lemma lem1245388 : term37.
Proof. exact (EQ_MP (@lem1245387) (@lem0)). Qed.
