Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_RMUL_term_abbrevs.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import RIGHT_SUB_DISTRIB_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1245389 (m : nat) : term0 m.
Proof. exact (@lem137108 m). Qed.
Lemma lem1245390 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245391 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1245390 m) (@lem1245389 m)). Qed.
Lemma lem1245392 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245391 m n). Qed.
Lemma lem1245393 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245394 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1245393 m n) (@lem1245392 m n)). Qed.
Lemma lem1245395 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1245394 m n p). Qed.
Lemma lem1245396 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1245398 (m : nat) : term7 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1245399 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1245400 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1245399 m) (@lem1245398 m)). Qed.
Lemma lem1245401 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1245400 m n). Qed.
Lemma lem1245402 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1245403 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem1245402 m n) (@lem1245401 m n)). Qed.
Lemma lem1245404 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem1245403 m n p). Qed.
Lemma lem1245405 (m : nat) (n : nat) (p : nat) : (term11 m n p) = ((term12 m n p) = (term13 m n p)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1245407 (n : nat) : term14 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245408 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem1245409 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1245408 n) (@lem1245407 n)). Qed.
Lemma lem1245410 (n : nat) (m : nat) : term16 n m.
Proof. exact (@lem1245409 n m). Qed.
Lemma lem1245411 (n : nat) (m : nat) : (term16 n m) = ((term17 m n) = (term18 n m)).
Proof. exact (eq_refl (term16 n m)). Qed.
Lemma lem1245428 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (EQ_MP (@lem1245411 n m) (@lem1245410 n m)). Qed.
Lemma lem1245429 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1245430 (n : nat) (m : nat) : (term19 m n) = (term20 n m).
Proof. exact (MK_COMB (@lem1245429) (@lem1245428 n m)). Qed.
Lemma lem1245431 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1245432 (n : nat) (m : nat) (p : nat) : (term21 m n p) = (term22 n m p).
Proof. exact (MK_COMB (@lem1245430 n m) (@lem1245431 p)). Qed.
Lemma lem1245434 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term13 m n p).
Proof. exact (EQ_MP (@lem1245405 m n p) (@lem1245404 m n p)). Qed.
Lemma lem1245435 (n : nat) (m : nat) (p : nat) : (term22 n m p) = (term23 n m p).
Proof. exact (@lem1245434 (Nat.sub m n) (Nat.sub n m) p). Qed.
Lemma lem1245437 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem1245396 m n p) (@lem1245395 m n p)). Qed.
Lemma lem1245438 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245439 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term25 m n p).
Proof. exact (MK_COMB (@lem1245438) (@lem1245437 m n p)). Qed.
Lemma lem1245441 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem1245396 m n p) (@lem1245395 m n p)). Qed.
Lemma lem1245442 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (@lem1245441 n m p). Qed.
Lemma lem1245443 (n : nat) (m : nat) (p : nat) : (term23 n m p) = (term26 n m p).
Proof. exact (MK_COMB (@lem1245439 m n p) (@lem1245442 n m p)). Qed.
Lemma lem1245444 (n : nat) (m : nat) (p : nat) : (term22 n m p) = (term26 n m p).
Proof. exact (TRANS (@lem1245435 n m p) (@lem1245443 n m p)). Qed.
Lemma lem1245445 (n : nat) (m : nat) (p : nat) : (term21 m n p) = (term26 n m p).
Proof. exact (TRANS (@lem1245432 n m p) (@lem1245444 n m p)). Qed.
Lemma lem1245446 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245447 (n : nat) (m : nat) (p : nat) : (term27 m n p) = (term28 n m p).
Proof. exact (MK_COMB (@lem1245446) (@lem1245445 n m p)). Qed.
Lemma lem1245449 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (EQ_MP (@lem1245411 n m) (@lem1245410 n m)). Qed.
Lemma lem1245450 (n : nat) (m : nat) (p : nat) : (term29 m n p) = (term26 n m p).
Proof. exact (@lem1245449 (Nat.mul n p) (Nat.mul m p)). Qed.
Lemma lem1245451 (n : nat) (m : nat) (p : nat) : ((term21 m n p) = (term29 m n p)) = ((term26 n m p) = (term26 n m p)).
Proof. exact (MK_COMB (@lem1245447 n m p) (@lem1245450 n m p)). Qed.
Lemma lem1245453 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245454 (x : nat) : (x = x) = True.
Proof. exact (@lem1245453 nat x). Qed.
Lemma lem1245455 (n : nat) (m : nat) (p : nat) : ((term26 n m p) = (term26 n m p)) = True.
Proof. exact (@lem1245454 (term26 n m p)). Qed.
Lemma lem1245456 (m : nat) (n : nat) (p : nat) : ((term21 m n p) = (term29 m n p)) = True.
Proof. exact (TRANS (@lem1245451 n m p) (@lem1245455 n m p)). Qed.
Lemma lem1245457 (m : nat) (n : nat) : (term30 m n) = term31.
Proof. exact (fun_ext (fun p : nat => @lem1245456 m n p)). Qed.
Lemma lem1245458 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245459 (m : nat) (n : nat) : (term32 m n) = term33.
Proof. exact (MK_COMB (@lem1245458) (@lem1245457 m n)). Qed.
Lemma lem1245461 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245462 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1245461 nat t). Qed.
Lemma lem1245463 : term33 = True.
Proof. exact (@lem1245462 True). Qed.
Lemma lem1245464 (m : nat) (n : nat) : (term32 m n) = True.
Proof. exact (TRANS (@lem1245459 m n) (@lem1245463)). Qed.
Lemma lem1245465 (m : nat) : (term36 m) = term31.
Proof. exact (fun_ext (fun n : nat => @lem1245464 m n)). Qed.
Lemma lem1245466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245467 (m : nat) : (term37 m) = term33.
Proof. exact (MK_COMB (@lem1245466) (@lem1245465 m)). Qed.
Lemma lem1245469 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245470 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1245469 nat t). Qed.
Lemma lem1245471 : term33 = True.
Proof. exact (@lem1245470 True). Qed.
Lemma lem1245472 (m : nat) : (term37 m) = True.
Proof. exact (TRANS (@lem1245467 m) (@lem1245471)). Qed.
Lemma lem1245473 : term38 = term31.
Proof. exact (fun_ext (fun m : nat => @lem1245472 m)). Qed.
Lemma lem1245474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245475 : term39 = term33.
Proof. exact (MK_COMB (@lem1245474) (@lem1245473)). Qed.
Lemma lem1245477 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245478 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1245477 nat t). Qed.
Lemma lem1245479 : term33 = True.
Proof. exact (@lem1245478 True). Qed.
Lemma lem1245480 : term39 = True.
Proof. exact (TRANS (@lem1245475) (@lem1245479)). Qed.
Lemma lem1245481 : True = term39.
Proof. exact (SYM (@lem1245480)). Qed.
Lemma lem1245482 : term39.
Proof. exact (EQ_MP (@lem1245481) (@lem0)). Qed.
