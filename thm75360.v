Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm75360_term_abbrevs.
Require Import EXISTS_UNIQUE_REFL_spec.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import SUC_INJ_spec.
Require Import UNIQUE_SKOLEM_ALT_spec.
Require Import UNWIND_THM1_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm72734_spec.
Require Import thm73444_spec.
Require Import thm7400_spec.
Require Import thm82_spec.
Require Import thm9102_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem73445 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem73446 (P : nat -> Prop) (h1 : term0) : term1 P.
Proof. exact (@lem73445 h1 P). Qed.
Lemma lem73447 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem73448 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (EQ_MP (@lem73447 P) (@lem73446 P h1)). Qed.
Lemma lem73449 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem73450 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem73448 P h1 (@lem73449 P h2)). Qed.
Lemma lem73451 (P : nat -> Prop) (h1 : term3 P) : term5 P.
Proof. exact (fun h0 : term0 => @lem73450 P h0 h1). Qed.
Lemma lem73452 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem73453 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem73451 P h2 (@lem73452 h1)). Qed.
Lemma lem73454 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (fun h0 : term3 P => @lem73453 P h1 h0). Qed.
Lemma lem73455 (h1 : term0) : term0.
Proof. exact (fun P : nat -> Prop => @lem73454 P h1). Qed.
Lemma lem73456 : term6.
Proof. exact (fun h0 : term0 => @lem73455 h0). Qed.
Lemma lem73457 : term0.
Proof. exact (@lem73456 (@lem73444)). Qed.
Lemma lem73458 (P : nat -> Prop) : term1 P.
Proof. exact (@lem73457 P). Qed.
Lemma lem73459 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem73461 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem73462 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem73463 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem73462 A B f) (@lem73461 A B f)). Qed.
Lemma lem73464 {A B : Type'} (f : A -> B) (g : A -> B) : term9 A B f g.
Proof. exact (@lem73463 A B f g). Qed.
Lemma lem73465 {A B : Type'} (f : A -> B) (g : A -> B) : (term9 A B f g) = ((f = g) = (term10 A B f g)).
Proof. exact (eq_refl (term9 A B f g)). Qed.
Lemma lem73467 {A B : Type'} (P : type1413 A B) : term11 A B P.
Proof. exact (@lem13833 A B P). Qed.
Lemma lem73468 {A B : Type'} (P : type1413 A B) : (term11 A B P) = ((term12 A B P) = (term13 A B P)).
Proof. exact (eq_refl (term11 A B P)). Qed.
Lemma lem73470 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem73471 {A : Type'} (P : A -> Prop) : (term14 A P) = ((term15 A P) = (term16 A P)).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem73473 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem73474 {A : Type'} (P : A -> Prop) : (term17 A P) = (term18 A P).
Proof. exact (eq_refl (term17 A P)). Qed.
Lemma lem73475 {A : Type'} (P : A -> Prop) : term18 A P.
Proof. exact (EQ_MP (@lem73474 A P) (@lem73473 A P)). Qed.
Lemma lem73476 {A : Type'} (P : A -> Prop) (a : A) : term19 A P a.
Proof. exact (@lem73475 A P a). Qed.
Lemma lem73477 {A : Type'} (P : A -> Prop) (a : A) : (term19 A P a) = ((term20 A a P) = (P a)).
Proof. exact (eq_refl (term19 A P a)). Qed.
Lemma lem73492 {A : Type'} (a : A) : term21 A a.
Proof. exact (@lem4476 A a). Qed.
Lemma lem73493 {A : Type'} (a : A) : (term21 A a) = (term22 A a).
Proof. exact (eq_refl (term21 A a)). Qed.
Lemma lem73494 {A : Type'} (a : A) : term22 A a.
Proof. exact (EQ_MP (@lem73493 A a) (@lem73492 A a)). Qed.
Lemma lem73495 {A : Type'} (a : A) : (term22 A a) = ((term22 A a) = True).
Proof. exact (@lem7 (term22 A a)). Qed.
Lemma lem73497 (m : nat) : term23 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem73498 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem73499 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem73498 m) (@lem73497 m)). Qed.
Lemma lem73500 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem73499 m n). Qed.
Lemma lem73501 (m : nat) (n : nat) : (term25 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem73503 (n : nat) : term26 n.
Proof. exact (@lem72734 n). Qed.
Lemma lem73504 (n : nat) : (term26 n) = (term27 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem73505 (n : nat) : term27 n.
Proof. exact (EQ_MP (@lem73504 n) (@lem73503 n)). Qed.
Lemma lem73506 (n : nat) : term28 n.
Proof. exact (@lem82 ((S n) = 0)). Qed.
Lemma lem73509 (n : nat) (h1 : (S n) = 0) : (S n) = 0.
Proof. exact (h1). Qed.
Lemma lem73510 (n : nat) (h1 : (S n) = 0) : 0 = (S n).
Proof. exact (SYM (@lem73509 n h1)). Qed.
Lemma lem73511 (n : nat) (h1 : 0 = (S n)) : 0 = (S n).
Proof. exact (h1). Qed.
Lemma lem73512 (n : nat) (h1 : 0 = (S n)) : (S n) = 0.
Proof. exact (SYM (@lem73511 n h1)). Qed.
Lemma lem73513 (n : nat) : ((S n) = 0) = (0 = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = 0 => @lem73510 n h1) (fun h1 : 0 = (S n) => @lem73512 n h1)). Qed.
Lemma lem73514 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem73515 (n : nat) : (term27 n) = (term29 n).
Proof. exact (MK_COMB (@lem73514) (@lem73513 n)). Qed.
Lemma lem73516 (n : nat) : term29 n.
Proof. exact (EQ_MP (@lem73515 n) (@lem73505 n)). Qed.
Lemma lem73517 (n : nat) : term30 n.
Proof. exact (@lem82 (0 = (S n))). Qed.
Lemma lem73535 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem73536 (P : nat -> Prop) (h1 : term0) : term1 P.
Proof. exact (@lem73535 h1 P). Qed.
Lemma lem73537 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem73538 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (EQ_MP (@lem73537 P) (@lem73536 P h1)). Qed.
Lemma lem73539 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem73540 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem73538 P h1 (@lem73539 P h2)). Qed.
Lemma lem73541 (P : nat -> Prop) (h1 : term3 P) : term5 P.
Proof. exact (fun h0 : term0 => @lem73540 P h0 h1). Qed.
Lemma lem73542 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem73543 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem73541 P h2 (@lem73542 h1)). Qed.
Lemma lem73544 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (fun h0 : term3 P => @lem73543 P h1 h0). Qed.
Lemma lem73545 (h1 : term0) : term0.
Proof. exact (fun P : nat -> Prop => @lem73544 P h1). Qed.
Lemma lem73546 : term6.
Proof. exact (fun h0 : term0 => @lem73545 h0). Qed.
Lemma lem73547 : term0.
Proof. exact (@lem73546 (@lem73444)). Qed.
Lemma lem73548 (P : nat -> Prop) : term1 P.
Proof. exact (@lem73547 P). Qed.
Lemma lem73549 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem73551 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73552 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : a1 = e.
Proof. exact (proj2 (@lem73551 A a0 a1 e h1)). Qed.
Lemma lem73553 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : a0 = 0.
Proof. exact (proj1 (@lem73551 A a0 a1 e h1)). Qed.
Lemma lem73554 {A : Type'} (PRG : type1597 A) (e : A) (h1 : PRG 0 e) : PRG 0 e.
Proof. exact (h1). Qed.
Lemma lem73555 {A : Type'} (PRG : type1597 A) : PRG = PRG.
Proof. exact (eq_refl PRG). Qed.
Lemma lem73556 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : (PRG a0) = (PRG 0).
Proof. exact (MK_COMB (@lem73555 A PRG) (@lem73553 A a0 a1 e h1)). Qed.
Lemma lem73557 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : (PRG a0 a1) = (PRG 0 e).
Proof. exact (MK_COMB (@lem73556 A PRG a0 a1 e h1) (@lem73552 A a0 a1 e h1)). Qed.
Lemma lem73558 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : (PRG 0 e) = (PRG a0 a1).
Proof. exact (SYM (@lem73557 A PRG a0 a1 e h1)). Qed.
Lemma lem73559 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (h1 : term31 A a0 a1 e) (h2 : PRG 0 e) : PRG a0 a1.
Proof. exact (EQ_MP (@lem73558 A PRG a0 a1 e h1) (@lem73554 A PRG e h2)). Qed.
Lemma lem73560 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (h1 : PRG 0 e) : term32 A e PRG a0 a1.
Proof. exact (fun h0 : term31 A a0 a1 e => @lem73559 A a0 a1 PRG e h0 h1). Qed.
Lemma lem73561 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73562 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (h1 : term31 A a0 a1 e) (h2 : PRG 0 e) : PRG a0 a1.
Proof. exact (@lem73560 A a0 a1 PRG e h2 (@lem73561 A a0 a1 e h1)). Qed.
Lemma lem73563 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (h1 : PRG 0 e) : term32 A e PRG a0 a1.
Proof. exact (fun h0 : term31 A a0 a1 e => @lem73562 A a0 a1 PRG e h0 h1). Qed.
Lemma lem73564 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (h1 : PRG 0 e) : term33 A e PRG a0.
Proof. exact (fun a1 : A => @lem73563 A a0 a1 PRG e h1). Qed.
Lemma lem73565 {A : Type'} (PRG : type1597 A) (e : A) (h1 : PRG 0 e) : term34 A e PRG.
Proof. exact (fun a0 : nat => @lem73564 A a0 PRG e h1). Qed.
Lemma lem73566 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : term34 A e PRG.
Proof. exact (h1). Qed.
Lemma lem73567 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : term35 A e PRG.
Proof. exact (@lem73566 A e PRG h1 0). Qed.
Lemma lem73568 {A : Type'} (e : A) (PRG : type1597 A) : (term35 A e PRG) = (term36 A e PRG).
Proof. exact (eq_refl (term35 A e PRG)). Qed.
Lemma lem73569 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : term36 A e PRG.
Proof. exact (EQ_MP (@lem73568 A e PRG) (@lem73567 A e PRG h1)). Qed.
Lemma lem73570 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : term37 A PRG e.
Proof. exact (@lem73569 A e PRG h1 e). Qed.
Lemma lem73571 {A : Type'} (PRG : type1597 A) (e : A) : (term37 A PRG e) = (term38 A PRG e).
Proof. exact (eq_refl (term37 A PRG e)). Qed.
Lemma lem73572 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : term38 A PRG e.
Proof. exact (EQ_MP (@lem73571 A PRG e) (@lem73570 A e PRG h1)). Qed.
Lemma lem73573 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem73574 {A : Type'} (e : A) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem73575 {A : Type'} (e : A) : term39 A e.
Proof. exact (conj (@lem73573) (@lem73574 A e)). Qed.
Lemma lem73576 {A : Type'} (e : A) (PRG : type1597 A) (h1 : term34 A e PRG) : PRG 0 e.
Proof. exact (@lem73572 A e PRG h1 (@lem73575 A e)). Qed.
Lemma lem73577 {A : Type'} (PRG : type1597 A) (e : A) : term40 A PRG e.
Proof. exact (fun h0 : term34 A e PRG => @lem73576 A e PRG h0). Qed.
Lemma lem73578 {A : Type'} (e : A) (PRG : type1597 A) : term41 A e PRG.
Proof. exact (fun h0 : PRG 0 e => @lem73565 A PRG e h0). Qed.
Lemma lem73579 {A : Type'} (PRG : type1597 A) (e : A) : term42 A PRG e.
Proof. exact (conj (@lem73578 A e PRG) (@lem73577 A PRG e)). Qed.
Lemma lem73580 {A : Type'} (e : A) (PRG : type1597 A) : (term42 A PRG e) = ((PRG 0 e) = (term34 A e PRG)).
Proof. exact (@lem32 (PRG 0 e) (term34 A e PRG)). Qed.
Lemma lem73581 {A : Type'} (e : A) (PRG : type1597 A) : (PRG 0 e) = (term34 A e PRG).
Proof. exact (EQ_MP (@lem73580 A e PRG) (@lem73579 A PRG e)). Qed.
Lemma lem73582 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term32 A e PRG a0 a1) : term32 A e PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73583 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73584 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term31 A a0 a1 e) (h2 : term32 A e PRG a0 a1) : PRG a0 a1.
Proof. exact (@lem73582 A e PRG a0 a1 h2 (@lem73583 A a0 a1 e h1)). Qed.
Lemma lem73585 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term43 A e PRG a0 a1.
Proof. exact (fun h0 : term32 A e PRG a0 a1 => @lem73584 A e PRG a0 a1 h1 h0). Qed.
Lemma lem73586 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term32 A e PRG a0 a1) : term32 A e PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73587 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term31 A a0 a1 e) (h2 : term32 A e PRG a0 a1) : PRG a0 a1.
Proof. exact (@lem73585 A PRG a0 a1 e h1 (@lem73586 A e PRG a0 a1 h2)). Qed.
Lemma lem73588 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term32 A e PRG a0 a1) : term32 A e PRG a0 a1.
Proof. exact (fun h0 : term31 A a0 a1 e => @lem73587 A e PRG a0 a1 h0 h1). Qed.
Lemma lem73589 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term32 A e PRG a0 a1) : term32 A e PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73590 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73591 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term31 A a0 a1 e) (h2 : term32 A e PRG a0 a1) : PRG a0 a1.
Proof. exact (@lem73589 A e PRG a0 a1 h2 (@lem73590 A a0 a1 e h1)). Qed.
Lemma lem73592 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term32 A e PRG a0 a1) : term32 A e PRG a0 a1.
Proof. exact (fun h0 : term31 A a0 a1 e => @lem73591 A e PRG a0 a1 h0 h1). Qed.
Lemma lem73593 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term44 A e PRG a0 a1.
Proof. exact (fun h0 : term32 A e PRG a0 a1 => @lem73592 A e PRG a0 a1 h0). Qed.
Lemma lem73594 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term44 A e PRG a0 a1.
Proof. exact (fun h0 : term32 A e PRG a0 a1 => @lem73588 A e PRG a0 a1 h0). Qed.
Lemma lem73595 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term45 A e PRG a0 a1.
Proof. exact (conj (@lem73594 A e PRG a0 a1) (@lem73593 A e PRG a0 a1)). Qed.
Lemma lem73596 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term45 A e PRG a0 a1) = ((term32 A e PRG a0 a1) = (term32 A e PRG a0 a1)).
Proof. exact (@lem32 (term32 A e PRG a0 a1) (term32 A e PRG a0 a1)). Qed.
Lemma lem73597 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term32 A e PRG a0 a1) = (term32 A e PRG a0 a1).
Proof. exact (EQ_MP (@lem73596 A e PRG a0 a1) (@lem73595 A e PRG a0 a1)). Qed.
Lemma lem73598 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) : (term46 A e PRG a0) = (term46 A e PRG a0).
Proof. exact (fun_ext (fun a1 : A => @lem73597 A e PRG a0 a1)). Qed.
Lemma lem73599 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem73600 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) : (term33 A e PRG a0) = (term33 A e PRG a0).
Proof. exact (MK_COMB (@lem73599 A) (@lem73598 A e PRG a0)). Qed.
Lemma lem73601 {A : Type'} (e : A) (PRG : type1597 A) : (term47 A e PRG) = (term47 A e PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem73600 A e PRG a0)). Qed.
Lemma lem73602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem73603 {A : Type'} (e : A) (PRG : type1597 A) : (term34 A e PRG) = (term34 A e PRG).
Proof. exact (MK_COMB (@lem73602) (@lem73601 A e PRG)). Qed.
Lemma lem73604 {A : Type'} (e : A) (PRG : type1597 A) : (PRG 0 e) = (term34 A e PRG).
Proof. exact (TRANS (@lem73581 A e PRG) (@lem73603 A e PRG)). Qed.
Lemma lem73605 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term48 A a0 a1 f PRG n b.
Proof. exact (h1). Qed.
Lemma lem73606 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term49 A a1 f PRG n b.
Proof. exact (proj2 (@lem73605 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73607 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : a0 = (S n).
Proof. exact (proj1 (@lem73605 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73608 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : PRG n b.
Proof. exact (proj2 (@lem73606 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73609 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : a1 = (f b n).
Proof. exact (proj1 (@lem73606 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73610 {A : Type'} (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term50 A PRG f.
Proof. exact (h1). Qed.
Lemma lem73611 {A : Type'} (b : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term51 A PRG f b.
Proof. exact (@lem73610 A PRG f h1 b). Qed.
Lemma lem73612 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) : (term51 A PRG f b) = (term52 A PRG f b).
Proof. exact (eq_refl (term51 A PRG f b)). Qed.
Lemma lem73613 {A : Type'} (b : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term52 A PRG f b.
Proof. exact (EQ_MP (@lem73612 A PRG f b) (@lem73611 A b PRG f h1)). Qed.
Lemma lem73614 {A : Type'} (b : A) (n : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term53 A PRG f b n.
Proof. exact (@lem73613 A b PRG f h1 n). Qed.
Lemma lem73615 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term53 A PRG f b n) = (term54 A PRG f b n).
Proof. exact (eq_refl (term53 A PRG f b n)). Qed.
Lemma lem73616 {A : Type'} (b : A) (n : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term54 A PRG f b n.
Proof. exact (EQ_MP (@lem73615 A PRG f b n) (@lem73614 A b n PRG f h1)). Qed.
Lemma lem73617 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term50 A PRG f) (h2 : term48 A a0 a1 f PRG n b) : term55 A PRG f b n.
Proof. exact (@lem73616 A b n PRG f h1 (@lem73608 A a0 a1 f PRG n b h2)). Qed.
Lemma lem73618 {A : Type'} (PRG : type1597 A) : PRG = PRG.
Proof. exact (eq_refl PRG). Qed.
Lemma lem73619 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : (PRG a0) = (term56 A PRG n).
Proof. exact (MK_COMB (@lem73618 A PRG) (@lem73607 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73620 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : (PRG a0 a1) = (term55 A PRG f b n).
Proof. exact (MK_COMB (@lem73619 A a0 a1 f PRG n b h1) (@lem73609 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73621 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : (term55 A PRG f b n) = (PRG a0 a1).
Proof. exact (SYM (@lem73620 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73622 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term50 A PRG f) (h2 : term48 A a0 a1 f PRG n b) : PRG a0 a1.
Proof. exact (EQ_MP (@lem73621 A a0 a1 f PRG n b h2) (@lem73617 A a0 a1 f PRG n b h1 h2)). Qed.
Lemma lem73623 {A : Type'} (n : nat) (b : A) (a0 : nat) (a1 : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term57 A f n b PRG a0 a1.
Proof. exact (fun h0 : term48 A a0 a1 f PRG n b => @lem73622 A a0 a1 f PRG n b h1 h0). Qed.
Lemma lem73624 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term48 A a0 a1 f PRG n b.
Proof. exact (h1). Qed.
Lemma lem73625 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term50 A PRG f) (h2 : term48 A a0 a1 f PRG n b) : PRG a0 a1.
Proof. exact (@lem73623 A n b a0 a1 PRG f h1 (@lem73624 A a0 a1 f PRG n b h2)). Qed.
Lemma lem73626 {A : Type'} (n : nat) (b : A) (a0 : nat) (a1 : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term57 A f n b PRG a0 a1.
Proof. exact (fun h0 : term48 A a0 a1 f PRG n b => @lem73625 A a0 a1 f PRG n b h1 h0). Qed.
Lemma lem73627 {A : Type'} (b : A) (a0 : nat) (a1 : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term58 A f b PRG a0 a1.
Proof. exact (fun n : nat => @lem73626 A n b a0 a1 PRG f h1). Qed.
Lemma lem73628 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term59 A f PRG a0 a1.
Proof. exact (fun b : A => @lem73627 A b a0 a1 PRG f h1). Qed.
Lemma lem73629 {A : Type'} (a0 : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term60 A f PRG a0.
Proof. exact (fun a1 : A => @lem73628 A a0 a1 PRG f h1). Qed.
Lemma lem73630 {A : Type'} (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term61 A f PRG.
Proof. exact (fun a0 : nat => @lem73629 A a0 PRG f h1). Qed.
Lemma lem73631 {A : Type'} (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term61 A f PRG.
Proof. exact (h1). Qed.
Lemma lem73632 {A : Type'} (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term62 A f PRG n.
Proof. exact (@lem73631 A f PRG h1 (S n)). Qed.
Lemma lem73633 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term62 A f PRG n) = (term63 A f PRG n).
Proof. exact (eq_refl (term62 A f PRG n)). Qed.
Lemma lem73634 {A : Type'} (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term63 A f PRG n.
Proof. exact (EQ_MP (@lem73633 A f PRG n) (@lem73632 A n f PRG h1)). Qed.
Lemma lem73635 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term64 A PRG f b n.
Proof. exact (@lem73634 A n f PRG h1 (f b n)). Qed.
Lemma lem73636 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term64 A PRG f b n) = (term65 A PRG f b n).
Proof. exact (eq_refl (term64 A PRG f b n)). Qed.
Lemma lem73637 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term65 A PRG f b n.
Proof. exact (EQ_MP (@lem73636 A PRG f b n) (@lem73635 A b n f PRG h1)). Qed.
Lemma lem73638 {A : Type'} (n : nat) (b : A) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term66 A PRG f n b.
Proof. exact (@lem73637 A b n f PRG h1 b). Qed.
Lemma lem73639 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term66 A PRG f n b) = (term67 A PRG f b n).
Proof. exact (eq_refl (term66 A PRG f n b)). Qed.
Lemma lem73640 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term67 A PRG f b n.
Proof. exact (EQ_MP (@lem73639 A PRG f b n) (@lem73638 A n b f PRG h1)). Qed.
Lemma lem73641 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term68 A PRG f b n.
Proof. exact (@lem73640 A b n f PRG h1 n). Qed.
Lemma lem73642 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term68 A PRG f b n) = (term69 A PRG f b n).
Proof. exact (eq_refl (term68 A PRG f b n)). Qed.
Lemma lem73643 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term69 A PRG f b n.
Proof. exact (EQ_MP (@lem73642 A PRG f b n) (@lem73641 A b n f PRG h1)). Qed.
Lemma lem73644 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : PRG n b.
Proof. exact (h1). Qed.
Lemma lem73645 {A : Type'} (f : type1423 A) (b : A) (n : nat) : (f b n) = (f b n).
Proof. exact (eq_refl (f b n)). Qed.
Lemma lem73646 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : term70 A f PRG n b.
Proof. exact (conj (@lem73645 A f b n) (@lem73644 A PRG n b h1)). Qed.
Lemma lem73647 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem73648 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : term71 A f PRG n b.
Proof. exact (conj (@lem73647 n) (@lem73646 A f PRG n b h1)). Qed.
Lemma lem73649 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term61 A f PRG) (h2 : PRG n b) : term55 A PRG f b n.
Proof. exact (@lem73643 A b n f PRG h1 (@lem73648 A f PRG n b h2)). Qed.
Lemma lem73650 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term54 A PRG f b n.
Proof. exact (fun h0 : PRG n b => @lem73649 A f PRG n b h1 h0). Qed.
Lemma lem73651 {A : Type'} (b : A) (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term52 A PRG f b.
Proof. exact (fun n : nat => @lem73650 A b n f PRG h1). Qed.
Lemma lem73652 {A : Type'} (f : type1423 A) (PRG : type1597 A) (h1 : term61 A f PRG) : term50 A PRG f.
Proof. exact (fun b : A => @lem73651 A b f PRG h1). Qed.
Lemma lem73653 {A : Type'} (PRG : type1597 A) (f : type1423 A) : term72 A PRG f.
Proof. exact (fun h0 : term61 A f PRG => @lem73652 A f PRG h0). Qed.
Lemma lem73654 {A : Type'} (f : type1423 A) (PRG : type1597 A) : term73 A f PRG.
Proof. exact (fun h0 : term50 A PRG f => @lem73630 A PRG f h0). Qed.
Lemma lem73655 {A : Type'} (PRG : type1597 A) (f : type1423 A) : term74 A PRG f.
Proof. exact (conj (@lem73654 A f PRG) (@lem73653 A PRG f)). Qed.
Lemma lem73656 {A : Type'} (f : type1423 A) (PRG : type1597 A) : (term74 A PRG f) = ((term50 A PRG f) = (term61 A f PRG)).
Proof. exact (@lem32 (term50 A PRG f) (term61 A f PRG)). Qed.
Lemma lem73657 {A : Type'} (f : type1423 A) (PRG : type1597 A) : (term50 A PRG f) = (term61 A f PRG).
Proof. exact (EQ_MP (@lem73656 A f PRG) (@lem73655 A PRG f)). Qed.
Lemma lem73658 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term59 A f PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73659 {A : Type'} (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term75 A f PRG a0 a1 b.
Proof. exact (@lem73658 A f PRG a0 a1 h1 b). Qed.
Lemma lem73660 {A : Type'} (f : type1423 A) (b : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term75 A f PRG a0 a1 b) = (term58 A f b PRG a0 a1).
Proof. exact (eq_refl (term75 A f PRG a0 a1 b)). Qed.
Lemma lem73661 {A : Type'} (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term58 A f b PRG a0 a1.
Proof. exact (EQ_MP (@lem73660 A f b PRG a0 a1) (@lem73659 A b f PRG a0 a1 h1)). Qed.
Lemma lem73662 {A : Type'} (b : A) (n : nat) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term76 A f b PRG a0 a1 n.
Proof. exact (@lem73661 A b f PRG a0 a1 h1 n). Qed.
Lemma lem73663 {A : Type'} (f : type1423 A) (n : nat) (b : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term76 A f b PRG a0 a1 n) = (term57 A f n b PRG a0 a1).
Proof. exact (eq_refl (term76 A f b PRG a0 a1 n)). Qed.
Lemma lem73664 {A : Type'} (n : nat) (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term57 A f n b PRG a0 a1.
Proof. exact (EQ_MP (@lem73663 A f n b PRG a0 a1) (@lem73662 A b n f PRG a0 a1 h1)). Qed.
Lemma lem73665 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term48 A a0 a1 f PRG n b.
Proof. exact (h1). Qed.
Lemma lem73666 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term59 A f PRG a0 a1) (h2 : term48 A a0 a1 f PRG n b) : PRG a0 a1.
Proof. exact (@lem73664 A n b f PRG a0 a1 h1 (@lem73665 A a0 a1 f PRG n b h2)). Qed.
Lemma lem73667 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term77 A f PRG a0 a1.
Proof. exact (fun h0 : term59 A f PRG a0 a1 => @lem73666 A a0 a1 f PRG n b h0 h1). Qed.
Lemma lem73668 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) (h1 : term78 A a0 a1 f PRG b) : term78 A a0 a1 f PRG b.
Proof. exact (h1). Qed.
Lemma lem73669 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) (h1 : term78 A a0 a1 f PRG b) : term77 A f PRG a0 a1.
Proof. exact (ex_elim (@lem73668 A a0 a1 f PRG b h1) (fun n : nat => fun h0 : term79 A a0 a1 f PRG b n => @lem73667 A a0 a1 f PRG n b h0)). Qed.
Lemma lem73670 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term80 A a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73671 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term77 A f PRG a0 a1.
Proof. exact (ex_elim (@lem73670 A a0 a1 f PRG h1) (fun b : A => fun h0 : term81 A a0 a1 f PRG b => @lem73669 A a0 a1 f PRG b h0)). Qed.
Lemma lem73672 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term59 A f PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73673 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term59 A f PRG a0 a1) (h2 : term80 A a0 a1 f PRG) : PRG a0 a1.
Proof. exact (@lem73671 A a0 a1 f PRG h2 (@lem73672 A f PRG a0 a1 h1)). Qed.
Lemma lem73674 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term59 A f PRG a0 a1) : term82 A f PRG a0 a1.
Proof. exact (fun h0 : term80 A a0 a1 f PRG => @lem73673 A a0 a1 f PRG h1 h0). Qed.
Lemma lem73675 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term82 A f PRG a0 a1) : term82 A f PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73676 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term48 A a0 a1 f PRG n b.
Proof. exact (h1). Qed.
Lemma lem73677 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term78 A a0 a1 f PRG b.
Proof. exact (ex_intro (term79 A a0 a1 f PRG b) n (@lem73676 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73678 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term48 A a0 a1 f PRG n b) : term80 A a0 a1 f PRG.
Proof. exact (ex_intro (term81 A a0 a1 f PRG) b (@lem73677 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73679 {A : Type'} (n : nat) (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term48 A a0 a1 f PRG n b) (h2 : term82 A f PRG a0 a1) : PRG a0 a1.
Proof. exact (@lem73675 A f PRG a0 a1 h2 (@lem73678 A a0 a1 f PRG n b h1)). Qed.
Lemma lem73680 {A : Type'} (n : nat) (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term82 A f PRG a0 a1) : term57 A f n b PRG a0 a1.
Proof. exact (fun h0 : term48 A a0 a1 f PRG n b => @lem73679 A n b f PRG a0 a1 h0 h1). Qed.
Lemma lem73681 {A : Type'} (b : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term82 A f PRG a0 a1) : term58 A f b PRG a0 a1.
Proof. exact (fun n : nat => @lem73680 A n b f PRG a0 a1 h1). Qed.
Lemma lem73682 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term82 A f PRG a0 a1) : term59 A f PRG a0 a1.
Proof. exact (fun b : A => @lem73681 A b f PRG a0 a1 h1). Qed.
Lemma lem73683 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term83 A f PRG a0 a1.
Proof. exact (fun h0 : term82 A f PRG a0 a1 => @lem73682 A f PRG a0 a1 h0). Qed.
Lemma lem73684 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term84 A f PRG a0 a1.
Proof. exact (fun h0 : term59 A f PRG a0 a1 => @lem73674 A f PRG a0 a1 h0). Qed.
Lemma lem73685 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : term85 A f PRG a0 a1.
Proof. exact (conj (@lem73684 A f PRG a0 a1) (@lem73683 A f PRG a0 a1)). Qed.
Lemma lem73686 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term85 A f PRG a0 a1) = ((term59 A f PRG a0 a1) = (term82 A f PRG a0 a1)).
Proof. exact (@lem32 (term59 A f PRG a0 a1) (term82 A f PRG a0 a1)). Qed.
Lemma lem73687 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term59 A f PRG a0 a1) = (term82 A f PRG a0 a1).
Proof. exact (EQ_MP (@lem73686 A f PRG a0 a1) (@lem73685 A f PRG a0 a1)). Qed.
Lemma lem73688 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term86 A f PRG a0) = (term87 A f PRG a0).
Proof. exact (fun_ext (fun a1 : A => @lem73687 A f PRG a0 a1)). Qed.
Lemma lem73689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem73690 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term60 A f PRG a0) = (term88 A f PRG a0).
Proof. exact (MK_COMB (@lem73689 A) (@lem73688 A f PRG a0)). Qed.
Lemma lem73691 {A : Type'} (f : type1423 A) (PRG : type1597 A) : (term89 A f PRG) = (term90 A f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem73690 A f PRG a0)). Qed.
Lemma lem73692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem73693 {A : Type'} (f : type1423 A) (PRG : type1597 A) : (term61 A f PRG) = (term91 A f PRG).
Proof. exact (MK_COMB (@lem73692) (@lem73691 A f PRG)). Qed.
Lemma lem73694 {A : Type'} (f : type1423 A) (PRG : type1597 A) : (term50 A PRG f) = (term91 A f PRG).
Proof. exact (TRANS (@lem73657 A f PRG) (@lem73693 A f PRG)). Qed.
Lemma lem73696 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem73697 (x : Prop) : (x = x) = True.
Proof. exact (@lem73696 Prop x). Qed.
Lemma lem73698 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : ((term92 A e f PRG) = (term92 A e f PRG)) = True.
Proof. exact (@lem73697 (term92 A e f PRG)). Qed.
Lemma lem73699 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : True = ((term92 A e f PRG) = (term92 A e f PRG)).
Proof. exact (SYM (@lem73698 A e f PRG)). Qed.
Lemma lem73700 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term92 A e f PRG) = (term92 A e f PRG).
Proof. exact (EQ_MP (@lem73699 A e f PRG) (@lem0)). Qed.
Lemma lem73701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem73702 {A : Type'} (e : A) (PRG : type1597 A) : (term93 A PRG e) = (term94 A e PRG).
Proof. exact (MK_COMB (@lem73701) (@lem73604 A e PRG)). Qed.
Lemma lem73703 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term95 A e PRG f) = (term92 A e f PRG).
Proof. exact (MK_COMB (@lem73702 A e PRG) (@lem73694 A f PRG)). Qed.
Lemma lem73704 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term95 A e PRG f) = (term92 A e f PRG).
Proof. exact (TRANS (@lem73703 A e f PRG) (@lem73700 A e f PRG)). Qed.
Lemma lem73705 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term92 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem73706 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term91 A f PRG.
Proof. exact (proj2 (@lem73705 A e f PRG h1)). Qed.
Lemma lem73707 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term34 A e PRG.
Proof. exact (proj1 (@lem73705 A e f PRG h1)). Qed.
Lemma lem73708 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term96 A e PRG a0.
Proof. exact (@lem73707 A e f PRG h1 a0). Qed.
Lemma lem73709 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) : (term96 A e PRG a0) = (term33 A e PRG a0).
Proof. exact (eq_refl (term96 A e PRG a0)). Qed.
Lemma lem73710 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term33 A e PRG a0.
Proof. exact (EQ_MP (@lem73709 A e PRG a0) (@lem73708 A a0 e f PRG h1)). Qed.
Lemma lem73711 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term97 A e PRG a0 a1.
Proof. exact (@lem73710 A a0 e f PRG h1 a1). Qed.
Lemma lem73712 {A : Type'} (e : A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term97 A e PRG a0 a1) = (term32 A e PRG a0 a1).
Proof. exact (eq_refl (term97 A e PRG a0 a1)). Qed.
Lemma lem73713 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term32 A e PRG a0 a1.
Proof. exact (EQ_MP (@lem73712 A e PRG a0 a1) (@lem73711 A a0 a1 e f PRG h1)). Qed.
Lemma lem73714 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73715 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term92 A e f PRG) (h2 : term31 A a0 a1 e) : PRG a0 a1.
Proof. exact (@lem73713 A a0 a1 e f PRG h1 (@lem73714 A a0 a1 e h2)). Qed.
Lemma lem73716 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term98 A e f PRG a0 a1.
Proof. exact (fun h0 : term92 A e f PRG => @lem73715 A f PRG a0 a1 e h0 h1). Qed.
Lemma lem73717 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term99 A f PRG a0.
Proof. exact (@lem73706 A e f PRG h1 a0). Qed.
Lemma lem73718 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term99 A f PRG a0) = (term88 A f PRG a0).
Proof. exact (eq_refl (term99 A f PRG a0)). Qed.
Lemma lem73719 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term88 A f PRG a0.
Proof. exact (EQ_MP (@lem73718 A f PRG a0) (@lem73717 A a0 e f PRG h1)). Qed.
Lemma lem73720 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term100 A f PRG a0 a1.
Proof. exact (@lem73719 A a0 e f PRG h1 a1). Qed.
Lemma lem73721 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term100 A f PRG a0 a1) = (term82 A f PRG a0 a1).
Proof. exact (eq_refl (term100 A f PRG a0 a1)). Qed.
Lemma lem73722 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term82 A f PRG a0 a1.
Proof. exact (EQ_MP (@lem73721 A f PRG a0 a1) (@lem73720 A a0 a1 e f PRG h1)). Qed.
Lemma lem73723 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term80 A a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73724 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) (h2 : term92 A e f PRG) : PRG a0 a1.
Proof. exact (@lem73722 A a0 a1 e f PRG h2 (@lem73723 A a0 a1 f PRG h1)). Qed.
Lemma lem73725 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term98 A e f PRG a0 a1.
Proof. exact (fun h0 : term92 A e f PRG => @lem73724 A a0 a1 e f PRG h1 h0). Qed.
Lemma lem73726 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term101 A e a0 a1 f PRG) : term101 A e a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73727 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term101 A e a0 a1 f PRG) : term98 A e f PRG a0 a1.
Proof. exact (or_elim (@lem73726 A e a0 a1 f PRG h1) (fun h0 : term31 A a0 a1 e => @lem73716 A f PRG a0 a1 e h0) (fun h0 : term80 A a0 a1 f PRG => @lem73725 A e a0 a1 f PRG h0)). Qed.
Lemma lem73728 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term92 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem73729 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) (h2 : term101 A e a0 a1 f PRG) : PRG a0 a1.
Proof. exact (@lem73727 A e a0 a1 f PRG h2 (@lem73728 A e f PRG h1)). Qed.
Lemma lem73730 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term102 A e f PRG a0 a1.
Proof. exact (fun h0 : term101 A e a0 a1 f PRG => @lem73729 A e a0 a1 f PRG h1 h0). Qed.
Lemma lem73731 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term103 A e f PRG a0.
Proof. exact (fun a1 : A => @lem73730 A a0 a1 e f PRG h1). Qed.
Lemma lem73732 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term92 A e f PRG) : term104 A e f PRG.
Proof. exact (fun a0 : nat => @lem73731 A a0 e f PRG h1). Qed.
Lemma lem73733 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term104 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem73734 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term105 A e f PRG a0.
Proof. exact (@lem73733 A e f PRG h1 a0). Qed.
Lemma lem73735 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term105 A e f PRG a0) = (term103 A e f PRG a0).
Proof. exact (eq_refl (term105 A e f PRG a0)). Qed.
Lemma lem73736 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term103 A e f PRG a0.
Proof. exact (EQ_MP (@lem73735 A e f PRG a0) (@lem73734 A a0 e f PRG h1)). Qed.
Lemma lem73737 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term106 A e f PRG a0 a1.
Proof. exact (@lem73736 A a0 e f PRG h1 a1). Qed.
Lemma lem73738 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term106 A e f PRG a0 a1) = (term102 A e f PRG a0 a1).
Proof. exact (eq_refl (term106 A e f PRG a0 a1)). Qed.
Lemma lem73739 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term102 A e f PRG a0 a1.
Proof. exact (EQ_MP (@lem73738 A e f PRG a0 a1) (@lem73737 A a0 a1 e f PRG h1)). Qed.
Lemma lem73740 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term101 A e a0 a1 f PRG) : term101 A e a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73741 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) (h2 : term101 A e a0 a1 f PRG) : PRG a0 a1.
Proof. exact (@lem73739 A a0 a1 e f PRG h1 (@lem73740 A e a0 a1 f PRG h2)). Qed.
Lemma lem73742 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term101 A e a0 a1 f PRG) : term107 A e f PRG a0 a1.
Proof. exact (fun h0 : term104 A e f PRG => @lem73741 A e a0 a1 f PRG h0 h1). Qed.
Lemma lem73743 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term80 A a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73744 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term101 A e a0 a1 f PRG.
Proof. exact (or_intro2 (term31 A a0 a1 e) (@lem73743 A a0 a1 f PRG h1)). Qed.
Lemma lem73745 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : (term101 A e a0 a1 f PRG) = (term107 A e f PRG a0 a1).
Proof. exact (prop_ext (fun h2 : term101 A e a0 a1 f PRG => @lem73742 A e a0 a1 f PRG h2) (fun h2 : term107 A e f PRG a0 a1 => @lem73744 A e a0 a1 f PRG h1)). Qed.
Lemma lem73746 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term80 A a0 a1 f PRG) : term107 A e f PRG a0 a1.
Proof. exact (EQ_MP (@lem73745 A e a0 a1 f PRG h1) (@lem73744 A e a0 a1 f PRG h1)). Qed.
Lemma lem73747 {A : Type'} (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term31 A a0 a1 e.
Proof. exact (h1). Qed.
Lemma lem73748 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term101 A e a0 a1 f PRG.
Proof. exact (or_intro1 (@lem73747 A a0 a1 e h1) (term80 A a0 a1 f PRG)). Qed.
Lemma lem73749 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : (term101 A e a0 a1 f PRG) = (term107 A e f PRG a0 a1).
Proof. exact (prop_ext (fun h2 : term101 A e a0 a1 f PRG => @lem73742 A e a0 a1 f PRG h2) (fun h2 : term107 A e f PRG a0 a1 => @lem73748 A f PRG a0 a1 e h1)). Qed.
Lemma lem73750 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term31 A a0 a1 e) : term107 A e f PRG a0 a1.
Proof. exact (EQ_MP (@lem73749 A f PRG a0 a1 e h1) (@lem73748 A f PRG a0 a1 e h1)). Qed.
Lemma lem73751 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term104 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem73752 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) (h2 : term80 A a0 a1 f PRG) : PRG a0 a1.
Proof. exact (@lem73746 A e a0 a1 f PRG h2 (@lem73751 A e f PRG h1)). Qed.
Lemma lem73753 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term82 A f PRG a0 a1.
Proof. exact (fun h0 : term80 A a0 a1 f PRG => @lem73752 A e a0 a1 f PRG h1 h0). Qed.
Lemma lem73754 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term88 A f PRG a0.
Proof. exact (fun a1 : A => @lem73753 A a0 a1 e f PRG h1). Qed.
Lemma lem73755 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term91 A f PRG.
Proof. exact (fun a0 : nat => @lem73754 A a0 e f PRG h1). Qed.
Lemma lem73756 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term104 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem73757 {A : Type'} (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (e : A) (h1 : term104 A e f PRG) (h2 : term31 A a0 a1 e) : PRG a0 a1.
Proof. exact (@lem73750 A f PRG a0 a1 e h2 (@lem73756 A e f PRG h1)). Qed.
Lemma lem73758 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term32 A e PRG a0 a1.
Proof. exact (fun h0 : term31 A a0 a1 e => @lem73757 A f PRG a0 a1 e h1 h0). Qed.
Lemma lem73759 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term33 A e PRG a0.
Proof. exact (fun a1 : A => @lem73758 A a0 a1 e f PRG h1). Qed.
Lemma lem73760 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term34 A e PRG.
Proof. exact (fun a0 : nat => @lem73759 A a0 e f PRG h1). Qed.
Lemma lem73761 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term104 A e f PRG) : term92 A e f PRG.
Proof. exact (conj (@lem73760 A e f PRG h1) (@lem73755 A e f PRG h1)). Qed.
Lemma lem73762 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term108 A e f PRG.
Proof. exact (fun h0 : term104 A e f PRG => @lem73761 A e f PRG h0). Qed.
Lemma lem73763 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term109 A e f PRG.
Proof. exact (fun h0 : term92 A e f PRG => @lem73732 A e f PRG h0). Qed.
Lemma lem73764 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term110 A e f PRG.
Proof. exact (conj (@lem73763 A e f PRG) (@lem73762 A e f PRG)). Qed.
Lemma lem73765 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term110 A e f PRG) = ((term92 A e f PRG) = (term104 A e f PRG)).
Proof. exact (@lem32 (term92 A e f PRG) (term104 A e f PRG)). Qed.
Lemma lem73766 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term92 A e f PRG) = (term104 A e f PRG).
Proof. exact (EQ_MP (@lem73765 A e f PRG) (@lem73764 A e f PRG)). Qed.
Lemma lem73767 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term95 A e PRG f) = (term104 A e f PRG).
Proof. exact (TRANS (@lem73704 A e f PRG) (@lem73766 A e f PRG)). Qed.
Lemma lem73768 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) : (term104 A e f PRG) = (term95 A e PRG f).
Proof. exact (SYM (@lem73767 A e f PRG)). Qed.
Lemma lem73769 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : PRG = (term111 A e f).
Proof. exact (h1). Qed.
Lemma lem73770 (a0 : nat) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem73771 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0) = (term112 A e f a0).
Proof. exact (MK_COMB (@lem73769 A PRG e f h1) (@lem73770 a0)). Qed.
Lemma lem73772 {A : Type'} (e : A) (f : type1423 A) (a0 : nat) : (term112 A e f a0) = (term113 A e f a0).
Proof. exact (eq_refl (term112 A e f a0)). Qed.
Lemma lem73773 {A : Type'} (PRG : type1597 A) (a0 : nat) : (term114 A PRG a0) = (term114 A PRG a0).
Proof. exact (eq_refl (term114 A PRG a0)). Qed.
Lemma lem73774 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) : ((PRG a0) = (term112 A e f a0)) = ((PRG a0) = (term113 A e f a0)).
Proof. exact (MK_COMB (@lem73773 A PRG a0) (@lem73772 A e f a0)). Qed.
Lemma lem73775 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0) = (term113 A e f a0).
Proof. exact (EQ_MP (@lem73774 A PRG e f a0) (@lem73771 A a0 PRG e f h1)). Qed.
Lemma lem73776 {A : Type'} (a1 : A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem73777 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0 a1) = (term115 A e f a0 a1).
Proof. exact (MK_COMB (@lem73775 A a0 PRG e f h1) (@lem73776 A a1)). Qed.
Lemma lem73778 {A : Type'} (e : A) (f : type1423 A) (a0 : nat) (a1 : A) : (term115 A e f a0 a1) = (term116 A e f a0 a1).
Proof. exact (eq_refl (term115 A e f a0 a1)). Qed.
Lemma lem73779 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) : (term117 A PRG a0 a1) = (term117 A PRG a0 a1).
Proof. exact (eq_refl (term117 A PRG a0 a1)). Qed.
Lemma lem73780 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) (a1 : A) : ((PRG a0 a1) = (term115 A e f a0 a1)) = ((PRG a0 a1) = (term116 A e f a0 a1)).
Proof. exact (MK_COMB (@lem73779 A PRG a0 a1) (@lem73778 A e f a0 a1)). Qed.
Lemma lem73781 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0 a1) = (term116 A e f a0 a1).
Proof. exact (EQ_MP (@lem73780 A PRG e f a0 a1) (@lem73777 A a0 a1 PRG e f h1)). Qed.
Lemma lem73782 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term118 A PRG e f a0.
Proof. exact (fun a1 : A => @lem73781 A a0 a1 PRG e f h1). Qed.
Lemma lem73783 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term119 A PRG e f.
Proof. exact (fun a0 : nat => @lem73782 A a0 PRG e f h1). Qed.
Lemma lem73784 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term120 A PRG e f a0.
Proof. exact (@lem73783 A PRG e f h1 a0). Qed.
Lemma lem73785 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) : (term120 A PRG e f a0) = (term118 A PRG e f a0).
Proof. exact (eq_refl (term120 A PRG e f a0)). Qed.
Lemma lem73786 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term118 A PRG e f a0.
Proof. exact (EQ_MP (@lem73785 A PRG e f a0) (@lem73784 A a0 PRG e f h1)). Qed.
Lemma lem73787 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term121 A PRG e f a0 a1.
Proof. exact (@lem73786 A a0 PRG e f h1 a1). Qed.
Lemma lem73788 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) (a1 : A) : (term121 A PRG e f a0 a1) = ((PRG a0 a1) = (term116 A e f a0 a1)).
Proof. exact (eq_refl (term121 A PRG e f a0 a1)). Qed.
Lemma lem73789 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0 a1) = (term116 A e f a0 a1).
Proof. exact (EQ_MP (@lem73788 A PRG e f a0 a1) (@lem73787 A a0 a1 PRG e f h1)). Qed.
Lemma lem73792 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) (a1 : A) : term122 A PRG e f a0 a1.
Proof. exact (@lem37 (PRG a0 a1) (term116 A e f a0 a1)). Qed.
Lemma lem73793 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term123 A PRG e f a0 a1.
Proof. exact (@lem73792 A PRG e f a0 a1 (@lem73789 A a0 a1 PRG e f h1)). Qed.
Lemma lem73794 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : PRG a0 a1) : PRG a0 a1.
Proof. exact (h1). Qed.
Lemma lem73795 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : PRG = (term111 A e f)) (h2 : PRG a0 a1) : term116 A e f a0 a1.
Proof. exact (@lem73793 A a0 a1 PRG e f h1 (@lem73794 A PRG a0 a1 h2)). Qed.
Lemma lem73796 {A : Type'} (PRG' : type1597 A) (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : PRG = (term111 A e f)) (h2 : PRG a0 a1) : term124 A e f a0 a1 PRG'.
Proof. exact (@lem73795 A e f PRG a0 a1 h1 h2 PRG'). Qed.
Lemma lem73797 {A : Type'} (e : A) (f : type1423 A) (PRG' : type1597 A) (a0 : nat) (a1 : A) : (term124 A e f a0 a1 PRG') = (term107 A e f PRG' a0 a1).
Proof. exact (eq_refl (term124 A e f a0 a1 PRG')). Qed.
Lemma lem73798 {A : Type'} (PRG' : type1597 A) (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : PRG = (term111 A e f)) (h2 : PRG a0 a1) : term107 A e f PRG' a0 a1.
Proof. exact (EQ_MP (@lem73797 A e f PRG' a0 a1) (@lem73796 A PRG' e f PRG a0 a1 h1 h2)). Qed.
Lemma lem73799 {A : Type'} (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term104 A e f PRG'.
Proof. exact (h1). Qed.
Lemma lem73800 {A : Type'} (PRG' : type1597 A) (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : term104 A e f PRG') (h2 : PRG = (term111 A e f)) (h3 : PRG a0 a1) : PRG' a0 a1.
Proof. exact (@lem73798 A PRG' e f PRG a0 a1 h2 h3 (@lem73799 A e f PRG' h1)). Qed.
Lemma lem73801 {A : Type'} (a0 : nat) (a1 : A) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term104 A e f PRG') (h2 : PRG = (term111 A e f)) : term125 A PRG PRG' a0 a1.
Proof. exact (fun h0 : PRG a0 a1 => @lem73800 A PRG' e f PRG a0 a1 h1 h2 h0). Qed.
Lemma lem73802 {A : Type'} (a0 : nat) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term104 A e f PRG') (h2 : PRG = (term111 A e f)) : term126 A PRG PRG' a0.
Proof. exact (fun a1 : A => @lem73801 A a0 a1 PRG' PRG e f h1 h2). Qed.
Lemma lem73803 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term104 A e f PRG') (h2 : PRG = (term111 A e f)) : term127 A PRG PRG'.
Proof. exact (fun a0 : nat => @lem73802 A a0 PRG' PRG e f h1 h2). Qed.
Lemma lem73804 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term128 A e f PRG PRG'.
Proof. exact (fun h0 : term104 A e f PRG' => @lem73803 A PRG' PRG e f h0 h1). Qed.
Lemma lem73805 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term129 A e f PRG.
Proof. exact (fun PRG' : type1597 A => @lem73804 A PRG' PRG e f h1). Qed.
Lemma lem73806 {A : Type'} (e : A) (f : type1423 A) (h1 : term130 A e f) : term130 A e f.
Proof. exact (h1). Qed.
Lemma lem73807 {A : Type'} (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term104 A e f PRG'.
Proof. exact (h1). Qed.
Lemma lem73808 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term131 A e f PRG PRG'.
Proof. exact (@lem73805 A PRG e f h1 PRG'). Qed.
Lemma lem73809 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) : (term131 A e f PRG PRG') = (term128 A e f PRG PRG').
Proof. exact (eq_refl (term131 A e f PRG PRG')). Qed.
Lemma lem73810 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term128 A e f PRG PRG'.
Proof. exact (EQ_MP (@lem73809 A e f PRG PRG') (@lem73808 A PRG' PRG e f h1)). Qed.
Lemma lem73811 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term104 A e f PRG') (h2 : PRG = (term111 A e f)) : term127 A PRG PRG'.
Proof. exact (@lem73810 A PRG' PRG e f h2 (@lem73807 A e f PRG' h1)). Qed.
Lemma lem73812 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term132 A e f PRG.
Proof. exact (@lem73806 A e f h1 PRG). Qed.
Lemma lem73813 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) : (term132 A e f PRG) = (term133 A PRG e f).
Proof. exact (eq_refl (term132 A e f PRG)). Qed.
Lemma lem73814 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term133 A PRG e f.
Proof. exact (EQ_MP (@lem73813 A PRG e f) (@lem73812 A PRG e f h1)). Qed.
Lemma lem73815 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term134 A PRG e f PRG'.
Proof. exact (@lem73814 A PRG e f h1 PRG'). Qed.
Lemma lem73816 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (PRG' : type1597 A) : (term134 A PRG e f PRG') = (term135 A PRG e f PRG').
Proof. exact (eq_refl (term134 A PRG e f PRG')). Qed.
Lemma lem73817 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term135 A PRG e f PRG'.
Proof. exact (EQ_MP (@lem73816 A PRG e f PRG') (@lem73815 A PRG PRG' e f h1)). Qed.
Lemma lem73818 {A : Type'} (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term136 A PRG e f PRG'.
Proof. exact (@lem73817 A PRG PRG' e f h1 (@lem73811 A PRG' PRG e f h2 h3)). Qed.
Lemma lem73819 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term105 A e f PRG' a0.
Proof. exact (@lem73807 A e f PRG' h1 a0). Qed.
Lemma lem73820 {A : Type'} (e : A) (f : type1423 A) (PRG' : type1597 A) (a0 : nat) : (term105 A e f PRG' a0) = (term103 A e f PRG' a0).
Proof. exact (eq_refl (term105 A e f PRG' a0)). Qed.
Lemma lem73821 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term103 A e f PRG' a0.
Proof. exact (EQ_MP (@lem73820 A e f PRG' a0) (@lem73819 A a0 e f PRG' h1)). Qed.
Lemma lem73822 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term106 A e f PRG' a0 a1.
Proof. exact (@lem73821 A a0 e f PRG' h1 a1). Qed.
Lemma lem73823 {A : Type'} (e : A) (f : type1423 A) (PRG' : type1597 A) (a0 : nat) (a1 : A) : (term106 A e f PRG' a0 a1) = (term102 A e f PRG' a0 a1).
Proof. exact (eq_refl (term106 A e f PRG' a0 a1)). Qed.
Lemma lem73824 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG' : type1597 A) (h1 : term104 A e f PRG') : term102 A e f PRG' a0 a1.
Proof. exact (EQ_MP (@lem73823 A e f PRG' a0 a1) (@lem73822 A a0 a1 e f PRG' h1)). Qed.
Lemma lem73825 {A : Type'} (a0 : nat) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term137 A PRG e f PRG' a0.
Proof. exact (@lem73818 A PRG' PRG e f h1 h2 h3 a0). Qed.
Lemma lem73826 {A : Type'} (PRG : type1597 A) (e : A) (a0 : nat) (f : type1423 A) (PRG' : type1597 A) : (term137 A PRG e f PRG' a0) = (term138 A PRG e a0 f PRG').
Proof. exact (eq_refl (term137 A PRG e f PRG' a0)). Qed.
Lemma lem73827 {A : Type'} (a0 : nat) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term138 A PRG e a0 f PRG'.
Proof. exact (EQ_MP (@lem73826 A PRG e a0 f PRG') (@lem73825 A a0 PRG' PRG e f h1 h2 h3)). Qed.
Lemma lem73828 {A : Type'} (a0 : nat) (a1 : A) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term139 A PRG e a0 f PRG' a1.
Proof. exact (@lem73827 A a0 PRG' PRG e f h1 h2 h3 a1). Qed.
Lemma lem73829 {A : Type'} (PRG : type1597 A) (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term139 A PRG e a0 f PRG' a1) = (term140 A PRG e a0 a1 f PRG').
Proof. exact (eq_refl (term139 A PRG e a0 f PRG' a1)). Qed.
Lemma lem73830 {A : Type'} (a0 : nat) (a1 : A) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term140 A PRG e a0 a1 f PRG'.
Proof. exact (EQ_MP (@lem73829 A PRG e a0 a1 f PRG') (@lem73828 A a0 a1 PRG' PRG e f h1 h2 h3)). Qed.
Lemma lem73831 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (a0 : nat) (a1 : A) : term141 A e f PRG PRG' a0 a1.
Proof. exact (@lem51 (term101 A e a0 a1 f PRG') (term101 A e a0 a1 f PRG) (PRG' a0 a1)). Qed.
Lemma lem73832 {A : Type'} (a0 : nat) (a1 : A) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term142 A e f PRG PRG' a0 a1.
Proof. exact (@lem73831 A e f PRG PRG' a0 a1 (@lem73830 A a0 a1 PRG' PRG e f h1 h2 h3)). Qed.
Lemma lem73833 {A : Type'} (a0 : nat) (a1 : A) (PRG' : type1597 A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) : term143 A e f PRG PRG' a0 a1.
Proof. exact (@lem73832 A a0 a1 PRG' PRG e f h1 h2 h3 (@lem73824 A a0 a1 e f PRG' h2)). Qed.
Lemma lem73834 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term101 A e a0 a1 f PRG) : term101 A e a0 a1 f PRG.
Proof. exact (h1). Qed.
Lemma lem73835 {A : Type'} (PRG' : type1597 A) (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term130 A e f) (h2 : term104 A e f PRG') (h3 : PRG = (term111 A e f)) (h4 : term101 A e a0 a1 f PRG) : PRG' a0 a1.
Proof. exact (@lem73833 A a0 a1 PRG' PRG e f h1 h2 h3 (@lem73834 A e a0 a1 f PRG h4)). Qed.
Lemma lem73836 {A : Type'} (PRG' : type1597 A) (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) (h3 : term101 A e a0 a1 f PRG) : term107 A e f PRG' a0 a1.
Proof. exact (fun h0 : term104 A e f PRG' => @lem73835 A PRG' e a0 a1 f PRG h1 h0 h2 h3). Qed.
Lemma lem73837 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) (h3 : term101 A e a0 a1 f PRG) : term116 A e f a0 a1.
Proof. exact (fun PRG' : type1597 A => @lem73836 A PRG' e a0 a1 f PRG h1 h2 h3). Qed.
Lemma lem73838 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term120 A PRG e f a0.
Proof. exact (@lem73783 A PRG e f h1 a0). Qed.
Lemma lem73839 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) : (term120 A PRG e f a0) = (term118 A PRG e f a0).
Proof. exact (eq_refl (term120 A PRG e f a0)). Qed.
Lemma lem73840 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term118 A PRG e f a0.
Proof. exact (EQ_MP (@lem73839 A PRG e f a0) (@lem73838 A a0 PRG e f h1)). Qed.
Lemma lem73841 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term121 A PRG e f a0 a1.
Proof. exact (@lem73840 A a0 PRG e f h1 a1). Qed.
Lemma lem73842 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (a0 : nat) (a1 : A) : (term121 A PRG e f a0 a1) = ((PRG a0 a1) = (term116 A e f a0 a1)).
Proof. exact (eq_refl (term121 A PRG e f a0 a1)). Qed.
Lemma lem73843 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (PRG a0 a1) = (term116 A e f a0 a1).
Proof. exact (EQ_MP (@lem73842 A PRG e f a0 a1) (@lem73841 A a0 a1 PRG e f h1)). Qed.
Lemma lem73844 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (term116 A e f a0 a1) = (PRG a0 a1).
Proof. exact (SYM (@lem73843 A a0 a1 PRG e f h1)). Qed.
Lemma lem73845 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) (h3 : term101 A e a0 a1 f PRG) : PRG a0 a1.
Proof. exact (EQ_MP (@lem73844 A a0 a1 PRG e f h2) (@lem73837 A e a0 a1 f PRG h1 h2 h3)). Qed.
Lemma lem73846 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term102 A e f PRG a0 a1.
Proof. exact (fun h0 : term101 A e a0 a1 f PRG => @lem73845 A e a0 a1 f PRG h1 h2 h0). Qed.
Lemma lem73847 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term103 A e f PRG a0.
Proof. exact (fun a1 : A => @lem73846 A a0 a1 PRG e f h1 h2). Qed.
Lemma lem73848 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term104 A e f PRG.
Proof. exact (fun a0 : nat => @lem73847 A a0 PRG e f h1 h2). Qed.
Lemma lem73851 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term144 A e f PRG a0) = (term144 A e f PRG a0).
Proof. exact (eq_refl (term144 A e f PRG a0)). Qed.
Lemma lem73852 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term144 A e f PRG a0) = (term145 A e a0 f PRG).
Proof. exact (eq_refl (term144 A e f PRG a0)). Qed.
Lemma lem73853 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term146 A e f PRG a0) = (term146 A e f PRG a0).
Proof. exact (eq_refl (term146 A e f PRG a0)). Qed.
Lemma lem73854 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : ((term144 A e f PRG a0) = (term144 A e f PRG a0)) = ((term144 A e f PRG a0) = (term145 A e a0 f PRG)).
Proof. exact (MK_COMB (@lem73853 A e f PRG a0) (@lem73852 A e a0 f PRG)). Qed.
Lemma lem73855 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term144 A e f PRG a0) = (term145 A e a0 f PRG).
Proof. exact (EQ_MP (@lem73854 A e a0 f PRG) (@lem73851 A e f PRG a0)). Qed.
Lemma lem73856 {A : Type'} (a1 : A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem73857 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) (a1 : A) : (term147 A e f PRG a0 a1) = (term148 A e a0 f PRG a1).
Proof. exact (MK_COMB (@lem73855 A e a0 f PRG) (@lem73856 A a1)). Qed.
Lemma lem73858 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term148 A e a0 f PRG a1) = (term101 A e a0 a1 f PRG).
Proof. exact (eq_refl (term148 A e a0 f PRG a1)). Qed.
Lemma lem73859 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term149 A e f PRG a0 a1) = (term149 A e f PRG a0 a1).
Proof. exact (eq_refl (term149 A e f PRG a0 a1)). Qed.
Lemma lem73860 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : ((term147 A e f PRG a0 a1) = (term148 A e a0 f PRG a1)) = ((term147 A e f PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (MK_COMB (@lem73859 A e f PRG a0 a1) (@lem73858 A e a0 a1 f PRG)). Qed.
Lemma lem73861 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term147 A e f PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (EQ_MP (@lem73860 A e a0 a1 f PRG) (@lem73857 A e a0 f PRG a1)). Qed.
Lemma lem73862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73863 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term150 A e f PRG a0 a1) = (term151 A e a0 a1 f PRG).
Proof. exact (MK_COMB (@lem73862) (@lem73861 A e a0 a1 f PRG)). Qed.
Lemma lem73864 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) : (PRG a0 a1) = (PRG a0 a1).
Proof. exact (eq_refl (PRG a0 a1)). Qed.
Lemma lem73865 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term152 A e f PRG a0 a1) = (term102 A e f PRG a0 a1).
Proof. exact (MK_COMB (@lem73863 A e a0 a1 f PRG) (@lem73864 A PRG a0 a1)). Qed.
Lemma lem73866 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) : (term153 A a0 a1 e f PRG) = (term153 A a0 a1 e f PRG).
Proof. exact (eq_refl (term153 A a0 a1 e f PRG)). Qed.
Lemma lem73867 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term154 A e f PRG a0 a1) = (term155 A e a0 a1 f PRG).
Proof. exact (MK_COMB (@lem73866 A a0 a1 e f PRG) (@lem73861 A e a0 a1 f PRG)). Qed.
Lemma lem73868 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) : (term156 A PRG a0 a1) = (term156 A PRG a0 a1).
Proof. exact (eq_refl (term156 A PRG a0 a1)). Qed.
Lemma lem73869 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term157 A e f PRG a0 a1) = (term158 A e a0 a1 f PRG).
Proof. exact (MK_COMB (@lem73868 A PRG a0 a1) (@lem73861 A e a0 a1 f PRG)). Qed.
Lemma lem73870 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term159 A e f PRG a0) = (term160 A e a0 f PRG).
Proof. exact (fun_ext (fun a1 : A => @lem73869 A e a0 a1 f PRG)). Qed.
Lemma lem73871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem73872 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term161 A e f PRG a0) = (term162 A e a0 f PRG).
Proof. exact (MK_COMB (@lem73871 A) (@lem73870 A e a0 f PRG)). Qed.
Lemma lem73873 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term163 A e f PRG) = (term164 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem73872 A e a0 f PRG)). Qed.
Lemma lem73874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem73875 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term165 A e f PRG) = (term166 A e f PRG).
Proof. exact (MK_COMB (@lem73874) (@lem73873 A e f PRG)). Qed.
Lemma lem73876 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term167 A e f PRG a0) = (term168 A e a0 f PRG).
Proof. exact (fun_ext (fun a1 : A => @lem73867 A e a0 a1 f PRG)). Qed.
Lemma lem73877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem73878 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term169 A e f PRG a0) = (term170 A e a0 f PRG).
Proof. exact (MK_COMB (@lem73877 A) (@lem73876 A e a0 f PRG)). Qed.
Lemma lem73879 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term171 A e f PRG) = (term172 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem73878 A e a0 f PRG)). Qed.
Lemma lem73880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem73881 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term173 A e f PRG) = (term174 A e f PRG).
Proof. exact (MK_COMB (@lem73880) (@lem73879 A e f PRG)). Qed.
Lemma lem73882 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term175 A e f PRG a0) = (term176 A e f PRG a0).
Proof. exact (fun_ext (fun a1 : A => @lem73865 A e f PRG a0 a1)). Qed.
Lemma lem73883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem73884 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term177 A e f PRG a0) = (term103 A e f PRG a0).
Proof. exact (MK_COMB (@lem73883 A) (@lem73882 A e f PRG a0)). Qed.
Lemma lem73885 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term178 A e f PRG) = (term179 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem73884 A e f PRG a0)). Qed.
Lemma lem73886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem73887 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term180 A e f PRG) = (term104 A e f PRG).
Proof. exact (MK_COMB (@lem73886) (@lem73885 A e f PRG)). Qed.
Lemma lem73888 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term104 A e f PRG) = (term180 A e f PRG).
Proof. exact (SYM (@lem73887 A e f PRG)). Qed.
Lemma lem73889 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term180 A e f PRG.
Proof. exact (EQ_MP (@lem73888 A e f PRG) (@lem73848 A PRG e f h1 h2)). Qed.
Lemma lem73890 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term181 A e f PRG.
Proof. exact (@lem73806 A e f h1 (term182 A e f PRG)). Qed.
Lemma lem73891 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) : (term181 A e f PRG) = (term183 A PRG e f).
Proof. exact (eq_refl (term181 A e f PRG)). Qed.
Lemma lem73892 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term183 A PRG e f.
Proof. exact (EQ_MP (@lem73891 A PRG e f) (@lem73890 A PRG e f h1)). Qed.
Lemma lem73893 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term184 A e f PRG.
Proof. exact (@lem73892 A PRG e f h1 PRG). Qed.
Lemma lem73894 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term184 A e f PRG) = (term185 A e f PRG).
Proof. exact (eq_refl (term184 A e f PRG)). Qed.
Lemma lem73895 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) : term185 A e f PRG.
Proof. exact (EQ_MP (@lem73894 A e f PRG) (@lem73893 A PRG e f h1)). Qed.
Lemma lem73896 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term174 A e f PRG.
Proof. exact (@lem73895 A PRG e f h1 (@lem73889 A PRG e f h1 h2)). Qed.
Lemma lem73897 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term174 A e f PRG) = (term173 A e f PRG).
Proof. exact (SYM (@lem73881 A e f PRG)). Qed.
Lemma lem73898 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term173 A e f PRG.
Proof. exact (EQ_MP (@lem73897 A e f PRG) (@lem73896 A PRG e f h1 h2)). Qed.
Lemma lem73899 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term186 A e f PRG.
Proof. exact (@lem73805 A PRG e f h1 (term182 A e f PRG)). Qed.
Lemma lem73900 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term186 A e f PRG) = (term187 A e f PRG).
Proof. exact (eq_refl (term186 A e f PRG)). Qed.
Lemma lem73901 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term187 A e f PRG.
Proof. exact (EQ_MP (@lem73900 A e f PRG) (@lem73899 A PRG e f h1)). Qed.
Lemma lem73902 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term165 A e f PRG.
Proof. exact (@lem73901 A PRG e f h2 (@lem73898 A PRG e f h1 h2)). Qed.
Lemma lem73903 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term166 A e f PRG.
Proof. exact (EQ_MP (@lem73875 A e f PRG) (@lem73902 A PRG e f h1 h2)). Qed.
Lemma lem73904 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term105 A e f PRG a0.
Proof. exact (@lem73848 A PRG e f h1 h2 a0). Qed.
Lemma lem73905 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term105 A e f PRG a0) = (term103 A e f PRG a0).
Proof. exact (eq_refl (term105 A e f PRG a0)). Qed.
Lemma lem73906 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term103 A e f PRG a0.
Proof. exact (EQ_MP (@lem73905 A e f PRG a0) (@lem73904 A a0 PRG e f h1 h2)). Qed.
Lemma lem73907 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term106 A e f PRG a0 a1.
Proof. exact (@lem73906 A a0 PRG e f h1 h2 a1). Qed.
Lemma lem73908 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : (term106 A e f PRG a0 a1) = (term102 A e f PRG a0 a1).
Proof. exact (eq_refl (term106 A e f PRG a0 a1)). Qed.
Lemma lem73909 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term102 A e f PRG a0 a1.
Proof. exact (EQ_MP (@lem73908 A e f PRG a0 a1) (@lem73907 A a0 a1 PRG e f h1 h2)). Qed.
Lemma lem73910 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term188 A e f PRG a0.
Proof. exact (@lem73903 A PRG e f h1 h2 a0). Qed.
Lemma lem73911 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term188 A e f PRG a0) = (term162 A e a0 f PRG).
Proof. exact (eq_refl (term188 A e f PRG a0)). Qed.
Lemma lem73912 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term162 A e a0 f PRG.
Proof. exact (EQ_MP (@lem73911 A e a0 f PRG) (@lem73910 A a0 PRG e f h1 h2)). Qed.
Lemma lem73913 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term189 A e a0 f PRG a1.
Proof. exact (@lem73912 A a0 PRG e f h1 h2 a1). Qed.
Lemma lem73914 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term189 A e a0 f PRG a1) = (term158 A e a0 a1 f PRG).
Proof. exact (eq_refl (term189 A e a0 f PRG a1)). Qed.
Lemma lem73915 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term158 A e a0 a1 f PRG.
Proof. exact (EQ_MP (@lem73914 A e a0 a1 f PRG) (@lem73913 A a0 a1 PRG e f h1 h2)). Qed.
Lemma lem73916 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term190 A e f PRG a0 a1.
Proof. exact (conj (@lem73915 A a0 a1 PRG e f h1 h2) (@lem73909 A a0 a1 PRG e f h1 h2)). Qed.
Lemma lem73917 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term190 A e f PRG a0 a1) = ((PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (@lem32 (PRG a0 a1) (term101 A e a0 a1 f PRG)). Qed.
Lemma lem73918 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (EQ_MP (@lem73917 A e a0 a1 f PRG) (@lem73916 A a0 a1 PRG e f h1 h2)). Qed.
Lemma lem73919 {A : Type'} (a0 : nat) (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term191 A e a0 f PRG.
Proof. exact (fun a1 : A => @lem73918 A a0 a1 PRG e f h1 h2). Qed.
Lemma lem73924 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term104 A e f PRG.
Proof. exact (fun a0 : nat => @lem73847 A a0 PRG e f h1 h2). Qed.
Lemma lem73925 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term192 A e f PRG.
Proof. exact (fun a0 : nat => @lem73919 A a0 PRG e f h1 h2). Qed.
Lemma lem73926 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term129 A e f PRG.
Proof. exact (fun PRG' : type1597 A => @lem73804 A PRG' PRG e f h2). Qed.
Lemma lem73927 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term95 A e PRG f.
Proof. exact (EQ_MP (@lem73768 A e PRG f) (@lem73924 A PRG e f h1 h2)). Qed.
Lemma lem73941 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) : (term104 A e f PRG) = (term95 A e PRG f).
Proof. exact (SYM (@lem73767 A e f PRG)). Qed.
Lemma lem73942 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) : (term104 A e f PRG) = (term95 A e PRG f).
Proof. exact (@lem73941 A e PRG f). Qed.
Lemma lem73943 {A : Type'} (e : A) (PRG' : type1597 A) (f : type1423 A) : (term104 A e f PRG') = (term95 A e PRG' f).
Proof. exact (@lem73942 A e PRG' f). Qed.
Lemma lem73944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem73945 {A : Type'} (e : A) (PRG' : type1597 A) (f : type1423 A) : (term193 A e f PRG') = (term194 A e PRG' f).
Proof. exact (MK_COMB (@lem73944) (@lem73943 A e PRG' f)). Qed.
Lemma lem73984 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) : (term127 A PRG PRG') = (term127 A PRG PRG').
Proof. exact (eq_refl (term127 A PRG PRG')). Qed.
Lemma lem73985 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) : (term128 A e f PRG PRG') = (term195 A e f PRG PRG').
Proof. exact (MK_COMB (@lem73945 A e PRG' f) (@lem73984 A PRG PRG')). Qed.
Lemma lem73986 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term196 A e f PRG) = (term197 A e f PRG).
Proof. exact (fun_ext (fun PRG' : type1597 A => @lem73985 A e f PRG PRG')). Qed.
Lemma lem73987 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem73988 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term129 A e f PRG) = (term198 A e f PRG).
Proof. exact (MK_COMB (@lem73987 A) (@lem73986 A e f PRG)). Qed.
Lemma lem73989 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term198 A e f PRG.
Proof. exact (EQ_MP (@lem73988 A e f PRG) (@lem73926 A PRG e f h1 h2)). Qed.
Lemma lem73990 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term199 A e f PRG.
Proof. exact (conj (@lem73989 A PRG e f h1 h2) (@lem73925 A PRG e f h1 h2)). Qed.
Lemma lem73991 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : term130 A e f) (h2 : PRG = (term111 A e f)) : term200 A e f PRG.
Proof. exact (conj (@lem73927 A PRG e f h1 h2) (@lem73990 A PRG e f h1 h2)). Qed.
Lemma lem73992 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term127 A PRG PRG'.
Proof. exact (h1). Qed.
Lemma lem73994 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term201 A C B D.
Proof. exact (fun h0 : term202 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem73996 {A : Type'} (a0 : nat) (a1 : A) (e : A) : term203 A a0 a1 e.
Proof. exact (@lem9120 (term31 A a0 a1 e)). Qed.
Lemma lem73997 {A : Type'} (a0 : nat) (a1 : A) (e : A) : (term203 A a0 a1 e) = (term204 A a0 a1 e).
Proof. exact (eq_refl (term203 A a0 a1 e)). Qed.
Lemma lem73998 {A : Type'} (a0 : nat) (a1 : A) (e : A) : term204 A a0 a1 e.
Proof. exact (EQ_MP (@lem73997 A a0 a1 e) (@lem73996 A a0 a1 e)). Qed.
Lemma lem74000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term205 A P Q.
Proof. exact (fun h0 : term206 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem74001 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term205 A P Q.
Proof. exact (@lem74000 A P Q). Qed.
Lemma lem74002 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : term207 A PRG a0 a1 f PRG'.
Proof. exact (@lem74001 A (term81 A a0 a1 f PRG) (term81 A a0 a1 f PRG')). Qed.
Lemma lem74003 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term208 A a0 a1 f PRG b) = (term78 A a0 a1 f PRG b).
Proof. exact (eq_refl (term208 A a0 a1 f PRG b)). Qed.
Lemma lem74004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74005 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term209 A a0 a1 f PRG b) = (term210 A a0 a1 f PRG b).
Proof. exact (MK_COMB (@lem74004) (@lem74003 A a0 a1 f PRG b)). Qed.
Lemma lem74006 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term208 A a0 a1 f PRG' b) = (term78 A a0 a1 f PRG' b).
Proof. exact (eq_refl (term208 A a0 a1 f PRG' b)). Qed.
Lemma lem74007 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term211 A PRG a0 a1 f PRG' b) = (term212 A PRG a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74005 A a0 a1 f PRG b) (@lem74006 A a0 a1 f PRG' b)). Qed.
Lemma lem74008 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term213 A PRG a0 a1 f PRG') = (term214 A PRG a0 a1 f PRG').
Proof. exact (fun_ext (fun b : A => @lem74007 A PRG a0 a1 f PRG' b)). Qed.
Lemma lem74009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74010 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term215 A PRG a0 a1 f PRG') = (term216 A PRG a0 a1 f PRG').
Proof. exact (MK_COMB (@lem74009 A) (@lem74008 A PRG a0 a1 f PRG')). Qed.
Lemma lem74011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74012 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term217 A PRG a0 a1 f PRG') = (term218 A PRG a0 a1 f PRG').
Proof. exact (MK_COMB (@lem74011) (@lem74010 A PRG a0 a1 f PRG')). Qed.
Lemma lem74013 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term208 A a0 a1 f PRG b) = (term78 A a0 a1 f PRG b).
Proof. exact (eq_refl (term208 A a0 a1 f PRG b)). Qed.
Lemma lem74014 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term219 A a0 a1 f PRG) = (term81 A a0 a1 f PRG).
Proof. exact (fun_ext (fun b : A => @lem74013 A a0 a1 f PRG b)). Qed.
Lemma lem74015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74016 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term220 A a0 a1 f PRG) = (term80 A a0 a1 f PRG).
Proof. exact (MK_COMB (@lem74015 A) (@lem74014 A a0 a1 f PRG)). Qed.
Lemma lem74017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74018 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term221 A a0 a1 f PRG) = (term222 A a0 a1 f PRG).
Proof. exact (MK_COMB (@lem74017) (@lem74016 A a0 a1 f PRG)). Qed.
Lemma lem74019 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term208 A a0 a1 f PRG' b) = (term78 A a0 a1 f PRG' b).
Proof. exact (eq_refl (term208 A a0 a1 f PRG' b)). Qed.
Lemma lem74020 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term219 A a0 a1 f PRG') = (term81 A a0 a1 f PRG').
Proof. exact (fun_ext (fun b : A => @lem74019 A a0 a1 f PRG' b)). Qed.
Lemma lem74021 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74022 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term220 A a0 a1 f PRG') = (term80 A a0 a1 f PRG').
Proof. exact (MK_COMB (@lem74021 A) (@lem74020 A a0 a1 f PRG')). Qed.
Lemma lem74023 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term223 A PRG a0 a1 f PRG') = (term224 A PRG a0 a1 f PRG').
Proof. exact (MK_COMB (@lem74018 A a0 a1 f PRG) (@lem74022 A a0 a1 f PRG')). Qed.
Lemma lem74024 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : (term207 A PRG a0 a1 f PRG') = (term225 A PRG a0 a1 f PRG').
Proof. exact (MK_COMB (@lem74012 A PRG a0 a1 f PRG') (@lem74023 A PRG a0 a1 f PRG')). Qed.
Lemma lem74027 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term205 A P Q.
Proof. exact (fun h0 : term206 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem74028 (P : nat -> Prop) (Q : nat -> Prop) : term226 P Q.
Proof. exact (@lem74027 nat P Q). Qed.
Lemma lem74029 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : term227 A PRG a0 a1 f PRG' b.
Proof. exact (@lem74028 (term79 A a0 a1 f PRG b) (term79 A a0 a1 f PRG' b)). Qed.
Lemma lem74030 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term228 A a0 a1 f PRG b n) = (term48 A a0 a1 f PRG n b).
Proof. exact (eq_refl (term228 A a0 a1 f PRG b n)). Qed.
Lemma lem74031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74032 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term229 A a0 a1 f PRG b n) = (term230 A a0 a1 f PRG n b).
Proof. exact (MK_COMB (@lem74031) (@lem74030 A a0 a1 f PRG n b)). Qed.
Lemma lem74033 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : (term228 A a0 a1 f PRG' b n) = (term48 A a0 a1 f PRG' n b).
Proof. exact (eq_refl (term228 A a0 a1 f PRG' b n)). Qed.
Lemma lem74034 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : (term231 A PRG a0 a1 f PRG' b n) = (term232 A PRG a0 a1 f PRG' n b).
Proof. exact (MK_COMB (@lem74032 A a0 a1 f PRG n b) (@lem74033 A a0 a1 f PRG' n b)). Qed.
Lemma lem74035 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term233 A PRG a0 a1 f PRG' b) = (term234 A PRG a0 a1 f PRG' b).
Proof. exact (fun_ext (fun n : nat => @lem74034 A PRG a0 a1 f PRG' n b)). Qed.
Lemma lem74036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74037 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term235 A PRG a0 a1 f PRG' b) = (term236 A PRG a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74036) (@lem74035 A PRG a0 a1 f PRG' b)). Qed.
Lemma lem74038 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74039 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term237 A PRG a0 a1 f PRG' b) = (term238 A PRG a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74038) (@lem74037 A PRG a0 a1 f PRG' b)). Qed.
Lemma lem74040 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term228 A a0 a1 f PRG b n) = (term48 A a0 a1 f PRG n b).
Proof. exact (eq_refl (term228 A a0 a1 f PRG b n)). Qed.
Lemma lem74041 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term239 A a0 a1 f PRG b) = (term79 A a0 a1 f PRG b).
Proof. exact (fun_ext (fun n : nat => @lem74040 A a0 a1 f PRG n b)). Qed.
Lemma lem74042 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem74043 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term240 A a0 a1 f PRG b) = (term78 A a0 a1 f PRG b).
Proof. exact (MK_COMB (@lem74042) (@lem74041 A a0 a1 f PRG b)). Qed.
Lemma lem74044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74045 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term241 A a0 a1 f PRG b) = (term210 A a0 a1 f PRG b).
Proof. exact (MK_COMB (@lem74044) (@lem74043 A a0 a1 f PRG b)). Qed.
Lemma lem74046 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : (term228 A a0 a1 f PRG' b n) = (term48 A a0 a1 f PRG' n b).
Proof. exact (eq_refl (term228 A a0 a1 f PRG' b n)). Qed.
Lemma lem74047 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term239 A a0 a1 f PRG' b) = (term79 A a0 a1 f PRG' b).
Proof. exact (fun_ext (fun n : nat => @lem74046 A a0 a1 f PRG' n b)). Qed.
Lemma lem74048 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem74049 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term240 A a0 a1 f PRG' b) = (term78 A a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74048) (@lem74047 A a0 a1 f PRG' b)). Qed.
Lemma lem74050 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term242 A PRG a0 a1 f PRG' b) = (term212 A PRG a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74045 A a0 a1 f PRG b) (@lem74049 A a0 a1 f PRG' b)). Qed.
Lemma lem74051 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : (term227 A PRG a0 a1 f PRG' b) = (term243 A PRG a0 a1 f PRG' b).
Proof. exact (MK_COMB (@lem74039 A PRG a0 a1 f PRG' b) (@lem74050 A PRG a0 a1 f PRG' b)). Qed.
Lemma lem74054 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term244 A C B D.
Proof. exact (fun h0 : term202 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem74056 (a0 : nat) (n : nat) : term245 a0 n.
Proof. exact (@lem9120 (a0 = (S n))). Qed.
Lemma lem74057 (a0 : nat) (n : nat) : (term245 a0 n) = (term246 a0 n).
Proof. exact (eq_refl (term245 a0 n)). Qed.
Lemma lem74058 (a0 : nat) (n : nat) : term246 a0 n.
Proof. exact (EQ_MP (@lem74057 a0 n) (@lem74056 a0 n)). Qed.
Lemma lem74060 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term244 A C B D.
Proof. exact (fun h0 : term202 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem74062 {A : Type'} (a1 : A) (f : type1423 A) (b : A) (n : nat) : term247 A a1 f b n.
Proof. exact (@lem9120 (a1 = (f b n))). Qed.
Lemma lem74063 {A : Type'} (a1 : A) (f : type1423 A) (b : A) (n : nat) : (term247 A a1 f b n) = (term248 A a1 f b n).
Proof. exact (eq_refl (term247 A a1 f b n)). Qed.
Lemma lem74064 {A : Type'} (a1 : A) (f : type1423 A) (b : A) (n : nat) : term248 A a1 f b n.
Proof. exact (EQ_MP (@lem74063 A a1 f b n) (@lem74062 A a1 f b n)). Qed.
Lemma lem74065 {A : Type'} (a0 : nat) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term249 A PRG PRG' a0.
Proof. exact (@lem73992 A PRG PRG' h1 a0). Qed.
Lemma lem74066 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (a0 : nat) : (term249 A PRG PRG' a0) = (term126 A PRG PRG' a0).
Proof. exact (eq_refl (term249 A PRG PRG' a0)). Qed.
Lemma lem74067 {A : Type'} (a0 : nat) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term126 A PRG PRG' a0.
Proof. exact (EQ_MP (@lem74066 A PRG PRG' a0) (@lem74065 A a0 PRG PRG' h1)). Qed.
Lemma lem74068 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term250 A PRG PRG' a0 a1.
Proof. exact (@lem74067 A a0 PRG PRG' h1 a1). Qed.
Lemma lem74069 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (a0 : nat) (a1 : A) : (term250 A PRG PRG' a0 a1) = (term125 A PRG PRG' a0 a1).
Proof. exact (eq_refl (term250 A PRG PRG' a0 a1)). Qed.
Lemma lem74070 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term125 A PRG PRG' a0 a1.
Proof. exact (EQ_MP (@lem74069 A PRG PRG' a0 a1) (@lem74068 A a0 a1 PRG PRG' h1)). Qed.
Lemma lem74071 {A : Type'} (PRG : type1597 A) (PRG' : type1597 A) (a0 : nat) (a1 : A) : (term125 A PRG PRG' a0 a1) = ((term125 A PRG PRG' a0 a1) = True).
Proof. exact (@lem7 (term125 A PRG PRG' a0 a1)). Qed.
Lemma lem74074 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : (term125 A PRG PRG' a0 a1) = True.
Proof. exact (EQ_MP (@lem74071 A PRG PRG' a0 a1) (@lem74070 A a0 a1 PRG PRG' h1)). Qed.
Lemma lem74075 {A : Type'} (a0 : nat) (a1 : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : (term125 A PRG PRG' a0 a1) = True.
Proof. exact (@lem74074 A a0 a1 PRG PRG' h1). Qed.
Lemma lem74076 {A : Type'} (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : (term125 A PRG PRG' n b) = True.
Proof. exact (@lem74075 A n b PRG PRG' h1). Qed.
Lemma lem74077 {A : Type'} (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : True = (term125 A PRG PRG' n b).
Proof. exact (SYM (@lem74076 A n b PRG PRG' h1)). Qed.
Lemma lem74078 {A : Type'} (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term125 A PRG PRG' n b.
Proof. exact (EQ_MP (@lem74077 A n b PRG PRG' h1) (@lem0)). Qed.
Lemma lem74079 {A : Type'} (a1 : A) (f : type1423 A) (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term251 A a1 f PRG PRG' n b.
Proof. exact (conj (@lem74064 A a1 f b n) (@lem74078 A n b PRG PRG' h1)). Qed.
Lemma lem74081 {A : Type'} (PRG : type1597 A) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : term252 A PRG a1 f PRG' n b.
Proof. exact (@lem74060 (a1 = (f b n)) (PRG n b) (a1 = (f b n)) (PRG' n b)). Qed.
Lemma lem74082 {A : Type'} (PRG : type1597 A) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : term252 A PRG a1 f PRG' n b.
Proof. exact (@lem74081 A PRG a1 f PRG' n b). Qed.
Lemma lem74083 {A : Type'} (a1 : A) (f : type1423 A) (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term253 A PRG a1 f PRG' n b.
Proof. exact (@lem74082 A PRG a1 f PRG' n b (@lem74079 A a1 f n b PRG PRG' h1)). Qed.
Lemma lem74084 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term254 A a0 PRG a1 f PRG' n b.
Proof. exact (conj (@lem74058 a0 n) (@lem74083 A a1 f n b PRG PRG' h1)). Qed.
Lemma lem74086 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : term255 A PRG a0 a1 f PRG' n b.
Proof. exact (@lem74054 (a0 = (S n)) (term49 A a1 f PRG n b) (a0 = (S n)) (term49 A a1 f PRG' n b)). Qed.
Lemma lem74087 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (n : nat) (b : A) : term255 A PRG a0 a1 f PRG' n b.
Proof. exact (@lem74086 A PRG a0 a1 f PRG' n b). Qed.
Lemma lem74088 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (n : nat) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term232 A PRG a0 a1 f PRG' n b.
Proof. exact (@lem74087 A PRG a0 a1 f PRG' n b (@lem74084 A a0 a1 f n b PRG PRG' h1)). Qed.
Lemma lem74093 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term236 A PRG a0 a1 f PRG' b.
Proof. exact (fun n : nat => @lem74088 A a0 a1 f n b PRG PRG' h1). Qed.
Lemma lem74095 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : term243 A PRG a0 a1 f PRG' b.
Proof. exact (EQ_MP (@lem74051 A PRG a0 a1 f PRG' b) (@lem74029 A PRG a0 a1 f PRG' b)). Qed.
Lemma lem74096 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) (b : A) : term243 A PRG a0 a1 f PRG' b.
Proof. exact (@lem74095 A PRG a0 a1 f PRG' b). Qed.
Lemma lem74097 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (b : A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term212 A PRG a0 a1 f PRG' b.
Proof. exact (@lem74096 A PRG a0 a1 f PRG' b (@lem74093 A a0 a1 f b PRG PRG' h1)). Qed.
Lemma lem74102 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term216 A PRG a0 a1 f PRG'.
Proof. exact (fun b : A => @lem74097 A a0 a1 f b PRG PRG' h1). Qed.
Lemma lem74104 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : term225 A PRG a0 a1 f PRG'.
Proof. exact (EQ_MP (@lem74024 A PRG a0 a1 f PRG') (@lem74002 A PRG a0 a1 f PRG')). Qed.
Lemma lem74105 {A : Type'} (PRG : type1597 A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : term225 A PRG a0 a1 f PRG'.
Proof. exact (@lem74104 A PRG a0 a1 f PRG'). Qed.
Lemma lem74106 {A : Type'} (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term224 A PRG a0 a1 f PRG'.
Proof. exact (@lem74105 A PRG a0 a1 f PRG' (@lem74102 A a0 a1 f PRG PRG' h1)). Qed.
Lemma lem74107 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term256 A e PRG a0 a1 f PRG'.
Proof. exact (conj (@lem73998 A a0 a1 e) (@lem74106 A a0 a1 f PRG PRG' h1)). Qed.
Lemma lem74109 {A : Type'} (PRG : type1597 A) (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : term257 A PRG e a0 a1 f PRG'.
Proof. exact (@lem73994 (term31 A a0 a1 e) (term80 A a0 a1 f PRG) (term31 A a0 a1 e) (term80 A a0 a1 f PRG')). Qed.
Lemma lem74110 {A : Type'} (PRG : type1597 A) (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG' : type1597 A) : term257 A PRG e a0 a1 f PRG'.
Proof. exact (@lem74109 A PRG e a0 a1 f PRG'). Qed.
Lemma lem74111 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term140 A PRG e a0 a1 f PRG'.
Proof. exact (@lem74110 A PRG e a0 a1 f PRG' (@lem74107 A e a0 a1 f PRG PRG' h1)). Qed.
Lemma lem74116 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term138 A PRG e a0 f PRG'.
Proof. exact (fun a1 : A => @lem74111 A e a0 a1 f PRG PRG' h1). Qed.
Lemma lem74121 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term136 A PRG e f PRG'.
Proof. exact (fun a0 : nat => @lem74116 A e a0 f PRG PRG' h1). Qed.
Lemma lem74122 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : (term127 A PRG PRG') = (term136 A PRG e f PRG').
Proof. exact (prop_ext (fun h2 : term127 A PRG PRG' => @lem74121 A e f PRG PRG' h1) (fun h2 : term136 A PRG e f PRG' => @lem73992 A PRG PRG' h1)). Qed.
Lemma lem74123 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (PRG' : type1597 A) (h1 : term127 A PRG PRG') : term136 A PRG e f PRG'.
Proof. exact (EQ_MP (@lem74122 A e f PRG PRG' h1) (@lem73992 A PRG PRG' h1)). Qed.
Lemma lem74124 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (PRG' : type1597 A) : term135 A PRG e f PRG'.
Proof. exact (fun h0 : term127 A PRG PRG' => @lem74123 A e f PRG PRG' h0). Qed.
Lemma lem74129 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) : term133 A PRG e f.
Proof. exact (fun PRG' : type1597 A => @lem74124 A PRG e f PRG'). Qed.
Lemma lem74134 {A : Type'} (e : A) (f : type1423 A) : term130 A e f.
Proof. exact (fun PRG : type1597 A => @lem74129 A PRG e f). Qed.
Lemma lem74135 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : (term130 A e f) = (term200 A e f PRG).
Proof. exact (prop_ext (fun h2 : term130 A e f => @lem73991 A PRG e f h2 h1) (fun h2 : term200 A e f PRG => @lem74134 A e f)). Qed.
Lemma lem74136 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term200 A e f PRG.
Proof. exact (EQ_MP (@lem74135 A PRG e f h1) (@lem74134 A e f)). Qed.
Lemma lem74137 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : PRG = (term111 A e f).
Proof. exact (h1). Qed.
Lemma lem74138 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term258 A e f PRG.
Proof. exact (fun h0 : PRG = (term111 A e f) => @lem74136 A PRG e f h0). Qed.
Lemma lem74139 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term258 A e f PRG.
Proof. exact (@lem74138 A e f PRG). Qed.
Lemma lem74140 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term200 A e f PRG.
Proof. exact (@lem74139 A e f PRG (@lem74137 A PRG e f h1)). Qed.
Lemma lem74141 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term259 A e f PRG) = (term200 A e f PRG).
Proof. exact (eq_refl (term259 A e f PRG)). Qed.
Lemma lem74142 {A : Type'} : term260 A.
Proof. exact (@lem9102 (type1597 A)). Qed.
Lemma lem74143 {A : Type'} (e : A) (f : type1423 A) : term261 A e f.
Proof. exact (@lem74142 A (term262 A e f)). Qed.
Lemma lem74144 {A : Type'} (e : A) (f : type1423 A) : (term261 A e f) = (term263 A e f).
Proof. exact (eq_refl (term261 A e f)). Qed.
Lemma lem74145 {A : Type'} (e : A) (f : type1423 A) : term263 A e f.
Proof. exact (EQ_MP (@lem74144 A e f) (@lem74143 A e f)). Qed.
Lemma lem74146 {A : Type'} (e : A) (f : type1423 A) : term264 A e f.
Proof. exact (@lem74145 A e f (term111 A e f)). Qed.
Lemma lem74147 {A : Type'} (e : A) (f : type1423 A) : (term264 A e f) = (term265 A e f).
Proof. exact (eq_refl (term264 A e f)). Qed.
Lemma lem74148 {A : Type'} (e : A) (f : type1423 A) : term265 A e f.
Proof. exact (EQ_MP (@lem74147 A e f) (@lem74146 A e f)). Qed.
Lemma lem74149 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term200 A e f PRG) = (term259 A e f PRG).
Proof. exact (SYM (@lem74141 A e f PRG)). Qed.
Lemma lem74150 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) (h1 : PRG = (term111 A e f)) : term259 A e f PRG.
Proof. exact (EQ_MP (@lem74149 A e f PRG) (@lem74140 A PRG e f h1)). Qed.
Lemma lem74151 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term266 A e f PRG.
Proof. exact (fun h0 : PRG = (term111 A e f) => @lem74150 A PRG e f h0). Qed.
Lemma lem74152 {A : Type'} (e : A) (f : type1423 A) : term267 A e f.
Proof. exact (fun PRG : type1597 A => @lem74151 A e f PRG). Qed.
Lemma lem74153 {A : Type'} (e : A) (f : type1423 A) : term268 A e f.
Proof. exact (@lem74148 A e f (@lem74152 A e f)). Qed.
Lemma lem74154 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem74155 {A : Type'} (P : A -> Prop) : (term14 A P) = ((term15 A P) = (term16 A P)).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem74158 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (EQ_MP (@lem74155 A P) (@lem74154 A P)). Qed.
Lemma lem74159 {A : Type'} (P : type976 A) : (term269 A P) = (term270 A P).
Proof. exact (@lem74158 (nat -> A) P). Qed.
Lemma lem74160 {A : Type'} (e : A) (f : type1423 A) : (term271 A e f) = (term272 A e f).
Proof. exact (@lem74159 A (term273 A e f)). Qed.
Lemma lem74161 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term274 A e f fn) = (term275 A e f fn).
Proof. exact (eq_refl (term274 A e f fn)). Qed.
Lemma lem74162 {A : Type'} (e : A) (f : type1423 A) : (term276 A e f) = (term273 A e f).
Proof. exact (fun_ext (fun fn : nat -> A => @lem74161 A e f fn)). Qed.
Lemma lem74163 {A : Type'} : (@ex1 (nat -> A)) = (@ex1 (nat -> A)).
Proof. exact (eq_refl (@ex1 (nat -> A))). Qed.
Lemma lem74164 {A : Type'} (e : A) (f : type1423 A) : (term271 A e f) = (term277 A e f).
Proof. exact (MK_COMB (@lem74163 A) (@lem74162 A e f)). Qed.
Lemma lem74165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem74166 {A : Type'} (e : A) (f : type1423 A) : (term278 A e f) = (term279 A e f).
Proof. exact (MK_COMB (@lem74165) (@lem74164 A e f)). Qed.
Lemma lem74167 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term274 A e f fn) = (term275 A e f fn).
Proof. exact (eq_refl (term274 A e f fn)). Qed.
Lemma lem74168 {A : Type'} (e : A) (f : type1423 A) : (term276 A e f) = (term273 A e f).
Proof. exact (fun_ext (fun fn : nat -> A => @lem74167 A e f fn)). Qed.
Lemma lem74169 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem74170 {A : Type'} (e : A) (f : type1423 A) : (term280 A e f) = (term281 A e f).
Proof. exact (MK_COMB (@lem74169 A) (@lem74168 A e f)). Qed.
Lemma lem74171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74172 {A : Type'} (e : A) (f : type1423 A) : (term282 A e f) = (term283 A e f).
Proof. exact (MK_COMB (@lem74171) (@lem74170 A e f)). Qed.
Lemma lem74173 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term274 A e f fn) = (term275 A e f fn).
Proof. exact (eq_refl (term274 A e f fn)). Qed.
Lemma lem74174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74175 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term284 A e f fn) = (term285 A e f fn).
Proof. exact (MK_COMB (@lem74174) (@lem74173 A e f fn)). Qed.
Lemma lem74176 {A : Type'} (e : A) (f : type1423 A) (x' : nat -> A) : (term274 A e f x') = (term275 A e f x').
Proof. exact (eq_refl (term274 A e f x')). Qed.
Lemma lem74177 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) : (term286 A fn e f x') = (term287 A fn e f x').
Proof. exact (MK_COMB (@lem74175 A e f fn) (@lem74176 A e f x')). Qed.
Lemma lem74178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74179 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) : (term288 A fn e f x') = (term289 A fn e f x').
Proof. exact (MK_COMB (@lem74178) (@lem74177 A fn e f x')). Qed.
Lemma lem74180 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (fn = x') = (fn = x').
Proof. exact (eq_refl (fn = x')). Qed.
Lemma lem74181 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) (x' : nat -> A) : (term290 A e f fn x') = (term291 A e f fn x').
Proof. exact (MK_COMB (@lem74179 A fn e f x') (@lem74180 A fn x')). Qed.
Lemma lem74182 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term292 A e f fn) = (term293 A e f fn).
Proof. exact (fun_ext (fun x' : nat -> A => @lem74181 A e f fn x')). Qed.
Lemma lem74183 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem74184 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term294 A e f fn) = (term295 A e f fn).
Proof. exact (MK_COMB (@lem74183 A) (@lem74182 A e f fn)). Qed.
Lemma lem74185 {A : Type'} (e : A) (f : type1423 A) : (term296 A e f) = (term297 A e f).
Proof. exact (fun_ext (fun fn : nat -> A => @lem74184 A e f fn)). Qed.
Lemma lem74186 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem74187 {A : Type'} (e : A) (f : type1423 A) : (term298 A e f) = (term299 A e f).
Proof. exact (MK_COMB (@lem74186 A) (@lem74185 A e f)). Qed.
Lemma lem74188 {A : Type'} (e : A) (f : type1423 A) : (term272 A e f) = (term300 A e f).
Proof. exact (MK_COMB (@lem74172 A e f) (@lem74187 A e f)). Qed.
Lemma lem74189 {A : Type'} (e : A) (f : type1423 A) : ((term271 A e f) = (term272 A e f)) = ((term277 A e f) = (term300 A e f)).
Proof. exact (MK_COMB (@lem74166 A e f) (@lem74188 A e f)). Qed.
Lemma lem74190 {A : Type'} (e : A) (f : type1423 A) : (term277 A e f) = (term300 A e f).
Proof. exact (EQ_MP (@lem74189 A e f) (@lem74160 A e f)). Qed.
Lemma lem74191 {A : Type'} (e : A) (f : type1423 A) : (term300 A e f) = (term277 A e f).
Proof. exact (SYM (@lem74190 A e f)). Qed.
Lemma lem74192 {A : Type'} (e : A) (f : type1423 A) (h1 : term268 A e f) : term268 A e f.
Proof. exact (h1). Qed.
Lemma lem74193 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term200 A e f PRG) : term200 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem74194 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term199 A e f PRG) : term199 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem74195 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term95 A e PRG f.
Proof. exact (h1). Qed.
Lemma lem74196 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term199 A e f PRG) : term199 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem74197 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term192 A e f PRG.
Proof. exact (h1). Qed.
Lemma lem74200 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (h1). Qed.
Lemma lem74201 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (SYM (@lem74200 A e a0 a1 f PRG h1)). Qed.
Lemma lem74202 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (h1). Qed.
Lemma lem74203 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (SYM (@lem74202 A e f PRG a0 a1 h1)). Qed.
Lemma lem74204 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) : ((PRG a0 a1) = (term101 A e a0 a1 f PRG)) = ((term101 A e a0 a1 f PRG) = (PRG a0 a1)).
Proof. exact (prop_ext (fun h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG) => @lem74201 A e a0 a1 f PRG h1) (fun h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1) => @lem74203 A e f PRG a0 a1 h1)). Qed.
Lemma lem74205 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term301 A e a0 f PRG) = (term302 A e f PRG a0).
Proof. exact (fun_ext (fun a1 : A => @lem74204 A e f PRG a0 a1)). Qed.
Lemma lem74206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74207 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) : (term191 A e a0 f PRG) = (term303 A e f PRG a0).
Proof. exact (MK_COMB (@lem74206 A) (@lem74205 A e f PRG a0)). Qed.
Lemma lem74208 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term304 A e f PRG) = (term305 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem74207 A e f PRG a0)). Qed.
Lemma lem74209 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74210 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term192 A e f PRG) = (term306 A e f PRG).
Proof. exact (MK_COMB (@lem74209) (@lem74208 A e f PRG)). Qed.
Lemma lem74211 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term306 A e f PRG.
Proof. exact (EQ_MP (@lem74210 A e f PRG) (@lem74197 A e f PRG h1)). Qed.
Lemma lem74213 {A : Type'} (PRG : type1597 A) (h1 : term307 A PRG) : term307 A PRG.
Proof. exact (h1). Qed.
Lemma lem74215 (P : nat -> Prop) : term2 P.
Proof. exact (EQ_MP (@lem73549 P) (@lem73548 P)). Qed.
Lemma lem74216 {A : Type'} (PRG : type1597 A) : term308 A PRG.
Proof. exact (@lem74215 (term309 A PRG)). Qed.
Lemma lem74217 {A : Type'} (PRG : type1597 A) : (term310 A PRG) = (term311 A PRG).
Proof. exact (eq_refl (term310 A PRG)). Qed.
Lemma lem74218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74219 {A : Type'} (PRG : type1597 A) : (term312 A PRG) = (term313 A PRG).
Proof. exact (MK_COMB (@lem74218) (@lem74217 A PRG)). Qed.
Lemma lem74220 {A : Type'} (PRG : type1597 A) (n : nat) : (term314 A PRG n) = (term315 A PRG n).
Proof. exact (eq_refl (term314 A PRG n)). Qed.
Lemma lem74221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74222 {A : Type'} (PRG : type1597 A) (n : nat) : (term316 A PRG n) = (term317 A PRG n).
Proof. exact (MK_COMB (@lem74221) (@lem74220 A PRG n)). Qed.
Lemma lem74223 {A : Type'} (PRG : type1597 A) (n : nat) : (term318 A PRG n) = (term319 A PRG n).
Proof. exact (eq_refl (term318 A PRG n)). Qed.
Lemma lem74224 {A : Type'} (PRG : type1597 A) (n : nat) : (term320 A PRG n) = (term321 A PRG n).
Proof. exact (MK_COMB (@lem74222 A PRG n) (@lem74223 A PRG n)). Qed.
Lemma lem74225 {A : Type'} (PRG : type1597 A) : (term322 A PRG) = (term323 A PRG).
Proof. exact (fun_ext (fun n : nat => @lem74224 A PRG n)). Qed.
Lemma lem74226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74227 {A : Type'} (PRG : type1597 A) : (term324 A PRG) = (term325 A PRG).
Proof. exact (MK_COMB (@lem74226) (@lem74225 A PRG)). Qed.
Lemma lem74228 {A : Type'} (PRG : type1597 A) : (term326 A PRG) = (term327 A PRG).
Proof. exact (MK_COMB (@lem74219 A PRG) (@lem74227 A PRG)). Qed.
Lemma lem74229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74230 {A : Type'} (PRG : type1597 A) : (term328 A PRG) = (term329 A PRG).
Proof. exact (MK_COMB (@lem74229) (@lem74228 A PRG)). Qed.
Lemma lem74231 {A : Type'} (PRG : type1597 A) (n : nat) : (term314 A PRG n) = (term315 A PRG n).
Proof. exact (eq_refl (term314 A PRG n)). Qed.
Lemma lem74232 {A : Type'} (PRG : type1597 A) : (term330 A PRG) = (term309 A PRG).
Proof. exact (fun_ext (fun n : nat => @lem74231 A PRG n)). Qed.
Lemma lem74233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74234 {A : Type'} (PRG : type1597 A) : (term331 A PRG) = (term307 A PRG).
Proof. exact (MK_COMB (@lem74233) (@lem74232 A PRG)). Qed.
Lemma lem74235 {A : Type'} (PRG : type1597 A) : (term308 A PRG) = (term332 A PRG).
Proof. exact (MK_COMB (@lem74230 A PRG) (@lem74234 A PRG)). Qed.
Lemma lem74236 {A : Type'} (PRG : type1597 A) : term332 A PRG.
Proof. exact (EQ_MP (@lem74235 A PRG) (@lem74216 A PRG)). Qed.
Lemma lem74237 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term315 A PRG n) : term315 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74240 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (h1). Qed.
Lemma lem74241 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (SYM (@lem74240 A e f PRG a0 a1 h1)). Qed.
Lemma lem74242 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (h1). Qed.
Lemma lem74243 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (SYM (@lem74242 A e a0 a1 f PRG h1)). Qed.
Lemma lem74244 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : ((term101 A e a0 a1 f PRG) = (PRG a0 a1)) = ((PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (prop_ext (fun h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1) => @lem74241 A e f PRG a0 a1 h1) (fun h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG) => @lem74243 A e a0 a1 f PRG h1)). Qed.
Lemma lem74245 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term302 A e f PRG a0) = (term301 A e a0 f PRG).
Proof. exact (fun_ext (fun a1 : A => @lem74244 A e a0 a1 f PRG)). Qed.
Lemma lem74246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74247 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term303 A e f PRG a0) = (term191 A e a0 f PRG).
Proof. exact (MK_COMB (@lem74246 A) (@lem74245 A e a0 f PRG)). Qed.
Lemma lem74248 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term305 A e f PRG) = (term304 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem74247 A e a0 f PRG)). Qed.
Lemma lem74249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74250 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term306 A e f PRG) = (term192 A e f PRG).
Proof. exact (MK_COMB (@lem74249) (@lem74248 A e f PRG)). Qed.
Lemma lem74251 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term192 A e f PRG.
Proof. exact (EQ_MP (@lem74250 A e f PRG) (@lem74211 A e f PRG h1)). Qed.
Lemma lem74252 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term333 A e f PRG a0.
Proof. exact (@lem74251 A e f PRG h1 a0). Qed.
Lemma lem74253 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term333 A e f PRG a0) = (term191 A e a0 f PRG).
Proof. exact (eq_refl (term333 A e f PRG a0)). Qed.
Lemma lem74254 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term191 A e a0 f PRG.
Proof. exact (EQ_MP (@lem74253 A e a0 f PRG) (@lem74252 A a0 e f PRG h1)). Qed.
Lemma lem74255 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term334 A e a0 f PRG a1.
Proof. exact (@lem74254 A a0 e f PRG h1 a1). Qed.
Lemma lem74256 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term334 A e a0 f PRG a1) = ((PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (eq_refl (term334 A e a0 f PRG a1)). Qed.
Lemma lem74259 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (EQ_MP (@lem74256 A e a0 a1 f PRG) (@lem74255 A a0 a1 e f PRG h1)). Qed.
Lemma lem74260 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (@lem74259 A a0 a1 e f PRG h1). Qed.
Lemma lem74261 {A : Type'} (y : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (PRG 0 y) = (term335 A e y f PRG).
Proof. exact (@lem74260 A 0 y e f PRG h1). Qed.
Lemma lem74262 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term336 A PRG) = (term337 A e f PRG).
Proof. exact (fun_ext (fun y : A => @lem74261 A y e f PRG h1)). Qed.
Lemma lem74263 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74264 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term311 A PRG) = (term338 A e f PRG).
Proof. exact (MK_COMB (@lem74263 A) (@lem74262 A e f PRG h1)). Qed.
Lemma lem74265 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term338 A e f PRG) = (term311 A PRG).
Proof. exact (SYM (@lem74264 A e f PRG h1)). Qed.
Lemma lem74274 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (h1). Qed.
Lemma lem74275 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (a0 : nat) (a1 : A) (h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (SYM (@lem74274 A e f PRG a0 a1 h1)). Qed.
Lemma lem74276 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (h1). Qed.
Lemma lem74277 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) (h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG)) : (term101 A e a0 a1 f PRG) = (PRG a0 a1).
Proof. exact (SYM (@lem74276 A e a0 a1 f PRG h1)). Qed.
Lemma lem74278 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : ((term101 A e a0 a1 f PRG) = (PRG a0 a1)) = ((PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (prop_ext (fun h1 : (term101 A e a0 a1 f PRG) = (PRG a0 a1) => @lem74275 A e f PRG a0 a1 h1) (fun h1 : (PRG a0 a1) = (term101 A e a0 a1 f PRG) => @lem74277 A e a0 a1 f PRG h1)). Qed.
Lemma lem74279 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term302 A e f PRG a0) = (term301 A e a0 f PRG).
Proof. exact (fun_ext (fun a1 : A => @lem74278 A e a0 a1 f PRG)). Qed.
Lemma lem74280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74281 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term303 A e f PRG a0) = (term191 A e a0 f PRG).
Proof. exact (MK_COMB (@lem74280 A) (@lem74279 A e a0 f PRG)). Qed.
Lemma lem74282 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term305 A e f PRG) = (term304 A e f PRG).
Proof. exact (fun_ext (fun a0 : nat => @lem74281 A e a0 f PRG)). Qed.
Lemma lem74283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem74284 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term306 A e f PRG) = (term192 A e f PRG).
Proof. exact (MK_COMB (@lem74283) (@lem74282 A e f PRG)). Qed.
Lemma lem74285 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term192 A e f PRG.
Proof. exact (EQ_MP (@lem74284 A e f PRG) (@lem74211 A e f PRG h1)). Qed.
Lemma lem74286 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term333 A e f PRG a0.
Proof. exact (@lem74285 A e f PRG h1 a0). Qed.
Lemma lem74287 {A : Type'} (e : A) (a0 : nat) (f : type1423 A) (PRG : type1597 A) : (term333 A e f PRG a0) = (term191 A e a0 f PRG).
Proof. exact (eq_refl (term333 A e f PRG a0)). Qed.
Lemma lem74288 {A : Type'} (a0 : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term191 A e a0 f PRG.
Proof. exact (EQ_MP (@lem74287 A e a0 f PRG) (@lem74286 A a0 e f PRG h1)). Qed.
Lemma lem74289 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term334 A e a0 f PRG a1.
Proof. exact (@lem74288 A a0 e f PRG h1 a1). Qed.
Lemma lem74290 {A : Type'} (e : A) (a0 : nat) (a1 : A) (f : type1423 A) (PRG : type1597 A) : (term334 A e a0 f PRG a1) = ((PRG a0 a1) = (term101 A e a0 a1 f PRG)).
Proof. exact (eq_refl (term334 A e a0 f PRG a1)). Qed.
Lemma lem74293 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (EQ_MP (@lem74290 A e a0 a1 f PRG) (@lem74289 A a0 a1 e f PRG h1)). Qed.
Lemma lem74294 {A : Type'} (a0 : nat) (a1 : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (PRG a0 a1) = (term101 A e a0 a1 f PRG).
Proof. exact (@lem74293 A a0 a1 e f PRG h1). Qed.
Lemma lem74295 {A : Type'} (n : nat) (y : A) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term339 A PRG n y) = (term340 A e n y f PRG).
Proof. exact (@lem74294 A (S n) y e f PRG h1). Qed.
Lemma lem74296 {A : Type'} (n : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term341 A PRG n) = (term342 A e n f PRG).
Proof. exact (fun_ext (fun y : A => @lem74295 A n y e f PRG h1)). Qed.
Lemma lem74297 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74298 {A : Type'} (n : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term319 A PRG n) = (term343 A e n f PRG).
Proof. exact (MK_COMB (@lem74297 A) (@lem74296 A n e f PRG h1)). Qed.
Lemma lem74299 {A : Type'} (n : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : (term343 A e n f PRG) = (term319 A PRG n).
Proof. exact (SYM (@lem74298 A n e f PRG h1)). Qed.
Lemma lem74305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem74306 (x : nat) : (x = x) = True.
Proof. exact (@lem74305 nat x). Qed.
Lemma lem74307 : (0 = 0) = True.
Proof. exact (@lem74306 0). Qed.
Lemma lem74308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74309 : term344 = (and True).
Proof. exact (MK_COMB (@lem74308) (@lem74307)). Qed.
Lemma lem74312 {A : Type'} (y : A) (e : A) : (y = e) = (y = e).
Proof. exact (eq_refl (y = e)). Qed.
Lemma lem74313 {A : Type'} (y : A) (e : A) : (term345 A y e) = (term346 A y e).
Proof. exact (MK_COMB (@lem74309) (@lem74312 A y e)). Qed.
Lemma lem74315 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem74316 {A : Type'} (y : A) (e : A) : (term346 A y e) = (y = e).
Proof. exact (@lem74315 (y = e)). Qed.
Lemma lem74319 {A : Type'} (y : A) (e : A) : (term345 A y e) = (y = e).
Proof. exact (TRANS (@lem74313 A y e) (@lem74316 A y e)). Qed.
Lemma lem74320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem74321 {A : Type'} (y : A) (e : A) : (term347 A y e) = (term348 A y e).
Proof. exact (MK_COMB (@lem74320) (@lem74319 A y e)). Qed.
Lemma lem74333 (n : nat) : (0 = (S n)) = False.
Proof. exact (@lem73517 n (@lem73516 n)). Qed.
Lemma lem74334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74335 (n : nat) : (term349 n) = (and False).
Proof. exact (MK_COMB (@lem74334) (@lem74333 n)). Qed.
Lemma lem74340 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term49 A y f PRG n b) = (term49 A y f PRG n b).
Proof. exact (eq_refl (term49 A y f PRG n b)). Qed.
Lemma lem74341 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term350 A y f PRG n b) = (term351 A y f PRG n b).
Proof. exact (MK_COMB (@lem74335 n) (@lem74340 A y f PRG n b)). Qed.
Lemma lem74343 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem74344 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term351 A y f PRG n b) = False.
Proof. exact (@lem74343 (term49 A y f PRG n b)). Qed.
Lemma lem74345 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term350 A y f PRG n b) = False.
Proof. exact (TRANS (@lem74341 A y f PRG n b) (@lem74344 A y f PRG n b)). Qed.
Lemma lem74346 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term352 A y f PRG b) = term353.
Proof. exact (fun_ext (fun n : nat => @lem74345 A y f PRG n b)). Qed.
Lemma lem74347 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem74348 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term354 A y f PRG b) = term355.
Proof. exact (MK_COMB (@lem74347) (@lem74346 A y f PRG b)). Qed.
Lemma lem74350 {A : Type'} (t : Prop) : (term356 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem74351 (t : Prop) : (term357 t) = t.
Proof. exact (@lem74350 nat t). Qed.
Lemma lem74352 : term355 = False.
Proof. exact (@lem74351 False). Qed.
Lemma lem74353 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term354 A y f PRG b) = False.
Proof. exact (TRANS (@lem74348 A y f PRG b) (@lem74352)). Qed.
Lemma lem74354 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) : (term358 A y f PRG) = (term359 A).
Proof. exact (fun_ext (fun b : A => @lem74353 A y f PRG b)). Qed.
Lemma lem74355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74356 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) : (term360 A y f PRG) = (term361 A).
Proof. exact (MK_COMB (@lem74355 A) (@lem74354 A y f PRG)). Qed.
Lemma lem74358 {A : Type'} (t : Prop) : (term356 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem74359 {A : Type'} (t : Prop) : (term356 A t) = t.
Proof. exact (@lem74358 A t). Qed.
Lemma lem74360 {A : Type'} : (term361 A) = False.
Proof. exact (@lem74359 A False). Qed.
Lemma lem74361 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) : (term360 A y f PRG) = False.
Proof. exact (TRANS (@lem74356 A y f PRG) (@lem74360 A)). Qed.
Lemma lem74362 {A : Type'} (f : type1423 A) (PRG : type1597 A) (y : A) (e : A) : (term335 A e y f PRG) = (term362 A y e).
Proof. exact (MK_COMB (@lem74321 A y e) (@lem74361 A y f PRG)). Qed.
Lemma lem74364 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem74365 {A : Type'} (y : A) (e : A) : (term362 A y e) = (y = e).
Proof. exact (@lem74364 (y = e)). Qed.
Lemma lem74368 {A : Type'} (f : type1423 A) (PRG : type1597 A) (y : A) (e : A) : (term335 A e y f PRG) = (y = e).
Proof. exact (TRANS (@lem74362 A f PRG y e) (@lem74365 A y e)). Qed.
Lemma lem74369 {A : Type'} (f : type1423 A) (PRG : type1597 A) (e : A) : (term337 A e f PRG) = (term363 A e).
Proof. exact (fun_ext (fun y : A => @lem74368 A f PRG y e)). Qed.
Lemma lem74370 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74371 {A : Type'} (f : type1423 A) (PRG : type1597 A) (e : A) : (term338 A e f PRG) = (term22 A e).
Proof. exact (MK_COMB (@lem74370 A) (@lem74369 A f PRG e)). Qed.
Lemma lem74373 {A : Type'} (a : A) : (term22 A a) = True.
Proof. exact (EQ_MP (@lem73495 A a) (@lem73494 A a)). Qed.
Lemma lem74374 {A : Type'} (a : A) : (term22 A a) = True.
Proof. exact (@lem74373 A a). Qed.
Lemma lem74375 {A : Type'} (e : A) : (term22 A e) = True.
Proof. exact (@lem74374 A e). Qed.
Lemma lem74376 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : (term338 A e f PRG) = True.
Proof. exact (TRANS (@lem74371 A f PRG e) (@lem74375 A e)). Qed.
Lemma lem74377 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : True = (term338 A e f PRG).
Proof. exact (SYM (@lem74376 A e f PRG)). Qed.
Lemma lem74378 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) : term338 A e f PRG.
Proof. exact (EQ_MP (@lem74377 A e f PRG) (@lem0)). Qed.
Lemma lem74384 (n : nat) : ((S n) = 0) = False.
Proof. exact (@lem73506 n (@lem73505 n)). Qed.
Lemma lem74385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74386 (n : nat) : (term364 n) = (and False).
Proof. exact (MK_COMB (@lem74385) (@lem74384 n)). Qed.
Lemma lem74389 {A : Type'} (y : A) (e : A) : (y = e) = (y = e).
Proof. exact (eq_refl (y = e)). Qed.
Lemma lem74390 {A : Type'} (n : nat) (y : A) (e : A) : (term365 A n y e) = (term366 A y e).
Proof. exact (MK_COMB (@lem74386 n) (@lem74389 A y e)). Qed.
Lemma lem74392 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem74393 {A : Type'} (y : A) (e : A) : (term366 A y e) = False.
Proof. exact (@lem74392 (y = e)). Qed.
Lemma lem74394 {A : Type'} (n : nat) (y : A) (e : A) : (term365 A n y e) = False.
Proof. exact (TRANS (@lem74390 A n y e) (@lem74393 A y e)). Qed.
Lemma lem74395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem74396 {A : Type'} (n : nat) (y : A) (e : A) : (term367 A n y e) = (or False).
Proof. exact (MK_COMB (@lem74395) (@lem74394 A n y e)). Qed.
Lemma lem74408 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem73501 m n) (@lem73500 m n)). Qed.
Lemma lem74409 (n : nat) (n' : nat) : ((S n) = (S n')) = (n = n').
Proof. exact (@lem74408 n n'). Qed.
Lemma lem74412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74413 (n : nat) (n' : nat) : (term368 n n') = (term369 n n').
Proof. exact (MK_COMB (@lem74412) (@lem74409 n n')). Qed.
Lemma lem74418 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n' : nat) (b : A) : (term49 A y f PRG n' b) = (term49 A y f PRG n' b).
Proof. exact (eq_refl (term49 A y f PRG n' b)). Qed.
Lemma lem74419 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (n' : nat) (b : A) : (term370 A n y f PRG n' b) = (term371 A n y f PRG n' b).
Proof. exact (MK_COMB (@lem74413 n n') (@lem74418 A y f PRG n' b)). Qed.
Lemma lem74422 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term372 A n y f PRG b) = (term373 A n y f PRG b).
Proof. exact (fun_ext (fun n' : nat => @lem74419 A n y f PRG n' b)). Qed.
Lemma lem74423 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem74424 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term374 A n y f PRG b) = (term375 A n y f PRG b).
Proof. exact (MK_COMB (@lem74423) (@lem74422 A n y f PRG b)). Qed.
Lemma lem74429 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) : (term376 A n y f PRG) = (term377 A n y f PRG).
Proof. exact (fun_ext (fun b : A => @lem74424 A n y f PRG b)). Qed.
Lemma lem74430 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74431 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) : (term378 A n y f PRG) = (term379 A n y f PRG).
Proof. exact (MK_COMB (@lem74430 A) (@lem74429 A n y f PRG)). Qed.
Lemma lem74436 {A : Type'} (e : A) (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) : (term340 A e n y f PRG) = (term380 A n y f PRG).
Proof. exact (MK_COMB (@lem74396 A n y e) (@lem74431 A n y f PRG)). Qed.
Lemma lem74438 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem74439 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) : (term380 A n y f PRG) = (term379 A n y f PRG).
Proof. exact (@lem74438 (term379 A n y f PRG)). Qed.
Lemma lem74456 {A : Type'} (e : A) (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) : (term340 A e n y f PRG) = (term379 A n y f PRG).
Proof. exact (TRANS (@lem74436 A e n y f PRG) (@lem74439 A n y f PRG)). Qed.
Lemma lem74457 {A : Type'} (e : A) (n : nat) (f : type1423 A) (PRG : type1597 A) : (term342 A e n f PRG) = (term381 A n f PRG).
Proof. exact (fun_ext (fun y : A => @lem74456 A e n y f PRG)). Qed.
Lemma lem74458 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74459 {A : Type'} (e : A) (n : nat) (f : type1423 A) (PRG : type1597 A) : (term343 A e n f PRG) = (term382 A n f PRG).
Proof. exact (MK_COMB (@lem74458 A) (@lem74457 A e n f PRG)). Qed.
Lemma lem74460 {A : Type'} (e : A) (n : nat) (f : type1423 A) (PRG : type1597 A) : (term382 A n f PRG) = (term343 A e n f PRG).
Proof. exact (SYM (@lem74459 A e n f PRG)). Qed.
Lemma lem74466 {A : Type'} (P : A -> Prop) (a : A) : (term20 A a P) = (P a).
Proof. exact (EQ_MP (@lem73477 A P a) (@lem73476 A P a)). Qed.
Lemma lem74467 (P : nat -> Prop) (a : nat) : (term383 a P) = (P a).
Proof. exact (@lem74466 nat P a). Qed.
Lemma lem74468 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) (n : nat) : (term384 A n y f PRG b) = (term385 A y f PRG b n).
Proof. exact (@lem74467 (term386 A y f PRG b) n). Qed.
Lemma lem74469 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n' : nat) (b : A) : (term385 A y f PRG b n') = (term49 A y f PRG n' b).
Proof. exact (eq_refl (term385 A y f PRG b n')). Qed.
Lemma lem74470 (n : nat) (n' : nat) : (term369 n n') = (term369 n n').
Proof. exact (eq_refl (term369 n n')). Qed.
Lemma lem74471 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (n' : nat) (b : A) : (term387 A n y f PRG b n') = (term371 A n y f PRG n' b).
Proof. exact (MK_COMB (@lem74470 n n') (@lem74469 A y f PRG n' b)). Qed.
Lemma lem74472 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term388 A n y f PRG b) = (term373 A n y f PRG b).
Proof. exact (fun_ext (fun n' : nat => @lem74471 A n y f PRG n' b)). Qed.
Lemma lem74473 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem74474 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term384 A n y f PRG b) = (term375 A n y f PRG b).
Proof. exact (MK_COMB (@lem74473) (@lem74472 A n y f PRG b)). Qed.
Lemma lem74475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem74476 {A : Type'} (n : nat) (y : A) (f : type1423 A) (PRG : type1597 A) (b : A) : (term389 A n y f PRG b) = (term390 A n y f PRG b).
Proof. exact (MK_COMB (@lem74475) (@lem74474 A n y f PRG b)). Qed.
Lemma lem74477 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term385 A y f PRG b n) = (term49 A y f PRG n b).
Proof. exact (eq_refl (term385 A y f PRG b n)). Qed.
Lemma lem74478 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : ((term384 A n y f PRG b) = (term385 A y f PRG b n)) = ((term375 A n y f PRG b) = (term49 A y f PRG n b)).
Proof. exact (MK_COMB (@lem74476 A n y f PRG b) (@lem74477 A y f PRG n b)). Qed.
Lemma lem74479 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) : (term375 A n y f PRG b) = (term49 A y f PRG n b).
Proof. exact (EQ_MP (@lem74478 A y f PRG n b) (@lem74468 A y f PRG b n)). Qed.
Lemma lem74484 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term377 A n y f PRG) = (term391 A y f PRG n).
Proof. exact (fun_ext (fun b : A => @lem74479 A y f PRG n b)). Qed.
Lemma lem74485 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74486 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term379 A n y f PRG) = (term392 A y f PRG n).
Proof. exact (MK_COMB (@lem74485 A) (@lem74484 A y f PRG n)). Qed.
Lemma lem74493 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term381 A n f PRG) = (term393 A f PRG n).
Proof. exact (fun_ext (fun y : A => @lem74486 A y f PRG n)). Qed.
Lemma lem74494 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74495 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term382 A n f PRG) = (term394 A f PRG n).
Proof. exact (MK_COMB (@lem74494 A) (@lem74493 A f PRG n)). Qed.
Lemma lem74496 {A : Type'} (n : nat) (f : type1423 A) (PRG : type1597 A) : (term394 A f PRG n) = (term382 A n f PRG).
Proof. exact (SYM (@lem74495 A f PRG n)). Qed.
Lemma lem74500 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (EQ_MP (@lem73471 A P) (@lem73470 A P)). Qed.
Lemma lem74501 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (@lem74500 A P). Qed.
Lemma lem74502 {A : Type'} (PRG : type1597 A) (n : nat) : (term395 A PRG n) = (term396 A PRG n).
Proof. exact (@lem74501 A (term397 A PRG n)). Qed.
Lemma lem74503 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term398 A PRG n y) = (PRG n y).
Proof. exact (eq_refl (term398 A PRG n y)). Qed.
Lemma lem74504 {A : Type'} (PRG : type1597 A) (n : nat) : (term399 A PRG n) = (term397 A PRG n).
Proof. exact (fun_ext (fun y : A => @lem74503 A PRG n y)). Qed.
Lemma lem74505 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74506 {A : Type'} (PRG : type1597 A) (n : nat) : (term395 A PRG n) = (term315 A PRG n).
Proof. exact (MK_COMB (@lem74505 A) (@lem74504 A PRG n)). Qed.
Lemma lem74507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem74508 {A : Type'} (PRG : type1597 A) (n : nat) : (term400 A PRG n) = (term401 A PRG n).
Proof. exact (MK_COMB (@lem74507) (@lem74506 A PRG n)). Qed.
Lemma lem74509 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term398 A PRG n y) = (PRG n y).
Proof. exact (eq_refl (term398 A PRG n y)). Qed.
Lemma lem74510 {A : Type'} (PRG : type1597 A) (n : nat) : (term399 A PRG n) = (term397 A PRG n).
Proof. exact (fun_ext (fun y : A => @lem74509 A PRG n y)). Qed.
Lemma lem74511 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74512 {A : Type'} (PRG : type1597 A) (n : nat) : (term402 A PRG n) = (term403 A PRG n).
Proof. exact (MK_COMB (@lem74511 A) (@lem74510 A PRG n)). Qed.
Lemma lem74513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74514 {A : Type'} (PRG : type1597 A) (n : nat) : (term404 A PRG n) = (term405 A PRG n).
Proof. exact (MK_COMB (@lem74513) (@lem74512 A PRG n)). Qed.
Lemma lem74515 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term398 A PRG n y) = (PRG n y).
Proof. exact (eq_refl (term398 A PRG n y)). Qed.
Lemma lem74516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74517 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term406 A PRG n y) = (term407 A PRG n y).
Proof. exact (MK_COMB (@lem74516) (@lem74515 A PRG n y)). Qed.
Lemma lem74518 {A : Type'} (PRG : type1597 A) (n : nat) (x' : A) : (term398 A PRG n x') = (PRG n x').
Proof. exact (eq_refl (term398 A PRG n x')). Qed.
Lemma lem74519 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) : (term408 A y PRG n x') = (term409 A y PRG n x').
Proof. exact (MK_COMB (@lem74517 A PRG n y) (@lem74518 A PRG n x')). Qed.
Lemma lem74520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74521 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) : (term410 A y PRG n x') = (term411 A y PRG n x').
Proof. exact (MK_COMB (@lem74520) (@lem74519 A y PRG n x')). Qed.
Lemma lem74522 {A : Type'} (y : A) (x' : A) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem74523 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) (x' : A) : (term412 A PRG n y x') = (term413 A PRG n y x').
Proof. exact (MK_COMB (@lem74521 A y PRG n x') (@lem74522 A y x')). Qed.
Lemma lem74524 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term414 A PRG n y) = (term415 A PRG n y).
Proof. exact (fun_ext (fun x' : A => @lem74523 A PRG n y x')). Qed.
Lemma lem74525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74526 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term416 A PRG n y) = (term417 A PRG n y).
Proof. exact (MK_COMB (@lem74525 A) (@lem74524 A PRG n y)). Qed.
Lemma lem74527 {A : Type'} (PRG : type1597 A) (n : nat) : (term418 A PRG n) = (term419 A PRG n).
Proof. exact (fun_ext (fun y : A => @lem74526 A PRG n y)). Qed.
Lemma lem74528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74529 {A : Type'} (PRG : type1597 A) (n : nat) : (term420 A PRG n) = (term421 A PRG n).
Proof. exact (MK_COMB (@lem74528 A) (@lem74527 A PRG n)). Qed.
Lemma lem74530 {A : Type'} (PRG : type1597 A) (n : nat) : (term396 A PRG n) = (term422 A PRG n).
Proof. exact (MK_COMB (@lem74514 A PRG n) (@lem74529 A PRG n)). Qed.
Lemma lem74531 {A : Type'} (PRG : type1597 A) (n : nat) : ((term395 A PRG n) = (term396 A PRG n)) = ((term315 A PRG n) = (term422 A PRG n)).
Proof. exact (MK_COMB (@lem74508 A PRG n) (@lem74530 A PRG n)). Qed.
Lemma lem74532 {A : Type'} (PRG : type1597 A) (n : nat) : (term315 A PRG n) = (term422 A PRG n).
Proof. exact (EQ_MP (@lem74531 A PRG n) (@lem74502 A PRG n)). Qed.
Lemma lem74553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74554 {A : Type'} (PRG : type1597 A) (n : nat) : (term317 A PRG n) = (term423 A PRG n).
Proof. exact (MK_COMB (@lem74553) (@lem74532 A PRG n)). Qed.
Lemma lem74556 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (EQ_MP (@lem73471 A P) (@lem73470 A P)). Qed.
Lemma lem74557 {A : Type'} (P : A -> Prop) : (term15 A P) = (term16 A P).
Proof. exact (@lem74556 A P). Qed.
Lemma lem74558 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term424 A f PRG n) = (term425 A f PRG n).
Proof. exact (@lem74557 A (term393 A f PRG n)). Qed.
Lemma lem74559 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term426 A f PRG n y) = (term392 A y f PRG n).
Proof. exact (eq_refl (term426 A f PRG n y)). Qed.
Lemma lem74560 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term427 A f PRG n) = (term393 A f PRG n).
Proof. exact (fun_ext (fun y : A => @lem74559 A y f PRG n)). Qed.
Lemma lem74561 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem74562 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term424 A f PRG n) = (term394 A f PRG n).
Proof. exact (MK_COMB (@lem74561 A) (@lem74560 A f PRG n)). Qed.
Lemma lem74563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem74564 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term428 A f PRG n) = (term429 A f PRG n).
Proof. exact (MK_COMB (@lem74563) (@lem74562 A f PRG n)). Qed.
Lemma lem74565 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term426 A f PRG n y) = (term392 A y f PRG n).
Proof. exact (eq_refl (term426 A f PRG n y)). Qed.
Lemma lem74566 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term427 A f PRG n) = (term393 A f PRG n).
Proof. exact (fun_ext (fun y : A => @lem74565 A y f PRG n)). Qed.
Lemma lem74567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem74568 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term430 A f PRG n) = (term431 A f PRG n).
Proof. exact (MK_COMB (@lem74567 A) (@lem74566 A f PRG n)). Qed.
Lemma lem74569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74570 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term432 A f PRG n) = (term433 A f PRG n).
Proof. exact (MK_COMB (@lem74569) (@lem74568 A f PRG n)). Qed.
Lemma lem74571 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term426 A f PRG n y) = (term392 A y f PRG n).
Proof. exact (eq_refl (term426 A f PRG n y)). Qed.
Lemma lem74572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74573 {A : Type'} (y : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term434 A f PRG n y) = (term435 A y f PRG n).
Proof. exact (MK_COMB (@lem74572) (@lem74571 A y f PRG n)). Qed.
Lemma lem74574 {A : Type'} (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term426 A f PRG n x') = (term392 A x' f PRG n).
Proof. exact (eq_refl (term426 A f PRG n x')). Qed.
Lemma lem74575 {A : Type'} (y : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term436 A y f PRG n x') = (term437 A y x' f PRG n).
Proof. exact (MK_COMB (@lem74573 A y f PRG n) (@lem74574 A x' f PRG n)). Qed.
Lemma lem74576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74577 {A : Type'} (y : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) : (term438 A y f PRG n x') = (term439 A y x' f PRG n).
Proof. exact (MK_COMB (@lem74576) (@lem74575 A y x' f PRG n)). Qed.
Lemma lem74578 {A : Type'} (y : A) (x' : A) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem74579 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (x' : A) : (term440 A f PRG n y x') = (term441 A f PRG n y x').
Proof. exact (MK_COMB (@lem74577 A y x' f PRG n) (@lem74578 A y x')). Qed.
Lemma lem74580 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) : (term442 A f PRG n y) = (term443 A f PRG n y).
Proof. exact (fun_ext (fun x' : A => @lem74579 A f PRG n y x')). Qed.
Lemma lem74581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74582 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) : (term444 A f PRG n y) = (term445 A f PRG n y).
Proof. exact (MK_COMB (@lem74581 A) (@lem74580 A f PRG n y)). Qed.
Lemma lem74583 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term446 A f PRG n) = (term447 A f PRG n).
Proof. exact (fun_ext (fun y : A => @lem74582 A f PRG n y)). Qed.
Lemma lem74584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem74585 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term448 A f PRG n) = (term449 A f PRG n).
Proof. exact (MK_COMB (@lem74584 A) (@lem74583 A f PRG n)). Qed.
Lemma lem74586 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term425 A f PRG n) = (term450 A f PRG n).
Proof. exact (MK_COMB (@lem74570 A f PRG n) (@lem74585 A f PRG n)). Qed.
Lemma lem74587 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : ((term424 A f PRG n) = (term425 A f PRG n)) = ((term394 A f PRG n) = (term450 A f PRG n)).
Proof. exact (MK_COMB (@lem74564 A f PRG n) (@lem74586 A f PRG n)). Qed.
Lemma lem74588 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term394 A f PRG n) = (term450 A f PRG n).
Proof. exact (EQ_MP (@lem74587 A f PRG n) (@lem74558 A f PRG n)). Qed.
Lemma lem74633 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term451 A f PRG n) = (term452 A f PRG n).
Proof. exact (MK_COMB (@lem74554 A PRG n) (@lem74588 A f PRG n)). Qed.
Lemma lem74636 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : (term452 A f PRG n) = (term451 A f PRG n).
Proof. exact (SYM (@lem74633 A f PRG n)). Qed.
Lemma lem74637 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term422 A PRG n) : term422 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74638 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term421 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74639 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term403 A PRG n) : term403 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74640 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : PRG n y.
Proof. exact (h1). Qed.
Lemma lem74641 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term437 A y' x' f PRG n) : term437 A y' x' f PRG n.
Proof. exact (h1). Qed.
Lemma lem74642 {A : Type'} (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term392 A x' f PRG n) : term392 A x' f PRG n.
Proof. exact (h1). Qed.
Lemma lem74643 {A : Type'} (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term392 A y' f PRG n) : term392 A y' f PRG n.
Proof. exact (h1). Qed.
Lemma lem74644 {A : Type'} (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term49 A y' f PRG n b) : term49 A y' f PRG n b.
Proof. exact (h1). Qed.
Lemma lem74645 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : PRG n b.
Proof. exact (h1). Qed.
Lemma lem74646 {A : Type'} (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : y' = (f b n)) : y' = (f b n).
Proof. exact (h1). Qed.
Lemma lem74647 {A : Type'} (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term49 A x' f PRG n b') : term49 A x' f PRG n b'.
Proof. exact (h1). Qed.
Lemma lem74648 {A : Type'} (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b') : PRG n b'.
Proof. exact (h1). Qed.
Lemma lem74649 {A : Type'} (x' : A) (f : type1423 A) (b' : A) (n : nat) (h1 : x' = (f b' n)) : x' = (f b' n).
Proof. exact (h1). Qed.
Lemma lem74737 {A : Type'} (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : y' = (f b n)) : y' = (f b n).
Proof. exact (h1). Qed.
Lemma lem74738 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem74739 {A : Type'} (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : y' = (f b n)) : (@eq A y') = (term453 A f b n).
Proof. exact (MK_COMB (@lem74738 A) (@lem74737 A y' f b n h1)). Qed.
Lemma lem74741 {A : Type'} (x' : A) (f : type1423 A) (b' : A) (n : nat) (h1 : x' = (f b' n)) : x' = (f b' n).
Proof. exact (h1). Qed.
Lemma lem74742 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : x' = (f b' n)) (h2 : y' = (f b n)) : (y' = x') = ((f b n) = (f b' n)).
Proof. exact (MK_COMB (@lem74739 A y' f b n h2) (@lem74741 A x' f b' n h1)). Qed.
Lemma lem74745 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : x' = (f b' n)) (h2 : y' = (f b n)) : ((f b n) = (f b' n)) = (y' = x').
Proof. exact (SYM (@lem74742 A x' b' y' f b n h1 h2)). Qed.
Lemma lem74746 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem74747 {A : Type'} (f : type1423 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem74748 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term421 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74749 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term454 A PRG n y.
Proof. exact (@lem74748 A PRG n h1 y). Qed.
Lemma lem74750 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term454 A PRG n y) = (term417 A PRG n y).
Proof. exact (eq_refl (term454 A PRG n y)). Qed.
Lemma lem74751 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term417 A PRG n y.
Proof. exact (EQ_MP (@lem74750 A PRG n y) (@lem74749 A y PRG n h1)). Qed.
Lemma lem74752 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term455 A PRG n y x'.
Proof. exact (@lem74751 A y PRG n h1 x'). Qed.
Lemma lem74753 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) (x' : A) : (term455 A PRG n y x') = (term413 A PRG n y x').
Proof. exact (eq_refl (term455 A PRG n y x')). Qed.
Lemma lem74754 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term413 A PRG n y x'.
Proof. exact (EQ_MP (@lem74753 A PRG n y x') (@lem74752 A y x' PRG n h1)). Qed.
Lemma lem74755 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) (h1 : term409 A y PRG n x') : term409 A y PRG n x'.
Proof. exact (h1). Qed.
Lemma lem74756 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) (h1 : term421 A PRG n) (h2 : term409 A y PRG n x') : y = x'.
Proof. exact (@lem74754 A y x' PRG n h1 (@lem74755 A y PRG n x' h2)). Qed.
Lemma lem74757 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) (h1 : term409 A y PRG n x') : term456 A PRG n y x'.
Proof. exact (fun h0 : term421 A PRG n => @lem74756 A y PRG n x' h0 h1). Qed.
Lemma lem74758 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term421 A PRG n.
Proof. exact (h1). Qed.
Lemma lem74759 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (x' : A) (h1 : term421 A PRG n) (h2 : term409 A y PRG n x') : y = x'.
Proof. exact (@lem74757 A y PRG n x' h2 (@lem74758 A PRG n h1)). Qed.
Lemma lem74760 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term413 A PRG n y x'.
Proof. exact (fun h0 : term409 A y PRG n x' => @lem74759 A y PRG n x' h1 h0). Qed.
Lemma lem74761 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term417 A PRG n y.
Proof. exact (fun x' : A => @lem74760 A y x' PRG n h1). Qed.
Lemma lem74762 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term421 A PRG n.
Proof. exact (fun y : A => @lem74761 A y PRG n h1). Qed.
Lemma lem74763 {A : Type'} (PRG : type1597 A) (n : nat) : term457 A PRG n.
Proof. exact (fun h0 : term421 A PRG n => @lem74762 A PRG n h0). Qed.
Lemma lem74764 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term421 A PRG n.
Proof. exact (@lem74763 A PRG n (@lem74638 A PRG n h1)). Qed.
Lemma lem74765 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term454 A PRG n y.
Proof. exact (@lem74764 A PRG n h1 y). Qed.
Lemma lem74766 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (term454 A PRG n y) = (term417 A PRG n y).
Proof. exact (eq_refl (term454 A PRG n y)). Qed.
Lemma lem74767 {A : Type'} (y : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term417 A PRG n y.
Proof. exact (EQ_MP (@lem74766 A PRG n y) (@lem74765 A y PRG n h1)). Qed.
Lemma lem74768 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term455 A PRG n y x'.
Proof. exact (@lem74767 A y PRG n h1 x'). Qed.
Lemma lem74769 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) (x' : A) : (term455 A PRG n y x') = (term413 A PRG n y x').
Proof. exact (eq_refl (term455 A PRG n y x')). Qed.
Lemma lem74772 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term413 A PRG n y x'.
Proof. exact (EQ_MP (@lem74769 A PRG n y x') (@lem74768 A y x' PRG n h1)). Qed.
Lemma lem74773 {A : Type'} (y : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term413 A PRG n y x'.
Proof. exact (@lem74772 A y x' PRG n h1). Qed.
Lemma lem74774 {A : Type'} (b : A) (b' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term413 A PRG n b b'.
Proof. exact (@lem74773 A b b' PRG n h1). Qed.
Lemma lem74798 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) : (PRG n y) = ((PRG n y) = True).
Proof. exact (@lem7 (PRG n y)). Qed.
Lemma lem74811 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem74812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem74811 A x). Qed.
Lemma lem74813 {A : Type'} (f : type1423 A) (y : A) (n : nat) : ((f y n) = (f y n)) = True.
Proof. exact (@lem74812 A (f y n)). Qed.
Lemma lem74814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74815 {A : Type'} (f : type1423 A) (y : A) (n : nat) : (term458 A f y n) = (and True).
Proof. exact (MK_COMB (@lem74814) (@lem74813 A f y n)). Qed.
Lemma lem74817 {A : Type'} (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : (PRG n y) = True.
Proof. exact (EQ_MP (@lem74798 A PRG n y) (@lem74640 A PRG n y h1)). Qed.
Lemma lem74818 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : (term70 A f PRG n y) = (True /\ True).
Proof. exact (MK_COMB (@lem74815 A f y n) (@lem74817 A PRG n y h1)). Qed.
Lemma lem74820 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem74821 : (True /\ True) = True.
Proof. exact (@lem74820 True). Qed.
Lemma lem74822 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : (term70 A f PRG n y) = True.
Proof. exact (TRANS (@lem74818 A f PRG n y h1) (@lem74821)). Qed.
Lemma lem74823 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : True = (term70 A f PRG n y).
Proof. exact (SYM (@lem74822 A f PRG n y h1)). Qed.
Lemma lem74824 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : term70 A f PRG n y.
Proof. exact (EQ_MP (@lem74823 A f PRG n y h1) (@lem0)). Qed.
Lemma lem74858 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) : (PRG n b) = ((PRG n b) = True).
Proof. exact (@lem7 (PRG n b)). Qed.
Lemma lem74860 {A : Type'} (PRG : type1597 A) (n : nat) (b' : A) : (PRG n b') = ((PRG n b') = True).
Proof. exact (@lem7 (PRG n b')). Qed.
Lemma lem74865 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : (PRG n b) = True.
Proof. exact (EQ_MP (@lem74858 A PRG n b) (@lem74645 A PRG n b h1)). Qed.
Lemma lem74866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem74867 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : (term407 A PRG n b) = (and True).
Proof. exact (MK_COMB (@lem74866) (@lem74865 A PRG n b h1)). Qed.
Lemma lem74869 {A : Type'} (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b') : (PRG n b') = True.
Proof. exact (EQ_MP (@lem74860 A PRG n b') (@lem74648 A PRG n b' h1)). Qed.
Lemma lem74870 {A : Type'} (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b) (h2 : PRG n b') : (term409 A b PRG n b') = (True /\ True).
Proof. exact (MK_COMB (@lem74867 A PRG n b h1) (@lem74869 A PRG n b' h2)). Qed.
Lemma lem74872 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem74873 : (True /\ True) = True.
Proof. exact (@lem74872 True). Qed.
Lemma lem74874 {A : Type'} (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b) (h2 : PRG n b') : (term409 A b PRG n b') = True.
Proof. exact (TRANS (@lem74870 A b PRG n b' h1 h2) (@lem74873)). Qed.
Lemma lem74875 {A : Type'} (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b) (h2 : PRG n b') : True = (term409 A b PRG n b').
Proof. exact (SYM (@lem74874 A b PRG n b' h1 h2)). Qed.
Lemma lem74876 {A : Type'} (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : PRG n b) (h2 : PRG n b') : term409 A b PRG n b'.
Proof. exact (EQ_MP (@lem74875 A b PRG n b' h1 h2) (@lem0)). Qed.
Lemma lem74877 {A : Type'} (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : PRG n b) (h3 : PRG n b') : b = b'.
Proof. exact (@lem74774 A b b' PRG n h1 (@lem74876 A b PRG n b' h2 h3)). Qed.
Lemma lem74878 {A : Type'} (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : PRG n b) (h3 : PRG n b') : (f b) = (f b').
Proof. exact (MK_COMB (@lem74747 A f) (@lem74877 A b PRG n b' h1 h2 h3)). Qed.
Lemma lem74879 {A : Type'} (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : PRG n b) (h3 : PRG n b') : (f b n) = (f b' n).
Proof. exact (MK_COMB (@lem74878 A f b PRG n b' h1 h2 h3) (@lem74746 n)). Qed.
Lemma lem74880 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : term459 A y f PRG n.
Proof. exact (ex_intro (term460 A y f PRG n) y (@lem74824 A f PRG n y h1)). Qed.
Lemma lem74882 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : x' = (f b' n)) (h3 : y' = (f b n)) (h4 : PRG n b) (h5 : PRG n b') : y' = x'.
Proof. exact (EQ_MP (@lem74745 A x' b' y' f b n h2 h3) (@lem74879 A f b PRG n b' h1 h4 h5)). Qed.
Lemma lem74883 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : PRG n y) : term431 A f PRG n.
Proof. exact (ex_intro (term393 A f PRG n) (f y n) (@lem74880 A f PRG n y h1)). Qed.
Lemma lem74884 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term437 A y' x' f PRG n) : term392 A x' f PRG n.
Proof. exact (proj2 (@lem74641 A y' x' f PRG n h1)). Qed.
Lemma lem74885 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term437 A y' x' f PRG n) : term392 A y' f PRG n.
Proof. exact (proj1 (@lem74641 A y' x' f PRG n h1)). Qed.
Lemma lem74886 {A : Type'} (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term49 A x' f PRG n b') : PRG n b'.
Proof. exact (proj2 (@lem74647 A x' f PRG n b' h1)). Qed.
Lemma lem74887 {A : Type'} (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term49 A x' f PRG n b') : x' = (f b' n).
Proof. exact (proj1 (@lem74647 A x' f PRG n b' h1)). Qed.
Lemma lem74888 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : x' = (f b' n)) (h3 : y' = (f b n)) (h4 : PRG n b) (h5 : PRG n b') : (PRG n b') = (y' = x').
Proof. exact (prop_ext (fun h6 : PRG n b' => @lem74882 A x' y' f b PRG n b' h1 h2 h3 h4 h5) (fun h6 : y' = x' => @lem74648 A PRG n b' h5)). Qed.
Lemma lem74889 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : x' = (f b' n)) (h3 : y' = (f b n)) (h4 : PRG n b) (h5 : PRG n b') : y' = x'.
Proof. exact (EQ_MP (@lem74888 A x' y' f b PRG n b' h1 h2 h3 h4 h5) (@lem74648 A PRG n b' h5)). Qed.
Lemma lem74890 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : x' = (f b' n)) (h3 : y' = (f b n)) (h4 : PRG n b) (h5 : PRG n b') : (x' = (f b' n)) = (y' = x').
Proof. exact (prop_ext (fun h6 : x' = (f b' n) => @lem74889 A x' y' f b PRG n b' h1 h2 h3 h4 h5) (fun h6 : y' = x' => @lem74649 A x' f b' n h2)). Qed.
Lemma lem74891 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (b : A) (PRG : type1597 A) (n : nat) (b' : A) (h1 : term421 A PRG n) (h2 : x' = (f b' n)) (h3 : y' = (f b n)) (h4 : PRG n b) (h5 : PRG n b') : y' = x'.
Proof. exact (EQ_MP (@lem74890 A x' y' f b PRG n b' h1 h2 h3 h4 h5) (@lem74649 A x' f b' n h2)). Qed.
Lemma lem74892 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term49 A x' f PRG n b') (h3 : x' = (f b' n)) (h4 : y' = (f b n)) (h5 : PRG n b) : (PRG n b') = (y' = x').
Proof. exact (prop_ext (fun h6 : PRG n b' => @lem74891 A x' y' f b PRG n b' h1 h3 h4 h5 h6) (fun h6 : y' = x' => @lem74886 A x' f PRG n b' h2)). Qed.
Lemma lem74893 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term49 A x' f PRG n b') (h3 : x' = (f b' n)) (h4 : y' = (f b n)) (h5 : PRG n b) : y' = x'.
Proof. exact (EQ_MP (@lem74892 A x' b' y' f PRG n b h1 h2 h3 h4 h5) (@lem74886 A x' f PRG n b' h2)). Qed.
Lemma lem74894 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term49 A x' f PRG n b') (h3 : y' = (f b n)) (h4 : PRG n b) : (x' = (f b' n)) = (y' = x').
Proof. exact (prop_ext (fun h5 : x' = (f b' n) => @lem74893 A x' b' y' f PRG n b h1 h2 h5 h3 h4) (fun h5 : y' = x' => @lem74887 A x' f PRG n b' h2)). Qed.
Lemma lem74895 {A : Type'} (x' : A) (b' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term49 A x' f PRG n b') (h3 : y' = (f b n)) (h4 : PRG n b) : y' = x'.
Proof. exact (EQ_MP (@lem74894 A x' b' y' f PRG n b h1 h2 h3 h4) (@lem74887 A x' f PRG n b' h2)). Qed.
Lemma lem74896 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : y' = (f b n)) (h4 : PRG n b) : y' = x'.
Proof. exact (ex_elim (@lem74642 A x' f PRG n h2) (fun b' : A => fun h0 : term391 A x' f PRG n b' => @lem74895 A x' b' y' f PRG n b h1 h0 h3 h4)). Qed.
Lemma lem74897 {A : Type'} (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term49 A y' f PRG n b) : PRG n b.
Proof. exact (proj2 (@lem74644 A y' f PRG n b h1)). Qed.
Lemma lem74898 {A : Type'} (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term49 A y' f PRG n b) : y' = (f b n).
Proof. exact (proj1 (@lem74644 A y' f PRG n b h1)). Qed.
Lemma lem74899 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : y' = (f b n)) (h4 : PRG n b) : (PRG n b) = (y' = x').
Proof. exact (prop_ext (fun h5 : PRG n b => @lem74896 A x' y' f PRG n b h1 h2 h3 h4) (fun h5 : y' = x' => @lem74645 A PRG n b h4)). Qed.
Lemma lem74900 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : y' = (f b n)) (h4 : PRG n b) : y' = x'.
Proof. exact (EQ_MP (@lem74899 A x' y' f PRG n b h1 h2 h3 h4) (@lem74645 A PRG n b h4)). Qed.
Lemma lem74901 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : y' = (f b n)) (h4 : PRG n b) : (y' = (f b n)) = (y' = x').
Proof. exact (prop_ext (fun h5 : y' = (f b n) => @lem74900 A x' y' f PRG n b h1 h2 h3 h4) (fun h5 : y' = x' => @lem74646 A y' f b n h3)). Qed.
Lemma lem74902 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : y' = (f b n)) (h4 : PRG n b) : y' = x'.
Proof. exact (EQ_MP (@lem74901 A x' y' f PRG n b h1 h2 h3 h4) (@lem74646 A y' f b n h3)). Qed.
Lemma lem74903 {A : Type'} (x' : A) (PRG : type1597 A) (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : term49 A y' f PRG n b) (h4 : y' = (f b n)) : (PRG n b) = (y' = x').
Proof. exact (prop_ext (fun h5 : PRG n b => @lem74902 A x' y' f PRG n b h1 h2 h4 h5) (fun h5 : y' = x' => @lem74897 A y' f PRG n b h3)). Qed.
Lemma lem74904 {A : Type'} (x' : A) (PRG : type1597 A) (y' : A) (f : type1423 A) (b : A) (n : nat) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : term49 A y' f PRG n b) (h4 : y' = (f b n)) : y' = x'.
Proof. exact (EQ_MP (@lem74903 A x' PRG y' f b n h1 h2 h3 h4) (@lem74897 A y' f PRG n b h3)). Qed.
Lemma lem74905 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : term49 A y' f PRG n b) : (y' = (f b n)) = (y' = x').
Proof. exact (prop_ext (fun h4 : y' = (f b n) => @lem74904 A x' PRG y' f b n h1 h2 h3 h4) (fun h4 : y' = x' => @lem74898 A y' f PRG n b h3)). Qed.
Lemma lem74906 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : term49 A y' f PRG n b) : y' = x'.
Proof. exact (EQ_MP (@lem74905 A x' y' f PRG n b h1 h2 h3) (@lem74898 A y' f PRG n b h3)). Qed.
Lemma lem74907 {A : Type'} (x' : A) (y' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term392 A x' f PRG n) (h3 : term392 A y' f PRG n) : y' = x'.
Proof. exact (ex_elim (@lem74643 A y' f PRG n h3) (fun b : A => fun h0 : term391 A y' f PRG n b => @lem74906 A x' y' f PRG n b h1 h2 h0)). Qed.
Lemma lem74908 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term392 A y' f PRG n) (h3 : term437 A y' x' f PRG n) : (term392 A x' f PRG n) = (y' = x').
Proof. exact (prop_ext (fun h4 : term392 A x' f PRG n => @lem74907 A x' y' f PRG n h1 h4 h2) (fun h4 : y' = x' => @lem74884 A y' x' f PRG n h3)). Qed.
Lemma lem74909 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term392 A y' f PRG n) (h3 : term437 A y' x' f PRG n) : y' = x'.
Proof. exact (EQ_MP (@lem74908 A y' x' f PRG n h1 h2 h3) (@lem74884 A y' x' f PRG n h3)). Qed.
Lemma lem74910 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term437 A y' x' f PRG n) : (term392 A y' f PRG n) = (y' = x').
Proof. exact (prop_ext (fun h3 : term392 A y' f PRG n => @lem74909 A y' x' f PRG n h1 h3 h2) (fun h3 : y' = x' => @lem74885 A y' x' f PRG n h2)). Qed.
Lemma lem74911 {A : Type'} (y' : A) (x' : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term437 A y' x' f PRG n) : y' = x'.
Proof. exact (EQ_MP (@lem74910 A y' x' f PRG n h1 h2) (@lem74885 A y' x' f PRG n h2)). Qed.
Lemma lem74912 {A : Type'} (f : type1423 A) (y' : A) (x' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term441 A f PRG n y' x'.
Proof. exact (fun h0 : term437 A y' x' f PRG n => @lem74911 A y' x' f PRG n h1 h0). Qed.
Lemma lem74917 {A : Type'} (f : type1423 A) (y' : A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term445 A f PRG n y'.
Proof. exact (fun x' : A => @lem74912 A f y' x' PRG n h1). Qed.
Lemma lem74922 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) : term449 A f PRG n.
Proof. exact (fun y' : A => @lem74917 A f y' PRG n h1). Qed.
Lemma lem74923 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : term421 A PRG n) (h2 : PRG n y) : term450 A f PRG n.
Proof. exact (conj (@lem74883 A f PRG n y h2) (@lem74922 A f PRG n h1)). Qed.
Lemma lem74924 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term422 A PRG n) : term421 A PRG n.
Proof. exact (proj2 (@lem74637 A PRG n h1)). Qed.
Lemma lem74925 {A : Type'} (PRG : type1597 A) (n : nat) (h1 : term422 A PRG n) : term403 A PRG n.
Proof. exact (proj1 (@lem74637 A PRG n h1)). Qed.
Lemma lem74926 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : term421 A PRG n) (h2 : PRG n y) : (term421 A PRG n) = (term450 A f PRG n).
Proof. exact (prop_ext (fun h3 : term421 A PRG n => @lem74923 A f PRG n y h1 h2) (fun h3 : term450 A f PRG n => @lem74638 A PRG n h1)). Qed.
Lemma lem74927 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (y : A) (h1 : term421 A PRG n) (h2 : PRG n y) : term450 A f PRG n.
Proof. exact (EQ_MP (@lem74926 A f PRG n y h1 h2) (@lem74638 A PRG n h1)). Qed.
Lemma lem74928 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term421 A PRG n) (h2 : term403 A PRG n) : term450 A f PRG n.
Proof. exact (ex_elim (@lem74639 A PRG n h2) (fun y : A => fun h0 : term397 A PRG n y => @lem74927 A f PRG n y h1 h0)). Qed.
Lemma lem74929 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term403 A PRG n) (h2 : term422 A PRG n) : (term421 A PRG n) = (term450 A f PRG n).
Proof. exact (prop_ext (fun h3 : term421 A PRG n => @lem74928 A f PRG n h3 h1) (fun h3 : term450 A f PRG n => @lem74924 A PRG n h2)). Qed.
Lemma lem74930 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term403 A PRG n) (h2 : term422 A PRG n) : term450 A f PRG n.
Proof. exact (EQ_MP (@lem74929 A f PRG n h1 h2) (@lem74924 A PRG n h2)). Qed.
Lemma lem74931 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term422 A PRG n) : (term403 A PRG n) = (term450 A f PRG n).
Proof. exact (prop_ext (fun h2 : term403 A PRG n => @lem74930 A f PRG n h2 h1) (fun h2 : term450 A f PRG n => @lem74925 A PRG n h1)). Qed.
Lemma lem74932 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term422 A PRG n) : term450 A f PRG n.
Proof. exact (EQ_MP (@lem74931 A f PRG n h1) (@lem74925 A PRG n h1)). Qed.
Lemma lem74933 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : term452 A f PRG n.
Proof. exact (fun h0 : term422 A PRG n => @lem74932 A f PRG n h0). Qed.
Lemma lem74934 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) : term451 A f PRG n.
Proof. exact (EQ_MP (@lem74636 A f PRG n) (@lem74933 A f PRG n)). Qed.
Lemma lem74935 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term315 A PRG n) : term394 A f PRG n.
Proof. exact (@lem74934 A f PRG n (@lem74237 A PRG n h1)). Qed.
Lemma lem74936 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term315 A PRG n) : term382 A n f PRG.
Proof. exact (EQ_MP (@lem74496 A n f PRG) (@lem74935 A f PRG n h1)). Qed.
Lemma lem74937 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term315 A PRG n) : term343 A e n f PRG.
Proof. exact (EQ_MP (@lem74460 A e n f PRG) (@lem74936 A f PRG n h1)). Qed.
Lemma lem74938 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term192 A e f PRG) (h2 : term315 A PRG n) : term319 A PRG n.
Proof. exact (EQ_MP (@lem74299 A n e f PRG h1) (@lem74937 A e f PRG n h2)). Qed.
Lemma lem74939 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term311 A PRG.
Proof. exact (EQ_MP (@lem74265 A e f PRG h1) (@lem74378 A e f PRG)). Qed.
Lemma lem74940 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term192 A e f PRG) (h2 : term315 A PRG n) : (term315 A PRG n) = (term319 A PRG n).
Proof. exact (prop_ext (fun h3 : term315 A PRG n => @lem74938 A e f PRG n h1 h2) (fun h3 : term319 A PRG n => @lem74237 A PRG n h2)). Qed.
Lemma lem74941 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (n : nat) (h1 : term192 A e f PRG) (h2 : term315 A PRG n) : term319 A PRG n.
Proof. exact (EQ_MP (@lem74940 A e f PRG n h1 h2) (@lem74237 A PRG n h2)). Qed.
Lemma lem74942 {A : Type'} (n : nat) (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term321 A PRG n.
Proof. exact (fun h0 : term315 A PRG n => @lem74941 A e f PRG n h1 h0). Qed.
Lemma lem74947 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term325 A PRG.
Proof. exact (fun n : nat => @lem74942 A n e f PRG h1). Qed.
Lemma lem74948 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term327 A PRG.
Proof. exact (conj (@lem74939 A e f PRG h1) (@lem74947 A e f PRG h1)). Qed.
Lemma lem74949 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term192 A e f PRG) : term307 A PRG.
Proof. exact (@lem74236 A PRG (@lem74948 A e f PRG h1)). Qed.
Lemma lem74953 {A B : Type'} (P : type1413 A B) : (term12 A B P) = (term13 A B P).
Proof. exact (EQ_MP (@lem73468 A B P) (@lem73467 A B P)). Qed.
Lemma lem74954 {A : Type'} (P : type1597 A) : (term307 A P) = (term461 A P).
Proof. exact (@lem74953 nat A P). Qed.
Lemma lem74955 {A : Type'} (PRG : type1597 A) : (term307 A PRG) = (term461 A PRG).
Proof. exact (@lem74954 A PRG). Qed.
Lemma lem74972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem74973 {A : Type'} (PRG : type1597 A) : (term462 A PRG) = (term463 A PRG).
Proof. exact (MK_COMB (@lem74972) (@lem74955 A PRG)). Qed.
Lemma lem74988 {A : Type'} (e : A) (f : type1423 A) : (term281 A e f) = (term281 A e f).
Proof. exact (eq_refl (term281 A e f)). Qed.
Lemma lem74989 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) : (term464 A PRG e f) = (term465 A PRG e f).
Proof. exact (MK_COMB (@lem74973 A PRG) (@lem74988 A e f)). Qed.
Lemma lem74992 {A : Type'} (PRG : type1597 A) (e : A) (f : type1423 A) : (term465 A PRG e f) = (term464 A PRG e f).
Proof. exact (SYM (@lem74989 A PRG e f)). Qed.
Lemma lem74993 {A : Type'} (PRG : type1597 A) (h1 : term461 A PRG) : term461 A PRG.
Proof. exact (h1). Qed.
Lemma lem74994 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term466 A PRG fn.
Proof. exact (h1). Qed.
Lemma lem74997 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) (h1 : (PRG n y) = ((fn n) = y)) : (PRG n y) = ((fn n) = y).
Proof. exact (h1). Qed.
Lemma lem74998 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) (h1 : (PRG n y) = ((fn n) = y)) : ((fn n) = y) = (PRG n y).
Proof. exact (SYM (@lem74997 A PRG fn n y h1)). Qed.
Lemma lem74999 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) (h1 : ((fn n) = y) = (PRG n y)) : ((fn n) = y) = (PRG n y).
Proof. exact (h1). Qed.
Lemma lem75000 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) (h1 : ((fn n) = y) = (PRG n y)) : (PRG n y) = ((fn n) = y).
Proof. exact (SYM (@lem74999 A fn PRG n y h1)). Qed.
Lemma lem75001 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) : ((PRG n y) = ((fn n) = y)) = (((fn n) = y) = (PRG n y)).
Proof. exact (prop_ext (fun h1 : (PRG n y) = ((fn n) = y) => @lem74998 A PRG fn n y h1) (fun h1 : ((fn n) = y) = (PRG n y) => @lem75000 A fn PRG n y h1)). Qed.
Lemma lem75002 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) : (term467 A PRG fn n) = (term468 A fn PRG n).
Proof. exact (fun_ext (fun y : A => @lem75001 A fn PRG n y)). Qed.
Lemma lem75003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem75004 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) : (term469 A PRG fn n) = (term470 A fn PRG n).
Proof. exact (MK_COMB (@lem75003 A) (@lem75002 A fn PRG n)). Qed.
Lemma lem75005 {A : Type'} (fn : nat -> A) (PRG : type1597 A) : (term471 A PRG fn) = (term472 A fn PRG).
Proof. exact (fun_ext (fun n : nat => @lem75004 A fn PRG n)). Qed.
Lemma lem75006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75007 {A : Type'} (fn : nat -> A) (PRG : type1597 A) : (term466 A PRG fn) = (term473 A fn PRG).
Proof. exact (MK_COMB (@lem75006) (@lem75005 A fn PRG)). Qed.
Lemma lem75008 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term473 A fn PRG.
Proof. exact (EQ_MP (@lem75007 A fn PRG) (@lem74994 A PRG fn h1)). Qed.
Lemma lem75018 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : PRG 0 e.
Proof. exact (proj1 (@lem74195 A e PRG f h1)). Qed.
Lemma lem75019 {A : Type'} (PRG : type1597 A) (e : A) : (PRG 0 e) = ((PRG 0 e) = True).
Proof. exact (@lem7 (PRG 0 e)). Qed.
Lemma lem75032 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term474 A fn PRG n.
Proof. exact (@lem75008 A PRG fn h1 n). Qed.
Lemma lem75033 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) : (term474 A fn PRG n) = (term470 A fn PRG n).
Proof. exact (eq_refl (term474 A fn PRG n)). Qed.
Lemma lem75034 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term470 A fn PRG n.
Proof. exact (EQ_MP (@lem75033 A fn PRG n) (@lem75032 A n PRG fn h1)). Qed.
Lemma lem75035 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term475 A fn PRG n y.
Proof. exact (@lem75034 A n PRG fn h1 y). Qed.
Lemma lem75036 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) : (term475 A fn PRG n y) = (((fn n) = y) = (PRG n y)).
Proof. exact (eq_refl (term475 A fn PRG n y)). Qed.
Lemma lem75041 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn n) = y) = (PRG n y).
Proof. exact (EQ_MP (@lem75036 A fn PRG n y) (@lem75035 A n y PRG fn h1)). Qed.
Lemma lem75042 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn n) = y) = (PRG n y).
Proof. exact (@lem75041 A n y PRG fn h1). Qed.
Lemma lem75043 {A : Type'} (e : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn 0) = e) = (PRG 0 e).
Proof. exact (@lem75042 A 0 e PRG fn h1). Qed.
Lemma lem75045 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : (PRG 0 e) = True.
Proof. exact (EQ_MP (@lem75019 A PRG e) (@lem75018 A e PRG f h1)). Qed.
Lemma lem75046 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : ((fn 0) = e) = True.
Proof. exact (TRANS (@lem75043 A e PRG fn h1) (@lem75045 A e PRG f h2)). Qed.
Lemma lem75047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75048 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : (term476 A fn e) = (and True).
Proof. exact (MK_COMB (@lem75047) (@lem75046 A fn e PRG f h1 h2)). Qed.
Lemma lem75054 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn n) = y) = (PRG n y).
Proof. exact (EQ_MP (@lem75036 A fn PRG n y) (@lem75035 A n y PRG fn h1)). Qed.
Lemma lem75055 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn n) = y) = (PRG n y).
Proof. exact (@lem75054 A n y PRG fn h1). Qed.
Lemma lem75056 {A : Type'} (f : type1423 A) (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((term477 A fn n) = (term478 A f fn n)) = (term479 A PRG f fn n).
Proof. exact (@lem75055 A (S n) (term478 A f fn n) PRG fn h1). Qed.
Lemma lem75057 {A : Type'} (f : type1423 A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : (term480 A f fn) = (term481 A PRG f fn).
Proof. exact (fun_ext (fun n : nat => @lem75056 A f n PRG fn h1)). Qed.
Lemma lem75058 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75059 {A : Type'} (f : type1423 A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : (term482 A f fn) = (term483 A PRG f fn).
Proof. exact (MK_COMB (@lem75058) (@lem75057 A f PRG fn h1)). Qed.
Lemma lem75064 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : (term275 A e f fn) = (term484 A PRG f fn).
Proof. exact (MK_COMB (@lem75048 A fn e PRG f h1 h2) (@lem75059 A f PRG fn h1)). Qed.
Lemma lem75066 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem75067 {A : Type'} (PRG : type1597 A) (f : type1423 A) (fn : nat -> A) : (term484 A PRG f fn) = (term483 A PRG f fn).
Proof. exact (@lem75066 (term483 A PRG f fn)). Qed.
Lemma lem75072 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : (term275 A e f fn) = (term483 A PRG f fn).
Proof. exact (TRANS (@lem75064 A fn e PRG f h1 h2) (@lem75067 A PRG f fn)). Qed.
Lemma lem75073 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : (term483 A PRG f fn) = (term275 A e f fn).
Proof. exact (SYM (@lem75072 A fn e PRG f h1 h2)). Qed.
Lemma lem75074 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term50 A PRG f.
Proof. exact (proj2 (@lem74195 A e PRG f h1)). Qed.
Lemma lem75075 {A : Type'} (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term50 A PRG f.
Proof. exact (h1). Qed.
Lemma lem75076 {A : Type'} (b : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term51 A PRG f b.
Proof. exact (@lem75075 A PRG f h1 b). Qed.
Lemma lem75077 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) : (term51 A PRG f b) = (term52 A PRG f b).
Proof. exact (eq_refl (term51 A PRG f b)). Qed.
Lemma lem75078 {A : Type'} (b : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term52 A PRG f b.
Proof. exact (EQ_MP (@lem75077 A PRG f b) (@lem75076 A b PRG f h1)). Qed.
Lemma lem75079 {A : Type'} (b : A) (n : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term53 A PRG f b n.
Proof. exact (@lem75078 A b PRG f h1 n). Qed.
Lemma lem75080 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term53 A PRG f b n) = (term54 A PRG f b n).
Proof. exact (eq_refl (term53 A PRG f b n)). Qed.
Lemma lem75081 {A : Type'} (b : A) (n : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term54 A PRG f b n.
Proof. exact (EQ_MP (@lem75080 A PRG f b n) (@lem75079 A b n PRG f h1)). Qed.
Lemma lem75082 {A : Type'} (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : PRG n b.
Proof. exact (h1). Qed.
Lemma lem75083 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term50 A PRG f) (h2 : PRG n b) : term55 A PRG f b n.
Proof. exact (@lem75081 A b n PRG f h1 (@lem75082 A PRG n b h2)). Qed.
Lemma lem75084 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : PRG n b) : term485 A PRG f b n.
Proof. exact (fun h0 : term50 A PRG f => @lem75083 A f PRG n b h0 h1). Qed.
Lemma lem75085 {A : Type'} (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term50 A PRG f.
Proof. exact (h1). Qed.
Lemma lem75086 {A : Type'} (f : type1423 A) (PRG : type1597 A) (n : nat) (b : A) (h1 : term50 A PRG f) (h2 : PRG n b) : term55 A PRG f b n.
Proof. exact (@lem75084 A f PRG n b h2 (@lem75085 A PRG f h1)). Qed.
Lemma lem75087 {A : Type'} (b : A) (n : nat) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term54 A PRG f b n.
Proof. exact (fun h0 : PRG n b => @lem75086 A f PRG n b h1 h0). Qed.
Lemma lem75088 {A : Type'} (b : A) (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term52 A PRG f b.
Proof. exact (fun n : nat => @lem75087 A b n PRG f h1). Qed.
Lemma lem75089 {A : Type'} (PRG : type1597 A) (f : type1423 A) (h1 : term50 A PRG f) : term50 A PRG f.
Proof. exact (fun b : A => @lem75088 A b PRG f h1). Qed.
Lemma lem75090 {A : Type'} (PRG : type1597 A) (f : type1423 A) : term486 A PRG f.
Proof. exact (fun h0 : term50 A PRG f => @lem75089 A PRG f h0). Qed.
Lemma lem75091 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term50 A PRG f.
Proof. exact (@lem75090 A PRG f (@lem75074 A e PRG f h1)). Qed.
Lemma lem75092 {A : Type'} (b : A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term51 A PRG f b.
Proof. exact (@lem75091 A e PRG f h1 b). Qed.
Lemma lem75093 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) : (term51 A PRG f b) = (term52 A PRG f b).
Proof. exact (eq_refl (term51 A PRG f b)). Qed.
Lemma lem75094 {A : Type'} (b : A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term52 A PRG f b.
Proof. exact (EQ_MP (@lem75093 A PRG f b) (@lem75092 A b e PRG f h1)). Qed.
Lemma lem75095 {A : Type'} (b : A) (n : nat) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term53 A PRG f b n.
Proof. exact (@lem75094 A b e PRG f h1 n). Qed.
Lemma lem75096 {A : Type'} (PRG : type1597 A) (f : type1423 A) (b : A) (n : nat) : (term53 A PRG f b n) = (term54 A PRG f b n).
Proof. exact (eq_refl (term53 A PRG f b n)). Qed.
Lemma lem75099 {A : Type'} (b : A) (n : nat) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term54 A PRG f b n.
Proof. exact (EQ_MP (@lem75096 A PRG f b n) (@lem75095 A b n e PRG f h1)). Qed.
Lemma lem75100 {A : Type'} (b : A) (n : nat) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term54 A PRG f b n.
Proof. exact (@lem75099 A b n e PRG f h1). Qed.
Lemma lem75101 {A : Type'} (fn : nat -> A) (n : nat) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term487 A PRG f fn n.
Proof. exact (@lem75100 A (fn n) n e PRG f h1). Qed.
Lemma lem75104 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) (h1 : ((fn n) = y) = (PRG n y)) : ((fn n) = y) = (PRG n y).
Proof. exact (h1). Qed.
Lemma lem75105 {A : Type'} (fn : nat -> A) (PRG : type1597 A) (n : nat) (y : A) (h1 : ((fn n) = y) = (PRG n y)) : (PRG n y) = ((fn n) = y).
Proof. exact (SYM (@lem75104 A fn PRG n y h1)). Qed.
Lemma lem75106 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) (h1 : (PRG n y) = ((fn n) = y)) : (PRG n y) = ((fn n) = y).
Proof. exact (h1). Qed.
Lemma lem75107 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) (h1 : (PRG n y) = ((fn n) = y)) : ((fn n) = y) = (PRG n y).
Proof. exact (SYM (@lem75106 A PRG fn n y h1)). Qed.
Lemma lem75108 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) : (((fn n) = y) = (PRG n y)) = ((PRG n y) = ((fn n) = y)).
Proof. exact (prop_ext (fun h1 : ((fn n) = y) = (PRG n y) => @lem75105 A fn PRG n y h1) (fun h1 : (PRG n y) = ((fn n) = y) => @lem75107 A PRG fn n y h1)). Qed.
Lemma lem75109 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) : (term468 A fn PRG n) = (term467 A PRG fn n).
Proof. exact (fun_ext (fun y : A => @lem75108 A PRG fn n y)). Qed.
Lemma lem75110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem75111 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) : (term470 A fn PRG n) = (term469 A PRG fn n).
Proof. exact (MK_COMB (@lem75110 A) (@lem75109 A PRG fn n)). Qed.
Lemma lem75112 {A : Type'} (PRG : type1597 A) (fn : nat -> A) : (term472 A fn PRG) = (term471 A PRG fn).
Proof. exact (fun_ext (fun n : nat => @lem75111 A PRG fn n)). Qed.
Lemma lem75113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75114 {A : Type'} (PRG : type1597 A) (fn : nat -> A) : (term473 A fn PRG) = (term466 A PRG fn).
Proof. exact (MK_COMB (@lem75113) (@lem75112 A PRG fn)). Qed.
Lemma lem75115 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term466 A PRG fn.
Proof. exact (EQ_MP (@lem75114 A PRG fn) (@lem75008 A PRG fn h1)). Qed.
Lemma lem75116 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term488 A PRG fn n.
Proof. exact (@lem75115 A PRG fn h1 n). Qed.
Lemma lem75117 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) : (term488 A PRG fn n) = (term469 A PRG fn n).
Proof. exact (eq_refl (term488 A PRG fn n)). Qed.
Lemma lem75118 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term469 A PRG fn n.
Proof. exact (EQ_MP (@lem75117 A PRG fn n) (@lem75116 A n PRG fn h1)). Qed.
Lemma lem75119 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term489 A PRG fn n y.
Proof. exact (@lem75118 A n PRG fn h1 y). Qed.
Lemma lem75120 {A : Type'} (PRG : type1597 A) (fn : nat -> A) (n : nat) (y : A) : (term489 A PRG fn n y) = ((PRG n y) = ((fn n) = y)).
Proof. exact (eq_refl (term489 A PRG fn n y)). Qed.
Lemma lem75123 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : (PRG n y) = ((fn n) = y).
Proof. exact (EQ_MP (@lem75120 A PRG fn n y) (@lem75119 A n y PRG fn h1)). Qed.
Lemma lem75124 {A : Type'} (n : nat) (y : A) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : (PRG n y) = ((fn n) = y).
Proof. exact (@lem75123 A n y PRG fn h1). Qed.
Lemma lem75125 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : (term490 A PRG fn n) = ((fn n) = (fn n)).
Proof. exact (@lem75124 A n (fn n) PRG fn h1). Qed.
Lemma lem75126 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : ((fn n) = (fn n)) = (term490 A PRG fn n).
Proof. exact (SYM (@lem75125 A n PRG fn h1)). Qed.
Lemma lem75127 {A : Type'} (fn : nat -> A) (n : nat) : (fn n) = (fn n).
Proof. exact (eq_refl (fn n)). Qed.
Lemma lem75128 {A : Type'} (n : nat) (PRG : type1597 A) (fn : nat -> A) (h1 : term466 A PRG fn) : term490 A PRG fn n.
Proof. exact (EQ_MP (@lem75126 A n PRG fn h1) (@lem75127 A fn n)). Qed.
Lemma lem75129 {A : Type'} (n : nat) (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : term479 A PRG f fn n.
Proof. exact (@lem75101 A fn n e PRG f h2 (@lem75128 A n PRG fn h1)). Qed.
Lemma lem75134 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : term483 A PRG f fn.
Proof. exact (fun n : nat => @lem75129 A n fn e PRG f h1 h2). Qed.
Lemma lem75135 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : term275 A e f fn.
Proof. exact (EQ_MP (@lem75073 A fn e PRG f h1 h2) (@lem75134 A fn e PRG f h1 h2)). Qed.
Lemma lem75136 {A : Type'} (fn : nat -> A) (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term466 A PRG fn) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (ex_intro (term273 A e f) fn (@lem75135 A fn e PRG f h1 h2)). Qed.
Lemma lem75137 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term461 A PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (ex_elim (@lem74993 A PRG h1) (fun fn : nat -> A => fun h0 : term491 A PRG fn => @lem75136 A fn e PRG f h0 h2)). Qed.
Lemma lem75138 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term465 A PRG e f.
Proof. exact (fun h0 : term461 A PRG => @lem75137 A e PRG f h0 h1). Qed.
Lemma lem75139 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term464 A PRG e f.
Proof. exact (EQ_MP (@lem74992 A PRG e f) (@lem75138 A e PRG f h1)). Qed.
Lemma lem75140 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term307 A PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (@lem75139 A e PRG f h2 (@lem74213 A PRG h1)). Qed.
Lemma lem75141 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term192 A e f PRG) (h2 : term95 A e PRG f) : (term307 A PRG) = (term281 A e f).
Proof. exact (prop_ext (fun h3 : term307 A PRG => @lem75140 A e PRG f h3 h2) (fun h3 : term281 A e f => @lem74949 A e f PRG h1)). Qed.
Lemma lem75142 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term192 A e f PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (EQ_MP (@lem75141 A e PRG f h1 h2) (@lem74949 A e f PRG h1)). Qed.
Lemma lem75143 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term199 A e f PRG) : term192 A e f PRG.
Proof. exact (proj2 (@lem74196 A e f PRG h1)). Qed.
Lemma lem75145 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term199 A e f PRG) (h2 : term95 A e PRG f) : (term192 A e f PRG) = (term281 A e f).
Proof. exact (prop_ext (fun h3 : term192 A e f PRG => @lem75142 A e PRG f h3 h2) (fun h3 : term281 A e f => @lem75143 A e f PRG h1)). Qed.
Lemma lem75146 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term199 A e f PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (EQ_MP (@lem75145 A e PRG f h1 h2) (@lem75143 A e f PRG h1)). Qed.
Lemma lem75147 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term95 A e PRG f) : term492 A PRG e f.
Proof. exact (fun h0 : term199 A e f PRG => @lem75146 A e PRG f h0 h1). Qed.
Lemma lem75148 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term200 A e f PRG) : term199 A e f PRG.
Proof. exact (proj2 (@lem74193 A e f PRG h1)). Qed.
Lemma lem75149 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term200 A e f PRG) : term95 A e PRG f.
Proof. exact (proj1 (@lem74193 A e f PRG h1)). Qed.
Lemma lem75150 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term199 A e f PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (@lem75147 A e PRG f h2 (@lem74194 A e f PRG h1)). Qed.
Lemma lem75151 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term199 A e f PRG) (h2 : term95 A e PRG f) : (term95 A e PRG f) = (term281 A e f).
Proof. exact (prop_ext (fun h3 : term95 A e PRG f => @lem75150 A e PRG f h1 h2) (fun h3 : term281 A e f => @lem74195 A e PRG f h2)). Qed.
Lemma lem75152 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term199 A e f PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (EQ_MP (@lem75151 A e PRG f h1 h2) (@lem74195 A e PRG f h2)). Qed.
Lemma lem75153 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term200 A e f PRG) (h2 : term95 A e PRG f) : (term199 A e f PRG) = (term281 A e f).
Proof. exact (prop_ext (fun h3 : term199 A e f PRG => @lem75152 A e PRG f h3 h2) (fun h3 : term281 A e f => @lem75148 A e f PRG h1)). Qed.
Lemma lem75154 {A : Type'} (e : A) (PRG : type1597 A) (f : type1423 A) (h1 : term200 A e f PRG) (h2 : term95 A e PRG f) : term281 A e f.
Proof. exact (EQ_MP (@lem75153 A e PRG f h1 h2) (@lem75148 A e f PRG h1)). Qed.
Lemma lem75155 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term200 A e f PRG) : (term95 A e PRG f) = (term281 A e f).
Proof. exact (prop_ext (fun h2 : term95 A e PRG f => @lem75154 A e PRG f h1 h2) (fun h2 : term281 A e f => @lem75149 A e f PRG h1)). Qed.
Lemma lem75156 {A : Type'} (e : A) (f : type1423 A) (PRG : type1597 A) (h1 : term200 A e f PRG) : term281 A e f.
Proof. exact (EQ_MP (@lem75155 A e f PRG h1) (@lem75149 A e f PRG h1)). Qed.
Lemma lem75157 {A : Type'} (e : A) (f : type1423 A) (h1 : term268 A e f) : term281 A e f.
Proof. exact (ex_elim (@lem74192 A e f h1) (fun PRG : type1597 A => fun h0 : term262 A e f PRG => @lem75156 A e f PRG h0)). Qed.
Lemma lem75158 {A : Type'} (e : A) (f : type1423 A) : term493 A e f.
Proof. exact (fun h0 : term268 A e f => @lem75157 A e f h0). Qed.
Lemma lem75159 {A : Type'} (e : A) (f : type1423 A) : term281 A e f.
Proof. exact (@lem75158 A e f (@lem74153 A e f)). Qed.
Lemma lem75160 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term287 A fn e f x') : term287 A fn e f x'.
Proof. exact (h1). Qed.
Lemma lem75161 {A : Type'} (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term275 A e f x') : term275 A e f x'.
Proof. exact (h1). Qed.
Lemma lem75162 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) (h1 : term275 A e f fn) : term275 A e f fn.
Proof. exact (h1). Qed.
Lemma lem75163 {A : Type'} (f : type1423 A) (fn : nat -> A) (h1 : term482 A f fn) : term482 A f fn.
Proof. exact (h1). Qed.
Lemma lem75164 {A : Type'} (fn : nat -> A) (e : A) (h1 : (fn 0) = e) : (fn 0) = e.
Proof. exact (h1). Qed.
Lemma lem75165 {A : Type'} (f : type1423 A) (x' : nat -> A) (h1 : term482 A f x') : term482 A f x'.
Proof. exact (h1). Qed.
Lemma lem75166 {A : Type'} (x' : nat -> A) (e : A) (h1 : (x' 0) = e) : (x' 0) = e.
Proof. exact (h1). Qed.
Lemma lem75170 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term10 A B f g).
Proof. exact (EQ_MP (@lem73465 A B f g) (@lem73464 A B f g)). Qed.
Lemma lem75171 {A : Type'} (f : nat -> A) (g : nat -> A) : (f = g) = (term494 A f g).
Proof. exact (@lem75170 nat A f g). Qed.
Lemma lem75172 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (fn = x') = (term494 A fn x').
Proof. exact (@lem75171 A fn x'). Qed.
Lemma lem75173 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term494 A fn x') = (fn = x').
Proof. exact (SYM (@lem75172 A fn x')). Qed.
Lemma lem75175 (P : nat -> Prop) : term2 P.
Proof. exact (EQ_MP (@lem73459 P) (@lem73458 P)). Qed.
Lemma lem75176 {A : Type'} (fn : nat -> A) (x' : nat -> A) : term495 A fn x'.
Proof. exact (@lem75175 (term496 A fn x')). Qed.
Lemma lem75177 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term497 A fn x') = ((fn 0) = (x' 0)).
Proof. exact (eq_refl (term497 A fn x')). Qed.
Lemma lem75178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75179 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term498 A fn x') = (term499 A fn x').
Proof. exact (MK_COMB (@lem75178) (@lem75177 A fn x')). Qed.
Lemma lem75180 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term500 A fn x' x) = ((fn x) = (x' x)).
Proof. exact (eq_refl (term500 A fn x' x)). Qed.
Lemma lem75181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem75182 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term501 A fn x' x) = (term502 A fn x' x).
Proof. exact (MK_COMB (@lem75181) (@lem75180 A fn x' x)). Qed.
Lemma lem75183 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term503 A fn x' x) = ((term477 A fn x) = (term477 A x' x)).
Proof. exact (eq_refl (term503 A fn x' x)). Qed.
Lemma lem75184 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term504 A fn x' x) = (term505 A fn x' x).
Proof. exact (MK_COMB (@lem75182 A fn x' x) (@lem75183 A fn x' x)). Qed.
Lemma lem75185 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term506 A fn x') = (term507 A fn x').
Proof. exact (fun_ext (fun x : nat => @lem75184 A fn x' x)). Qed.
Lemma lem75186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75187 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term508 A fn x') = (term509 A fn x').
Proof. exact (MK_COMB (@lem75186) (@lem75185 A fn x')). Qed.
Lemma lem75188 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term510 A fn x') = (term511 A fn x').
Proof. exact (MK_COMB (@lem75179 A fn x') (@lem75187 A fn x')). Qed.
Lemma lem75189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem75190 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term512 A fn x') = (term513 A fn x').
Proof. exact (MK_COMB (@lem75189) (@lem75188 A fn x')). Qed.
Lemma lem75191 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term500 A fn x' x) = ((fn x) = (x' x)).
Proof. exact (eq_refl (term500 A fn x' x)). Qed.
Lemma lem75192 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term514 A fn x') = (term496 A fn x').
Proof. exact (fun_ext (fun x : nat => @lem75191 A fn x' x)). Qed.
Lemma lem75193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75194 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term515 A fn x') = (term494 A fn x').
Proof. exact (MK_COMB (@lem75193) (@lem75192 A fn x')). Qed.
Lemma lem75195 {A : Type'} (fn : nat -> A) (x' : nat -> A) : (term495 A fn x') = (term516 A fn x').
Proof. exact (MK_COMB (@lem75190 A fn x') (@lem75194 A fn x')). Qed.
Lemma lem75196 {A : Type'} (fn : nat -> A) (x' : nat -> A) : term516 A fn x'.
Proof. exact (EQ_MP (@lem75195 A fn x') (@lem75176 A fn x')). Qed.
Lemma lem75197 {A : Type'} (n : nat) (f : type1423 A) (fn : nat -> A) (h1 : term482 A f fn) : term517 A f fn n.
Proof. exact (@lem75163 A f fn h1 n). Qed.
Lemma lem75198 {A : Type'} (f : type1423 A) (fn : nat -> A) (n : nat) : (term517 A f fn n) = ((term477 A fn n) = (term478 A f fn n)).
Proof. exact (eq_refl (term517 A f fn n)). Qed.
Lemma lem75200 {A : Type'} (n : nat) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f x') : term517 A f x' n.
Proof. exact (@lem75165 A f x' h1 n). Qed.
Lemma lem75201 {A : Type'} (f : type1423 A) (x' : nat -> A) (n : nat) : (term517 A f x' n) = ((term477 A x' n) = (term478 A f x' n)).
Proof. exact (eq_refl (term517 A f x' n)). Qed.
Lemma lem75208 {A : Type'} (fn : nat -> A) (e : A) (h1 : (fn 0) = e) : (fn 0) = e.
Proof. exact (h1). Qed.
Lemma lem75209 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem75210 {A : Type'} (fn : nat -> A) (e : A) (h1 : (fn 0) = e) : (term518 A fn) = (@eq A e).
Proof. exact (MK_COMB (@lem75209 A) (@lem75208 A fn e h1)). Qed.
Lemma lem75212 {A : Type'} (x' : nat -> A) (e : A) (h1 : (x' 0) = e) : (x' 0) = e.
Proof. exact (h1). Qed.
Lemma lem75213 {A : Type'} (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : (fn 0) = e) (h2 : (x' 0) = e) : ((fn 0) = (x' 0)) = (e = e).
Proof. exact (MK_COMB (@lem75210 A fn e h1) (@lem75212 A x' e h2)). Qed.
Lemma lem75215 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem75216 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem75215 A x). Qed.
Lemma lem75217 {A : Type'} (e : A) : (e = e) = True.
Proof. exact (@lem75216 A e). Qed.
Lemma lem75218 {A : Type'} (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : (fn 0) = e) (h2 : (x' 0) = e) : ((fn 0) = (x' 0)) = True.
Proof. exact (TRANS (@lem75213 A fn x' e h1 h2) (@lem75217 A e)). Qed.
Lemma lem75219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75220 {A : Type'} (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : (fn 0) = e) (h2 : (x' 0) = e) : (term499 A fn x') = (and True).
Proof. exact (MK_COMB (@lem75219) (@lem75218 A fn x' e h1 h2)). Qed.
Lemma lem75234 {A : Type'} (n : nat) (f : type1423 A) (fn : nat -> A) (h1 : term482 A f fn) : (term477 A fn n) = (term478 A f fn n).
Proof. exact (EQ_MP (@lem75198 A f fn n) (@lem75197 A n f fn h1)). Qed.
Lemma lem75235 {A : Type'} (x : nat) (f : type1423 A) (fn : nat -> A) (h1 : term482 A f fn) : (term477 A fn x) = (term478 A f fn x).
Proof. exact (@lem75234 A x f fn h1). Qed.
Lemma lem75236 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem75237 {A : Type'} (x : nat) (f : type1423 A) (fn : nat -> A) (h1 : term482 A f fn) : (term519 A fn x) = (term520 A f fn x).
Proof. exact (MK_COMB (@lem75236 A) (@lem75235 A x f fn h1)). Qed.
Lemma lem75239 {A : Type'} (n : nat) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f x') : (term477 A x' n) = (term478 A f x' n).
Proof. exact (EQ_MP (@lem75201 A f x' n) (@lem75200 A n f x' h1)). Qed.
Lemma lem75240 {A : Type'} (x : nat) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f x') : (term477 A x' x) = (term478 A f x' x).
Proof. exact (@lem75239 A x f x' h1). Qed.
Lemma lem75241 {A : Type'} (x : nat) (fn : nat -> A) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f fn) (h2 : term482 A f x') : ((term477 A fn x) = (term477 A x' x)) = ((term478 A f fn x) = (term478 A f x' x)).
Proof. exact (MK_COMB (@lem75237 A x f fn h1) (@lem75240 A x f x' h2)). Qed.
Lemma lem75244 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) : (term502 A fn x' x) = (term502 A fn x' x).
Proof. exact (eq_refl (term502 A fn x' x)). Qed.
Lemma lem75245 {A : Type'} (x : nat) (fn : nat -> A) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f fn) (h2 : term482 A f x') : (term505 A fn x' x) = (term521 A fn f x' x).
Proof. exact (MK_COMB (@lem75244 A fn x' x) (@lem75241 A x fn f x' h1 h2)). Qed.
Lemma lem75250 {A : Type'} (fn : nat -> A) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f fn) (h2 : term482 A f x') : (term507 A fn x') = (term522 A fn f x').
Proof. exact (fun_ext (fun x : nat => @lem75245 A x fn f x' h1 h2)). Qed.
Lemma lem75251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem75252 {A : Type'} (fn : nat -> A) (f : type1423 A) (x' : nat -> A) (h1 : term482 A f fn) (h2 : term482 A f x') : (term509 A fn x') = (term523 A fn f x').
Proof. exact (MK_COMB (@lem75251) (@lem75250 A fn f x' h1 h2)). Qed.
Lemma lem75257 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : (term511 A fn x') = (term524 A fn f x').
Proof. exact (MK_COMB (@lem75220 A fn x' e h3 h4) (@lem75252 A fn f x' h1 h2)). Qed.
Lemma lem75259 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem75260 {A : Type'} (fn : nat -> A) (f : type1423 A) (x' : nat -> A) : (term524 A fn f x') = (term523 A fn f x').
Proof. exact (@lem75259 (term523 A fn f x')). Qed.
Lemma lem75273 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : (term511 A fn x') = (term523 A fn f x').
Proof. exact (TRANS (@lem75257 A f fn x' e h1 h2 h3 h4) (@lem75260 A fn f x')). Qed.
Lemma lem75274 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : (term523 A fn f x') = (term511 A fn x').
Proof. exact (SYM (@lem75273 A f fn x' e h1 h2 h3 h4)). Qed.
Lemma lem75275 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (fn x) = (x' x).
Proof. exact (h1). Qed.
Lemma lem75285 {A : Type'} (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (fn x) = (x' x).
Proof. exact (h1). Qed.
Lemma lem75286 {A : Type'} (f : type1423 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem75287 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (term525 A f fn x) = (term525 A f x' x).
Proof. exact (MK_COMB (@lem75286 A f) (@lem75285 A fn x' x h1)). Qed.
Lemma lem75288 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem75289 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (term478 A f fn x) = (term478 A f x' x).
Proof. exact (MK_COMB (@lem75287 A f fn x' x h1) (@lem75288 x)). Qed.
Lemma lem75290 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem75291 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (term520 A f fn x) = (term520 A f x' x).
Proof. exact (MK_COMB (@lem75290 A) (@lem75289 A f fn x' x h1)). Qed.
Lemma lem75292 {A : Type'} (f : type1423 A) (x' : nat -> A) (x : nat) : (term478 A f x' x) = (term478 A f x' x).
Proof. exact (eq_refl (term478 A f x' x)). Qed.
Lemma lem75293 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : ((term478 A f fn x) = (term478 A f x' x)) = ((term478 A f x' x) = (term478 A f x' x)).
Proof. exact (MK_COMB (@lem75291 A f fn x' x h1) (@lem75292 A f x' x)). Qed.
Lemma lem75295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem75296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem75295 A x). Qed.
Lemma lem75297 {A : Type'} (f : type1423 A) (x' : nat -> A) (x : nat) : ((term478 A f x' x) = (term478 A f x' x)) = True.
Proof. exact (@lem75296 A (term478 A f x' x)). Qed.
Lemma lem75298 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : ((term478 A f fn x) = (term478 A f x' x)) = True.
Proof. exact (TRANS (@lem75293 A f fn x' x h1) (@lem75297 A f x' x)). Qed.
Lemma lem75299 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : True = ((term478 A f fn x) = (term478 A f x' x)).
Proof. exact (SYM (@lem75298 A f fn x' x h1)). Qed.
Lemma lem75300 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (term478 A f fn x) = (term478 A f x' x).
Proof. exact (EQ_MP (@lem75299 A f fn x' x h1) (@lem0)). Qed.
Lemma lem75301 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : ((fn x) = (x' x)) = ((term478 A f fn x) = (term478 A f x' x)).
Proof. exact (prop_ext (fun h2 : (fn x) = (x' x) => @lem75300 A f fn x' x h1) (fun h2 : (term478 A f fn x) = (term478 A f x' x) => @lem75275 A fn x' x h1)). Qed.
Lemma lem75302 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (x : nat) (h1 : (fn x) = (x' x)) : (term478 A f fn x) = (term478 A f x' x).
Proof. exact (EQ_MP (@lem75301 A f fn x' x h1) (@lem75275 A fn x' x h1)). Qed.
Lemma lem75303 {A : Type'} (fn : nat -> A) (f : type1423 A) (x' : nat -> A) (x : nat) : term521 A fn f x' x.
Proof. exact (fun h0 : (fn x) = (x' x) => @lem75302 A f fn x' x h0). Qed.
Lemma lem75308 {A : Type'} (fn : nat -> A) (f : type1423 A) (x' : nat -> A) : term523 A fn f x'.
Proof. exact (fun x : nat => @lem75303 A fn f x' x). Qed.
Lemma lem75309 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : term511 A fn x'.
Proof. exact (EQ_MP (@lem75274 A f fn x' e h1 h2 h3 h4) (@lem75308 A fn f x')). Qed.
Lemma lem75310 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : term494 A fn x'.
Proof. exact (@lem75196 A fn x' (@lem75309 A f fn x' e h1 h2 h3 h4)). Qed.
Lemma lem75311 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75173 A fn x') (@lem75310 A f fn x' e h1 h2 h3 h4)). Qed.
Lemma lem75312 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term287 A fn e f x') : term275 A e f x'.
Proof. exact (proj2 (@lem75160 A fn e f x' h1)). Qed.
Lemma lem75313 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term287 A fn e f x') : term275 A e f fn.
Proof. exact (proj1 (@lem75160 A fn e f x' h1)). Qed.
Lemma lem75314 {A : Type'} (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term275 A e f x') : term482 A f x'.
Proof. exact (proj2 (@lem75161 A e f x' h1)). Qed.
Lemma lem75315 {A : Type'} (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term275 A e f x') : (x' 0) = e.
Proof. exact (proj1 (@lem75161 A e f x' h1)). Qed.
Lemma lem75316 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : (term482 A f x') = (fn = x').
Proof. exact (prop_ext (fun h5 : term482 A f x' => @lem75311 A f fn x' e h1 h2 h3 h4) (fun h5 : fn = x' => @lem75165 A f x' h2)). Qed.
Lemma lem75317 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75316 A f fn x' e h1 h2 h3 h4) (@lem75165 A f x' h2)). Qed.
Lemma lem75318 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : ((x' 0) = e) = (fn = x').
Proof. exact (prop_ext (fun h5 : (x' 0) = e => @lem75317 A f fn x' e h1 h2 h3 h4) (fun h5 : fn = x' => @lem75166 A x' e h4)). Qed.
Lemma lem75319 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term482 A f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75318 A f fn x' e h1 h2 h3 h4) (@lem75166 A x' e h4)). Qed.
Lemma lem75320 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : (term482 A f x') = (fn = x').
Proof. exact (prop_ext (fun h5 : term482 A f x' => @lem75319 A f fn x' e h1 h5 h3 h4) (fun h5 : fn = x' => @lem75314 A e f x' h2)). Qed.
Lemma lem75321 {A : Type'} (f : type1423 A) (fn : nat -> A) (x' : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) (h4 : (x' 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75320 A f fn x' e h1 h2 h3 h4) (@lem75314 A e f x' h2)). Qed.
Lemma lem75322 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : ((x' 0) = e) = (fn = x').
Proof. exact (prop_ext (fun h4 : (x' 0) = e => @lem75321 A f fn x' e h1 h2 h3 h4) (fun h4 : fn = x' => @lem75315 A e f x' h2)). Qed.
Lemma lem75323 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75322 A f x' fn e h1 h2 h3) (@lem75315 A e f x' h2)). Qed.
Lemma lem75324 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) (h1 : term275 A e f fn) : term482 A f fn.
Proof. exact (proj2 (@lem75162 A e f fn h1)). Qed.
Lemma lem75325 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) (h1 : term275 A e f fn) : (fn 0) = e.
Proof. exact (proj1 (@lem75162 A e f fn h1)). Qed.
Lemma lem75326 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : (term482 A f fn) = (fn = x').
Proof. exact (prop_ext (fun h4 : term482 A f fn => @lem75323 A f x' fn e h1 h2 h3) (fun h4 : fn = x' => @lem75163 A f fn h1)). Qed.
Lemma lem75327 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75326 A f x' fn e h1 h2 h3) (@lem75163 A f fn h1)). Qed.
Lemma lem75328 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : ((fn 0) = e) = (fn = x').
Proof. exact (prop_ext (fun h4 : (fn 0) = e => @lem75327 A f x' fn e h1 h2 h3) (fun h4 : fn = x' => @lem75164 A fn e h3)). Qed.
Lemma lem75329 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term482 A f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75328 A f x' fn e h1 h2 h3) (@lem75164 A fn e h3)). Qed.
Lemma lem75330 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term275 A e f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : (term482 A f fn) = (fn = x').
Proof. exact (prop_ext (fun h4 : term482 A f fn => @lem75329 A f x' fn e h4 h2 h3) (fun h4 : fn = x' => @lem75324 A e f fn h1)). Qed.
Lemma lem75331 {A : Type'} (f : type1423 A) (x' : nat -> A) (fn : nat -> A) (e : A) (h1 : term275 A e f fn) (h2 : term275 A e f x') (h3 : (fn 0) = e) : fn = x'.
Proof. exact (EQ_MP (@lem75330 A f x' fn e h1 h2 h3) (@lem75324 A e f fn h1)). Qed.
Lemma lem75332 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term275 A e f fn) (h2 : term275 A e f x') : ((fn 0) = e) = (fn = x').
Proof. exact (prop_ext (fun h3 : (fn 0) = e => @lem75331 A f x' fn e h1 h2 h3) (fun h3 : fn = x' => @lem75325 A e f fn h1)). Qed.
Lemma lem75333 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term275 A e f fn) (h2 : term275 A e f x') : fn = x'.
Proof. exact (EQ_MP (@lem75332 A fn e f x' h1 h2) (@lem75325 A e f fn h1)). Qed.
Lemma lem75334 {A : Type'} (x' : nat -> A) (e : A) (f : type1423 A) (fn : nat -> A) (h1 : term287 A fn e f x') (h2 : term275 A e f fn) : (term275 A e f x') = (fn = x').
Proof. exact (prop_ext (fun h3 : term275 A e f x' => @lem75333 A fn e f x' h2 h3) (fun h3 : fn = x' => @lem75312 A fn e f x' h1)). Qed.
Lemma lem75335 {A : Type'} (x' : nat -> A) (e : A) (f : type1423 A) (fn : nat -> A) (h1 : term287 A fn e f x') (h2 : term275 A e f fn) : fn = x'.
Proof. exact (EQ_MP (@lem75334 A x' e f fn h1 h2) (@lem75312 A fn e f x' h1)). Qed.
Lemma lem75336 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term287 A fn e f x') : (term275 A e f fn) = (fn = x').
Proof. exact (prop_ext (fun h2 : term275 A e f fn => @lem75335 A x' e f fn h1 h2) (fun h2 : fn = x' => @lem75313 A fn e f x' h1)). Qed.
Lemma lem75337 {A : Type'} (fn : nat -> A) (e : A) (f : type1423 A) (x' : nat -> A) (h1 : term287 A fn e f x') : fn = x'.
Proof. exact (EQ_MP (@lem75336 A fn e f x' h1) (@lem75313 A fn e f x' h1)). Qed.
Lemma lem75338 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) (x' : nat -> A) : term291 A e f fn x'.
Proof. exact (fun h0 : term287 A fn e f x' => @lem75337 A fn e f x' h0). Qed.
Lemma lem75343 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : term295 A e f fn.
Proof. exact (fun x' : nat -> A => @lem75338 A e f fn x'). Qed.
Lemma lem75348 {A : Type'} (e : A) (f : type1423 A) : term299 A e f.
Proof. exact (fun fn : nat -> A => @lem75343 A e f fn). Qed.
Lemma lem75349 {A : Type'} (e : A) (f : type1423 A) : term300 A e f.
Proof. exact (conj (@lem75159 A e f) (@lem75348 A e f)). Qed.
Lemma lem75350 {A : Type'} (e : A) (f : type1423 A) : term277 A e f.
Proof. exact (EQ_MP (@lem74191 A e f) (@lem75349 A e f)). Qed.
Lemma lem75355 {A : Type'} (e : A) : term526 A e.
Proof. exact (fun f : type1423 A => @lem75350 A e f). Qed.
Lemma lem75360 {A : Type'} : term527 A.
Proof. exact (fun e : A => @lem75355 A e). Qed.
