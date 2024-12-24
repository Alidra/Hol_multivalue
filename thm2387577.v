Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2387577_term_abbrevs.
Require Import thm2386787_spec.
Require Import thm2387510_spec.
Lemma lem2387511 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem2387512 : term1.
Proof. exact (EQ_MP (@lem2387511) (@lem2386787)). Qed.
Lemma lem2387513 : term2.
Proof. exact (@lem2387512 term3). Qed.
Lemma lem2387514 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem2387515 : term4.
Proof. exact (EQ_MP (@lem2387514) (@lem2387513)). Qed.
Lemma lem2387516 (h1 : rem = term5) : rem = term5.
Proof. exact (h1). Qed.
Lemma lem2387517 (h1 : rem = term5) : term5 = rem.
Proof. exact (SYM (@lem2387516 h1)). Qed.
Lemma lem2387518 (h1 : term5 = rem) : term5 = rem.
Proof. exact (h1). Qed.
Lemma lem2387519 (h1 : term5 = rem) : rem = term5.
Proof. exact (SYM (@lem2387518 h1)). Qed.
Lemma lem2387520 : (rem = term5) = (term5 = rem).
Proof. exact (prop_ext (fun h1 : rem = term5 => @lem2387517 h1) (fun h1 : term5 = rem => @lem2387519 h1)). Qed.
Lemma lem2387523 : term5 = rem.
Proof. exact (EQ_MP (@lem2387520) (@lem2387510)). Qed.
Lemma lem2387524 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2387525 (m : int) : (term6 m) = (rem m).
Proof. exact (MK_COMB (@lem2387523) (@lem2387524 m)). Qed.
Lemma lem2387526 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2387527 (m : int) (n : int) : (term7 m n) = (rem m n).
Proof. exact (MK_COMB (@lem2387525 m) (@lem2387526 n)). Qed.
Lemma lem2387528 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2387529 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2387528) (@lem2387527 m n)). Qed.
Lemma lem2387530 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2387531 (n : int) (m : int) : ((term7 m n) = m) = ((rem m n) = m).
Proof. exact (MK_COMB (@lem2387529 m n) (@lem2387530 m)). Qed.
Lemma lem2387532 (m : int) (n : int) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem2387533 (n : int) (m : int) : (term11 n m) = (term12 n m).
Proof. exact (MK_COMB (@lem2387532 m n) (@lem2387531 n m)). Qed.
Lemma lem2387534 (n : int) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem2387535 (n : int) (m : int) : (term14 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem2387534 n) (@lem2387533 n m)). Qed.
Lemma lem2387537 : term5 = rem.
Proof. exact (EQ_MP (@lem2387520) (@lem2387510)). Qed.
Lemma lem2387538 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2387539 (m : int) : (term6 m) = (rem m).
Proof. exact (MK_COMB (@lem2387537) (@lem2387538 m)). Qed.
Lemma lem2387540 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2387541 (m : int) (n : int) : (term7 m n) = (rem m n).
Proof. exact (MK_COMB (@lem2387539 m) (@lem2387540 n)). Qed.
Lemma lem2387542 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem2387543 (m : int) (n : int) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem2387542) (@lem2387541 m n)). Qed.
Lemma lem2387544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2387545 (m : int) (n : int) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem2387544) (@lem2387543 m n)). Qed.
Lemma lem2387547 : term5 = rem.
Proof. exact (EQ_MP (@lem2387520) (@lem2387510)). Qed.
Lemma lem2387548 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2387549 (m : int) : (term6 m) = (rem m).
Proof. exact (MK_COMB (@lem2387547) (@lem2387548 m)). Qed.
Lemma lem2387550 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2387551 (m : int) (n : int) : (term7 m n) = (rem m n).
Proof. exact (MK_COMB (@lem2387549 m) (@lem2387550 n)). Qed.
Lemma lem2387552 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2387553 (m : int) (n : int) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem2387552) (@lem2387551 m n)). Qed.
Lemma lem2387554 (n : int) : (int_abs n) = (int_abs n).
Proof. exact (eq_refl (int_abs n)). Qed.
Lemma lem2387555 (m : int) (n : int) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem2387553 m n) (@lem2387554 n)). Qed.
Lemma lem2387556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2387557 (m : int) (n : int) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem2387556) (@lem2387555 m n)). Qed.
Lemma lem2387559 : term5 = rem.
Proof. exact (EQ_MP (@lem2387520) (@lem2387510)). Qed.
Lemma lem2387560 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2387561 (m : int) : (term6 m) = (rem m).
Proof. exact (MK_COMB (@lem2387559) (@lem2387560 m)). Qed.
Lemma lem2387562 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2387563 (m : int) (n : int) : (term7 m n) = (rem m n).
Proof. exact (MK_COMB (@lem2387561 m) (@lem2387562 n)). Qed.
Lemma lem2387564 (m : int) (n : int) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem2387565 (m : int) (n : int) : (term28 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem2387564 m n) (@lem2387563 m n)). Qed.
Lemma lem2387566 (m : int) : (@eq int m) = (@eq int m).
Proof. exact (eq_refl (@eq int m)). Qed.
Lemma lem2387567 (m : int) (n : int) : (m = (term28 m n)) = (m = (term29 m n)).
Proof. exact (MK_COMB (@lem2387566 m) (@lem2387565 m n)). Qed.
Lemma lem2387568 (m : int) (n : int) : (term30 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem2387557 m n) (@lem2387567 m n)). Qed.
Lemma lem2387569 (m : int) (n : int) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem2387545 m n) (@lem2387568 m n)). Qed.
Lemma lem2387570 (m : int) (n : int) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2387535 n m) (@lem2387569 m n)). Qed.
Lemma lem2387571 (m : int) : (term36 m) = (term37 m).
Proof. exact (fun_ext (fun n : int => @lem2387570 m n)). Qed.
Lemma lem2387572 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387573 (m : int) : (term38 m) = (term39 m).
Proof. exact (MK_COMB (@lem2387572) (@lem2387571 m)). Qed.
Lemma lem2387574 : term40 = term41.
Proof. exact (fun_ext (fun m : int => @lem2387573 m)). Qed.
Lemma lem2387575 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2387576 : term4 = term42.
Proof. exact (MK_COMB (@lem2387575) (@lem2387574)). Qed.
Lemma lem2387577 : term42.
Proof. exact (EQ_MP (@lem2387576) (@lem2387515)). Qed.
