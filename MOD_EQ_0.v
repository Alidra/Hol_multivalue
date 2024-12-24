Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EQ_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_UNIQ_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm89498_spec.
Lemma lem196470 : term0.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem196481 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem196482 (m : nat) (h1 : term1) : term2 m.
Proof. exact (@lem196481 h1 m). Qed.
Lemma lem196483 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem196484 (m : nat) (h1 : term1) : term3 m.
Proof. exact (EQ_MP (@lem196483 m) (@lem196482 m h1)). Qed.
Lemma lem196485 (m : nat) (n : nat) (h1 : term1) : term4 m n.
Proof. exact (@lem196484 m h1 n). Qed.
Lemma lem196486 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem196487 (m : nat) (n : nat) (h1 : term1) : term5 m n.
Proof. exact (EQ_MP (@lem196486 m n) (@lem196485 m n h1)). Qed.
Lemma lem196488 (m : nat) (n : nat) (q : nat) (h1 : term1) : term6 m n q.
Proof. exact (@lem196487 m n h1 q). Qed.
Lemma lem196489 (q : nat) (m : nat) (n : nat) : (term6 m n q) = (term7 q m n).
Proof. exact (eq_refl (term6 m n q)). Qed.
Lemma lem196490 (q : nat) (m : nat) (n : nat) (h1 : term1) : term7 q m n.
Proof. exact (EQ_MP (@lem196489 q m n) (@lem196488 m n q h1)). Qed.
Lemma lem196491 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term1) : term8 q m n r.
Proof. exact (@lem196490 q m n h1 r). Qed.
Lemma lem196492 (q : nat) (m : nat) (n : nat) (r : nat) : (term8 q m n r) = (term9 q m n r).
Proof. exact (eq_refl (term8 q m n r)). Qed.
Lemma lem196493 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term1) : term9 q m n r.
Proof. exact (EQ_MP (@lem196492 q m n r) (@lem196491 q m n r h1)). Qed.
Lemma lem196494 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term10 m q r n) : term10 m q r n.
Proof. exact (h1). Qed.
Lemma lem196495 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term1) (h2 : term10 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem196493 q m n r h1 (@lem196494 m q r n h2)). Qed.
Lemma lem196496 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term10 m q r n) : term11 m n r.
Proof. exact (fun h0 : term1 => @lem196495 m q r n h0 h1). Qed.
Lemma lem196497 (m : nat) (r : nat) (n : nat) (h1 : term12 m r n) : term12 m r n.
Proof. exact (h1). Qed.
Lemma lem196498 (m : nat) (r : nat) (n : nat) (h1 : term12 m r n) : term11 m n r.
Proof. exact (ex_elim (@lem196497 m r n h1) (fun q : nat => fun h0 : term13 m r n q => @lem196496 m q r n h0)). Qed.
Lemma lem196499 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem196500 (m : nat) (r : nat) (n : nat) (h1 : term1) (h2 : term12 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem196498 m r n h2 (@lem196499 h1)). Qed.
Lemma lem196501 (m : nat) (n : nat) (r : nat) (h1 : term1) : term14 m n r.
Proof. exact (fun h0 : term12 m r n => @lem196500 m r n h1 h0). Qed.
Lemma lem196502 (m : nat) (n : nat) (h1 : term1) : term15 m n.
Proof. exact (fun r : nat => @lem196501 m n r h1). Qed.
Lemma lem196503 (m : nat) (h1 : term1) : term16 m.
Proof. exact (fun n : nat => @lem196502 m n h1). Qed.
Lemma lem196504 (h1 : term1) : term17.
Proof. exact (fun m : nat => @lem196503 m h1). Qed.
Lemma lem196505 : term18.
Proof. exact (fun h0 : term1 => @lem196504 h0). Qed.
Lemma lem196506 : term17.
Proof. exact (@lem196505 (@lem169705)). Qed.
Lemma lem196507 (m : nat) : term19 m.
Proof. exact (@lem196506 m). Qed.
Lemma lem196508 (m : nat) : (term19 m) = (term16 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem196509 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem196508 m) (@lem196507 m)). Qed.
Lemma lem196510 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem196509 m n). Qed.
Lemma lem196511 (m : nat) (n : nat) : (term20 m n) = (term15 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem196512 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem196511 m n) (@lem196510 m n)). Qed.
Lemma lem196513 (m : nat) (n : nat) (r : nat) : term21 m n r.
Proof. exact (@lem196512 m n r). Qed.
Lemma lem196514 (m : nat) (n : nat) (r : nat) : (term21 m n r) = (term14 m n r).
Proof. exact (eq_refl (term21 m n r)). Qed.
Lemma lem196526 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem196527 (m : nat) (h1 : term22) : term23 m.
Proof. exact (@lem196526 h1 m). Qed.
Lemma lem196528 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem196529 (m : nat) (h1 : term22) : term24 m.
Proof. exact (EQ_MP (@lem196528 m) (@lem196527 m h1)). Qed.
Lemma lem196530 (m : nat) (n : nat) (h1 : term22) : term25 m n.
Proof. exact (@lem196529 m h1 n). Qed.
Lemma lem196531 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem196532 (m : nat) (n : nat) (h1 : term22) : term26 m n.
Proof. exact (EQ_MP (@lem196531 m n) (@lem196530 m n h1)). Qed.
Lemma lem196533 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem196534 (m : nat) (n : nat) (h1 : term22) (h2 : term27 n) : term28 m n.
Proof. exact (@lem196532 m n h1 (@lem196533 n h2)). Qed.
Lemma lem196535 (n : nat) (h1 : term22) (h2 : term27 n) : term29 n.
Proof. exact (fun m : nat => @lem196534 m n h1 h2). Qed.
Lemma lem196536 (n : nat) (h1 : term22) : term30 n.
Proof. exact (fun h0 : term27 n => @lem196535 n h1 h0). Qed.
Lemma lem196537 (h1 : term22) : term31.
Proof. exact (fun n : nat => @lem196536 n h1). Qed.
Lemma lem196538 : term32.
Proof. exact (fun h0 : term22 => @lem196537 h0). Qed.
Lemma lem196539 : term31.
Proof. exact (@lem196538 (@lem157261)). Qed.
Lemma lem196540 (n : nat) : term33 n.
Proof. exact (@lem196539 n). Qed.
Lemma lem196541 (n : nat) : (term33 n) = (term30 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem196543 (n : nat) : term34 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem196544 (n : nat) : (term34 n) = (term35 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem196545 (n : nat) : term35 n.
Proof. exact (EQ_MP (@lem196544 n) (@lem196543 n)). Qed.
Lemma lem196547 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem196548 (n : nat) : term36 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem196549 (n : nat) : (term36 n) = ((term37 n) = n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem196551 : term38.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem196577 : term39.
Proof. exact (proj1 (@lem196551)). Qed.
Lemma lem196578 (m : nat) : term40 m.
Proof. exact (@lem196577 m). Qed.
Lemma lem196579 (m : nat) : (term40 m) = ((term41 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem196590 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem196591 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem196592 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term37 m).
Proof. exact (MK_COMB (@lem196591 m) (@lem196590 n h1)). Qed.
Lemma lem196594 (n : nat) : (term37 n) = n.
Proof. exact (EQ_MP (@lem196549 n) (@lem196548 n)). Qed.
Lemma lem196595 (m : nat) : (term37 m) = m.
Proof. exact (@lem196594 m). Qed.
Lemma lem196596 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem196592 m n h1) (@lem196595 m)). Qed.
Lemma lem196597 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem196598 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term42 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem196597) (@lem196596 m n h1)). Qed.
Lemma lem196599 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem196600 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((Nat.modulo m n) = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem196598 m n h1) (@lem196599)). Qed.
Lemma lem196603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem196604 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term43 m n) = (term44 m).
Proof. exact (MK_COMB (@lem196603) (@lem196600 m n h1)). Qed.
Lemma lem196612 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem196613 (q : nat) : (Nat.mul q) = (Nat.mul q).
Proof. exact (eq_refl (Nat.mul q)). Qed.
Lemma lem196614 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul q n) = (term41 q).
Proof. exact (MK_COMB (@lem196613 q) (@lem196612 n h1)). Qed.
Lemma lem196616 (m : nat) : (term41 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem196579 m) (@lem196578 m)). Qed.
Lemma lem196617 (q : nat) : (term41 q) = (NUMERAL 0).
Proof. exact (@lem196616 q). Qed.
Lemma lem196618 (q : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul q n) = (NUMERAL 0).
Proof. exact (TRANS (@lem196614 q n h1) (@lem196617 q)). Qed.
Lemma lem196619 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem196620 (q : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (m = (Nat.mul q n)) = (m = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem196619 m) (@lem196618 q n h1)). Qed.
Lemma lem196623 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term45 m n) = (term46 m).
Proof. exact (fun_ext (fun q : nat => @lem196620 q m n h1)). Qed.
Lemma lem196624 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem196625 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 m n) = (term48 m).
Proof. exact (MK_COMB (@lem196624) (@lem196623 m n h1)). Qed.
Lemma lem196627 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem196628 (t : Prop) : (term50 t) = t.
Proof. exact (@lem196627 nat t). Qed.
Lemma lem196629 (m : nat) : (term48 m) = (m = (NUMERAL 0)).
Proof. exact (@lem196628 (m = (NUMERAL 0))). Qed.
Lemma lem196632 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term47 m n) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem196625 m n h1) (@lem196629 m)). Qed.
Lemma lem196633 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n)) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem196604 m n h1) (@lem196632 m n h1)). Qed.
Lemma lem196635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem196636 (x : Prop) : (x = x) = True.
Proof. exact (@lem196635 Prop x). Qed.
Lemma lem196637 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem196636 (m = (NUMERAL 0))). Qed.
Lemma lem196638 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n)) = True.
Proof. exact (TRANS (@lem196633 m n h1) (@lem196637 m)). Qed.
Lemma lem196639 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n)).
Proof. exact (SYM (@lem196638 m n h1)). Qed.
Lemma lem196640 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n).
Proof. exact (EQ_MP (@lem196639 m n h1) (@lem0)). Qed.
Lemma lem196703 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem196704 (m : nat) (n : nat) (h1 : term47 m n) : term47 m n.
Proof. exact (h1). Qed.
Lemma lem196705 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : m = (Nat.mul q n).
Proof. exact (h1). Qed.
Lemma lem196709 (n : nat) : term30 n.
Proof. exact (EQ_MP (@lem196541 n) (@lem196540 n)). Qed.
Lemma lem196710 (n : nat) (h1 : term27 n) : term29 n.
Proof. exact (@lem196709 n (@lem196547 n h1)). Qed.
Lemma lem196711 (m : nat) (n : nat) (h1 : term27 n) : term51 n m.
Proof. exact (@lem196710 n h1 m). Qed.
Lemma lem196712 (m : nat) (n : nat) : (term51 n m) = (term28 m n).
Proof. exact (eq_refl (term51 n m)). Qed.
Lemma lem196713 (m : nat) (n : nat) (h1 : term27 n) : term28 m n.
Proof. exact (EQ_MP (@lem196712 m n) (@lem196711 m n h1)). Qed.
Lemma lem196714 (m : nat) (n : nat) (h1 : term27 n) : m = (term52 m n).
Proof. exact (proj1 (@lem196713 m n h1)). Qed.
Lemma lem196715 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem196716 (m : nat) (n : nat) (h1 : term27 n) : (term54 n m) = (term55 m n).
Proof. exact (MK_COMB (@lem196715 n) (@lem196714 m n h1)). Qed.
Lemma lem196717 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem196718 (n : nat) (m : nat) : (term57 n m) = (term57 n m).
Proof. exact (eq_refl (term57 n m)). Qed.
Lemma lem196719 (m : nat) (n : nat) : ((term54 n m) = (term55 m n)) = ((term54 n m) = (term56 m n)).
Proof. exact (MK_COMB (@lem196718 n m) (@lem196717 m n)). Qed.
Lemma lem196720 (m : nat) (n : nat) : (term54 n m) = (term47 m n).
Proof. exact (eq_refl (term54 n m)). Qed.
Lemma lem196721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem196722 (m : nat) (n : nat) : (term57 n m) = (term58 m n).
Proof. exact (MK_COMB (@lem196721) (@lem196720 m n)). Qed.
Lemma lem196723 (m : nat) (n : nat) : (term56 m n) = (term56 m n).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem196724 (m : nat) (n : nat) : ((term54 n m) = (term56 m n)) = ((term47 m n) = (term56 m n)).
Proof. exact (MK_COMB (@lem196722 m n) (@lem196723 m n)). Qed.
Lemma lem196725 (m : nat) (n : nat) : ((term54 n m) = (term55 m n)) = ((term47 m n) = (term56 m n)).
Proof. exact (TRANS (@lem196719 m n) (@lem196724 m n)). Qed.
Lemma lem196726 (m : nat) (n : nat) (h1 : term27 n) : (term47 m n) = (term56 m n).
Proof. exact (EQ_MP (@lem196725 m n) (@lem196716 m n h1)). Qed.
Lemma lem196727 (m : nat) (n : nat) (h1 : term27 n) : (term56 m n) = (term47 m n).
Proof. exact (SYM (@lem196726 m n h1)). Qed.
Lemma lem196755 : term59.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem196771 : term60.
Proof. exact (proj1 (@lem196755)). Qed.
Lemma lem196772 (m : nat) : term61 m.
Proof. exact (@lem196771 m). Qed.
Lemma lem196773 (m : nat) : (term61 m) = ((term62 m) = m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem196869 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem196876 (m : nat) (n : nat) : (term63 m n) = (term63 m n).
Proof. exact (eq_refl (term63 m n)). Qed.
Lemma lem196877 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term52 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem196876 m n) (@lem196869 m n h1)). Qed.
Lemma lem196879 (m : nat) : (term62 m) = m.
Proof. exact (EQ_MP (@lem196773 m) (@lem196772 m)). Qed.
Lemma lem196880 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (@lem196879 (term65 m n)). Qed.
Lemma lem196899 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term52 m n) = (term65 m n).
Proof. exact (TRANS (@lem196877 m n h1) (@lem196880 m n)). Qed.
Lemma lem196900 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem196901 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem196900) (@lem196899 m n h1)). Qed.
Lemma lem196934 (q : nat) (n : nat) : (Nat.mul q n) = (Nat.mul q n).
Proof. exact (eq_refl (Nat.mul q n)). Qed.
Lemma lem196935 (q : nat) (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : ((term52 m n) = (Nat.mul q n)) = ((term65 m n) = (Nat.mul q n)).
Proof. exact (MK_COMB (@lem196901 m n h1) (@lem196934 q n)). Qed.
Lemma lem196972 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term68 m n) = (term69 m n).
Proof. exact (fun_ext (fun q : nat => @lem196935 q m n h1)). Qed.
Lemma lem197011 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197012 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term56 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem197011) (@lem196972 m n h1)). Qed.
Lemma lem197059 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : (term70 m n) = (term56 m n).
Proof. exact (SYM (@lem197012 m n h1)). Qed.
Lemma lem197061 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem197062 (m : nat) (n : nat) : (term70 m n) = (term72 m n).
Proof. exact (@lem197061 (term70 m n)). Qed.
Lemma lem197063 (m : nat) (n : nat) : (term72 m n) = (term70 m n).
Proof. exact (SYM (@lem197062 m n)). Qed.
Lemma lem197064 (m : nat) (n : nat) (h1 : term73 m n) : term73 m n.
Proof. exact (h1). Qed.
Lemma lem197067 (m : nat) (n : nat) (h1 : term72 m n) : term72 m n.
Proof. exact (h1). Qed.
Lemma lem197068 (m : nat) (n : nat) : term74 m n.
Proof. exact (fun h0 : term72 m n => @lem197067 m n h0). Qed.
Lemma lem197069 (m : nat) (n : nat) (h1 : term74 m n) : term74 m n.
Proof. exact (h1). Qed.
Lemma lem197070 (m : nat) (n : nat) (h1 : term72 m n) : term72 m n.
Proof. exact (h1). Qed.
Lemma lem197071 (m : nat) (n : nat) (h1 : term72 m n) (h2 : term74 m n) : term72 m n.
Proof. exact (@lem197069 m n h2 (@lem197070 m n h1)). Qed.
Lemma lem197072 (m : nat) (n : nat) (h1 : term72 m n) : term75 m n.
Proof. exact (fun h0 : term74 m n => @lem197071 m n h1 h0). Qed.
Lemma lem197073 (m : nat) (n : nat) (h1 : term74 m n) : term74 m n.
Proof. exact (h1). Qed.
Lemma lem197074 (m : nat) (n : nat) (h1 : term72 m n) (h2 : term74 m n) : term72 m n.
Proof. exact (@lem197072 m n h1 (@lem197073 m n h2)). Qed.
Lemma lem197075 (m : nat) (n : nat) (h1 : term74 m n) : term74 m n.
Proof. exact (fun h0 : term72 m n => @lem197074 m n h0 h1). Qed.
Lemma lem197076 (m : nat) (n : nat) : term76 m n.
Proof. exact (fun h0 : term74 m n => @lem197075 m n h0). Qed.
Lemma lem197079 (m : nat) (n : nat) : term74 m n.
Proof. exact (@lem197076 m n (@lem197068 m n)). Qed.
Lemma lem197089 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem197090 (m : nat) (n : nat) : (term72 m n) = (term77 m n).
Proof. exact (@lem197089 (term73 m n)). Qed.
Lemma lem197092 (t : Prop) : (term78 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem197093 (m : nat) (n : nat) : (term77 m n) = (term70 m n).
Proof. exact (@lem197092 (term70 m n)). Qed.
Lemma lem197098 (m : nat) (n : nat) : (term72 m n) = (term70 m n).
Proof. exact (TRANS (@lem197090 m n) (@lem197093 m n)). Qed.
Lemma lem197099 (n : nat) : (term79 n) = (term80 n).
Proof. exact (fun_ext (fun m : nat => @lem197098 m n)). Qed.
Lemma lem197100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197101 (n : nat) : (term81 n) = (term82 n).
Proof. exact (MK_COMB (@lem197100) (@lem197099 n)). Qed.
Lemma lem197106 : term83 = term84.
Proof. exact (fun_ext (fun n : nat => @lem197101 n)). Qed.
Lemma lem197107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197116 : term85 = term86.
Proof. exact (MK_COMB (@lem197107) (@lem197106)). Qed.
Lemma lem197117 (m : nat) (q : nat) (n : nat) : ((term65 m n) = (Nat.mul q n)) = ((term65 m n) = (Nat.mul q n)).
Proof. exact (eq_refl ((term65 m n) = (Nat.mul q n))). Qed.
Lemma lem197118 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (fun_ext (fun q : nat => @lem197117 m q n)). Qed.
Lemma lem197119 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197120 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem197119) (@lem197118 m n)). Qed.
Lemma lem197121 (n : nat) : (term80 n) = (term80 n).
Proof. exact (fun_ext (fun m : nat => @lem197120 m n)). Qed.
Lemma lem197122 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197123 (n : nat) : (term82 n) = (term82 n).
Proof. exact (MK_COMB (@lem197122) (@lem197121 n)). Qed.
Lemma lem197124 : term84 = term84.
Proof. exact (fun_ext (fun n : nat => @lem197123 n)). Qed.
Lemma lem197125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197126 : term86 = term86.
Proof. exact (MK_COMB (@lem197125) (@lem197124)). Qed.
Lemma lem197147 : term85 = term86.
Proof. exact (TRANS (@lem197116) (@lem197126)). Qed.
Lemma lem197148 : term86 = term85.
Proof. exact (SYM (@lem197147)). Qed.
Lemma lem197150 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem197151 (m : nat) (n : nat) : (term70 m n) = (term72 m n).
Proof. exact (@lem197150 (term70 m n)). Qed.
Lemma lem197152 (m : nat) (n : nat) : (term72 m n) = (term70 m n).
Proof. exact (SYM (@lem197151 m n)). Qed.
Lemma lem197153 (m : nat) (n : nat) (h1 : term73 m n) : term73 m n.
Proof. exact (h1). Qed.
Lemma lem197155 (P : nat -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem197156 (m : nat) (n : nat) : (term73 m n) = (term89 m n).
Proof. exact (@lem197155 (term69 m n)). Qed.
Lemma lem197157 (m : nat) (q : nat) (n : nat) : (term90 m n q) = ((term65 m n) = (Nat.mul q n)).
Proof. exact (eq_refl (term90 m n q)). Qed.
Lemma lem197158 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem197160 (m : nat) (q : nat) (n : nat) : (term91 m n q) = (term92 m q n).
Proof. exact (MK_COMB (@lem197158) (@lem197157 m q n)). Qed.
Lemma lem197161 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (fun_ext (fun q : nat => @lem197160 m q n)). Qed.
Lemma lem197162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197163 (m : nat) (n : nat) : (term89 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem197162) (@lem197161 m n)). Qed.
Lemma lem197172 (m : nat) (n : nat) : (term73 m n) = (term95 m n).
Proof. exact (TRANS (@lem197156 m n) (@lem197163 m n)). Qed.
Lemma lem197173 (m : nat) (n : nat) (h1 : term73 m n) : term95 m n.
Proof. exact (EQ_MP (@lem197172 m n) (@lem197153 m n h1)). Qed.
Lemma lem197192 (m : nat) (q : nat) (n : nat) : (term92 m q n) = (term92 m q n).
Proof. exact (eq_refl (term92 m q n)). Qed.
Lemma lem197193 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (fun_ext (fun q : nat => @lem197192 m q n)). Qed.
Lemma lem197194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197195 (m : nat) (n : nat) : (term95 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem197194) (@lem197193 m n)). Qed.
Lemma lem197196 (m : nat) (n : nat) (h1 : term73 m n) : term95 m n.
Proof. exact (EQ_MP (@lem197195 m n) (@lem197173 m n h1)). Qed.
Lemma lem197198 (m : nat) (q : nat) (n : nat) : (term92 m q n) = (term92 m q n).
Proof. exact (eq_refl (term92 m q n)). Qed.
Lemma lem197199 (m : nat) (n : nat) : (term94 m n) = (term94 m n).
Proof. exact (fun_ext (fun q : nat => @lem197198 m q n)). Qed.
Lemma lem197200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197202 (m : nat) (n : nat) : (term95 m n) = (term95 m n).
Proof. exact (MK_COMB (@lem197200) (@lem197199 m n)). Qed.
Lemma lem197203 (m : nat) (n : nat) (h1 : term73 m n) : term95 m n.
Proof. exact (EQ_MP (@lem197202 m n) (@lem197196 m n h1)). Qed.
Lemma lem197204 (_3952 : nat) (m : nat) (n : nat) (h1 : term73 m n) : term96 m n _3952.
Proof. exact (@lem197203 m n h1 _3952). Qed.
Lemma lem197205 (m : nat) (_3952 : nat) (n : nat) : (term96 m n _3952) = (term92 m _3952 n).
Proof. exact (eq_refl (term96 m n _3952)). Qed.
Lemma lem197208 (_3952 : nat) (m : nat) (n : nat) (h1 : term73 m n) : term92 m _3952 n.
Proof. exact (EQ_MP (@lem197205 m _3952 n) (@lem197204 _3952 m n h1)). Qed.
Lemma lem197242 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem197243 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (@lem197242 (term65 m n)). Qed.
Lemma lem197244 (m : nat) (n : nat) : term97 m n.
Proof. exact (fun h0 : term98 m n => @lem197243 m n). Qed.
Lemma lem197246 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem197247 (m : nat) (n : nat) : (term97 m n) = ((term65 m n) = (term65 m n)).
Proof. exact (@lem197246 ((term65 m n) = (term65 m n))). Qed.
Lemma lem197248 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (EQ_MP (@lem197247 m n) (@lem197244 m n)). Qed.
Lemma lem197251 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem197253 (m : nat) (_3952 : nat) (n : nat) : (term92 m _3952 n) = (term100 m _3952 n).
Proof. exact (@lem197251 ((term65 m n) = (Nat.mul _3952 n))). Qed.
Lemma lem197256 (_3952 : nat) (m : nat) (n : nat) (h1 : term73 m n) : term100 m _3952 n.
Proof. exact (EQ_MP (@lem197253 m _3952 n) (@lem197208 _3952 m n h1)). Qed.
Lemma lem197257 (m : nat) (n : nat) (h1 : term73 m n) : term101 m n.
Proof. exact (@lem197256 (Nat.div m n) m n h1). Qed.
Lemma lem197260 (m : nat) (n : nat) (h1 : term73 m n) : False.
Proof. exact (@lem197257 m n h1 (@lem197248 m n)). Qed.
Lemma lem197261 (m : nat) (n : nat) (h1 : term73 m n) : term102.
Proof. exact (fun h0 : ~ False => @lem197260 m n h1). Qed.
Lemma lem197263 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem197264 : term102 = False.
Proof. exact (@lem197263 False). Qed.
Lemma lem197265 (m : nat) (n : nat) (h1 : term73 m n) : False.
Proof. exact (EQ_MP (@lem197264) (@lem197261 m n h1)). Qed.
Lemma lem197266 (m : nat) (n : nat) (h1 : term73 m n) : (term73 m n) = False.
Proof. exact (prop_ext (fun h2 : term73 m n => @lem197265 m n h1) (fun h2 : False => @lem197153 m n h1)). Qed.
Lemma lem197267 (m : nat) (n : nat) (h1 : term73 m n) : False.
Proof. exact (EQ_MP (@lem197266 m n h1) (@lem197153 m n h1)). Qed.
Lemma lem197268 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun h0 : term73 m n => @lem197267 m n h0). Qed.
Lemma lem197269 (m : nat) (n : nat) : term70 m n.
Proof. exact (EQ_MP (@lem197152 m n) (@lem197268 m n)). Qed.
Lemma lem197274 (n : nat) : term82 n.
Proof. exact (fun m : nat => @lem197269 m n). Qed.
Lemma lem197279 : term86.
Proof. exact (fun n : nat => @lem197274 n). Qed.
Lemma lem197280 : term85.
Proof. exact (EQ_MP (@lem197148) (@lem197279)). Qed.
Lemma lem197281 (n : nat) : term103 n.
Proof. exact (@lem197280 n). Qed.
Lemma lem197282 (n : nat) : (term103 n) = (term81 n).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem197283 (n : nat) : term81 n.
Proof. exact (EQ_MP (@lem197282 n) (@lem197281 n)). Qed.
Lemma lem197284 (n : nat) (m : nat) : term104 n m.
Proof. exact (@lem197283 n m). Qed.
Lemma lem197285 (m : nat) (n : nat) : (term104 n m) = (term72 m n).
Proof. exact (eq_refl (term104 n m)). Qed.
Lemma lem197286 (m : nat) (n : nat) : term72 m n.
Proof. exact (EQ_MP (@lem197285 m n) (@lem197284 n m)). Qed.
Lemma lem197288 (m : nat) (n : nat) : term72 m n.
Proof. exact (@lem197079 m n (@lem197286 m n)). Qed.
Lemma lem197289 (m : nat) (n : nat) (h1 : term73 m n) : False.
Proof. exact (@lem197288 m n (@lem197064 m n h1)). Qed.
Lemma lem197290 (m : nat) (n : nat) (h1 : term73 m n) : (term73 m n) = False.
Proof. exact (prop_ext (fun h2 : term73 m n => @lem197289 m n h1) (fun h2 : False => @lem197064 m n h1)). Qed.
Lemma lem197291 (m : nat) (n : nat) (h1 : term73 m n) : False.
Proof. exact (EQ_MP (@lem197290 m n h1) (@lem197064 m n h1)). Qed.
Lemma lem197292 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun h0 : term73 m n => @lem197291 m n h0). Qed.
Lemma lem197293 (m : nat) (n : nat) : term70 m n.
Proof. exact (EQ_MP (@lem197063 m n) (@lem197292 m n)). Qed.
Lemma lem197294 (m : nat) (n : nat) (h1 : (Nat.modulo m n) = (NUMERAL 0)) : term56 m n.
Proof. exact (EQ_MP (@lem197059 m n h1) (@lem197293 m n)). Qed.
Lemma lem197295 (m : nat) (n : nat) (h1 : term27 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term47 m n.
Proof. exact (EQ_MP (@lem196727 m n h1) (@lem197294 m n h2)). Qed.
Lemma lem197297 (m : nat) (n : nat) (r : nat) : term14 m n r.
Proof. exact (EQ_MP (@lem196514 m n r) (@lem196513 m n r)). Qed.
Lemma lem197298 (m : nat) (n : nat) : term105 m n.
Proof. exact (@lem197297 m n (NUMERAL 0)). Qed.
Lemma lem197303 : term59.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem197319 : term60.
Proof. exact (proj1 (@lem197303)). Qed.
Lemma lem197320 (m : nat) : term61 m.
Proof. exact (@lem197319 m). Qed.
Lemma lem197321 (m : nat) : (term61 m) = ((term62 m) = m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem197391 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : m = (Nat.mul q n).
Proof. exact (h1). Qed.
Lemma lem197393 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem197394 (n : nat) (q : nat) : (Nat.mul q n) = (Nat.mul n q).
Proof. exact (@lem197393 n q). Qed.
Lemma lem197398 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : m = (Nat.mul n q).
Proof. exact (TRANS (@lem197391 m q n h1) (@lem197394 n q)). Qed.
Lemma lem197399 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem197400 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (@eq nat m) = (term106 n q).
Proof. exact (MK_COMB (@lem197399) (@lem197398 m q n h1)). Qed.
Lemma lem197405 (m : nat) : (term62 m) = m.
Proof. exact (EQ_MP (@lem197321 m) (@lem197320 m)). Qed.
Lemma lem197406 (_3961 : nat) (n : nat) : (term107 _3961 n) = (Nat.mul _3961 n).
Proof. exact (@lem197405 (Nat.mul _3961 n)). Qed.
Lemma lem197410 (_3961 : nat) (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (m = (term107 _3961 n)) = ((Nat.mul n q) = (Nat.mul _3961 n)).
Proof. exact (MK_COMB (@lem197400 m q n h1) (@lem197406 _3961 n)). Qed.
Lemma lem197419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197420 (_3961 : nat) (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term108 m _3961 n) = (term109 q _3961 n).
Proof. exact (MK_COMB (@lem197419) (@lem197410 _3961 m q n h1)). Qed.
Lemma lem197429 (n : nat) : (term110 n) = (term110 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem197430 (_3961 : nat) (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term111 m _3961 n) = (term112 q _3961 n).
Proof. exact (MK_COMB (@lem197420 _3961 m q n h1) (@lem197429 n)). Qed.
Lemma lem197443 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term113 m n) = (term114 q n).
Proof. exact (fun_ext (fun _3961 : nat => @lem197430 _3961 m q n h1)). Qed.
Lemma lem197452 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem197453 (n : nat) (q' : nat) : (Nat.mul q' n) = (Nat.mul n q').
Proof. exact (@lem197452 n q'). Qed.
Lemma lem197457 (n : nat) (q : nat) : (term106 n q) = (term106 n q).
Proof. exact (eq_refl (term106 n q)). Qed.
Lemma lem197458 (q : nat) (n : nat) (q' : nat) : ((Nat.mul n q) = (Nat.mul q' n)) = ((Nat.mul n q) = (Nat.mul n q')).
Proof. exact (MK_COMB (@lem197457 n q) (@lem197453 n q')). Qed.
Lemma lem197467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197468 (q : nat) (n : nat) (q' : nat) : (term109 q q' n) = (term115 q n q').
Proof. exact (MK_COMB (@lem197467) (@lem197458 q n q')). Qed.
Lemma lem197477 (n : nat) : (term110 n) = (term110 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem197478 (q : nat) (q' : nat) (n : nat) : (term112 q q' n) = (term116 q q' n).
Proof. exact (MK_COMB (@lem197468 q n q') (@lem197477 n)). Qed.
Lemma lem197489 (q : nat) (n : nat) : (term114 q n) = (term117 q n).
Proof. exact (fun_ext (fun q' : nat => @lem197478 q q' n)). Qed.
Lemma lem197500 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term113 m n) = (term117 q n).
Proof. exact (TRANS (@lem197443 m q n h1) (@lem197489 q n)). Qed.
Lemma lem197501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197502 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term118 m n) = (term119 q n).
Proof. exact (MK_COMB (@lem197501) (@lem197500 m q n h1)). Qed.
Lemma lem197517 (m : nat) (q : nat) (n : nat) (h1 : m = (Nat.mul q n)) : (term119 q n) = (term118 m n).
Proof. exact (SYM (@lem197502 m q n h1)). Qed.
Lemma lem197519 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem197520 (q : nat) (n : nat) : (term119 q n) = (term120 q n).
Proof. exact (@lem197519 (term119 q n)). Qed.
Lemma lem197521 (q : nat) (n : nat) : (term120 q n) = (term119 q n).
Proof. exact (SYM (@lem197520 q n)). Qed.
Lemma lem197522 (q : nat) (n : nat) (h1 : term121 q n) : term121 q n.
Proof. exact (h1). Qed.
Lemma lem197525 (m : nat) (q : nat) (n : nat) (h1 : term122 m q n) : term122 m q n.
Proof. exact (h1). Qed.
Lemma lem197526 (m : nat) (q : nat) (n : nat) : term123 m q n.
Proof. exact (fun h0 : term122 m q n => @lem197525 m q n h0). Qed.
Lemma lem197527 (m : nat) (q : nat) (n : nat) (h1 : term123 m q n) : term123 m q n.
Proof. exact (h1). Qed.
Lemma lem197528 (m : nat) (q : nat) (n : nat) (h1 : term122 m q n) : term122 m q n.
Proof. exact (h1). Qed.
Lemma lem197529 (m : nat) (q : nat) (n : nat) (h1 : term122 m q n) (h2 : term123 m q n) : term122 m q n.
Proof. exact (@lem197527 m q n h2 (@lem197528 m q n h1)). Qed.
Lemma lem197530 (m : nat) (q : nat) (n : nat) (h1 : term122 m q n) : term124 m q n.
Proof. exact (fun h0 : term123 m q n => @lem197529 m q n h1 h0). Qed.
Lemma lem197531 (m : nat) (q : nat) (n : nat) (h1 : term123 m q n) : term123 m q n.
Proof. exact (h1). Qed.
Lemma lem197532 (m : nat) (q : nat) (n : nat) (h1 : term122 m q n) (h2 : term123 m q n) : term122 m q n.
Proof. exact (@lem197530 m q n h1 (@lem197531 m q n h2)). Qed.
Lemma lem197533 (m : nat) (q : nat) (n : nat) (h1 : term123 m q n) : term123 m q n.
Proof. exact (fun h0 : term122 m q n => @lem197532 m q n h0 h1). Qed.
Lemma lem197534 (m : nat) (q : nat) (n : nat) : term125 m q n.
Proof. exact (fun h0 : term123 m q n => @lem197533 m q n h0). Qed.
Lemma lem197537 (m : nat) (q : nat) (n : nat) : term123 m q n.
Proof. exact (@lem197534 m q n (@lem197526 m q n)). Qed.
Lemma lem197577 {A : Type'} (P : A -> Prop) (Q : Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem197578 (P : nat -> Prop) (Q : Prop) : (term128 P Q) = (term129 P Q).
Proof. exact (@lem197577 nat P Q). Qed.
Lemma lem197579 (q : nat) (n : nat) : (term130 q n) = (term131 q n).
Proof. exact (@lem197578 (term132 q n) (term110 n)). Qed.
Lemma lem197580 (q : nat) (n : nat) (q' : nat) : (term133 q n q') = ((Nat.mul n q) = (Nat.mul n q')).
Proof. exact (eq_refl (term133 q n q')). Qed.
Lemma lem197581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197582 (q : nat) (n : nat) (q' : nat) : (term134 q n q') = (term115 q n q').
Proof. exact (MK_COMB (@lem197581) (@lem197580 q n q')). Qed.
Lemma lem197583 (n : nat) : (term110 n) = (term110 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem197584 (q : nat) (q' : nat) (n : nat) : (term135 q q' n) = (term116 q q' n).
Proof. exact (MK_COMB (@lem197582 q n q') (@lem197583 n)). Qed.
Lemma lem197585 (q : nat) (n : nat) : (term136 q n) = (term117 q n).
Proof. exact (fun_ext (fun q' : nat => @lem197584 q q' n)). Qed.
Lemma lem197586 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197587 (q : nat) (n : nat) : (term130 q n) = (term119 q n).
Proof. exact (MK_COMB (@lem197586) (@lem197585 q n)). Qed.
Lemma lem197588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem197589 (q : nat) (n : nat) : (term137 q n) = (term138 q n).
Proof. exact (MK_COMB (@lem197588) (@lem197587 q n)). Qed.
Lemma lem197590 (q : nat) (n : nat) (q' : nat) : (term133 q n q') = ((Nat.mul n q) = (Nat.mul n q')).
Proof. exact (eq_refl (term133 q n q')). Qed.
Lemma lem197591 (q : nat) (n : nat) : (term139 q n) = (term132 q n).
Proof. exact (fun_ext (fun q' : nat => @lem197590 q n q')). Qed.
Lemma lem197592 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197593 (q : nat) (n : nat) : (term140 q n) = (term141 q n).
Proof. exact (MK_COMB (@lem197592) (@lem197591 q n)). Qed.
Lemma lem197594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197595 (q : nat) (n : nat) : (term142 q n) = (term143 q n).
Proof. exact (MK_COMB (@lem197594) (@lem197593 q n)). Qed.
Lemma lem197596 (n : nat) : (term110 n) = (term110 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem197597 (q : nat) (n : nat) : (term131 q n) = (term144 q n).
Proof. exact (MK_COMB (@lem197595 q n) (@lem197596 n)). Qed.
Lemma lem197598 (q : nat) (n : nat) : ((term130 q n) = (term131 q n)) = ((term119 q n) = (term144 q n)).
Proof. exact (MK_COMB (@lem197589 q n) (@lem197597 q n)). Qed.
Lemma lem197599 (q : nat) (n : nat) : (term119 q n) = (term144 q n).
Proof. exact (EQ_MP (@lem197598 q n) (@lem197579 q n)). Qed.
Lemma lem197606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem197607 (q : nat) (n : nat) : (term121 q n) = (term145 q n).
Proof. exact (MK_COMB (@lem197606) (@lem197599 q n)). Qed.
Lemma lem197608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem197609 (q : nat) (n : nat) : (term146 q n) = (term147 q n).
Proof. exact (MK_COMB (@lem197608) (@lem197607 q n)). Qed.
Lemma lem197617 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem197618 : term148 = term149.
Proof. exact (@lem197617 term150). Qed.
Lemma lem197627 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem197628 : term152 = term153.
Proof. exact (MK_COMB (@lem197627) (@lem197618)). Qed.
Lemma lem197631 (q : nat) (n : nat) : (term154 q n) = (term155 q n).
Proof. exact (MK_COMB (@lem197609 q n) (@lem197628)). Qed.
Lemma lem197634 (m : nat) (q : nat) (n : nat) : (term156 m q n) = (term156 m q n).
Proof. exact (eq_refl (term156 m q n)). Qed.
Lemma lem197635 (m : nat) (q : nat) (n : nat) : (term157 m q n) = (term158 m q n).
Proof. exact (MK_COMB (@lem197634 m q n) (@lem197631 q n)). Qed.
Lemma lem197638 (n : nat) : (term159 n) = (term159 n).
Proof. exact (eq_refl (term159 n)). Qed.
Lemma lem197639 (m : nat) (q : nat) (n : nat) : (term122 m q n) = (term160 m q n).
Proof. exact (MK_COMB (@lem197638 n) (@lem197635 m q n)). Qed.
Lemma lem197642 (q : nat) (n : nat) : (term161 q n) = (term162 q n).
Proof. exact (fun_ext (fun m : nat => @lem197639 m q n)). Qed.
Lemma lem197643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197644 (q : nat) (n : nat) : (term163 q n) = (term164 q n).
Proof. exact (MK_COMB (@lem197643) (@lem197642 q n)). Qed.
Lemma lem197649 (n : nat) : (term165 n) = (term166 n).
Proof. exact (fun_ext (fun q : nat => @lem197644 q n)). Qed.
Lemma lem197650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197651 (n : nat) : (term167 n) = (term168 n).
Proof. exact (MK_COMB (@lem197650) (@lem197649 n)). Qed.
Lemma lem197656 : term169 = term170.
Proof. exact (fun_ext (fun n : nat => @lem197651 n)). Qed.
Lemma lem197657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197666 : term171 = term172.
Proof. exact (MK_COMB (@lem197657) (@lem197656)). Qed.
Lemma lem197673 (n : nat) (m : nat) : ((term173 m n) = (Peano.lt n m)) = ((term173 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term173 m n) = (Peano.lt n m))). Qed.
Lemma lem197674 (m : nat) : (term174 m) = (term174 m).
Proof. exact (fun_ext (fun n : nat => @lem197673 n m)). Qed.
Lemma lem197675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197676 (m : nat) : (term175 m) = (term175 m).
Proof. exact (MK_COMB (@lem197675) (@lem197674 m)). Qed.
Lemma lem197677 : term176 = term176.
Proof. exact (fun_ext (fun m : nat => @lem197676 m)). Qed.
Lemma lem197678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197679 : term150 = term150.
Proof. exact (MK_COMB (@lem197678) (@lem197677)). Qed.
Lemma lem197680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem197681 : term149 = term149.
Proof. exact (MK_COMB (@lem197680) (@lem197679)). Qed.
Lemma lem197686 (m : nat) : ((term177 m) = (m = (NUMERAL 0))) = ((term177 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term177 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem197687 : term178 = term178.
Proof. exact (fun_ext (fun m : nat => @lem197686 m)). Qed.
Lemma lem197688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197689 : term0 = term0.
Proof. exact (MK_COMB (@lem197688) (@lem197687)). Qed.
Lemma lem197690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem197691 : term151 = term151.
Proof. exact (MK_COMB (@lem197690) (@lem197689)). Qed.
Lemma lem197692 : term153 = term153.
Proof. exact (MK_COMB (@lem197691) (@lem197681)). Qed.
Lemma lem197693 (n : nat) : (term110 n) = (term110 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem197694 (q : nat) (n : nat) (q' : nat) : ((Nat.mul n q) = (Nat.mul n q')) = ((Nat.mul n q) = (Nat.mul n q')).
Proof. exact (eq_refl ((Nat.mul n q) = (Nat.mul n q'))). Qed.
Lemma lem197695 (q : nat) (n : nat) : (term132 q n) = (term132 q n).
Proof. exact (fun_ext (fun q' : nat => @lem197694 q n q')). Qed.
Lemma lem197696 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem197697 (q : nat) (n : nat) : (term141 q n) = (term141 q n).
Proof. exact (MK_COMB (@lem197696) (@lem197695 q n)). Qed.
Lemma lem197698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197699 (q : nat) (n : nat) : (term143 q n) = (term143 q n).
Proof. exact (MK_COMB (@lem197698) (@lem197697 q n)). Qed.
Lemma lem197700 (q : nat) (n : nat) : (term144 q n) = (term144 q n).
Proof. exact (MK_COMB (@lem197699 q n) (@lem197693 n)). Qed.
Lemma lem197701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem197702 (q : nat) (n : nat) : (term145 q n) = (term145 q n).
Proof. exact (MK_COMB (@lem197701) (@lem197700 q n)). Qed.
Lemma lem197703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem197704 (q : nat) (n : nat) : (term147 q n) = (term147 q n).
Proof. exact (MK_COMB (@lem197703) (@lem197702 q n)). Qed.
Lemma lem197705 (q : nat) (n : nat) : (term155 q n) = (term155 q n).
Proof. exact (MK_COMB (@lem197704 q n) (@lem197692)). Qed.
Lemma lem197708 (m : nat) (q : nat) (n : nat) : (term156 m q n) = (term156 m q n).
Proof. exact (eq_refl (term156 m q n)). Qed.
Lemma lem197709 (m : nat) (q : nat) (n : nat) : (term158 m q n) = (term158 m q n).
Proof. exact (MK_COMB (@lem197708 m q n) (@lem197705 q n)). Qed.
Lemma lem197714 (n : nat) : (term159 n) = (term159 n).
Proof. exact (eq_refl (term159 n)). Qed.
Lemma lem197715 (m : nat) (q : nat) (n : nat) : (term160 m q n) = (term160 m q n).
Proof. exact (MK_COMB (@lem197714 n) (@lem197709 m q n)). Qed.
Lemma lem197716 (q : nat) (n : nat) : (term162 q n) = (term162 q n).
Proof. exact (fun_ext (fun m : nat => @lem197715 m q n)). Qed.
Lemma lem197717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197718 (q : nat) (n : nat) : (term164 q n) = (term164 q n).
Proof. exact (MK_COMB (@lem197717) (@lem197716 q n)). Qed.
Lemma lem197719 (n : nat) : (term166 n) = (term166 n).
Proof. exact (fun_ext (fun q : nat => @lem197718 q n)). Qed.
Lemma lem197720 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197721 (n : nat) : (term168 n) = (term168 n).
Proof. exact (MK_COMB (@lem197720) (@lem197719 n)). Qed.
Lemma lem197722 : term170 = term170.
Proof. exact (fun_ext (fun n : nat => @lem197721 n)). Qed.
Lemma lem197723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197724 : term172 = term172.
Proof. exact (MK_COMB (@lem197723) (@lem197722)). Qed.
Lemma lem197779 : term171 = term172.
Proof. exact (TRANS (@lem197666) (@lem197724)). Qed.
Lemma lem197780 : term172 = term171.
Proof. exact (SYM (@lem197779)). Qed.
Lemma lem197783 (q : nat) (n : nat) (h1 : term145 q n) : term145 q n.
Proof. exact (h1). Qed.
Lemma lem197784 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem197785 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem197791 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem197799 (P : nat -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem197800 (q : nat) (n : nat) : (term179 q n) = (term180 q n).
Proof. exact (@lem197799 (term132 q n)). Qed.
Lemma lem197801 (q : nat) (n : nat) (q' : nat) : (term133 q n q') = ((Nat.mul n q) = (Nat.mul n q')).
Proof. exact (eq_refl (term133 q n q')). Qed.
Lemma lem197802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem197804 (q : nat) (n : nat) (q' : nat) : (term181 q n q') = (term182 q n q').
Proof. exact (MK_COMB (@lem197802) (@lem197801 q n q')). Qed.
Lemma lem197805 (q : nat) (n : nat) : (term183 q n) = (term184 q n).
Proof. exact (fun_ext (fun q' : nat => @lem197804 q n q')). Qed.
Lemma lem197806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197807 (q : nat) (n : nat) : (term180 q n) = (term185 q n).
Proof. exact (MK_COMB (@lem197806) (@lem197805 q n)). Qed.
Lemma lem197808 (q : nat) (n : nat) : (term179 q n) = (term185 q n).
Proof. exact (TRANS (@lem197800 q n) (@lem197807 q n)). Qed.
Lemma lem197809 (n : nat) : (term186 n) = (term186 n).
Proof. exact (eq_refl (term186 n)). Qed.
Lemma lem197810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem197811 (q : nat) (n : nat) : (term187 q n) = (term188 q n).
Proof. exact (MK_COMB (@lem197810) (@lem197808 q n)). Qed.
Lemma lem197812 (q : nat) (n : nat) : (term189 q n) = (term190 q n).
Proof. exact (MK_COMB (@lem197811 q n) (@lem197809 n)). Qed.
Lemma lem197813 (q : nat) (n : nat) : (term145 q n) = (term189 q n).
Proof. exact (@lem17045 (term141 q n) (term110 n)). Qed.
Lemma lem197822 (q : nat) (n : nat) : (term145 q n) = (term190 q n).
Proof. exact (TRANS (@lem197813 q n) (@lem197812 q n)). Qed.
Lemma lem197823 (q : nat) (n : nat) (h1 : term145 q n) : term190 q n.
Proof. exact (EQ_MP (@lem197822 q n) (@lem197783 q n h1)). Qed.
Lemma lem197838 (m : nat) : ((term177 m) = (m = (NUMERAL 0))) = (term191 m).
Proof. exact (@lem17784 (term177 m) (m = (NUMERAL 0))). Qed.
Lemma lem197839 : term178 = term192.
Proof. exact (fun_ext (fun m : nat => @lem197838 m)). Qed.
Lemma lem197840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197841 : term0 = term193.
Proof. exact (MK_COMB (@lem197840) (@lem197839)). Qed.
Lemma lem197843 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem197844 (P : nat -> Prop) (Q : nat -> Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem197843 nat P Q). Qed.
Lemma lem197845 : term198 = term199.
Proof. exact (@lem197844 term200 term201). Qed.
Lemma lem197846 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem197847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197848 (m : nat) : (term204 m) = (term205 m).
Proof. exact (MK_COMB (@lem197847) (@lem197846 m)). Qed.
Lemma lem197849 (m : nat) : (term206 m) = (term207 m).
Proof. exact (eq_refl (term206 m)). Qed.
Lemma lem197850 (m : nat) : (term208 m) = (term191 m).
Proof. exact (MK_COMB (@lem197848 m) (@lem197849 m)). Qed.
Lemma lem197851 : term209 = term192.
Proof. exact (fun_ext (fun m : nat => @lem197850 m)). Qed.
Lemma lem197852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197853 : term198 = term193.
Proof. exact (MK_COMB (@lem197852) (@lem197851)). Qed.
Lemma lem197854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem197855 : term210 = term211.
Proof. exact (MK_COMB (@lem197854) (@lem197853)). Qed.
Lemma lem197856 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem197857 : term212 = term200.
Proof. exact (fun_ext (fun m : nat => @lem197856 m)). Qed.
Lemma lem197858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197859 : term213 = term214.
Proof. exact (MK_COMB (@lem197858) (@lem197857)). Qed.
Lemma lem197860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem197861 : term215 = term216.
Proof. exact (MK_COMB (@lem197860) (@lem197859)). Qed.
Lemma lem197862 (m : nat) : (term206 m) = (term207 m).
Proof. exact (eq_refl (term206 m)). Qed.
Lemma lem197863 : term217 = term201.
Proof. exact (fun_ext (fun m : nat => @lem197862 m)). Qed.
Lemma lem197864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197865 : term218 = term219.
Proof. exact (MK_COMB (@lem197864) (@lem197863)). Qed.
Lemma lem197866 : term199 = term220.
Proof. exact (MK_COMB (@lem197861) (@lem197865)). Qed.
Lemma lem197867 : (term198 = term199) = (term193 = term220).
Proof. exact (MK_COMB (@lem197855) (@lem197866)). Qed.
Lemma lem197966 : term193 = term220.
Proof. exact (EQ_MP (@lem197867) (@lem197845)). Qed.
Lemma lem197967 : term0 = term220.
Proof. exact (TRANS (@lem197841) (@lem197966)). Qed.
Lemma lem197968 (h1 : term0) : term220.
Proof. exact (EQ_MP (@lem197967) (@lem197784 h1)). Qed.
Lemma lem197972 (m : nat) (n : nat) : (term221 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem197974 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem197975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem197976 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (MK_COMB (@lem197975) (@lem197972 m n)). Qed.
Lemma lem197977 (n : nat) (m : nat) : (term224 n m) = (term225 n m).
Proof. exact (MK_COMB (@lem197976 m n) (@lem197974 n m)). Qed.
Lemma lem197982 (n : nat) (m : nat) : (term226 n m) = (term226 n m).
Proof. exact (eq_refl (term226 n m)). Qed.
Lemma lem197983 (n : nat) (m : nat) : (term227 n m) = (term228 n m).
Proof. exact (MK_COMB (@lem197982 n m) (@lem197977 n m)). Qed.
Lemma lem197984 (n : nat) (m : nat) : ((term173 m n) = (Peano.lt n m)) = (term227 n m).
Proof. exact (@lem17784 (term173 m n) (Peano.lt n m)). Qed.
Lemma lem197985 (n : nat) (m : nat) : ((term173 m n) = (Peano.lt n m)) = (term228 n m).
Proof. exact (TRANS (@lem197984 n m) (@lem197983 n m)). Qed.
Lemma lem197986 (m : nat) : (term174 m) = (term229 m).
Proof. exact (fun_ext (fun n : nat => @lem197985 n m)). Qed.
Lemma lem197987 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197988 (m : nat) : (term175 m) = (term230 m).
Proof. exact (MK_COMB (@lem197987) (@lem197986 m)). Qed.
Lemma lem197989 : term176 = term231.
Proof. exact (fun_ext (fun m : nat => @lem197988 m)). Qed.
Lemma lem197990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem197991 : term150 = term232.
Proof. exact (MK_COMB (@lem197990) (@lem197989)). Qed.
Lemma lem197997 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem197998 (P : nat -> Prop) (Q : nat -> Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem197997 nat P Q). Qed.
Lemma lem197999 (m : nat) : (term233 m) = (term234 m).
Proof. exact (@lem197998 (term235 m) (term236 m)). Qed.
Lemma lem198000 (n : nat) (m : nat) : (term237 m n) = (term238 n m).
Proof. exact (eq_refl (term237 m n)). Qed.
Lemma lem198001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198002 (n : nat) (m : nat) : (term239 m n) = (term226 n m).
Proof. exact (MK_COMB (@lem198001) (@lem198000 n m)). Qed.
Lemma lem198003 (n : nat) (m : nat) : (term240 m n) = (term225 n m).
Proof. exact (eq_refl (term240 m n)). Qed.
Lemma lem198004 (n : nat) (m : nat) : (term241 m n) = (term228 n m).
Proof. exact (MK_COMB (@lem198002 n m) (@lem198003 n m)). Qed.
Lemma lem198005 (m : nat) : (term242 m) = (term229 m).
Proof. exact (fun_ext (fun n : nat => @lem198004 n m)). Qed.
Lemma lem198006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198007 (m : nat) : (term233 m) = (term230 m).
Proof. exact (MK_COMB (@lem198006) (@lem198005 m)). Qed.
Lemma lem198008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem198009 (m : nat) : (term243 m) = (term244 m).
Proof. exact (MK_COMB (@lem198008) (@lem198007 m)). Qed.
Lemma lem198010 (n : nat) (m : nat) : (term237 m n) = (term238 n m).
Proof. exact (eq_refl (term237 m n)). Qed.
Lemma lem198011 (m : nat) : (term245 m) = (term235 m).
Proof. exact (fun_ext (fun n : nat => @lem198010 n m)). Qed.
Lemma lem198012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198013 (m : nat) : (term246 m) = (term247 m).
Proof. exact (MK_COMB (@lem198012) (@lem198011 m)). Qed.
Lemma lem198014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198015 (m : nat) : (term248 m) = (term249 m).
Proof. exact (MK_COMB (@lem198014) (@lem198013 m)). Qed.
Lemma lem198016 (n : nat) (m : nat) : (term240 m n) = (term225 n m).
Proof. exact (eq_refl (term240 m n)). Qed.
Lemma lem198017 (m : nat) : (term250 m) = (term236 m).
Proof. exact (fun_ext (fun n : nat => @lem198016 n m)). Qed.
Lemma lem198018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198019 (m : nat) : (term251 m) = (term252 m).
Proof. exact (MK_COMB (@lem198018) (@lem198017 m)). Qed.
Lemma lem198020 (m : nat) : (term234 m) = (term253 m).
Proof. exact (MK_COMB (@lem198015 m) (@lem198019 m)). Qed.
Lemma lem198021 (m : nat) : ((term233 m) = (term234 m)) = ((term230 m) = (term253 m)).
Proof. exact (MK_COMB (@lem198009 m) (@lem198020 m)). Qed.
Lemma lem198022 (m : nat) : (term230 m) = (term253 m).
Proof. exact (EQ_MP (@lem198021 m) (@lem197999 m)). Qed.
Lemma lem198119 : term231 = term254.
Proof. exact (fun_ext (fun m : nat => @lem198022 m)). Qed.
Lemma lem198120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198121 : term232 = term255.
Proof. exact (MK_COMB (@lem198120) (@lem198119)). Qed.
Lemma lem198123 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem198124 (P : nat -> Prop) (Q : nat -> Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem198123 nat P Q). Qed.
Lemma lem198125 : term256 = term257.
Proof. exact (@lem198124 term258 term259). Qed.
Lemma lem198126 (m : nat) : (term260 m) = (term247 m).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem198127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198128 (m : nat) : (term261 m) = (term249 m).
Proof. exact (MK_COMB (@lem198127) (@lem198126 m)). Qed.
Lemma lem198129 (m : nat) : (term262 m) = (term252 m).
Proof. exact (eq_refl (term262 m)). Qed.
Lemma lem198130 (m : nat) : (term263 m) = (term253 m).
Proof. exact (MK_COMB (@lem198128 m) (@lem198129 m)). Qed.
Lemma lem198131 : term264 = term254.
Proof. exact (fun_ext (fun m : nat => @lem198130 m)). Qed.
Lemma lem198132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198133 : term256 = term255.
Proof. exact (MK_COMB (@lem198132) (@lem198131)). Qed.
Lemma lem198134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem198135 : term265 = term266.
Proof. exact (MK_COMB (@lem198134) (@lem198133)). Qed.
Lemma lem198136 (m : nat) : (term260 m) = (term247 m).
Proof. exact (eq_refl (term260 m)). Qed.
Lemma lem198137 : term267 = term258.
Proof. exact (fun_ext (fun m : nat => @lem198136 m)). Qed.
Lemma lem198138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198139 : term268 = term269.
Proof. exact (MK_COMB (@lem198138) (@lem198137)). Qed.
Lemma lem198140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198141 : term270 = term271.
Proof. exact (MK_COMB (@lem198140) (@lem198139)). Qed.
Lemma lem198142 (m : nat) : (term262 m) = (term252 m).
Proof. exact (eq_refl (term262 m)). Qed.
Lemma lem198143 : term272 = term259.
Proof. exact (fun_ext (fun m : nat => @lem198142 m)). Qed.
Lemma lem198144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198145 : term273 = term274.
Proof. exact (MK_COMB (@lem198144) (@lem198143)). Qed.
Lemma lem198146 : term257 = term275.
Proof. exact (MK_COMB (@lem198141) (@lem198145)). Qed.
Lemma lem198147 : (term256 = term257) = (term255 = term275).
Proof. exact (MK_COMB (@lem198135) (@lem198146)). Qed.
Lemma lem198148 : term255 = term275.
Proof. exact (EQ_MP (@lem198147) (@lem198125)). Qed.
Lemma lem198255 : term232 = term275.
Proof. exact (TRANS (@lem198121) (@lem198148)). Qed.
Lemma lem198256 : term150 = term275.
Proof. exact (TRANS (@lem197991) (@lem198255)). Qed.
Lemma lem198257 (h1 : term150) : term275.
Proof. exact (EQ_MP (@lem198256) (@lem197785 h1)). Qed.
Lemma lem198267 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem198286 (n : nat) : (term186 n) = (term186 n).
Proof. exact (eq_refl (term186 n)). Qed.
Lemma lem198301 (q : nat) (n : nat) (q' : nat) : (term182 q n q') = (term182 q n q').
Proof. exact (eq_refl (term182 q n q')). Qed.
Lemma lem198302 (q : nat) (n : nat) : (term184 q n) = (term184 q n).
Proof. exact (fun_ext (fun q' : nat => @lem198301 q n q')). Qed.
Lemma lem198303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198304 (q : nat) (n : nat) : (term185 q n) = (term185 q n).
Proof. exact (MK_COMB (@lem198303) (@lem198302 q n)). Qed.
Lemma lem198305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem198306 (q : nat) (n : nat) : (term188 q n) = (term188 q n).
Proof. exact (MK_COMB (@lem198305) (@lem198304 q n)). Qed.
Lemma lem198307 (q : nat) (n : nat) : (term190 q n) = (term190 q n).
Proof. exact (MK_COMB (@lem198306 q n) (@lem198286 n)). Qed.
Lemma lem198308 (q : nat) (n : nat) (h1 : term145 q n) : term190 q n.
Proof. exact (EQ_MP (@lem198307 q n) (@lem197823 q n h1)). Qed.
Lemma lem198327 (m : nat) : (term207 m) = (term207 m).
Proof. exact (eq_refl (term207 m)). Qed.
Lemma lem198328 : term201 = term201.
Proof. exact (fun_ext (fun m : nat => @lem198327 m)). Qed.
Lemma lem198329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198330 : term219 = term219.
Proof. exact (MK_COMB (@lem198329) (@lem198328)). Qed.
Lemma lem198349 (m : nat) : (term203 m) = (term203 m).
Proof. exact (eq_refl (term203 m)). Qed.
Lemma lem198350 : term200 = term200.
Proof. exact (fun_ext (fun m : nat => @lem198349 m)). Qed.
Lemma lem198351 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198352 : term214 = term214.
Proof. exact (MK_COMB (@lem198351) (@lem198350)). Qed.
Lemma lem198353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198354 : term216 = term216.
Proof. exact (MK_COMB (@lem198353) (@lem198352)). Qed.
Lemma lem198355 : term220 = term220.
Proof. exact (MK_COMB (@lem198354) (@lem198330)). Qed.
Lemma lem198356 (h1 : term0) : term220.
Proof. exact (EQ_MP (@lem198355) (@lem197968 h1)). Qed.
Lemma lem198369 (n : nat) (m : nat) : (term225 n m) = (term225 n m).
Proof. exact (eq_refl (term225 n m)). Qed.
Lemma lem198370 (m : nat) : (term236 m) = (term236 m).
Proof. exact (fun_ext (fun n : nat => @lem198369 n m)). Qed.
Lemma lem198371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198372 (m : nat) : (term252 m) = (term252 m).
Proof. exact (MK_COMB (@lem198371) (@lem198370 m)). Qed.
Lemma lem198373 : term259 = term259.
Proof. exact (fun_ext (fun m : nat => @lem198372 m)). Qed.
Lemma lem198374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198375 : term274 = term274.
Proof. exact (MK_COMB (@lem198374) (@lem198373)). Qed.
Lemma lem198392 (n : nat) (m : nat) : (term238 n m) = (term238 n m).
Proof. exact (eq_refl (term238 n m)). Qed.
Lemma lem198393 (m : nat) : (term235 m) = (term235 m).
Proof. exact (fun_ext (fun n : nat => @lem198392 n m)). Qed.
Lemma lem198394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198395 (m : nat) : (term247 m) = (term247 m).
Proof. exact (MK_COMB (@lem198394) (@lem198393 m)). Qed.
Lemma lem198396 : term258 = term258.
Proof. exact (fun_ext (fun m : nat => @lem198395 m)). Qed.
Lemma lem198397 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198398 : term269 = term269.
Proof. exact (MK_COMB (@lem198397) (@lem198396)). Qed.
Lemma lem198399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem198400 : term271 = term271.
Proof. exact (MK_COMB (@lem198399) (@lem198398)). Qed.
Lemma lem198401 : term275 = term275.
Proof. exact (MK_COMB (@lem198400) (@lem198375)). Qed.
Lemma lem198402 (h1 : term150) : term275.
Proof. exact (EQ_MP (@lem198401) (@lem198257 h1)). Qed.
Lemma lem198403 (h1 : term150) : term274.
Proof. exact (proj2 (@lem198402 h1)). Qed.
Lemma lem198405 (h1 : term0) : term219.
Proof. exact (proj2 (@lem198356 h1)). Qed.
Lemma lem198407 (q : nat) (n : nat) (h1 : term185 q n) : term185 q n.
Proof. exact (h1). Qed.
Lemma lem198476 (q : nat) (n : nat) (q' : nat) : (term182 q n q') = (term182 q n q').
Proof. exact (eq_refl (term182 q n q')). Qed.
Lemma lem198477 (q : nat) (n : nat) : (term184 q n) = (term184 q n).
Proof. exact (fun_ext (fun q' : nat => @lem198476 q n q')). Qed.
Lemma lem198478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198480 (q : nat) (n : nat) : (term185 q n) = (term185 q n).
Proof. exact (MK_COMB (@lem198478) (@lem198477 q n)). Qed.
Lemma lem198481 (q : nat) (n : nat) (h1 : term185 q n) : term185 q n.
Proof. exact (EQ_MP (@lem198480 q n) (@lem198407 q n h1)). Qed.
Lemma lem198485 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem198513 (n : nat) (m : nat) : (term225 n m) = (term225 n m).
Proof. exact (eq_refl (term225 n m)). Qed.
Lemma lem198514 (m : nat) : (term236 m) = (term236 m).
Proof. exact (fun_ext (fun n : nat => @lem198513 n m)). Qed.
Lemma lem198515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198516 (m : nat) : (term252 m) = (term252 m).
Proof. exact (MK_COMB (@lem198515) (@lem198514 m)). Qed.
Lemma lem198517 : term259 = term259.
Proof. exact (fun_ext (fun m : nat => @lem198516 m)). Qed.
Lemma lem198518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198520 : term274 = term274.
Proof. exact (MK_COMB (@lem198518) (@lem198517)). Qed.
Lemma lem198521 (h1 : term150) : term274.
Proof. exact (EQ_MP (@lem198520) (@lem198403 h1)). Qed.
Lemma lem198542 (m : nat) : (term207 m) = (term207 m).
Proof. exact (eq_refl (term207 m)). Qed.
Lemma lem198543 : term201 = term201.
Proof. exact (fun_ext (fun m : nat => @lem198542 m)). Qed.
Lemma lem198544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem198546 : term219 = term219.
Proof. exact (MK_COMB (@lem198544) (@lem198543)). Qed.
Lemma lem198547 (h1 : term0) : term219.
Proof. exact (EQ_MP (@lem198546) (@lem198405 h1)). Qed.
Lemma lem198551 (n : nat) (h1 : term186 n) : term186 n.
Proof. exact (h1). Qed.
Lemma lem198570 (_3968 : nat) (q : nat) (n : nat) (h1 : term185 q n) : term276 q n _3968.
Proof. exact (@lem198481 q n h1 _3968). Qed.
Lemma lem198571 (q : nat) (n : nat) (_3968 : nat) : (term276 q n _3968) = (term182 q n _3968).
Proof. exact (eq_refl (term276 q n _3968)). Qed.
Lemma lem198579 (_3971 : nat) (h1 : term150) : term262 _3971.
Proof. exact (@lem198521 h1 _3971). Qed.
Lemma lem198580 (_3971 : nat) : (term262 _3971) = (term252 _3971).
Proof. exact (eq_refl (term262 _3971)). Qed.
Lemma lem198581 (_3971 : nat) (h1 : term150) : term252 _3971.
Proof. exact (EQ_MP (@lem198580 _3971) (@lem198579 _3971 h1)). Qed.
Lemma lem198582 (_3971 : nat) (_3972 : nat) (h1 : term150) : term240 _3971 _3972.
Proof. exact (@lem198581 _3971 h1 _3972). Qed.
Lemma lem198583 (_3972 : nat) (_3971 : nat) : (term240 _3971 _3972) = (term225 _3972 _3971).
Proof. exact (eq_refl (term240 _3971 _3972)). Qed.
Lemma lem198588 (_3974 : nat) (h1 : term0) : term206 _3974.
Proof. exact (@lem198547 h1 _3974). Qed.
Lemma lem198589 (_3974 : nat) : (term206 _3974) = (term207 _3974).
Proof. exact (eq_refl (term206 _3974)). Qed.
Lemma lem198622 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem198650 (n : nat) (h1 : term186 n) : term186 n.
Proof. exact (h1). Qed.
Lemma lem198748 (_3968 : nat) (q : nat) (n : nat) (h1 : term185 q n) : term182 q n _3968.
Proof. exact (EQ_MP (@lem198571 q n _3968) (@lem198570 _3968 q n h1)). Qed.
Lemma lem198776 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem198804 (_3972 : nat) (_3971 : nat) (h1 : term150) : term225 _3972 _3971.
Proof. exact (EQ_MP (@lem198583 _3972 _3971) (@lem198582 _3971 _3972 h1)). Qed.
Lemma lem198832 (_3974 : nat) (h1 : term0) : term207 _3974.
Proof. exact (EQ_MP (@lem198589 _3974) (@lem198588 _3974 h1)). Qed.
Lemma lem198846 (n : nat) (h1 : term186 n) : term186 n.
Proof. exact (h1). Qed.
Lemma lem198911 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem198912 (n : nat) (q : nat) : (Nat.mul n q) = (Nat.mul n q).
Proof. exact (@lem198911 (Nat.mul n q)). Qed.
Lemma lem198913 (n : nat) (q : nat) : term277 n q.
Proof. exact (fun h0 : term278 n q => @lem198912 n q). Qed.
Lemma lem198915 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem198916 (n : nat) (q : nat) : (term277 n q) = ((Nat.mul n q) = (Nat.mul n q)).
Proof. exact (@lem198915 ((Nat.mul n q) = (Nat.mul n q))). Qed.
Lemma lem198917 (n : nat) (q : nat) : (Nat.mul n q) = (Nat.mul n q).
Proof. exact (EQ_MP (@lem198916 n q) (@lem198913 n q)). Qed.
Lemma lem198920 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem198922 (q : nat) (n : nat) (_3968 : nat) : (term182 q n _3968) = (term279 q n _3968).
Proof. exact (@lem198920 ((Nat.mul n q) = (Nat.mul n _3968))). Qed.
Lemma lem198925 (_3968 : nat) (q : nat) (n : nat) (h1 : term185 q n) : term279 q n _3968.
Proof. exact (EQ_MP (@lem198922 q n _3968) (@lem198748 _3968 q n h1)). Qed.
Lemma lem198926 (q : nat) (n : nat) (h1 : term185 q n) : term280 n q.
Proof. exact (@lem198925 q q n h1). Qed.
Lemma lem198929 (q : nat) (n : nat) (h1 : term185 q n) : False.
Proof. exact (@lem198926 q n h1 (@lem198917 n q)). Qed.
Lemma lem198930 (q : nat) (n : nat) (h1 : term185 q n) : term102.
Proof. exact (fun h0 : ~ False => @lem198929 q n h1). Qed.
Lemma lem198932 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem198933 : term102 = False.
Proof. exact (@lem198932 False). Qed.
Lemma lem198984 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (h1). Qed.
Lemma lem198985 (n : nat) (h1 : term27 n) : term281 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem198984 n h1). Qed.
Lemma lem198987 (p : Prop) : (term282 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem198988 (n : nat) : (term281 n) = (term27 n).
Proof. exact (@lem198987 (n = (NUMERAL 0))). Qed.
Lemma lem198989 (n : nat) (h1 : term27 n) : term27 n.
Proof. exact (EQ_MP (@lem198988 n) (@lem198985 n h1)). Qed.
Lemma lem198991 (b : Prop) (a : Prop) : (a \/ b) = (term283 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem198994 (_3974 : nat) : (term207 _3974) = (term284 _3974).
Proof. exact (@lem198991 (_3974 = (NUMERAL 0)) (term285 _3974)). Qed.
Lemma lem198997 (_3974 : nat) (h1 : term0) : term284 _3974.
Proof. exact (EQ_MP (@lem198994 _3974) (@lem198832 _3974 h1)). Qed.
Lemma lem198998 (n : nat) (h1 : term0) : term284 n.
Proof. exact (@lem198997 n h1). Qed.
Lemma lem199001 (n : nat) (h1 : term0) (h2 : term27 n) : term285 n.
Proof. exact (@lem198998 n h1 (@lem198989 n h2)). Qed.
Lemma lem199002 (n : nat) (h1 : term0) (h2 : term27 n) : term286 n.
Proof. exact (fun h0 : term177 n => @lem199001 n h1 h2). Qed.
Lemma lem199004 (p : Prop) : (term282 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem199005 (n : nat) : (term286 n) = (term285 n).
Proof. exact (@lem199004 (term177 n)). Qed.
Lemma lem199006 (n : nat) (h1 : term0) (h2 : term27 n) : term285 n.
Proof. exact (EQ_MP (@lem199005 n) (@lem199002 n h1 h2)). Qed.
Lemma lem199012 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem199013 (_3971 : nat) (_3972 : nat) : (term225 _3972 _3971) = (term287 _3971 _3972).
Proof. exact (@lem199012 (Peano.lt _3972 _3971) (Peano.le _3971 _3972)). Qed.
Lemma lem199019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem199020 (_3971 : nat) (_3972 : nat) : (term288 _3972 _3971) = (term289 _3971 _3972).
Proof. exact (MK_COMB (@lem199019) (@lem199013 _3971 _3972)). Qed.
Lemma lem199026 (_3971 : nat) (_3972 : nat) : (term287 _3971 _3972) = (term287 _3971 _3972).
Proof. exact (eq_refl (term287 _3971 _3972)). Qed.
Lemma lem199027 (_3971 : nat) (_3972 : nat) : ((term225 _3972 _3971) = (term287 _3971 _3972)) = ((term287 _3971 _3972) = (term287 _3971 _3972)).
Proof. exact (MK_COMB (@lem199020 _3971 _3972) (@lem199026 _3971 _3972)). Qed.
Lemma lem199029 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem199030 (x : Prop) : (x = x) = True.
Proof. exact (@lem199029 Prop x). Qed.
Lemma lem199031 (_3971 : nat) (_3972 : nat) : ((term287 _3971 _3972) = (term287 _3971 _3972)) = True.
Proof. exact (@lem199030 (term287 _3971 _3972)). Qed.
Lemma lem199032 (_3971 : nat) (_3972 : nat) : ((term225 _3972 _3971) = (term287 _3971 _3972)) = True.
Proof. exact (TRANS (@lem199027 _3971 _3972) (@lem199031 _3971 _3972)). Qed.
Lemma lem199033 (_3971 : nat) (_3972 : nat) : True = ((term225 _3972 _3971) = (term287 _3971 _3972)).
Proof. exact (SYM (@lem199032 _3971 _3972)). Qed.
Lemma lem199034 (_3971 : nat) (_3972 : nat) : (term225 _3972 _3971) = (term287 _3971 _3972).
Proof. exact (EQ_MP (@lem199033 _3971 _3972) (@lem0)). Qed.
Lemma lem199035 (_3971 : nat) (_3972 : nat) (h1 : term150) : term287 _3971 _3972.
Proof. exact (EQ_MP (@lem199034 _3971 _3972) (@lem198804 _3972 _3971 h1)). Qed.
Lemma lem199037 (b : Prop) (a : Prop) : (a \/ b) = (term283 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem199040 (_3972 : nat) (_3971 : nat) : (term287 _3971 _3972) = (term290 _3972 _3971).
Proof. exact (@lem199037 (Peano.le _3971 _3972) (Peano.lt _3972 _3971)). Qed.
Lemma lem199043 (_3972 : nat) (_3971 : nat) (h1 : term150) : term290 _3972 _3971.
Proof. exact (EQ_MP (@lem199040 _3972 _3971) (@lem199035 _3971 _3972 h1)). Qed.
Lemma lem199044 (n : nat) (h1 : term150) : term291 n.
Proof. exact (@lem199043 (NUMERAL 0) n h1). Qed.
Lemma lem199047 (n : nat) (h1 : term150) (h2 : term0) (h3 : term27 n) : term110 n.
Proof. exact (@lem199044 n h1 (@lem199006 n h2 h3)). Qed.
Lemma lem199048 (n : nat) (h1 : term150) (h2 : term0) (h3 : term27 n) : term292 n.
Proof. exact (fun h0 : term186 n => @lem199047 n h1 h2 h3). Qed.
Lemma lem199050 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem199051 (n : nat) : (term292 n) = (term110 n).
Proof. exact (@lem199050 (term110 n)). Qed.
Lemma lem199052 (n : nat) (h1 : term150) (h2 : term0) (h3 : term27 n) : term110 n.
Proof. exact (EQ_MP (@lem199051 n) (@lem199048 n h1 h2 h3)). Qed.
Lemma lem199055 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem199057 (n : nat) : (term186 n) = (term293 n).
Proof. exact (@lem199055 (term110 n)). Qed.
Lemma lem199060 (n : nat) (h1 : term186 n) : term293 n.
Proof. exact (EQ_MP (@lem199057 n) (@lem198846 n h1)). Qed.
Lemma lem199063 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (@lem199060 n h3 (@lem199052 n h1 h2 h4)). Qed.
Lemma lem199064 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : term102.
Proof. exact (fun h0 : ~ False => @lem199063 n h1 h2 h3 h4). Qed.
Lemma lem199066 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem199067 : term102 = False.
Proof. exact (@lem199066 False). Qed.
Lemma lem199068 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199067) (@lem199064 n h1 h2 h3 h4)). Qed.
Lemma lem199069 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term186 n) = False.
Proof. exact (prop_ext (fun h5 : term186 n => @lem199068 n h1 h2 h3 h4) (fun h5 : False => @lem198846 n h3)). Qed.
Lemma lem199070 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199069 n h1 h2 h3 h4) (@lem198846 n h3)). Qed.
Lemma lem199071 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199070 n h1 h2 h3 h4) (fun h5 : False => @lem198776 n h4)). Qed.
Lemma lem199073 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199071 n h1 h2 h3 h4) (@lem198776 n h4)). Qed.
Lemma lem199074 (q : nat) (n : nat) (h1 : term185 q n) : False.
Proof. exact (EQ_MP (@lem198933) (@lem198930 q n h1)). Qed.
Lemma lem199075 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term186 n) = False.
Proof. exact (prop_ext (fun h5 : term186 n => @lem199073 n h1 h2 h3 h4) (fun h5 : False => @lem198650 n h3)). Qed.
Lemma lem199076 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199075 n h1 h2 h3 h4) (@lem198650 n h3)). Qed.
Lemma lem199077 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199076 n h1 h2 h3 h4) (fun h5 : False => @lem198622 n h4)). Qed.
Lemma lem199078 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199077 n h1 h2 h3 h4) (@lem198622 n h4)). Qed.
Lemma lem199079 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term186 n) = False.
Proof. exact (prop_ext (fun h5 : term186 n => @lem199078 n h1 h2 h3 h4) (fun h5 : False => @lem198551 n h3)). Qed.
Lemma lem199080 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199079 n h1 h2 h3 h4) (@lem198551 n h3)). Qed.
Lemma lem199081 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199080 n h1 h2 h3 h4) (fun h5 : False => @lem198485 n h4)). Qed.
Lemma lem199082 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199081 n h1 h2 h3 h4) (@lem198485 n h4)). Qed.
Lemma lem199083 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term186 n) = False.
Proof. exact (prop_ext (fun h5 : term186 n => @lem199082 n h1 h2 h3 h4) (fun h5 : False => @lem198551 n h3)). Qed.
Lemma lem199084 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199083 n h1 h2 h3 h4) (@lem198551 n h3)). Qed.
Lemma lem199085 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199084 n h1 h2 h3 h4) (fun h5 : False => @lem198485 n h4)). Qed.
Lemma lem199086 (n : nat) (h1 : term150) (h2 : term0) (h3 : term186 n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199085 n h1 h2 h3 h4) (@lem198485 n h4)). Qed.
Lemma lem199087 (q : nat) (n : nat) (h1 : term185 q n) : (term185 q n) = False.
Proof. exact (prop_ext (fun h2 : term185 q n => @lem199074 q n h1) (fun h2 : False => @lem198481 q n h1)). Qed.
Lemma lem199088 (q : nat) (n : nat) (h1 : term185 q n) : False.
Proof. exact (EQ_MP (@lem199087 q n h1) (@lem198481 q n h1)). Qed.
Lemma lem199089 (q : nat) (n : nat) (h1 : term150) (h2 : term0) (h3 : term145 q n) (h4 : term27 n) : False.
Proof. exact (or_elim (@lem198308 q n h3) (fun h0 : term185 q n => @lem199088 q n h0) (fun h0 : term186 n => @lem199086 n h1 h2 h0 h4)). Qed.
Lemma lem199090 (q : nat) (n : nat) (h1 : term150) (h2 : term0) (h3 : term145 q n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199089 q n h1 h2 h3 h4) (fun h5 : False => @lem198267 n h4)). Qed.
Lemma lem199091 (q : nat) (n : nat) (h1 : term150) (h2 : term0) (h3 : term145 q n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199090 q n h1 h2 h3 h4) (@lem198267 n h4)). Qed.
Lemma lem199092 (q : nat) (n : nat) (h1 : term150) (h2 : term0) (h3 : term145 q n) (h4 : term27 n) : (term27 n) = False.
Proof. exact (prop_ext (fun h5 : term27 n => @lem199091 q n h1 h2 h3 h4) (fun h5 : False => @lem197791 n h4)). Qed.
Lemma lem199093 (q : nat) (n : nat) (h1 : term150) (h2 : term0) (h3 : term145 q n) (h4 : term27 n) : False.
Proof. exact (EQ_MP (@lem199092 q n h1 h2 h3 h4) (@lem197791 n h4)). Qed.
Lemma lem199094 (q : nat) (n : nat) (h1 : term0) (h2 : term145 q n) (h3 : term27 n) : term148.
Proof. exact (fun h0 : term150 => @lem199093 q n h0 h1 h2 h3). Qed.
Lemma lem199095 : term148 = term149.
Proof. exact (@lem69 term150). Qed.
Lemma lem199096 (q : nat) (n : nat) (h1 : term0) (h2 : term145 q n) (h3 : term27 n) : term149.
Proof. exact (EQ_MP (@lem199095) (@lem199094 q n h1 h2 h3)). Qed.
Lemma lem199097 (q : nat) (n : nat) (h1 : term145 q n) (h2 : term27 n) : term153.
Proof. exact (fun h0 : term0 => @lem199096 q n h0 h1 h2). Qed.
Lemma lem199098 (q : nat) (n : nat) (h1 : term27 n) : term155 q n.
Proof. exact (fun h0 : term145 q n => @lem199097 q n h0 h1). Qed.
Lemma lem199099 (m : nat) (q : nat) (n : nat) (h1 : term27 n) : term158 m q n.
Proof. exact (fun h0 : m = (Nat.mul q n) => @lem199098 q n h1). Qed.
Lemma lem199100 (m : nat) (q : nat) (n : nat) : term160 m q n.
Proof. exact (fun h0 : term27 n => @lem199099 m q n h0). Qed.
Lemma lem199105 (q : nat) (n : nat) : term164 q n.
Proof. exact (fun m : nat => @lem199100 m q n). Qed.
Lemma lem199110 (n : nat) : term168 n.
Proof. exact (fun q : nat => @lem199105 q n). Qed.
Lemma lem199115 : term172.
Proof. exact (fun n : nat => @lem199110 n). Qed.
Lemma lem199116 : term171.
Proof. exact (EQ_MP (@lem197780) (@lem199115)). Qed.
Lemma lem199117 (n : nat) : term294 n.
Proof. exact (@lem199116 n). Qed.
Lemma lem199118 (n : nat) : (term294 n) = (term167 n).
Proof. exact (eq_refl (term294 n)). Qed.
Lemma lem199119 (n : nat) : term167 n.
Proof. exact (EQ_MP (@lem199118 n) (@lem199117 n)). Qed.
Lemma lem199120 (n : nat) (q : nat) : term295 n q.
Proof. exact (@lem199119 n q). Qed.
Lemma lem199121 (q : nat) (n : nat) : (term295 n q) = (term163 q n).
Proof. exact (eq_refl (term295 n q)). Qed.
Lemma lem199122 (q : nat) (n : nat) : term163 q n.
Proof. exact (EQ_MP (@lem199121 q n) (@lem199120 n q)). Qed.
Lemma lem199123 (q : nat) (n : nat) (m : nat) : term296 q n m.
Proof. exact (@lem199122 q n m). Qed.
Lemma lem199124 (m : nat) (q : nat) (n : nat) : (term296 q n m) = (term122 m q n).
Proof. exact (eq_refl (term296 q n m)). Qed.
Lemma lem199125 (m : nat) (q : nat) (n : nat) : term122 m q n.
Proof. exact (EQ_MP (@lem199124 m q n) (@lem199123 q n m)). Qed.
Lemma lem199127 (m : nat) (q : nat) (n : nat) : term122 m q n.
Proof. exact (@lem197537 m q n (@lem199125 m q n)). Qed.
Lemma lem199128 (m : nat) (q : nat) (n : nat) (h1 : term27 n) : term157 m q n.
Proof. exact (@lem199127 m q n (@lem196547 n h1)). Qed.
Lemma lem199129 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : term154 q n.
Proof. exact (@lem199128 m q n h1 (@lem196705 m q n h2)). Qed.
Lemma lem199130 (m : nat) (q : nat) (n : nat) (h1 : term121 q n) (h2 : term27 n) (h3 : m = (Nat.mul q n)) : term152.
Proof. exact (@lem199129 m q n h2 h3 (@lem197522 q n h1)). Qed.
Lemma lem199131 (m : nat) (q : nat) (n : nat) (h1 : term121 q n) (h2 : term27 n) (h3 : m = (Nat.mul q n)) : term148.
Proof. exact (@lem199130 m q n h1 h2 h3 (@lem196470)). Qed.
Lemma lem199132 (m : nat) (q : nat) (n : nat) (h1 : term121 q n) (h2 : term27 n) (h3 : m = (Nat.mul q n)) : False.
Proof. exact (@lem199131 m q n h1 h2 h3 (@lem97961)). Qed.
Lemma lem199133 (m : nat) (q : nat) (n : nat) (h1 : term121 q n) (h2 : term27 n) (h3 : m = (Nat.mul q n)) : (term121 q n) = False.
Proof. exact (prop_ext (fun h4 : term121 q n => @lem199132 m q n h1 h2 h3) (fun h4 : False => @lem197522 q n h1)). Qed.
Lemma lem199134 (m : nat) (q : nat) (n : nat) (h1 : term121 q n) (h2 : term27 n) (h3 : m = (Nat.mul q n)) : False.
Proof. exact (EQ_MP (@lem199133 m q n h1 h2 h3) (@lem197522 q n h1)). Qed.
Lemma lem199135 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : term120 q n.
Proof. exact (fun h0 : term121 q n => @lem199134 m q n h0 h1 h2). Qed.
Lemma lem199136 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : term119 q n.
Proof. exact (EQ_MP (@lem197521 q n) (@lem199135 m q n h1 h2)). Qed.
Lemma lem199137 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : term118 m n.
Proof. exact (EQ_MP (@lem197517 m q n h2) (@lem199136 m q n h1 h2)). Qed.
Lemma lem199138 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (@lem197298 m n (@lem199137 m q n h1 h2)). Qed.
Lemma lem199139 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : (m = (Nat.mul q n)) = ((Nat.modulo m n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h3 : m = (Nat.mul q n) => @lem199138 m q n h1 h2) (fun h3 : (Nat.modulo m n) = (NUMERAL 0) => @lem196705 m q n h2)). Qed.
Lemma lem199140 (m : nat) (q : nat) (n : nat) (h1 : term27 n) (h2 : m = (Nat.mul q n)) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem199139 m q n h1 h2) (@lem196705 m q n h2)). Qed.
Lemma lem199141 (m : nat) (n : nat) (h1 : term47 m n) (h2 : term27 n) : (Nat.modulo m n) = (NUMERAL 0).
Proof. exact (ex_elim (@lem196704 m n h1) (fun q : nat => fun h0 : term45 m n q => @lem199140 m q n h2 h0)). Qed.
Lemma lem199142 (m : nat) (n : nat) (h1 : term27 n) : term297 m n.
Proof. exact (fun h0 : term47 m n => @lem199141 m n h0 h1). Qed.
Lemma lem199143 (m : nat) (n : nat) (h1 : term27 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : ((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n).
Proof. exact (prop_ext (fun h3 : (Nat.modulo m n) = (NUMERAL 0) => @lem197295 m n h1 h2) (fun h3 : term47 m n => @lem196703 m n h2)). Qed.
Lemma lem199144 (m : nat) (n : nat) (h1 : term27 n) (h2 : (Nat.modulo m n) = (NUMERAL 0)) : term47 m n.
Proof. exact (EQ_MP (@lem199143 m n h1 h2) (@lem196703 m n h2)). Qed.
Lemma lem199145 (m : nat) (n : nat) (h1 : term27 n) : term298 m n.
Proof. exact (fun h0 : (Nat.modulo m n) = (NUMERAL 0) => @lem199144 m n h1 h0). Qed.
Lemma lem199146 (m : nat) (n : nat) (h1 : term27 n) : term299 m n.
Proof. exact (conj (@lem199145 m n h1) (@lem199142 m n h1)). Qed.
Lemma lem199147 (m : nat) (n : nat) : (term299 m n) = (((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n)).
Proof. exact (@lem32 ((Nat.modulo m n) = (NUMERAL 0)) (term47 m n)). Qed.
Lemma lem199149 (m : nat) (n : nat) (h1 : term27 n) : ((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n).
Proof. exact (EQ_MP (@lem199147 m n) (@lem199146 m n h1)). Qed.
Lemma lem199150 (m : nat) (n : nat) : ((Nat.modulo m n) = (NUMERAL 0)) = (term47 m n).
Proof. exact (or_elim (@lem196545 n) (fun h0 : n = (NUMERAL 0) => @lem196640 m n h0) (fun h0 : term27 n => @lem199149 m n h0)). Qed.
Lemma lem199155 (m : nat) : term300 m.
Proof. exact (fun n : nat => @lem199150 m n). Qed.
Lemma lem199160 : term301.
Proof. exact (fun m : nat => @lem199155 m). Qed.
