Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1006570_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1005489 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1005490 (m : nat) (n : nat) (p : nat) : (((Nat.add m n) = p) = ((term1 m n) = (NUMERAL p))) = (term2 m n p).
Proof. exact (@lem1005489 (((Nat.add m n) = p) = ((term1 m n) = (NUMERAL p)))). Qed.
Lemma lem1005491 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (((Nat.add m n) = p) = ((term1 m n) = (NUMERAL p))).
Proof. exact (SYM (@lem1005490 m n p)). Qed.
Lemma lem1005492 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term3 m n p.
Proof. exact (h1). Qed.
Lemma lem1005495 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term4 m n p.
Proof. exact (h1). Qed.
Lemma lem1005496 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (fun h0 : term4 m n p => @lem1005495 m n p h0). Qed.
Lemma lem1005497 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (h1). Qed.
Lemma lem1005498 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term4 m n p.
Proof. exact (h1). Qed.
Lemma lem1005499 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) (h2 : term5 m n p) : term4 m n p.
Proof. exact (@lem1005497 m n p h2 (@lem1005498 m n p h1)). Qed.
Lemma lem1005500 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) : term6 m n p.
Proof. exact (fun h0 : term5 m n p => @lem1005499 m n p h1 h0). Qed.
Lemma lem1005501 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (h1). Qed.
Lemma lem1005502 (m : nat) (n : nat) (p : nat) (h1 : term4 m n p) (h2 : term5 m n p) : term4 m n p.
Proof. exact (@lem1005500 m n p h1 (@lem1005501 m n p h2)). Qed.
Lemma lem1005503 (m : nat) (n : nat) (p : nat) (h1 : term5 m n p) : term5 m n p.
Proof. exact (fun h0 : term4 m n p => @lem1005502 m n p h0 h1). Qed.
Lemma lem1005504 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (fun h0 : term5 m n p => @lem1005503 m n p h0). Qed.
Lemma lem1005507 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1005504 m n p (@lem1005496 m n p)). Qed.
Lemma lem1005523 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1005524 : term8 = term9.
Proof. exact (@lem1005523 term10). Qed.
Lemma lem1005529 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1005530 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term12 m n p).
Proof. exact (MK_COMB (@lem1005529 m n p) (@lem1005524)). Qed.
Lemma lem1005533 (n : nat) (p : nat) : (term13 n p) = (term14 n p).
Proof. exact (fun_ext (fun m : nat => @lem1005530 m n p)). Qed.
Lemma lem1005534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005535 (n : nat) (p : nat) : (term15 n p) = (term16 n p).
Proof. exact (MK_COMB (@lem1005534) (@lem1005533 n p)). Qed.
Lemma lem1005540 (p : nat) : (term17 p) = (term18 p).
Proof. exact (fun_ext (fun n : nat => @lem1005535 n p)). Qed.
Lemma lem1005541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005542 (p : nat) : (term19 p) = (term20 p).
Proof. exact (MK_COMB (@lem1005541) (@lem1005540 p)). Qed.
Lemma lem1005547 : term21 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1005542 p)). Qed.
Lemma lem1005548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005557 : term23 = term24.
Proof. exact (MK_COMB (@lem1005548) (@lem1005547)). Qed.
Lemma lem1005558 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005559 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1005558 n)). Qed.
Lemma lem1005560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005561 : term10 = term10.
Proof. exact (MK_COMB (@lem1005560) (@lem1005559)). Qed.
Lemma lem1005562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1005563 : term9 = term9.
Proof. exact (MK_COMB (@lem1005562) (@lem1005561)). Qed.
Lemma lem1005572 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1005573 (m : nat) (n : nat) (p : nat) : (term12 m n p) = (term12 m n p).
Proof. exact (MK_COMB (@lem1005572 m n p) (@lem1005563)). Qed.
Lemma lem1005574 (n : nat) (p : nat) : (term14 n p) = (term14 n p).
Proof. exact (fun_ext (fun m : nat => @lem1005573 m n p)). Qed.
Lemma lem1005575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005576 (n : nat) (p : nat) : (term16 n p) = (term16 n p).
Proof. exact (MK_COMB (@lem1005575) (@lem1005574 n p)). Qed.
Lemma lem1005577 (p : nat) : (term18 p) = (term18 p).
Proof. exact (fun_ext (fun n : nat => @lem1005576 n p)). Qed.
Lemma lem1005578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005579 (p : nat) : (term20 p) = (term20 p).
Proof. exact (MK_COMB (@lem1005578) (@lem1005577 p)). Qed.
Lemma lem1005580 : term22 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1005579 p)). Qed.
Lemma lem1005581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005582 : term24 = term24.
Proof. exact (MK_COMB (@lem1005581) (@lem1005580)). Qed.
Lemma lem1005611 : term23 = term24.
Proof. exact (TRANS (@lem1005557) (@lem1005582)). Qed.
Lemma lem1005612 : term24 = term23.
Proof. exact (SYM (@lem1005611)). Qed.
Lemma lem1005613 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term3 m n p.
Proof. exact (h1). Qed.
Lemma lem1005614 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1005633 (m : nat) (n : nat) (p : nat) : (term3 m n p) = (term26 m n p).
Proof. exact (@lem17646 ((Nat.add m n) = p) ((term1 m n) = (NUMERAL p))). Qed.
Lemma lem1005635 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005636 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1005635 n)). Qed.
Lemma lem1005637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005646 : term10 = term10.
Proof. exact (MK_COMB (@lem1005637) (@lem1005636)). Qed.
Lemma lem1005647 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1005646) (@lem1005614 h1)). Qed.
Lemma lem1005709 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term26 m n p.
Proof. exact (EQ_MP (@lem1005633 m n p) (@lem1005613 m n p h1)). Qed.
Lemma lem1005716 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005717 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1005716 n)). Qed.
Lemma lem1005718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005719 : term10 = term10.
Proof. exact (MK_COMB (@lem1005718) (@lem1005717)). Qed.
Lemma lem1005720 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1005719) (@lem1005647 h1)). Qed.
Lemma lem1005721 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term27 m n p.
Proof. exact (h1). Qed.
Lemma lem1005722 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term28 m n p.
Proof. exact (h1). Qed.
Lemma lem1005728 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005729 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1005728 n)). Qed.
Lemma lem1005730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005732 : term10 = term10.
Proof. exact (MK_COMB (@lem1005730) (@lem1005729)). Qed.
Lemma lem1005733 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1005732) (@lem1005720 h1)). Qed.
Lemma lem1005743 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1005744 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1005743 n)). Qed.
Lemma lem1005745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1005747 : term10 = term10.
Proof. exact (MK_COMB (@lem1005745) (@lem1005744)). Qed.
Lemma lem1005748 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1005747) (@lem1005720 h1)). Qed.
Lemma lem1005757 (_16302 : nat) (h1 : term10) : term29 _16302.
Proof. exact (@lem1005733 h1 _16302). Qed.
Lemma lem1005758 (_16302 : nat) : (term29 _16302) = ((NUMERAL _16302) = _16302).
Proof. exact (eq_refl (term29 _16302)). Qed.
Lemma lem1005760 (_16303 : nat) (h1 : term10) : term29 _16303.
Proof. exact (@lem1005748 h1 _16303). Qed.
Lemma lem1005761 (_16303 : nat) : (term29 _16303) = ((NUMERAL _16303) = _16303).
Proof. exact (eq_refl (term29 _16303)). Qed.
Lemma lem1005766 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (Nat.add m n) = p.
Proof. exact (proj1 (@lem1005721 m n p h1)). Qed.
Lemma lem1005768 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term30 m n p.
Proof. exact (proj2 (@lem1005721 m n p h1)). Qed.
Lemma lem1005772 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term31 m n p.
Proof. exact (proj1 (@lem1005722 m n p h1)). Qed.
Lemma lem1005775 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : p = (Nat.add m n).
Proof. exact (SYM (@lem1005766 m n p h1)). Qed.
Lemma lem1005804 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1005805 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (term33 m n p) = (term34 m n).
Proof. exact (MK_COMB (@lem1005804 m n) (@lem1005775 m n p h1)). Qed.
Lemma lem1005806 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1005807 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term36 m n p).
Proof. exact (eq_refl (term36 m n p)). Qed.
Lemma lem1005808 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term34 m n)) = ((term33 m n p) = (term35 m n)).
Proof. exact (MK_COMB (@lem1005807 m n p) (@lem1005806 m n)). Qed.
Lemma lem1005809 (m : nat) (n : nat) (p : nat) : (term33 m n p) = (term30 m n p).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem1005810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1005811 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term37 m n p).
Proof. exact (MK_COMB (@lem1005810) (@lem1005809 m n p)). Qed.
Lemma lem1005812 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1005813 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term35 m n)) = ((term30 m n p) = (term35 m n)).
Proof. exact (MK_COMB (@lem1005811 m n p) (@lem1005812 m n)). Qed.
Lemma lem1005814 (p : nat) (m : nat) (n : nat) : ((term33 m n p) = (term34 m n)) = ((term30 m n p) = (term35 m n)).
Proof. exact (TRANS (@lem1005808 p m n) (@lem1005813 p m n)). Qed.
Lemma lem1005815 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : (term30 m n p) = (term35 m n).
Proof. exact (EQ_MP (@lem1005814 p m n) (@lem1005805 m n p h1)). Qed.
Lemma lem1005816 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term35 m n.
Proof. exact (EQ_MP (@lem1005815 m n p h1) (@lem1005768 m n p h1)). Qed.
Lemma lem1005817 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1005818 (_16310 : nat) (_16312 : nat) (h1 : _16310 = _16312) : _16310 = _16312.
Proof. exact (h1). Qed.
Lemma lem1005819 (_16311 : nat) (_16313 : nat) (h1 : _16311 = _16313) : _16311 = _16313.
Proof. exact (h1). Qed.
Lemma lem1005820 (_16310 : nat) (_16312 : nat) (h1 : _16310 = _16312) : (Nat.add _16310) = (Nat.add _16312).
Proof. exact (MK_COMB (@lem1005817) (@lem1005818 _16310 _16312 h1)). Qed.
Lemma lem1005821 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) (h1 : _16310 = _16312) (h2 : _16311 = _16313) : (Nat.add _16310 _16311) = (Nat.add _16312 _16313).
Proof. exact (MK_COMB (@lem1005820 _16310 _16312 h1) (@lem1005819 _16311 _16313 h2)). Qed.
Lemma lem1005822 (_16311 : nat) (_16313 : nat) (_16310 : nat) (_16312 : nat) (h1 : _16310 = _16312) : term38 _16310 _16311 _16312 _16313.
Proof. exact (fun h0 : _16311 = _16313 => @lem1005821 _16310 _16312 _16311 _16313 h1 h0). Qed.
Lemma lem1005824 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1005825 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : (term38 _16310 _16311 _16312 _16313) = (term40 _16310 _16311 _16312 _16313).
Proof. exact (@lem1005824 (_16311 = _16313) ((Nat.add _16310 _16311) = (Nat.add _16312 _16313))). Qed.
Lemma lem1005826 (_16311 : nat) (_16313 : nat) (_16310 : nat) (_16312 : nat) (h1 : _16310 = _16312) : term40 _16310 _16311 _16312 _16313.
Proof. exact (EQ_MP (@lem1005825 _16310 _16311 _16312 _16313) (@lem1005822 _16311 _16313 _16310 _16312 h1)). Qed.
Lemma lem1005827 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : term41 _16310 _16311 _16312 _16313.
Proof. exact (fun h0 : _16310 = _16312 => @lem1005826 _16311 _16313 _16310 _16312 h0). Qed.
Lemma lem1005829 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1005830 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : (term41 _16310 _16311 _16312 _16313) = (term42 _16310 _16311 _16312 _16313).
Proof. exact (@lem1005829 (_16310 = _16312) (term40 _16310 _16311 _16312 _16313)). Qed.
Lemma lem1005831 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : term42 _16310 _16311 _16312 _16313.
Proof. exact (EQ_MP (@lem1005830 _16310 _16311 _16312 _16313) (@lem1005827 _16310 _16311 _16312 _16313)). Qed.
Lemma lem1005832 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1005833 (_16314 : nat) (_16315 : nat) (h1 : _16314 = _16315) : _16314 = _16315.
Proof. exact (h1). Qed.
Lemma lem1005834 (_16314 : nat) (_16315 : nat) (h1 : _16314 = _16315) : (NUMERAL _16314) = (NUMERAL _16315).
Proof. exact (MK_COMB (@lem1005832) (@lem1005833 _16314 _16315 h1)). Qed.
Lemma lem1005835 (_16314 : nat) (_16315 : nat) : term43 _16314 _16315.
Proof. exact (fun h0 : _16314 = _16315 => @lem1005834 _16314 _16315 h0). Qed.
Lemma lem1005837 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1005838 (_16314 : nat) (_16315 : nat) : (term43 _16314 _16315) = (term44 _16314 _16315).
Proof. exact (@lem1005837 (_16314 = _16315) ((NUMERAL _16314) = (NUMERAL _16315))). Qed.
Lemma lem1005839 (_16314 : nat) (_16315 : nat) : term44 _16314 _16315.
Proof. exact (EQ_MP (@lem1005838 _16314 _16315) (@lem1005835 _16314 _16315)). Qed.
Lemma lem1005841 (x : nat) (y : nat) (z : nat) : term45 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1005843 (_16302 : nat) (h1 : term10) : (NUMERAL _16302) = _16302.
Proof. exact (EQ_MP (@lem1005758 _16302) (@lem1005757 _16302 h1)). Qed.
Lemma lem1005844 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term1 m n).
Proof. exact (@lem1005843 (term1 m n) h1). Qed.
Lemma lem1005845 (m : nat) (n : nat) (h1 : term10) : term47 m n.
Proof. exact (fun h0 : term48 m n => @lem1005844 m n h1). Qed.
Lemma lem1005847 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005848 (m : nat) (n : nat) : (term47 m n) = ((term46 m n) = (term1 m n)).
Proof. exact (@lem1005847 ((term46 m n) = (term1 m n))). Qed.
Lemma lem1005849 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem1005848 m n) (@lem1005845 m n h1)). Qed.
Lemma lem1005851 (_16302 : nat) (h1 : term10) : (NUMERAL _16302) = _16302.
Proof. exact (EQ_MP (@lem1005758 _16302) (@lem1005757 _16302 h1)). Qed.
Lemma lem1005852 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (@lem1005851 m h1). Qed.
Lemma lem1005853 (m : nat) (h1 : term10) : term50 m.
Proof. exact (fun h0 : term51 m => @lem1005852 m h1). Qed.
Lemma lem1005855 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005856 (m : nat) : (term50 m) = ((NUMERAL m) = m).
Proof. exact (@lem1005855 ((NUMERAL m) = m)). Qed.
Lemma lem1005857 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1005856 m) (@lem1005853 m h1)). Qed.
Lemma lem1005859 (_16302 : nat) (h1 : term10) : (NUMERAL _16302) = _16302.
Proof. exact (EQ_MP (@lem1005758 _16302) (@lem1005757 _16302 h1)). Qed.
Lemma lem1005860 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (@lem1005859 n h1). Qed.
Lemma lem1005861 (n : nat) (h1 : term10) : term50 n.
Proof. exact (fun h0 : term51 n => @lem1005860 n h1). Qed.
Lemma lem1005863 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005864 (n : nat) : (term50 n) = ((NUMERAL n) = n).
Proof. exact (@lem1005863 ((NUMERAL n) = n)). Qed.
Lemma lem1005865 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1005864 n) (@lem1005861 n h1)). Qed.
Lemma lem1005883 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1005884 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term40 _16310 _16311 _16312 _16313) = (term52 _16310 _16312 _16311 _16313).
Proof. exact (@lem1005883 ((Nat.add _16310 _16311) = (Nat.add _16312 _16313)) (term53 _16311 _16313)). Qed.
Lemma lem1005894 (_16310 : nat) (_16312 : nat) : (term54 _16310 _16312) = (term54 _16310 _16312).
Proof. exact (eq_refl (term54 _16310 _16312)). Qed.
Lemma lem1005895 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term42 _16310 _16311 _16312 _16313) = (term55 _16310 _16312 _16311 _16313).
Proof. exact (MK_COMB (@lem1005894 _16310 _16312) (@lem1005884 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005899 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1005900 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term55 _16310 _16312 _16311 _16313) = (term57 _16310 _16312 _16311 _16313).
Proof. exact (@lem1005899 ((Nat.add _16310 _16311) = (Nat.add _16312 _16313)) (term53 _16310 _16312) (term53 _16311 _16313)). Qed.
Lemma lem1005922 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term42 _16310 _16311 _16312 _16313) = (term57 _16310 _16312 _16311 _16313).
Proof. exact (TRANS (@lem1005895 _16310 _16312 _16311 _16313) (@lem1005900 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1005924 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term58 _16310 _16311 _16312 _16313) = (term59 _16310 _16312 _16311 _16313).
Proof. exact (MK_COMB (@lem1005923) (@lem1005922 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005946 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term57 _16310 _16312 _16311 _16313) = (term57 _16310 _16312 _16311 _16313).
Proof. exact (eq_refl (term57 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005947 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : ((term42 _16310 _16311 _16312 _16313) = (term57 _16310 _16312 _16311 _16313)) = ((term57 _16310 _16312 _16311 _16313) = (term57 _16310 _16312 _16311 _16313)).
Proof. exact (MK_COMB (@lem1005924 _16310 _16312 _16311 _16313) (@lem1005946 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005949 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1005950 (x : Prop) : (x = x) = True.
Proof. exact (@lem1005949 Prop x). Qed.
Lemma lem1005951 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : ((term57 _16310 _16312 _16311 _16313) = (term57 _16310 _16312 _16311 _16313)) = True.
Proof. exact (@lem1005950 (term57 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005952 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : ((term42 _16310 _16311 _16312 _16313) = (term57 _16310 _16312 _16311 _16313)) = True.
Proof. exact (TRANS (@lem1005947 _16310 _16312 _16311 _16313) (@lem1005951 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005953 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : True = ((term42 _16310 _16311 _16312 _16313) = (term57 _16310 _16312 _16311 _16313)).
Proof. exact (SYM (@lem1005952 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005954 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term42 _16310 _16311 _16312 _16313) = (term57 _16310 _16312 _16311 _16313).
Proof. exact (EQ_MP (@lem1005953 _16310 _16312 _16311 _16313) (@lem0)). Qed.
Lemma lem1005955 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : term57 _16310 _16312 _16311 _16313.
Proof. exact (EQ_MP (@lem1005954 _16310 _16312 _16311 _16313) (@lem1005831 _16310 _16311 _16312 _16313)). Qed.
Lemma lem1005957 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1005958 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : (term57 _16310 _16312 _16311 _16313) = (term61 _16310 _16311 _16312 _16313).
Proof. exact (@lem1005957 (term62 _16310 _16312 _16311 _16313) ((Nat.add _16310 _16311) = (Nat.add _16312 _16313))). Qed.
Lemma lem1005960 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1005961 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term65 _16310 _16312 _16311 _16313) = (term66 _16310 _16312 _16311 _16313).
Proof. exact (@lem1005960 (term53 _16310 _16312) (term53 _16311 _16313)). Qed.
Lemma lem1005963 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1005964 (_16310 : nat) (_16312 : nat) : (term68 _16310 _16312) = (_16310 = _16312).
Proof. exact (@lem1005963 (_16310 = _16312)). Qed.
Lemma lem1005965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1005966 (_16310 : nat) (_16312 : nat) : (term69 _16310 _16312) = (term70 _16310 _16312).
Proof. exact (MK_COMB (@lem1005965) (@lem1005964 _16310 _16312)). Qed.
Lemma lem1005968 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1005969 (_16311 : nat) (_16313 : nat) : (term68 _16311 _16313) = (_16311 = _16313).
Proof. exact (@lem1005968 (_16311 = _16313)). Qed.
Lemma lem1005970 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term66 _16310 _16312 _16311 _16313) = (term71 _16310 _16312 _16311 _16313).
Proof. exact (MK_COMB (@lem1005966 _16310 _16312) (@lem1005969 _16311 _16313)). Qed.
Lemma lem1005971 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term65 _16310 _16312 _16311 _16313) = (term71 _16310 _16312 _16311 _16313).
Proof. exact (TRANS (@lem1005961 _16310 _16312 _16311 _16313) (@lem1005970 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1005973 (_16310 : nat) (_16312 : nat) (_16311 : nat) (_16313 : nat) : (term72 _16310 _16312 _16311 _16313) = (term73 _16310 _16312 _16311 _16313).
Proof. exact (MK_COMB (@lem1005972) (@lem1005971 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005974 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : ((Nat.add _16310 _16311) = (Nat.add _16312 _16313)) = ((Nat.add _16310 _16311) = (Nat.add _16312 _16313)).
Proof. exact (eq_refl ((Nat.add _16310 _16311) = (Nat.add _16312 _16313))). Qed.
Lemma lem1005975 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : (term61 _16310 _16311 _16312 _16313) = (term74 _16310 _16311 _16312 _16313).
Proof. exact (MK_COMB (@lem1005973 _16310 _16312 _16311 _16313) (@lem1005974 _16310 _16311 _16312 _16313)). Qed.
Lemma lem1005976 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : (term57 _16310 _16312 _16311 _16313) = (term74 _16310 _16311 _16312 _16313).
Proof. exact (TRANS (@lem1005958 _16310 _16311 _16312 _16313) (@lem1005975 _16310 _16311 _16312 _16313)). Qed.
Lemma lem1005978 (m : nat) (n : nat) (h1 : term10) : term75 m n.
Proof. exact (conj (@lem1005857 m h1) (@lem1005865 n h1)). Qed.
Lemma lem1005980 (_16310 : nat) (_16311 : nat) (_16312 : nat) (_16313 : nat) : term74 _16310 _16311 _16312 _16313.
Proof. exact (EQ_MP (@lem1005976 _16310 _16311 _16312 _16313) (@lem1005955 _16310 _16312 _16311 _16313)). Qed.
Lemma lem1005981 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1005980 (NUMERAL m) (NUMERAL n) m n). Qed.
Lemma lem1005984 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.add m n).
Proof. exact (@lem1005981 m n (@lem1005978 m n h1)). Qed.
Lemma lem1005985 (m : nat) (n : nat) (h1 : term10) : term77 m n.
Proof. exact (fun h0 : term78 m n => @lem1005984 m n h1). Qed.
Lemma lem1005987 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1005988 (m : nat) (n : nat) : (term77 m n) = ((term1 m n) = (Nat.add m n)).
Proof. exact (@lem1005987 ((term1 m n) = (Nat.add m n))). Qed.
Lemma lem1005989 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.add m n).
Proof. exact (EQ_MP (@lem1005988 m n) (@lem1005985 m n h1)). Qed.
Lemma lem1005995 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1005996 (_16314 : nat) (_16315 : nat) : (term44 _16314 _16315) = (term79 _16314 _16315).
Proof. exact (@lem1005995 ((NUMERAL _16314) = (NUMERAL _16315)) (term53 _16314 _16315)). Qed.
Lemma lem1006006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1006007 (_16314 : nat) (_16315 : nat) : (term80 _16314 _16315) = (term81 _16314 _16315).
Proof. exact (MK_COMB (@lem1006006) (@lem1005996 _16314 _16315)). Qed.
Lemma lem1006017 (_16314 : nat) (_16315 : nat) : (term79 _16314 _16315) = (term79 _16314 _16315).
Proof. exact (eq_refl (term79 _16314 _16315)). Qed.
Lemma lem1006018 (_16314 : nat) (_16315 : nat) : ((term44 _16314 _16315) = (term79 _16314 _16315)) = ((term79 _16314 _16315) = (term79 _16314 _16315)).
Proof. exact (MK_COMB (@lem1006007 _16314 _16315) (@lem1006017 _16314 _16315)). Qed.
Lemma lem1006020 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1006021 (x : Prop) : (x = x) = True.
Proof. exact (@lem1006020 Prop x). Qed.
Lemma lem1006022 (_16314 : nat) (_16315 : nat) : ((term79 _16314 _16315) = (term79 _16314 _16315)) = True.
Proof. exact (@lem1006021 (term79 _16314 _16315)). Qed.
Lemma lem1006023 (_16314 : nat) (_16315 : nat) : ((term44 _16314 _16315) = (term79 _16314 _16315)) = True.
Proof. exact (TRANS (@lem1006018 _16314 _16315) (@lem1006022 _16314 _16315)). Qed.
Lemma lem1006024 (_16314 : nat) (_16315 : nat) : True = ((term44 _16314 _16315) = (term79 _16314 _16315)).
Proof. exact (SYM (@lem1006023 _16314 _16315)). Qed.
Lemma lem1006025 (_16314 : nat) (_16315 : nat) : (term44 _16314 _16315) = (term79 _16314 _16315).
Proof. exact (EQ_MP (@lem1006024 _16314 _16315) (@lem0)). Qed.
Lemma lem1006026 (_16314 : nat) (_16315 : nat) : term79 _16314 _16315.
Proof. exact (EQ_MP (@lem1006025 _16314 _16315) (@lem1005839 _16314 _16315)). Qed.
Lemma lem1006028 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1006029 (_16314 : nat) (_16315 : nat) : (term79 _16314 _16315) = (term82 _16314 _16315).
Proof. exact (@lem1006028 (term53 _16314 _16315) ((NUMERAL _16314) = (NUMERAL _16315))). Qed.
Lemma lem1006031 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006032 (_16314 : nat) (_16315 : nat) : (term68 _16314 _16315) = (_16314 = _16315).
Proof. exact (@lem1006031 (_16314 = _16315)). Qed.
Lemma lem1006033 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1006034 (_16314 : nat) (_16315 : nat) : (term83 _16314 _16315) = (term84 _16314 _16315).
Proof. exact (MK_COMB (@lem1006033) (@lem1006032 _16314 _16315)). Qed.
Lemma lem1006035 (_16314 : nat) (_16315 : nat) : ((NUMERAL _16314) = (NUMERAL _16315)) = ((NUMERAL _16314) = (NUMERAL _16315)).
Proof. exact (eq_refl ((NUMERAL _16314) = (NUMERAL _16315))). Qed.
Lemma lem1006036 (_16314 : nat) (_16315 : nat) : (term82 _16314 _16315) = (term43 _16314 _16315).
Proof. exact (MK_COMB (@lem1006034 _16314 _16315) (@lem1006035 _16314 _16315)). Qed.
Lemma lem1006037 (_16314 : nat) (_16315 : nat) : (term79 _16314 _16315) = (term43 _16314 _16315).
Proof. exact (TRANS (@lem1006029 _16314 _16315) (@lem1006036 _16314 _16315)). Qed.
Lemma lem1006040 (_16314 : nat) (_16315 : nat) : term43 _16314 _16315.
Proof. exact (EQ_MP (@lem1006037 _16314 _16315) (@lem1006026 _16314 _16315)). Qed.
Lemma lem1006041 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem1006040 (term1 m n) (Nat.add m n)). Qed.
Lemma lem1006044 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term86 m n).
Proof. exact (@lem1006041 m n (@lem1005989 m n h1)). Qed.
Lemma lem1006045 (m : nat) (n : nat) (h1 : term10) : term87 m n.
Proof. exact (fun h0 : term88 m n => @lem1006044 m n h1). Qed.
Lemma lem1006047 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006048 (m : nat) (n : nat) : (term87 m n) = ((term46 m n) = (term86 m n)).
Proof. exact (@lem1006047 ((term46 m n) = (term86 m n))). Qed.
Lemma lem1006049 (m : nat) (n : nat) (h1 : term10) : (term46 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1006048 m n) (@lem1006045 m n h1)). Qed.
Lemma lem1006067 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1006068 (y : nat) (x : nat) (z : nat) : (term89 x y z) = (term90 y x z).
Proof. exact (@lem1006067 (y = z) (term53 x z)). Qed.
Lemma lem1006078 (x : nat) (y : nat) : (term54 x y) = (term54 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1006079 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term91 y x z).
Proof. exact (MK_COMB (@lem1006078 x y) (@lem1006068 y x z)). Qed.
Lemma lem1006083 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1006084 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term92 y x z).
Proof. exact (@lem1006083 (y = z) (term53 x y) (term53 x z)). Qed.
Lemma lem1006106 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem1006079 y x z) (@lem1006084 y x z)). Qed.
Lemma lem1006107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1006108 (y : nat) (x : nat) (z : nat) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem1006107) (@lem1006106 y x z)). Qed.
Lemma lem1006130 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem1006131 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem1006108 y x z) (@lem1006130 y x z)). Qed.
Lemma lem1006133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1006134 (x : Prop) : (x = x) = True.
Proof. exact (@lem1006133 Prop x). Qed.
Lemma lem1006135 (y : nat) (x : nat) (z : nat) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem1006134 (term92 y x z)). Qed.
Lemma lem1006136 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem1006131 y x z) (@lem1006135 y x z)). Qed.
Lemma lem1006137 (y : nat) (x : nat) (z : nat) : True = ((term45 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem1006136 y x z)). Qed.
Lemma lem1006138 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem1006137 y x z) (@lem0)). Qed.
Lemma lem1006139 (y : nat) (x : nat) (z : nat) : term92 y x z.
Proof. exact (EQ_MP (@lem1006138 y x z) (@lem1005841 x y z)). Qed.
Lemma lem1006141 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1006142 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term95 x y z).
Proof. exact (@lem1006141 (term96 y x z) (y = z)). Qed.
Lemma lem1006144 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1006145 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (@lem1006144 (term53 x y) (term53 x z)). Qed.
Lemma lem1006147 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006148 (x : nat) (y : nat) : (term68 x y) = (x = y).
Proof. exact (@lem1006147 (x = y)). Qed.
Lemma lem1006149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1006150 (x : nat) (y : nat) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1006149) (@lem1006148 x y)). Qed.
Lemma lem1006152 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006153 (x : nat) (z : nat) : (term68 x z) = (x = z).
Proof. exact (@lem1006152 (x = z)). Qed.
Lemma lem1006154 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1006150 x y) (@lem1006153 x z)). Qed.
Lemma lem1006155 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem1006145 y x z) (@lem1006154 y x z)). Qed.
Lemma lem1006156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1006157 (y : nat) (x : nat) (z : nat) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1006156) (@lem1006155 y x z)). Qed.
Lemma lem1006158 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1006159 (x : nat) (y : nat) (z : nat) : (term95 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1006157 y x z) (@lem1006158 y z)). Qed.
Lemma lem1006160 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term102 x y z).
Proof. exact (TRANS (@lem1006142 x y z) (@lem1006159 x y z)). Qed.
Lemma lem1006162 (m : nat) (n : nat) (h1 : term10) : term103 m n.
Proof. exact (conj (@lem1005849 m n h1) (@lem1006049 m n h1)). Qed.
Lemma lem1006164 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1006160 x y z) (@lem1006139 y x z)). Qed.
Lemma lem1006165 (m : nat) (n : nat) : term104 m n.
Proof. exact (@lem1006164 (term46 m n) (term1 m n) (term86 m n)). Qed.
Lemma lem1006168 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (term86 m n).
Proof. exact (@lem1006165 m n (@lem1006162 m n h1)). Qed.
Lemma lem1006169 (m : nat) (n : nat) (h1 : term10) : term105 m n.
Proof. exact (fun h0 : term35 m n => @lem1006168 m n h1). Qed.
Lemma lem1006171 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006172 (m : nat) (n : nat) : (term105 m n) = ((term1 m n) = (term86 m n)).
Proof. exact (@lem1006171 ((term1 m n) = (term86 m n))). Qed.
Lemma lem1006173 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (term86 m n).
Proof. exact (EQ_MP (@lem1006172 m n) (@lem1006169 m n h1)). Qed.
Lemma lem1006176 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1006178 (m : nat) (n : nat) : (term35 m n) = (term106 m n).
Proof. exact (@lem1006176 ((term1 m n) = (term86 m n))). Qed.
Lemma lem1006181 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term106 m n.
Proof. exact (EQ_MP (@lem1006178 m n) (@lem1005816 m n p h1)). Qed.
Lemma lem1006184 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (@lem1006181 m n p h2 (@lem1006173 m n h1)). Qed.
Lemma lem1006185 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : term107.
Proof. exact (fun h0 : ~ False => @lem1006184 m n p h1 h2). Qed.
Lemma lem1006187 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006188 : term107 = False.
Proof. exact (@lem1006187 False). Qed.
Lemma lem1006190 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1006191 (_16316 : nat) (_16318 : nat) (h1 : _16316 = _16318) : _16316 = _16318.
Proof. exact (h1). Qed.
Lemma lem1006192 (_16317 : nat) (_16319 : nat) (h1 : _16317 = _16319) : _16317 = _16319.
Proof. exact (h1). Qed.
Lemma lem1006193 (_16316 : nat) (_16318 : nat) (h1 : _16316 = _16318) : (Nat.add _16316) = (Nat.add _16318).
Proof. exact (MK_COMB (@lem1006190) (@lem1006191 _16316 _16318 h1)). Qed.
Lemma lem1006194 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) (h1 : _16316 = _16318) (h2 : _16317 = _16319) : (Nat.add _16316 _16317) = (Nat.add _16318 _16319).
Proof. exact (MK_COMB (@lem1006193 _16316 _16318 h1) (@lem1006192 _16317 _16319 h2)). Qed.
Lemma lem1006195 (_16317 : nat) (_16319 : nat) (_16316 : nat) (_16318 : nat) (h1 : _16316 = _16318) : term38 _16316 _16317 _16318 _16319.
Proof. exact (fun h0 : _16317 = _16319 => @lem1006194 _16316 _16318 _16317 _16319 h1 h0). Qed.
Lemma lem1006197 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1006198 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : (term38 _16316 _16317 _16318 _16319) = (term40 _16316 _16317 _16318 _16319).
Proof. exact (@lem1006197 (_16317 = _16319) ((Nat.add _16316 _16317) = (Nat.add _16318 _16319))). Qed.
Lemma lem1006199 (_16317 : nat) (_16319 : nat) (_16316 : nat) (_16318 : nat) (h1 : _16316 = _16318) : term40 _16316 _16317 _16318 _16319.
Proof. exact (EQ_MP (@lem1006198 _16316 _16317 _16318 _16319) (@lem1006195 _16317 _16319 _16316 _16318 h1)). Qed.
Lemma lem1006200 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : term41 _16316 _16317 _16318 _16319.
Proof. exact (fun h0 : _16316 = _16318 => @lem1006199 _16317 _16319 _16316 _16318 h0). Qed.
Lemma lem1006202 (a : Prop) (b : Prop) : (a -> b) = (term39 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1006203 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : (term41 _16316 _16317 _16318 _16319) = (term42 _16316 _16317 _16318 _16319).
Proof. exact (@lem1006202 (_16316 = _16318) (term40 _16316 _16317 _16318 _16319)). Qed.
Lemma lem1006204 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : term42 _16316 _16317 _16318 _16319.
Proof. exact (EQ_MP (@lem1006203 _16316 _16317 _16318 _16319) (@lem1006200 _16316 _16317 _16318 _16319)). Qed.
Lemma lem1006214 (x : nat) (y : nat) (z : nat) : term45 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1006216 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : (term1 m n) = (NUMERAL p).
Proof. exact (proj2 (@lem1005722 m n p h1)). Qed.
Lemma lem1006217 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term108 m n p.
Proof. exact (fun h0 : term30 m n p => @lem1006216 m n p h1). Qed.
Lemma lem1006219 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006220 (m : nat) (n : nat) (p : nat) : (term108 m n p) = ((term1 m n) = (NUMERAL p)).
Proof. exact (@lem1006219 ((term1 m n) = (NUMERAL p))). Qed.
Lemma lem1006221 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : (term1 m n) = (NUMERAL p).
Proof. exact (EQ_MP (@lem1006220 m n p) (@lem1006217 m n p h1)). Qed.
Lemma lem1006223 (_16303 : nat) (h1 : term10) : (NUMERAL _16303) = _16303.
Proof. exact (EQ_MP (@lem1005761 _16303) (@lem1005760 _16303 h1)). Qed.
Lemma lem1006224 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (@lem1006223 m h1). Qed.
Lemma lem1006225 (m : nat) (h1 : term10) : term50 m.
Proof. exact (fun h0 : term51 m => @lem1006224 m h1). Qed.
Lemma lem1006227 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006228 (m : nat) : (term50 m) = ((NUMERAL m) = m).
Proof. exact (@lem1006227 ((NUMERAL m) = m)). Qed.
Lemma lem1006229 (m : nat) (h1 : term10) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1006228 m) (@lem1006225 m h1)). Qed.
Lemma lem1006231 (_16303 : nat) (h1 : term10) : (NUMERAL _16303) = _16303.
Proof. exact (EQ_MP (@lem1005761 _16303) (@lem1005760 _16303 h1)). Qed.
Lemma lem1006232 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (@lem1006231 n h1). Qed.
Lemma lem1006233 (n : nat) (h1 : term10) : term50 n.
Proof. exact (fun h0 : term51 n => @lem1006232 n h1). Qed.
Lemma lem1006235 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006236 (n : nat) : (term50 n) = ((NUMERAL n) = n).
Proof. exact (@lem1006235 ((NUMERAL n) = n)). Qed.
Lemma lem1006237 (n : nat) (h1 : term10) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1006236 n) (@lem1006233 n h1)). Qed.
Lemma lem1006255 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1006256 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term40 _16316 _16317 _16318 _16319) = (term52 _16316 _16318 _16317 _16319).
Proof. exact (@lem1006255 ((Nat.add _16316 _16317) = (Nat.add _16318 _16319)) (term53 _16317 _16319)). Qed.
Lemma lem1006266 (_16316 : nat) (_16318 : nat) : (term54 _16316 _16318) = (term54 _16316 _16318).
Proof. exact (eq_refl (term54 _16316 _16318)). Qed.
Lemma lem1006267 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term42 _16316 _16317 _16318 _16319) = (term55 _16316 _16318 _16317 _16319).
Proof. exact (MK_COMB (@lem1006266 _16316 _16318) (@lem1006256 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006271 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1006272 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term55 _16316 _16318 _16317 _16319) = (term57 _16316 _16318 _16317 _16319).
Proof. exact (@lem1006271 ((Nat.add _16316 _16317) = (Nat.add _16318 _16319)) (term53 _16316 _16318) (term53 _16317 _16319)). Qed.
Lemma lem1006294 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term42 _16316 _16317 _16318 _16319) = (term57 _16316 _16318 _16317 _16319).
Proof. exact (TRANS (@lem1006267 _16316 _16318 _16317 _16319) (@lem1006272 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1006296 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term58 _16316 _16317 _16318 _16319) = (term59 _16316 _16318 _16317 _16319).
Proof. exact (MK_COMB (@lem1006295) (@lem1006294 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006318 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term57 _16316 _16318 _16317 _16319) = (term57 _16316 _16318 _16317 _16319).
Proof. exact (eq_refl (term57 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006319 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : ((term42 _16316 _16317 _16318 _16319) = (term57 _16316 _16318 _16317 _16319)) = ((term57 _16316 _16318 _16317 _16319) = (term57 _16316 _16318 _16317 _16319)).
Proof. exact (MK_COMB (@lem1006296 _16316 _16318 _16317 _16319) (@lem1006318 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006321 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1006322 (x : Prop) : (x = x) = True.
Proof. exact (@lem1006321 Prop x). Qed.
Lemma lem1006323 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : ((term57 _16316 _16318 _16317 _16319) = (term57 _16316 _16318 _16317 _16319)) = True.
Proof. exact (@lem1006322 (term57 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006324 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : ((term42 _16316 _16317 _16318 _16319) = (term57 _16316 _16318 _16317 _16319)) = True.
Proof. exact (TRANS (@lem1006319 _16316 _16318 _16317 _16319) (@lem1006323 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006325 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : True = ((term42 _16316 _16317 _16318 _16319) = (term57 _16316 _16318 _16317 _16319)).
Proof. exact (SYM (@lem1006324 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006326 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term42 _16316 _16317 _16318 _16319) = (term57 _16316 _16318 _16317 _16319).
Proof. exact (EQ_MP (@lem1006325 _16316 _16318 _16317 _16319) (@lem0)). Qed.
Lemma lem1006327 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : term57 _16316 _16318 _16317 _16319.
Proof. exact (EQ_MP (@lem1006326 _16316 _16318 _16317 _16319) (@lem1006204 _16316 _16317 _16318 _16319)). Qed.
Lemma lem1006329 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1006330 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : (term57 _16316 _16318 _16317 _16319) = (term61 _16316 _16317 _16318 _16319).
Proof. exact (@lem1006329 (term62 _16316 _16318 _16317 _16319) ((Nat.add _16316 _16317) = (Nat.add _16318 _16319))). Qed.
Lemma lem1006332 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1006333 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term65 _16316 _16318 _16317 _16319) = (term66 _16316 _16318 _16317 _16319).
Proof. exact (@lem1006332 (term53 _16316 _16318) (term53 _16317 _16319)). Qed.
Lemma lem1006335 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006336 (_16316 : nat) (_16318 : nat) : (term68 _16316 _16318) = (_16316 = _16318).
Proof. exact (@lem1006335 (_16316 = _16318)). Qed.
Lemma lem1006337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1006338 (_16316 : nat) (_16318 : nat) : (term69 _16316 _16318) = (term70 _16316 _16318).
Proof. exact (MK_COMB (@lem1006337) (@lem1006336 _16316 _16318)). Qed.
Lemma lem1006340 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006341 (_16317 : nat) (_16319 : nat) : (term68 _16317 _16319) = (_16317 = _16319).
Proof. exact (@lem1006340 (_16317 = _16319)). Qed.
Lemma lem1006342 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term66 _16316 _16318 _16317 _16319) = (term71 _16316 _16318 _16317 _16319).
Proof. exact (MK_COMB (@lem1006338 _16316 _16318) (@lem1006341 _16317 _16319)). Qed.
Lemma lem1006343 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term65 _16316 _16318 _16317 _16319) = (term71 _16316 _16318 _16317 _16319).
Proof. exact (TRANS (@lem1006333 _16316 _16318 _16317 _16319) (@lem1006342 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1006345 (_16316 : nat) (_16318 : nat) (_16317 : nat) (_16319 : nat) : (term72 _16316 _16318 _16317 _16319) = (term73 _16316 _16318 _16317 _16319).
Proof. exact (MK_COMB (@lem1006344) (@lem1006343 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006346 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : ((Nat.add _16316 _16317) = (Nat.add _16318 _16319)) = ((Nat.add _16316 _16317) = (Nat.add _16318 _16319)).
Proof. exact (eq_refl ((Nat.add _16316 _16317) = (Nat.add _16318 _16319))). Qed.
Lemma lem1006347 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : (term61 _16316 _16317 _16318 _16319) = (term74 _16316 _16317 _16318 _16319).
Proof. exact (MK_COMB (@lem1006345 _16316 _16318 _16317 _16319) (@lem1006346 _16316 _16317 _16318 _16319)). Qed.
Lemma lem1006348 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : (term57 _16316 _16318 _16317 _16319) = (term74 _16316 _16317 _16318 _16319).
Proof. exact (TRANS (@lem1006330 _16316 _16317 _16318 _16319) (@lem1006347 _16316 _16317 _16318 _16319)). Qed.
Lemma lem1006350 (m : nat) (n : nat) (h1 : term10) : term75 m n.
Proof. exact (conj (@lem1006229 m h1) (@lem1006237 n h1)). Qed.
Lemma lem1006352 (_16316 : nat) (_16317 : nat) (_16318 : nat) (_16319 : nat) : term74 _16316 _16317 _16318 _16319.
Proof. exact (EQ_MP (@lem1006348 _16316 _16317 _16318 _16319) (@lem1006327 _16316 _16318 _16317 _16319)). Qed.
Lemma lem1006353 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1006352 (NUMERAL m) (NUMERAL n) m n). Qed.
Lemma lem1006356 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.add m n).
Proof. exact (@lem1006353 m n (@lem1006350 m n h1)). Qed.
Lemma lem1006357 (m : nat) (n : nat) (h1 : term10) : term77 m n.
Proof. exact (fun h0 : term78 m n => @lem1006356 m n h1). Qed.
Lemma lem1006359 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006360 (m : nat) (n : nat) : (term77 m n) = ((term1 m n) = (Nat.add m n)).
Proof. exact (@lem1006359 ((term1 m n) = (Nat.add m n))). Qed.
Lemma lem1006361 (m : nat) (n : nat) (h1 : term10) : (term1 m n) = (Nat.add m n).
Proof. exact (EQ_MP (@lem1006360 m n) (@lem1006357 m n h1)). Qed.
Lemma lem1006379 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1006380 (y : nat) (x : nat) (z : nat) : (term89 x y z) = (term90 y x z).
Proof. exact (@lem1006379 (y = z) (term53 x z)). Qed.
Lemma lem1006390 (x : nat) (y : nat) : (term54 x y) = (term54 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1006391 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term91 y x z).
Proof. exact (MK_COMB (@lem1006390 x y) (@lem1006380 y x z)). Qed.
Lemma lem1006395 (q : Prop) (p : Prop) (r : Prop) : (term56 p q r) = (term56 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1006396 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term92 y x z).
Proof. exact (@lem1006395 (y = z) (term53 x y) (term53 x z)). Qed.
Lemma lem1006418 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (TRANS (@lem1006391 y x z) (@lem1006396 y x z)). Qed.
Lemma lem1006419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1006420 (y : nat) (x : nat) (z : nat) : (term93 x y z) = (term94 y x z).
Proof. exact (MK_COMB (@lem1006419) (@lem1006418 y x z)). Qed.
Lemma lem1006442 (y : nat) (x : nat) (z : nat) : (term92 y x z) = (term92 y x z).
Proof. exact (eq_refl (term92 y x z)). Qed.
Lemma lem1006443 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = ((term92 y x z) = (term92 y x z)).
Proof. exact (MK_COMB (@lem1006420 y x z) (@lem1006442 y x z)). Qed.
Lemma lem1006445 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1006446 (x : Prop) : (x = x) = True.
Proof. exact (@lem1006445 Prop x). Qed.
Lemma lem1006447 (y : nat) (x : nat) (z : nat) : ((term92 y x z) = (term92 y x z)) = True.
Proof. exact (@lem1006446 (term92 y x z)). Qed.
Lemma lem1006448 (y : nat) (x : nat) (z : nat) : ((term45 x y z) = (term92 y x z)) = True.
Proof. exact (TRANS (@lem1006443 y x z) (@lem1006447 y x z)). Qed.
Lemma lem1006449 (y : nat) (x : nat) (z : nat) : True = ((term45 x y z) = (term92 y x z)).
Proof. exact (SYM (@lem1006448 y x z)). Qed.
Lemma lem1006450 (y : nat) (x : nat) (z : nat) : (term45 x y z) = (term92 y x z).
Proof. exact (EQ_MP (@lem1006449 y x z) (@lem0)). Qed.
Lemma lem1006451 (y : nat) (x : nat) (z : nat) : term92 y x z.
Proof. exact (EQ_MP (@lem1006450 y x z) (@lem1006214 x y z)). Qed.
Lemma lem1006453 (b : Prop) (a : Prop) : (a \/ b) = (term60 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1006454 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term95 x y z).
Proof. exact (@lem1006453 (term96 y x z) (y = z)). Qed.
Lemma lem1006456 (a : Prop) (b : Prop) : (term63 a b) = (term64 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1006457 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (@lem1006456 (term53 x y) (term53 x z)). Qed.
Lemma lem1006459 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006460 (x : nat) (y : nat) : (term68 x y) = (x = y).
Proof. exact (@lem1006459 (x = y)). Qed.
Lemma lem1006461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1006462 (x : nat) (y : nat) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1006461) (@lem1006460 x y)). Qed.
Lemma lem1006464 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1006465 (x : nat) (z : nat) : (term68 x z) = (x = z).
Proof. exact (@lem1006464 (x = z)). Qed.
Lemma lem1006466 (y : nat) (x : nat) (z : nat) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1006462 x y) (@lem1006465 x z)). Qed.
Lemma lem1006467 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem1006457 y x z) (@lem1006466 y x z)). Qed.
Lemma lem1006468 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1006469 (y : nat) (x : nat) (z : nat) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1006468) (@lem1006467 y x z)). Qed.
Lemma lem1006470 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1006471 (x : nat) (y : nat) (z : nat) : (term95 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1006469 y x z) (@lem1006470 y z)). Qed.
Lemma lem1006472 (x : nat) (y : nat) (z : nat) : (term92 y x z) = (term102 x y z).
Proof. exact (TRANS (@lem1006454 x y z) (@lem1006471 x y z)). Qed.
Lemma lem1006474 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term109 p m n.
Proof. exact (conj (@lem1006221 m n p h2) (@lem1006361 m n h1)). Qed.
Lemma lem1006476 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1006472 x y z) (@lem1006451 y x z)). Qed.
Lemma lem1006477 (p : nat) (m : nat) (n : nat) : term110 p m n.
Proof. exact (@lem1006476 (term1 m n) (NUMERAL p) (Nat.add m n)). Qed.
Lemma lem1006480 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (NUMERAL p) = (Nat.add m n).
Proof. exact (@lem1006477 p m n (@lem1006474 m n p h1 h2)). Qed.
Lemma lem1006481 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term111 p m n.
Proof. exact (fun h0 : term112 p m n => @lem1006480 m n p h1 h2). Qed.
Lemma lem1006483 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006484 (p : nat) (m : nat) (n : nat) : (term111 p m n) = ((NUMERAL p) = (Nat.add m n)).
Proof. exact (@lem1006483 ((NUMERAL p) = (Nat.add m n))). Qed.
Lemma lem1006485 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (NUMERAL p) = (Nat.add m n).
Proof. exact (EQ_MP (@lem1006484 p m n) (@lem1006481 m n p h1 h2)). Qed.
Lemma lem1006487 (_16303 : nat) (h1 : term10) : (NUMERAL _16303) = _16303.
Proof. exact (EQ_MP (@lem1005761 _16303) (@lem1005760 _16303 h1)). Qed.
Lemma lem1006488 (p : nat) (h1 : term10) : (NUMERAL p) = p.
Proof. exact (@lem1006487 p h1). Qed.
Lemma lem1006489 (p : nat) (h1 : term10) : term50 p.
Proof. exact (fun h0 : term51 p => @lem1006488 p h1). Qed.
Lemma lem1006491 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006492 (p : nat) : (term50 p) = ((NUMERAL p) = p).
Proof. exact (@lem1006491 ((NUMERAL p) = p)). Qed.
Lemma lem1006493 (p : nat) (h1 : term10) : (NUMERAL p) = p.
Proof. exact (EQ_MP (@lem1006492 p) (@lem1006489 p h1)). Qed.
Lemma lem1006494 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term113 m n p.
Proof. exact (conj (@lem1006485 m n p h1 h2) (@lem1006493 p h1)). Qed.
Lemma lem1006496 (x : nat) (y : nat) (z : nat) : term102 x y z.
Proof. exact (EQ_MP (@lem1006472 x y z) (@lem1006451 y x z)). Qed.
Lemma lem1006497 (m : nat) (n : nat) (p : nat) : term114 m n p.
Proof. exact (@lem1006496 (NUMERAL p) (Nat.add m n) p). Qed.
Lemma lem1006500 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (Nat.add m n) = p.
Proof. exact (@lem1006497 m n p (@lem1006494 m n p h1 h2)). Qed.
Lemma lem1006501 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term115 m n p.
Proof. exact (fun h0 : term31 m n p => @lem1006500 m n p h1 h2). Qed.
Lemma lem1006503 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006504 (m : nat) (n : nat) (p : nat) : (term115 m n p) = ((Nat.add m n) = p).
Proof. exact (@lem1006503 ((Nat.add m n) = p)). Qed.
Lemma lem1006505 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : (Nat.add m n) = p.
Proof. exact (EQ_MP (@lem1006504 m n p) (@lem1006501 m n p h1 h2)). Qed.
Lemma lem1006508 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1006510 (m : nat) (n : nat) (p : nat) : (term31 m n p) = (term116 m n p).
Proof. exact (@lem1006508 ((Nat.add m n) = p)). Qed.
Lemma lem1006513 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term116 m n p.
Proof. exact (EQ_MP (@lem1006510 m n p) (@lem1005772 m n p h1)). Qed.
Lemma lem1006516 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (@lem1006513 m n p h2 (@lem1006505 m n p h1 h2)). Qed.
Lemma lem1006517 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term107.
Proof. exact (fun h0 : ~ False => @lem1006516 m n p h1 h2). Qed.
Lemma lem1006519 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1006520 : term107 = False.
Proof. exact (@lem1006519 False). Qed.
Lemma lem1006521 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (EQ_MP (@lem1006520) (@lem1006517 m n p h1 h2)). Qed.
Lemma lem1006522 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (EQ_MP (@lem1006188) (@lem1006185 m n p h1 h2)). Qed.
Lemma lem1006523 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1006521 m n p h1 h2) (fun h3 : False => @lem1005748 h1)). Qed.
Lemma lem1006524 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term28 m n p) : False.
Proof. exact (EQ_MP (@lem1006523 m n p h1 h2) (@lem1005748 h1)). Qed.
Lemma lem1006525 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1006522 m n p h1 h2) (fun h3 : False => @lem1005733 h1)). Qed.
Lemma lem1006526 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term27 m n p) : False.
Proof. exact (EQ_MP (@lem1006525 m n p h1 h2) (@lem1005733 h1)). Qed.
Lemma lem1006527 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (or_elim (@lem1005709 m n p h2) (fun h0 : term27 m n p => @lem1006526 m n p h1 h0) (fun h0 : term28 m n p => @lem1006524 m n p h1 h0)). Qed.
Lemma lem1006528 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1006527 m n p h1 h2) (fun h3 : False => @lem1005720 h1)). Qed.
Lemma lem1006529 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1006528 m n p h1 h2) (@lem1005720 h1)). Qed.
Lemma lem1006530 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1006529 m n p h1 h2) (fun h3 : False => @lem1005647 h1)). Qed.
Lemma lem1006531 (m : nat) (n : nat) (p : nat) (h1 : term10) (h2 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1006530 m n p h1 h2) (@lem1005647 h1)). Qed.
Lemma lem1006532 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term8.
Proof. exact (fun h0 : term10 => @lem1006531 m n p h0 h1). Qed.
Lemma lem1006533 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1006534 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term9.
Proof. exact (EQ_MP (@lem1006533) (@lem1006532 m n p h1)). Qed.
Lemma lem1006535 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (fun h0 : term3 m n p => @lem1006534 m n p h0). Qed.
Lemma lem1006540 (n : nat) (p : nat) : term16 n p.
Proof. exact (fun m : nat => @lem1006535 m n p). Qed.
Lemma lem1006545 (p : nat) : term20 p.
Proof. exact (fun n : nat => @lem1006540 n p). Qed.
Lemma lem1006550 : term24.
Proof. exact (fun p : nat => @lem1006545 p). Qed.
Lemma lem1006551 : term23.
Proof. exact (EQ_MP (@lem1005612) (@lem1006550)). Qed.
Lemma lem1006552 (p : nat) : term117 p.
Proof. exact (@lem1006551 p). Qed.
Lemma lem1006553 (p : nat) : (term117 p) = (term19 p).
Proof. exact (eq_refl (term117 p)). Qed.
Lemma lem1006554 (p : nat) : term19 p.
Proof. exact (EQ_MP (@lem1006553 p) (@lem1006552 p)). Qed.
Lemma lem1006555 (p : nat) (n : nat) : term118 p n.
Proof. exact (@lem1006554 p n). Qed.
Lemma lem1006556 (n : nat) (p : nat) : (term118 p n) = (term15 n p).
Proof. exact (eq_refl (term118 p n)). Qed.
Lemma lem1006557 (n : nat) (p : nat) : term15 n p.
Proof. exact (EQ_MP (@lem1006556 n p) (@lem1006555 p n)). Qed.
Lemma lem1006558 (n : nat) (p : nat) (m : nat) : term119 n p m.
Proof. exact (@lem1006557 n p m). Qed.
Lemma lem1006559 (m : nat) (n : nat) (p : nat) : (term119 n p m) = (term4 m n p).
Proof. exact (eq_refl (term119 n p m)). Qed.
Lemma lem1006560 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (EQ_MP (@lem1006559 m n p) (@lem1006558 n p m)). Qed.
Lemma lem1006562 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1005507 m n p (@lem1006560 m n p)). Qed.
Lemma lem1006563 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : term8.
Proof. exact (@lem1006562 m n p (@lem1005492 m n p h1)). Qed.
Lemma lem1006564 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : False.
Proof. exact (@lem1006563 m n p h1 (@lem75543)). Qed.
Lemma lem1006565 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : (term3 m n p) = False.
Proof. exact (prop_ext (fun h2 : term3 m n p => @lem1006564 m n p h1) (fun h2 : False => @lem1005492 m n p h1)). Qed.
Lemma lem1006566 (m : nat) (n : nat) (p : nat) (h1 : term3 m n p) : False.
Proof. exact (EQ_MP (@lem1006565 m n p h1) (@lem1005492 m n p h1)). Qed.
Lemma lem1006567 (m : nat) (n : nat) (p : nat) : term2 m n p.
Proof. exact (fun h0 : term3 m n p => @lem1006566 m n p h0). Qed.
Lemma lem1006570 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = p) = ((term1 m n) = (NUMERAL p)).
Proof. exact (EQ_MP (@lem1005491 m n p) (@lem1006567 m n p)). Qed.
