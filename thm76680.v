Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm76680_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem76578 (PRE' : nat -> nat) (h1 : (term0 PRE') = (NUMERAL 0)) : (term0 PRE') = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem76579 (PRE' : nat -> nat) (h1 : term1 PRE') : term1 PRE'.
Proof. exact (h1). Qed.
Lemma lem76580 (n : nat) (PRE' : nat -> nat) (h1 : term1 PRE') : term2 PRE' n.
Proof. exact (@lem76579 PRE' h1 n). Qed.
Lemma lem76581 (PRE' : nat -> nat) (n : nat) : (term2 PRE' n) = ((term3 PRE' n) = n).
Proof. exact (eq_refl (term2 PRE' n)). Qed.
Lemma lem76582 (n : nat) (PRE' : nat -> nat) (h1 : term1 PRE') : (term3 PRE' n) = n.
Proof. exact (EQ_MP (@lem76581 PRE' n) (@lem76580 n PRE' h1)). Qed.
Lemma lem76583 (PRE' : nat -> nat) (h1 : term1 PRE') : term1 PRE'.
Proof. exact (fun n : nat => @lem76582 n PRE' h1). Qed.
Lemma lem76584 (PRE' : nat -> nat) (h1 : term4 PRE') : term4 PRE'.
Proof. exact (h1). Qed.
Lemma lem76585 (PRE' : nat -> nat) (h1 : term4 PRE') : term1 PRE'.
Proof. exact (proj2 (@lem76584 PRE' h1)). Qed.
Lemma lem76586 (PRE' : nat -> nat) (h1 : term4 PRE') : (term0 PRE') = (NUMERAL 0).
Proof. exact (proj1 (@lem76584 PRE' h1)). Qed.
Lemma lem76587 (PRE' : nat -> nat) (h1 : term4 PRE') : ((term0 PRE') = (NUMERAL 0)) = ((term0 PRE') = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : (term0 PRE') = (NUMERAL 0) => @lem76578 PRE' h2) (fun h2 : (term0 PRE') = (NUMERAL 0) => @lem76586 PRE' h1)). Qed.
Lemma lem76588 (PRE' : nat -> nat) (h1 : term4 PRE') : (term0 PRE') = (NUMERAL 0).
Proof. exact (EQ_MP (@lem76587 PRE' h1) (@lem76586 PRE' h1)). Qed.
Lemma lem76589 (PRE' : nat -> nat) (h1 : term4 PRE') : (term1 PRE') = (term1 PRE').
Proof. exact (prop_ext (fun h2 : term1 PRE' => @lem76583 PRE' h2) (fun h2 : term1 PRE' => @lem76585 PRE' h1)). Qed.
Lemma lem76590 (PRE' : nat -> nat) (h1 : term4 PRE') : term1 PRE'.
Proof. exact (EQ_MP (@lem76589 PRE' h1) (@lem76585 PRE' h1)). Qed.
Lemma lem76591 (PRE' : nat -> nat) (h1 : term4 PRE') : term4 PRE'.
Proof. exact (conj (@lem76588 PRE' h1) (@lem76590 PRE' h1)). Qed.
Lemma lem76592 {A : Type'} (e : A) : term5 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem76593 {A : Type'} (e : A) : (term5 A e) = (term6 A e).
Proof. exact (eq_refl (term5 A e)). Qed.
Lemma lem76594 {A : Type'} (e : A) : term6 A e.
Proof. exact (EQ_MP (@lem76593 A e) (@lem76592 A e)). Qed.
Lemma lem76595 {A : Type'} (e : A) (f : type1423 A) : term7 A e f.
Proof. exact (@lem76594 A e f). Qed.
Lemma lem76596 {A : Type'} (e : A) (f : type1423 A) : (term7 A e f) = (term8 A e f).
Proof. exact (eq_refl (term7 A e f)). Qed.
Lemma lem76597 {A : Type'} (e : A) (f : type1423 A) : term8 A e f.
Proof. exact (EQ_MP (@lem76596 A e f) (@lem76595 A e f)). Qed.
Lemma lem76598 (e : nat) (f : type1606) : term9 e f.
Proof. exact (@lem76597 nat e f). Qed.
Lemma lem76599 : term10.
Proof. exact (@lem76598 (NUMERAL 0) term11). Qed.
Lemma lem76600 (fn : nat -> nat) (n : nat) : (term12 fn n) = term13.
Proof. exact (eq_refl (term12 fn n)). Qed.
Lemma lem76601 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76602 (fn : nat -> nat) (n : nat) : (term14 fn n) = (term15 n).
Proof. exact (MK_COMB (@lem76600 fn n) (@lem76601 n)). Qed.
Lemma lem76603 (n : nat) : (term15 n) = n.
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem76604 (fn : nat -> nat) (n : nat) : (term14 fn n) = n.
Proof. exact (TRANS (@lem76602 fn n) (@lem76603 n)). Qed.
Lemma lem76605 (fn : nat -> nat) (n : nat) : (term16 fn n) = (term16 fn n).
Proof. exact (eq_refl (term16 fn n)). Qed.
Lemma lem76606 (fn : nat -> nat) (n : nat) : ((term3 fn n) = (term14 fn n)) = ((term3 fn n) = n).
Proof. exact (MK_COMB (@lem76605 fn n) (@lem76604 fn n)). Qed.
Lemma lem76607 (fn : nat -> nat) : (term17 fn) = (term18 fn).
Proof. exact (fun_ext (fun n : nat => @lem76606 fn n)). Qed.
Lemma lem76608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76609 (fn : nat -> nat) : (term19 fn) = (term1 fn).
Proof. exact (MK_COMB (@lem76608) (@lem76607 fn)). Qed.
Lemma lem76610 (fn : nat -> nat) : (term20 fn) = (term20 fn).
Proof. exact (eq_refl (term20 fn)). Qed.
Lemma lem76611 (fn : nat -> nat) : (term21 fn) = (term4 fn).
Proof. exact (MK_COMB (@lem76610 fn) (@lem76609 fn)). Qed.
Lemma lem76612 : term22 = term23.
Proof. exact (fun_ext (fun fn : nat -> nat => @lem76611 fn)). Qed.
Lemma lem76613 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem76614 : term10 = term24.
Proof. exact (MK_COMB (@lem76613) (@lem76612)). Qed.
Lemma lem76615 : term24.
Proof. exact (EQ_MP (@lem76614) (@lem76599)). Qed.
Lemma lem76616 (PRE' : nat -> nat) (h1 : term4 PRE') : term4 PRE'.
Proof. exact (h1). Qed.
Lemma lem76617 (PRE' : nat -> nat) (h1 : term4 PRE') : term1 PRE'.
Proof. exact (proj2 (@lem76616 PRE' h1)). Qed.
Lemma lem76618 (PRE' : nat -> nat) (h1 : term4 PRE') : (term0 PRE') = (NUMERAL 0).
Proof. exact (proj1 (@lem76616 PRE' h1)). Qed.
Lemma lem76619 (PRE' : nat -> nat) (h1 : term4 PRE') : term4 PRE'.
Proof. exact (conj (@lem76618 PRE' h1) (@lem76617 PRE' h1)). Qed.
Lemma lem76620 (PRE' : nat -> nat) (h1 : term4 PRE') : term24.
Proof. exact (ex_intro term23 PRE' (@lem76619 PRE' h1)). Qed.
Lemma lem76621 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem76622 (h1 : term24) : term24.
Proof. exact (ex_elim (@lem76621 h1) (fun PRE' : nat -> nat => fun h0 : term23 PRE' => @lem76620 PRE' h0)). Qed.
Lemma lem76623 : term24 = term24.
Proof. exact (prop_ext (fun h1 : term24 => @lem76622 h1) (fun h1 : term24 => @lem76615)). Qed.
Lemma lem76624 : term24.
Proof. exact (EQ_MP (@lem76623) (@lem76615)). Qed.
Lemma lem76625 (PRE' : nat -> nat) (h1 : term4 PRE') : term24.
Proof. exact (ex_intro term23 PRE' (@lem76591 PRE' h1)). Qed.
Lemma lem76626 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem76627 (h1 : term24) : term24.
Proof. exact (ex_elim (@lem76626 h1) (fun PRE' : nat -> nat => fun h0 : term23 PRE' => @lem76625 PRE' h0)). Qed.
Lemma lem76628 : term24 = term24.
Proof. exact (prop_ext (fun h1 : term24 => @lem76627 h1) (fun h1 : term24 => @lem76624)). Qed.
Lemma lem76629 : term24.
Proof. exact (EQ_MP (@lem76628) (@lem76624)). Qed.
Lemma lem76632 (PRE' : nat -> nat) (h1 : term4 PRE') : term4 PRE'.
Proof. exact (h1). Qed.
Lemma lem76633 (PRE' : nat -> nat) (h1 : term4 PRE') : term24.
Proof. exact (ex_intro term23 PRE' (@lem76632 PRE' h1)). Qed.
Lemma lem76634 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem76635 (h1 : term24) : term24.
Proof. exact (ex_elim (@lem76634 h1) (fun PRE' : nat -> nat => fun h0 : term23 PRE' => @lem76633 PRE' h0)). Qed.
Lemma lem76636 : term24 = term24.
Proof. exact (prop_ext (fun h1 : term24 => @lem76635 h1) (fun h1 : term24 => @lem76629)). Qed.
Lemma lem76637 : term24.
Proof. exact (EQ_MP (@lem76636) (@lem76629)). Qed.
Lemma lem76638 : term25.
Proof. exact (fun _2151 : type1674 => @lem76637). Qed.
Lemma lem76639 {A B : Type'} (P : type1413 A B) : term26 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem76640 {A B : Type'} (P : type1413 A B) : (term26 A B P) = ((term27 A B P) = (term28 A B P)).
Proof. exact (eq_refl (term26 A B P)). Qed.
Lemma lem76643 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term28 A B P).
Proof. exact (EQ_MP (@lem76640 A B P) (@lem76639 A B P)). Qed.
Lemma lem76644 (P : type1302) : (term29 P) = (term30 P).
Proof. exact (@lem76643 type1674 (nat -> nat) P). Qed.
Lemma lem76645 : term31 = term32.
Proof. exact (@lem76644 term33). Qed.
Lemma lem76646 (_2151 : type1674) : (term34 _2151) = term23.
Proof. exact (eq_refl (term34 _2151)). Qed.
Lemma lem76647 (PRE' : nat -> nat) : PRE' = PRE'.
Proof. exact (eq_refl PRE'). Qed.
Lemma lem76648 (_2151 : type1674) (PRE' : nat -> nat) : (term35 _2151 PRE') = (term36 PRE').
Proof. exact (MK_COMB (@lem76646 _2151) (@lem76647 PRE')). Qed.
Lemma lem76649 (PRE' : nat -> nat) : (term36 PRE') = (term4 PRE').
Proof. exact (eq_refl (term36 PRE')). Qed.
Lemma lem76650 (_2151 : type1674) (PRE' : nat -> nat) : (term35 _2151 PRE') = (term4 PRE').
Proof. exact (TRANS (@lem76648 _2151 PRE') (@lem76649 PRE')). Qed.
Lemma lem76651 (_2151 : type1674) : (term37 _2151) = term23.
Proof. exact (fun_ext (fun PRE' : nat -> nat => @lem76650 _2151 PRE')). Qed.
Lemma lem76652 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem76653 (_2151 : type1674) : (term38 _2151) = term24.
Proof. exact (MK_COMB (@lem76652) (@lem76651 _2151)). Qed.
Lemma lem76654 : term39 = term40.
Proof. exact (fun_ext (fun _2151 : type1674 => @lem76653 _2151)). Qed.
Lemma lem76655 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem76656 : term31 = term25.
Proof. exact (MK_COMB (@lem76655) (@lem76654)). Qed.
Lemma lem76657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem76658 : term41 = term42.
Proof. exact (MK_COMB (@lem76657) (@lem76656)). Qed.
Lemma lem76659 (_2151 : type1674) : (term34 _2151) = term23.
Proof. exact (eq_refl (term34 _2151)). Qed.
Lemma lem76660 (PRE' : type1308) (_2151 : type1674) : (PRE' _2151) = (PRE' _2151).
Proof. exact (eq_refl (PRE' _2151)). Qed.
Lemma lem76661 (PRE' : type1308) (_2151 : type1674) : (term43 PRE' _2151) = (term44 PRE' _2151).
Proof. exact (MK_COMB (@lem76659 _2151) (@lem76660 PRE' _2151)). Qed.
Lemma lem76662 (PRE' : type1308) (_2151 : type1674) : (term44 PRE' _2151) = (term45 PRE' _2151).
Proof. exact (eq_refl (term44 PRE' _2151)). Qed.
Lemma lem76663 (PRE' : type1308) (_2151 : type1674) : (term43 PRE' _2151) = (term45 PRE' _2151).
Proof. exact (TRANS (@lem76661 PRE' _2151) (@lem76662 PRE' _2151)). Qed.
Lemma lem76664 (PRE' : type1308) : (term46 PRE') = (term47 PRE').
Proof. exact (fun_ext (fun _2151 : type1674 => @lem76663 PRE' _2151)). Qed.
Lemma lem76665 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem76666 (PRE' : type1308) : (term48 PRE') = (term49 PRE').
Proof. exact (MK_COMB (@lem76665) (@lem76664 PRE')). Qed.
Lemma lem76667 : term50 = term51.
Proof. exact (fun_ext (fun PRE' : type1308 => @lem76666 PRE')). Qed.
Lemma lem76668 : (@ex ((prod nat (prod nat nat)) -> nat -> nat)) = (@ex ((prod nat (prod nat nat)) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> nat -> nat))). Qed.
Lemma lem76669 : term32 = term52.
Proof. exact (MK_COMB (@lem76668) (@lem76667)). Qed.
Lemma lem76670 : (term31 = term32) = (term25 = term52).
Proof. exact (MK_COMB (@lem76658) (@lem76669)). Qed.
Lemma lem76671 : term25 = term52.
Proof. exact (EQ_MP (@lem76670) (@lem76645)). Qed.
Lemma lem76672 : term52.
Proof. exact (EQ_MP (@lem76671) (@lem76638)). Qed.
Lemma lem76674 {A : Type'} : (@ex A) = (term53 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem76675 : (@ex ((prod nat (prod nat nat)) -> nat -> nat)) = term54.
Proof. exact (@lem76674 type1308). Qed.
Lemma lem76676 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem76677 : term52 = term55.
Proof. exact (MK_COMB (@lem76675) (@lem76676)). Qed.
Lemma lem76678 : term55 = term56.
Proof. exact (eq_refl term55). Qed.
Lemma lem76679 : term52 = term56.
Proof. exact (TRANS (@lem76677) (@lem76678)). Qed.
Lemma lem76680 : term56.
Proof. exact (EQ_MP (@lem76679) (@lem76672)). Qed.
