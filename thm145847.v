Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm145847_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem145745 (FACT' : nat -> nat) (h1 : (term0 FACT') = term1) : (term0 FACT') = term1.
Proof. exact (h1). Qed.
Lemma lem145746 (FACT' : nat -> nat) (h1 : term2 FACT') : term2 FACT'.
Proof. exact (h1). Qed.
Lemma lem145747 (n : nat) (FACT' : nat -> nat) (h1 : term2 FACT') : term3 FACT' n.
Proof. exact (@lem145746 FACT' h1 n). Qed.
Lemma lem145748 (FACT' : nat -> nat) (n : nat) : (term3 FACT' n) = ((term4 FACT' n) = (term5 FACT' n)).
Proof. exact (eq_refl (term3 FACT' n)). Qed.
Lemma lem145749 (n : nat) (FACT' : nat -> nat) (h1 : term2 FACT') : (term4 FACT' n) = (term5 FACT' n).
Proof. exact (EQ_MP (@lem145748 FACT' n) (@lem145747 n FACT' h1)). Qed.
Lemma lem145750 (FACT' : nat -> nat) (h1 : term2 FACT') : term2 FACT'.
Proof. exact (fun n : nat => @lem145749 n FACT' h1). Qed.
Lemma lem145751 (FACT' : nat -> nat) (h1 : term6 FACT') : term6 FACT'.
Proof. exact (h1). Qed.
Lemma lem145752 (FACT' : nat -> nat) (h1 : term6 FACT') : term2 FACT'.
Proof. exact (proj2 (@lem145751 FACT' h1)). Qed.
Lemma lem145753 (FACT' : nat -> nat) (h1 : term6 FACT') : (term0 FACT') = term1.
Proof. exact (proj1 (@lem145751 FACT' h1)). Qed.
Lemma lem145754 (FACT' : nat -> nat) (h1 : term6 FACT') : ((term0 FACT') = term1) = ((term0 FACT') = term1).
Proof. exact (prop_ext (fun h2 : (term0 FACT') = term1 => @lem145745 FACT' h2) (fun h2 : (term0 FACT') = term1 => @lem145753 FACT' h1)). Qed.
Lemma lem145755 (FACT' : nat -> nat) (h1 : term6 FACT') : (term0 FACT') = term1.
Proof. exact (EQ_MP (@lem145754 FACT' h1) (@lem145753 FACT' h1)). Qed.
Lemma lem145756 (FACT' : nat -> nat) (h1 : term6 FACT') : (term2 FACT') = (term2 FACT').
Proof. exact (prop_ext (fun h2 : term2 FACT' => @lem145750 FACT' h2) (fun h2 : term2 FACT' => @lem145752 FACT' h1)). Qed.
Lemma lem145757 (FACT' : nat -> nat) (h1 : term6 FACT') : term2 FACT'.
Proof. exact (EQ_MP (@lem145756 FACT' h1) (@lem145752 FACT' h1)). Qed.
Lemma lem145758 (FACT' : nat -> nat) (h1 : term6 FACT') : term6 FACT'.
Proof. exact (conj (@lem145755 FACT' h1) (@lem145757 FACT' h1)). Qed.
Lemma lem145759 {A : Type'} (e : A) : term7 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem145760 {A : Type'} (e : A) : (term7 A e) = (term8 A e).
Proof. exact (eq_refl (term7 A e)). Qed.
Lemma lem145761 {A : Type'} (e : A) : term8 A e.
Proof. exact (EQ_MP (@lem145760 A e) (@lem145759 A e)). Qed.
Lemma lem145762 {A : Type'} (e : A) (f : type1423 A) : term9 A e f.
Proof. exact (@lem145761 A e f). Qed.
Lemma lem145763 {A : Type'} (e : A) (f : type1423 A) : (term9 A e f) = (term10 A e f).
Proof. exact (eq_refl (term9 A e f)). Qed.
Lemma lem145764 {A : Type'} (e : A) (f : type1423 A) : term10 A e f.
Proof. exact (EQ_MP (@lem145763 A e f) (@lem145762 A e f)). Qed.
Lemma lem145765 (e : nat) (f : type1606) : term11 e f.
Proof. exact (@lem145764 nat e f). Qed.
Lemma lem145766 : term12.
Proof. exact (@lem145765 term1 term13). Qed.
Lemma lem145767 (fn : nat -> nat) (n : nat) : (term14 fn n) = (term15 fn n).
Proof. exact (eq_refl (term14 fn n)). Qed.
Lemma lem145768 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem145769 (fn : nat -> nat) (n : nat) : (term16 fn n) = (term17 fn n).
Proof. exact (MK_COMB (@lem145767 fn n) (@lem145768 n)). Qed.
Lemma lem145770 (fn : nat -> nat) (n : nat) : (term17 fn n) = (term5 fn n).
Proof. exact (eq_refl (term17 fn n)). Qed.
Lemma lem145771 (fn : nat -> nat) (n : nat) : (term16 fn n) = (term5 fn n).
Proof. exact (TRANS (@lem145769 fn n) (@lem145770 fn n)). Qed.
Lemma lem145772 (fn : nat -> nat) (n : nat) : (term18 fn n) = (term18 fn n).
Proof. exact (eq_refl (term18 fn n)). Qed.
Lemma lem145773 (fn : nat -> nat) (n : nat) : ((term4 fn n) = (term16 fn n)) = ((term4 fn n) = (term5 fn n)).
Proof. exact (MK_COMB (@lem145772 fn n) (@lem145771 fn n)). Qed.
Lemma lem145774 (fn : nat -> nat) : (term19 fn) = (term20 fn).
Proof. exact (fun_ext (fun n : nat => @lem145773 fn n)). Qed.
Lemma lem145775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem145776 (fn : nat -> nat) : (term21 fn) = (term2 fn).
Proof. exact (MK_COMB (@lem145775) (@lem145774 fn)). Qed.
Lemma lem145777 (fn : nat -> nat) : (term22 fn) = (term22 fn).
Proof. exact (eq_refl (term22 fn)). Qed.
Lemma lem145778 (fn : nat -> nat) : (term23 fn) = (term6 fn).
Proof. exact (MK_COMB (@lem145777 fn) (@lem145776 fn)). Qed.
Lemma lem145779 : term24 = term25.
Proof. exact (fun_ext (fun fn : nat -> nat => @lem145778 fn)). Qed.
Lemma lem145780 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem145781 : term12 = term26.
Proof. exact (MK_COMB (@lem145780) (@lem145779)). Qed.
Lemma lem145782 : term26.
Proof. exact (EQ_MP (@lem145781) (@lem145766)). Qed.
Lemma lem145783 (FACT' : nat -> nat) (h1 : term6 FACT') : term6 FACT'.
Proof. exact (h1). Qed.
Lemma lem145784 (FACT' : nat -> nat) (h1 : term6 FACT') : term2 FACT'.
Proof. exact (proj2 (@lem145783 FACT' h1)). Qed.
Lemma lem145785 (FACT' : nat -> nat) (h1 : term6 FACT') : (term0 FACT') = term1.
Proof. exact (proj1 (@lem145783 FACT' h1)). Qed.
Lemma lem145786 (FACT' : nat -> nat) (h1 : term6 FACT') : term6 FACT'.
Proof. exact (conj (@lem145785 FACT' h1) (@lem145784 FACT' h1)). Qed.
Lemma lem145787 (FACT' : nat -> nat) (h1 : term6 FACT') : term26.
Proof. exact (ex_intro term25 FACT' (@lem145786 FACT' h1)). Qed.
Lemma lem145788 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem145789 (h1 : term26) : term26.
Proof. exact (ex_elim (@lem145788 h1) (fun FACT' : nat -> nat => fun h0 : term25 FACT' => @lem145787 FACT' h0)). Qed.
Lemma lem145790 : term26 = term26.
Proof. exact (prop_ext (fun h1 : term26 => @lem145789 h1) (fun h1 : term26 => @lem145782)). Qed.
Lemma lem145791 : term26.
Proof. exact (EQ_MP (@lem145790) (@lem145782)). Qed.
Lemma lem145792 (FACT' : nat -> nat) (h1 : term6 FACT') : term26.
Proof. exact (ex_intro term25 FACT' (@lem145758 FACT' h1)). Qed.
Lemma lem145793 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem145794 (h1 : term26) : term26.
Proof. exact (ex_elim (@lem145793 h1) (fun FACT' : nat -> nat => fun h0 : term25 FACT' => @lem145792 FACT' h0)). Qed.
Lemma lem145795 : term26 = term26.
Proof. exact (prop_ext (fun h1 : term26 => @lem145794 h1) (fun h1 : term26 => @lem145791)). Qed.
Lemma lem145796 : term26.
Proof. exact (EQ_MP (@lem145795) (@lem145791)). Qed.
Lemma lem145799 (FACT' : nat -> nat) (h1 : term6 FACT') : term6 FACT'.
Proof. exact (h1). Qed.
Lemma lem145800 (FACT' : nat -> nat) (h1 : term6 FACT') : term26.
Proof. exact (ex_intro term25 FACT' (@lem145799 FACT' h1)). Qed.
Lemma lem145801 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem145802 (h1 : term26) : term26.
Proof. exact (ex_elim (@lem145801 h1) (fun FACT' : nat -> nat => fun h0 : term25 FACT' => @lem145800 FACT' h0)). Qed.
Lemma lem145803 : term26 = term26.
Proof. exact (prop_ext (fun h1 : term26 => @lem145802 h1) (fun h1 : term26 => @lem145796)). Qed.
Lemma lem145804 : term26.
Proof. exact (EQ_MP (@lem145803) (@lem145796)). Qed.
Lemma lem145805 : term27.
Proof. exact (fun _2944 : type1673 => @lem145804). Qed.
Lemma lem145806 {A B : Type'} (P : type1413 A B) : term28 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem145807 {A B : Type'} (P : type1413 A B) : (term28 A B P) = ((term29 A B P) = (term30 A B P)).
Proof. exact (eq_refl (term28 A B P)). Qed.
Lemma lem145810 {A B : Type'} (P : type1413 A B) : (term29 A B P) = (term30 A B P).
Proof. exact (EQ_MP (@lem145807 A B P) (@lem145806 A B P)). Qed.
Lemma lem145811 (P : type1288) : (term31 P) = (term32 P).
Proof. exact (@lem145810 type1673 (nat -> nat) P). Qed.
Lemma lem145812 : term33 = term34.
Proof. exact (@lem145811 term35). Qed.
Lemma lem145813 (_2944 : type1673) : (term36 _2944) = term25.
Proof. exact (eq_refl (term36 _2944)). Qed.
Lemma lem145814 (FACT' : nat -> nat) : FACT' = FACT'.
Proof. exact (eq_refl FACT'). Qed.
Lemma lem145815 (_2944 : type1673) (FACT' : nat -> nat) : (term37 _2944 FACT') = (term38 FACT').
Proof. exact (MK_COMB (@lem145813 _2944) (@lem145814 FACT')). Qed.
Lemma lem145816 (FACT' : nat -> nat) : (term38 FACT') = (term6 FACT').
Proof. exact (eq_refl (term38 FACT')). Qed.
Lemma lem145817 (_2944 : type1673) (FACT' : nat -> nat) : (term37 _2944 FACT') = (term6 FACT').
Proof. exact (TRANS (@lem145815 _2944 FACT') (@lem145816 FACT')). Qed.
Lemma lem145818 (_2944 : type1673) : (term39 _2944) = term25.
Proof. exact (fun_ext (fun FACT' : nat -> nat => @lem145817 _2944 FACT')). Qed.
Lemma lem145819 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem145820 (_2944 : type1673) : (term40 _2944) = term26.
Proof. exact (MK_COMB (@lem145819) (@lem145818 _2944)). Qed.
Lemma lem145821 : term41 = term42.
Proof. exact (fun_ext (fun _2944 : type1673 => @lem145820 _2944)). Qed.
Lemma lem145822 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem145823 : term33 = term27.
Proof. exact (MK_COMB (@lem145822) (@lem145821)). Qed.
Lemma lem145824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145825 : term43 = term44.
Proof. exact (MK_COMB (@lem145824) (@lem145823)). Qed.
Lemma lem145826 (_2944 : type1673) : (term36 _2944) = term25.
Proof. exact (eq_refl (term36 _2944)). Qed.
Lemma lem145827 (FACT' : type1292) (_2944 : type1673) : (FACT' _2944) = (FACT' _2944).
Proof. exact (eq_refl (FACT' _2944)). Qed.
Lemma lem145828 (FACT' : type1292) (_2944 : type1673) : (term45 FACT' _2944) = (term46 FACT' _2944).
Proof. exact (MK_COMB (@lem145826 _2944) (@lem145827 FACT' _2944)). Qed.
Lemma lem145829 (FACT' : type1292) (_2944 : type1673) : (term46 FACT' _2944) = (term47 FACT' _2944).
Proof. exact (eq_refl (term46 FACT' _2944)). Qed.
Lemma lem145830 (FACT' : type1292) (_2944 : type1673) : (term45 FACT' _2944) = (term47 FACT' _2944).
Proof. exact (TRANS (@lem145828 FACT' _2944) (@lem145829 FACT' _2944)). Qed.
Lemma lem145831 (FACT' : type1292) : (term48 FACT') = (term49 FACT').
Proof. exact (fun_ext (fun _2944 : type1673 => @lem145830 FACT' _2944)). Qed.
Lemma lem145832 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem145833 (FACT' : type1292) : (term50 FACT') = (term51 FACT').
Proof. exact (MK_COMB (@lem145832) (@lem145831 FACT')). Qed.
Lemma lem145834 : term52 = term53.
Proof. exact (fun_ext (fun FACT' : type1292 => @lem145833 FACT')). Qed.
Lemma lem145835 : (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> nat)) = (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> nat))). Qed.
Lemma lem145836 : term34 = term54.
Proof. exact (MK_COMB (@lem145835) (@lem145834)). Qed.
Lemma lem145837 : (term33 = term34) = (term27 = term54).
Proof. exact (MK_COMB (@lem145825) (@lem145836)). Qed.
Lemma lem145838 : term27 = term54.
Proof. exact (EQ_MP (@lem145837) (@lem145812)). Qed.
Lemma lem145839 : term54.
Proof. exact (EQ_MP (@lem145838) (@lem145805)). Qed.
Lemma lem145841 {A : Type'} : (@ex A) = (term55 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem145842 : (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> nat)) = term56.
Proof. exact (@lem145841 type1292). Qed.
Lemma lem145843 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem145844 : term54 = term57.
Proof. exact (MK_COMB (@lem145842) (@lem145843)). Qed.
Lemma lem145845 : term57 = term58.
Proof. exact (eq_refl term57). Qed.
Lemma lem145846 : term54 = term58.
Proof. exact (TRANS (@lem145844) (@lem145845)). Qed.
Lemma lem145847 : term58.
Proof. exact (EQ_MP (@lem145846) (@lem145839)). Qed.
