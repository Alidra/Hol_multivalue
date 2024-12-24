Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_LE_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483460_spec.
Require Import thm1483519_spec.
Require Import thm1483533_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Lemma lem1535675 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1535676 : term2 = term3.
Proof. exact (@lem1535675 term4). Qed.
Lemma lem1535677 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1535678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1535680 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1535678) (@lem1535677 x)). Qed.
Lemma lem1535681 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1535680 x)). Qed.
Lemma lem1535682 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535683 : term3 = term11.
Proof. exact (MK_COMB (@lem1535682) (@lem1535681)). Qed.
Lemma lem1535685 : term2 = term11.
Proof. exact (TRANS (@lem1535676) (@lem1535683)). Qed.
Lemma lem1535688 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1535689 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1535688 x)). Qed.
Lemma lem1535690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535691 : term11 = term11.
Proof. exact (MK_COMB (@lem1535690) (@lem1535689)). Qed.
Lemma lem1535692 : term2 = term11.
Proof. exact (TRANS (@lem1535685) (@lem1535691)). Qed.
Lemma lem1535693 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483533 x (real_abs x)). Qed.
Lemma lem1535706 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1483519 x (real_abs x)). Qed.
Lemma lem1535707 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535708 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1535707) (@lem1535706 x)). Qed.
Lemma lem1535709 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1535710 (x : real) : (term12 x) = (term18 x).
Proof. exact (MK_COMB (@lem1535708 x) (@lem1535709)). Qed.
Lemma lem1535711 (x : real) : (term8 x) = (term18 x).
Proof. exact (TRANS (@lem1535693 x) (@lem1535710 x)). Qed.
Lemma lem1535712 : term10 = term19.
Proof. exact (fun_ext (fun x : real => @lem1535711 x)). Qed.
Lemma lem1535713 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535714 : term11 = term20.
Proof. exact (MK_COMB (@lem1535713) (@lem1535712)). Qed.
Lemma lem1535725 : term2 = term20.
Proof. exact (TRANS (@lem1535692) (@lem1535714)). Qed.
Lemma lem1535726 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1535727 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1535726 x)). Qed.
Lemma lem1535728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535729 : term20 = term20.
Proof. exact (MK_COMB (@lem1535728) (@lem1535727)). Qed.
Lemma lem1535730 : term2 = term20.
Proof. exact (TRANS (@lem1535725) (@lem1535729)). Qed.
Lemma lem1535732 (a : real) (x : real) (r : real) : (term21 a x r) = (term22 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1535733 (x : real) : (term18 x) = (term23 x).
Proof. exact (@lem1535732 x x term17). Qed.
Lemma lem1535740 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1535743 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1535744 (x : real) : (term25 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1535743 x) (@lem1535740 x)). Qed.
Lemma lem1535745 (x : real) : (real_add x x) = (term26 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1535746 : term27 = term28.
Proof. exact (@lem1367770 term29 term29). Qed.
Lemma lem1535747 : term30 = term31.
Proof. exact (@lem706885). Qed.
Lemma lem1535748 : (term30 = term31) = (term32 = term33).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term31). Qed.
Lemma lem1535749 : term32 = term33.
Proof. exact (EQ_MP (@lem1535748) (@lem1535747)). Qed.
Lemma lem1535750 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535751 : term28 = term34.
Proof. exact (MK_COMB (@lem1535750) (@lem1535749)). Qed.
Lemma lem1535752 : term27 = term34.
Proof. exact (TRANS (@lem1535746) (@lem1535751)). Qed.
Lemma lem1535753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535754 : term35 = term36.
Proof. exact (MK_COMB (@lem1535753) (@lem1535752)). Qed.
Lemma lem1535755 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535756 (x : real) : (term26 x) = (term37 x).
Proof. exact (MK_COMB (@lem1535754) (@lem1535755 x)). Qed.
Lemma lem1535757 (x : real) : (real_add x x) = (term37 x).
Proof. exact (TRANS (@lem1535745 x) (@lem1535756 x)). Qed.
Lemma lem1535758 (x : real) : (term25 x) = (term37 x).
Proof. exact (TRANS (@lem1535744 x) (@lem1535757 x)). Qed.
Lemma lem1535759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535760 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1535759) (@lem1535758 x)). Qed.
Lemma lem1535761 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1535762 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1535760 x) (@lem1535761)). Qed.
Lemma lem1535774 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483442 term44 x). Qed.
Lemma lem1535776 (m : nat) : (term45 m) = term17.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1535777 : term46 = term17.
Proof. exact (@lem1535776 term29). Qed.
Lemma lem1535778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535779 : term47 = term48.
Proof. exact (MK_COMB (@lem1535778) (@lem1535777)). Qed.
Lemma lem1535780 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535781 (x : real) : (term43 x) = (term49 x).
Proof. exact (MK_COMB (@lem1535779) (@lem1535780 x)). Qed.
Lemma lem1535782 (x : real) : (term42 x) = (term49 x).
Proof. exact (TRANS (@lem1535774 x) (@lem1535781 x)). Qed.
Lemma lem1535783 (x : real) : (term49 x) = term17.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1535785 (x : real) : (term42 x) = term17.
Proof. exact (TRANS (@lem1535782 x) (@lem1535783 x)). Qed.
Lemma lem1535786 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535787 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1535786) (@lem1535785 x)). Qed.
Lemma lem1535788 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1535789 (x : real) : (term52 x) = term53.
Proof. exact (MK_COMB (@lem1535787 x) (@lem1535788)). Qed.
Lemma lem1535790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535791 (x : real) : (term54 x) = term55.
Proof. exact (MK_COMB (@lem1535790) (@lem1535789 x)). Qed.
Lemma lem1535792 (x : real) : (term23 x) = (term56 x).
Proof. exact (MK_COMB (@lem1535791 x) (@lem1535762 x)). Qed.
Lemma lem1535795 (x : real) : (term18 x) = (term56 x).
Proof. exact (TRANS (@lem1535733 x) (@lem1535792 x)). Qed.
Lemma lem1535796 (x : real) (h1 : term56 x) : term56 x.
Proof. exact (h1). Qed.
Lemma lem1535798 (x : real) (h1 : term56 x) : term53.
Proof. exact (proj1 (@lem1535796 x h1)). Qed.
Lemma lem1535800 (n : nat) (m : nat) : (term57 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535801 : term53 = term58.
Proof. exact (@lem1535800 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535802 : term58 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535803 : term53 = False.
Proof. exact (TRANS (@lem1535801) (@lem1535802)). Qed.
Lemma lem1535804 (x : real) (h1 : term56 x) : False.
Proof. exact (EQ_MP (@lem1535803) (@lem1535798 x h1)). Qed.
Lemma lem1535805 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1535806 (x : real) (h1 : term18 x) : term56 x.
Proof. exact (EQ_MP (@lem1535795 x) (@lem1535805 x h1)). Qed.
Lemma lem1535807 (x : real) (h1 : term18 x) : (term56 x) = False.
Proof. exact (prop_ext (fun h2 : term56 x => @lem1535804 x h2) (fun h2 : False => @lem1535806 x h1)). Qed.
Lemma lem1535808 (x : real) (h1 : term18 x) : False.
Proof. exact (EQ_MP (@lem1535807 x h1) (@lem1535806 x h1)). Qed.
Lemma lem1535809 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1535810 (h1 : term20) : False.
Proof. exact (ex_elim (@lem1535809 h1) (fun x : real => fun h0 : term19 x => @lem1535808 x h0)). Qed.
Lemma lem1535811 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1535812 (h1 : term2) : term20.
Proof. exact (EQ_MP (@lem1535730) (@lem1535811 h1)). Qed.
Lemma lem1535813 (h1 : term2) : term20 = False.
Proof. exact (prop_ext (fun h2 : term20 => @lem1535810 h2) (fun h2 : False => @lem1535812 h1)). Qed.
Lemma lem1535814 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1535813 h1) (@lem1535812 h1)). Qed.
Lemma lem1535815 : term59.
Proof. exact (fun h0 : term2 => @lem1535814 h0). Qed.
Lemma lem1535816 : term60.
Proof. exact (@lem1386578 term61). Qed.
Lemma lem1535817 : term61.
Proof. exact (@lem1535816 (@lem1535815)). Qed.
