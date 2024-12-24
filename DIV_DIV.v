Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_DIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIV_0_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_ANTISYM_spec.
Require Import LE_RDIV_EQ_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem218680 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem218681 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem218682 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem218681 t1) (@lem218680 t1)). Qed.
Lemma lem218683 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem218682 t1 t2). Qed.
Lemma lem218684 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem218685 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem218684 t1 t2) (@lem218683 t1 t2)). Qed.
Lemma lem218686 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem218685 t1 t2 t3). Qed.
Lemma lem218687 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem218688 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem218687 t1 t2 t3) (@lem218686 t1 t2 t3)). Qed.
Lemma lem218689 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem218688 t1 t2 t3)). Qed.
Lemma lem218691 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem218692 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (@lem218691 (term8 m n)). Qed.
Lemma lem218693 (m : nat) (n : nat) : (term9 m n) = (term8 m n).
Proof. exact (SYM (@lem218692 m n)). Qed.
Lemma lem218694 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem218697 (m : nat) (n : nat) (h1 : term11 m n) : term11 m n.
Proof. exact (h1). Qed.
Lemma lem218698 (m : nat) (n : nat) : term12 m n.
Proof. exact (fun h0 : term11 m n => @lem218697 m n h0). Qed.
Lemma lem218699 (m : nat) (n : nat) (h1 : term12 m n) : term12 m n.
Proof. exact (h1). Qed.
Lemma lem218700 (m : nat) (n : nat) (h1 : term11 m n) : term11 m n.
Proof. exact (h1). Qed.
Lemma lem218701 (m : nat) (n : nat) (h1 : term11 m n) (h2 : term12 m n) : term11 m n.
Proof. exact (@lem218699 m n h2 (@lem218700 m n h1)). Qed.
Lemma lem218702 (m : nat) (n : nat) (h1 : term11 m n) : term13 m n.
Proof. exact (fun h0 : term12 m n => @lem218701 m n h1 h0). Qed.
Lemma lem218703 (m : nat) (n : nat) (h1 : term12 m n) : term12 m n.
Proof. exact (h1). Qed.
Lemma lem218704 (m : nat) (n : nat) (h1 : term11 m n) (h2 : term12 m n) : term11 m n.
Proof. exact (@lem218702 m n h1 (@lem218703 m n h2)). Qed.
Lemma lem218705 (m : nat) (n : nat) (h1 : term12 m n) : term12 m n.
Proof. exact (fun h0 : term11 m n => @lem218704 m n h0 h1). Qed.
Lemma lem218706 (m : nat) (n : nat) : term14 m n.
Proof. exact (fun h0 : term12 m n => @lem218705 m n h0). Qed.
Lemma lem218709 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem218706 m n (@lem218698 m n)). Qed.
Lemma lem218727 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem218728 : term15 = term16.
Proof. exact (@lem218727 term17). Qed.
Lemma lem218739 (m : nat) (n : nat) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem218740 (m : nat) (n : nat) : (term11 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem218739 m n) (@lem218728)). Qed.
Lemma lem218743 (n : nat) : (term20 n) = (term21 n).
Proof. exact (fun_ext (fun m : nat => @lem218740 m n)). Qed.
Lemma lem218744 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218745 (n : nat) : (term22 n) = (term23 n).
Proof. exact (MK_COMB (@lem218744) (@lem218743 n)). Qed.
Lemma lem218750 : term24 = term25.
Proof. exact (fun_ext (fun n : nat => @lem218745 n)). Qed.
Lemma lem218751 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218760 : term26 = term27.
Proof. exact (MK_COMB (@lem218751) (@lem218750)). Qed.
Lemma lem218769 (m : nat) (n : nat) : ((term28 n m) = (m = n)) = ((term28 n m) = (m = n)).
Proof. exact (eq_refl ((term28 n m) = (m = n))). Qed.
Lemma lem218770 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem218769 m n)). Qed.
Lemma lem218771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218772 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem218771) (@lem218770 m)). Qed.
Lemma lem218773 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem218772 m)). Qed.
Lemma lem218774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218775 : term17 = term17.
Proof. exact (MK_COMB (@lem218774) (@lem218773)). Qed.
Lemma lem218776 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem218777 : term16 = term16.
Proof. exact (MK_COMB (@lem218776) (@lem218775)). Qed.
Lemma lem218778 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem218783 (m : nat) (k : nat) (n : nat) : ((Peano.le k m) = (Peano.le k n)) = ((Peano.le k m) = (Peano.le k n)).
Proof. exact (eq_refl ((Peano.le k m) = (Peano.le k n))). Qed.
Lemma lem218784 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (fun_ext (fun k : nat => @lem218783 m k n)). Qed.
Lemma lem218785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218786 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem218785) (@lem218784 m n)). Qed.
Lemma lem218787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem218788 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem218787) (@lem218786 m n)). Qed.
Lemma lem218789 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem218788 m n) (@lem218778 m n)). Qed.
Lemma lem218790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem218791 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem218790) (@lem218789 m n)). Qed.
Lemma lem218792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem218793 (m : nat) (n : nat) : (term18 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem218792) (@lem218791 m n)). Qed.
Lemma lem218794 (m : nat) (n : nat) : (term19 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem218793 m n) (@lem218777)). Qed.
Lemma lem218795 (n : nat) : (term21 n) = (term21 n).
Proof. exact (fun_ext (fun m : nat => @lem218794 m n)). Qed.
Lemma lem218796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218797 (n : nat) : (term23 n) = (term23 n).
Proof. exact (MK_COMB (@lem218796) (@lem218795 n)). Qed.
Lemma lem218798 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem218797 n)). Qed.
Lemma lem218799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218800 : term27 = term27.
Proof. exact (MK_COMB (@lem218799) (@lem218798)). Qed.
Lemma lem218839 : term26 = term27.
Proof. exact (TRANS (@lem218760) (@lem218800)). Qed.
Lemma lem218840 : term27 = term26.
Proof. exact (SYM (@lem218839)). Qed.
Lemma lem218841 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem218842 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem218857 (m : nat) (k : nat) (n : nat) : ((Peano.le k m) = (Peano.le k n)) = (term35 m k n).
Proof. exact (@lem17784 (Peano.le k m) (Peano.le k n)). Qed.
Lemma lem218858 (m : nat) (n : nat) : (term32 m n) = (term36 m n).
Proof. exact (fun_ext (fun k : nat => @lem218857 m k n)). Qed.
Lemma lem218859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218860 (m : nat) (n : nat) : (term33 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem218859) (@lem218858 m n)). Qed.
Lemma lem218861 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem218862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem218863 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem218862) (@lem218860 m n)). Qed.
Lemma lem218864 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem218863 m n) (@lem218861 m n)). Qed.
Lemma lem218865 (m : nat) (n : nat) : (term10 m n) = (term41 m n).
Proof. exact (@lem17362 (term33 m n) (m = n)). Qed.
Lemma lem218866 (m : nat) (n : nat) : (term10 m n) = (term42 m n).
Proof. exact (TRANS (@lem218865 m n) (@lem218864 m n)). Qed.
Lemma lem218868 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem218869 (P : nat -> Prop) (Q : nat -> Prop) : (term45 P Q) = (term46 P Q).
Proof. exact (@lem218868 nat P Q). Qed.
Lemma lem218870 (m : nat) (n : nat) : (term47 m n) = (term48 m n).
Proof. exact (@lem218869 (term49 m n) (term50 m n)). Qed.
Lemma lem218871 (m : nat) (k : nat) (n : nat) : (term51 m n k) = (term52 m k n).
Proof. exact (eq_refl (term51 m n k)). Qed.
Lemma lem218872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem218873 (m : nat) (k : nat) (n : nat) : (term53 m n k) = (term54 m k n).
Proof. exact (MK_COMB (@lem218872) (@lem218871 m k n)). Qed.
Lemma lem218874 (m : nat) (k : nat) (n : nat) : (term55 m n k) = (term56 m k n).
Proof. exact (eq_refl (term55 m n k)). Qed.
Lemma lem218875 (m : nat) (k : nat) (n : nat) : (term57 m n k) = (term35 m k n).
Proof. exact (MK_COMB (@lem218873 m k n) (@lem218874 m k n)). Qed.
Lemma lem218876 (m : nat) (n : nat) : (term58 m n) = (term36 m n).
Proof. exact (fun_ext (fun k : nat => @lem218875 m k n)). Qed.
Lemma lem218877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218878 (m : nat) (n : nat) : (term47 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem218877) (@lem218876 m n)). Qed.
Lemma lem218879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem218880 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem218879) (@lem218878 m n)). Qed.
Lemma lem218881 (m : nat) (k : nat) (n : nat) : (term51 m n k) = (term52 m k n).
Proof. exact (eq_refl (term51 m n k)). Qed.
Lemma lem218882 (m : nat) (n : nat) : (term61 m n) = (term49 m n).
Proof. exact (fun_ext (fun k : nat => @lem218881 m k n)). Qed.
Lemma lem218883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218884 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem218883) (@lem218882 m n)). Qed.
Lemma lem218885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem218886 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem218885) (@lem218884 m n)). Qed.
Lemma lem218887 (m : nat) (k : nat) (n : nat) : (term55 m n k) = (term56 m k n).
Proof. exact (eq_refl (term55 m n k)). Qed.
Lemma lem218888 (m : nat) (n : nat) : (term66 m n) = (term50 m n).
Proof. exact (fun_ext (fun k : nat => @lem218887 m k n)). Qed.
Lemma lem218889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem218890 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem218889) (@lem218888 m n)). Qed.
Lemma lem218891 (m : nat) (n : nat) : (term48 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem218886 m n) (@lem218890 m n)). Qed.
Lemma lem218892 (m : nat) (n : nat) : ((term47 m n) = (term48 m n)) = ((term37 m n) = (term69 m n)).
Proof. exact (MK_COMB (@lem218880 m n) (@lem218891 m n)). Qed.
Lemma lem218893 (m : nat) (n : nat) : (term37 m n) = (term69 m n).
Proof. exact (EQ_MP (@lem218892 m n) (@lem218870 m n)). Qed.
Lemma lem218990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem218991 (m : nat) (n : nat) : (term40 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem218990) (@lem218893 m n)). Qed.
Lemma lem218992 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem218995 (m : nat) (n : nat) : (term42 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem218991 m n) (@lem218992 m n)). Qed.
Lemma lem218996 (m : nat) (n : nat) : (term10 m n) = (term71 m n).
Proof. exact (TRANS (@lem218866 m n) (@lem218995 m n)). Qed.
Lemma lem218997 (m : nat) (n : nat) (h1 : term10 m n) : term71 m n.
Proof. exact (EQ_MP (@lem218996 m n) (@lem218841 m n h1)). Qed.
Lemma lem219006 (n : nat) (m : nat) : (term72 n m) = (term73 n m).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n m)). Qed.
Lemma lem219011 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem219012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem219013 (n : nat) (m : nat) : (term74 n m) = (term75 n m).
Proof. exact (MK_COMB (@lem219012) (@lem219006 n m)). Qed.
Lemma lem219014 (m : nat) (n : nat) : (term76 m n) = (term77 m n).
Proof. exact (MK_COMB (@lem219013 n m) (@lem219011 m n)). Qed.
Lemma lem219019 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem219020 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem219019 m n) (@lem219014 m n)). Qed.
Lemma lem219021 (m : nat) (n : nat) : ((term28 n m) = (m = n)) = (term79 m n).
Proof. exact (@lem17784 (term28 n m) (m = n)). Qed.
Lemma lem219022 (m : nat) (n : nat) : ((term28 n m) = (m = n)) = (term80 m n).
Proof. exact (TRANS (@lem219021 m n) (@lem219020 m n)). Qed.
Lemma lem219023 (m : nat) : (term29 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem219022 m n)). Qed.
Lemma lem219024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219025 (m : nat) : (term30 m) = (term82 m).
Proof. exact (MK_COMB (@lem219024) (@lem219023 m)). Qed.
Lemma lem219026 : term31 = term83.
Proof. exact (fun_ext (fun m : nat => @lem219025 m)). Qed.
Lemma lem219027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219028 : term17 = term84.
Proof. exact (MK_COMB (@lem219027) (@lem219026)). Qed.
Lemma lem219034 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem219035 (P : nat -> Prop) (Q : nat -> Prop) : (term45 P Q) = (term46 P Q).
Proof. exact (@lem219034 nat P Q). Qed.
Lemma lem219036 (m : nat) : (term85 m) = (term86 m).
Proof. exact (@lem219035 (term87 m) (term88 m)). Qed.
Lemma lem219037 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem219038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219039 (m : nat) (n : nat) : (term91 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem219038) (@lem219037 m n)). Qed.
Lemma lem219040 (m : nat) (n : nat) : (term92 m n) = (term77 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem219041 (m : nat) (n : nat) : (term93 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem219039 m n) (@lem219040 m n)). Qed.
Lemma lem219042 (m : nat) : (term94 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem219041 m n)). Qed.
Lemma lem219043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219044 (m : nat) : (term85 m) = (term82 m).
Proof. exact (MK_COMB (@lem219043) (@lem219042 m)). Qed.
Lemma lem219045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem219046 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem219045) (@lem219044 m)). Qed.
Lemma lem219047 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem219048 (m : nat) : (term97 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem219047 m n)). Qed.
Lemma lem219049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219050 (m : nat) : (term98 m) = (term99 m).
Proof. exact (MK_COMB (@lem219049) (@lem219048 m)). Qed.
Lemma lem219051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219052 (m : nat) : (term100 m) = (term101 m).
Proof. exact (MK_COMB (@lem219051) (@lem219050 m)). Qed.
Lemma lem219053 (m : nat) (n : nat) : (term92 m n) = (term77 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem219054 (m : nat) : (term102 m) = (term88 m).
Proof. exact (fun_ext (fun n : nat => @lem219053 m n)). Qed.
Lemma lem219055 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219056 (m : nat) : (term103 m) = (term104 m).
Proof. exact (MK_COMB (@lem219055) (@lem219054 m)). Qed.
Lemma lem219057 (m : nat) : (term86 m) = (term105 m).
Proof. exact (MK_COMB (@lem219052 m) (@lem219056 m)). Qed.
Lemma lem219058 (m : nat) : ((term85 m) = (term86 m)) = ((term82 m) = (term105 m)).
Proof. exact (MK_COMB (@lem219046 m) (@lem219057 m)). Qed.
Lemma lem219059 (m : nat) : (term82 m) = (term105 m).
Proof. exact (EQ_MP (@lem219058 m) (@lem219036 m)). Qed.
Lemma lem219156 : term83 = term106.
Proof. exact (fun_ext (fun m : nat => @lem219059 m)). Qed.
Lemma lem219157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219158 : term84 = term107.
Proof. exact (MK_COMB (@lem219157) (@lem219156)). Qed.
Lemma lem219160 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem219161 (P : nat -> Prop) (Q : nat -> Prop) : (term45 P Q) = (term46 P Q).
Proof. exact (@lem219160 nat P Q). Qed.
Lemma lem219162 : term108 = term109.
Proof. exact (@lem219161 term110 term111). Qed.
Lemma lem219163 (m : nat) : (term112 m) = (term99 m).
Proof. exact (eq_refl (term112 m)). Qed.
Lemma lem219164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219165 (m : nat) : (term113 m) = (term101 m).
Proof. exact (MK_COMB (@lem219164) (@lem219163 m)). Qed.
Lemma lem219166 (m : nat) : (term114 m) = (term104 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem219167 (m : nat) : (term115 m) = (term105 m).
Proof. exact (MK_COMB (@lem219165 m) (@lem219166 m)). Qed.
Lemma lem219168 : term116 = term106.
Proof. exact (fun_ext (fun m : nat => @lem219167 m)). Qed.
Lemma lem219169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219170 : term108 = term107.
Proof. exact (MK_COMB (@lem219169) (@lem219168)). Qed.
Lemma lem219171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem219172 : term117 = term118.
Proof. exact (MK_COMB (@lem219171) (@lem219170)). Qed.
Lemma lem219173 (m : nat) : (term112 m) = (term99 m).
Proof. exact (eq_refl (term112 m)). Qed.
Lemma lem219174 : term119 = term110.
Proof. exact (fun_ext (fun m : nat => @lem219173 m)). Qed.
Lemma lem219175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219176 : term120 = term121.
Proof. exact (MK_COMB (@lem219175) (@lem219174)). Qed.
Lemma lem219177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219178 : term122 = term123.
Proof. exact (MK_COMB (@lem219177) (@lem219176)). Qed.
Lemma lem219179 (m : nat) : (term114 m) = (term104 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem219180 : term124 = term111.
Proof. exact (fun_ext (fun m : nat => @lem219179 m)). Qed.
Lemma lem219181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219182 : term125 = term126.
Proof. exact (MK_COMB (@lem219181) (@lem219180)). Qed.
Lemma lem219183 : term109 = term127.
Proof. exact (MK_COMB (@lem219178) (@lem219182)). Qed.
Lemma lem219184 : (term108 = term109) = (term107 = term127).
Proof. exact (MK_COMB (@lem219172) (@lem219183)). Qed.
Lemma lem219185 : term107 = term127.
Proof. exact (EQ_MP (@lem219184) (@lem219162)). Qed.
Lemma lem219292 : term84 = term127.
Proof. exact (TRANS (@lem219158) (@lem219185)). Qed.
Lemma lem219293 : term17 = term127.
Proof. exact (TRANS (@lem219028) (@lem219292)). Qed.
Lemma lem219294 (h1 : term17) : term127.
Proof. exact (EQ_MP (@lem219293) (@lem218842 h1)). Qed.
Lemma lem219301 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem219316 (m : nat) (k : nat) (n : nat) : (term56 m k n) = (term56 m k n).
Proof. exact (eq_refl (term56 m k n)). Qed.
Lemma lem219317 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (fun_ext (fun k : nat => @lem219316 m k n)). Qed.
Lemma lem219318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219319 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem219318) (@lem219317 m n)). Qed.
Lemma lem219334 (m : nat) (k : nat) (n : nat) : (term52 m k n) = (term52 m k n).
Proof. exact (eq_refl (term52 m k n)). Qed.
Lemma lem219335 (m : nat) (n : nat) : (term49 m n) = (term49 m n).
Proof. exact (fun_ext (fun k : nat => @lem219334 m k n)). Qed.
Lemma lem219336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219337 (m : nat) (n : nat) : (term63 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem219336) (@lem219335 m n)). Qed.
Lemma lem219338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219339 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem219338) (@lem219337 m n)). Qed.
Lemma lem219340 (m : nat) (n : nat) : (term69 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem219339 m n) (@lem219319 m n)). Qed.
Lemma lem219341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219342 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem219341) (@lem219340 m n)). Qed.
Lemma lem219343 (m : nat) (n : nat) : (term71 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem219342 m n) (@lem219301 m n)). Qed.
Lemma lem219344 (m : nat) (n : nat) (h1 : term10 m n) : term71 m n.
Proof. exact (EQ_MP (@lem219343 m n) (@lem218997 m n h1)). Qed.
Lemma lem219369 (m : nat) (n : nat) : (term77 m n) = (term77 m n).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem219370 (m : nat) : (term88 m) = (term88 m).
Proof. exact (fun_ext (fun n : nat => @lem219369 m n)). Qed.
Lemma lem219371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219372 (m : nat) : (term104 m) = (term104 m).
Proof. exact (MK_COMB (@lem219371) (@lem219370 m)). Qed.
Lemma lem219373 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem219372 m)). Qed.
Lemma lem219374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219375 : term126 = term126.
Proof. exact (MK_COMB (@lem219374) (@lem219373)). Qed.
Lemma lem219398 (m : nat) (n : nat) : (term90 m n) = (term90 m n).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem219399 (m : nat) : (term87 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem219398 m n)). Qed.
Lemma lem219400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219401 (m : nat) : (term99 m) = (term99 m).
Proof. exact (MK_COMB (@lem219400) (@lem219399 m)). Qed.
Lemma lem219402 : term110 = term110.
Proof. exact (fun_ext (fun m : nat => @lem219401 m)). Qed.
Lemma lem219403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219404 : term121 = term121.
Proof. exact (MK_COMB (@lem219403) (@lem219402)). Qed.
Lemma lem219405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219406 : term123 = term123.
Proof. exact (MK_COMB (@lem219405) (@lem219404)). Qed.
Lemma lem219407 : term127 = term127.
Proof. exact (MK_COMB (@lem219406) (@lem219375)). Qed.
Lemma lem219408 (h1 : term17) : term127.
Proof. exact (EQ_MP (@lem219407) (@lem219294 h1)). Qed.
Lemma lem219409 (h1 : term17) : term126.
Proof. exact (proj2 (@lem219408 h1)). Qed.
Lemma lem219410 (h1 : term17) : term121.
Proof. exact (proj1 (@lem219408 h1)). Qed.
Lemma lem219412 (m : nat) (n : nat) (h1 : term10 m n) : term69 m n.
Proof. exact (proj1 (@lem219344 m n h1)). Qed.
Lemma lem219413 (m : nat) (n : nat) (h1 : term10 m n) : term68 m n.
Proof. exact (proj2 (@lem219412 m n h1)). Qed.
Lemma lem219414 (m : nat) (n : nat) (h1 : term10 m n) : term63 m n.
Proof. exact (proj1 (@lem219412 m n h1)). Qed.
Lemma lem219432 (m : nat) (n : nat) : (term90 m n) = (term128 m n).
Proof. exact (@lem19699 (Peano.le m n) (Peano.le n m) (term38 m n)). Qed.
Lemma lem219433 (m : nat) : (term87 m) = (term129 m).
Proof. exact (fun_ext (fun n : nat => @lem219432 m n)). Qed.
Lemma lem219434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219435 (m : nat) : (term99 m) = (term130 m).
Proof. exact (MK_COMB (@lem219434) (@lem219433 m)). Qed.
Lemma lem219436 : term110 = term131.
Proof. exact (fun_ext (fun m : nat => @lem219435 m)). Qed.
Lemma lem219437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219439 : term121 = term132.
Proof. exact (MK_COMB (@lem219437) (@lem219436)). Qed.
Lemma lem219440 (h1 : term17) : term132.
Proof. exact (EQ_MP (@lem219439) (@lem219410 h1)). Qed.
Lemma lem219454 (m : nat) (n : nat) : (term77 m n) = (term77 m n).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem219455 (m : nat) : (term88 m) = (term88 m).
Proof. exact (fun_ext (fun n : nat => @lem219454 m n)). Qed.
Lemma lem219456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219457 (m : nat) : (term104 m) = (term104 m).
Proof. exact (MK_COMB (@lem219456) (@lem219455 m)). Qed.
Lemma lem219458 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem219457 m)). Qed.
Lemma lem219459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219461 : term126 = term126.
Proof. exact (MK_COMB (@lem219459) (@lem219458)). Qed.
Lemma lem219462 (h1 : term17) : term126.
Proof. exact (EQ_MP (@lem219461) (@lem219409 h1)). Qed.
Lemma lem219474 (m : nat) (k : nat) (n : nat) : (term52 m k n) = (term52 m k n).
Proof. exact (eq_refl (term52 m k n)). Qed.
Lemma lem219475 (m : nat) (n : nat) : (term49 m n) = (term49 m n).
Proof. exact (fun_ext (fun k : nat => @lem219474 m k n)). Qed.
Lemma lem219476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219478 (m : nat) (n : nat) : (term63 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem219476) (@lem219475 m n)). Qed.
Lemma lem219479 (m : nat) (n : nat) (h1 : term10 m n) : term63 m n.
Proof. exact (EQ_MP (@lem219478 m n) (@lem219414 m n h1)). Qed.
Lemma lem219487 (m : nat) (k : nat) (n : nat) : (term56 m k n) = (term56 m k n).
Proof. exact (eq_refl (term56 m k n)). Qed.
Lemma lem219488 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (fun_ext (fun k : nat => @lem219487 m k n)). Qed.
Lemma lem219489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem219491 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem219489) (@lem219488 m n)). Qed.
Lemma lem219492 (m : nat) (n : nat) (h1 : term10 m n) : term68 m n.
Proof. exact (EQ_MP (@lem219491 m n) (@lem219413 m n h1)). Qed.
Lemma lem219493 (_4390 : nat) (h1 : term17) : term133 _4390.
Proof. exact (@lem219440 h1 _4390). Qed.
Lemma lem219494 (_4390 : nat) : (term133 _4390) = (term130 _4390).
Proof. exact (eq_refl (term133 _4390)). Qed.
Lemma lem219495 (_4390 : nat) (h1 : term17) : term130 _4390.
Proof. exact (EQ_MP (@lem219494 _4390) (@lem219493 _4390 h1)). Qed.
Lemma lem219496 (_4390 : nat) (_4391 : nat) (h1 : term17) : term134 _4390 _4391.
Proof. exact (@lem219495 _4390 h1 _4391). Qed.
Lemma lem219497 (_4390 : nat) (_4391 : nat) : (term134 _4390 _4391) = (term128 _4390 _4391).
Proof. exact (eq_refl (term134 _4390 _4391)). Qed.
Lemma lem219498 (_4390 : nat) (_4391 : nat) (h1 : term17) : term128 _4390 _4391.
Proof. exact (EQ_MP (@lem219497 _4390 _4391) (@lem219496 _4390 _4391 h1)). Qed.
Lemma lem219499 (_4392 : nat) (h1 : term17) : term114 _4392.
Proof. exact (@lem219462 h1 _4392). Qed.
Lemma lem219500 (_4392 : nat) : (term114 _4392) = (term104 _4392).
Proof. exact (eq_refl (term114 _4392)). Qed.
Lemma lem219501 (_4392 : nat) (h1 : term17) : term104 _4392.
Proof. exact (EQ_MP (@lem219500 _4392) (@lem219499 _4392 h1)). Qed.
Lemma lem219502 (_4392 : nat) (_4393 : nat) (h1 : term17) : term92 _4392 _4393.
Proof. exact (@lem219501 _4392 h1 _4393). Qed.
Lemma lem219503 (_4392 : nat) (_4393 : nat) : (term92 _4392 _4393) = (term77 _4392 _4393).
Proof. exact (eq_refl (term92 _4392 _4393)). Qed.
Lemma lem219504 (_4392 : nat) (_4393 : nat) (h1 : term17) : term77 _4392 _4393.
Proof. exact (EQ_MP (@lem219503 _4392 _4393) (@lem219502 _4392 _4393 h1)). Qed.
Lemma lem219505 (_4394 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term51 m n _4394.
Proof. exact (@lem219479 m n h1 _4394). Qed.
Lemma lem219506 (m : nat) (_4394 : nat) (n : nat) : (term51 m n _4394) = (term52 m _4394 n).
Proof. exact (eq_refl (term51 m n _4394)). Qed.
Lemma lem219508 (_4395 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term55 m n _4395.
Proof. exact (@lem219492 m n h1 _4395). Qed.
Lemma lem219509 (m : nat) (_4395 : nat) (n : nat) : (term55 m n _4395) = (term56 m _4395 n).
Proof. exact (eq_refl (term55 m n _4395)). Qed.
Lemma lem219523 (_4392 : nat) (_4393 : nat) : (term77 _4392 _4393) = (term135 _4392 _4393).
Proof. exact (@lem218689 (term136 _4392 _4393) (term136 _4393 _4392) (_4392 = _4393)). Qed.
Lemma lem219524 (_4392 : nat) (_4393 : nat) (h1 : term17) : term135 _4392 _4393.
Proof. exact (EQ_MP (@lem219523 _4392 _4393) (@lem219504 _4392 _4393 h1)). Qed.
Lemma lem219526 (m : nat) (n : nat) (h1 : term10 m n) : term38 m n.
Proof. exact (proj2 (@lem219344 m n h1)). Qed.
Lemma lem219532 (_4394 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term52 m _4394 n.
Proof. exact (EQ_MP (@lem219506 m _4394 n) (@lem219505 _4394 m n h1)). Qed.
Lemma lem219538 (_4395 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term56 m _4395 n.
Proof. exact (EQ_MP (@lem219509 m _4395 n) (@lem219508 _4395 m n h1)). Qed.
Lemma lem219550 (_4390 : nat) (_4391 : nat) (h1 : term17) : term137 _4390 _4391.
Proof. exact (proj2 (@lem219498 _4390 _4391 h1)). Qed.
Lemma lem219573 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem219574 (m : nat) : m = m.
Proof. exact (@lem219573 m). Qed.
Lemma lem219575 (m : nat) : term138 m.
Proof. exact (fun h0 : term139 m => @lem219574 m). Qed.
Lemma lem219577 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219578 (m : nat) : (term138 m) = (m = m).
Proof. exact (@lem219577 (m = m)). Qed.
Lemma lem219579 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem219578 m) (@lem219575 m)). Qed.
Lemma lem219581 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem219582 (_4391 : nat) (_4390 : nat) : (term137 _4390 _4391) = (term142 _4391 _4390).
Proof. exact (@lem219581 (term38 _4390 _4391) (Peano.le _4391 _4390)). Qed.
Lemma lem219584 (a : Prop) : (term143 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem219585 (_4390 : nat) (_4391 : nat) : (term144 _4390 _4391) = (_4390 = _4391).
Proof. exact (@lem219584 (_4390 = _4391)). Qed.
Lemma lem219586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem219587 (_4390 : nat) (_4391 : nat) : (term145 _4390 _4391) = (term146 _4390 _4391).
Proof. exact (MK_COMB (@lem219586) (@lem219585 _4390 _4391)). Qed.
Lemma lem219588 (_4391 : nat) (_4390 : nat) : (Peano.le _4391 _4390) = (Peano.le _4391 _4390).
Proof. exact (eq_refl (Peano.le _4391 _4390)). Qed.
Lemma lem219589 (_4391 : nat) (_4390 : nat) : (term142 _4391 _4390) = (term147 _4391 _4390).
Proof. exact (MK_COMB (@lem219587 _4390 _4391) (@lem219588 _4391 _4390)). Qed.
Lemma lem219590 (_4391 : nat) (_4390 : nat) : (term137 _4390 _4391) = (term147 _4391 _4390).
Proof. exact (TRANS (@lem219582 _4391 _4390) (@lem219589 _4391 _4390)). Qed.
Lemma lem219593 (_4391 : nat) (_4390 : nat) (h1 : term17) : term147 _4391 _4390.
Proof. exact (EQ_MP (@lem219590 _4391 _4390) (@lem219550 _4390 _4391 h1)). Qed.
Lemma lem219594 (m : nat) (h1 : term17) : term148 m.
Proof. exact (@lem219593 m m h1). Qed.
Lemma lem219597 (m : nat) (h1 : term17) : Peano.le m m.
Proof. exact (@lem219594 m h1 (@lem219579 m)). Qed.
Lemma lem219598 (m : nat) (h1 : term17) : term149 m.
Proof. exact (fun h0 : term150 m => @lem219597 m h1). Qed.
Lemma lem219600 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219601 (m : nat) : (term149 m) = (Peano.le m m).
Proof. exact (@lem219600 (Peano.le m m)). Qed.
Lemma lem219602 (m : nat) (h1 : term17) : Peano.le m m.
Proof. exact (EQ_MP (@lem219601 m) (@lem219598 m h1)). Qed.
Lemma lem219608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem219609 (n : nat) (_4395 : nat) (m : nat) : (term56 m _4395 n) = (term52 n _4395 m).
Proof. exact (@lem219608 (Peano.le _4395 n) (term136 _4395 m)). Qed.
Lemma lem219615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem219616 (n : nat) (_4395 : nat) (m : nat) : (term151 m _4395 n) = (term152 n _4395 m).
Proof. exact (MK_COMB (@lem219615) (@lem219609 n _4395 m)). Qed.
Lemma lem219622 (n : nat) (_4395 : nat) (m : nat) : (term52 n _4395 m) = (term52 n _4395 m).
Proof. exact (eq_refl (term52 n _4395 m)). Qed.
Lemma lem219623 (n : nat) (_4395 : nat) (m : nat) : ((term56 m _4395 n) = (term52 n _4395 m)) = ((term52 n _4395 m) = (term52 n _4395 m)).
Proof. exact (MK_COMB (@lem219616 n _4395 m) (@lem219622 n _4395 m)). Qed.
Lemma lem219625 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem219626 (x : Prop) : (x = x) = True.
Proof. exact (@lem219625 Prop x). Qed.
Lemma lem219627 (n : nat) (_4395 : nat) (m : nat) : ((term52 n _4395 m) = (term52 n _4395 m)) = True.
Proof. exact (@lem219626 (term52 n _4395 m)). Qed.
Lemma lem219628 (n : nat) (_4395 : nat) (m : nat) : ((term56 m _4395 n) = (term52 n _4395 m)) = True.
Proof. exact (TRANS (@lem219623 n _4395 m) (@lem219627 n _4395 m)). Qed.
Lemma lem219629 (n : nat) (_4395 : nat) (m : nat) : True = ((term56 m _4395 n) = (term52 n _4395 m)).
Proof. exact (SYM (@lem219628 n _4395 m)). Qed.
Lemma lem219630 (n : nat) (_4395 : nat) (m : nat) : (term56 m _4395 n) = (term52 n _4395 m).
Proof. exact (EQ_MP (@lem219629 n _4395 m) (@lem0)). Qed.
Lemma lem219631 (_4395 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term52 n _4395 m.
Proof. exact (EQ_MP (@lem219630 n _4395 m) (@lem219538 _4395 m n h1)). Qed.
Lemma lem219633 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem219634 (m : nat) (_4395 : nat) (n : nat) : (term52 n _4395 m) = (term153 m _4395 n).
Proof. exact (@lem219633 (term136 _4395 m) (Peano.le _4395 n)). Qed.
Lemma lem219636 (a : Prop) : (term143 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem219637 (_4395 : nat) (m : nat) : (term154 _4395 m) = (Peano.le _4395 m).
Proof. exact (@lem219636 (Peano.le _4395 m)). Qed.
Lemma lem219638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem219639 (_4395 : nat) (m : nat) : (term155 _4395 m) = (term156 _4395 m).
Proof. exact (MK_COMB (@lem219638) (@lem219637 _4395 m)). Qed.
Lemma lem219640 (_4395 : nat) (n : nat) : (Peano.le _4395 n) = (Peano.le _4395 n).
Proof. exact (eq_refl (Peano.le _4395 n)). Qed.
Lemma lem219641 (m : nat) (_4395 : nat) (n : nat) : (term153 m _4395 n) = (term157 m _4395 n).
Proof. exact (MK_COMB (@lem219639 _4395 m) (@lem219640 _4395 n)). Qed.
Lemma lem219642 (m : nat) (_4395 : nat) (n : nat) : (term52 n _4395 m) = (term157 m _4395 n).
Proof. exact (TRANS (@lem219634 m _4395 n) (@lem219641 m _4395 n)). Qed.
Lemma lem219645 (_4395 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term157 m _4395 n.
Proof. exact (EQ_MP (@lem219642 m _4395 n) (@lem219631 _4395 m n h1)). Qed.
Lemma lem219646 (m : nat) (n : nat) (h1 : term10 m n) : term158 m n.
Proof. exact (@lem219645 m m n h1). Qed.
Lemma lem219649 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : Peano.le m n.
Proof. exact (@lem219646 m n h2 (@lem219602 m h1)). Qed.
Lemma lem219650 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : term159 m n.
Proof. exact (fun h0 : term136 m n => @lem219649 m n h1 h2). Qed.
Lemma lem219652 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219653 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem219652 (Peano.le m n)). Qed.
Lemma lem219654 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem219653 m n) (@lem219650 m n h1 h2)). Qed.
Lemma lem219656 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem219657 (n : nat) : n = n.
Proof. exact (@lem219656 n). Qed.
Lemma lem219658 (n : nat) : term138 n.
Proof. exact (fun h0 : term139 n => @lem219657 n). Qed.
Lemma lem219660 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219661 (n : nat) : (term138 n) = (n = n).
Proof. exact (@lem219660 (n = n)). Qed.
Lemma lem219662 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem219661 n) (@lem219658 n)). Qed.
Lemma lem219664 (_4391 : nat) (_4390 : nat) (h1 : term17) : term147 _4391 _4390.
Proof. exact (EQ_MP (@lem219590 _4391 _4390) (@lem219550 _4390 _4391 h1)). Qed.
Lemma lem219665 (n : nat) (h1 : term17) : term148 n.
Proof. exact (@lem219664 n n h1). Qed.
Lemma lem219668 (n : nat) (h1 : term17) : Peano.le n n.
Proof. exact (@lem219665 n h1 (@lem219662 n)). Qed.
Lemma lem219669 (n : nat) (h1 : term17) : term149 n.
Proof. exact (fun h0 : term150 n => @lem219668 n h1). Qed.
Lemma lem219671 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219672 (n : nat) : (term149 n) = (Peano.le n n).
Proof. exact (@lem219671 (Peano.le n n)). Qed.
Lemma lem219673 (n : nat) (h1 : term17) : Peano.le n n.
Proof. exact (EQ_MP (@lem219672 n) (@lem219669 n h1)). Qed.
Lemma lem219675 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem219676 (n : nat) (_4394 : nat) (m : nat) : (term52 m _4394 n) = (term153 n _4394 m).
Proof. exact (@lem219675 (term136 _4394 n) (Peano.le _4394 m)). Qed.
Lemma lem219678 (a : Prop) : (term143 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem219679 (_4394 : nat) (n : nat) : (term154 _4394 n) = (Peano.le _4394 n).
Proof. exact (@lem219678 (Peano.le _4394 n)). Qed.
Lemma lem219680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem219681 (_4394 : nat) (n : nat) : (term155 _4394 n) = (term156 _4394 n).
Proof. exact (MK_COMB (@lem219680) (@lem219679 _4394 n)). Qed.
Lemma lem219682 (_4394 : nat) (m : nat) : (Peano.le _4394 m) = (Peano.le _4394 m).
Proof. exact (eq_refl (Peano.le _4394 m)). Qed.
Lemma lem219683 (n : nat) (_4394 : nat) (m : nat) : (term153 n _4394 m) = (term157 n _4394 m).
Proof. exact (MK_COMB (@lem219681 _4394 n) (@lem219682 _4394 m)). Qed.
Lemma lem219684 (n : nat) (_4394 : nat) (m : nat) : (term52 m _4394 n) = (term157 n _4394 m).
Proof. exact (TRANS (@lem219676 n _4394 m) (@lem219683 n _4394 m)). Qed.
Lemma lem219687 (_4394 : nat) (m : nat) (n : nat) (h1 : term10 m n) : term157 n _4394 m.
Proof. exact (EQ_MP (@lem219684 n _4394 m) (@lem219532 _4394 m n h1)). Qed.
Lemma lem219688 (m : nat) (n : nat) (h1 : term10 m n) : term158 n m.
Proof. exact (@lem219687 n m n h1). Qed.
Lemma lem219691 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : Peano.le n m.
Proof. exact (@lem219688 m n h2 (@lem219673 n h1)). Qed.
Lemma lem219692 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : term159 n m.
Proof. exact (fun h0 : term136 n m => @lem219691 m n h1 h2). Qed.
Lemma lem219694 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219695 (n : nat) (m : nat) : (term159 n m) = (Peano.le n m).
Proof. exact (@lem219694 (Peano.le n m)). Qed.
Lemma lem219696 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : Peano.le n m.
Proof. exact (EQ_MP (@lem219695 n m) (@lem219692 m n h1 h2)). Qed.
Lemma lem219712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem219713 (_4393 : nat) (_4392 : nat) : (term160 _4392 _4393) = (term161 _4393 _4392).
Proof. exact (@lem219712 (_4392 = _4393) (term136 _4393 _4392)). Qed.
Lemma lem219721 (_4392 : nat) (_4393 : nat) : (term162 _4392 _4393) = (term162 _4392 _4393).
Proof. exact (eq_refl (term162 _4392 _4393)). Qed.
Lemma lem219722 (_4393 : nat) (_4392 : nat) : (term135 _4392 _4393) = (term163 _4393 _4392).
Proof. exact (MK_COMB (@lem219721 _4392 _4393) (@lem219713 _4393 _4392)). Qed.
Lemma lem219726 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem219727 (_4393 : nat) (_4392 : nat) : (term163 _4393 _4392) = (term164 _4393 _4392).
Proof. exact (@lem219726 (_4392 = _4393) (term136 _4392 _4393) (term136 _4393 _4392)). Qed.
Lemma lem219745 (_4393 : nat) (_4392 : nat) : (term135 _4392 _4393) = (term164 _4393 _4392).
Proof. exact (TRANS (@lem219722 _4393 _4392) (@lem219727 _4393 _4392)). Qed.
Lemma lem219746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem219747 (_4393 : nat) (_4392 : nat) : (term165 _4392 _4393) = (term166 _4393 _4392).
Proof. exact (MK_COMB (@lem219746) (@lem219745 _4393 _4392)). Qed.
Lemma lem219765 (_4393 : nat) (_4392 : nat) : (term164 _4393 _4392) = (term164 _4393 _4392).
Proof. exact (eq_refl (term164 _4393 _4392)). Qed.
Lemma lem219766 (_4393 : nat) (_4392 : nat) : ((term135 _4392 _4393) = (term164 _4393 _4392)) = ((term164 _4393 _4392) = (term164 _4393 _4392)).
Proof. exact (MK_COMB (@lem219747 _4393 _4392) (@lem219765 _4393 _4392)). Qed.
Lemma lem219768 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem219769 (x : Prop) : (x = x) = True.
Proof. exact (@lem219768 Prop x). Qed.
Lemma lem219770 (_4393 : nat) (_4392 : nat) : ((term164 _4393 _4392) = (term164 _4393 _4392)) = True.
Proof. exact (@lem219769 (term164 _4393 _4392)). Qed.
Lemma lem219771 (_4393 : nat) (_4392 : nat) : ((term135 _4392 _4393) = (term164 _4393 _4392)) = True.
Proof. exact (TRANS (@lem219766 _4393 _4392) (@lem219770 _4393 _4392)). Qed.
Lemma lem219772 (_4393 : nat) (_4392 : nat) : True = ((term135 _4392 _4393) = (term164 _4393 _4392)).
Proof. exact (SYM (@lem219771 _4393 _4392)). Qed.
Lemma lem219773 (_4393 : nat) (_4392 : nat) : (term135 _4392 _4393) = (term164 _4393 _4392).
Proof. exact (EQ_MP (@lem219772 _4393 _4392) (@lem0)). Qed.
Lemma lem219774 (_4393 : nat) (_4392 : nat) (h1 : term17) : term164 _4393 _4392.
Proof. exact (EQ_MP (@lem219773 _4393 _4392) (@lem219524 _4392 _4393 h1)). Qed.
Lemma lem219776 (b : Prop) (a : Prop) : (a \/ b) = (term141 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem219777 (_4392 : nat) (_4393 : nat) : (term164 _4393 _4392) = (term167 _4392 _4393).
Proof. exact (@lem219776 (term73 _4393 _4392) (_4392 = _4393)). Qed.
Lemma lem219779 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem219780 (_4393 : nat) (_4392 : nat) : (term170 _4393 _4392) = (term171 _4393 _4392).
Proof. exact (@lem219779 (term136 _4392 _4393) (term136 _4393 _4392)). Qed.
Lemma lem219782 (a : Prop) : (term143 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem219783 (_4392 : nat) (_4393 : nat) : (term154 _4392 _4393) = (Peano.le _4392 _4393).
Proof. exact (@lem219782 (Peano.le _4392 _4393)). Qed.
Lemma lem219784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem219785 (_4392 : nat) (_4393 : nat) : (term172 _4392 _4393) = (term173 _4392 _4393).
Proof. exact (MK_COMB (@lem219784) (@lem219783 _4392 _4393)). Qed.
Lemma lem219787 (a : Prop) : (term143 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem219788 (_4393 : nat) (_4392 : nat) : (term154 _4393 _4392) = (Peano.le _4393 _4392).
Proof. exact (@lem219787 (Peano.le _4393 _4392)). Qed.
Lemma lem219789 (_4393 : nat) (_4392 : nat) : (term171 _4393 _4392) = (term28 _4393 _4392).
Proof. exact (MK_COMB (@lem219785 _4392 _4393) (@lem219788 _4393 _4392)). Qed.
Lemma lem219790 (_4393 : nat) (_4392 : nat) : (term170 _4393 _4392) = (term28 _4393 _4392).
Proof. exact (TRANS (@lem219780 _4393 _4392) (@lem219789 _4393 _4392)). Qed.
Lemma lem219791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem219792 (_4393 : nat) (_4392 : nat) : (term174 _4393 _4392) = (term175 _4393 _4392).
Proof. exact (MK_COMB (@lem219791) (@lem219790 _4393 _4392)). Qed.
Lemma lem219793 (_4392 : nat) (_4393 : nat) : (_4392 = _4393) = (_4392 = _4393).
Proof. exact (eq_refl (_4392 = _4393)). Qed.
Lemma lem219794 (_4392 : nat) (_4393 : nat) : (term167 _4392 _4393) = (term176 _4392 _4393).
Proof. exact (MK_COMB (@lem219792 _4393 _4392) (@lem219793 _4392 _4393)). Qed.
Lemma lem219795 (_4392 : nat) (_4393 : nat) : (term164 _4393 _4392) = (term176 _4392 _4393).
Proof. exact (TRANS (@lem219777 _4392 _4393) (@lem219794 _4392 _4393)). Qed.
Lemma lem219797 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : term28 n m.
Proof. exact (conj (@lem219654 m n h1 h2) (@lem219696 m n h1 h2)). Qed.
Lemma lem219799 (_4392 : nat) (_4393 : nat) (h1 : term17) : term176 _4392 _4393.
Proof. exact (EQ_MP (@lem219795 _4392 _4393) (@lem219774 _4393 _4392 h1)). Qed.
Lemma lem219800 (m : nat) (n : nat) (h1 : term17) : term176 m n.
Proof. exact (@lem219799 m n h1). Qed.
Lemma lem219803 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : m = n.
Proof. exact (@lem219800 m n h1 (@lem219797 m n h1 h2)). Qed.
Lemma lem219804 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : term177 m n.
Proof. exact (fun h0 : term38 m n => @lem219803 m n h1 h2). Qed.
Lemma lem219806 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219807 (m : nat) (n : nat) : (term177 m n) = (m = n).
Proof. exact (@lem219806 (m = n)). Qed.
Lemma lem219808 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : m = n.
Proof. exact (EQ_MP (@lem219807 m n) (@lem219804 m n h1 h2)). Qed.
Lemma lem219811 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem219813 (m : nat) (n : nat) : (term38 m n) = (term178 m n).
Proof. exact (@lem219811 (m = n)). Qed.
Lemma lem219816 (m : nat) (n : nat) (h1 : term10 m n) : term178 m n.
Proof. exact (EQ_MP (@lem219813 m n) (@lem219526 m n h1)). Qed.
Lemma lem219819 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : False.
Proof. exact (@lem219816 m n h2 (@lem219808 m n h1 h2)). Qed.
Lemma lem219820 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : term179.
Proof. exact (fun h0 : ~ False => @lem219819 m n h1 h2). Qed.
Lemma lem219822 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem219823 : term179 = False.
Proof. exact (@lem219822 False). Qed.
Lemma lem219824 (m : nat) (n : nat) (h1 : term17) (h2 : term10 m n) : False.
Proof. exact (EQ_MP (@lem219823) (@lem219820 m n h1 h2)). Qed.
Lemma lem219825 (m : nat) (n : nat) (h1 : term10 m n) : term15.
Proof. exact (fun h0 : term17 => @lem219824 m n h0 h1). Qed.
Lemma lem219826 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem219827 (m : nat) (n : nat) (h1 : term10 m n) : term16.
Proof. exact (EQ_MP (@lem219826) (@lem219825 m n h1)). Qed.
Lemma lem219828 (m : nat) (n : nat) : term19 m n.
Proof. exact (fun h0 : term10 m n => @lem219827 m n h0). Qed.
Lemma lem219833 (n : nat) : term23 n.
Proof. exact (fun m : nat => @lem219828 m n). Qed.
Lemma lem219838 : term27.
Proof. exact (fun n : nat => @lem219833 n). Qed.
Lemma lem219839 : term26.
Proof. exact (EQ_MP (@lem218840) (@lem219838)). Qed.
Lemma lem219840 (n : nat) : term180 n.
Proof. exact (@lem219839 n). Qed.
Lemma lem219841 (n : nat) : (term180 n) = (term22 n).
Proof. exact (eq_refl (term180 n)). Qed.
Lemma lem219842 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem219841 n) (@lem219840 n)). Qed.
Lemma lem219843 (n : nat) (m : nat) : term181 n m.
Proof. exact (@lem219842 n m). Qed.
Lemma lem219844 (m : nat) (n : nat) : (term181 n m) = (term11 m n).
Proof. exact (eq_refl (term181 n m)). Qed.
Lemma lem219845 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem219844 m n) (@lem219843 n m)). Qed.
Lemma lem219847 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem218709 m n (@lem219845 m n)). Qed.
Lemma lem219848 (m : nat) (n : nat) (h1 : term10 m n) : term15.
Proof. exact (@lem219847 m n (@lem218694 m n h1)). Qed.
Lemma lem219849 (m : nat) (n : nat) (h1 : term10 m n) : False.
Proof. exact (@lem219848 m n h1 (@lem92426)). Qed.
Lemma lem219850 (m : nat) (n : nat) (h1 : term10 m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h2 : term10 m n => @lem219849 m n h1) (fun h2 : False => @lem218694 m n h1)). Qed.
Lemma lem219851 (m : nat) (n : nat) (h1 : term10 m n) : False.
Proof. exact (EQ_MP (@lem219850 m n h1) (@lem218694 m n h1)). Qed.
Lemma lem219852 (m : nat) (n : nat) : term9 m n.
Proof. exact (fun h0 : term10 m n => @lem219851 m n h0). Qed.
Lemma lem219853 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem218693 m n) (@lem219852 m n)). Qed.
Lemma lem219854 (m : nat) (n : nat) (h1 : term8 m n) : term8 m n.
Proof. exact (h1). Qed.
Lemma lem219855 (m : nat) (n : nat) (h1 : term33 m n) : term33 m n.
Proof. exact (h1). Qed.
Lemma lem219856 (m : nat) (n : nat) (h1 : term33 m n) (h2 : term8 m n) : m = n.
Proof. exact (@lem219854 m n h2 (@lem219855 m n h1)). Qed.
Lemma lem219857 (m : nat) (n : nat) (h1 : term33 m n) : term182 m n.
Proof. exact (fun h0 : term8 m n => @lem219856 m n h1 h0). Qed.
Lemma lem219858 (m : nat) (n : nat) (h1 : term8 m n) : term8 m n.
Proof. exact (h1). Qed.
Lemma lem219859 (m : nat) (n : nat) (h1 : term33 m n) (h2 : term8 m n) : m = n.
Proof. exact (@lem219857 m n h1 (@lem219858 m n h2)). Qed.
Lemma lem219860 (m : nat) (n : nat) (h1 : term8 m n) : term8 m n.
Proof. exact (fun h0 : term33 m n => @lem219859 m n h0 h1). Qed.
Lemma lem219861 (m : nat) (n : nat) : term183 m n.
Proof. exact (fun h0 : term8 m n => @lem219860 m n h0). Qed.
Lemma lem219877 (n : nat) : term184 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem219878 (n : nat) : (term184 n) = (term185 n).
Proof. exact (eq_refl (term184 n)). Qed.
Lemma lem219879 (n : nat) : term185 n.
Proof. exact (EQ_MP (@lem219878 n) (@lem219877 n)). Qed.
Lemma lem219881 (n : nat) (h1 : term186 n) : term186 n.
Proof. exact (h1). Qed.
Lemma lem219882 (p : nat) : term184 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem219883 (p : nat) : (term184 p) = (term185 p).
Proof. exact (eq_refl (term184 p)). Qed.
Lemma lem219884 (p : nat) : term185 p.
Proof. exact (EQ_MP (@lem219883 p) (@lem219882 p)). Qed.
Lemma lem219886 (p : nat) (h1 : term186 p) : term186 p.
Proof. exact (h1). Qed.
Lemma lem219887 (n : nat) : term187 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem219888 (n : nat) : (term187 n) = ((term188 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term187 n)). Qed.
Lemma lem219890 : term189.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem219916 : term190.
Proof. exact (proj1 (@lem219890)). Qed.
Lemma lem219917 (m : nat) : term191 m.
Proof. exact (@lem219916 m). Qed.
Lemma lem219918 (m : nat) : (term191 m) = ((term192 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term191 m)). Qed.
Lemma lem219927 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem219928 (m : nat) (n : nat) : (term193 m n) = (term193 m n).
Proof. exact (eq_refl (term193 m n)). Qed.
Lemma lem219929 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term194 m n p) = (term195 m n).
Proof. exact (MK_COMB (@lem219928 m n) (@lem219927 p h1)). Qed.
Lemma lem219931 (n : nat) : (term188 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem219888 n) (@lem219887 n)). Qed.
Lemma lem219932 (m : nat) (n : nat) : (term195 m n) = (NUMERAL 0).
Proof. exact (@lem219931 (Nat.div m n)). Qed.
Lemma lem219933 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term194 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem219929 m n p h1) (@lem219932 m n)). Qed.
Lemma lem219934 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem219935 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term196 m n p) = term197.
Proof. exact (MK_COMB (@lem219934) (@lem219933 m n p h1)). Qed.
Lemma lem219937 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem219938 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem219939 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (term192 n).
Proof. exact (MK_COMB (@lem219938 n) (@lem219937 p h1)). Qed.
Lemma lem219941 (m : nat) : (term192 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem219918 m) (@lem219917 m)). Qed.
Lemma lem219942 (n : nat) : (term192 n) = (NUMERAL 0).
Proof. exact (@lem219941 n). Qed.
Lemma lem219943 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem219939 n p h1) (@lem219942 n)). Qed.
Lemma lem219944 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem219945 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term198 m n p) = (term188 m).
Proof. exact (MK_COMB (@lem219944 m) (@lem219943 n p h1)). Qed.
Lemma lem219947 (n : nat) : (term188 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem219888 n) (@lem219887 n)). Qed.
Lemma lem219948 (m : nat) : (term188 m) = (NUMERAL 0).
Proof. exact (@lem219947 m). Qed.
Lemma lem219949 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term198 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem219945 n m p h1) (@lem219948 m)). Qed.
Lemma lem219950 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term194 m n p) = (term198 m n p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem219935 m n p h1) (@lem219949 m n p h1)). Qed.
Lemma lem219952 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem219953 (x : nat) : (x = x) = True.
Proof. exact (@lem219952 nat x). Qed.
Lemma lem219954 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem219953 (NUMERAL 0)). Qed.
Lemma lem219955 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term194 m n p) = (term198 m n p)) = True.
Proof. exact (TRANS (@lem219950 m n p h1) (@lem219954)). Qed.
Lemma lem219956 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = ((term194 m n p) = (term198 m n p)).
Proof. exact (SYM (@lem219955 m n p h1)). Qed.
Lemma lem219957 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term194 m n p) = (term198 m n p).
Proof. exact (EQ_MP (@lem219956 m n p h1) (@lem0)). Qed.
Lemma lem220012 (n : nat) : term187 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem220013 (n : nat) : (term187 n) = ((term188 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term187 n)). Qed.
Lemma lem220045 : term199.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem220046 (n : nat) : term200 n.
Proof. exact (@lem220045 n). Qed.
Lemma lem220047 (n : nat) : (term200 n) = ((term201 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term200 n)). Qed.
Lemma lem220049 (n : nat) : term202 n.
Proof. exact (@lem170051 n). Qed.
Lemma lem220050 (n : nat) : (term202 n) = ((term203 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term202 n)). Qed.
Lemma lem220068 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem220069 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem220070 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term188 m).
Proof. exact (MK_COMB (@lem220069 m) (@lem220068 n h1)). Qed.
Lemma lem220072 (n : nat) : (term188 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem220013 n) (@lem220012 n)). Qed.
Lemma lem220073 (m : nat) : (term188 m) = (NUMERAL 0).
Proof. exact (@lem220072 m). Qed.
Lemma lem220074 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem220070 m n h1) (@lem220073 m)). Qed.
Lemma lem220075 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem220076 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term193 m n) = term204.
Proof. exact (MK_COMB (@lem220075) (@lem220074 m n h1)). Qed.
Lemma lem220077 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem220078 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term194 m n p) = (term203 p).
Proof. exact (MK_COMB (@lem220076 m n h1) (@lem220077 p)). Qed.
Lemma lem220080 (n : nat) : (term203 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem220050 n) (@lem220049 n)). Qed.
Lemma lem220081 (p : nat) : (term203 p) = (NUMERAL 0).
Proof. exact (@lem220080 p). Qed.
Lemma lem220082 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term194 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem220078 m p n h1) (@lem220081 p)). Qed.
Lemma lem220083 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem220084 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term196 m n p) = term197.
Proof. exact (MK_COMB (@lem220083) (@lem220082 m p n h1)). Qed.
Lemma lem220086 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem220087 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem220088 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term205.
Proof. exact (MK_COMB (@lem220087) (@lem220086 n h1)). Qed.
Lemma lem220089 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem220090 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (term201 p).
Proof. exact (MK_COMB (@lem220088 n h1) (@lem220089 p)). Qed.
Lemma lem220092 (n : nat) : (term201 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem220047 n) (@lem220046 n)). Qed.
Lemma lem220093 (p : nat) : (term201 p) = (NUMERAL 0).
Proof. exact (@lem220092 p). Qed.
Lemma lem220094 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem220090 p n h1) (@lem220093 p)). Qed.
Lemma lem220095 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem220096 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term198 m n p) = (term188 m).
Proof. exact (MK_COMB (@lem220095 m) (@lem220094 p n h1)). Qed.
Lemma lem220098 (n : nat) : (term188 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem220013 n) (@lem220012 n)). Qed.
Lemma lem220099 (m : nat) : (term188 m) = (NUMERAL 0).
Proof. exact (@lem220098 m). Qed.
Lemma lem220100 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term198 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem220096 p m n h1) (@lem220099 m)). Qed.
Lemma lem220101 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term194 m n p) = (term198 m n p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem220084 m p n h1) (@lem220100 m p n h1)). Qed.
Lemma lem220103 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem220104 (x : nat) : (x = x) = True.
Proof. exact (@lem220103 nat x). Qed.
Lemma lem220105 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem220104 (NUMERAL 0)). Qed.
Lemma lem220106 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term194 m n p) = (term198 m n p)) = True.
Proof. exact (TRANS (@lem220101 m p n h1) (@lem220105)). Qed.
Lemma lem220107 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term194 m n p) = (term198 m n p)).
Proof. exact (SYM (@lem220106 m p n h1)). Qed.
Lemma lem220108 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term194 m n p) = (term198 m n p).
Proof. exact (EQ_MP (@lem220107 m p n h1) (@lem0)). Qed.
Lemma lem220184 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem219861 m n (@lem219853 m n)). Qed.
Lemma lem220185 (m : nat) (n : nat) (p : nat) : term206 m n p.
Proof. exact (@lem220184 (term194 m n p) (term198 m n p)). Qed.
Lemma lem220186 (m : nat) : term207 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem220187 (m : nat) : (term207 m) = (term208 m).
Proof. exact (eq_refl (term207 m)). Qed.
Lemma lem220188 (m : nat) : term208 m.
Proof. exact (EQ_MP (@lem220187 m) (@lem220186 m)). Qed.
Lemma lem220189 (m : nat) (n : nat) : term209 m n.
Proof. exact (@lem220188 m n). Qed.
Lemma lem220190 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (eq_refl (term209 m n)). Qed.
Lemma lem220191 (m : nat) (n : nat) : term210 m n.
Proof. exact (EQ_MP (@lem220190 m n) (@lem220189 m n)). Qed.
Lemma lem220192 (m : nat) (n : nat) (p : nat) : term211 m n p.
Proof. exact (@lem220191 m n p). Qed.
Lemma lem220193 (m : nat) (n : nat) (p : nat) : (term211 m n p) = ((term212 m n p) = (term213 m n p)).
Proof. exact (eq_refl (term211 m n p)). Qed.
Lemma lem220195 (m : nat) : term214 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem220196 (m : nat) : (term214 m) = (term215 m).
Proof. exact (eq_refl (term214 m)). Qed.
Lemma lem220197 (m : nat) : term215 m.
Proof. exact (EQ_MP (@lem220196 m) (@lem220195 m)). Qed.
Lemma lem220198 (m : nat) (n : nat) : term216 m n.
Proof. exact (@lem220197 m n). Qed.
Lemma lem220199 (m : nat) (n : nat) : (term216 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term217 m n)).
Proof. exact (eq_refl (term216 m n)). Qed.
Lemma lem220201 (a : nat) : term218 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem220202 (a : nat) : (term218 a) = (term219 a).
Proof. exact (eq_refl (term218 a)). Qed.
Lemma lem220203 (a : nat) : term219 a.
Proof. exact (EQ_MP (@lem220202 a) (@lem220201 a)). Qed.
Lemma lem220204 (a : nat) (b : nat) : term220 a b.
Proof. exact (@lem220203 a b). Qed.
Lemma lem220205 (a : nat) (b : nat) : (term220 a b) = (term221 a b).
Proof. exact (eq_refl (term220 a b)). Qed.
Lemma lem220206 (a : nat) (b : nat) : term221 a b.
Proof. exact (EQ_MP (@lem220205 a b) (@lem220204 a b)). Qed.
Lemma lem220207 (a : nat) (b : nat) (n : nat) : term222 a b n.
Proof. exact (@lem220206 a b n). Qed.
Lemma lem220208 (a : nat) (n : nat) (b : nat) : (term222 a b n) = (term223 a n b).
Proof. exact (eq_refl (term222 a b n)). Qed.
Lemma lem220209 (a : nat) (n : nat) (b : nat) : term223 a n b.
Proof. exact (EQ_MP (@lem220208 a n b) (@lem220207 a b n)). Qed.
Lemma lem220210 (a : nat) (h1 : term186 a) : term186 a.
Proof. exact (h1). Qed.
Lemma lem220211 (n : nat) (b : nat) (a : nat) (h1 : term186 a) : (term224 n b a) = (term225 a n b).
Proof. exact (@lem220209 a n b (@lem220210 a h1)). Qed.
Lemma lem220217 (p : nat) : term226 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem220230 (n : nat) : term226 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem220250 (a : nat) (n : nat) (b : nat) : term223 a n b.
Proof. exact (fun h0 : term186 a => @lem220211 n b a h0). Qed.
Lemma lem220251 (p : nat) (k : nat) (m : nat) (n : nat) : term227 p k m n.
Proof. exact (@lem220250 p k (Nat.div m n)). Qed.
Lemma lem220253 (p : nat) (h1 : term186 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem220217 p (@lem219886 p h1)). Qed.
Lemma lem220254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem220255 (p : nat) (h1 : term186 p) : (term186 p) = (~ False).
Proof. exact (MK_COMB (@lem220254) (@lem220253 p h1)). Qed.
Lemma lem220257 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem220258 (p : nat) (h1 : term186 p) : (term186 p) = True.
Proof. exact (TRANS (@lem220255 p h1) (@lem220257)). Qed.
Lemma lem220259 (p : nat) (h1 : term186 p) : True = (term186 p).
Proof. exact (SYM (@lem220258 p h1)). Qed.
Lemma lem220260 (p : nat) (h1 : term186 p) : term186 p.
Proof. exact (EQ_MP (@lem220259 p h1) (@lem0)). Qed.
Lemma lem220261 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 p) : (term228 k m n p) = (term229 p k m n).
Proof. exact (@lem220251 p k m n (@lem220260 p h1)). Qed.
Lemma lem220263 (a : nat) (n : nat) (b : nat) : term223 a n b.
Proof. exact (fun h0 : term186 a => @lem220211 n b a h0). Qed.
Lemma lem220264 (n : nat) (p : nat) (k : nat) (m : nat) : term230 n p k m.
Proof. exact (@lem220263 n (Nat.mul p k) m). Qed.
Lemma lem220266 (n : nat) (h1 : term186 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem220230 n (@lem219881 n h1)). Qed.
Lemma lem220267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem220268 (n : nat) (h1 : term186 n) : (term186 n) = (~ False).
Proof. exact (MK_COMB (@lem220267) (@lem220266 n h1)). Qed.
Lemma lem220270 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem220271 (n : nat) (h1 : term186 n) : (term186 n) = True.
Proof. exact (TRANS (@lem220268 n h1) (@lem220270)). Qed.
Lemma lem220272 (n : nat) (h1 : term186 n) : True = (term186 n).
Proof. exact (SYM (@lem220271 n h1)). Qed.
Lemma lem220273 (n : nat) (h1 : term186 n) : term186 n.
Proof. exact (EQ_MP (@lem220272 n h1) (@lem0)). Qed.
Lemma lem220274 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term186 n) : (term229 p k m n) = (term231 n p k m).
Proof. exact (@lem220264 n p k m (@lem220273 n h1)). Qed.
Lemma lem220276 (m : nat) (n : nat) (p : nat) : (term212 m n p) = (term213 m n p).
Proof. exact (EQ_MP (@lem220193 m n p) (@lem220192 m n p)). Qed.
Lemma lem220277 (n : nat) (p : nat) (k : nat) : (term212 n p k) = (term213 n p k).
Proof. exact (@lem220276 n p k). Qed.
Lemma lem220278 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem220279 (n : nat) (p : nat) (k : nat) : (term232 n p k) = (term233 n p k).
Proof. exact (MK_COMB (@lem220278) (@lem220277 n p k)). Qed.
Lemma lem220280 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem220281 (n : nat) (p : nat) (k : nat) (m : nat) : (term231 n p k m) = (term234 n p k m).
Proof. exact (MK_COMB (@lem220279 n p k) (@lem220280 m)). Qed.
Lemma lem220282 (p : nat) (k : nat) (m : nat) (n : nat) (h1 : term186 n) : (term229 p k m n) = (term234 n p k m).
Proof. exact (TRANS (@lem220274 p k m n h1) (@lem220281 n p k m)). Qed.
Lemma lem220283 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term228 k m n p) = (term234 n p k m).
Proof. exact (TRANS (@lem220261 k m n p h2) (@lem220282 p k m n h1)). Qed.
Lemma lem220284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem220285 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term235 k m n p) = (term236 n p k m).
Proof. exact (MK_COMB (@lem220284) (@lem220283 k m n p h1 h2)). Qed.
Lemma lem220287 (a : nat) (n : nat) (b : nat) : term223 a n b.
Proof. exact (fun h0 : term186 a => @lem220211 n b a h0). Qed.
Lemma lem220288 (n : nat) (p : nat) (k : nat) (m : nat) : term237 n p k m.
Proof. exact (@lem220287 (Nat.mul n p) k m). Qed.
Lemma lem220290 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term217 m n).
Proof. exact (EQ_MP (@lem220199 m n) (@lem220198 m n)). Qed.
Lemma lem220291 (n : nat) (p : nat) : ((Nat.mul n p) = (NUMERAL 0)) = (term217 n p).
Proof. exact (@lem220290 n p). Qed.
Lemma lem220295 (n : nat) (h1 : term186 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem220230 n (@lem219881 n h1)). Qed.
Lemma lem220296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem220297 (n : nat) (h1 : term186 n) : (term238 n) = (or False).
Proof. exact (MK_COMB (@lem220296) (@lem220295 n h1)). Qed.
Lemma lem220299 (p : nat) (h1 : term186 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem220217 p (@lem219886 p h1)). Qed.
Lemma lem220300 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term217 n p) = (False \/ False).
Proof. exact (MK_COMB (@lem220297 n h1) (@lem220299 p h2)). Qed.
Lemma lem220302 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem220303 : (False \/ False) = False.
Proof. exact (@lem220302 False). Qed.
Lemma lem220304 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term217 n p) = False.
Proof. exact (TRANS (@lem220300 n p h1 h2) (@lem220303)). Qed.
Lemma lem220305 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : ((Nat.mul n p) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem220291 n p) (@lem220304 n p h1 h2)). Qed.
Lemma lem220306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem220307 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term239 n p) = (~ False).
Proof. exact (MK_COMB (@lem220306) (@lem220305 n p h1 h2)). Qed.
Lemma lem220309 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem220310 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term239 n p) = True.
Proof. exact (TRANS (@lem220307 n p h1 h2) (@lem220309)). Qed.
Lemma lem220311 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : True = (term239 n p).
Proof. exact (SYM (@lem220310 n p h1 h2)). Qed.
Lemma lem220312 (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : term239 n p.
Proof. exact (EQ_MP (@lem220311 n p h1 h2) (@lem0)). Qed.
Lemma lem220313 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term240 k m n p) = (term234 n p k m).
Proof. exact (@lem220288 n p k m (@lem220312 n p h1 h2)). Qed.
Lemma lem220314 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : ((term228 k m n p) = (term240 k m n p)) = ((term234 n p k m) = (term234 n p k m)).
Proof. exact (MK_COMB (@lem220285 k m n p h1 h2) (@lem220313 k m n p h1 h2)). Qed.
Lemma lem220316 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem220317 (x : Prop) : (x = x) = True.
Proof. exact (@lem220316 Prop x). Qed.
Lemma lem220318 (n : nat) (p : nat) (k : nat) (m : nat) : ((term234 n p k m) = (term234 n p k m)) = True.
Proof. exact (@lem220317 (term234 n p k m)). Qed.
Lemma lem220319 (k : nat) (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : ((term228 k m n p) = (term240 k m n p)) = True.
Proof. exact (TRANS (@lem220314 k m n p h1 h2) (@lem220318 n p k m)). Qed.
Lemma lem220320 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term241 m n p) = term242.
Proof. exact (fun_ext (fun k : nat => @lem220319 k m n p h1 h2)). Qed.
Lemma lem220321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem220322 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term243 m n p) = term244.
Proof. exact (MK_COMB (@lem220321) (@lem220320 m n p h1 h2)). Qed.
Lemma lem220324 {A : Type'} (t : Prop) : (term245 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem220325 (t : Prop) : (term246 t) = t.
Proof. exact (@lem220324 nat t). Qed.
Lemma lem220326 : term244 = True.
Proof. exact (@lem220325 True). Qed.
Lemma lem220327 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term243 m n p) = True.
Proof. exact (TRANS (@lem220322 m n p h1 h2) (@lem220326)). Qed.
Lemma lem220328 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : True = (term243 m n p).
Proof. exact (SYM (@lem220327 m n p h1 h2)). Qed.
Lemma lem220329 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : term243 m n p.
Proof. exact (EQ_MP (@lem220328 m n p h1 h2) (@lem0)). Qed.
Lemma lem220332 (m : nat) (n : nat) (p : nat) (h1 : term186 n) (h2 : term186 p) : (term194 m n p) = (term198 m n p).
Proof. exact (@lem220185 m n p (@lem220329 m n p h1 h2)). Qed.
Lemma lem220334 (m : nat) (n : nat) (p : nat) (h1 : term186 p) : (term194 m n p) = (term198 m n p).
Proof. exact (or_elim (@lem219879 n) (fun h0 : n = (NUMERAL 0) => @lem220108 m p n h0) (fun h0 : term186 n => @lem220332 m n p h0 h1)). Qed.
Lemma lem220335 (m : nat) (n : nat) (p : nat) : (term194 m n p) = (term198 m n p).
Proof. exact (or_elim (@lem219884 p) (fun h0 : p = (NUMERAL 0) => @lem219957 m n p h0) (fun h0 : term186 p => @lem220334 m n p h0)). Qed.
Lemma lem220340 (m : nat) (n : nat) : term247 m n.
Proof. exact (fun p : nat => @lem220335 m n p). Qed.
Lemma lem220345 (m : nat) : term248 m.
Proof. exact (fun n : nat => @lem220340 m n). Qed.
Lemma lem220350 : term249.
Proof. exact (fun m : nat => @lem220345 m). Qed.
