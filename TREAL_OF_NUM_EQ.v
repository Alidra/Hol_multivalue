Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_OF_NUM_EQ_term_abbrevs.
Require Import HREAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm1318825_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_of_num_spec.
Lemma lem1326852 (n : hreal) : term0 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1326853 (n : hreal) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1326855 (m : nat) : term2 m.
Proof. exact (@lem1318825 m). Qed.
Lemma lem1326856 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1326857 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1326856 m) (@lem1326855 m)). Qed.
Lemma lem1326858 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1326857 m n). Qed.
Lemma lem1326859 (m : nat) (n : nat) : (term4 m n) = (((hreal_of_num m) = (hreal_of_num n)) = (m = n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1326861 (x1 : hreal) : term5 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1326862 (x1 : hreal) : (term5 x1) = (term6 x1).
Proof. exact (eq_refl (term5 x1)). Qed.
Lemma lem1326863 (x1 : hreal) : term6 x1.
Proof. exact (EQ_MP (@lem1326862 x1) (@lem1326861 x1)). Qed.
Lemma lem1326864 (x1 : hreal) (y2 : hreal) : term7 x1 y2.
Proof. exact (@lem1326863 x1 y2). Qed.
Lemma lem1326865 (x1 : hreal) (y2 : hreal) : (term7 x1 y2) = (term8 x1 y2).
Proof. exact (eq_refl (term7 x1 y2)). Qed.
Lemma lem1326866 (x1 : hreal) (y2 : hreal) : term8 x1 y2.
Proof. exact (EQ_MP (@lem1326865 x1 y2) (@lem1326864 x1 y2)). Qed.
Lemma lem1326867 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term9 x1 y2 x2.
Proof. exact (@lem1326866 x1 y2 x2). Qed.
Lemma lem1326868 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term9 x1 y2 x2) = (term10 x1 y2 x2).
Proof. exact (eq_refl (term9 x1 y2 x2)). Qed.
Lemma lem1326869 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term10 x1 y2 x2.
Proof. exact (EQ_MP (@lem1326868 x1 y2 x2) (@lem1326867 x1 y2 x2)). Qed.
Lemma lem1326870 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term11 x1 y2 x2 y1.
Proof. exact (@lem1326869 x1 y2 x2 y1). Qed.
Lemma lem1326871 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term11 x1 y2 x2 y1) = ((term12 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term11 x1 y2 x2 y1)). Qed.
Lemma lem1326873 (n : nat) : term13 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1326874 (n : nat) : (term13 n) = ((treal_of_num n) = (term14 n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem1326887 (n : nat) : (treal_of_num n) = (term14 n).
Proof. exact (EQ_MP (@lem1326874 n) (@lem1326873 n)). Qed.
Lemma lem1326888 (m : nat) : (treal_of_num m) = (term14 m).
Proof. exact (@lem1326887 m). Qed.
Lemma lem1326889 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1326890 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem1326889) (@lem1326888 m)). Qed.
Lemma lem1326892 (n : nat) : (treal_of_num n) = (term14 n).
Proof. exact (EQ_MP (@lem1326874 n) (@lem1326873 n)). Qed.
Lemma lem1326893 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem1326890 m) (@lem1326892 n)). Qed.
Lemma lem1326895 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term12 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326871 x1 y2 x2 y1) (@lem1326870 x1 y2 x2 y1)). Qed.
Lemma lem1326896 (m : nat) (n : nat) : (term18 m n) = ((term19 m) = (term19 n)).
Proof. exact (@lem1326895 (hreal_of_num m) term20 (hreal_of_num n) term20). Qed.
Lemma lem1326900 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1326853 n) (@lem1326852 n)). Qed.
Lemma lem1326901 (m : nat) : (term19 m) = (hreal_of_num m).
Proof. exact (@lem1326900 (hreal_of_num m)). Qed.
Lemma lem1326902 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1326903 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem1326902) (@lem1326901 m)). Qed.
Lemma lem1326905 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1326853 n) (@lem1326852 n)). Qed.
Lemma lem1326906 (n : nat) : (term19 n) = (hreal_of_num n).
Proof. exact (@lem1326905 (hreal_of_num n)). Qed.
Lemma lem1326907 (m : nat) (n : nat) : ((term19 m) = (term19 n)) = ((hreal_of_num m) = (hreal_of_num n)).
Proof. exact (MK_COMB (@lem1326903 m) (@lem1326906 n)). Qed.
Lemma lem1326909 (m : nat) (n : nat) : ((hreal_of_num m) = (hreal_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1326859 m n) (@lem1326858 m n)). Qed.
Lemma lem1326912 (m : nat) (n : nat) : ((term19 m) = (term19 n)) = (m = n).
Proof. exact (TRANS (@lem1326907 m n) (@lem1326909 m n)). Qed.
Lemma lem1326913 (m : nat) (n : nat) : (term18 m n) = (m = n).
Proof. exact (TRANS (@lem1326896 m n) (@lem1326912 m n)). Qed.
Lemma lem1326914 (m : nat) (n : nat) : (term17 m n) = (m = n).
Proof. exact (TRANS (@lem1326893 m n) (@lem1326913 m n)). Qed.
Lemma lem1326915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326916 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem1326915) (@lem1326914 m n)). Qed.
Lemma lem1326919 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1326920 (m : nat) (n : nat) : ((term17 m n) = (m = n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem1326916 m n) (@lem1326919 m n)). Qed.
Lemma lem1326922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1326923 (x : Prop) : (x = x) = True.
Proof. exact (@lem1326922 Prop x). Qed.
Lemma lem1326924 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem1326923 (m = n)). Qed.
Lemma lem1326925 (m : nat) (n : nat) : ((term17 m n) = (m = n)) = True.
Proof. exact (TRANS (@lem1326920 m n) (@lem1326924 m n)). Qed.
Lemma lem1326926 (m : nat) : (term25 m) = term26.
Proof. exact (fun_ext (fun n : nat => @lem1326925 m n)). Qed.
Lemma lem1326927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1326928 (m : nat) : (term27 m) = term28.
Proof. exact (MK_COMB (@lem1326927) (@lem1326926 m)). Qed.
Lemma lem1326930 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326931 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1326930 nat t). Qed.
Lemma lem1326932 : term28 = True.
Proof. exact (@lem1326931 True). Qed.
Lemma lem1326933 (m : nat) : (term27 m) = True.
Proof. exact (TRANS (@lem1326928 m) (@lem1326932)). Qed.
Lemma lem1326934 : term31 = term26.
Proof. exact (fun_ext (fun m : nat => @lem1326933 m)). Qed.
Lemma lem1326935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1326936 : term32 = term28.
Proof. exact (MK_COMB (@lem1326935) (@lem1326934)). Qed.
Lemma lem1326938 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326939 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1326938 nat t). Qed.
Lemma lem1326940 : term28 = True.
Proof. exact (@lem1326939 True). Qed.
Lemma lem1326941 : term32 = True.
Proof. exact (TRANS (@lem1326936) (@lem1326940)). Qed.
Lemma lem1326942 : True = term32.
Proof. exact (SYM (@lem1326941)). Qed.
Lemma lem1326943 : term32.
Proof. exact (EQ_MP (@lem1326942) (@lem0)). Qed.
