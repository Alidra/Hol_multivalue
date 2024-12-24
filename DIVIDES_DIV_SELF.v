Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_DIV_SELF_term_abbrevs.
Require Import INT_DIVIDES_DIV_SELF_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3112883 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3112884 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3112883 m n h1)). Qed.
Lemma lem3112885 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3112886 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3112885 m n h1)). Qed.
Lemma lem3112887 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3112884 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3112886 m n h1)). Qed.
Lemma lem3112888 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3112887 m n)). Qed.
Lemma lem3112889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112890 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3112889) (@lem3112888 m)). Qed.
Lemma lem3112891 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3112890 m)). Qed.
Lemma lem3112892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112893 : term8 = term9.
Proof. exact (MK_COMB (@lem3112892) (@lem3112891)). Qed.
Lemma lem3112894 : term9.
Proof. exact (EQ_MP (@lem3112893) (@lem2538105)). Qed.
Lemma lem3112895 (n : int) : term10 n.
Proof. exact (@lem2730195 n). Qed.
Lemma lem3112896 (n : int) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem3112897 (n : int) : term11 n.
Proof. exact (EQ_MP (@lem3112896 n) (@lem3112895 n)). Qed.
Lemma lem3112898 (n : int) (d : int) : term12 n d.
Proof. exact (@lem3112897 n d). Qed.
Lemma lem3112899 (d : int) (n : int) : (term12 n d) = (term13 d n).
Proof. exact (eq_refl (term12 n d)). Qed.
Lemma lem3112900 (d : int) (n : int) : term13 d n.
Proof. exact (EQ_MP (@lem3112899 d n) (@lem3112898 n d)). Qed.
Lemma lem3112901 (d : int) (n : int) : (term13 d n) = ((term13 d n) = True).
Proof. exact (@lem7 (term13 d n)). Qed.
Lemma lem3112903 (m : nat) : term14 m.
Proof. exact (@lem3112894 m). Qed.
Lemma lem3112904 (m : nat) : (term14 m) = (term5 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem3112905 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem3112904 m) (@lem3112903 m)). Qed.
Lemma lem3112906 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem3112905 m n). Qed.
Lemma lem3112907 (m : nat) (n : nat) : (term15 m n) = ((term1 m n) = (term0 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem3112909 (a : nat) : term16 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3112910 (a : nat) : (term16 a) = (term17 a).
Proof. exact (eq_refl (term16 a)). Qed.
Lemma lem3112911 (a : nat) : term17 a.
Proof. exact (EQ_MP (@lem3112910 a) (@lem3112909 a)). Qed.
Lemma lem3112912 (a : nat) (b : nat) : term18 a b.
Proof. exact (@lem3112911 a b). Qed.
Lemma lem3112913 (a : nat) (b : nat) : (term18 a b) = ((num_divides a b) = (term19 a b)).
Proof. exact (eq_refl (term18 a b)). Qed.
Lemma lem3112926 (a : nat) (b : nat) : (num_divides a b) = (term19 a b).
Proof. exact (EQ_MP (@lem3112913 a b) (@lem3112912 a b)). Qed.
Lemma lem3112927 (d : nat) (n : nat) : (num_divides d n) = (term19 d n).
Proof. exact (@lem3112926 d n). Qed.
Lemma lem3112928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3112929 (d : nat) (n : nat) : (term20 d n) = (term21 d n).
Proof. exact (MK_COMB (@lem3112928) (@lem3112927 d n)). Qed.
Lemma lem3112931 (a : nat) (b : nat) : (num_divides a b) = (term19 a b).
Proof. exact (EQ_MP (@lem3112913 a b) (@lem3112912 a b)). Qed.
Lemma lem3112932 (d : nat) (n : nat) : (term22 d n) = (term23 d n).
Proof. exact (@lem3112931 (Nat.div n d) n). Qed.
Lemma lem3112934 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem3112907 m n) (@lem3112906 m n)). Qed.
Lemma lem3112935 (n : nat) (d : nat) : (term1 n d) = (term0 n d).
Proof. exact (@lem3112934 n d). Qed.
Lemma lem3112936 : int_divides = int_divides.
Proof. exact (eq_refl int_divides). Qed.
Lemma lem3112937 (n : nat) (d : nat) : (term24 n d) = (term25 n d).
Proof. exact (MK_COMB (@lem3112936) (@lem3112935 n d)). Qed.
Lemma lem3112938 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem3112939 (d : nat) (n : nat) : (term23 d n) = (term26 d n).
Proof. exact (MK_COMB (@lem3112937 n d) (@lem3112938 n)). Qed.
Lemma lem3112940 (d : nat) (n : nat) : (term22 d n) = (term26 d n).
Proof. exact (TRANS (@lem3112932 d n) (@lem3112939 d n)). Qed.
Lemma lem3112941 (d : nat) (n : nat) : (term27 d n) = (term28 d n).
Proof. exact (MK_COMB (@lem3112929 d n) (@lem3112940 d n)). Qed.
Lemma lem3112943 (d : int) (n : int) : (term13 d n) = True.
Proof. exact (EQ_MP (@lem3112901 d n) (@lem3112900 d n)). Qed.
Lemma lem3112944 (d : nat) (n : nat) : (term28 d n) = True.
Proof. exact (@lem3112943 (int_of_num d) (int_of_num n)). Qed.
Lemma lem3112945 (d : nat) (n : nat) : (term27 d n) = True.
Proof. exact (TRANS (@lem3112941 d n) (@lem3112944 d n)). Qed.
Lemma lem3112946 (n : nat) : (term29 n) = term30.
Proof. exact (fun_ext (fun d : nat => @lem3112945 d n)). Qed.
Lemma lem3112947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112948 (n : nat) : (term31 n) = term32.
Proof. exact (MK_COMB (@lem3112947) (@lem3112946 n)). Qed.
Lemma lem3112950 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112951 (t : Prop) : (term34 t) = t.
Proof. exact (@lem3112950 nat t). Qed.
Lemma lem3112952 : term32 = True.
Proof. exact (@lem3112951 True). Qed.
Lemma lem3112953 (n : nat) : (term31 n) = True.
Proof. exact (TRANS (@lem3112948 n) (@lem3112952)). Qed.
Lemma lem3112954 : term35 = term30.
Proof. exact (fun_ext (fun n : nat => @lem3112953 n)). Qed.
Lemma lem3112955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112956 : term36 = term32.
Proof. exact (MK_COMB (@lem3112955) (@lem3112954)). Qed.
Lemma lem3112958 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112959 (t : Prop) : (term34 t) = t.
Proof. exact (@lem3112958 nat t). Qed.
Lemma lem3112960 : term32 = True.
Proof. exact (@lem3112959 True). Qed.
Lemma lem3112961 : term36 = True.
Proof. exact (TRANS (@lem3112956) (@lem3112960)). Qed.
Lemma lem3112962 : True = term36.
Proof. exact (SYM (@lem3112961)). Qed.
Lemma lem3112963 : term36.
Proof. exact (EQ_MP (@lem3112962) (@lem0)). Qed.
