Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_EQ_REFL_term_abbrevs.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1267931 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1267932 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1267933 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1267932 n) (@lem1267931 n)). Qed.
Lemma lem1267934 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1267936 (n : nat) : term2 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1267937 (n : nat) : (term2 n) = ((term3 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1267939 (x : nadd) : term4 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1267940 (x : nadd) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1267941 (x : nadd) : term5 x.
Proof. exact (EQ_MP (@lem1267940 x) (@lem1267939 x)). Qed.
Lemma lem1267942 (x : nadd) (y : nadd) : term6 x y.
Proof. exact (@lem1267941 x y). Qed.
Lemma lem1267943 (x : nadd) (y : nadd) : (term6 x y) = ((nadd_eq x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1267946 (x : nadd) (y : nadd) : (nadd_eq x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1267943 x y) (@lem1267942 x y)). Qed.
Lemma lem1267947 (x : nadd) : (nadd_eq x x) = (term8 x).
Proof. exact (@lem1267946 x x). Qed.
Lemma lem1267957 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1267937 n) (@lem1267936 n)). Qed.
Lemma lem1267958 (x : nadd) (n : nat) : (term9 x n) = (NUMERAL 0).
Proof. exact (@lem1267957 (dest_nadd x n)). Qed.
Lemma lem1267959 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1267960 (x : nadd) (n : nat) : (term10 x n) = term11.
Proof. exact (MK_COMB (@lem1267959) (@lem1267958 x n)). Qed.
Lemma lem1267961 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1267962 (x : nadd) (n : nat) (B : nat) : (term12 x n B) = (term1 B).
Proof. exact (MK_COMB (@lem1267960 x n) (@lem1267961 B)). Qed.
Lemma lem1267964 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1267934 n) (@lem1267933 n)). Qed.
Lemma lem1267965 (B : nat) : (term1 B) = True.
Proof. exact (@lem1267964 B). Qed.
Lemma lem1267966 (x : nadd) (n : nat) (B : nat) : (term12 x n B) = True.
Proof. exact (TRANS (@lem1267962 x n B) (@lem1267965 B)). Qed.
Lemma lem1267967 (x : nadd) (B : nat) : (term13 x B) = term14.
Proof. exact (fun_ext (fun n : nat => @lem1267966 x n B)). Qed.
Lemma lem1267968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1267969 (x : nadd) (B : nat) : (term15 x B) = term16.
Proof. exact (MK_COMB (@lem1267968) (@lem1267967 x B)). Qed.
Lemma lem1267971 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1267972 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1267971 nat t). Qed.
Lemma lem1267973 : term16 = True.
Proof. exact (@lem1267972 True). Qed.
Lemma lem1267974 (x : nadd) (B : nat) : (term15 x B) = True.
Proof. exact (TRANS (@lem1267969 x B) (@lem1267973)). Qed.
Lemma lem1267975 (x : nadd) : (term19 x) = term14.
Proof. exact (fun_ext (fun B : nat => @lem1267974 x B)). Qed.
Lemma lem1267976 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1267977 (x : nadd) : (term8 x) = term20.
Proof. exact (MK_COMB (@lem1267976) (@lem1267975 x)). Qed.
Lemma lem1267979 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1267980 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1267979 nat t). Qed.
Lemma lem1267981 : term20 = True.
Proof. exact (@lem1267980 True). Qed.
Lemma lem1267982 (x : nadd) : (term8 x) = True.
Proof. exact (TRANS (@lem1267977 x) (@lem1267981)). Qed.
Lemma lem1267983 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (TRANS (@lem1267947 x) (@lem1267982 x)). Qed.
Lemma lem1267984 (x : nadd) : True = (nadd_eq x x).
Proof. exact (SYM (@lem1267983 x)). Qed.
Lemma lem1267985 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1267984 x) (@lem0)). Qed.
Lemma lem1267990 : term23.
Proof. exact (fun x : nadd => @lem1267985 x). Qed.
