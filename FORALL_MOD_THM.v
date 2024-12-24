Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_MOD_THM_term_abbrevs.
Require Import FORALL_LT_MOD_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem241862 (P : nat -> Prop) : term0 P.
Proof. exact (@lem241861 P). Qed.
Lemma lem241863 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem241864 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem241863 P) (@lem241862 P)). Qed.
Lemma lem241865 (P : nat -> Prop) (n : nat) : term2 P n.
Proof. exact (@lem241864 P n). Qed.
Lemma lem241866 (P : nat -> Prop) (n : nat) : (term2 P n) = ((term3 n P) = (term4 P n)).
Proof. exact (eq_refl (term2 P n)). Qed.
Lemma lem241879 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term5 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem241880 (p : Prop) (q : Prop) (p' : Prop) : term6 p q p'.
Proof. exact (fun q' : Prop => @lem241879 p q p' q'). Qed.
Lemma lem241881 (p : Prop) (q : Prop) : term7 p q.
Proof. exact (fun p' : Prop => @lem241880 p q p'). Qed.
Lemma lem241882 (n : nat) (P : nat -> Prop) : term8 n P.
Proof. exact (@lem241881 (term9 n) ((term10 P n) = (term3 n P))). Qed.
Lemma lem241883 (n : nat) (P : nat -> Prop) (p' : Prop) : term11 n P p'.
Proof. exact (@lem241882 n P p'). Qed.
Lemma lem241884 (n : nat) (P : nat -> Prop) (p' : Prop) : (term11 n P p') = (term12 n P p').
Proof. exact (eq_refl (term11 n P p')). Qed.
Lemma lem241885 (n : nat) (P : nat -> Prop) (p' : Prop) : term12 n P p'.
Proof. exact (EQ_MP (@lem241884 n P p') (@lem241883 n P p')). Qed.
Lemma lem241886 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term13 n P p' q'.
Proof. exact (@lem241885 n P p' q'). Qed.
Lemma lem241887 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term13 n P p' q') = (term14 n P p' q').
Proof. exact (eq_refl (term13 n P p' q')). Qed.
Lemma lem241888 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term14 n P p' q'.
Proof. exact (EQ_MP (@lem241887 n P p' q') (@lem241886 n P p' q')). Qed.
Lemma lem241891 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem241892 (P : nat -> Prop) (n : nat) (q' : Prop) : term15 P n q'.
Proof. exact (@lem241888 n P (term9 n) q'). Qed.
Lemma lem241893 (P : nat -> Prop) (n : nat) (q' : Prop) : term16 P n q'.
Proof. exact (@lem241892 P n q' (@lem241891 n)). Qed.
Lemma lem241894 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem241895 (n : nat) : term17 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem241915 (P : nat -> Prop) (n : nat) : (term3 n P) = (term4 P n).
Proof. exact (EQ_MP (@lem241866 P n) (@lem241865 P n)). Qed.
Lemma lem241919 (n : nat) (h1 : term9 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem241895 n (@lem241894 n h1)). Qed.
Lemma lem241920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem241921 (n : nat) (h1 : term9 n) : (term18 n) = (or False).
Proof. exact (MK_COMB (@lem241920) (@lem241919 n h1)). Qed.
Lemma lem241926 (P : nat -> Prop) (n : nat) : (term10 P n) = (term10 P n).
Proof. exact (eq_refl (term10 P n)). Qed.
Lemma lem241927 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term4 P n) = (term19 P n).
Proof. exact (MK_COMB (@lem241921 n h1) (@lem241926 P n)). Qed.
Lemma lem241929 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem241930 (P : nat -> Prop) (n : nat) : (term19 P n) = (term10 P n).
Proof. exact (@lem241929 (term10 P n)). Qed.
Lemma lem241935 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term4 P n) = (term10 P n).
Proof. exact (TRANS (@lem241927 P n h1) (@lem241930 P n)). Qed.
Lemma lem241936 (P : nat -> Prop) (n : nat) (h1 : term9 n) : (term3 n P) = (term10 P n).
Proof. exact (TRANS (@lem241915 P n) (@lem241935 P n h1)). Qed.
Lemma lem241937 (P : nat -> Prop) (n : nat) : (term20 P n) = (term20 P n).
Proof. exact (eq_refl (term20 P n)). Qed.
Lemma lem241938 (P : nat -> Prop) (n : nat) (h1 : term9 n) : ((term10 P n) = (term3 n P)) = ((term10 P n) = (term10 P n)).
Proof. exact (MK_COMB (@lem241937 P n) (@lem241936 P n h1)). Qed.
Lemma lem241940 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem241941 (x : Prop) : (x = x) = True.
Proof. exact (@lem241940 Prop x). Qed.
Lemma lem241942 (P : nat -> Prop) (n : nat) : ((term10 P n) = (term10 P n)) = True.
Proof. exact (@lem241941 (term10 P n)). Qed.
Lemma lem241943 (P : nat -> Prop) (n : nat) (h1 : term9 n) : ((term10 P n) = (term3 n P)) = True.
Proof. exact (TRANS (@lem241938 P n h1) (@lem241942 P n)). Qed.
Lemma lem241944 (n : nat) (P : nat -> Prop) : term21 n P.
Proof. exact (fun h0 : term9 n => @lem241943 P n h0). Qed.
Lemma lem241945 (P : nat -> Prop) (n : nat) : term22 P n.
Proof. exact (@lem241893 P n True). Qed.
Lemma lem241946 (P : nat -> Prop) (n : nat) : (term23 n P) = (term24 n).
Proof. exact (@lem241945 P n (@lem241944 n P)). Qed.
Lemma lem241948 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem241949 (n : nat) : (term24 n) = True.
Proof. exact (@lem241948 (term9 n)). Qed.
Lemma lem241950 (n : nat) (P : nat -> Prop) : (term23 n P) = True.
Proof. exact (TRANS (@lem241946 P n) (@lem241949 n)). Qed.
Lemma lem241951 (P : nat -> Prop) : (term25 P) = term26.
Proof. exact (fun_ext (fun n : nat => @lem241950 n P)). Qed.
Lemma lem241952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem241953 (P : nat -> Prop) : (term27 P) = term28.
Proof. exact (MK_COMB (@lem241952) (@lem241951 P)). Qed.
Lemma lem241955 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem241956 (t : Prop) : (term30 t) = t.
Proof. exact (@lem241955 nat t). Qed.
Lemma lem241957 : term28 = True.
Proof. exact (@lem241956 True). Qed.
Lemma lem241958 (P : nat -> Prop) : (term27 P) = True.
Proof. exact (TRANS (@lem241953 P) (@lem241957)). Qed.
Lemma lem241959 : term31 = term32.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem241958 P)). Qed.
Lemma lem241960 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem241961 : term33 = term34.
Proof. exact (MK_COMB (@lem241960) (@lem241959)). Qed.
Lemma lem241963 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem241964 (t : Prop) : (term35 t) = t.
Proof. exact (@lem241963 (nat -> Prop) t). Qed.
Lemma lem241965 : term34 = True.
Proof. exact (@lem241964 True). Qed.
Lemma lem241966 : term33 = True.
Proof. exact (TRANS (@lem241961) (@lem241965)). Qed.
Lemma lem241967 : True = term33.
Proof. exact (SYM (@lem241966)). Qed.
Lemma lem241968 : term33.
Proof. exact (EQ_MP (@lem241967) (@lem0)). Qed.
