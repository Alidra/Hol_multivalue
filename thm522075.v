Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522075_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm521107_spec.
Require Import thm521108_spec.
Require Import thm521115_spec.
Require Import thm521116_spec.
Require Import thm521123_spec.
Require Import thm521124_spec.
Lemma lem521932 (n : nat) : (Peano.le 0 n) = True.
Proof. exact (EQ_MP (@lem521108 n) (@lem521107 n)). Qed.
Lemma lem521933 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem521934 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem521933 n) (@lem521932 n)). Qed.
Lemma lem521936 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem521937 (n : nat) : (term2 n) = (Peano.le n 0).
Proof. exact (@lem521936 (Peano.le n 0)). Qed.
Lemma lem521938 (n : nat) : (term1 n) = (Peano.le n 0).
Proof. exact (TRANS (@lem521934 n) (@lem521937 n)). Qed.
Lemma lem521939 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem521940 (n : nat) : ((Peano.le n 0) = (term1 n)) = ((Peano.le n 0) = (Peano.le n 0)).
Proof. exact (MK_COMB (@lem521939 n) (@lem521938 n)). Qed.
Lemma lem521942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521943 (x : Prop) : (x = x) = True.
Proof. exact (@lem521942 Prop x). Qed.
Lemma lem521944 (n : nat) : ((Peano.le n 0) = (Peano.le n 0)) = True.
Proof. exact (@lem521943 (Peano.le n 0)). Qed.
Lemma lem521945 (n : nat) : ((Peano.le n 0) = (term1 n)) = True.
Proof. exact (TRANS (@lem521940 n) (@lem521944 n)). Qed.
Lemma lem521946 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem521945 n)). Qed.
Lemma lem521947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521948 : term6 = term7.
Proof. exact (MK_COMB (@lem521947) (@lem521946)). Qed.
Lemma lem521950 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521951 (t : Prop) : (term9 t) = t.
Proof. exact (@lem521950 nat t). Qed.
Lemma lem521952 : term7 = True.
Proof. exact (@lem521951 True). Qed.
Lemma lem521953 : term6 = True.
Proof. exact (TRANS (@lem521948) (@lem521952)). Qed.
Lemma lem521954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521955 : term10 = (and True).
Proof. exact (MK_COMB (@lem521954) (@lem521953)). Qed.
Lemma lem521967 (n : nat) : (Peano.le 0 n) = True.
Proof. exact (EQ_MP (@lem521108 n) (@lem521107 n)). Qed.
Lemma lem521968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521969 (n : nat) : (term11 n) = (and True).
Proof. exact (MK_COMB (@lem521968) (@lem521967 n)). Qed.
Lemma lem521970 (n : nat) : (Peano.le n 0) = (Peano.le n 0).
Proof. exact (eq_refl (Peano.le n 0)). Qed.
Lemma lem521971 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem521969 n) (@lem521970 n)). Qed.
Lemma lem521973 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem521974 (n : nat) : (term13 n) = (Peano.le n 0).
Proof. exact (@lem521973 (Peano.le n 0)). Qed.
Lemma lem521975 (n : nat) : (term12 n) = (Peano.le n 0).
Proof. exact (TRANS (@lem521971 n) (@lem521974 n)). Qed.
Lemma lem521976 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem521977 (n : nat) : ((Peano.le n 0) = (term12 n)) = ((Peano.le n 0) = (Peano.le n 0)).
Proof. exact (MK_COMB (@lem521976 n) (@lem521975 n)). Qed.
Lemma lem521979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem521980 (x : Prop) : (x = x) = True.
Proof. exact (@lem521979 Prop x). Qed.
Lemma lem521981 (n : nat) : ((Peano.le n 0) = (Peano.le n 0)) = True.
Proof. exact (@lem521980 (Peano.le n 0)). Qed.
Lemma lem521982 (n : nat) : ((Peano.le n 0) = (term12 n)) = True.
Proof. exact (TRANS (@lem521977 n) (@lem521981 n)). Qed.
Lemma lem521983 : term14 = term5.
Proof. exact (fun_ext (fun n : nat => @lem521982 n)). Qed.
Lemma lem521984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem521985 : term15 = term7.
Proof. exact (MK_COMB (@lem521984) (@lem521983)). Qed.
Lemma lem521987 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem521988 (t : Prop) : (term9 t) = t.
Proof. exact (@lem521987 nat t). Qed.
Lemma lem521989 : term7 = True.
Proof. exact (@lem521988 True). Qed.
Lemma lem521990 : term15 = True.
Proof. exact (TRANS (@lem521985) (@lem521989)). Qed.
Lemma lem521991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem521992 : term16 = (and True).
Proof. exact (MK_COMB (@lem521991) (@lem521990)). Qed.
Lemma lem522004 (n : nat) (m : nat) : (term17 n m) = False.
Proof. exact (@lem521124 n m (@lem521123 n m)). Qed.
Lemma lem522005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem522006 (n : nat) (m : nat) : (term18 n m) = (~ False).
Proof. exact (MK_COMB (@lem522005) (@lem522004 n m)). Qed.
Lemma lem522008 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem522009 (n : nat) (m : nat) : (term18 n m) = True.
Proof. exact (TRANS (@lem522006 n m) (@lem522008)). Qed.
Lemma lem522010 (m : nat) : (term19 m) = term5.
Proof. exact (fun_ext (fun n : nat => @lem522009 n m)). Qed.
Lemma lem522011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522012 (m : nat) : (term20 m) = term7.
Proof. exact (MK_COMB (@lem522011) (@lem522010 m)). Qed.
Lemma lem522014 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522015 (t : Prop) : (term9 t) = t.
Proof. exact (@lem522014 nat t). Qed.
Lemma lem522016 : term7 = True.
Proof. exact (@lem522015 True). Qed.
Lemma lem522017 (m : nat) : (term20 m) = True.
Proof. exact (TRANS (@lem522012 m) (@lem522016)). Qed.
Lemma lem522018 : term21 = term5.
Proof. exact (fun_ext (fun m : nat => @lem522017 m)). Qed.
Lemma lem522019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522020 : term22 = term7.
Proof. exact (MK_COMB (@lem522019) (@lem522018)). Qed.
Lemma lem522022 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522023 (t : Prop) : (term9 t) = t.
Proof. exact (@lem522022 nat t). Qed.
Lemma lem522024 : term7 = True.
Proof. exact (@lem522023 True). Qed.
Lemma lem522025 : term22 = True.
Proof. exact (TRANS (@lem522020) (@lem522024)). Qed.
Lemma lem522026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522027 : term23 = (and True).
Proof. exact (MK_COMB (@lem522026) (@lem522025)). Qed.
Lemma lem522037 (n : nat) (m : nat) : (term24 n m) = False.
Proof. exact (@lem521116 n m (@lem521115 n m)). Qed.
Lemma lem522038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem522039 (n : nat) (m : nat) : (term25 n m) = (~ False).
Proof. exact (MK_COMB (@lem522038) (@lem522037 n m)). Qed.
Lemma lem522041 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem522042 (n : nat) (m : nat) : (term25 n m) = True.
Proof. exact (TRANS (@lem522039 n m) (@lem522041)). Qed.
Lemma lem522043 (m : nat) : (term26 m) = term5.
Proof. exact (fun_ext (fun n : nat => @lem522042 n m)). Qed.
Lemma lem522044 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522045 (m : nat) : (term27 m) = term7.
Proof. exact (MK_COMB (@lem522044) (@lem522043 m)). Qed.
Lemma lem522047 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522048 (t : Prop) : (term9 t) = t.
Proof. exact (@lem522047 nat t). Qed.
Lemma lem522049 : term7 = True.
Proof. exact (@lem522048 True). Qed.
Lemma lem522050 (m : nat) : (term27 m) = True.
Proof. exact (TRANS (@lem522045 m) (@lem522049)). Qed.
Lemma lem522051 : term28 = term5.
Proof. exact (fun_ext (fun m : nat => @lem522050 m)). Qed.
Lemma lem522052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522053 : term29 = term7.
Proof. exact (MK_COMB (@lem522052) (@lem522051)). Qed.
Lemma lem522055 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522056 (t : Prop) : (term9 t) = t.
Proof. exact (@lem522055 nat t). Qed.
Lemma lem522057 : term7 = True.
Proof. exact (@lem522056 True). Qed.
Lemma lem522058 : term29 = True.
Proof. exact (TRANS (@lem522053) (@lem522057)). Qed.
Lemma lem522059 : term30 = (True /\ True).
Proof. exact (MK_COMB (@lem522027) (@lem522058)). Qed.
Lemma lem522061 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522062 : (True /\ True) = True.
Proof. exact (@lem522061 True). Qed.
Lemma lem522063 : term30 = True.
Proof. exact (TRANS (@lem522059) (@lem522062)). Qed.
Lemma lem522064 : term31 = (True /\ True).
Proof. exact (MK_COMB (@lem521992) (@lem522063)). Qed.
Lemma lem522066 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522067 : (True /\ True) = True.
Proof. exact (@lem522066 True). Qed.
Lemma lem522068 : term31 = True.
Proof. exact (TRANS (@lem522064) (@lem522067)). Qed.
Lemma lem522069 : term32 = (True /\ True).
Proof. exact (MK_COMB (@lem521955) (@lem522068)). Qed.
Lemma lem522071 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522072 : (True /\ True) = True.
Proof. exact (@lem522071 True). Qed.
Lemma lem522073 : term32 = True.
Proof. exact (TRANS (@lem522069) (@lem522072)). Qed.
Lemma lem522074 : True = term32.
Proof. exact (SYM (@lem522073)). Qed.
Lemma lem522075 : term32.
Proof. exact (EQ_MP (@lem522074) (@lem0)). Qed.
