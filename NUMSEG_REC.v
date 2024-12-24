Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_REC_term_abbrevs.
Require Import NUMSEG_RREC_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5371012 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (term0 m n) = (dotdot m n).
Proof. exact (h1). Qed.
Lemma lem5371013 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (dotdot m n) = (term0 m n).
Proof. exact (SYM (@lem5371012 m n h1)). Qed.
Lemma lem5371014 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (dotdot m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem5371015 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (term0 m n) = (dotdot m n).
Proof. exact (SYM (@lem5371014 m n h1)). Qed.
Lemma lem5371016 (m : nat) (n : nat) : ((term0 m n) = (dotdot m n)) = ((dotdot m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (dotdot m n) => @lem5371013 m n h1) (fun h1 : (dotdot m n) = (term0 m n) => @lem5371015 m n h1)). Qed.
Lemma lem5371017 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem5371018 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem5371017 m n) (@lem5371016 m n)). Qed.
Lemma lem5371019 (m : nat) : (term4 m) = (term5 m).
Proof. exact (fun_ext (fun n : nat => @lem5371018 m n)). Qed.
Lemma lem5371020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371021 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem5371020) (@lem5371019 m)). Qed.
Lemma lem5371022 : term8 = term9.
Proof. exact (fun_ext (fun m : nat => @lem5371021 m)). Qed.
Lemma lem5371023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371024 : term10 = term11.
Proof. exact (MK_COMB (@lem5371023) (@lem5371022)). Qed.
Lemma lem5371025 : term11.
Proof. exact (EQ_MP (@lem5371024) (@lem5371007)). Qed.
Lemma lem5371026 (n : nat) : term12 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem5371027 (n : nat) : (term12 n) = ((term13 n) = n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem5371029 (m : nat) : term14 m.
Proof. exact (@lem5371025 m). Qed.
Lemma lem5371030 (m : nat) : (term14 m) = (term7 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem5371031 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem5371030 m) (@lem5371029 m)). Qed.
Lemma lem5371032 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem5371031 m n). Qed.
Lemma lem5371033 (m : nat) (n : nat) : (term15 m n) = (term3 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem5371034 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5371033 m n) (@lem5371032 m n)). Qed.
Lemma lem5371035 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem5371036 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term0 m n).
Proof. exact (@lem5371034 m n (@lem5371035 m n h1)). Qed.
Lemma lem5371053 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5371054 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem5371053 p q p' q'). Qed.
Lemma lem5371055 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem5371054 p q p'). Qed.
Lemma lem5371056 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem5371055 (term20 m n) ((term21 m n) = (term22 m n))). Qed.
Lemma lem5371057 (m : nat) (n : nat) (p' : Prop) : term23 m n p'.
Proof. exact (@lem5371056 m n p'). Qed.
Lemma lem5371058 (m : nat) (n : nat) (p' : Prop) : (term23 m n p') = (term24 m n p').
Proof. exact (eq_refl (term23 m n p')). Qed.
Lemma lem5371059 (m : nat) (n : nat) (p' : Prop) : term24 m n p'.
Proof. exact (EQ_MP (@lem5371058 m n p') (@lem5371057 m n p')). Qed.
Lemma lem5371060 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term25 m n p' q'.
Proof. exact (@lem5371059 m n p' q'). Qed.
Lemma lem5371061 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term25 m n p' q') = (term26 m n p' q').
Proof. exact (eq_refl (term25 m n p' q')). Qed.
Lemma lem5371062 (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term26 m n p' q'.
Proof. exact (EQ_MP (@lem5371061 m n p' q') (@lem5371060 m n p' q')). Qed.
Lemma lem5371063 (m : nat) (n : nat) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem5371064 (m : nat) (n : nat) (q' : Prop) : term27 m n q'.
Proof. exact (@lem5371062 m n (term20 m n) q'). Qed.
Lemma lem5371065 (m : nat) (n : nat) (q' : Prop) : term28 m n q'.
Proof. exact (@lem5371064 m n q' (@lem5371063 m n)). Qed.
Lemma lem5371066 (m : nat) (n : nat) (h1 : term20 m n) : term20 m n.
Proof. exact (h1). Qed.
Lemma lem5371067 (m : nat) (n : nat) : (term20 m n) = ((term20 m n) = True).
Proof. exact (@lem7 (term20 m n)). Qed.
Lemma lem5371072 (m : nat) (n : nat) : term3 m n.
Proof. exact (fun h0 : Peano.le m n => @lem5371036 m n h0). Qed.
Lemma lem5371073 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem5371072 m (S n)). Qed.
Lemma lem5371075 (m : nat) (n : nat) (h1 : term20 m n) : (term20 m n) = True.
Proof. exact (EQ_MP (@lem5371067 m n) (@lem5371066 m n h1)). Qed.
Lemma lem5371076 (m : nat) (n : nat) (h1 : term20 m n) : True = (term20 m n).
Proof. exact (SYM (@lem5371075 m n h1)). Qed.
Lemma lem5371077 (m : nat) (n : nat) (h1 : term20 m n) : term20 m n.
Proof. exact (EQ_MP (@lem5371076 m n h1) (@lem0)). Qed.
Lemma lem5371078 (m : nat) (n : nat) (h1 : term20 m n) : (term21 m n) = (term30 m n).
Proof. exact (@lem5371073 m n (@lem5371077 m n h1)). Qed.
Lemma lem5371088 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem5371027 n) (@lem5371026 n)). Qed.
Lemma lem5371089 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem5371090 (m : nat) (n : nat) : (term31 m n) = (dotdot m n).
Proof. exact (MK_COMB (@lem5371089 m) (@lem5371088 n)). Qed.
Lemma lem5371095 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem5371096 (m : nat) (n : nat) : (term30 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem5371095 n) (@lem5371090 m n)). Qed.
Lemma lem5371101 (m : nat) (n : nat) (h1 : term20 m n) : (term21 m n) = (term22 m n).
Proof. exact (TRANS (@lem5371078 m n h1) (@lem5371096 m n)). Qed.
Lemma lem5371102 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem5371103 (m : nat) (n : nat) (h1 : term20 m n) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem5371102) (@lem5371101 m n h1)). Qed.
Lemma lem5371112 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem5371113 (m : nat) (n : nat) (h1 : term20 m n) : ((term21 m n) = (term22 m n)) = ((term22 m n) = (term22 m n)).
Proof. exact (MK_COMB (@lem5371103 m n h1) (@lem5371112 m n)). Qed.
Lemma lem5371115 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5371116 (x : nat -> Prop) : (x = x) = True.
Proof. exact (@lem5371115 (nat -> Prop) x). Qed.
Lemma lem5371117 (m : nat) (n : nat) : ((term22 m n) = (term22 m n)) = True.
Proof. exact (@lem5371116 (term22 m n)). Qed.
Lemma lem5371118 (m : nat) (n : nat) (h1 : term20 m n) : ((term21 m n) = (term22 m n)) = True.
Proof. exact (TRANS (@lem5371113 m n h1) (@lem5371117 m n)). Qed.
Lemma lem5371119 (m : nat) (n : nat) : term35 m n.
Proof. exact (fun h0 : term20 m n => @lem5371118 m n h0). Qed.
Lemma lem5371120 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem5371065 m n True). Qed.
Lemma lem5371121 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (@lem5371120 m n (@lem5371119 m n)). Qed.
Lemma lem5371123 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5371124 (m : nat) (n : nat) : (term38 m n) = True.
Proof. exact (@lem5371123 (term20 m n)). Qed.
Lemma lem5371125 (m : nat) (n : nat) : (term37 m n) = True.
Proof. exact (TRANS (@lem5371121 m n) (@lem5371124 m n)). Qed.
Lemma lem5371126 (m : nat) : (term39 m) = term40.
Proof. exact (fun_ext (fun n : nat => @lem5371125 m n)). Qed.
Lemma lem5371127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371128 (m : nat) : (term41 m) = term42.
Proof. exact (MK_COMB (@lem5371127) (@lem5371126 m)). Qed.
Lemma lem5371130 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371131 (t : Prop) : (term44 t) = t.
Proof. exact (@lem5371130 nat t). Qed.
Lemma lem5371132 : term42 = True.
Proof. exact (@lem5371131 True). Qed.
Lemma lem5371133 (m : nat) : (term41 m) = True.
Proof. exact (TRANS (@lem5371128 m) (@lem5371132)). Qed.
Lemma lem5371134 : term45 = term40.
Proof. exact (fun_ext (fun m : nat => @lem5371133 m)). Qed.
Lemma lem5371135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371136 : term46 = term42.
Proof. exact (MK_COMB (@lem5371135) (@lem5371134)). Qed.
Lemma lem5371138 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371139 (t : Prop) : (term44 t) = t.
Proof. exact (@lem5371138 nat t). Qed.
Lemma lem5371140 : term42 = True.
Proof. exact (@lem5371139 True). Qed.
Lemma lem5371141 : term46 = True.
Proof. exact (TRANS (@lem5371136) (@lem5371140)). Qed.
Lemma lem5371142 : True = term46.
Proof. exact (SYM (@lem5371141)). Qed.
Lemma lem5371143 : term46.
Proof. exact (EQ_MP (@lem5371142) (@lem0)). Qed.
