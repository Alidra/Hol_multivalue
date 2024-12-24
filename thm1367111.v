Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367111_term_abbrevs.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367021 (x : real) : term0 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1367022 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367024 (x : real) : term3 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1367025 (x : real) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1367032 (x : real) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem1367025 x) (@lem1367024 x)). Qed.
Lemma lem1367033 (x : nat) : (term5 x) = term2.
Proof. exact (@lem1367032 (real_of_num x)). Qed.
Lemma lem1367034 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367035 (x : nat) : (term6 x) = term7.
Proof. exact (MK_COMB (@lem1367034) (@lem1367033 x)). Qed.
Lemma lem1367036 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367037 (x : nat) : ((term5 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367035 x) (@lem1367036)). Qed.
Lemma lem1367039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367040 (x : real) : (x = x) = True.
Proof. exact (@lem1367039 real x). Qed.
Lemma lem1367041 : (term2 = term2) = True.
Proof. exact (@lem1367040 term2). Qed.
Lemma lem1367042 (x : nat) : ((term5 x) = term2) = True.
Proof. exact (TRANS (@lem1367037 x) (@lem1367041)). Qed.
Lemma lem1367043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367044 (x : nat) : (term8 x) = (and True).
Proof. exact (MK_COMB (@lem1367043) (@lem1367042 x)). Qed.
Lemma lem1367050 (x : real) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem1367025 x) (@lem1367024 x)). Qed.
Lemma lem1367051 (x : nat) : (term9 x) = term2.
Proof. exact (@lem1367050 (term10 x)). Qed.
Lemma lem1367052 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367053 (x : nat) : (term11 x) = term7.
Proof. exact (MK_COMB (@lem1367052) (@lem1367051 x)). Qed.
Lemma lem1367054 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367055 (x : nat) : ((term9 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367053 x) (@lem1367054)). Qed.
Lemma lem1367057 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367058 (x : real) : (x = x) = True.
Proof. exact (@lem1367057 real x). Qed.
Lemma lem1367059 : (term2 = term2) = True.
Proof. exact (@lem1367058 term2). Qed.
Lemma lem1367060 (x : nat) : ((term9 x) = term2) = True.
Proof. exact (TRANS (@lem1367055 x) (@lem1367059)). Qed.
Lemma lem1367061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367062 (x : nat) : (term12 x) = (and True).
Proof. exact (MK_COMB (@lem1367061) (@lem1367060 x)). Qed.
Lemma lem1367068 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1367022 x) (@lem1367021 x)). Qed.
Lemma lem1367069 (x : nat) : (term13 x) = term2.
Proof. exact (@lem1367068 (real_of_num x)). Qed.
Lemma lem1367070 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367071 (x : nat) : (term14 x) = term7.
Proof. exact (MK_COMB (@lem1367070) (@lem1367069 x)). Qed.
Lemma lem1367072 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367073 (x : nat) : ((term13 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367071 x) (@lem1367072)). Qed.
Lemma lem1367075 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367076 (x : real) : (x = x) = True.
Proof. exact (@lem1367075 real x). Qed.
Lemma lem1367077 : (term2 = term2) = True.
Proof. exact (@lem1367076 term2). Qed.
Lemma lem1367078 (x : nat) : ((term13 x) = term2) = True.
Proof. exact (TRANS (@lem1367073 x) (@lem1367077)). Qed.
Lemma lem1367079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367080 (x : nat) : (term15 x) = (and True).
Proof. exact (MK_COMB (@lem1367079) (@lem1367078 x)). Qed.
Lemma lem1367084 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1367022 x) (@lem1367021 x)). Qed.
Lemma lem1367085 (x : nat) : (term16 x) = term2.
Proof. exact (@lem1367084 (term10 x)). Qed.
Lemma lem1367086 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367087 (x : nat) : (term17 x) = term7.
Proof. exact (MK_COMB (@lem1367086) (@lem1367085 x)). Qed.
Lemma lem1367088 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367089 (x : nat) : ((term16 x) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367087 x) (@lem1367088)). Qed.
Lemma lem1367091 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367092 (x : real) : (x = x) = True.
Proof. exact (@lem1367091 real x). Qed.
Lemma lem1367093 : (term2 = term2) = True.
Proof. exact (@lem1367092 term2). Qed.
Lemma lem1367094 (x : nat) : ((term16 x) = term2) = True.
Proof. exact (TRANS (@lem1367089 x) (@lem1367093)). Qed.
Lemma lem1367095 (x : nat) : (term18 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1367080 x) (@lem1367094 x)). Qed.
Lemma lem1367097 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367098 : (True /\ True) = True.
Proof. exact (@lem1367097 True). Qed.
Lemma lem1367099 (x : nat) : (term18 x) = True.
Proof. exact (TRANS (@lem1367095 x) (@lem1367098)). Qed.
Lemma lem1367100 (x : nat) : (term19 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1367062 x) (@lem1367099 x)). Qed.
Lemma lem1367102 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367103 : (True /\ True) = True.
Proof. exact (@lem1367102 True). Qed.
Lemma lem1367104 (x : nat) : (term19 x) = True.
Proof. exact (TRANS (@lem1367100 x) (@lem1367103)). Qed.
Lemma lem1367105 (x : nat) : (term20 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1367044 x) (@lem1367104 x)). Qed.
Lemma lem1367107 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367108 : (True /\ True) = True.
Proof. exact (@lem1367107 True). Qed.
Lemma lem1367109 (x : nat) : (term20 x) = True.
Proof. exact (TRANS (@lem1367105 x) (@lem1367108)). Qed.
Lemma lem1367110 (x : nat) : True = (term20 x).
Proof. exact (SYM (@lem1367109 x)). Qed.
Lemma lem1367111 (x : nat) : term20 x.
Proof. exact (EQ_MP (@lem1367110 x) (@lem0)). Qed.
