Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIVIDES_ABS_term_abbrevs.
Require Import INT_DIVIDES_LABS_spec.
Require Import INT_DIVIDES_RABS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2806008 (d : int) : term0 d.
Proof. exact (@lem2806007 d). Qed.
Lemma lem2806009 (d : int) : (term0 d) = (term1 d).
Proof. exact (eq_refl (term0 d)). Qed.
Lemma lem2806010 (d : int) : term1 d.
Proof. exact (EQ_MP (@lem2806009 d) (@lem2806008 d)). Qed.
Lemma lem2806011 (d : int) (n : int) : term2 d n.
Proof. exact (@lem2806010 d n). Qed.
Lemma lem2806012 (d : int) (n : int) : (term2 d n) = ((term3 d n) = (int_divides d n)).
Proof. exact (eq_refl (term2 d n)). Qed.
Lemma lem2806014 (d : int) : term4 d.
Proof. exact (@lem2804399 d). Qed.
Lemma lem2806015 (d : int) : (term4 d) = (term5 d).
Proof. exact (eq_refl (term4 d)). Qed.
Lemma lem2806016 (d : int) : term5 d.
Proof. exact (EQ_MP (@lem2806015 d) (@lem2806014 d)). Qed.
Lemma lem2806017 (d : int) (n : int) : term6 d n.
Proof. exact (@lem2806016 d n). Qed.
Lemma lem2806018 (d : int) (n : int) : (term6 d n) = ((term7 d n) = (int_divides d n)).
Proof. exact (eq_refl (term6 d n)). Qed.
Lemma lem2806033 (d : int) (n : int) : (term7 d n) = (int_divides d n).
Proof. exact (EQ_MP (@lem2806018 d n) (@lem2806017 d n)). Qed.
Lemma lem2806034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2806035 (d : int) (n : int) : (term8 d n) = (term9 d n).
Proof. exact (MK_COMB (@lem2806034) (@lem2806033 d n)). Qed.
Lemma lem2806036 (d : int) (n : int) : (int_divides d n) = (int_divides d n).
Proof. exact (eq_refl (int_divides d n)). Qed.
Lemma lem2806037 (d : int) (n : int) : ((term7 d n) = (int_divides d n)) = ((int_divides d n) = (int_divides d n)).
Proof. exact (MK_COMB (@lem2806035 d n) (@lem2806036 d n)). Qed.
Lemma lem2806039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2806040 (x : Prop) : (x = x) = True.
Proof. exact (@lem2806039 Prop x). Qed.
Lemma lem2806041 (d : int) (n : int) : ((int_divides d n) = (int_divides d n)) = True.
Proof. exact (@lem2806040 (int_divides d n)). Qed.
Lemma lem2806042 (d : int) (n : int) : ((term7 d n) = (int_divides d n)) = True.
Proof. exact (TRANS (@lem2806037 d n) (@lem2806041 d n)). Qed.
Lemma lem2806043 (d : int) : (term10 d) = term11.
Proof. exact (fun_ext (fun n : int => @lem2806042 d n)). Qed.
Lemma lem2806044 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2806045 (d : int) : (term5 d) = term12.
Proof. exact (MK_COMB (@lem2806044) (@lem2806043 d)). Qed.
Lemma lem2806047 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2806048 (t : Prop) : (term14 t) = t.
Proof. exact (@lem2806047 int t). Qed.
Lemma lem2806049 : term12 = True.
Proof. exact (@lem2806048 True). Qed.
Lemma lem2806050 (d : int) : (term5 d) = True.
Proof. exact (TRANS (@lem2806045 d) (@lem2806049)). Qed.
Lemma lem2806051 : term15 = term11.
Proof. exact (fun_ext (fun d : int => @lem2806050 d)). Qed.
Lemma lem2806052 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2806053 : term16 = term12.
Proof. exact (MK_COMB (@lem2806052) (@lem2806051)). Qed.
Lemma lem2806055 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2806056 (t : Prop) : (term14 t) = t.
Proof. exact (@lem2806055 int t). Qed.
Lemma lem2806057 : term12 = True.
Proof. exact (@lem2806056 True). Qed.
Lemma lem2806058 : term16 = True.
Proof. exact (TRANS (@lem2806053) (@lem2806057)). Qed.
Lemma lem2806059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2806060 : term17 = (and True).
Proof. exact (MK_COMB (@lem2806059) (@lem2806058)). Qed.
Lemma lem2806072 (d : int) (n : int) : (term3 d n) = (int_divides d n).
Proof. exact (EQ_MP (@lem2806012 d n) (@lem2806011 d n)). Qed.
Lemma lem2806073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2806074 (d : int) (n : int) : (term18 d n) = (term9 d n).
Proof. exact (MK_COMB (@lem2806073) (@lem2806072 d n)). Qed.
Lemma lem2806075 (d : int) (n : int) : (int_divides d n) = (int_divides d n).
Proof. exact (eq_refl (int_divides d n)). Qed.
Lemma lem2806076 (d : int) (n : int) : ((term3 d n) = (int_divides d n)) = ((int_divides d n) = (int_divides d n)).
Proof. exact (MK_COMB (@lem2806074 d n) (@lem2806075 d n)). Qed.
Lemma lem2806078 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2806079 (x : Prop) : (x = x) = True.
Proof. exact (@lem2806078 Prop x). Qed.
Lemma lem2806080 (d : int) (n : int) : ((int_divides d n) = (int_divides d n)) = True.
Proof. exact (@lem2806079 (int_divides d n)). Qed.
Lemma lem2806081 (d : int) (n : int) : ((term3 d n) = (int_divides d n)) = True.
Proof. exact (TRANS (@lem2806076 d n) (@lem2806080 d n)). Qed.
Lemma lem2806082 (d : int) : (term19 d) = term11.
Proof. exact (fun_ext (fun n : int => @lem2806081 d n)). Qed.
Lemma lem2806083 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2806084 (d : int) : (term1 d) = term12.
Proof. exact (MK_COMB (@lem2806083) (@lem2806082 d)). Qed.
Lemma lem2806086 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2806087 (t : Prop) : (term14 t) = t.
Proof. exact (@lem2806086 int t). Qed.
Lemma lem2806088 : term12 = True.
Proof. exact (@lem2806087 True). Qed.
Lemma lem2806089 (d : int) : (term1 d) = True.
Proof. exact (TRANS (@lem2806084 d) (@lem2806088)). Qed.
Lemma lem2806090 : term20 = term11.
Proof. exact (fun_ext (fun d : int => @lem2806089 d)). Qed.
Lemma lem2806091 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2806092 : term21 = term12.
Proof. exact (MK_COMB (@lem2806091) (@lem2806090)). Qed.
Lemma lem2806094 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2806095 (t : Prop) : (term14 t) = t.
Proof. exact (@lem2806094 int t). Qed.
Lemma lem2806096 : term12 = True.
Proof. exact (@lem2806095 True). Qed.
Lemma lem2806097 : term21 = True.
Proof. exact (TRANS (@lem2806092) (@lem2806096)). Qed.
Lemma lem2806098 : term22 = (True /\ True).
Proof. exact (MK_COMB (@lem2806060) (@lem2806097)). Qed.
Lemma lem2806100 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2806101 : (True /\ True) = True.
Proof. exact (@lem2806100 True). Qed.
Lemma lem2806102 : term22 = True.
Proof. exact (TRANS (@lem2806098) (@lem2806101)). Qed.
Lemma lem2806103 : True = term22.
Proof. exact (SYM (@lem2806102)). Qed.
Lemma lem2806104 : term22.
Proof. exact (EQ_MP (@lem2806103) (@lem0)). Qed.
