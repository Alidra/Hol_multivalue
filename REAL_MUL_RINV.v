Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_RINV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1340174_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1591935 (x : real) : term0 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1591936 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1591937 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1591936 x) (@lem1591935 x)). Qed.
Lemma lem1591938 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1591940 (x : real) : term2 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1591941 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1591942 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1591941 x) (@lem1591940 x)). Qed.
Lemma lem1591943 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1591942 x y). Qed.
Lemma lem1591944 (y : real) (x : real) : (term4 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1591957 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1591944 y x) (@lem1591943 x y)). Qed.
Lemma lem1591958 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1591957 (real_inv x) x). Qed.
Lemma lem1591959 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1591960 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1591959) (@lem1591958 x)). Qed.
Lemma lem1591961 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1591962 (x : real) : ((term5 x) = term9) = ((term6 x) = term9).
Proof. exact (MK_COMB (@lem1591960 x) (@lem1591961)). Qed.
Lemma lem1591963 (x : real) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1591964 (x : real) : (term11 x) = (term1 x).
Proof. exact (MK_COMB (@lem1591963 x) (@lem1591962 x)). Qed.
Lemma lem1591965 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1591964 x)). Qed.
Lemma lem1591966 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1591967 : term14 = term15.
Proof. exact (MK_COMB (@lem1591966) (@lem1591965)). Qed.
Lemma lem1591968 : term15 = term14.
Proof. exact (SYM (@lem1591967)). Qed.
Lemma lem1591974 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1591938 x) (@lem1591937 x)). Qed.
Lemma lem1591975 : term13 = term16.
Proof. exact (fun_ext (fun x : real => @lem1591974 x)). Qed.
Lemma lem1591976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1591977 : term15 = term17.
Proof. exact (MK_COMB (@lem1591976) (@lem1591975)). Qed.
Lemma lem1591979 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1591980 (t : Prop) : (term19 t) = t.
Proof. exact (@lem1591979 real t). Qed.
Lemma lem1591981 : term17 = True.
Proof. exact (@lem1591980 True). Qed.
Lemma lem1591982 : term15 = True.
Proof. exact (TRANS (@lem1591977) (@lem1591981)). Qed.
Lemma lem1591983 : True = term15.
Proof. exact (SYM (@lem1591982)). Qed.
Lemma lem1591984 : term15.
Proof. exact (EQ_MP (@lem1591983) (@lem0)). Qed.
Lemma lem1591985 : term14.
Proof. exact (EQ_MP (@lem1591968) (@lem1591984)). Qed.
