Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LET_TOTAL_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Lemma lem1368042 (y : real) : term0 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1368043 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1368044 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1368043 y) (@lem1368042 y)). Qed.
Lemma lem1368045 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1368044 y x). Qed.
Lemma lem1368046 (y : real) (x : real) : (term2 y x) = ((real_lt x y) = (term3 y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1368059 (y : real) (x : real) : (real_lt x y) = (term3 y x).
Proof. exact (EQ_MP (@lem1368046 y x) (@lem1368045 y x)). Qed.
Lemma lem1368060 (x : real) (y : real) : (real_lt y x) = (term3 x y).
Proof. exact (@lem1368059 x y). Qed.
Lemma lem1368061 (x : real) (y : real) : (term4 x y) = (term4 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1368062 (x : real) (y : real) : (term5 y x) = (term6 x y).
Proof. exact (MK_COMB (@lem1368061 x y) (@lem1368060 x y)). Qed.
Lemma lem1368065 (x : real) : (term7 x) = (term8 x).
Proof. exact (fun_ext (fun y : real => @lem1368062 x y)). Qed.
Lemma lem1368066 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368067 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1368066) (@lem1368065 x)). Qed.
Lemma lem1368072 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1368067 x)). Qed.
Lemma lem1368073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368074 : term13 = term14.
Proof. exact (MK_COMB (@lem1368073) (@lem1368072)). Qed.
Lemma lem1368079 : term14 = term13.
Proof. exact (SYM (@lem1368074)). Qed.
Lemma lem1368084 (x : real) (y : real) : term15 x y.
Proof. exact (@lem9851 (real_le x y)). Qed.
Lemma lem1368085 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1368086 (x : real) (y : real) : term16 x y.
Proof. exact (EQ_MP (@lem1368085 x y) (@lem1368084 x y)). Qed.
Lemma lem1368087 (x : real) (y : real) (h1 : (real_le x y) = True) : (real_le x y) = True.
Proof. exact (h1). Qed.
Lemma lem1368088 (x : real) (y : real) (h1 : (real_le x y) = False) : (real_le x y) = False.
Proof. exact (h1). Qed.
Lemma lem1368093 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1368094 (x : real) (y : real) (h1 : (real_le x y) = True) : (term18 x y) = term19.
Proof. exact (MK_COMB (@lem1368093) (@lem1368087 x y h1)). Qed.
Lemma lem1368095 : term19 = term20.
Proof. exact (eq_refl term19). Qed.
Lemma lem1368096 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1368097 (x : real) (y : real) : ((term18 x y) = term19) = ((term18 x y) = term20).
Proof. exact (MK_COMB (@lem1368096 x y) (@lem1368095)). Qed.
Lemma lem1368098 (x : real) (y : real) : (term18 x y) = (term6 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1368099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1368100 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1368099) (@lem1368098 x y)). Qed.
Lemma lem1368101 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1368102 (x : real) (y : real) : ((term18 x y) = term20) = ((term6 x y) = term20).
Proof. exact (MK_COMB (@lem1368100 x y) (@lem1368101)). Qed.
Lemma lem1368103 (x : real) (y : real) : ((term18 x y) = term19) = ((term6 x y) = term20).
Proof. exact (TRANS (@lem1368097 x y) (@lem1368102 x y)). Qed.
Lemma lem1368104 (x : real) (y : real) (h1 : (real_le x y) = True) : (term6 x y) = term20.
Proof. exact (EQ_MP (@lem1368103 x y) (@lem1368094 x y h1)). Qed.
Lemma lem1368105 (x : real) (y : real) (h1 : (real_le x y) = True) : term20 = (term6 x y).
Proof. exact (SYM (@lem1368104 x y h1)). Qed.
Lemma lem1368106 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1368107 (x : real) (y : real) (h1 : (real_le x y) = False) : (term18 x y) = term23.
Proof. exact (MK_COMB (@lem1368106) (@lem1368088 x y h1)). Qed.
Lemma lem1368108 : term23 = term24.
Proof. exact (eq_refl term23). Qed.
Lemma lem1368109 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1368110 (x : real) (y : real) : ((term18 x y) = term23) = ((term18 x y) = term24).
Proof. exact (MK_COMB (@lem1368109 x y) (@lem1368108)). Qed.
Lemma lem1368111 (x : real) (y : real) : (term18 x y) = (term6 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1368112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1368113 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1368112) (@lem1368111 x y)). Qed.
Lemma lem1368114 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1368115 (x : real) (y : real) : ((term18 x y) = term24) = ((term6 x y) = term24).
Proof. exact (MK_COMB (@lem1368113 x y) (@lem1368114)). Qed.
Lemma lem1368116 (x : real) (y : real) : ((term18 x y) = term23) = ((term6 x y) = term24).
Proof. exact (TRANS (@lem1368110 x y) (@lem1368115 x y)). Qed.
Lemma lem1368117 (x : real) (y : real) (h1 : (real_le x y) = False) : (term6 x y) = term24.
Proof. exact (EQ_MP (@lem1368116 x y) (@lem1368107 x y h1)). Qed.
Lemma lem1368118 (x : real) (y : real) (h1 : (real_le x y) = False) : term24 = (term6 x y).
Proof. exact (SYM (@lem1368117 x y h1)). Qed.
Lemma lem1368120 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1368121 : term20 = True.
Proof. exact (@lem1368120 (~ True)). Qed.
Lemma lem1368122 : True = term20.
Proof. exact (SYM (@lem1368121)). Qed.
Lemma lem1368123 : term20.
Proof. exact (EQ_MP (@lem1368122) (@lem0)). Qed.
Lemma lem1368125 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1368126 : term24 = (~ False).
Proof. exact (@lem1368125 (~ False)). Qed.
Lemma lem1368128 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1368129 : term24 = True.
Proof. exact (TRANS (@lem1368126) (@lem1368128)). Qed.
Lemma lem1368130 : True = term24.
Proof. exact (SYM (@lem1368129)). Qed.
Lemma lem1368131 : term24.
Proof. exact (EQ_MP (@lem1368130) (@lem0)). Qed.
Lemma lem1368132 (x : real) (y : real) (h1 : (real_le x y) = False) : term6 x y.
Proof. exact (EQ_MP (@lem1368118 x y h1) (@lem1368131)). Qed.
Lemma lem1368133 (x : real) (y : real) (h1 : (real_le x y) = True) : term6 x y.
Proof. exact (EQ_MP (@lem1368105 x y h1) (@lem1368123)). Qed.
Lemma lem1368136 (x : real) (y : real) : term6 x y.
Proof. exact (or_elim (@lem1368086 x y) (fun h0 : (real_le x y) = True => @lem1368133 x y h0) (fun h0 : (real_le x y) = False => @lem1368132 x y h0)). Qed.
Lemma lem1368141 (x : real) : term10 x.
Proof. exact (fun y : real => @lem1368136 x y). Qed.
Lemma lem1368146 : term14.
Proof. exact (fun x : real => @lem1368141 x). Qed.
Lemma lem1368147 : term13.
Proof. exact (EQ_MP (@lem1368079) (@lem1368146)). Qed.
