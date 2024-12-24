Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LNEG_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Require Import REAL_LE_RNEG_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1502118 (x : real) : term0 x.
Proof. exact (@lem1362465 x). Qed.
Lemma lem1502119 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1502120 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1502119 x) (@lem1502118 x)). Qed.
Lemma lem1502121 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1502120 x y). Qed.
Lemma lem1502122 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1502124 (y : real) : term5 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1502125 (y : real) : (term5 y) = (term6 y).
Proof. exact (eq_refl (term5 y)). Qed.
Lemma lem1502126 (y : real) : term6 y.
Proof. exact (EQ_MP (@lem1502125 y) (@lem1502124 y)). Qed.
Lemma lem1502127 (y : real) (x : real) : term7 y x.
Proof. exact (@lem1502126 y x). Qed.
Lemma lem1502128 (y : real) (x : real) : (term7 y x) = ((real_lt x y) = (term8 y x)).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1502141 (y : real) (x : real) : (real_lt x y) = (term8 y x).
Proof. exact (EQ_MP (@lem1502128 y x) (@lem1502127 y x)). Qed.
Lemma lem1502142 (y : real) (x : real) : (term9 x y) = (term10 y x).
Proof. exact (@lem1502141 y (real_neg x)). Qed.
Lemma lem1502144 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1502122 x y) (@lem1502121 x y)). Qed.
Lemma lem1502145 (y : real) (x : real) : (term3 y x) = (term4 y x).
Proof. exact (@lem1502144 y x). Qed.
Lemma lem1502147 (n : real) (m : real) : (real_add m n) = (real_add n m).
Proof. exact (proj1 (@lem1352530 n m (@el real))). Qed.
Lemma lem1502148 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1502147 x y). Qed.
Lemma lem1502152 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1502153 (x : real) (y : real) : (term11 y x) = (term11 x y).
Proof. exact (MK_COMB (@lem1502152) (@lem1502148 x y)). Qed.
Lemma lem1502154 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem1502155 (x : real) (y : real) : (term4 y x) = (term4 x y).
Proof. exact (MK_COMB (@lem1502153 x y) (@lem1502154)). Qed.
Lemma lem1502156 (x : real) (y : real) : (term3 y x) = (term4 x y).
Proof. exact (TRANS (@lem1502145 y x) (@lem1502155 x y)). Qed.
Lemma lem1502157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1502158 (x : real) (y : real) : (term10 y x) = (term13 x y).
Proof. exact (MK_COMB (@lem1502157) (@lem1502156 x y)). Qed.
Lemma lem1502159 (x : real) (y : real) : (term9 x y) = (term13 x y).
Proof. exact (TRANS (@lem1502142 y x) (@lem1502158 x y)). Qed.
Lemma lem1502160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502161 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1502160) (@lem1502159 x y)). Qed.
Lemma lem1502163 (y : real) (x : real) : (real_lt x y) = (term8 y x).
Proof. exact (EQ_MP (@lem1502128 y x) (@lem1502127 y x)). Qed.
Lemma lem1502164 (x : real) (y : real) : (term16 x y) = (term13 x y).
Proof. exact (@lem1502163 (real_add x y) term12). Qed.
Lemma lem1502168 (x : real) (y : real) : ((term9 x y) = (term16 x y)) = ((term13 x y) = (term13 x y)).
Proof. exact (MK_COMB (@lem1502161 x y) (@lem1502164 x y)). Qed.
Lemma lem1502170 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1502171 (x : Prop) : (x = x) = True.
Proof. exact (@lem1502170 Prop x). Qed.
Lemma lem1502172 (x : real) (y : real) : ((term13 x y) = (term13 x y)) = True.
Proof. exact (@lem1502171 (term13 x y)). Qed.
Lemma lem1502173 (x : real) (y : real) : ((term9 x y) = (term16 x y)) = True.
Proof. exact (TRANS (@lem1502168 x y) (@lem1502172 x y)). Qed.
Lemma lem1502174 (x : real) : (term17 x) = term18.
Proof. exact (fun_ext (fun y : real => @lem1502173 x y)). Qed.
Lemma lem1502175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1502176 (x : real) : (term19 x) = term20.
Proof. exact (MK_COMB (@lem1502175) (@lem1502174 x)). Qed.
Lemma lem1502178 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1502179 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1502178 real t). Qed.
Lemma lem1502180 : term20 = True.
Proof. exact (@lem1502179 True). Qed.
Lemma lem1502181 (x : real) : (term19 x) = True.
Proof. exact (TRANS (@lem1502176 x) (@lem1502180)). Qed.
Lemma lem1502182 : term23 = term18.
Proof. exact (fun_ext (fun x : real => @lem1502181 x)). Qed.
Lemma lem1502183 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1502184 : term24 = term20.
Proof. exact (MK_COMB (@lem1502183) (@lem1502182)). Qed.
Lemma lem1502186 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1502187 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1502186 real t). Qed.
Lemma lem1502188 : term20 = True.
Proof. exact (@lem1502187 True). Qed.
Lemma lem1502189 : term24 = True.
Proof. exact (TRANS (@lem1502184) (@lem1502188)). Qed.
Lemma lem1502190 : True = term24.
Proof. exact (SYM (@lem1502189)). Qed.
Lemma lem1502191 : term24.
Proof. exact (EQ_MP (@lem1502190) (@lem0)). Qed.
