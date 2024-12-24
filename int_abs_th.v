Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_abs_th_term_abbrevs.
Require Import int_abs_spec.
Require Import int_neg_spec.
Require Import int_neg_th_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2288128 (i : int) (h1 : (int_neg i) = (term0 i)) : (int_neg i) = (term0 i).
Proof. exact (h1). Qed.
Lemma lem2288129 (i : int) (h1 : (int_neg i) = (term0 i)) : (term0 i) = (int_neg i).
Proof. exact (SYM (@lem2288128 i h1)). Qed.
Lemma lem2288130 (i : int) (h1 : (term0 i) = (int_neg i)) : (term0 i) = (int_neg i).
Proof. exact (h1). Qed.
Lemma lem2288131 (i : int) (h1 : (term0 i) = (int_neg i)) : (int_neg i) = (term0 i).
Proof. exact (SYM (@lem2288130 i h1)). Qed.
Lemma lem2288132 (i : int) : ((int_neg i) = (term0 i)) = ((term0 i) = (int_neg i)).
Proof. exact (prop_ext (fun h1 : (int_neg i) = (term0 i) => @lem2288129 i h1) (fun h1 : (term0 i) = (int_neg i) => @lem2288131 i h1)). Qed.
Lemma lem2288133 : term1 = term2.
Proof. exact (fun_ext (fun i : int => @lem2288132 i)). Qed.
Lemma lem2288134 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2288135 : term3 = term4.
Proof. exact (MK_COMB (@lem2288134) (@lem2288133)). Qed.
Lemma lem2288136 : term4.
Proof. exact (EQ_MP (@lem2288135) (@lem2272662)). Qed.
Lemma lem2288137 (x : int) : term5 x.
Proof. exact (@lem2273074 x). Qed.
Lemma lem2288138 (x : int) : (term5 x) = ((term6 x) = (term7 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2288140 (i : int) : term8 i.
Proof. exact (@lem2288136 i). Qed.
Lemma lem2288141 (i : int) : (term8 i) = ((term0 i) = (int_neg i)).
Proof. exact (eq_refl (term8 i)). Qed.
Lemma lem2288143 (x : real) : term9 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem2288144 (x : real) : (term9 x) = ((real_abs x) = (term10 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2288146 (x : int) : term11 x.
Proof. exact (@lem2288126 x). Qed.
Lemma lem2288147 (x : int) : (term11 x) = ((int_abs x) = (term12 x)).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem2288152 (x : int) : (int_abs x) = (term12 x).
Proof. exact (EQ_MP (@lem2288147 x) (@lem2288146 x)). Qed.
Lemma lem2288154 (x : real) : (real_abs x) = (term10 x).
Proof. exact (EQ_MP (@lem2288144 x) (@lem2288143 x)). Qed.
Lemma lem2288155 (x : int) : (term13 x) = (term14 x).
Proof. exact (@lem2288154 (real_of_int x)). Qed.
Lemma lem2288156 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2288157 (x : int) : (term12 x) = (term15 x).
Proof. exact (MK_COMB (@lem2288156) (@lem2288155 x)). Qed.
Lemma lem2288158 (x : int) : (int_abs x) = (term15 x).
Proof. exact (TRANS (@lem2288152 x) (@lem2288157 x)). Qed.
Lemma lem2288159 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2288160 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2288159) (@lem2288158 x)). Qed.
Lemma lem2288161 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2288162 (x : int) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem2288161) (@lem2288160 x)). Qed.
Lemma lem2288164 (x : real) : (real_abs x) = (term10 x).
Proof. exact (EQ_MP (@lem2288144 x) (@lem2288143 x)). Qed.
Lemma lem2288165 (x : int) : (term13 x) = (term14 x).
Proof. exact (@lem2288164 (real_of_int x)). Qed.
Lemma lem2288166 (x : int) : ((term16 x) = (term13 x)) = ((term17 x) = (term14 x)).
Proof. exact (MK_COMB (@lem2288162 x) (@lem2288165 x)). Qed.
Lemma lem2288169 (x : int) : ((term17 x) = (term14 x)) = ((term16 x) = (term13 x)).
Proof. exact (SYM (@lem2288166 x)). Qed.
Lemma lem2288170 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term20 _476 _475 _474 _477) = (term21 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem2288171 (_474 : real) (_475 : Prop) (_477 : real) : (term22 _475 _474 _477) = (term23 _474 _475 _477).
Proof. exact (@lem2288170 _474 _475 term24 _477). Qed.
Lemma lem2288172 (x : int) : (term25 x) = (term26 x).
Proof. exact (@lem2288171 (real_of_int x) (term27 x) (term7 x)). Qed.
Lemma lem2288173 (x : int) : (term28 x) = ((term29 x) = (term7 x)).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2288174 (x : int) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem2288175 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2288174 x) (@lem2288173 x)). Qed.
Lemma lem2288176 (x : int) : (term33 x) = ((term34 x) = (real_of_int x)).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2288177 (x : int) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem2288178 (x : int) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem2288177 x) (@lem2288176 x)). Qed.
Lemma lem2288179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2288180 (x : int) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem2288179) (@lem2288178 x)). Qed.
Lemma lem2288181 (x : int) : (term26 x) = (term40 x).
Proof. exact (MK_COMB (@lem2288180 x) (@lem2288175 x)). Qed.
Lemma lem2288182 (x : int) : (term25 x) = ((term17 x) = (term14 x)).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2288183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2288184 (x : int) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem2288183) (@lem2288182 x)). Qed.
Lemma lem2288185 (x : int) : ((term25 x) = (term26 x)) = (((term17 x) = (term14 x)) = (term40 x)).
Proof. exact (MK_COMB (@lem2288184 x) (@lem2288181 x)). Qed.
Lemma lem2288186 (x : int) : ((term17 x) = (term14 x)) = (term40 x).
Proof. exact (EQ_MP (@lem2288185 x) (@lem2288172 x)). Qed.
Lemma lem2288187 (x : int) : (term40 x) = ((term17 x) = (term14 x)).
Proof. exact (SYM (@lem2288186 x)). Qed.
Lemma lem2288225 (a : int) : (term43 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2288226 (x : int) : (term43 x) = x.
Proof. exact (@lem2288225 x). Qed.
Lemma lem2288227 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2288228 (x : int) : (term34 x) = (real_of_int x).
Proof. exact (MK_COMB (@lem2288227) (@lem2288226 x)). Qed.
Lemma lem2288229 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2288230 (x : int) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem2288229) (@lem2288228 x)). Qed.
Lemma lem2288231 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2288232 (x : int) : ((term34 x) = (real_of_int x)) = ((real_of_int x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2288230 x) (@lem2288231 x)). Qed.
Lemma lem2288234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2288235 (x : real) : (x = x) = True.
Proof. exact (@lem2288234 real x). Qed.
Lemma lem2288236 (x : int) : ((real_of_int x) = (real_of_int x)) = True.
Proof. exact (@lem2288235 (real_of_int x)). Qed.
Lemma lem2288237 (x : int) : ((term34 x) = (real_of_int x)) = True.
Proof. exact (TRANS (@lem2288232 x) (@lem2288236 x)). Qed.
Lemma lem2288238 (x : int) : True = ((term34 x) = (real_of_int x)).
Proof. exact (SYM (@lem2288237 x)). Qed.
Lemma lem2288243 (i : int) : (term0 i) = (int_neg i).
Proof. exact (EQ_MP (@lem2288141 i) (@lem2288140 i)). Qed.
Lemma lem2288244 (x : int) : (term0 x) = (int_neg x).
Proof. exact (@lem2288243 x). Qed.
Lemma lem2288245 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2288246 (x : int) : (term29 x) = (term6 x).
Proof. exact (MK_COMB (@lem2288245) (@lem2288244 x)). Qed.
Lemma lem2288248 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2288138 x) (@lem2288137 x)). Qed.
Lemma lem2288249 (x : int) : (term29 x) = (term7 x).
Proof. exact (TRANS (@lem2288246 x) (@lem2288248 x)). Qed.
Lemma lem2288250 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2288251 (x : int) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem2288250) (@lem2288249 x)). Qed.
Lemma lem2288252 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2288253 (x : int) : ((term29 x) = (term7 x)) = ((term7 x) = (term7 x)).
Proof. exact (MK_COMB (@lem2288251 x) (@lem2288252 x)). Qed.
Lemma lem2288255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2288256 (x : real) : (x = x) = True.
Proof. exact (@lem2288255 real x). Qed.
Lemma lem2288257 (x : int) : ((term7 x) = (term7 x)) = True.
Proof. exact (@lem2288256 (term7 x)). Qed.
Lemma lem2288258 (x : int) : ((term29 x) = (term7 x)) = True.
Proof. exact (TRANS (@lem2288253 x) (@lem2288257 x)). Qed.
Lemma lem2288259 (x : int) : True = ((term29 x) = (term7 x)).
Proof. exact (SYM (@lem2288258 x)). Qed.
Lemma lem2288261 (x : int) : (term29 x) = (term7 x).
Proof. exact (EQ_MP (@lem2288259 x) (@lem0)). Qed.
Lemma lem2288262 (x : int) : term32 x.
Proof. exact (fun h0 : term48 x => @lem2288261 x). Qed.
Lemma lem2288263 (x : int) : (term34 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2288238 x) (@lem0)). Qed.
Lemma lem2288264 (x : int) : term37 x.
Proof. exact (fun h0 : term27 x => @lem2288263 x). Qed.
Lemma lem2288265 (x : int) : term40 x.
Proof. exact (conj (@lem2288264 x) (@lem2288262 x)). Qed.
Lemma lem2288266 (x : int) : (term17 x) = (term14 x).
Proof. exact (EQ_MP (@lem2288187 x) (@lem2288265 x)). Qed.
Lemma lem2288267 (x : int) : (term16 x) = (term13 x).
Proof. exact (EQ_MP (@lem2288169 x) (@lem2288266 x)). Qed.
Lemma lem2288272 : term49.
Proof. exact (fun x : int => @lem2288267 x). Qed.
