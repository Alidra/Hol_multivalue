Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_GE_term_abbrevs.
Require Import int_ge_spec.
Require Import int_le_spec.
Require Import real_ge_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2318181 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem2318182 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem2318183 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem2318182 y) (@lem2318181 y)). Qed.
Lemma lem2318184 (y : real) (x : real) : term2 y x.
Proof. exact (@lem2318183 y x). Qed.
Lemma lem2318185 (y : real) (x : real) : (term2 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem2318187 (x : int) : term3 x.
Proof. exact (@lem2269094 x). Qed.
Lemma lem2318188 (x : int) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2318189 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2318188 x) (@lem2318187 x)). Qed.
Lemma lem2318190 (x : int) (y : int) : term5 x y.
Proof. exact (@lem2318189 x y). Qed.
Lemma lem2318191 (x : int) (y : int) : (term5 x y) = ((int_le x y) = (term6 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem2318193 (x : int) : term7 x.
Proof. exact (@lem2270452 x). Qed.
Lemma lem2318194 (x : int) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2318195 (x : int) : term8 x.
Proof. exact (EQ_MP (@lem2318194 x) (@lem2318193 x)). Qed.
Lemma lem2318196 (x : int) (y : int) : term9 x y.
Proof. exact (@lem2318195 x y). Qed.
Lemma lem2318197 (x : int) (y : int) : (term9 x y) = ((int_ge x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem2318210 (x : int) (y : int) : (int_ge x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2318197 x y) (@lem2318196 x y)). Qed.
Lemma lem2318212 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem2318185 y x) (@lem2318184 y x)). Qed.
Lemma lem2318213 (y : int) (x : int) : (term10 x y) = (term6 y x).
Proof. exact (@lem2318212 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2318214 (y : int) (x : int) : (int_ge x y) = (term6 y x).
Proof. exact (TRANS (@lem2318210 x y) (@lem2318213 y x)). Qed.
Lemma lem2318215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318216 (y : int) (x : int) : (term11 x y) = (term12 y x).
Proof. exact (MK_COMB (@lem2318215) (@lem2318214 y x)). Qed.
Lemma lem2318218 (x : int) (y : int) : (int_le x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2318191 x y) (@lem2318190 x y)). Qed.
Lemma lem2318219 (y : int) (x : int) : (int_le y x) = (term6 y x).
Proof. exact (@lem2318218 y x). Qed.
Lemma lem2318220 (y : int) (x : int) : ((int_ge x y) = (int_le y x)) = ((term6 y x) = (term6 y x)).
Proof. exact (MK_COMB (@lem2318216 y x) (@lem2318219 y x)). Qed.
Lemma lem2318222 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318223 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318222 Prop x). Qed.
Lemma lem2318224 (y : int) (x : int) : ((term6 y x) = (term6 y x)) = True.
Proof. exact (@lem2318223 (term6 y x)). Qed.
Lemma lem2318225 (y : int) (x : int) : ((int_ge x y) = (int_le y x)) = True.
Proof. exact (TRANS (@lem2318220 y x) (@lem2318224 y x)). Qed.
Lemma lem2318226 (x : int) : (term13 x) = term14.
Proof. exact (fun_ext (fun y : int => @lem2318225 y x)). Qed.
Lemma lem2318227 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318228 (x : int) : (term15 x) = term16.
Proof. exact (MK_COMB (@lem2318227) (@lem2318226 x)). Qed.
Lemma lem2318230 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318231 (t : Prop) : (term18 t) = t.
Proof. exact (@lem2318230 int t). Qed.
Lemma lem2318232 : term16 = True.
Proof. exact (@lem2318231 True). Qed.
Lemma lem2318233 (x : int) : (term15 x) = True.
Proof. exact (TRANS (@lem2318228 x) (@lem2318232)). Qed.
Lemma lem2318234 : term19 = term14.
Proof. exact (fun_ext (fun x : int => @lem2318233 x)). Qed.
Lemma lem2318235 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318236 : term20 = term16.
Proof. exact (MK_COMB (@lem2318235) (@lem2318234)). Qed.
Lemma lem2318238 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318239 (t : Prop) : (term18 t) = t.
Proof. exact (@lem2318238 int t). Qed.
Lemma lem2318240 : term16 = True.
Proof. exact (@lem2318239 True). Qed.
Lemma lem2318241 : term20 = True.
Proof. exact (TRANS (@lem2318236) (@lem2318240)). Qed.
Lemma lem2318242 : True = term20.
Proof. exact (SYM (@lem2318241)). Qed.
Lemma lem2318243 : term20.
Proof. exact (EQ_MP (@lem2318242) (@lem0)). Qed.
