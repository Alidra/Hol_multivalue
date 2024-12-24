Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RNEG_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Require Import REAL_LE_LNEG_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1502196 (x : real) : term0 x.
Proof. exact (@lem1362225 x). Qed.
Lemma lem1502197 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1502198 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1502197 x) (@lem1502196 x)). Qed.
Lemma lem1502199 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1502198 x y). Qed.
Lemma lem1502200 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1502202 (y : real) : term5 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1502203 (y : real) : (term5 y) = (term6 y).
Proof. exact (eq_refl (term5 y)). Qed.
Lemma lem1502204 (y : real) : term6 y.
Proof. exact (EQ_MP (@lem1502203 y) (@lem1502202 y)). Qed.
Lemma lem1502205 (y : real) (x : real) : term7 y x.
Proof. exact (@lem1502204 y x). Qed.
Lemma lem1502206 (y : real) (x : real) : (term7 y x) = ((real_lt x y) = (term8 y x)).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1502219 (y : real) (x : real) : (real_lt x y) = (term8 y x).
Proof. exact (EQ_MP (@lem1502206 y x) (@lem1502205 y x)). Qed.
Lemma lem1502220 (y : real) (x : real) : (term9 x y) = (term10 y x).
Proof. exact (@lem1502219 (real_neg y) x). Qed.
Lemma lem1502222 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1502200 x y) (@lem1502199 x y)). Qed.
Lemma lem1502223 (y : real) (x : real) : (term3 y x) = (term4 y x).
Proof. exact (@lem1502222 y x). Qed.
Lemma lem1502225 (n : real) (m : real) : (real_add m n) = (real_add n m).
Proof. exact (proj1 (@lem1352530 n m (@el real))). Qed.
Lemma lem1502226 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1502225 x y). Qed.
Lemma lem1502230 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1502231 (x : real) (y : real) : (term4 y x) = (term4 x y).
Proof. exact (MK_COMB (@lem1502230) (@lem1502226 x y)). Qed.
Lemma lem1502232 (x : real) (y : real) : (term3 y x) = (term4 x y).
Proof. exact (TRANS (@lem1502223 y x) (@lem1502231 x y)). Qed.
Lemma lem1502233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1502234 (x : real) (y : real) : (term10 y x) = (term12 x y).
Proof. exact (MK_COMB (@lem1502233) (@lem1502232 x y)). Qed.
Lemma lem1502235 (x : real) (y : real) : (term9 x y) = (term12 x y).
Proof. exact (TRANS (@lem1502220 y x) (@lem1502234 x y)). Qed.
Lemma lem1502236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1502237 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1502236) (@lem1502235 x y)). Qed.
Lemma lem1502239 (y : real) (x : real) : (real_lt x y) = (term8 y x).
Proof. exact (EQ_MP (@lem1502206 y x) (@lem1502205 y x)). Qed.
Lemma lem1502240 (x : real) (y : real) : (term15 x y) = (term12 x y).
Proof. exact (@lem1502239 term16 (real_add x y)). Qed.
Lemma lem1502244 (x : real) (y : real) : ((term9 x y) = (term15 x y)) = ((term12 x y) = (term12 x y)).
Proof. exact (MK_COMB (@lem1502237 x y) (@lem1502240 x y)). Qed.
Lemma lem1502246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1502247 (x : Prop) : (x = x) = True.
Proof. exact (@lem1502246 Prop x). Qed.
Lemma lem1502248 (x : real) (y : real) : ((term12 x y) = (term12 x y)) = True.
Proof. exact (@lem1502247 (term12 x y)). Qed.
Lemma lem1502249 (x : real) (y : real) : ((term9 x y) = (term15 x y)) = True.
Proof. exact (TRANS (@lem1502244 x y) (@lem1502248 x y)). Qed.
Lemma lem1502250 (x : real) : (term17 x) = term18.
Proof. exact (fun_ext (fun y : real => @lem1502249 x y)). Qed.
Lemma lem1502251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1502252 (x : real) : (term19 x) = term20.
Proof. exact (MK_COMB (@lem1502251) (@lem1502250 x)). Qed.
Lemma lem1502254 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1502255 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1502254 real t). Qed.
Lemma lem1502256 : term20 = True.
Proof. exact (@lem1502255 True). Qed.
Lemma lem1502257 (x : real) : (term19 x) = True.
Proof. exact (TRANS (@lem1502252 x) (@lem1502256)). Qed.
Lemma lem1502258 : term23 = term18.
Proof. exact (fun_ext (fun x : real => @lem1502257 x)). Qed.
Lemma lem1502259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1502260 : term24 = term20.
Proof. exact (MK_COMB (@lem1502259) (@lem1502258)). Qed.
Lemma lem1502262 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1502263 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1502262 real t). Qed.
Lemma lem1502264 : term20 = True.
Proof. exact (@lem1502263 True). Qed.
Lemma lem1502265 : term24 = True.
Proof. exact (TRANS (@lem1502260) (@lem1502264)). Qed.
Lemma lem1502266 : True = term24.
Proof. exact (SYM (@lem1502265)). Qed.
Lemma lem1502267 : term24.
Proof. exact (EQ_MP (@lem1502266) (@lem0)). Qed.
