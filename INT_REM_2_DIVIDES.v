Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_2_DIVIDES_term_abbrevs.
Require Import INT_REM_EQ_0_spec.
Require Import NOT_INT_REM_2_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2725225 (m : int) : term0 m.
Proof. exact (@lem2526537 m). Qed.
Lemma lem2725226 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2725227 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2725226 m) (@lem2725225 m)). Qed.
Lemma lem2725228 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2725227 m n). Qed.
Lemma lem2725229 (n : int) (m : int) : (term2 m n) = (((rem m n) = term3) = (int_divides n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2725231 : term4.
Proof. exact (proj1 (@lem2725224)). Qed.
Lemma lem2725233 (n : int) (h1 : (term5 n) = ((term6 n) = term7)) : (term5 n) = ((term6 n) = term7).
Proof. exact (h1). Qed.
Lemma lem2725234 (n : int) (h1 : (term5 n) = ((term6 n) = term7)) : ((term6 n) = term7) = (term5 n).
Proof. exact (SYM (@lem2725233 n h1)). Qed.
Lemma lem2725235 (n : int) (h1 : ((term6 n) = term7) = (term5 n)) : ((term6 n) = term7) = (term5 n).
Proof. exact (h1). Qed.
Lemma lem2725236 (n : int) (h1 : ((term6 n) = term7) = (term5 n)) : (term5 n) = ((term6 n) = term7).
Proof. exact (SYM (@lem2725235 n h1)). Qed.
Lemma lem2725237 (n : int) : ((term5 n) = ((term6 n) = term7)) = (((term6 n) = term7) = (term5 n)).
Proof. exact (prop_ext (fun h1 : (term5 n) = ((term6 n) = term7) => @lem2725234 n h1) (fun h1 : ((term6 n) = term7) = (term5 n) => @lem2725236 n h1)). Qed.
Lemma lem2725238 : term8 = term9.
Proof. exact (fun_ext (fun n : int => @lem2725237 n)). Qed.
Lemma lem2725239 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725240 : term4 = term10.
Proof. exact (MK_COMB (@lem2725239) (@lem2725238)). Qed.
Lemma lem2725241 : term10.
Proof. exact (EQ_MP (@lem2725240) (@lem2725231)). Qed.
Lemma lem2725242 (n : int) : term11 n.
Proof. exact (@lem2725241 n). Qed.
Lemma lem2725243 (n : int) : (term11 n) = (((term6 n) = term7) = (term5 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem2725262 (n : int) : ((term6 n) = term7) = (term5 n).
Proof. exact (EQ_MP (@lem2725243 n) (@lem2725242 n)). Qed.
Lemma lem2725265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725266 (n : int) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem2725265) (@lem2725262 n)). Qed.
Lemma lem2725267 (n : int) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem2725268 (n : int) : (((term6 n) = term7) = (term14 n)) = ((term5 n) = (term14 n)).
Proof. exact (MK_COMB (@lem2725266 n) (@lem2725267 n)). Qed.
Lemma lem2725271 : term15 = term16.
Proof. exact (fun_ext (fun n : int => @lem2725268 n)). Qed.
Lemma lem2725272 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725273 : term17 = term18.
Proof. exact (MK_COMB (@lem2725272) (@lem2725271)). Qed.
Lemma lem2725278 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem2725279 : term20 = term21.
Proof. exact (MK_COMB (@lem2725278) (@lem2725273)). Qed.
Lemma lem2725282 : term21 = term20.
Proof. exact (SYM (@lem2725279)). Qed.
Lemma lem2725292 (n : int) (m : int) : ((rem m n) = term3) = (int_divides n m).
Proof. exact (EQ_MP (@lem2725229 n m) (@lem2725228 m n)). Qed.
Lemma lem2725293 (n : int) : ((term6 n) = term3) = (term22 n).
Proof. exact (@lem2725292 term23 n). Qed.
Lemma lem2725294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725295 (n : int) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem2725294) (@lem2725293 n)). Qed.
Lemma lem2725296 (n : int) : (term22 n) = (term22 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem2725297 (n : int) : (((term6 n) = term3) = (term22 n)) = ((term22 n) = (term22 n)).
Proof. exact (MK_COMB (@lem2725295 n) (@lem2725296 n)). Qed.
Lemma lem2725299 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2725300 (x : Prop) : (x = x) = True.
Proof. exact (@lem2725299 Prop x). Qed.
Lemma lem2725301 (n : int) : ((term22 n) = (term22 n)) = True.
Proof. exact (@lem2725300 (term22 n)). Qed.
Lemma lem2725302 (n : int) : (((term6 n) = term3) = (term22 n)) = True.
Proof. exact (TRANS (@lem2725297 n) (@lem2725301 n)). Qed.
Lemma lem2725303 : term26 = term27.
Proof. exact (fun_ext (fun n : int => @lem2725302 n)). Qed.
Lemma lem2725304 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725305 : term28 = term29.
Proof. exact (MK_COMB (@lem2725304) (@lem2725303)). Qed.
Lemma lem2725307 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2725308 (t : Prop) : (term31 t) = t.
Proof. exact (@lem2725307 int t). Qed.
Lemma lem2725309 : term29 = True.
Proof. exact (@lem2725308 True). Qed.
Lemma lem2725310 : term28 = True.
Proof. exact (TRANS (@lem2725305) (@lem2725309)). Qed.
Lemma lem2725311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725312 : term19 = (and True).
Proof. exact (MK_COMB (@lem2725311) (@lem2725310)). Qed.
Lemma lem2725320 (n : int) (m : int) : ((rem m n) = term3) = (int_divides n m).
Proof. exact (EQ_MP (@lem2725229 n m) (@lem2725228 m n)). Qed.
Lemma lem2725321 (n : int) : ((term6 n) = term3) = (term22 n).
Proof. exact (@lem2725320 term23 n). Qed.
Lemma lem2725322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2725323 (n : int) : (term5 n) = (term14 n).
Proof. exact (MK_COMB (@lem2725322) (@lem2725321 n)). Qed.
Lemma lem2725324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2725325 (n : int) : (term13 n) = (term32 n).
Proof. exact (MK_COMB (@lem2725324) (@lem2725323 n)). Qed.
Lemma lem2725326 (n : int) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem2725327 (n : int) : ((term5 n) = (term14 n)) = ((term14 n) = (term14 n)).
Proof. exact (MK_COMB (@lem2725325 n) (@lem2725326 n)). Qed.
Lemma lem2725329 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2725330 (x : Prop) : (x = x) = True.
Proof. exact (@lem2725329 Prop x). Qed.
Lemma lem2725331 (n : int) : ((term14 n) = (term14 n)) = True.
Proof. exact (@lem2725330 (term14 n)). Qed.
Lemma lem2725332 (n : int) : ((term5 n) = (term14 n)) = True.
Proof. exact (TRANS (@lem2725327 n) (@lem2725331 n)). Qed.
Lemma lem2725333 : term16 = term27.
Proof. exact (fun_ext (fun n : int => @lem2725332 n)). Qed.
Lemma lem2725334 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2725335 : term18 = term29.
Proof. exact (MK_COMB (@lem2725334) (@lem2725333)). Qed.
Lemma lem2725337 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2725338 (t : Prop) : (term31 t) = t.
Proof. exact (@lem2725337 int t). Qed.
Lemma lem2725339 : term29 = True.
Proof. exact (@lem2725338 True). Qed.
Lemma lem2725340 : term18 = True.
Proof. exact (TRANS (@lem2725335) (@lem2725339)). Qed.
Lemma lem2725341 : term21 = (True /\ True).
Proof. exact (MK_COMB (@lem2725312) (@lem2725340)). Qed.
Lemma lem2725343 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2725344 : (True /\ True) = True.
Proof. exact (@lem2725343 True). Qed.
Lemma lem2725345 : term21 = True.
Proof. exact (TRANS (@lem2725341) (@lem2725344)). Qed.
Lemma lem2725346 : True = term21.
Proof. exact (SYM (@lem2725345)). Qed.
Lemma lem2725347 : term21.
Proof. exact (EQ_MP (@lem2725346) (@lem0)). Qed.
Lemma lem2725348 : term20.
Proof. exact (EQ_MP (@lem2725282) (@lem2725347)). Qed.
