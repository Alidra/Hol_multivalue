Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1319377_term_abbrevs.
Require Import NADD_LE_ANTISYM_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1319283 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1319285 (x : nadd) (y : nadd) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1319284) (@lem1319283 x y)). Qed.
Lemma lem1319287 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319288 (y : nadd) (x : nadd) : (nadd_le y x) = (term0 y x).
Proof. exact (@lem1319287 y x). Qed.
Lemma lem1319289 (y : nadd) (x : nadd) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1319285 x y) (@lem1319288 y x)). Qed.
Lemma lem1319292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319293 (y : nadd) (x : nadd) : (term5 y x) = (term6 y x).
Proof. exact (MK_COMB (@lem1319292) (@lem1319289 y x)). Qed.
Lemma lem1319295 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term7 x) = (term7 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1319298 (x : nadd) (y : nadd) : ((term3 y x) = (nadd_eq x y)) = ((term4 y x) = ((term7 x) = (term7 y))).
Proof. exact (MK_COMB (@lem1319293 y x) (@lem1319295 x y)). Qed.
Lemma lem1319301 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319298 x y)). Qed.
Lemma lem1319302 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319303 (x : nadd) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1319302) (@lem1319301 x)). Qed.
Lemma lem1319309 (P : hreal -> Prop) : (term12 P) = (term13 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319310 (x : nadd) : (term14 x) = (term15 x).
Proof. exact (@lem1319309 (term16 x)). Qed.
Lemma lem1319311 (x : nadd) (y : nadd) : (term17 x y) = ((term4 y x) = ((term7 x) = (term7 y))).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1319312 (x : nadd) : (term18 x) = (term9 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319311 x y)). Qed.
Lemma lem1319313 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319314 (x : nadd) : (term14 x) = (term11 x).
Proof. exact (MK_COMB (@lem1319313) (@lem1319312 x)). Qed.
Lemma lem1319315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319316 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1319315) (@lem1319314 x)). Qed.
Lemma lem1319317 (x : nadd) (y : hreal) : (term21 x y) = ((term22 y x) = ((term7 x) = y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1319318 (x : nadd) : (term23 x) = (term16 x).
Proof. exact (fun_ext (fun y : hreal => @lem1319317 x y)). Qed.
Lemma lem1319319 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319320 (x : nadd) : (term15 x) = (term24 x).
Proof. exact (MK_COMB (@lem1319319) (@lem1319318 x)). Qed.
Lemma lem1319321 (x : nadd) : ((term14 x) = (term15 x)) = ((term11 x) = (term24 x)).
Proof. exact (MK_COMB (@lem1319316 x) (@lem1319320 x)). Qed.
Lemma lem1319322 (x : nadd) : (term11 x) = (term24 x).
Proof. exact (EQ_MP (@lem1319321 x) (@lem1319310 x)). Qed.
Lemma lem1319335 (x : nadd) : (term10 x) = (term24 x).
Proof. exact (TRANS (@lem1319303 x) (@lem1319322 x)). Qed.
Lemma lem1319336 : term25 = term26.
Proof. exact (fun_ext (fun x : nadd => @lem1319335 x)). Qed.
Lemma lem1319337 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319338 : term27 = term28.
Proof. exact (MK_COMB (@lem1319337) (@lem1319336)). Qed.
Lemma lem1319344 (P : hreal -> Prop) : (term12 P) = (term13 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319345 : term29 = term30.
Proof. exact (@lem1319344 term31). Qed.
Lemma lem1319346 (x : nadd) : (term32 x) = (term24 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1319347 : term33 = term26.
Proof. exact (fun_ext (fun x : nadd => @lem1319346 x)). Qed.
Lemma lem1319348 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319349 : term29 = term28.
Proof. exact (MK_COMB (@lem1319348) (@lem1319347)). Qed.
Lemma lem1319350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319351 : term34 = term35.
Proof. exact (MK_COMB (@lem1319350) (@lem1319349)). Qed.
Lemma lem1319352 (x : hreal) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1319353 : term38 = term31.
Proof. exact (fun_ext (fun x : hreal => @lem1319352 x)). Qed.
Lemma lem1319354 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319355 : term30 = term39.
Proof. exact (MK_COMB (@lem1319354) (@lem1319353)). Qed.
Lemma lem1319356 : (term29 = term30) = (term28 = term39).
Proof. exact (MK_COMB (@lem1319351) (@lem1319355)). Qed.
Lemma lem1319357 : term28 = term39.
Proof. exact (EQ_MP (@lem1319356) (@lem1319345)). Qed.
Lemma lem1319376 : term27 = term39.
Proof. exact (TRANS (@lem1319338) (@lem1319357)). Qed.
Lemma lem1319377 : term39.
Proof. exact (EQ_MP (@lem1319376) (@lem1271366)). Qed.
