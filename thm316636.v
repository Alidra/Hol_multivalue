Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm316636_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18934_spec.
Require Import thm18935_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm309993_spec.
Require Import thm309994_spec.
Require Import thm309995_spec.
Require Import thm310010_spec.
Require Import thm310011_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem310220 {A : Type'} (lt2 : type1402 A) (h1 : term0 A lt2) : term0 A lt2.
Proof. exact (h1). Qed.
Lemma lem310221 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term1 A lt2 P) : term1 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem310222 {A : Type'} (lt2 : type1402 A) (h1 : term2 A lt2) : term2 A lt2.
Proof. exact (h1). Qed.
Lemma lem310223 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term3 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem310225 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (EQ_MP (@lem310011 t1 t2) (@lem310010 t1 t2)). Qed.
Lemma lem310226 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term1 A lt2 P) = (term6 A lt2 P).
Proof. exact (@lem310225 (term7 A P) (term8 A lt2 P)). Qed.
Lemma lem310245 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term1 A lt2 P) : term6 A lt2 P.
Proof. exact (EQ_MP (@lem310226 A lt2 P) (@lem310221 A lt2 P h1)). Qed.
Lemma lem310246 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term6 A lt2 P) : term6 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem310247 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem310248 {A : Type'} (P : A -> Prop) (h1 : term7 A P) : term7 A P.
Proof. exact (h1). Qed.
Lemma lem310249 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem310250 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term10 A P lt2) : term10 A P lt2.
Proof. exact (h1). Qed.
Lemma lem310252 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem310253 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term10 A P lt2) = (term12 A P lt2).
Proof. exact (@lem310252 (term10 A P lt2)). Qed.
Lemma lem310254 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term12 A P lt2) = (term10 A P lt2).
Proof. exact (SYM (@lem310253 A P lt2)). Qed.
Lemma lem310255 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term13 A P lt2) : term13 A P lt2.
Proof. exact (h1). Qed.
Lemma lem310258 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term14 A a P lt2) : term14 A a P lt2.
Proof. exact (h1). Qed.
Lemma lem310259 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term15 A a P lt2.
Proof. exact (fun h0 : term14 A a P lt2 => @lem310258 A a P lt2 h0). Qed.
Lemma lem310260 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term15 A a P lt2) : term15 A a P lt2.
Proof. exact (h1). Qed.
Lemma lem310261 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term14 A a P lt2) : term14 A a P lt2.
Proof. exact (h1). Qed.
Lemma lem310262 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term14 A a P lt2) (h2 : term15 A a P lt2) : term14 A a P lt2.
Proof. exact (@lem310260 A a P lt2 h2 (@lem310261 A a P lt2 h1)). Qed.
Lemma lem310263 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term14 A a P lt2) : term16 A a P lt2.
Proof. exact (fun h0 : term15 A a P lt2 => @lem310262 A a P lt2 h1 h0). Qed.
Lemma lem310264 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term15 A a P lt2) : term15 A a P lt2.
Proof. exact (h1). Qed.
Lemma lem310265 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term14 A a P lt2) (h2 : term15 A a P lt2) : term14 A a P lt2.
Proof. exact (@lem310263 A a P lt2 h1 (@lem310264 A a P lt2 h2)). Qed.
Lemma lem310266 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (h1 : term15 A a P lt2) : term15 A a P lt2.
Proof. exact (fun h0 : term14 A a P lt2 => @lem310265 A a P lt2 h0 h1). Qed.
Lemma lem310267 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term17 A a P lt2.
Proof. exact (fun h0 : term15 A a P lt2 => @lem310266 A a P lt2 h0). Qed.
Lemma lem310270 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term15 A a P lt2.
Proof. exact (@lem310267 A a P lt2 (@lem310259 A a P lt2)). Qed.
Lemma lem310271 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term15 A a P lt2.
Proof. exact (@lem310270 A a P lt2). Qed.
Lemma lem310325 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem310326 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term12 A P lt2) = (term18 A P lt2).
Proof. exact (@lem310325 (term13 A P lt2)). Qed.
Lemma lem310328 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem310329 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term18 A P lt2) = (term10 A P lt2).
Proof. exact (@lem310328 (term10 A P lt2)). Qed.
Lemma lem310334 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term12 A P lt2) = (term10 A P lt2).
Proof. exact (TRANS (@lem310326 A P lt2) (@lem310329 A P lt2)). Qed.
Lemma lem310343 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (eq_refl (term20 A lt2 P)). Qed.
Lemma lem310344 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term21 A P lt2) = (term22 A P lt2).
Proof. exact (MK_COMB (@lem310343 A lt2 P) (@lem310334 A P lt2)). Qed.
Lemma lem310347 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem310348 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : (term14 A a P lt2) = (term24 A a P lt2).
Proof. exact (MK_COMB (@lem310347 A P a) (@lem310344 A P lt2)). Qed.
Lemma lem310351 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term25 A P lt2) = (term26 A P lt2).
Proof. exact (fun_ext (fun a : A => @lem310348 A a P lt2)). Qed.
Lemma lem310352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310353 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term27 A P lt2) = (term28 A P lt2).
Proof. exact (MK_COMB (@lem310352 A) (@lem310351 A P lt2)). Qed.
Lemma lem310358 {A : Type'} (lt2 : type1402 A) : (term29 A lt2) = (term30 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem310353 A P lt2)). Qed.
Lemma lem310359 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem310360 {A : Type'} (lt2 : type1402 A) : (term31 A lt2) = (term32 A lt2).
Proof. exact (MK_COMB (@lem310359 A) (@lem310358 A lt2)). Qed.
Lemma lem310365 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem310360 A lt2)). Qed.
Lemma lem310366 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem310375 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem310366 A) (@lem310365 A)). Qed.
Lemma lem310384 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term37 A P lt2 y x) = (term37 A P lt2 y x).
Proof. exact (eq_refl (term37 A P lt2 y x)). Qed.
Lemma lem310385 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term38 A P lt2 x) = (term38 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310384 A P lt2 y x)). Qed.
Lemma lem310386 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310387 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term39 A P lt2 x) = (term39 A P lt2 x).
Proof. exact (MK_COMB (@lem310386 A) (@lem310385 A P lt2 x)). Qed.
Lemma lem310388 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term40 A P lt2) = (term40 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem310387 A P lt2 x)). Qed.
Lemma lem310389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310390 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term10 A P lt2) = (term10 A P lt2).
Proof. exact (MK_COMB (@lem310389 A) (@lem310388 A P lt2)). Qed.
Lemma lem310397 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term41 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term41 A lt2 x P y)). Qed.
Lemma lem310398 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term42 A lt2 x P) = (term42 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem310397 A lt2 x P y)). Qed.
Lemma lem310399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310400 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term43 A lt2 x P) = (term43 A lt2 x P).
Proof. exact (MK_COMB (@lem310399 A) (@lem310398 A lt2 x P)). Qed.
Lemma lem310403 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem310404 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term45 A lt2 x P) = (term45 A lt2 x P).
Proof. exact (MK_COMB (@lem310403 A P x) (@lem310400 A lt2 x P)). Qed.
Lemma lem310405 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term46 A lt2 P) = (term46 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem310404 A lt2 x P)). Qed.
Lemma lem310406 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310407 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term8 A lt2 P) = (term8 A lt2 P).
Proof. exact (MK_COMB (@lem310406 A) (@lem310405 A lt2 P)). Qed.
Lemma lem310408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310409 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term9 A lt2 P).
Proof. exact (MK_COMB (@lem310408) (@lem310407 A lt2 P)). Qed.
Lemma lem310410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem310411 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (MK_COMB (@lem310410) (@lem310409 A lt2 P)). Qed.
Lemma lem310412 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term22 A P lt2) = (term22 A P lt2).
Proof. exact (MK_COMB (@lem310411 A lt2 P) (@lem310390 A P lt2)). Qed.
Lemma lem310415 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem310416 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : (term24 A a P lt2) = (term24 A a P lt2).
Proof. exact (MK_COMB (@lem310415 A P a) (@lem310412 A P lt2)). Qed.
Lemma lem310417 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term26 A P lt2) = (term26 A P lt2).
Proof. exact (fun_ext (fun a : A => @lem310416 A a P lt2)). Qed.
Lemma lem310418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310419 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term28 A P lt2) = (term28 A P lt2).
Proof. exact (MK_COMB (@lem310418 A) (@lem310417 A P lt2)). Qed.
Lemma lem310420 {A : Type'} (lt2 : type1402 A) : (term30 A lt2) = (term30 A lt2).
Proof. exact (fun_ext (fun P : A -> Prop => @lem310419 A P lt2)). Qed.
Lemma lem310421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem310422 {A : Type'} (lt2 : type1402 A) : (term32 A lt2) = (term32 A lt2).
Proof. exact (MK_COMB (@lem310421 A) (@lem310420 A lt2)). Qed.
Lemma lem310423 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem310422 A lt2)). Qed.
Lemma lem310424 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem310425 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem310424 A) (@lem310423 A)). Qed.
Lemma lem310482 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (TRANS (@lem310375 A) (@lem310425 A)). Qed.
Lemma lem310483 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem310482 A)). Qed.
Lemma lem310485 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem310487 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem310488 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term39 A P lt2 x) = (term47 A P lt2 x).
Proof. exact (@lem310487 (term39 A P lt2 x)). Qed.
Lemma lem310489 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term47 A P lt2 x) = (term39 A P lt2 x).
Proof. exact (SYM (@lem310488 A P lt2 x)). Qed.
Lemma lem310490 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term48 A P lt2 x.
Proof. exact (h1). Qed.
Lemma lem310501 {A : Type'} (P : A -> Prop) (y : A) : (term49 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem310503 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term50 A lt2 y x) = (term50 A lt2 y x).
Proof. exact (eq_refl (term50 A lt2 y x)). Qed.
Lemma lem310504 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (MK_COMB (@lem310503 A lt2 y x) (@lem310501 A P y)). Qed.
Lemma lem310505 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term51 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term54 A P y)). Qed.
Lemma lem310506 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem310505 A lt2 x P y) (@lem310504 A lt2 x P y)). Qed.
Lemma lem310507 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem310508 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem310507 A (term42 A lt2 x P)). Qed.
Lemma lem310509 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term59 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term59 A lt2 x P y)). Qed.
Lemma lem310510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310511 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term53 A lt2 x P y).
Proof. exact (MK_COMB (@lem310510) (@lem310509 A lt2 x P y)). Qed.
Lemma lem310512 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem310511 A lt2 x P y) (@lem310506 A lt2 x P y)). Qed.
Lemma lem310513 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term61 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem310512 A lt2 x P y)). Qed.
Lemma lem310514 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310515 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem310514 A) (@lem310513 A lt2 x P)). Qed.
Lemma lem310516 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (TRANS (@lem310508 A lt2 x P) (@lem310515 A lt2 x P)). Qed.
Lemma lem310518 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem310519 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem310518 A P x) (@lem310516 A lt2 x P)). Qed.
Lemma lem310520 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term65 A lt2 x P).
Proof. exact (@lem17045 (P x) (term43 A lt2 x P)). Qed.
Lemma lem310521 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem310520 A lt2 x P) (@lem310519 A lt2 x P)). Qed.
Lemma lem310522 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem310523 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term70 A lt2 P).
Proof. exact (@lem310522 A (term46 A lt2 P)). Qed.
Lemma lem310524 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term71 A lt2 P x) = (term45 A lt2 x P).
Proof. exact (eq_refl (term71 A lt2 P x)). Qed.
Lemma lem310525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310526 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term67 A lt2 x P).
Proof. exact (MK_COMB (@lem310525) (@lem310524 A lt2 x P)). Qed.
Lemma lem310527 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem310526 A lt2 x P) (@lem310521 A lt2 x P)). Qed.
Lemma lem310528 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term74 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem310527 A lt2 x P)). Qed.
Lemma lem310529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310530 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term70 A lt2 P) = (term75 A lt2 P).
Proof. exact (MK_COMB (@lem310529 A) (@lem310528 A lt2 P)). Qed.
Lemma lem310531 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term75 A lt2 P).
Proof. exact (TRANS (@lem310523 A lt2 P) (@lem310530 A lt2 P)). Qed.
Lemma lem310614 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem310615 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem310614 A P Q). Qed.
Lemma lem310616 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term79 A lt2 x P).
Proof. exact (@lem310615 A (term54 A P x) (term62 A lt2 x P)). Qed.
Lemma lem310617 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem310618 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term81 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem310617 A lt2 x P y)). Qed.
Lemma lem310619 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310620 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem310619 A) (@lem310618 A lt2 x P)). Qed.
Lemma lem310621 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem310622 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem310621 A P x) (@lem310620 A lt2 x P)). Qed.
Lemma lem310623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310624 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term83 A lt2 x P) = (term84 A lt2 x P).
Proof. exact (MK_COMB (@lem310623) (@lem310622 A lt2 x P)). Qed.
Lemma lem310625 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem310626 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem310627 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term85 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (MK_COMB (@lem310626 A P x) (@lem310625 A lt2 x P y)). Qed.
Lemma lem310628 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term87 A lt2 x P) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem310627 A lt2 x P y)). Qed.
Lemma lem310629 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310630 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term79 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem310629 A) (@lem310628 A lt2 x P)). Qed.
Lemma lem310631 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term78 A lt2 x P) = (term79 A lt2 x P)) = ((term66 A lt2 x P) = (term89 A lt2 x P)).
Proof. exact (MK_COMB (@lem310624 A lt2 x P) (@lem310630 A lt2 x P)). Qed.
Lemma lem310632 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term66 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (EQ_MP (@lem310631 A lt2 x P) (@lem310616 A lt2 x P)). Qed.
Lemma lem310633 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem310632 A lt2 x P)). Qed.
Lemma lem310634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310635 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem310634 A) (@lem310633 A lt2 P)). Qed.
Lemma lem310637 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem310638 {A : Type'} (P : type1402 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem310637 A A P). Qed.
Lemma lem310639 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term97 A lt2 P).
Proof. exact (@lem310638 A (term98 A lt2 P)). Qed.
Lemma lem310640 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem310641 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem310642 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term101 A lt2 x P y).
Proof. exact (MK_COMB (@lem310640 A lt2 x P) (@lem310641 A y)). Qed.
Lemma lem310643 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term101 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (eq_refl (term101 A lt2 x P y)). Qed.
Lemma lem310644 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term86 A lt2 x P y).
Proof. exact (TRANS (@lem310642 A lt2 x P y) (@lem310643 A lt2 x P y)). Qed.
Lemma lem310645 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term102 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem310644 A lt2 x P y)). Qed.
Lemma lem310646 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem310647 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term103 A lt2 P x) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem310646 A) (@lem310645 A lt2 x P)). Qed.
Lemma lem310648 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term104 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem310647 A lt2 x P)). Qed.
Lemma lem310649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310650 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem310649 A) (@lem310648 A lt2 P)). Qed.
Lemma lem310651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310652 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term105 A lt2 P) = (term106 A lt2 P).
Proof. exact (MK_COMB (@lem310651) (@lem310650 A lt2 P)). Qed.
Lemma lem310653 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem310654 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem310655 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term108 A lt2 P y x).
Proof. exact (MK_COMB (@lem310653 A lt2 x P) (@lem310654 A y x)). Qed.
Lemma lem310656 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term108 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (eq_refl (term108 A lt2 P y x)). Qed.
Lemma lem310657 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (TRANS (@lem310655 A lt2 P y x) (@lem310656 A lt2 P y x)). Qed.
Lemma lem310658 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term110 A lt2 P y) = (term111 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem310657 A lt2 P y x)). Qed.
Lemma lem310659 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310660 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term112 A lt2 P y) = (term113 A lt2 P y).
Proof. exact (MK_COMB (@lem310659 A) (@lem310658 A lt2 P y)). Qed.
Lemma lem310661 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term114 A lt2 P) = (term115 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem310660 A lt2 P y)). Qed.
Lemma lem310662 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem310663 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term97 A lt2 P) = (term116 A lt2 P).
Proof. exact (MK_COMB (@lem310662 A) (@lem310661 A lt2 P)). Qed.
Lemma lem310664 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term96 A lt2 P) = (term97 A lt2 P)) = ((term91 A lt2 P) = (term116 A lt2 P)).
Proof. exact (MK_COMB (@lem310652 A lt2 P) (@lem310663 A lt2 P)). Qed.
Lemma lem310665 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term116 A lt2 P).
Proof. exact (EQ_MP (@lem310664 A lt2 P) (@lem310639 A lt2 P)). Qed.
Lemma lem310667 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem310635 A lt2 P) (@lem310665 A lt2 P)). Qed.
Lemma lem310668 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem310531 A lt2 P) (@lem310667 A lt2 P)). Qed.
Lemma lem310669 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term116 A lt2 P.
Proof. exact (EQ_MP (@lem310668 A lt2 P) (@lem310485 A lt2 P h1)). Qed.
Lemma lem310677 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term117 A P lt2 y x) = (term118 A P lt2 y x).
Proof. exact (@lem17045 (P y) (lt2 y x)). Qed.
Lemma lem310679 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem310680 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term119 A P lt2 y x) = (term120 A P lt2 y x).
Proof. exact (MK_COMB (@lem310679 A P x) (@lem310677 A P lt2 y x)). Qed.
Lemma lem310681 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term121 A P lt2 y x) = (term119 A P lt2 y x).
Proof. exact (@lem17362 (P x) (term122 A P lt2 y x)). Qed.
Lemma lem310682 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term121 A P lt2 y x) = (term120 A P lt2 y x).
Proof. exact (TRANS (@lem310681 A P lt2 y x) (@lem310680 A P lt2 y x)). Qed.
Lemma lem310683 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem310684 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term48 A P lt2 x) = (term123 A P lt2 x).
Proof. exact (@lem310683 A (term38 A P lt2 x)). Qed.
Lemma lem310685 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term124 A P lt2 x y) = (term37 A P lt2 y x).
Proof. exact (eq_refl (term124 A P lt2 x y)). Qed.
Lemma lem310686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem310687 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term125 A P lt2 x y) = (term121 A P lt2 y x).
Proof. exact (MK_COMB (@lem310686) (@lem310685 A P lt2 y x)). Qed.
Lemma lem310688 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term125 A P lt2 x y) = (term120 A P lt2 y x).
Proof. exact (TRANS (@lem310687 A P lt2 y x) (@lem310682 A P lt2 y x)). Qed.
Lemma lem310689 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term126 A P lt2 x) = (term127 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310688 A P lt2 y x)). Qed.
Lemma lem310690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310691 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term123 A P lt2 x) = (term128 A P lt2 x).
Proof. exact (MK_COMB (@lem310690 A) (@lem310689 A P lt2 x)). Qed.
Lemma lem310692 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term48 A P lt2 x) = (term128 A P lt2 x).
Proof. exact (TRANS (@lem310684 A P lt2 x) (@lem310691 A P lt2 x)). Qed.
Lemma lem310694 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem310695 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (@lem310694 A P Q). Qed.
Lemma lem310696 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term131 A P lt2 x) = (term132 A P lt2 x).
Proof. exact (@lem310695 A (term133 A P x) (term134 A P lt2 x)). Qed.
Lemma lem310697 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term135 A P x y) = (P x).
Proof. exact (eq_refl (term135 A P x y)). Qed.
Lemma lem310698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem310699 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term136 A P x y) = (term44 A P x).
Proof. exact (MK_COMB (@lem310698) (@lem310697 A y P x)). Qed.
Lemma lem310700 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term137 A P lt2 x y) = (term118 A P lt2 y x).
Proof. exact (eq_refl (term137 A P lt2 x y)). Qed.
Lemma lem310701 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term138 A P lt2 x y) = (term120 A P lt2 y x).
Proof. exact (MK_COMB (@lem310699 A y P x) (@lem310700 A P lt2 y x)). Qed.
Lemma lem310702 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term139 A P lt2 x) = (term127 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310701 A P lt2 y x)). Qed.
Lemma lem310703 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310704 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term131 A P lt2 x) = (term128 A P lt2 x).
Proof. exact (MK_COMB (@lem310703 A) (@lem310702 A P lt2 x)). Qed.
Lemma lem310705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310706 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term140 A P lt2 x) = (term141 A P lt2 x).
Proof. exact (MK_COMB (@lem310705) (@lem310704 A P lt2 x)). Qed.
Lemma lem310707 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term135 A P x y) = (P x).
Proof. exact (eq_refl (term135 A P x y)). Qed.
Lemma lem310708 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (term133 A P x).
Proof. exact (fun_ext (fun y : A => @lem310707 A y P x)). Qed.
Lemma lem310709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310710 {A : Type'} (P : A -> Prop) (x : A) : (term143 A P x) = (term144 A P x).
Proof. exact (MK_COMB (@lem310709 A) (@lem310708 A P x)). Qed.
Lemma lem310711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem310712 {A : Type'} (P : A -> Prop) (x : A) : (term145 A P x) = (term146 A P x).
Proof. exact (MK_COMB (@lem310711) (@lem310710 A P x)). Qed.
Lemma lem310713 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term137 A P lt2 x y) = (term118 A P lt2 y x).
Proof. exact (eq_refl (term137 A P lt2 x y)). Qed.
Lemma lem310714 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term147 A P lt2 x) = (term134 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310713 A P lt2 y x)). Qed.
Lemma lem310715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310716 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term148 A P lt2 x) = (term149 A P lt2 x).
Proof. exact (MK_COMB (@lem310715 A) (@lem310714 A P lt2 x)). Qed.
Lemma lem310717 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term132 A P lt2 x) = (term150 A P lt2 x).
Proof. exact (MK_COMB (@lem310712 A P x) (@lem310716 A P lt2 x)). Qed.
Lemma lem310718 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : ((term131 A P lt2 x) = (term132 A P lt2 x)) = ((term128 A P lt2 x) = (term150 A P lt2 x)).
Proof. exact (MK_COMB (@lem310706 A P lt2 x) (@lem310717 A P lt2 x)). Qed.
Lemma lem310719 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term128 A P lt2 x) = (term150 A P lt2 x).
Proof. exact (EQ_MP (@lem310718 A P lt2 x) (@lem310696 A P lt2 x)). Qed.
Lemma lem310721 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem310722 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (@lem310721 A t). Qed.
Lemma lem310723 {A : Type'} (P : A -> Prop) (x : A) : (term144 A P x) = (P x).
Proof. exact (@lem310722 A (P x)). Qed.
Lemma lem310724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem310725 {A : Type'} (P : A -> Prop) (x : A) : (term146 A P x) = (term44 A P x).
Proof. exact (MK_COMB (@lem310724) (@lem310723 A P x)). Qed.
Lemma lem310774 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term149 A P lt2 x) = (term149 A P lt2 x).
Proof. exact (eq_refl (term149 A P lt2 x)). Qed.
Lemma lem310775 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term150 A P lt2 x) = (term152 A P lt2 x).
Proof. exact (MK_COMB (@lem310725 A P x) (@lem310774 A P lt2 x)). Qed.
Lemma lem310778 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term128 A P lt2 x) = (term152 A P lt2 x).
Proof. exact (TRANS (@lem310719 A P lt2 x) (@lem310775 A P lt2 x)). Qed.
Lemma lem310779 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term48 A P lt2 x) = (term152 A P lt2 x).
Proof. exact (TRANS (@lem310692 A P lt2 x) (@lem310778 A P lt2 x)). Qed.
Lemma lem310780 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term152 A P lt2 x.
Proof. exact (EQ_MP (@lem310779 A P lt2 x) (@lem310490 A P lt2 x h1)). Qed.
Lemma lem310781 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term113 A lt2 P y.
Proof. exact (h1). Qed.
Lemma lem310800 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term118 A P lt2 y x) = (term118 A P lt2 y x).
Proof. exact (eq_refl (term118 A P lt2 y x)). Qed.
Lemma lem310801 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term134 A P lt2 x) = (term134 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310800 A P lt2 y x)). Qed.
Lemma lem310802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310803 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term149 A P lt2 x) = (term149 A P lt2 x).
Proof. exact (MK_COMB (@lem310802 A) (@lem310801 A P lt2 x)). Qed.
Lemma lem310808 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem310809 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term152 A P lt2 x) = (term152 A P lt2 x).
Proof. exact (MK_COMB (@lem310808 A P x) (@lem310803 A P lt2 x)). Qed.
Lemma lem310810 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term152 A P lt2 x.
Proof. exact (EQ_MP (@lem310809 A P lt2 x) (@lem310780 A P lt2 x h1)). Qed.
Lemma lem310833 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term109 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (eq_refl (term109 A lt2 P y x)). Qed.
Lemma lem310834 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term111 A lt2 P y) = (term111 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem310833 A lt2 P y x)). Qed.
Lemma lem310835 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310836 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term113 A lt2 P y) = (term113 A lt2 P y).
Proof. exact (MK_COMB (@lem310835 A) (@lem310834 A lt2 P y)). Qed.
Lemma lem310837 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term113 A lt2 P y.
Proof. exact (EQ_MP (@lem310836 A lt2 P y) (@lem310781 A lt2 P y h1)). Qed.
Lemma lem310838 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term149 A P lt2 x.
Proof. exact (proj2 (@lem310810 A P lt2 x h1)). Qed.
Lemma lem310861 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term109 A lt2 P y x) = (term153 A lt2 P y x).
Proof. exact (@lem19490 (term154 A lt2 y x) (term54 A P x) (term155 A P y x)). Qed.
Lemma lem310862 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term111 A lt2 P y) = (term156 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem310861 A lt2 P y x)). Qed.
Lemma lem310863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310865 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term113 A lt2 P y) = (term157 A lt2 P y).
Proof. exact (MK_COMB (@lem310863 A) (@lem310862 A lt2 P y)). Qed.
Lemma lem310866 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term157 A lt2 P y.
Proof. exact (EQ_MP (@lem310865 A lt2 P y) (@lem310837 A lt2 P y h1)). Qed.
Lemma lem310878 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term118 A P lt2 y x) = (term118 A P lt2 y x).
Proof. exact (eq_refl (term118 A P lt2 y x)). Qed.
Lemma lem310879 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term134 A P lt2 x) = (term134 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem310878 A P lt2 y x)). Qed.
Lemma lem310880 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem310882 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term149 A P lt2 x) = (term149 A P lt2 x).
Proof. exact (MK_COMB (@lem310880 A) (@lem310879 A P lt2 x)). Qed.
Lemma lem310883 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term149 A P lt2 x.
Proof. exact (EQ_MP (@lem310882 A P lt2 x) (@lem310838 A P lt2 x h1)). Qed.
Lemma lem310884 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term158 A lt2 P y _6804.
Proof. exact (@lem310866 A lt2 P y h1 _6804). Qed.
Lemma lem310885 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (_6804 : A) : (term158 A lt2 P y _6804) = (term153 A lt2 P y _6804).
Proof. exact (eq_refl (term158 A lt2 P y _6804)). Qed.
Lemma lem310886 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term153 A lt2 P y _6804.
Proof. exact (EQ_MP (@lem310885 A lt2 P y _6804) (@lem310884 A _6804 lt2 P y h1)). Qed.
Lemma lem310887 {A : Type'} (_6805 : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term137 A P lt2 x _6805.
Proof. exact (@lem310883 A P lt2 x h1 _6805). Qed.
Lemma lem310888 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6805 : A) (x : A) : (term137 A P lt2 x _6805) = (term118 A P lt2 _6805 x).
Proof. exact (eq_refl (term137 A P lt2 x _6805)). Qed.
Lemma lem310901 {A : Type'} (_6805 : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term118 A P lt2 _6805 x.
Proof. exact (EQ_MP (@lem310888 A P lt2 _6805 x) (@lem310887 A _6805 P lt2 x h1)). Qed.
Lemma lem310907 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term159 A P lt2 y _6804.
Proof. exact (proj1 (@lem310886 A _6804 lt2 P y h1)). Qed.
Lemma lem310913 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term160 A P y _6804.
Proof. exact (proj2 (@lem310886 A _6804 lt2 P y h1)). Qed.
Lemma lem310915 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : P x.
Proof. exact (proj1 (@lem310810 A P lt2 x h1)). Qed.
Lemma lem310916 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term161 A P x.
Proof. exact (fun h0 : term54 A P x => @lem310915 A P lt2 x h1). Qed.
Lemma lem310918 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem310919 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem310918 (P x)). Qed.
Lemma lem310920 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : P x.
Proof. exact (EQ_MP (@lem310919 A P x) (@lem310916 A P lt2 x h1)). Qed.
Lemma lem310926 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem310927 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : (term160 A P y _6804) = (term163 A y P _6804).
Proof. exact (@lem310926 (term155 A P y _6804) (term54 A P _6804)). Qed.
Lemma lem310933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310934 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : (term164 A P y _6804) = (term165 A y P _6804).
Proof. exact (MK_COMB (@lem310933) (@lem310927 A y P _6804)). Qed.
Lemma lem310940 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : (term163 A y P _6804) = (term163 A y P _6804).
Proof. exact (eq_refl (term163 A y P _6804)). Qed.
Lemma lem310941 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term160 A P y _6804) = (term163 A y P _6804)) = ((term163 A y P _6804) = (term163 A y P _6804)).
Proof. exact (MK_COMB (@lem310934 A y P _6804) (@lem310940 A y P _6804)). Qed.
Lemma lem310943 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem310944 (x : Prop) : (x = x) = True.
Proof. exact (@lem310943 Prop x). Qed.
Lemma lem310945 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term163 A y P _6804) = (term163 A y P _6804)) = True.
Proof. exact (@lem310944 (term163 A y P _6804)). Qed.
Lemma lem310946 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term160 A P y _6804) = (term163 A y P _6804)) = True.
Proof. exact (TRANS (@lem310941 A y P _6804) (@lem310945 A y P _6804)). Qed.
Lemma lem310947 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : True = ((term160 A P y _6804) = (term163 A y P _6804)).
Proof. exact (SYM (@lem310946 A y P _6804)). Qed.
Lemma lem310948 {A : Type'} (y : A -> A) (P : A -> Prop) (_6804 : A) : (term160 A P y _6804) = (term163 A y P _6804).
Proof. exact (EQ_MP (@lem310947 A y P _6804) (@lem0)). Qed.
Lemma lem310949 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term163 A y P _6804.
Proof. exact (EQ_MP (@lem310948 A y P _6804) (@lem310913 A _6804 lt2 P y h1)). Qed.
Lemma lem310951 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem310952 {A : Type'} (P : A -> Prop) (y : A -> A) (_6804 : A) : (term163 A y P _6804) = (term167 A P y _6804).
Proof. exact (@lem310951 (term54 A P _6804) (term155 A P y _6804)). Qed.
Lemma lem310954 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem310955 {A : Type'} (P : A -> Prop) (_6804 : A) : (term49 A P _6804) = (P _6804).
Proof. exact (@lem310954 (P _6804)). Qed.
Lemma lem310956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem310957 {A : Type'} (P : A -> Prop) (_6804 : A) : (term168 A P _6804) = (term23 A P _6804).
Proof. exact (MK_COMB (@lem310956) (@lem310955 A P _6804)). Qed.
Lemma lem310958 {A : Type'} (P : A -> Prop) (y : A -> A) (_6804 : A) : (term155 A P y _6804) = (term155 A P y _6804).
Proof. exact (eq_refl (term155 A P y _6804)). Qed.
Lemma lem310959 {A : Type'} (P : A -> Prop) (y : A -> A) (_6804 : A) : (term167 A P y _6804) = (term169 A P y _6804).
Proof. exact (MK_COMB (@lem310957 A P _6804) (@lem310958 A P y _6804)). Qed.
Lemma lem310960 {A : Type'} (P : A -> Prop) (y : A -> A) (_6804 : A) : (term163 A y P _6804) = (term169 A P y _6804).
Proof. exact (TRANS (@lem310952 A P y _6804) (@lem310959 A P y _6804)). Qed.
Lemma lem310963 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term169 A P y _6804.
Proof. exact (EQ_MP (@lem310960 A P y _6804) (@lem310949 A _6804 lt2 P y h1)). Qed.
Lemma lem310964 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term169 A P y _6804.
Proof. exact (@lem310963 A _6804 lt2 P y h1). Qed.
Lemma lem310965 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term169 A P y x.
Proof. exact (@lem310964 A x lt2 P y h1). Qed.
Lemma lem310968 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term155 A P y x.
Proof. exact (@lem310965 A x lt2 P y h1 (@lem310920 A P lt2 x h2)). Qed.
Lemma lem310969 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term170 A P y x.
Proof. exact (fun h0 : term171 A P y x => @lem310968 A y P lt2 x h1 h2). Qed.
Lemma lem310971 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem310972 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term170 A P y x) = (term155 A P y x).
Proof. exact (@lem310971 (term155 A P y x)). Qed.
Lemma lem310973 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term155 A P y x.
Proof. exact (EQ_MP (@lem310972 A P y x) (@lem310969 A y P lt2 x h1 h2)). Qed.
Lemma lem310975 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : P x.
Proof. exact (proj1 (@lem310810 A P lt2 x h1)). Qed.
Lemma lem310976 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term161 A P x.
Proof. exact (fun h0 : term54 A P x => @lem310975 A P lt2 x h1). Qed.
Lemma lem310978 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem310979 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem310978 (P x)). Qed.
Lemma lem310980 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : P x.
Proof. exact (EQ_MP (@lem310979 A P x) (@lem310976 A P lt2 x h1)). Qed.
Lemma lem310986 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem310987 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : (term159 A P lt2 y _6804) = (term172 A lt2 y P _6804).
Proof. exact (@lem310986 (term154 A lt2 y _6804) (term54 A P _6804)). Qed.
Lemma lem310993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem310994 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : (term173 A P lt2 y _6804) = (term174 A lt2 y P _6804).
Proof. exact (MK_COMB (@lem310993) (@lem310987 A lt2 y P _6804)). Qed.
Lemma lem311000 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : (term172 A lt2 y P _6804) = (term172 A lt2 y P _6804).
Proof. exact (eq_refl (term172 A lt2 y P _6804)). Qed.
Lemma lem311001 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term159 A P lt2 y _6804) = (term172 A lt2 y P _6804)) = ((term172 A lt2 y P _6804) = (term172 A lt2 y P _6804)).
Proof. exact (MK_COMB (@lem310994 A lt2 y P _6804) (@lem311000 A lt2 y P _6804)). Qed.
Lemma lem311003 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem311004 (x : Prop) : (x = x) = True.
Proof. exact (@lem311003 Prop x). Qed.
Lemma lem311005 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term172 A lt2 y P _6804) = (term172 A lt2 y P _6804)) = True.
Proof. exact (@lem311004 (term172 A lt2 y P _6804)). Qed.
Lemma lem311006 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : ((term159 A P lt2 y _6804) = (term172 A lt2 y P _6804)) = True.
Proof. exact (TRANS (@lem311001 A lt2 y P _6804) (@lem311005 A lt2 y P _6804)). Qed.
Lemma lem311007 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : True = ((term159 A P lt2 y _6804) = (term172 A lt2 y P _6804)).
Proof. exact (SYM (@lem311006 A lt2 y P _6804)). Qed.
Lemma lem311008 {A : Type'} (lt2 : type1402 A) (y : A -> A) (P : A -> Prop) (_6804 : A) : (term159 A P lt2 y _6804) = (term172 A lt2 y P _6804).
Proof. exact (EQ_MP (@lem311007 A lt2 y P _6804) (@lem0)). Qed.
Lemma lem311009 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term172 A lt2 y P _6804.
Proof. exact (EQ_MP (@lem311008 A lt2 y P _6804) (@lem310907 A _6804 lt2 P y h1)). Qed.
Lemma lem311011 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem311012 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6804 : A) : (term172 A lt2 y P _6804) = (term175 A P lt2 y _6804).
Proof. exact (@lem311011 (term54 A P _6804) (term154 A lt2 y _6804)). Qed.
Lemma lem311014 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem311015 {A : Type'} (P : A -> Prop) (_6804 : A) : (term49 A P _6804) = (P _6804).
Proof. exact (@lem311014 (P _6804)). Qed.
Lemma lem311016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311017 {A : Type'} (P : A -> Prop) (_6804 : A) : (term168 A P _6804) = (term23 A P _6804).
Proof. exact (MK_COMB (@lem311016) (@lem311015 A P _6804)). Qed.
Lemma lem311018 {A : Type'} (lt2 : type1402 A) (y : A -> A) (_6804 : A) : (term154 A lt2 y _6804) = (term154 A lt2 y _6804).
Proof. exact (eq_refl (term154 A lt2 y _6804)). Qed.
Lemma lem311019 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6804 : A) : (term175 A P lt2 y _6804) = (term176 A P lt2 y _6804).
Proof. exact (MK_COMB (@lem311017 A P _6804) (@lem311018 A lt2 y _6804)). Qed.
Lemma lem311020 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (_6804 : A) : (term172 A lt2 y P _6804) = (term176 A P lt2 y _6804).
Proof. exact (TRANS (@lem311012 A P lt2 y _6804) (@lem311019 A P lt2 y _6804)). Qed.
Lemma lem311023 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term176 A P lt2 y _6804.
Proof. exact (EQ_MP (@lem311020 A P lt2 y _6804) (@lem311009 A _6804 lt2 P y h1)). Qed.
Lemma lem311024 {A : Type'} (_6804 : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term176 A P lt2 y _6804.
Proof. exact (@lem311023 A _6804 lt2 P y h1). Qed.
Lemma lem311025 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (h1 : term113 A lt2 P y) : term176 A P lt2 y x.
Proof. exact (@lem311024 A x lt2 P y h1). Qed.
Lemma lem311028 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term154 A lt2 y x.
Proof. exact (@lem311025 A x lt2 P y h1 (@lem310980 A P lt2 x h2)). Qed.
Lemma lem311029 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term177 A lt2 y x.
Proof. exact (fun h0 : term178 A lt2 y x => @lem311028 A y P lt2 x h1 h2). Qed.
Lemma lem311031 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem311032 {A : Type'} (lt2 : type1402 A) (y : A -> A) (x : A) : (term177 A lt2 y x) = (term154 A lt2 y x).
Proof. exact (@lem311031 (term154 A lt2 y x)). Qed.
Lemma lem311033 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term154 A lt2 y x.
Proof. exact (EQ_MP (@lem311032 A lt2 y x) (@lem311029 A y P lt2 x h1 h2)). Qed.
Lemma lem311035 (a : Prop) (b : Prop) : (term179 a b) = (term180 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem311036 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6805 : A) (x : A) : (term118 A P lt2 _6805 x) = (term117 A P lt2 _6805 x).
Proof. exact (@lem311035 (P _6805) (lt2 _6805 x)). Qed.
Lemma lem311038 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem311039 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6805 : A) (x : A) : (term117 A P lt2 _6805 x) = (term181 A P lt2 _6805 x).
Proof. exact (@lem311038 (term122 A P lt2 _6805 x)). Qed.
Lemma lem311040 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (_6805 : A) (x : A) : (term118 A P lt2 _6805 x) = (term181 A P lt2 _6805 x).
Proof. exact (TRANS (@lem311036 A P lt2 _6805 x) (@lem311039 A P lt2 _6805 x)). Qed.
Lemma lem311042 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term182 A P lt2 y x.
Proof. exact (conj (@lem310973 A y P lt2 x h1 h2) (@lem311033 A y P lt2 x h1 h2)). Qed.
Lemma lem311044 {A : Type'} (_6805 : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term181 A P lt2 _6805 x.
Proof. exact (EQ_MP (@lem311040 A P lt2 _6805 x) (@lem310901 A _6805 P lt2 x h1)). Qed.
Lemma lem311045 {A : Type'} (_6805 : A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term181 A P lt2 _6805 x.
Proof. exact (@lem311044 A _6805 P lt2 x h1). Qed.
Lemma lem311046 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term48 A P lt2 x) : term183 A P lt2 y x.
Proof. exact (@lem311045 A (y x) P lt2 x h1). Qed.
Lemma lem311049 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : False.
Proof. exact (@lem311046 A y P lt2 x h2 (@lem311042 A y P lt2 x h1 h2)). Qed.
Lemma lem311050 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : term184.
Proof. exact (fun h0 : ~ False => @lem311049 A y P lt2 x h1 h2). Qed.
Lemma lem311052 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem311053 : term184 = False.
Proof. exact (@lem311052 False). Qed.
Lemma lem311054 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : False.
Proof. exact (EQ_MP (@lem311053) (@lem311050 A y P lt2 x h1 h2)). Qed.
Lemma lem311055 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : (term113 A lt2 P y) = False.
Proof. exact (prop_ext (fun h3 : term113 A lt2 P y => @lem311054 A y P lt2 x h1 h2) (fun h3 : False => @lem310837 A lt2 P y h1)). Qed.
Lemma lem311056 {A : Type'} (y : A -> A) (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term113 A lt2 P y) (h2 : term48 A P lt2 x) : False.
Proof. exact (EQ_MP (@lem311055 A y P lt2 x h1 h2) (@lem310837 A lt2 P y h1)). Qed.
Lemma lem311057 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term9 A lt2 P) (h2 : term48 A P lt2 x) : False.
Proof. exact (ex_elim (@lem310669 A lt2 P h1) (fun y : A -> A => fun h0 : term115 A lt2 P y => @lem311056 A y P lt2 x h0 h2)). Qed.
Lemma lem311058 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term9 A lt2 P) (h2 : term48 A P lt2 x) : (term48 A P lt2 x) = False.
Proof. exact (prop_ext (fun h3 : term48 A P lt2 x => @lem311057 A P lt2 x h1 h2) (fun h3 : False => @lem310490 A P lt2 x h2)). Qed.
Lemma lem311059 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (h1 : term9 A lt2 P) (h2 : term48 A P lt2 x) : False.
Proof. exact (EQ_MP (@lem311058 A P lt2 x h1 h2) (@lem310490 A P lt2 x h2)). Qed.
Lemma lem311060 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term47 A P lt2 x.
Proof. exact (fun h0 : term48 A P lt2 x => @lem311059 A P lt2 x h1 h0). Qed.
Lemma lem311061 {A : Type'} (x : A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term39 A P lt2 x.
Proof. exact (EQ_MP (@lem310489 A P lt2 x) (@lem311060 A x lt2 P h1)). Qed.
Lemma lem311066 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term10 A P lt2.
Proof. exact (fun x : A => @lem311061 A x lt2 P h1). Qed.
Lemma lem311067 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term22 A P lt2.
Proof. exact (fun h0 : term9 A lt2 P => @lem311066 A lt2 P h0). Qed.
Lemma lem311068 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term24 A a P lt2.
Proof. exact (fun h0 : P a => @lem311067 A P lt2). Qed.
Lemma lem311073 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term28 A P lt2.
Proof. exact (fun a : A => @lem311068 A a P lt2). Qed.
Lemma lem311078 {A : Type'} (lt2 : type1402 A) : term32 A lt2.
Proof. exact (fun P : A -> Prop => @lem311073 A P lt2). Qed.
Lemma lem311083 {A : Type'} : term36 A.
Proof. exact (fun lt2 : type1402 A => @lem311078 A lt2). Qed.
Lemma lem311084 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem310483 A) (@lem311083 A)). Qed.
Lemma lem311085 {A : Type'} (lt2 : type1402 A) : term185 A lt2.
Proof. exact (@lem311084 A lt2). Qed.
Lemma lem311086 {A : Type'} (lt2 : type1402 A) : (term185 A lt2) = (term31 A lt2).
Proof. exact (eq_refl (term185 A lt2)). Qed.
Lemma lem311087 {A : Type'} (lt2 : type1402 A) : term31 A lt2.
Proof. exact (EQ_MP (@lem311086 A lt2) (@lem311085 A lt2)). Qed.
Lemma lem311088 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : term186 A lt2 P.
Proof. exact (@lem311087 A lt2 P). Qed.
Lemma lem311089 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term186 A lt2 P) = (term27 A P lt2).
Proof. exact (eq_refl (term186 A lt2 P)). Qed.
Lemma lem311090 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term27 A P lt2.
Proof. exact (EQ_MP (@lem311089 A P lt2) (@lem311088 A lt2 P)). Qed.
Lemma lem311091 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (a : A) : term187 A P lt2 a.
Proof. exact (@lem311090 A P lt2 a). Qed.
Lemma lem311092 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : (term187 A P lt2 a) = (term14 A a P lt2).
Proof. exact (eq_refl (term187 A P lt2 a)). Qed.
Lemma lem311093 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term14 A a P lt2.
Proof. exact (EQ_MP (@lem311092 A a P lt2) (@lem311091 A P lt2 a)). Qed.
Lemma lem311095 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) : term14 A a P lt2.
Proof. exact (@lem310271 A a P lt2 (@lem311093 A a P lt2)). Qed.
Lemma lem311096 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : P a) : term21 A P lt2.
Proof. exact (@lem311095 A a P lt2 (@lem310249 A P a h1)). Qed.
Lemma lem311097 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term12 A P lt2.
Proof. exact (@lem311096 A lt2 P a h2 (@lem310247 A lt2 P h1)). Qed.
Lemma lem311098 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term13 A P lt2) (h2 : term9 A lt2 P) (h3 : P a) : False.
Proof. exact (@lem311097 A lt2 P a h2 h3 (@lem310255 A P lt2 h1)). Qed.
Lemma lem311099 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term13 A P lt2) (h2 : term9 A lt2 P) (h3 : P a) : (term13 A P lt2) = False.
Proof. exact (prop_ext (fun h4 : term13 A P lt2 => @lem311098 A lt2 P a h1 h2 h3) (fun h4 : False => @lem310255 A P lt2 h1)). Qed.
Lemma lem311100 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term13 A P lt2) (h2 : term9 A lt2 P) (h3 : P a) : False.
Proof. exact (EQ_MP (@lem311099 A lt2 P a h1 h2 h3) (@lem310255 A P lt2 h1)). Qed.
Lemma lem311101 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term12 A P lt2.
Proof. exact (fun h0 : term13 A P lt2 => @lem311100 A lt2 P a h0 h1 h2). Qed.
Lemma lem311102 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term10 A P lt2.
Proof. exact (EQ_MP (@lem310254 A P lt2) (@lem311101 A lt2 P a h1 h2)). Qed.
Lemma lem311106 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem309995 A B P) (@lem309994 A B P)). Qed.
Lemma lem311107 {A : Type'} (P : type1402 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem311106 A A P). Qed.
Lemma lem311108 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term188 A P lt2) = (term189 A P lt2).
Proof. exact (@lem311107 A (term190 A P lt2)). Qed.
Lemma lem311109 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term191 A P lt2 x) = (term38 A P lt2 x).
Proof. exact (eq_refl (term191 A P lt2 x)). Qed.
Lemma lem311110 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem311111 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term192 A P lt2 x y) = (term124 A P lt2 x y).
Proof. exact (MK_COMB (@lem311109 A P lt2 x) (@lem311110 A y)). Qed.
Lemma lem311112 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term124 A P lt2 x y) = (term37 A P lt2 y x).
Proof. exact (eq_refl (term124 A P lt2 x y)). Qed.
Lemma lem311113 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A) (x : A) : (term192 A P lt2 x y) = (term37 A P lt2 y x).
Proof. exact (TRANS (@lem311111 A P lt2 x y) (@lem311112 A P lt2 y x)). Qed.
Lemma lem311114 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term193 A P lt2 x) = (term38 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem311113 A P lt2 y x)). Qed.
Lemma lem311115 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311116 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term194 A P lt2 x) = (term39 A P lt2 x).
Proof. exact (MK_COMB (@lem311115 A) (@lem311114 A P lt2 x)). Qed.
Lemma lem311117 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term195 A P lt2) = (term40 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem311116 A P lt2 x)). Qed.
Lemma lem311118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311119 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term188 A P lt2) = (term10 A P lt2).
Proof. exact (MK_COMB (@lem311118 A) (@lem311117 A P lt2)). Qed.
Lemma lem311120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem311121 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term196 A P lt2) = (term197 A P lt2).
Proof. exact (MK_COMB (@lem311120) (@lem311119 A P lt2)). Qed.
Lemma lem311122 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term191 A P lt2 x) = (term38 A P lt2 x).
Proof. exact (eq_refl (term191 A P lt2 x)). Qed.
Lemma lem311123 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem311124 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (x : A) : (term198 A P lt2 y x) = (term199 A P lt2 y x).
Proof. exact (MK_COMB (@lem311122 A P lt2 x) (@lem311123 A y x)). Qed.
Lemma lem311125 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (x : A) : (term199 A P lt2 y x) = (term200 A P lt2 y x).
Proof. exact (eq_refl (term199 A P lt2 y x)). Qed.
Lemma lem311126 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) (x : A) : (term198 A P lt2 y x) = (term200 A P lt2 y x).
Proof. exact (TRANS (@lem311124 A P lt2 y x) (@lem311125 A P lt2 y x)). Qed.
Lemma lem311127 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) : (term201 A P lt2 y) = (term202 A P lt2 y).
Proof. exact (fun_ext (fun x : A => @lem311126 A P lt2 y x)). Qed.
Lemma lem311128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311129 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (y : A -> A) : (term203 A P lt2 y) = (term204 A P lt2 y).
Proof. exact (MK_COMB (@lem311128 A) (@lem311127 A P lt2 y)). Qed.
Lemma lem311130 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term205 A P lt2) = (term206 A P lt2).
Proof. exact (fun_ext (fun y : A -> A => @lem311129 A P lt2 y)). Qed.
Lemma lem311131 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem311132 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term189 A P lt2) = (term207 A P lt2).
Proof. exact (MK_COMB (@lem311131 A) (@lem311130 A P lt2)). Qed.
Lemma lem311133 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : ((term188 A P lt2) = (term189 A P lt2)) = ((term10 A P lt2) = (term207 A P lt2)).
Proof. exact (MK_COMB (@lem311121 A P lt2) (@lem311132 A P lt2)). Qed.
Lemma lem311134 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term10 A P lt2) = (term207 A P lt2).
Proof. exact (EQ_MP (@lem311133 A P lt2) (@lem311108 A P lt2)). Qed.
Lemma lem311147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311148 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term208 A P lt2) = (term209 A P lt2).
Proof. exact (MK_COMB (@lem311147) (@lem311134 A P lt2)). Qed.
Lemma lem311157 {A : Type'} (lt2 : type1402 A) : (term2 A lt2) = (term2 A lt2).
Proof. exact (eq_refl (term2 A lt2)). Qed.
Lemma lem311158 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term210 A P lt2) = (term211 A P lt2).
Proof. exact (MK_COMB (@lem311148 A P lt2) (@lem311157 A lt2)). Qed.
Lemma lem311161 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term211 A P lt2) = (term210 A P lt2).
Proof. exact (SYM (@lem311158 A P lt2)). Qed.
Lemma lem311162 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term207 A P lt2) : term207 A P lt2.
Proof. exact (h1). Qed.
Lemma lem311163 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term204 A P lt2 f.
Proof. exact (h1). Qed.
Lemma lem311164 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term212 A a f s.
Proof. exact (h1). Qed.
Lemma lem311174 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term213 A f s.
Proof. exact (proj2 (@lem311164 A a f s h1)). Qed.
Lemma lem311175 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term214 A f s n.
Proof. exact (@lem311174 A a f s h1 n). Qed.
Lemma lem311176 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term214 A f s n) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl (term214 A f s n)). Qed.
Lemma lem311184 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem311176 A f s n) (@lem311175 A n a f s h1)). Qed.
Lemma lem311185 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem311186 {A : Type'} (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term217 A lt2 s n) = (term218 A lt2 f s n).
Proof. exact (MK_COMB (@lem311185 A lt2) (@lem311184 A n a f s h1)). Qed.
Lemma lem311187 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (s n).
Proof. exact (eq_refl (s n)). Qed.
Lemma lem311188 {A : Type'} (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term219 A lt2 s n) = (term220 A lt2 f s n).
Proof. exact (MK_COMB (@lem311186 A lt2 n a f s h1) (@lem311187 A s n)). Qed.
Lemma lem311189 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term221 A lt2 s) = (term222 A lt2 f s).
Proof. exact (fun_ext (fun n : nat => @lem311188 A lt2 n a f s h1)). Qed.
Lemma lem311190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311191 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term3 A lt2 s) = (term223 A lt2 f s).
Proof. exact (MK_COMB (@lem311190) (@lem311189 A lt2 a f s h1)). Qed.
Lemma lem311196 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term223 A lt2 f s) = (term3 A lt2 s).
Proof. exact (SYM (@lem311191 A lt2 a f s h1)). Qed.
Lemma lem311197 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term224 A P lt2 s) : term224 A P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311209 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem311210 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term223 A lt2 f s) = (term225 A lt2 f s).
Proof. exact (@lem311209 (term223 A lt2 f s)). Qed.
Lemma lem311211 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term225 A lt2 f s) = (term223 A lt2 f s).
Proof. exact (SYM (@lem311210 A lt2 f s)). Qed.
Lemma lem311212 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (h1 : term226 A lt2 f s) : term226 A lt2 f s.
Proof. exact (h1). Qed.
Lemma lem311215 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term227 A a f P lt2 s) : term227 A a f P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311216 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term228 A a f P lt2 s.
Proof. exact (fun h0 : term227 A a f P lt2 s => @lem311215 A a f P lt2 s h0). Qed.
Lemma lem311217 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A a f P lt2 s) : term228 A a f P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311218 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term227 A a f P lt2 s) : term227 A a f P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311219 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term227 A a f P lt2 s) (h2 : term228 A a f P lt2 s) : term227 A a f P lt2 s.
Proof. exact (@lem311217 A a f P lt2 s h2 (@lem311218 A a f P lt2 s h1)). Qed.
Lemma lem311220 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term227 A a f P lt2 s) : term229 A a f P lt2 s.
Proof. exact (fun h0 : term228 A a f P lt2 s => @lem311219 A a f P lt2 s h1 h0). Qed.
Lemma lem311221 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A a f P lt2 s) : term228 A a f P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311222 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term227 A a f P lt2 s) (h2 : term228 A a f P lt2 s) : term227 A a f P lt2 s.
Proof. exact (@lem311220 A a f P lt2 s h1 (@lem311221 A a f P lt2 s h2)). Qed.
Lemma lem311223 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A a f P lt2 s) : term228 A a f P lt2 s.
Proof. exact (fun h0 : term227 A a f P lt2 s => @lem311222 A a f P lt2 s h0 h1). Qed.
Lemma lem311224 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term230 A a f P lt2 s.
Proof. exact (fun h0 : term228 A a f P lt2 s => @lem311223 A a f P lt2 s h0). Qed.
Lemma lem311227 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term228 A a f P lt2 s.
Proof. exact (@lem311224 A a f P lt2 s (@lem311216 A a f P lt2 s)). Qed.
Lemma lem311228 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term228 A a f P lt2 s.
Proof. exact (@lem311227 A a f P lt2 s). Qed.
Lemma lem311314 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem311315 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term231 A P lt2 s) = (term232 A P lt2 s).
Proof. exact (@lem311314 (term224 A P lt2 s)). Qed.
Lemma lem311317 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem311318 (P : nat -> Prop) (Q : nat -> Prop) : (term233 P Q) = (term234 P Q).
Proof. exact (@lem311317 nat P Q). Qed.
Lemma lem311319 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term235 A P lt2 s) = (term236 A P lt2 s).
Proof. exact (@lem311318 (term237 A P s) (term221 A lt2 s)). Qed.
Lemma lem311320 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term238 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term238 A P s n)). Qed.
Lemma lem311321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem311322 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term240 A P s n) = (term241 A P s n).
Proof. exact (MK_COMB (@lem311321) (@lem311320 A P s n)). Qed.
Lemma lem311323 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term242 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term242 A lt2 s n)). Qed.
Lemma lem311324 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term243 A P lt2 s n) = (term244 A P lt2 s n).
Proof. exact (MK_COMB (@lem311322 A P s n) (@lem311323 A lt2 s n)). Qed.
Lemma lem311325 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term245 A P lt2 s) = (term246 A P lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem311324 A P lt2 s n)). Qed.
Lemma lem311326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311327 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term235 A P lt2 s) = (term224 A P lt2 s).
Proof. exact (MK_COMB (@lem311326) (@lem311325 A P lt2 s)). Qed.
Lemma lem311328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem311329 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term247 A P lt2 s) = (term248 A P lt2 s).
Proof. exact (MK_COMB (@lem311328) (@lem311327 A P lt2 s)). Qed.
Lemma lem311330 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term238 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term238 A P s n)). Qed.
Lemma lem311331 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term249 A P s) = (term237 A P s).
Proof. exact (fun_ext (fun n : nat => @lem311330 A P s n)). Qed.
Lemma lem311332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311333 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term250 A P s) = (term251 A P s).
Proof. exact (MK_COMB (@lem311332) (@lem311331 A P s)). Qed.
Lemma lem311334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem311335 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term252 A P s) = (term253 A P s).
Proof. exact (MK_COMB (@lem311334) (@lem311333 A P s)). Qed.
Lemma lem311336 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term242 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term242 A lt2 s n)). Qed.
Lemma lem311337 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term254 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem311336 A lt2 s n)). Qed.
Lemma lem311338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311339 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term255 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem311338) (@lem311337 A lt2 s)). Qed.
Lemma lem311340 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term236 A P lt2 s) = (term256 A P lt2 s).
Proof. exact (MK_COMB (@lem311335 A P s) (@lem311339 A lt2 s)). Qed.
Lemma lem311341 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : ((term235 A P lt2 s) = (term236 A P lt2 s)) = ((term224 A P lt2 s) = (term256 A P lt2 s)).
Proof. exact (MK_COMB (@lem311329 A P lt2 s) (@lem311340 A P lt2 s)). Qed.
Lemma lem311342 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term224 A P lt2 s) = (term256 A P lt2 s).
Proof. exact (EQ_MP (@lem311341 A P lt2 s) (@lem311319 A P lt2 s)). Qed.
Lemma lem311353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311354 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term232 A P lt2 s) = (term257 A P lt2 s).
Proof. exact (MK_COMB (@lem311353) (@lem311342 A P lt2 s)). Qed.
Lemma lem311355 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term231 A P lt2 s) = (term257 A P lt2 s).
Proof. exact (TRANS (@lem311315 A P lt2 s) (@lem311354 A P lt2 s)). Qed.
Lemma lem311356 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term258 A lt2 f s) = (term258 A lt2 f s).
Proof. exact (eq_refl (term258 A lt2 f s)). Qed.
Lemma lem311357 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term259 A f P lt2 s) = (term260 A f P lt2 s).
Proof. exact (MK_COMB (@lem311356 A lt2 f s) (@lem311355 A P lt2 s)). Qed.
Lemma lem311360 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (eq_refl (term261 A a f s)). Qed.
Lemma lem311361 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term262 A a f P lt2 s) = (term263 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311360 A a f s) (@lem311357 A f P lt2 s)). Qed.
Lemma lem311364 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (eq_refl (term264 A P lt2 f)). Qed.
Lemma lem311365 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term265 A a f P lt2 s) = (term266 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311364 A P lt2 f) (@lem311361 A a f P lt2 s)). Qed.
Lemma lem311368 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (eq_refl (term20 A lt2 P)). Qed.
Lemma lem311369 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term267 A a f P lt2 s) = (term268 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311368 A lt2 P) (@lem311365 A a f P lt2 s)). Qed.
Lemma lem311372 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem311373 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term227 A a f P lt2 s) = (term269 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311372 A P a) (@lem311369 A a f P lt2 s)). Qed.
Lemma lem311376 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term270 A f P lt2 s) = (term271 A f P lt2 s).
Proof. exact (fun_ext (fun a : A => @lem311373 A a f P lt2 s)). Qed.
Lemma lem311377 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311378 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term272 A f P lt2 s) = (term273 A f P lt2 s).
Proof. exact (MK_COMB (@lem311377 A) (@lem311376 A f P lt2 s)). Qed.
Lemma lem311383 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term274 A P lt2 s) = (term275 A P lt2 s).
Proof. exact (fun_ext (fun f : A -> A => @lem311378 A f P lt2 s)). Qed.
Lemma lem311384 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem311385 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term276 A P lt2 s) = (term277 A P lt2 s).
Proof. exact (MK_COMB (@lem311384 A) (@lem311383 A P lt2 s)). Qed.
Lemma lem311390 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term278 A lt2 s) = (term279 A lt2 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem311385 A P lt2 s)). Qed.
Lemma lem311391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem311392 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term280 A lt2 s) = (term281 A lt2 s).
Proof. exact (MK_COMB (@lem311391 A) (@lem311390 A lt2 s)). Qed.
Lemma lem311397 {A : Type'} (s : nat -> A) : (term282 A s) = (term283 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem311392 A lt2 s)). Qed.
Lemma lem311398 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem311399 {A : Type'} (s : nat -> A) : (term284 A s) = (term285 A s).
Proof. exact (MK_COMB (@lem311398 A) (@lem311397 A s)). Qed.
Lemma lem311404 {A : Type'} : (term286 A) = (term287 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem311399 A s)). Qed.
Lemma lem311405 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem311414 {A : Type'} : (term288 A) = (term289 A).
Proof. exact (MK_COMB (@lem311405 A) (@lem311404 A)). Qed.
Lemma lem311415 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem311416 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem311415 A lt2 s n)). Qed.
Lemma lem311417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311418 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem311417) (@lem311416 A lt2 s)). Qed.
Lemma lem311419 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term239 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term239 A P s n)). Qed.
Lemma lem311420 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term237 A P s) = (term237 A P s).
Proof. exact (fun_ext (fun n : nat => @lem311419 A P s n)). Qed.
Lemma lem311421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311422 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term251 A P s) = (term251 A P s).
Proof. exact (MK_COMB (@lem311421) (@lem311420 A P s)). Qed.
Lemma lem311423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem311424 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term253 A P s) = (term253 A P s).
Proof. exact (MK_COMB (@lem311423) (@lem311422 A P s)). Qed.
Lemma lem311425 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term256 A P lt2 s) = (term256 A P lt2 s).
Proof. exact (MK_COMB (@lem311424 A P s) (@lem311418 A lt2 s)). Qed.
Lemma lem311426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311427 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term257 A P lt2 s) = (term257 A P lt2 s).
Proof. exact (MK_COMB (@lem311426) (@lem311425 A P lt2 s)). Qed.
Lemma lem311428 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term220 A lt2 f s n) = (term220 A lt2 f s n).
Proof. exact (eq_refl (term220 A lt2 f s n)). Qed.
Lemma lem311429 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term222 A lt2 f s) = (term222 A lt2 f s).
Proof. exact (fun_ext (fun n : nat => @lem311428 A lt2 f s n)). Qed.
Lemma lem311430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311431 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term223 A lt2 f s) = (term223 A lt2 f s).
Proof. exact (MK_COMB (@lem311430) (@lem311429 A lt2 f s)). Qed.
Lemma lem311432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311433 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term226 A lt2 f s) = (term226 A lt2 f s).
Proof. exact (MK_COMB (@lem311432) (@lem311431 A lt2 f s)). Qed.
Lemma lem311434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311435 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term258 A lt2 f s) = (term258 A lt2 f s).
Proof. exact (MK_COMB (@lem311434) (@lem311433 A lt2 f s)). Qed.
Lemma lem311436 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term260 A f P lt2 s) = (term260 A f P lt2 s).
Proof. exact (MK_COMB (@lem311435 A lt2 f s) (@lem311427 A P lt2 s)). Qed.
Lemma lem311437 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : ((term215 A s n) = (term216 A f s n)) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl ((term215 A s n) = (term216 A f s n))). Qed.
Lemma lem311438 {A : Type'} (f : A -> A) (s : nat -> A) : (term290 A f s) = (term290 A f s).
Proof. exact (fun_ext (fun n : nat => @lem311437 A f s n)). Qed.
Lemma lem311439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311440 {A : Type'} (f : A -> A) (s : nat -> A) : (term213 A f s) = (term213 A f s).
Proof. exact (MK_COMB (@lem311439) (@lem311438 A f s)). Qed.
Lemma lem311443 {A : Type'} (s : nat -> A) (a : A) : (term291 A s a) = (term291 A s a).
Proof. exact (eq_refl (term291 A s a)). Qed.
Lemma lem311444 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term212 A a f s) = (term212 A a f s).
Proof. exact (MK_COMB (@lem311443 A s a) (@lem311440 A f s)). Qed.
Lemma lem311445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311446 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (MK_COMB (@lem311445) (@lem311444 A a f s)). Qed.
Lemma lem311447 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term263 A a f P lt2 s) = (term263 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311446 A a f s) (@lem311436 A f P lt2 s)). Qed.
Lemma lem311456 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term200 A P lt2 f x).
Proof. exact (eq_refl (term200 A P lt2 f x)). Qed.
Lemma lem311457 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term202 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem311456 A P lt2 f x)). Qed.
Lemma lem311458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311459 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term204 A P lt2 f).
Proof. exact (MK_COMB (@lem311458 A) (@lem311457 A P lt2 f)). Qed.
Lemma lem311460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311461 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (MK_COMB (@lem311460) (@lem311459 A P lt2 f)). Qed.
Lemma lem311462 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term266 A a f P lt2 s) = (term266 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311461 A P lt2 f) (@lem311447 A a f P lt2 s)). Qed.
Lemma lem311469 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term41 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term41 A lt2 x P y)). Qed.
Lemma lem311470 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term42 A lt2 x P) = (term42 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem311469 A lt2 x P y)). Qed.
Lemma lem311471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311472 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term43 A lt2 x P) = (term43 A lt2 x P).
Proof. exact (MK_COMB (@lem311471 A) (@lem311470 A lt2 x P)). Qed.
Lemma lem311475 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem311476 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term45 A lt2 x P) = (term45 A lt2 x P).
Proof. exact (MK_COMB (@lem311475 A P x) (@lem311472 A lt2 x P)). Qed.
Lemma lem311477 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term46 A lt2 P) = (term46 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem311476 A lt2 x P)). Qed.
Lemma lem311478 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311479 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term8 A lt2 P) = (term8 A lt2 P).
Proof. exact (MK_COMB (@lem311478 A) (@lem311477 A lt2 P)). Qed.
Lemma lem311480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311481 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term9 A lt2 P).
Proof. exact (MK_COMB (@lem311480) (@lem311479 A lt2 P)). Qed.
Lemma lem311482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem311483 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (MK_COMB (@lem311482) (@lem311481 A lt2 P)). Qed.
Lemma lem311484 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term268 A a f P lt2 s) = (term268 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311483 A lt2 P) (@lem311462 A a f P lt2 s)). Qed.
Lemma lem311487 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem311488 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term269 A a f P lt2 s) = (term269 A a f P lt2 s).
Proof. exact (MK_COMB (@lem311487 A P a) (@lem311484 A a f P lt2 s)). Qed.
Lemma lem311489 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term271 A f P lt2 s) = (term271 A f P lt2 s).
Proof. exact (fun_ext (fun a : A => @lem311488 A a f P lt2 s)). Qed.
Lemma lem311490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311491 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term273 A f P lt2 s) = (term273 A f P lt2 s).
Proof. exact (MK_COMB (@lem311490 A) (@lem311489 A f P lt2 s)). Qed.
Lemma lem311492 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term275 A P lt2 s) = (term275 A P lt2 s).
Proof. exact (fun_ext (fun f : A -> A => @lem311491 A f P lt2 s)). Qed.
Lemma lem311493 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem311494 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term277 A P lt2 s) = (term277 A P lt2 s).
Proof. exact (MK_COMB (@lem311493 A) (@lem311492 A P lt2 s)). Qed.
Lemma lem311495 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term279 A lt2 s) = (term279 A lt2 s).
Proof. exact (fun_ext (fun P : A -> Prop => @lem311494 A P lt2 s)). Qed.
Lemma lem311496 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem311497 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term281 A lt2 s) = (term281 A lt2 s).
Proof. exact (MK_COMB (@lem311496 A) (@lem311495 A lt2 s)). Qed.
Lemma lem311498 {A : Type'} (s : nat -> A) : (term283 A s) = (term283 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem311497 A lt2 s)). Qed.
Lemma lem311499 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem311500 {A : Type'} (s : nat -> A) : (term285 A s) = (term285 A s).
Proof. exact (MK_COMB (@lem311499 A) (@lem311498 A s)). Qed.
Lemma lem311501 {A : Type'} : (term287 A) = (term287 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem311500 A s)). Qed.
Lemma lem311502 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem311503 {A : Type'} : (term289 A) = (term289 A).
Proof. exact (MK_COMB (@lem311502 A) (@lem311501 A)). Qed.
Lemma lem311600 {A : Type'} : (term288 A) = (term289 A).
Proof. exact (TRANS (@lem311414 A) (@lem311503 A)). Qed.
Lemma lem311601 {A : Type'} : (term289 A) = (term288 A).
Proof. exact (SYM (@lem311600 A)). Qed.
Lemma lem311603 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem311604 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term204 A P lt2 f.
Proof. exact (h1). Qed.
Lemma lem311606 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (h1 : term226 A lt2 f s) : term226 A lt2 f s.
Proof. exact (h1). Qed.
Lemma lem311607 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term256 A P lt2 s.
Proof. exact (h1). Qed.
Lemma lem311618 {A : Type'} (P : A -> Prop) (y : A) : (term49 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem311620 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term50 A lt2 y x) = (term50 A lt2 y x).
Proof. exact (eq_refl (term50 A lt2 y x)). Qed.
Lemma lem311621 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (MK_COMB (@lem311620 A lt2 y x) (@lem311618 A P y)). Qed.
Lemma lem311622 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term51 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term54 A P y)). Qed.
Lemma lem311623 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem311622 A lt2 x P y) (@lem311621 A lt2 x P y)). Qed.
Lemma lem311624 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem311625 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem311624 A (term42 A lt2 x P)). Qed.
Lemma lem311626 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term59 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term59 A lt2 x P y)). Qed.
Lemma lem311627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311628 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term53 A lt2 x P y).
Proof. exact (MK_COMB (@lem311627) (@lem311626 A lt2 x P y)). Qed.
Lemma lem311629 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem311628 A lt2 x P y) (@lem311623 A lt2 x P y)). Qed.
Lemma lem311630 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term61 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem311629 A lt2 x P y)). Qed.
Lemma lem311631 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311632 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem311631 A) (@lem311630 A lt2 x P)). Qed.
Lemma lem311633 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (TRANS (@lem311625 A lt2 x P) (@lem311632 A lt2 x P)). Qed.
Lemma lem311635 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem311636 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem311635 A P x) (@lem311633 A lt2 x P)). Qed.
Lemma lem311637 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term65 A lt2 x P).
Proof. exact (@lem17045 (P x) (term43 A lt2 x P)). Qed.
Lemma lem311638 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem311637 A lt2 x P) (@lem311636 A lt2 x P)). Qed.
Lemma lem311639 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem311640 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term70 A lt2 P).
Proof. exact (@lem311639 A (term46 A lt2 P)). Qed.
Lemma lem311641 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term71 A lt2 P x) = (term45 A lt2 x P).
Proof. exact (eq_refl (term71 A lt2 P x)). Qed.
Lemma lem311642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311643 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term67 A lt2 x P).
Proof. exact (MK_COMB (@lem311642) (@lem311641 A lt2 x P)). Qed.
Lemma lem311644 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem311643 A lt2 x P) (@lem311638 A lt2 x P)). Qed.
Lemma lem311645 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term74 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem311644 A lt2 x P)). Qed.
Lemma lem311646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311647 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term70 A lt2 P) = (term75 A lt2 P).
Proof. exact (MK_COMB (@lem311646 A) (@lem311645 A lt2 P)). Qed.
Lemma lem311648 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term75 A lt2 P).
Proof. exact (TRANS (@lem311640 A lt2 P) (@lem311647 A lt2 P)). Qed.
Lemma lem311731 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem311732 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem311731 A P Q). Qed.
Lemma lem311733 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term79 A lt2 x P).
Proof. exact (@lem311732 A (term54 A P x) (term62 A lt2 x P)). Qed.
Lemma lem311734 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem311735 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term81 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem311734 A lt2 x P y)). Qed.
Lemma lem311736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311737 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem311736 A) (@lem311735 A lt2 x P)). Qed.
Lemma lem311738 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem311739 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem311738 A P x) (@lem311737 A lt2 x P)). Qed.
Lemma lem311740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem311741 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term83 A lt2 x P) = (term84 A lt2 x P).
Proof. exact (MK_COMB (@lem311740) (@lem311739 A lt2 x P)). Qed.
Lemma lem311742 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem311743 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem311744 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term85 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (MK_COMB (@lem311743 A P x) (@lem311742 A lt2 x P y)). Qed.
Lemma lem311745 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term87 A lt2 x P) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem311744 A lt2 x P y)). Qed.
Lemma lem311746 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311747 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term79 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem311746 A) (@lem311745 A lt2 x P)). Qed.
Lemma lem311748 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term78 A lt2 x P) = (term79 A lt2 x P)) = ((term66 A lt2 x P) = (term89 A lt2 x P)).
Proof. exact (MK_COMB (@lem311741 A lt2 x P) (@lem311747 A lt2 x P)). Qed.
Lemma lem311749 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term66 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (EQ_MP (@lem311748 A lt2 x P) (@lem311733 A lt2 x P)). Qed.
Lemma lem311750 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem311749 A lt2 x P)). Qed.
Lemma lem311751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311752 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem311751 A) (@lem311750 A lt2 P)). Qed.
Lemma lem311754 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem311755 {A : Type'} (P : type1402 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem311754 A A P). Qed.
Lemma lem311756 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term97 A lt2 P).
Proof. exact (@lem311755 A (term98 A lt2 P)). Qed.
Lemma lem311757 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem311758 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem311759 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term101 A lt2 x P y).
Proof. exact (MK_COMB (@lem311757 A lt2 x P) (@lem311758 A y)). Qed.
Lemma lem311760 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term101 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (eq_refl (term101 A lt2 x P y)). Qed.
Lemma lem311761 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term86 A lt2 x P y).
Proof. exact (TRANS (@lem311759 A lt2 x P y) (@lem311760 A lt2 x P y)). Qed.
Lemma lem311762 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term102 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem311761 A lt2 x P y)). Qed.
Lemma lem311763 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem311764 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term103 A lt2 P x) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem311763 A) (@lem311762 A lt2 x P)). Qed.
Lemma lem311765 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term104 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem311764 A lt2 x P)). Qed.
Lemma lem311766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311767 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem311766 A) (@lem311765 A lt2 P)). Qed.
Lemma lem311768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem311769 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term105 A lt2 P) = (term106 A lt2 P).
Proof. exact (MK_COMB (@lem311768) (@lem311767 A lt2 P)). Qed.
Lemma lem311770 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem311771 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem311772 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term108 A lt2 P y x).
Proof. exact (MK_COMB (@lem311770 A lt2 x P) (@lem311771 A y x)). Qed.
Lemma lem311773 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term108 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (eq_refl (term108 A lt2 P y x)). Qed.
Lemma lem311774 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (TRANS (@lem311772 A lt2 P y x) (@lem311773 A lt2 P y x)). Qed.
Lemma lem311775 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term110 A lt2 P y) = (term111 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem311774 A lt2 P y x)). Qed.
Lemma lem311776 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311777 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term112 A lt2 P y) = (term113 A lt2 P y).
Proof. exact (MK_COMB (@lem311776 A) (@lem311775 A lt2 P y)). Qed.
Lemma lem311778 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term114 A lt2 P) = (term115 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem311777 A lt2 P y)). Qed.
Lemma lem311779 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem311780 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term97 A lt2 P) = (term116 A lt2 P).
Proof. exact (MK_COMB (@lem311779 A) (@lem311778 A lt2 P)). Qed.
Lemma lem311781 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term96 A lt2 P) = (term97 A lt2 P)) = ((term91 A lt2 P) = (term116 A lt2 P)).
Proof. exact (MK_COMB (@lem311769 A lt2 P) (@lem311780 A lt2 P)). Qed.
Lemma lem311782 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term116 A lt2 P).
Proof. exact (EQ_MP (@lem311781 A lt2 P) (@lem311756 A lt2 P)). Qed.
Lemma lem311784 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem311752 A lt2 P) (@lem311782 A lt2 P)). Qed.
Lemma lem311785 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem311648 A lt2 P) (@lem311784 A lt2 P)). Qed.
Lemma lem311786 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term116 A lt2 P.
Proof. exact (EQ_MP (@lem311785 A lt2 P) (@lem311603 A lt2 P h1)). Qed.
Lemma lem311797 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (@lem17265 (P x) (term182 A P lt2 f x)). Qed.
Lemma lem311798 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem311797 A P lt2 f x)). Qed.
Lemma lem311799 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311852 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem311799 A) (@lem311798 A P lt2 f)). Qed.
Lemma lem311853 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem311852 A P lt2 f) (@lem311604 A P lt2 f h1)). Qed.
Lemma lem311872 (P : nat -> Prop) : (term295 P) = (term296 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem311873 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term226 A lt2 f s) = (term297 A lt2 f s).
Proof. exact (@lem311872 (term222 A lt2 f s)). Qed.
Lemma lem311874 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term298 A lt2 f s n) = (term220 A lt2 f s n).
Proof. exact (eq_refl (term298 A lt2 f s n)). Qed.
Lemma lem311875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem311877 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term299 A lt2 f s n) = (term300 A lt2 f s n).
Proof. exact (MK_COMB (@lem311875) (@lem311874 A lt2 f s n)). Qed.
Lemma lem311878 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term301 A lt2 f s) = (term302 A lt2 f s).
Proof. exact (fun_ext (fun n : nat => @lem311877 A lt2 f s n)). Qed.
Lemma lem311879 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem311880 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term297 A lt2 f s) = (term303 A lt2 f s).
Proof. exact (MK_COMB (@lem311879) (@lem311878 A lt2 f s)). Qed.
Lemma lem311889 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term226 A lt2 f s) = (term303 A lt2 f s).
Proof. exact (TRANS (@lem311873 A lt2 f s) (@lem311880 A lt2 f s)). Qed.
Lemma lem311890 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (h1 : term226 A lt2 f s) : term303 A lt2 f s.
Proof. exact (EQ_MP (@lem311889 A lt2 f s) (@lem311606 A lt2 f s h1)). Qed.
Lemma lem311891 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term239 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term239 A P s n)). Qed.
Lemma lem311892 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term237 A P s) = (term237 A P s).
Proof. exact (fun_ext (fun n : nat => @lem311891 A P s n)). Qed.
Lemma lem311893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311894 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term251 A P s) = (term251 A P s).
Proof. exact (MK_COMB (@lem311893) (@lem311892 A P s)). Qed.
Lemma lem311895 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem311896 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem311895 A lt2 s n)). Qed.
Lemma lem311897 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311898 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem311897) (@lem311896 A lt2 s)). Qed.
Lemma lem311899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem311900 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term253 A P s) = (term253 A P s).
Proof. exact (MK_COMB (@lem311899) (@lem311894 A P s)). Qed.
Lemma lem311913 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term256 A P lt2 s) = (term256 A P lt2 s).
Proof. exact (MK_COMB (@lem311900 A P s) (@lem311898 A lt2 s)). Qed.
Lemma lem311914 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term256 A P lt2 s.
Proof. exact (EQ_MP (@lem311913 A P lt2 s) (@lem311607 A P lt2 s h1)). Qed.
Lemma lem311943 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (eq_refl (term292 A P lt2 f x)). Qed.
Lemma lem311944 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem311943 A P lt2 f x)). Qed.
Lemma lem311945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem311946 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem311945 A) (@lem311944 A P lt2 f)). Qed.
Lemma lem311947 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem311946 A P lt2 f) (@lem311853 A P lt2 f h1)). Qed.
Lemma lem311987 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem311988 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem311987 A lt2 s n)). Qed.
Lemma lem311989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311990 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem311989) (@lem311988 A lt2 s)). Qed.
Lemma lem311995 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term239 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term239 A P s n)). Qed.
Lemma lem311996 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term237 A P s) = (term237 A P s).
Proof. exact (fun_ext (fun n : nat => @lem311995 A P s n)). Qed.
Lemma lem311997 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem311998 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term251 A P s) = (term251 A P s).
Proof. exact (MK_COMB (@lem311997) (@lem311996 A P s)). Qed.
Lemma lem311999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem312000 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term253 A P s) = (term253 A P s).
Proof. exact (MK_COMB (@lem311999) (@lem311998 A P s)). Qed.
Lemma lem312001 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term256 A P lt2 s) = (term256 A P lt2 s).
Proof. exact (MK_COMB (@lem312000 A P s) (@lem311990 A lt2 s)). Qed.
Lemma lem312002 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term256 A P lt2 s.
Proof. exact (EQ_MP (@lem312001 A P lt2 s) (@lem311914 A P lt2 s h1)). Qed.
Lemma lem312016 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term300 A lt2 f s n) : term300 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem312045 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term251 A P s.
Proof. exact (proj1 (@lem312002 A P lt2 s h1)). Qed.
Lemma lem312069 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term304 A P lt2 f x).
Proof. exact (@lem19490 (term155 A P f x) (term54 A P x) (term154 A lt2 f x)). Qed.
Lemma lem312070 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term305 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem312069 A P lt2 f x)). Qed.
Lemma lem312071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem312073 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term306 A P lt2 f).
Proof. exact (MK_COMB (@lem312071 A) (@lem312070 A P lt2 f)). Qed.
Lemma lem312074 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term306 A P lt2 f.
Proof. exact (EQ_MP (@lem312073 A P lt2 f) (@lem311947 A P lt2 f h1)). Qed.
Lemma lem312078 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term300 A lt2 f s n) : term300 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem312103 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term239 A P s n) = (term239 A P s n).
Proof. exact (eq_refl (term239 A P s n)). Qed.
Lemma lem312104 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term237 A P s) = (term237 A P s).
Proof. exact (fun_ext (fun n : nat => @lem312103 A P s n)). Qed.
Lemma lem312105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem312107 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term251 A P s) = (term251 A P s).
Proof. exact (MK_COMB (@lem312105) (@lem312104 A P s)). Qed.
Lemma lem312108 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term251 A P s.
Proof. exact (EQ_MP (@lem312107 A P s) (@lem312045 A P lt2 s h1)). Qed.
Lemma lem312127 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term307 A P lt2 f _6806.
Proof. exact (@lem312074 A P lt2 f h1 _6806). Qed.
Lemma lem312128 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6806 : A) : (term307 A P lt2 f _6806) = (term304 A P lt2 f _6806).
Proof. exact (eq_refl (term307 A P lt2 f _6806)). Qed.
Lemma lem312129 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term304 A P lt2 f _6806.
Proof. exact (EQ_MP (@lem312128 A P lt2 f _6806) (@lem312127 A _6806 P lt2 f h1)). Qed.
Lemma lem312133 {A : Type'} (_6808 : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term238 A P s _6808.
Proof. exact (@lem312108 A P lt2 s h1 _6808). Qed.
Lemma lem312134 {A : Type'} (P : A -> Prop) (s : nat -> A) (_6808 : nat) : (term238 A P s _6808) = (term239 A P s _6808).
Proof. exact (eq_refl (term238 A P s _6808)). Qed.
Lemma lem312149 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term300 A lt2 f s n) : term300 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem312223 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term300 A lt2 f s n) : term300 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem312321 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term159 A P lt2 f _6806.
Proof. exact (proj2 (@lem312129 A _6806 P lt2 f h1)). Qed.
Lemma lem312398 {A : Type'} (_6808 : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term239 A P s _6808.
Proof. exact (EQ_MP (@lem312134 A P s _6808) (@lem312133 A _6808 P lt2 s h1)). Qed.
Lemma lem312399 {A : Type'} (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term239 A P s n.
Proof. exact (@lem312398 A n P lt2 s h1). Qed.
Lemma lem312400 {A : Type'} (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term308 A P s n.
Proof. exact (fun h0 : term309 A P s n => @lem312399 A n P lt2 s h1). Qed.
Lemma lem312402 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem312403 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term308 A P s n) = (term239 A P s n).
Proof. exact (@lem312402 (term239 A P s n)). Qed.
Lemma lem312404 {A : Type'} (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term256 A P lt2 s) : term239 A P s n.
Proof. exact (EQ_MP (@lem312403 A P s n) (@lem312400 A n P lt2 s h1)). Qed.
Lemma lem312410 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem312411 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : (term159 A P lt2 f _6806) = (term172 A lt2 f P _6806).
Proof. exact (@lem312410 (term154 A lt2 f _6806) (term54 A P _6806)). Qed.
Lemma lem312417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem312418 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : (term173 A P lt2 f _6806) = (term174 A lt2 f P _6806).
Proof. exact (MK_COMB (@lem312417) (@lem312411 A lt2 f P _6806)). Qed.
Lemma lem312424 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : (term172 A lt2 f P _6806) = (term172 A lt2 f P _6806).
Proof. exact (eq_refl (term172 A lt2 f P _6806)). Qed.
Lemma lem312425 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : ((term159 A P lt2 f _6806) = (term172 A lt2 f P _6806)) = ((term172 A lt2 f P _6806) = (term172 A lt2 f P _6806)).
Proof. exact (MK_COMB (@lem312418 A lt2 f P _6806) (@lem312424 A lt2 f P _6806)). Qed.
Lemma lem312427 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem312428 (x : Prop) : (x = x) = True.
Proof. exact (@lem312427 Prop x). Qed.
Lemma lem312429 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : ((term172 A lt2 f P _6806) = (term172 A lt2 f P _6806)) = True.
Proof. exact (@lem312428 (term172 A lt2 f P _6806)). Qed.
Lemma lem312430 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : ((term159 A P lt2 f _6806) = (term172 A lt2 f P _6806)) = True.
Proof. exact (TRANS (@lem312425 A lt2 f P _6806) (@lem312429 A lt2 f P _6806)). Qed.
Lemma lem312431 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : True = ((term159 A P lt2 f _6806) = (term172 A lt2 f P _6806)).
Proof. exact (SYM (@lem312430 A lt2 f P _6806)). Qed.
Lemma lem312432 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6806 : A) : (term159 A P lt2 f _6806) = (term172 A lt2 f P _6806).
Proof. exact (EQ_MP (@lem312431 A lt2 f P _6806) (@lem0)). Qed.
Lemma lem312433 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term172 A lt2 f P _6806.
Proof. exact (EQ_MP (@lem312432 A lt2 f P _6806) (@lem312321 A _6806 P lt2 f h1)). Qed.
Lemma lem312435 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem312436 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6806 : A) : (term172 A lt2 f P _6806) = (term175 A P lt2 f _6806).
Proof. exact (@lem312435 (term54 A P _6806) (term154 A lt2 f _6806)). Qed.
Lemma lem312438 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem312439 {A : Type'} (P : A -> Prop) (_6806 : A) : (term49 A P _6806) = (P _6806).
Proof. exact (@lem312438 (P _6806)). Qed.
Lemma lem312440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312441 {A : Type'} (P : A -> Prop) (_6806 : A) : (term168 A P _6806) = (term23 A P _6806).
Proof. exact (MK_COMB (@lem312440) (@lem312439 A P _6806)). Qed.
Lemma lem312442 {A : Type'} (lt2 : type1402 A) (f : A -> A) (_6806 : A) : (term154 A lt2 f _6806) = (term154 A lt2 f _6806).
Proof. exact (eq_refl (term154 A lt2 f _6806)). Qed.
Lemma lem312443 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6806 : A) : (term175 A P lt2 f _6806) = (term176 A P lt2 f _6806).
Proof. exact (MK_COMB (@lem312441 A P _6806) (@lem312442 A lt2 f _6806)). Qed.
Lemma lem312444 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6806 : A) : (term172 A lt2 f P _6806) = (term176 A P lt2 f _6806).
Proof. exact (TRANS (@lem312436 A P lt2 f _6806) (@lem312443 A P lt2 f _6806)). Qed.
Lemma lem312447 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6806.
Proof. exact (EQ_MP (@lem312444 A P lt2 f _6806) (@lem312433 A _6806 P lt2 f h1)). Qed.
Lemma lem312448 {A : Type'} (_6806 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6806.
Proof. exact (@lem312447 A _6806 P lt2 f h1). Qed.
Lemma lem312449 {A : Type'} (s : nat -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term310 A P lt2 f s n.
Proof. exact (@lem312448 A (s n) P lt2 f h1). Qed.
Lemma lem312452 {A : Type'} (n : nat) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term256 A P lt2 s) : term220 A lt2 f s n.
Proof. exact (@lem312449 A s n P lt2 f h1 (@lem312404 A n P lt2 s h2)). Qed.
Lemma lem312453 {A : Type'} (n : nat) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term256 A P lt2 s) : term311 A lt2 f s n.
Proof. exact (fun h0 : term300 A lt2 f s n => @lem312452 A n f P lt2 s h1 h2). Qed.
Lemma lem312455 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem312456 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term311 A lt2 f s n) = (term220 A lt2 f s n).
Proof. exact (@lem312455 (term220 A lt2 f s n)). Qed.
Lemma lem312457 {A : Type'} (n : nat) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term256 A P lt2 s) : term220 A lt2 f s n.
Proof. exact (EQ_MP (@lem312456 A lt2 f s n) (@lem312453 A n f P lt2 s h1 h2)). Qed.
Lemma lem312460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem312462 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term300 A lt2 f s n) = (term312 A lt2 f s n).
Proof. exact (@lem312460 (term220 A lt2 f s n)). Qed.
Lemma lem312465 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term300 A lt2 f s n) : term312 A lt2 f s n.
Proof. exact (EQ_MP (@lem312462 A lt2 f s n) (@lem312223 A lt2 f s n h1)). Qed.
Lemma lem312468 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (@lem312465 A lt2 f s n h2 (@lem312457 A n f P lt2 s h1 h3)). Qed.
Lemma lem312469 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : term184.
Proof. exact (fun h0 : ~ False => @lem312468 A f n P lt2 s h1 h2 h3). Qed.
Lemma lem312471 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem312472 : term184 = False.
Proof. exact (@lem312471 False). Qed.
Lemma lem312473 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312472) (@lem312469 A f n P lt2 s h1 h2 h3)). Qed.
Lemma lem312474 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term300 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term300 A lt2 f s n => @lem312473 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312223 A lt2 f s n h2)). Qed.
Lemma lem312476 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312474 A f n P lt2 s h1 h2 h3) (@lem312223 A lt2 f s n h2)). Qed.
Lemma lem312477 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term300 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term300 A lt2 f s n => @lem312476 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312149 A lt2 f s n h2)). Qed.
Lemma lem312478 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312477 A f n P lt2 s h1 h2 h3) (@lem312149 A lt2 f s n h2)). Qed.
Lemma lem312479 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term300 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term300 A lt2 f s n => @lem312478 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312078 A lt2 f s n h2)). Qed.
Lemma lem312480 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312479 A f n P lt2 s h1 h2 h3) (@lem312078 A lt2 f s n h2)). Qed.
Lemma lem312481 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term300 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term300 A lt2 f s n => @lem312480 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312078 A lt2 f s n h2)). Qed.
Lemma lem312482 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312481 A f n P lt2 s h1 h2 h3) (@lem312078 A lt2 f s n h2)). Qed.
Lemma lem312483 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term300 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term300 A lt2 f s n => @lem312482 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312016 A lt2 f s n h2)). Qed.
Lemma lem312484 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312483 A f n P lt2 s h1 h2 h3) (@lem312016 A lt2 f s n h2)). Qed.
Lemma lem312485 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : (term256 A P lt2 s) = False.
Proof. exact (prop_ext (fun h4 : term256 A P lt2 s => @lem312484 A f n P lt2 s h1 h2 h3) (fun h4 : False => @lem312002 A P lt2 s h3)). Qed.
Lemma lem312486 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term300 A lt2 f s n) (h3 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312485 A f n P lt2 s h1 h2 h3) (@lem312002 A P lt2 s h3)). Qed.
Lemma lem312487 {A : Type'} (f : A -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term300 A lt2 f s n) (h4 : term256 A P lt2 s) : False.
Proof. exact (ex_elim (@lem311786 A lt2 P h2) (fun y : A -> A => fun h0 : term115 A lt2 P y => @lem312486 A f n P lt2 s h1 h3 h4)). Qed.
Lemma lem312488 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) (h4 : term256 A P lt2 s) : False.
Proof. exact (ex_elim (@lem311890 A lt2 f s h2) (fun n : nat => fun h0 : term302 A lt2 f s n => @lem312487 A f n P lt2 s h1 h3 h0 h4)). Qed.
Lemma lem312489 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) (h4 : term256 A P lt2 s) : (term256 A P lt2 s) = False.
Proof. exact (prop_ext (fun h5 : term256 A P lt2 s => @lem312488 A f P lt2 s h1 h2 h3 h4) (fun h5 : False => @lem311914 A P lt2 s h4)). Qed.
Lemma lem312490 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) (h4 : term256 A P lt2 s) : False.
Proof. exact (EQ_MP (@lem312489 A f P lt2 s h1 h2 h3 h4) (@lem311914 A P lt2 s h4)). Qed.
Lemma lem312491 {A : Type'} (f : A -> A) (s : nat -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) : term313 A P lt2 s.
Proof. exact (fun h0 : term256 A P lt2 s => @lem312490 A f P lt2 s h1 h2 h3 h0). Qed.
Lemma lem312492 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term313 A P lt2 s) = (term257 A P lt2 s).
Proof. exact (@lem69 (term256 A P lt2 s)). Qed.
Lemma lem312493 {A : Type'} (f : A -> A) (s : nat -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) : term257 A P lt2 s.
Proof. exact (EQ_MP (@lem312492 A P lt2 s) (@lem312491 A f s lt2 P h1 h2 h3)). Qed.
Lemma lem312494 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) : term260 A f P lt2 s.
Proof. exact (fun h0 : term226 A lt2 f s => @lem312493 A f s lt2 P h1 h0 h2). Qed.
Lemma lem312495 {A : Type'} (a : A) (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) : term263 A a f P lt2 s.
Proof. exact (fun h0 : term212 A a f s => @lem312494 A s f lt2 P h1 h2). Qed.
Lemma lem312496 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term266 A a f P lt2 s.
Proof. exact (fun h0 : term204 A P lt2 f => @lem312495 A a s f lt2 P h0 h1). Qed.
Lemma lem312497 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term268 A a f P lt2 s.
Proof. exact (fun h0 : term9 A lt2 P => @lem312496 A a f s lt2 P h0). Qed.
Lemma lem312498 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term269 A a f P lt2 s.
Proof. exact (fun h0 : P a => @lem312497 A a f P lt2 s). Qed.
Lemma lem312503 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term273 A f P lt2 s.
Proof. exact (fun a : A => @lem312498 A a f P lt2 s). Qed.
Lemma lem312508 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term277 A P lt2 s.
Proof. exact (fun f : A -> A => @lem312503 A f P lt2 s). Qed.
Lemma lem312513 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term281 A lt2 s.
Proof. exact (fun P : A -> Prop => @lem312508 A P lt2 s). Qed.
Lemma lem312518 {A : Type'} (s : nat -> A) : term285 A s.
Proof. exact (fun lt2 : type1402 A => @lem312513 A lt2 s). Qed.
Lemma lem312523 {A : Type'} : term289 A.
Proof. exact (fun s : nat -> A => @lem312518 A s). Qed.
Lemma lem312524 {A : Type'} : term288 A.
Proof. exact (EQ_MP (@lem311601 A) (@lem312523 A)). Qed.
Lemma lem312525 {A : Type'} (s : nat -> A) : term314 A s.
Proof. exact (@lem312524 A s). Qed.
Lemma lem312526 {A : Type'} (s : nat -> A) : (term314 A s) = (term284 A s).
Proof. exact (eq_refl (term314 A s)). Qed.
Lemma lem312527 {A : Type'} (s : nat -> A) : term284 A s.
Proof. exact (EQ_MP (@lem312526 A s) (@lem312525 A s)). Qed.
Lemma lem312528 {A : Type'} (s : nat -> A) (lt2 : type1402 A) : term315 A s lt2.
Proof. exact (@lem312527 A s lt2). Qed.
Lemma lem312529 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term315 A s lt2) = (term280 A lt2 s).
Proof. exact (eq_refl (term315 A s lt2)). Qed.
Lemma lem312530 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term280 A lt2 s.
Proof. exact (EQ_MP (@lem312529 A lt2 s) (@lem312528 A s lt2)). Qed.
Lemma lem312531 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (P : A -> Prop) : term316 A lt2 s P.
Proof. exact (@lem312530 A lt2 s P). Qed.
Lemma lem312532 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term316 A lt2 s P) = (term276 A P lt2 s).
Proof. exact (eq_refl (term316 A lt2 s P)). Qed.
Lemma lem312533 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term276 A P lt2 s.
Proof. exact (EQ_MP (@lem312532 A P lt2 s) (@lem312531 A lt2 s P)). Qed.
Lemma lem312534 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (f : A -> A) : term317 A P lt2 s f.
Proof. exact (@lem312533 A P lt2 s f). Qed.
Lemma lem312535 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term317 A P lt2 s f) = (term272 A f P lt2 s).
Proof. exact (eq_refl (term317 A P lt2 s f)). Qed.
Lemma lem312536 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term272 A f P lt2 s.
Proof. exact (EQ_MP (@lem312535 A f P lt2 s) (@lem312534 A P lt2 s f)). Qed.
Lemma lem312537 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (a : A) : term318 A f P lt2 s a.
Proof. exact (@lem312536 A f P lt2 s a). Qed.
Lemma lem312538 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term318 A f P lt2 s a) = (term227 A a f P lt2 s).
Proof. exact (eq_refl (term318 A f P lt2 s a)). Qed.
Lemma lem312539 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term227 A a f P lt2 s.
Proof. exact (EQ_MP (@lem312538 A a f P lt2 s) (@lem312537 A f P lt2 s a)). Qed.
Lemma lem312541 {A : Type'} (a : A) (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term227 A a f P lt2 s.
Proof. exact (@lem311228 A a f P lt2 s (@lem312539 A a f P lt2 s)). Qed.
Lemma lem312542 {A : Type'} (f : A -> A) (lt2 : type1402 A) (s : nat -> A) (P : A -> Prop) (a : A) (h1 : P a) : term267 A a f P lt2 s.
Proof. exact (@lem312541 A a f P lt2 s (@lem310249 A P a h1)). Qed.
Lemma lem312543 {A : Type'} (f : A -> A) (s : nat -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term265 A a f P lt2 s.
Proof. exact (@lem312542 A f lt2 s P a h2 (@lem310247 A lt2 P h1)). Qed.
Lemma lem312544 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term262 A a f P lt2 s.
Proof. exact (@lem312543 A f s lt2 P a h2 h3 (@lem311163 A P lt2 f h1)). Qed.
Lemma lem312545 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term259 A f P lt2 s.
Proof. exact (@lem312544 A s f lt2 P a h1 h2 h3 (@lem311164 A a f s h4)). Qed.
Lemma lem312546 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term226 A lt2 f s) (h3 : term9 A lt2 P) (h4 : P a) (h5 : term212 A a f s) : term231 A P lt2 s.
Proof. exact (@lem312545 A lt2 P a f s h1 h3 h4 h5 (@lem311212 A lt2 f s h2)). Qed.
Lemma lem312547 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term226 A lt2 f s) (h4 : term9 A lt2 P) (h5 : P a) (h6 : term212 A a f s) : False.
Proof. exact (@lem312546 A lt2 P a f s h1 h3 h4 h5 h6 (@lem311197 A P lt2 s h2)). Qed.
Lemma lem312548 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term226 A lt2 f s) (h4 : term9 A lt2 P) (h5 : P a) (h6 : term212 A a f s) : (term224 A P lt2 s) = False.
Proof. exact (prop_ext (fun h7 : term224 A P lt2 s => @lem312547 A lt2 P a f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem311197 A P lt2 s h2)). Qed.
Lemma lem312549 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term226 A lt2 f s) (h4 : term9 A lt2 P) (h5 : P a) (h6 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem312548 A lt2 P a f s h1 h2 h3 h4 h5 h6) (@lem311197 A P lt2 s h2)). Qed.
Lemma lem312550 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term226 A lt2 f s) (h4 : term9 A lt2 P) (h5 : P a) (h6 : term212 A a f s) : (term226 A lt2 f s) = False.
Proof. exact (prop_ext (fun h7 : term226 A lt2 f s => @lem312549 A lt2 P a f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem311212 A lt2 f s h3)). Qed.
Lemma lem312551 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term226 A lt2 f s) (h4 : term9 A lt2 P) (h5 : P a) (h6 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem312550 A lt2 P a f s h1 h2 h3 h4 h5 h6) (@lem311212 A lt2 f s h3)). Qed.
Lemma lem312552 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term9 A lt2 P) (h4 : P a) (h5 : term212 A a f s) : term225 A lt2 f s.
Proof. exact (fun h0 : term226 A lt2 f s => @lem312551 A lt2 P a f s h1 h2 h0 h3 h4 h5). Qed.
Lemma lem312553 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term224 A P lt2 s) (h3 : term9 A lt2 P) (h4 : P a) (h5 : term212 A a f s) : term223 A lt2 f s.
Proof. exact (EQ_MP (@lem311211 A lt2 f s) (@lem312552 A lt2 P a f s h1 h2 h3 h4 h5)). Qed.
Lemma lem312555 (P : nat -> Prop) : term319 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem312556 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term320 A P lt2 s.
Proof. exact (@lem312555 (term246 A P lt2 s)). Qed.
Lemma lem312557 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term321 A P lt2 s) = (term322 A P lt2 s).
Proof. exact (eq_refl (term321 A P lt2 s)). Qed.
Lemma lem312558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem312559 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term323 A P lt2 s) = (term324 A P lt2 s).
Proof. exact (MK_COMB (@lem312558) (@lem312557 A P lt2 s)). Qed.
Lemma lem312560 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term325 A P lt2 s n) = (term244 A P lt2 s n).
Proof. exact (eq_refl (term325 A P lt2 s n)). Qed.
Lemma lem312561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312562 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term326 A P lt2 s n) = (term327 A P lt2 s n).
Proof. exact (MK_COMB (@lem312561) (@lem312560 A P lt2 s n)). Qed.
Lemma lem312563 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term328 A P lt2 s n) = (term329 A P lt2 s n).
Proof. exact (eq_refl (term328 A P lt2 s n)). Qed.
Lemma lem312564 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term330 A P lt2 s n) = (term331 A P lt2 s n).
Proof. exact (MK_COMB (@lem312562 A P lt2 s n) (@lem312563 A P lt2 s n)). Qed.
Lemma lem312565 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term332 A P lt2 s) = (term333 A P lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem312564 A P lt2 s n)). Qed.
Lemma lem312566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem312567 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term334 A P lt2 s) = (term335 A P lt2 s).
Proof. exact (MK_COMB (@lem312566) (@lem312565 A P lt2 s)). Qed.
Lemma lem312568 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term336 A P lt2 s) = (term337 A P lt2 s).
Proof. exact (MK_COMB (@lem312559 A P lt2 s) (@lem312567 A P lt2 s)). Qed.
Lemma lem312569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312570 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term338 A P lt2 s) = (term339 A P lt2 s).
Proof. exact (MK_COMB (@lem312569) (@lem312568 A P lt2 s)). Qed.
Lemma lem312571 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term325 A P lt2 s n) = (term244 A P lt2 s n).
Proof. exact (eq_refl (term325 A P lt2 s n)). Qed.
Lemma lem312572 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term340 A P lt2 s) = (term246 A P lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem312571 A P lt2 s n)). Qed.
Lemma lem312573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem312574 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term341 A P lt2 s) = (term224 A P lt2 s).
Proof. exact (MK_COMB (@lem312573) (@lem312572 A P lt2 s)). Qed.
Lemma lem312575 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : (term320 A P lt2 s) = (term342 A P lt2 s).
Proof. exact (MK_COMB (@lem312570 A P lt2 s) (@lem312574 A P lt2 s)). Qed.
Lemma lem312576 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) : term342 A P lt2 s.
Proof. exact (EQ_MP (@lem312575 A P lt2 s) (@lem312556 A P lt2 s)). Qed.
Lemma lem312577 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term244 A P lt2 s n.
Proof. exact (h1). Qed.
Lemma lem312578 {A : Type'} (P : A -> Prop) (a : A) : (P a) = ((P a) = True).
Proof. exact (@lem7 (P a)). Qed.
Lemma lem312587 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term213 A f s.
Proof. exact (proj2 (@lem311164 A a f s h1)). Qed.
Lemma lem312588 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term214 A f s n.
Proof. exact (@lem312587 A a f s h1 n). Qed.
Lemma lem312589 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term214 A f s n) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl (term214 A f s n)). Qed.
Lemma lem312595 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term343 A s) = a.
Proof. exact (proj1 (@lem311164 A a f s h1)). Qed.
Lemma lem312596 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem312597 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term344 A P s) = (P a).
Proof. exact (MK_COMB (@lem312596 A P) (@lem312595 A a f s h1)). Qed.
Lemma lem312599 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : (P a) = True.
Proof. exact (EQ_MP (@lem312578 A P a) (@lem310249 A P a h1)). Qed.
Lemma lem312600 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : (term344 A P s) = True.
Proof. exact (TRANS (@lem312597 A P a f s h2) (@lem312599 A P a h1)). Qed.
Lemma lem312601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem312602 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : (term345 A P s) = (and True).
Proof. exact (MK_COMB (@lem312601) (@lem312600 A P a f s h1 h2)). Qed.
Lemma lem312604 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem312589 A f s n) (@lem312588 A n a f s h1)). Qed.
Lemma lem312605 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term346 A s) = (term347 A f s).
Proof. exact (@lem312604 A (NUMERAL 0) a f s h1). Qed.
Lemma lem312607 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term343 A s) = a.
Proof. exact (proj1 (@lem311164 A a f s h1)). Qed.
Lemma lem312608 {A : Type'} (f : A -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem312609 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term347 A f s) = (f a).
Proof. exact (MK_COMB (@lem312608 A f) (@lem312607 A a f s h1)). Qed.
Lemma lem312610 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term346 A s) = (f a).
Proof. exact (TRANS (@lem312605 A a f s h1) (@lem312609 A a f s h1)). Qed.
Lemma lem312611 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem312612 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term348 A lt2 s) = (term349 A lt2 f a).
Proof. exact (MK_COMB (@lem312611 A lt2) (@lem312610 A a f s h1)). Qed.
Lemma lem312614 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term343 A s) = a.
Proof. exact (proj1 (@lem311164 A a f s h1)). Qed.
Lemma lem312615 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term350 A lt2 s) = (term154 A lt2 f a).
Proof. exact (MK_COMB (@lem312612 A lt2 a f s h1) (@lem312614 A a f s h1)). Qed.
Lemma lem312616 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : (term322 A P lt2 s) = (term351 A lt2 f a).
Proof. exact (MK_COMB (@lem312602 A P a f s h1 h2) (@lem312615 A lt2 a f s h2)). Qed.
Lemma lem312618 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem312619 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term351 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (@lem312618 (term154 A lt2 f a)). Qed.
Lemma lem312620 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : (term322 A P lt2 s) = (term154 A lt2 f a).
Proof. exact (TRANS (@lem312616 A lt2 P a f s h1 h2) (@lem312619 A lt2 f a)). Qed.
Lemma lem312621 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : (term154 A lt2 f a) = (term322 A P lt2 s).
Proof. exact (SYM (@lem312620 A lt2 P a f s h1 h2)). Qed.
Lemma lem312631 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term213 A f s.
Proof. exact (proj2 (@lem311164 A a f s h1)). Qed.
Lemma lem312632 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term214 A f s n.
Proof. exact (@lem312631 A a f s h1 n). Qed.
Lemma lem312633 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term214 A f s n) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl (term214 A f s n)). Qed.
Lemma lem312645 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem312633 A f s n) (@lem312632 A n a f s h1)). Qed.
Lemma lem312646 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem312647 {A : Type'} (P : A -> Prop) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term352 A P s n) = (term353 A P f s n).
Proof. exact (MK_COMB (@lem312646 A P) (@lem312645 A n a f s h1)). Qed.
Lemma lem312648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem312649 {A : Type'} (P : A -> Prop) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term354 A P s n) = (term355 A P f s n).
Proof. exact (MK_COMB (@lem312648) (@lem312647 A P n a f s h1)). Qed.
Lemma lem312651 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem312633 A f s n) (@lem312632 A n a f s h1)). Qed.
Lemma lem312652 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term356 A s n) = (term357 A f s n).
Proof. exact (@lem312651 A (S n) a f s h1). Qed.
Lemma lem312654 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem312633 A f s n) (@lem312632 A n a f s h1)). Qed.
Lemma lem312655 {A : Type'} (f : A -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem312656 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term357 A f s n) = (term358 A f s n).
Proof. exact (MK_COMB (@lem312655 A f) (@lem312654 A n a f s h1)). Qed.
Lemma lem312657 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term356 A s n) = (term358 A f s n).
Proof. exact (TRANS (@lem312652 A n a f s h1) (@lem312656 A n a f s h1)). Qed.
Lemma lem312658 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem312659 {A : Type'} (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term359 A lt2 s n) = (term360 A lt2 f s n).
Proof. exact (MK_COMB (@lem312658 A lt2) (@lem312657 A n a f s h1)). Qed.
Lemma lem312661 {A : Type'} (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term215 A s n) = (term216 A f s n).
Proof. exact (EQ_MP (@lem312633 A f s n) (@lem312632 A n a f s h1)). Qed.
Lemma lem312662 {A : Type'} (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term361 A lt2 s n) = (term362 A lt2 f s n).
Proof. exact (MK_COMB (@lem312659 A lt2 n a f s h1) (@lem312661 A n a f s h1)). Qed.
Lemma lem312663 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term329 A P lt2 s n) = (term363 A P lt2 f s n).
Proof. exact (MK_COMB (@lem312649 A P n a f s h1) (@lem312662 A lt2 n a f s h1)). Qed.
Lemma lem312666 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term363 A P lt2 f s n) = (term329 A P lt2 s n).
Proof. exact (SYM (@lem312663 A P lt2 n a f s h1)). Qed.
Lemma lem312668 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem312669 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term154 A lt2 f a) = (term364 A lt2 f a).
Proof. exact (@lem312668 (term154 A lt2 f a)). Qed.
Lemma lem312670 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term364 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (SYM (@lem312669 A lt2 f a)). Qed.
Lemma lem312671 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312674 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term365 A P s lt2 f a) : term365 A P s lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312675 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term366 A P s lt2 f a.
Proof. exact (fun h0 : term365 A P s lt2 f a => @lem312674 A P s lt2 f a h0). Qed.
Lemma lem312676 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term366 A P s lt2 f a) : term366 A P s lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312677 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term365 A P s lt2 f a) : term365 A P s lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312678 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term365 A P s lt2 f a) (h2 : term366 A P s lt2 f a) : term365 A P s lt2 f a.
Proof. exact (@lem312676 A P s lt2 f a h2 (@lem312677 A P s lt2 f a h1)). Qed.
Lemma lem312679 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term365 A P s lt2 f a) : term367 A P s lt2 f a.
Proof. exact (fun h0 : term366 A P s lt2 f a => @lem312678 A P s lt2 f a h1 h0). Qed.
Lemma lem312680 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term366 A P s lt2 f a) : term366 A P s lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312681 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term365 A P s lt2 f a) (h2 : term366 A P s lt2 f a) : term365 A P s lt2 f a.
Proof. exact (@lem312679 A P s lt2 f a h1 (@lem312680 A P s lt2 f a h2)). Qed.
Lemma lem312682 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term366 A P s lt2 f a) : term366 A P s lt2 f a.
Proof. exact (fun h0 : term365 A P s lt2 f a => @lem312681 A P s lt2 f a h0 h1). Qed.
Lemma lem312683 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term368 A P s lt2 f a.
Proof. exact (fun h0 : term366 A P s lt2 f a => @lem312682 A P s lt2 f a h0). Qed.
Lemma lem312686 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term366 A P s lt2 f a.
Proof. exact (@lem312683 A P s lt2 f a (@lem312675 A P s lt2 f a)). Qed.
Lemma lem312687 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term366 A P s lt2 f a.
Proof. exact (@lem312686 A P s lt2 f a). Qed.
Lemma lem312767 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem312768 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term364 A lt2 f a) = (term369 A lt2 f a).
Proof. exact (@lem312767 (term178 A lt2 f a)). Qed.
Lemma lem312770 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem312771 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term369 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (@lem312770 (term154 A lt2 f a)). Qed.
Lemma lem312772 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term364 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (TRANS (@lem312768 A lt2 f a) (@lem312771 A lt2 f a)). Qed.
Lemma lem312773 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (eq_refl (term261 A a f s)). Qed.
Lemma lem312774 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term370 A s lt2 f a) = (term371 A s lt2 f a).
Proof. exact (MK_COMB (@lem312773 A a f s) (@lem312772 A lt2 f a)). Qed.
Lemma lem312777 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (eq_refl (term264 A P lt2 f)). Qed.
Lemma lem312778 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term372 A P s lt2 f a) = (term373 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312777 A P lt2 f) (@lem312774 A s lt2 f a)). Qed.
Lemma lem312781 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (eq_refl (term20 A lt2 P)). Qed.
Lemma lem312782 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term374 A P s lt2 f a) = (term375 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312781 A lt2 P) (@lem312778 A P s lt2 f a)). Qed.
Lemma lem312785 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem312786 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term365 A P s lt2 f a) = (term376 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312785 A P a) (@lem312782 A P s lt2 f a)). Qed.
Lemma lem312789 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term377 A s lt2 f a) = (term378 A s lt2 f a).
Proof. exact (fun_ext (fun P : A -> Prop => @lem312786 A P s lt2 f a)). Qed.
Lemma lem312790 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem312791 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term379 A s lt2 f a) = (term380 A s lt2 f a).
Proof. exact (MK_COMB (@lem312790 A) (@lem312789 A s lt2 f a)). Qed.
Lemma lem312796 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term381 A lt2 f a) = (term382 A lt2 f a).
Proof. exact (fun_ext (fun s : nat -> A => @lem312791 A s lt2 f a)). Qed.
Lemma lem312797 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem312798 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term383 A lt2 f a) = (term384 A lt2 f a).
Proof. exact (MK_COMB (@lem312797 A) (@lem312796 A lt2 f a)). Qed.
Lemma lem312803 {A : Type'} (f : A -> A) (a : A) : (term385 A f a) = (term386 A f a).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem312798 A lt2 f a)). Qed.
Lemma lem312804 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem312805 {A : Type'} (f : A -> A) (a : A) : (term387 A f a) = (term388 A f a).
Proof. exact (MK_COMB (@lem312804 A) (@lem312803 A f a)). Qed.
Lemma lem312810 {A : Type'} (a : A) : (term389 A a) = (term390 A a).
Proof. exact (fun_ext (fun f : A -> A => @lem312805 A f a)). Qed.
Lemma lem312811 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem312812 {A : Type'} (a : A) : (term391 A a) = (term392 A a).
Proof. exact (MK_COMB (@lem312811 A) (@lem312810 A a)). Qed.
Lemma lem312817 {A : Type'} : (term393 A) = (term394 A).
Proof. exact (fun_ext (fun a : A => @lem312812 A a)). Qed.
Lemma lem312818 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem312827 {A : Type'} : (term395 A) = (term396 A).
Proof. exact (MK_COMB (@lem312818 A) (@lem312817 A)). Qed.
Lemma lem312828 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term154 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (eq_refl (term154 A lt2 f a)). Qed.
Lemma lem312829 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : ((term215 A s n) = (term216 A f s n)) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl ((term215 A s n) = (term216 A f s n))). Qed.
Lemma lem312830 {A : Type'} (f : A -> A) (s : nat -> A) : (term290 A f s) = (term290 A f s).
Proof. exact (fun_ext (fun n : nat => @lem312829 A f s n)). Qed.
Lemma lem312831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem312832 {A : Type'} (f : A -> A) (s : nat -> A) : (term213 A f s) = (term213 A f s).
Proof. exact (MK_COMB (@lem312831) (@lem312830 A f s)). Qed.
Lemma lem312835 {A : Type'} (s : nat -> A) (a : A) : (term291 A s a) = (term291 A s a).
Proof. exact (eq_refl (term291 A s a)). Qed.
Lemma lem312836 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term212 A a f s) = (term212 A a f s).
Proof. exact (MK_COMB (@lem312835 A s a) (@lem312832 A f s)). Qed.
Lemma lem312837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312838 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (MK_COMB (@lem312837) (@lem312836 A a f s)). Qed.
Lemma lem312839 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term371 A s lt2 f a) = (term371 A s lt2 f a).
Proof. exact (MK_COMB (@lem312838 A a f s) (@lem312828 A lt2 f a)). Qed.
Lemma lem312848 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term200 A P lt2 f x).
Proof. exact (eq_refl (term200 A P lt2 f x)). Qed.
Lemma lem312849 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term202 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem312848 A P lt2 f x)). Qed.
Lemma lem312850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem312851 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term204 A P lt2 f).
Proof. exact (MK_COMB (@lem312850 A) (@lem312849 A P lt2 f)). Qed.
Lemma lem312852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312853 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (MK_COMB (@lem312852) (@lem312851 A P lt2 f)). Qed.
Lemma lem312854 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term373 A P s lt2 f a) = (term373 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312853 A P lt2 f) (@lem312839 A s lt2 f a)). Qed.
Lemma lem312861 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term41 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term41 A lt2 x P y)). Qed.
Lemma lem312862 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term42 A lt2 x P) = (term42 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem312861 A lt2 x P y)). Qed.
Lemma lem312863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem312864 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term43 A lt2 x P) = (term43 A lt2 x P).
Proof. exact (MK_COMB (@lem312863 A) (@lem312862 A lt2 x P)). Qed.
Lemma lem312867 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem312868 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term45 A lt2 x P) = (term45 A lt2 x P).
Proof. exact (MK_COMB (@lem312867 A P x) (@lem312864 A lt2 x P)). Qed.
Lemma lem312869 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term46 A lt2 P) = (term46 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem312868 A lt2 x P)). Qed.
Lemma lem312870 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem312871 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term8 A lt2 P) = (term8 A lt2 P).
Proof. exact (MK_COMB (@lem312870 A) (@lem312869 A lt2 P)). Qed.
Lemma lem312872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem312873 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term9 A lt2 P).
Proof. exact (MK_COMB (@lem312872) (@lem312871 A lt2 P)). Qed.
Lemma lem312874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem312875 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (MK_COMB (@lem312874) (@lem312873 A lt2 P)). Qed.
Lemma lem312876 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term375 A P s lt2 f a) = (term375 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312875 A lt2 P) (@lem312854 A P s lt2 f a)). Qed.
Lemma lem312879 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem312880 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term376 A P s lt2 f a) = (term376 A P s lt2 f a).
Proof. exact (MK_COMB (@lem312879 A P a) (@lem312876 A P s lt2 f a)). Qed.
Lemma lem312881 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term378 A s lt2 f a) = (term378 A s lt2 f a).
Proof. exact (fun_ext (fun P : A -> Prop => @lem312880 A P s lt2 f a)). Qed.
Lemma lem312882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem312883 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term380 A s lt2 f a) = (term380 A s lt2 f a).
Proof. exact (MK_COMB (@lem312882 A) (@lem312881 A s lt2 f a)). Qed.
Lemma lem312884 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term382 A lt2 f a) = (term382 A lt2 f a).
Proof. exact (fun_ext (fun s : nat -> A => @lem312883 A s lt2 f a)). Qed.
Lemma lem312885 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem312886 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term384 A lt2 f a) = (term384 A lt2 f a).
Proof. exact (MK_COMB (@lem312885 A) (@lem312884 A lt2 f a)). Qed.
Lemma lem312887 {A : Type'} (f : A -> A) (a : A) : (term386 A f a) = (term386 A f a).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem312886 A lt2 f a)). Qed.
Lemma lem312888 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem312889 {A : Type'} (f : A -> A) (a : A) : (term388 A f a) = (term388 A f a).
Proof. exact (MK_COMB (@lem312888 A) (@lem312887 A f a)). Qed.
Lemma lem312890 {A : Type'} (a : A) : (term390 A a) = (term390 A a).
Proof. exact (fun_ext (fun f : A -> A => @lem312889 A f a)). Qed.
Lemma lem312891 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem312892 {A : Type'} (a : A) : (term392 A a) = (term392 A a).
Proof. exact (MK_COMB (@lem312891 A) (@lem312890 A a)). Qed.
Lemma lem312893 {A : Type'} : (term394 A) = (term394 A).
Proof. exact (fun_ext (fun a : A => @lem312892 A a)). Qed.
Lemma lem312894 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem312895 {A : Type'} : (term396 A) = (term396 A).
Proof. exact (MK_COMB (@lem312894 A) (@lem312893 A)). Qed.
Lemma lem312970 {A : Type'} : (term395 A) = (term396 A).
Proof. exact (TRANS (@lem312827 A) (@lem312895 A)). Qed.
Lemma lem312971 {A : Type'} : (term396 A) = (term395 A).
Proof. exact (SYM (@lem312970 A)). Qed.
Lemma lem312973 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem312974 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term204 A P lt2 f.
Proof. exact (h1). Qed.
Lemma lem312975 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term212 A a f s.
Proof. exact (h1). Qed.
Lemma lem312977 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem312978 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term154 A lt2 f a) = (term364 A lt2 f a).
Proof. exact (@lem312977 (term154 A lt2 f a)). Qed.
Lemma lem312979 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term364 A lt2 f a) = (term154 A lt2 f a).
Proof. exact (SYM (@lem312978 A lt2 f a)). Qed.
Lemma lem312980 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem312986 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem312991 {A : Type'} (P : A -> Prop) (y : A) : (term49 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem312993 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term50 A lt2 y x) = (term50 A lt2 y x).
Proof. exact (eq_refl (term50 A lt2 y x)). Qed.
Lemma lem312994 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (MK_COMB (@lem312993 A lt2 y x) (@lem312991 A P y)). Qed.
Lemma lem312995 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term51 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term54 A P y)). Qed.
Lemma lem312996 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem312995 A lt2 x P y) (@lem312994 A lt2 x P y)). Qed.
Lemma lem312997 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem312998 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem312997 A (term42 A lt2 x P)). Qed.
Lemma lem312999 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term59 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term59 A lt2 x P y)). Qed.
Lemma lem313000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem313001 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term53 A lt2 x P y).
Proof. exact (MK_COMB (@lem313000) (@lem312999 A lt2 x P y)). Qed.
Lemma lem313002 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem313001 A lt2 x P y) (@lem312996 A lt2 x P y)). Qed.
Lemma lem313003 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term61 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem313002 A lt2 x P y)). Qed.
Lemma lem313004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem313005 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem313004 A) (@lem313003 A lt2 x P)). Qed.
Lemma lem313006 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (TRANS (@lem312998 A lt2 x P) (@lem313005 A lt2 x P)). Qed.
Lemma lem313008 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem313009 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem313008 A P x) (@lem313006 A lt2 x P)). Qed.
Lemma lem313010 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term65 A lt2 x P).
Proof. exact (@lem17045 (P x) (term43 A lt2 x P)). Qed.
Lemma lem313011 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem313010 A lt2 x P) (@lem313009 A lt2 x P)). Qed.
Lemma lem313012 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem313013 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term70 A lt2 P).
Proof. exact (@lem313012 A (term46 A lt2 P)). Qed.
Lemma lem313014 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term71 A lt2 P x) = (term45 A lt2 x P).
Proof. exact (eq_refl (term71 A lt2 P x)). Qed.
Lemma lem313015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem313016 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term67 A lt2 x P).
Proof. exact (MK_COMB (@lem313015) (@lem313014 A lt2 x P)). Qed.
Lemma lem313017 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem313016 A lt2 x P) (@lem313011 A lt2 x P)). Qed.
Lemma lem313018 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term74 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem313017 A lt2 x P)). Qed.
Lemma lem313019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313020 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term70 A lt2 P) = (term75 A lt2 P).
Proof. exact (MK_COMB (@lem313019 A) (@lem313018 A lt2 P)). Qed.
Lemma lem313021 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term75 A lt2 P).
Proof. exact (TRANS (@lem313013 A lt2 P) (@lem313020 A lt2 P)). Qed.
Lemma lem313104 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem313105 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem313104 A P Q). Qed.
Lemma lem313106 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term79 A lt2 x P).
Proof. exact (@lem313105 A (term54 A P x) (term62 A lt2 x P)). Qed.
Lemma lem313107 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem313108 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term81 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem313107 A lt2 x P y)). Qed.
Lemma lem313109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem313110 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem313109 A) (@lem313108 A lt2 x P)). Qed.
Lemma lem313111 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem313112 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem313111 A P x) (@lem313110 A lt2 x P)). Qed.
Lemma lem313113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem313114 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term83 A lt2 x P) = (term84 A lt2 x P).
Proof. exact (MK_COMB (@lem313113) (@lem313112 A lt2 x P)). Qed.
Lemma lem313115 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem313116 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem313117 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term85 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (MK_COMB (@lem313116 A P x) (@lem313115 A lt2 x P y)). Qed.
Lemma lem313118 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term87 A lt2 x P) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem313117 A lt2 x P y)). Qed.
Lemma lem313119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem313120 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term79 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem313119 A) (@lem313118 A lt2 x P)). Qed.
Lemma lem313121 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term78 A lt2 x P) = (term79 A lt2 x P)) = ((term66 A lt2 x P) = (term89 A lt2 x P)).
Proof. exact (MK_COMB (@lem313114 A lt2 x P) (@lem313120 A lt2 x P)). Qed.
Lemma lem313122 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term66 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (EQ_MP (@lem313121 A lt2 x P) (@lem313106 A lt2 x P)). Qed.
Lemma lem313123 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem313122 A lt2 x P)). Qed.
Lemma lem313124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313125 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem313124 A) (@lem313123 A lt2 P)). Qed.
Lemma lem313127 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem313128 {A : Type'} (P : type1402 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem313127 A A P). Qed.
Lemma lem313129 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term97 A lt2 P).
Proof. exact (@lem313128 A (term98 A lt2 P)). Qed.
Lemma lem313130 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem313131 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem313132 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term101 A lt2 x P y).
Proof. exact (MK_COMB (@lem313130 A lt2 x P) (@lem313131 A y)). Qed.
Lemma lem313133 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term101 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (eq_refl (term101 A lt2 x P y)). Qed.
Lemma lem313134 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term86 A lt2 x P y).
Proof. exact (TRANS (@lem313132 A lt2 x P y) (@lem313133 A lt2 x P y)). Qed.
Lemma lem313135 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term102 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem313134 A lt2 x P y)). Qed.
Lemma lem313136 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem313137 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term103 A lt2 P x) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem313136 A) (@lem313135 A lt2 x P)). Qed.
Lemma lem313138 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term104 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem313137 A lt2 x P)). Qed.
Lemma lem313139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313140 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem313139 A) (@lem313138 A lt2 P)). Qed.
Lemma lem313141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem313142 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term105 A lt2 P) = (term106 A lt2 P).
Proof. exact (MK_COMB (@lem313141) (@lem313140 A lt2 P)). Qed.
Lemma lem313143 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem313144 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem313145 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term108 A lt2 P y x).
Proof. exact (MK_COMB (@lem313143 A lt2 x P) (@lem313144 A y x)). Qed.
Lemma lem313146 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term108 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (eq_refl (term108 A lt2 P y x)). Qed.
Lemma lem313147 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (TRANS (@lem313145 A lt2 P y x) (@lem313146 A lt2 P y x)). Qed.
Lemma lem313148 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term110 A lt2 P y) = (term111 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem313147 A lt2 P y x)). Qed.
Lemma lem313149 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313150 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term112 A lt2 P y) = (term113 A lt2 P y).
Proof. exact (MK_COMB (@lem313149 A) (@lem313148 A lt2 P y)). Qed.
Lemma lem313151 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term114 A lt2 P) = (term115 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem313150 A lt2 P y)). Qed.
Lemma lem313152 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem313153 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term97 A lt2 P) = (term116 A lt2 P).
Proof. exact (MK_COMB (@lem313152 A) (@lem313151 A lt2 P)). Qed.
Lemma lem313154 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term96 A lt2 P) = (term97 A lt2 P)) = ((term91 A lt2 P) = (term116 A lt2 P)).
Proof. exact (MK_COMB (@lem313142 A lt2 P) (@lem313153 A lt2 P)). Qed.
Lemma lem313155 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term116 A lt2 P).
Proof. exact (EQ_MP (@lem313154 A lt2 P) (@lem313129 A lt2 P)). Qed.
Lemma lem313157 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem313125 A lt2 P) (@lem313155 A lt2 P)). Qed.
Lemma lem313158 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem313021 A lt2 P) (@lem313157 A lt2 P)). Qed.
Lemma lem313159 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term116 A lt2 P.
Proof. exact (EQ_MP (@lem313158 A lt2 P) (@lem312973 A lt2 P h1)). Qed.
Lemma lem313170 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (@lem17265 (P x) (term182 A P lt2 f x)). Qed.
Lemma lem313171 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem313170 A P lt2 f x)). Qed.
Lemma lem313172 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313225 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem313172 A) (@lem313171 A P lt2 f)). Qed.
Lemma lem313226 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem313225 A P lt2 f) (@lem312974 A P lt2 f h1)). Qed.
Lemma lem313228 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : ((term215 A s n) = (term216 A f s n)) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl ((term215 A s n) = (term216 A f s n))). Qed.
Lemma lem313229 {A : Type'} (f : A -> A) (s : nat -> A) : (term290 A f s) = (term290 A f s).
Proof. exact (fun_ext (fun n : nat => @lem313228 A f s n)). Qed.
Lemma lem313230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem313231 {A : Type'} (f : A -> A) (s : nat -> A) : (term213 A f s) = (term213 A f s).
Proof. exact (MK_COMB (@lem313230) (@lem313229 A f s)). Qed.
Lemma lem313233 {A : Type'} (s : nat -> A) (a : A) : (term291 A s a) = (term291 A s a).
Proof. exact (eq_refl (term291 A s a)). Qed.
Lemma lem313242 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term212 A a f s) = (term212 A a f s).
Proof. exact (MK_COMB (@lem313233 A s a) (@lem313231 A f s)). Qed.
Lemma lem313243 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term212 A a f s.
Proof. exact (EQ_MP (@lem313242 A a f s) (@lem312975 A a f s h1)). Qed.
Lemma lem313249 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem313254 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem313277 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (eq_refl (term292 A P lt2 f x)). Qed.
Lemma lem313278 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem313277 A P lt2 f x)). Qed.
Lemma lem313279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313280 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem313279 A) (@lem313278 A P lt2 f)). Qed.
Lemma lem313281 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem313280 A P lt2 f) (@lem313226 A P lt2 f h1)). Qed.
Lemma lem313294 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : ((term215 A s n) = (term216 A f s n)) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl ((term215 A s n) = (term216 A f s n))). Qed.
Lemma lem313295 {A : Type'} (f : A -> A) (s : nat -> A) : (term290 A f s) = (term290 A f s).
Proof. exact (fun_ext (fun n : nat => @lem313294 A f s n)). Qed.
Lemma lem313296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem313297 {A : Type'} (f : A -> A) (s : nat -> A) : (term213 A f s) = (term213 A f s).
Proof. exact (MK_COMB (@lem313296) (@lem313295 A f s)). Qed.
Lemma lem313308 {A : Type'} (s : nat -> A) (a : A) : (term291 A s a) = (term291 A s a).
Proof. exact (eq_refl (term291 A s a)). Qed.
Lemma lem313309 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term212 A a f s) = (term212 A a f s).
Proof. exact (MK_COMB (@lem313308 A s a) (@lem313297 A f s)). Qed.
Lemma lem313310 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : term212 A a f s.
Proof. exact (EQ_MP (@lem313309 A a f s) (@lem313243 A a f s h1)). Qed.
Lemma lem313320 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem313353 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem313371 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term304 A P lt2 f x).
Proof. exact (@lem19490 (term155 A P f x) (term54 A P x) (term154 A lt2 f x)). Qed.
Lemma lem313372 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term305 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem313371 A P lt2 f x)). Qed.
Lemma lem313373 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313375 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term306 A P lt2 f).
Proof. exact (MK_COMB (@lem313373 A) (@lem313372 A P lt2 f)). Qed.
Lemma lem313376 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term306 A P lt2 f.
Proof. exact (EQ_MP (@lem313375 A P lt2 f) (@lem313281 A P lt2 f h1)). Qed.
Lemma lem313380 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem313415 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term307 A P lt2 f _6847.
Proof. exact (@lem313376 A P lt2 f h1 _6847). Qed.
Lemma lem313416 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6847 : A) : (term307 A P lt2 f _6847) = (term304 A P lt2 f _6847).
Proof. exact (eq_refl (term307 A P lt2 f _6847)). Qed.
Lemma lem313417 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term304 A P lt2 f _6847.
Proof. exact (EQ_MP (@lem313416 A P lt2 f _6847) (@lem313415 A _6847 P lt2 f h1)). Qed.
Lemma lem313429 {A : Type'} (P : A -> Prop) (a : A) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem313431 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (h1 : term178 A lt2 f a) : term178 A lt2 f a.
Proof. exact (h1). Qed.
Lemma lem313433 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term343 A s) = a.
Proof. exact (proj1 (@lem313310 A a f s h1)). Qed.
Lemma lem313460 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : a = (term343 A s).
Proof. exact (SYM (@lem313433 A a f s h1)). Qed.
Lemma lem313475 {A : Type'} (P : A -> Prop) : (term397 A P) = (term397 A P).
Proof. exact (eq_refl (term397 A P)). Qed.
Lemma lem313476 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term398 A P a) = (term399 A P s).
Proof. exact (MK_COMB (@lem313475 A P) (@lem313460 A a f s h1)). Qed.
Lemma lem313477 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term399 A P s) = (term344 A P s).
Proof. exact (eq_refl (term399 A P s)). Qed.
Lemma lem313478 {A : Type'} (P : A -> Prop) (a : A) : (term400 A P a) = (term400 A P a).
Proof. exact (eq_refl (term400 A P a)). Qed.
Lemma lem313479 {A : Type'} (a : A) (P : A -> Prop) (s : nat -> A) : ((term398 A P a) = (term399 A P s)) = ((term398 A P a) = (term344 A P s)).
Proof. exact (MK_COMB (@lem313478 A P a) (@lem313477 A P s)). Qed.
Lemma lem313480 {A : Type'} (P : A -> Prop) (a : A) : (term398 A P a) = (P a).
Proof. exact (eq_refl (term398 A P a)). Qed.
Lemma lem313481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem313482 {A : Type'} (P : A -> Prop) (a : A) : (term400 A P a) = (term401 A P a).
Proof. exact (MK_COMB (@lem313481) (@lem313480 A P a)). Qed.
Lemma lem313483 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term344 A P s) = (term344 A P s).
Proof. exact (eq_refl (term344 A P s)). Qed.
Lemma lem313484 {A : Type'} (a : A) (P : A -> Prop) (s : nat -> A) : ((term398 A P a) = (term344 A P s)) = ((P a) = (term344 A P s)).
Proof. exact (MK_COMB (@lem313482 A P a) (@lem313483 A P s)). Qed.
Lemma lem313485 {A : Type'} (a : A) (P : A -> Prop) (s : nat -> A) : ((term398 A P a) = (term399 A P s)) = ((P a) = (term344 A P s)).
Proof. exact (TRANS (@lem313479 A a P s) (@lem313484 A a P s)). Qed.
Lemma lem313486 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (P a) = (term344 A P s).
Proof. exact (EQ_MP (@lem313485 A a P s) (@lem313476 A P a f s h1)). Qed.
Lemma lem313488 {A : Type'} (lt2 : type1402 A) (f : A -> A) : (term402 A lt2 f) = (term402 A lt2 f).
Proof. exact (eq_refl (term402 A lt2 f)). Qed.
Lemma lem313489 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term403 A lt2 f a) = (term404 A lt2 f s).
Proof. exact (MK_COMB (@lem313488 A lt2 f) (@lem313460 A a f s h1)). Qed.
Lemma lem313490 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term404 A lt2 f s) = (term405 A lt2 f s).
Proof. exact (eq_refl (term404 A lt2 f s)). Qed.
Lemma lem313491 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term406 A lt2 f a) = (term406 A lt2 f a).
Proof. exact (eq_refl (term406 A lt2 f a)). Qed.
Lemma lem313492 {A : Type'} (a : A) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : ((term403 A lt2 f a) = (term404 A lt2 f s)) = ((term403 A lt2 f a) = (term405 A lt2 f s)).
Proof. exact (MK_COMB (@lem313491 A lt2 f a) (@lem313490 A lt2 f s)). Qed.
Lemma lem313493 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term403 A lt2 f a) = (term178 A lt2 f a).
Proof. exact (eq_refl (term403 A lt2 f a)). Qed.
Lemma lem313494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem313495 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term406 A lt2 f a) = (term407 A lt2 f a).
Proof. exact (MK_COMB (@lem313494) (@lem313493 A lt2 f a)). Qed.
Lemma lem313496 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term405 A lt2 f s) = (term405 A lt2 f s).
Proof. exact (eq_refl (term405 A lt2 f s)). Qed.
Lemma lem313497 {A : Type'} (a : A) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : ((term403 A lt2 f a) = (term405 A lt2 f s)) = ((term178 A lt2 f a) = (term405 A lt2 f s)).
Proof. exact (MK_COMB (@lem313495 A lt2 f a) (@lem313496 A lt2 f s)). Qed.
Lemma lem313498 {A : Type'} (a : A) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : ((term403 A lt2 f a) = (term404 A lt2 f s)) = ((term178 A lt2 f a) = (term405 A lt2 f s)).
Proof. exact (TRANS (@lem313492 A a lt2 f s) (@lem313497 A a lt2 f s)). Qed.
Lemma lem313499 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term212 A a f s) : (term178 A lt2 f a) = (term405 A lt2 f s).
Proof. exact (EQ_MP (@lem313498 A a lt2 f s) (@lem313489 A lt2 a f s h1)). Qed.
Lemma lem313500 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term178 A lt2 f a) (h2 : term212 A a f s) : term405 A lt2 f s.
Proof. exact (EQ_MP (@lem313499 A lt2 a f s h2) (@lem313431 A lt2 f a h1)). Qed.
Lemma lem313570 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term159 A P lt2 f _6847.
Proof. exact (proj2 (@lem313417 A _6847 P lt2 f h1)). Qed.
Lemma lem313647 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : term344 A P s.
Proof. exact (EQ_MP (@lem313486 A P a f s h2) (@lem313429 A P a h1)). Qed.
Lemma lem313648 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : term408 A P s.
Proof. exact (fun h0 : term409 A P s => @lem313647 A P a f s h1 h2). Qed.
Lemma lem313650 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem313651 {A : Type'} (P : A -> Prop) (s : nat -> A) : (term408 A P s) = (term344 A P s).
Proof. exact (@lem313650 (term344 A P s)). Qed.
Lemma lem313652 {A : Type'} (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : P a) (h2 : term212 A a f s) : term344 A P s.
Proof. exact (EQ_MP (@lem313651 A P s) (@lem313648 A P a f s h1 h2)). Qed.
Lemma lem313658 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem313659 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : (term159 A P lt2 f _6847) = (term172 A lt2 f P _6847).
Proof. exact (@lem313658 (term154 A lt2 f _6847) (term54 A P _6847)). Qed.
Lemma lem313665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem313666 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : (term173 A P lt2 f _6847) = (term174 A lt2 f P _6847).
Proof. exact (MK_COMB (@lem313665) (@lem313659 A lt2 f P _6847)). Qed.
Lemma lem313672 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : (term172 A lt2 f P _6847) = (term172 A lt2 f P _6847).
Proof. exact (eq_refl (term172 A lt2 f P _6847)). Qed.
Lemma lem313673 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : ((term159 A P lt2 f _6847) = (term172 A lt2 f P _6847)) = ((term172 A lt2 f P _6847) = (term172 A lt2 f P _6847)).
Proof. exact (MK_COMB (@lem313666 A lt2 f P _6847) (@lem313672 A lt2 f P _6847)). Qed.
Lemma lem313675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem313676 (x : Prop) : (x = x) = True.
Proof. exact (@lem313675 Prop x). Qed.
Lemma lem313677 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : ((term172 A lt2 f P _6847) = (term172 A lt2 f P _6847)) = True.
Proof. exact (@lem313676 (term172 A lt2 f P _6847)). Qed.
Lemma lem313678 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : ((term159 A P lt2 f _6847) = (term172 A lt2 f P _6847)) = True.
Proof. exact (TRANS (@lem313673 A lt2 f P _6847) (@lem313677 A lt2 f P _6847)). Qed.
Lemma lem313679 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : True = ((term159 A P lt2 f _6847) = (term172 A lt2 f P _6847)).
Proof. exact (SYM (@lem313678 A lt2 f P _6847)). Qed.
Lemma lem313680 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6847 : A) : (term159 A P lt2 f _6847) = (term172 A lt2 f P _6847).
Proof. exact (EQ_MP (@lem313679 A lt2 f P _6847) (@lem0)). Qed.
Lemma lem313681 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term172 A lt2 f P _6847.
Proof. exact (EQ_MP (@lem313680 A lt2 f P _6847) (@lem313570 A _6847 P lt2 f h1)). Qed.
Lemma lem313683 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem313684 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6847 : A) : (term172 A lt2 f P _6847) = (term175 A P lt2 f _6847).
Proof. exact (@lem313683 (term54 A P _6847) (term154 A lt2 f _6847)). Qed.
Lemma lem313686 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem313687 {A : Type'} (P : A -> Prop) (_6847 : A) : (term49 A P _6847) = (P _6847).
Proof. exact (@lem313686 (P _6847)). Qed.
Lemma lem313688 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem313689 {A : Type'} (P : A -> Prop) (_6847 : A) : (term168 A P _6847) = (term23 A P _6847).
Proof. exact (MK_COMB (@lem313688) (@lem313687 A P _6847)). Qed.
Lemma lem313690 {A : Type'} (lt2 : type1402 A) (f : A -> A) (_6847 : A) : (term154 A lt2 f _6847) = (term154 A lt2 f _6847).
Proof. exact (eq_refl (term154 A lt2 f _6847)). Qed.
Lemma lem313691 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6847 : A) : (term175 A P lt2 f _6847) = (term176 A P lt2 f _6847).
Proof. exact (MK_COMB (@lem313689 A P _6847) (@lem313690 A lt2 f _6847)). Qed.
Lemma lem313692 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6847 : A) : (term172 A lt2 f P _6847) = (term176 A P lt2 f _6847).
Proof. exact (TRANS (@lem313684 A P lt2 f _6847) (@lem313691 A P lt2 f _6847)). Qed.
Lemma lem313695 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6847.
Proof. exact (EQ_MP (@lem313692 A P lt2 f _6847) (@lem313681 A _6847 P lt2 f h1)). Qed.
Lemma lem313696 {A : Type'} (_6847 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6847.
Proof. exact (@lem313695 A _6847 P lt2 f h1). Qed.
Lemma lem313697 {A : Type'} (s : nat -> A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term410 A P lt2 f s.
Proof. exact (@lem313696 A (term343 A s) P lt2 f h1). Qed.
Lemma lem313700 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : P a) (h3 : term212 A a f s) : term411 A lt2 f s.
Proof. exact (@lem313697 A s P lt2 f h1 (@lem313652 A P a f s h2 h3)). Qed.
Lemma lem313701 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : P a) (h3 : term212 A a f s) : term412 A lt2 f s.
Proof. exact (fun h0 : term405 A lt2 f s => @lem313700 A lt2 P a f s h1 h2 h3). Qed.
Lemma lem313703 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem313704 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term412 A lt2 f s) = (term411 A lt2 f s).
Proof. exact (@lem313703 (term411 A lt2 f s)). Qed.
Lemma lem313705 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : P a) (h3 : term212 A a f s) : term411 A lt2 f s.
Proof. exact (EQ_MP (@lem313704 A lt2 f s) (@lem313701 A lt2 P a f s h1 h2 h3)). Qed.
Lemma lem313708 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem313710 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) : (term405 A lt2 f s) = (term413 A lt2 f s).
Proof. exact (@lem313708 (term411 A lt2 f s)). Qed.
Lemma lem313713 {A : Type'} (lt2 : type1402 A) (a : A) (f : A -> A) (s : nat -> A) (h1 : term178 A lt2 f a) (h2 : term212 A a f s) : term413 A lt2 f s.
Proof. exact (EQ_MP (@lem313710 A lt2 f s) (@lem313500 A lt2 a f s h1 h2)). Qed.
Lemma lem313716 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (@lem313713 A lt2 a f s h2 h4 (@lem313705 A lt2 P a f s h1 h3 h4)). Qed.
Lemma lem313717 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : term184.
Proof. exact (fun h0 : ~ False => @lem313716 A lt2 P a f s h1 h2 h3 h4). Qed.
Lemma lem313719 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem313720 : term184 = False.
Proof. exact (@lem313719 False). Qed.
Lemma lem313722 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313720) (@lem313717 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem313723 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h5 : term178 A lt2 f a => @lem313722 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313431 A lt2 f a h2)). Qed.
Lemma lem313724 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313723 A lt2 P a f s h1 h2 h3 h4) (@lem313431 A lt2 f a h2)). Qed.
Lemma lem313725 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (P a) = False.
Proof. exact (prop_ext (fun h5 : P a => @lem313724 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313429 A P a h3)). Qed.
Lemma lem313726 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313725 A lt2 P a f s h1 h2 h3 h4) (@lem313429 A P a h3)). Qed.
Lemma lem313727 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h5 : term178 A lt2 f a => @lem313726 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313380 A lt2 f a h2)). Qed.
Lemma lem313728 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313727 A lt2 P a f s h1 h2 h3 h4) (@lem313380 A lt2 f a h2)). Qed.
Lemma lem313729 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (P a) = False.
Proof. exact (prop_ext (fun h5 : P a => @lem313728 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313353 A P a h3)). Qed.
Lemma lem313730 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313729 A lt2 P a f s h1 h2 h3 h4) (@lem313353 A P a h3)). Qed.
Lemma lem313731 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h5 : term178 A lt2 f a => @lem313730 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313380 A lt2 f a h2)). Qed.
Lemma lem313732 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313731 A lt2 P a f s h1 h2 h3 h4) (@lem313380 A lt2 f a h2)). Qed.
Lemma lem313733 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (P a) = False.
Proof. exact (prop_ext (fun h5 : P a => @lem313732 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313353 A P a h3)). Qed.
Lemma lem313734 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313733 A lt2 P a f s h1 h2 h3 h4) (@lem313353 A P a h3)). Qed.
Lemma lem313735 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h5 : term178 A lt2 f a => @lem313734 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313320 A lt2 f a h2)). Qed.
Lemma lem313736 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313735 A lt2 P a f s h1 h2 h3 h4) (@lem313320 A lt2 f a h2)). Qed.
Lemma lem313737 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (term212 A a f s) = False.
Proof. exact (prop_ext (fun h5 : term212 A a f s => @lem313736 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313310 A a f s h4)). Qed.
Lemma lem313738 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313737 A lt2 P a f s h1 h2 h3 h4) (@lem313310 A a f s h4)). Qed.
Lemma lem313739 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : (P a) = False.
Proof. exact (prop_ext (fun h5 : P a => @lem313738 A lt2 P a f s h1 h2 h3 h4) (fun h5 : False => @lem313254 A P a h3)). Qed.
Lemma lem313740 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term178 A lt2 f a) (h3 : P a) (h4 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313739 A lt2 P a f s h1 h2 h3 h4) (@lem313254 A P a h3)). Qed.
Lemma lem313741 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (ex_elim (@lem313159 A lt2 P h2) (fun y : A -> A => fun h0 : term115 A lt2 P y => @lem313740 A lt2 P a f s h1 h3 h4 h5)). Qed.
Lemma lem313742 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h6 : term178 A lt2 f a => @lem313741 A lt2 P a f s h1 h2 h3 h4 h5) (fun h6 : False => @lem313249 A lt2 f a h3)). Qed.
Lemma lem313743 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313742 A lt2 P a f s h1 h2 h3 h4 h5) (@lem313249 A lt2 f a h3)). Qed.
Lemma lem313744 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : (term212 A a f s) = False.
Proof. exact (prop_ext (fun h6 : term212 A a f s => @lem313743 A lt2 P a f s h1 h2 h3 h4 h5) (fun h6 : False => @lem313243 A a f s h5)). Qed.
Lemma lem313745 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313744 A lt2 P a f s h1 h2 h3 h4 h5) (@lem313243 A a f s h5)). Qed.
Lemma lem313746 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : (P a) = False.
Proof. exact (prop_ext (fun h6 : P a => @lem313745 A lt2 P a f s h1 h2 h3 h4 h5) (fun h6 : False => @lem312986 A P a h4)). Qed.
Lemma lem313747 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313746 A lt2 P a f s h1 h2 h3 h4 h5) (@lem312986 A P a h4)). Qed.
Lemma lem313748 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h6 : term178 A lt2 f a => @lem313747 A lt2 P a f s h1 h2 h3 h4 h5) (fun h6 : False => @lem312980 A lt2 f a h3)). Qed.
Lemma lem313749 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313748 A lt2 P a f s h1 h2 h3 h4 h5) (@lem312980 A lt2 f a h3)). Qed.
Lemma lem313750 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term364 A lt2 f a.
Proof. exact (fun h0 : term178 A lt2 f a => @lem313749 A lt2 P a f s h1 h2 h0 h3 h4). Qed.
Lemma lem313751 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term154 A lt2 f a.
Proof. exact (EQ_MP (@lem312979 A lt2 f a) (@lem313750 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem313752 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term371 A s lt2 f a.
Proof. exact (fun h0 : term212 A a f s => @lem313751 A lt2 P a f s h1 h2 h3 h0). Qed.
Lemma lem313753 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term373 A P s lt2 f a.
Proof. exact (fun h0 : term204 A P lt2 f => @lem313752 A s f lt2 P a h0 h1 h2). Qed.
Lemma lem313754 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (a : A) (h1 : P a) : term375 A P s lt2 f a.
Proof. exact (fun h0 : term9 A lt2 P => @lem313753 A s f lt2 P a h0 h1). Qed.
Lemma lem313755 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term376 A P s lt2 f a.
Proof. exact (fun h0 : P a => @lem313754 A s lt2 f P a h0). Qed.
Lemma lem313760 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term380 A s lt2 f a.
Proof. exact (fun P : A -> Prop => @lem313755 A P s lt2 f a). Qed.
Lemma lem313765 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : term384 A lt2 f a.
Proof. exact (fun s : nat -> A => @lem313760 A s lt2 f a). Qed.
Lemma lem313770 {A : Type'} (f : A -> A) (a : A) : term388 A f a.
Proof. exact (fun lt2 : type1402 A => @lem313765 A lt2 f a). Qed.
Lemma lem313775 {A : Type'} (a : A) : term392 A a.
Proof. exact (fun f : A -> A => @lem313770 A f a). Qed.
Lemma lem313780 {A : Type'} : term396 A.
Proof. exact (fun a : A => @lem313775 A a). Qed.
Lemma lem313781 {A : Type'} : term395 A.
Proof. exact (EQ_MP (@lem312971 A) (@lem313780 A)). Qed.
Lemma lem313782 {A : Type'} (a : A) : term414 A a.
Proof. exact (@lem313781 A a). Qed.
Lemma lem313783 {A : Type'} (a : A) : (term414 A a) = (term391 A a).
Proof. exact (eq_refl (term414 A a)). Qed.
Lemma lem313784 {A : Type'} (a : A) : term391 A a.
Proof. exact (EQ_MP (@lem313783 A a) (@lem313782 A a)). Qed.
Lemma lem313785 {A : Type'} (a : A) (f : A -> A) : term415 A a f.
Proof. exact (@lem313784 A a f). Qed.
Lemma lem313786 {A : Type'} (f : A -> A) (a : A) : (term415 A a f) = (term387 A f a).
Proof. exact (eq_refl (term415 A a f)). Qed.
Lemma lem313787 {A : Type'} (f : A -> A) (a : A) : term387 A f a.
Proof. exact (EQ_MP (@lem313786 A f a) (@lem313785 A a f)). Qed.
Lemma lem313788 {A : Type'} (f : A -> A) (a : A) (lt2 : type1402 A) : term416 A f a lt2.
Proof. exact (@lem313787 A f a lt2). Qed.
Lemma lem313789 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : (term416 A f a lt2) = (term383 A lt2 f a).
Proof. exact (eq_refl (term416 A f a lt2)). Qed.
Lemma lem313790 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) : term383 A lt2 f a.
Proof. exact (EQ_MP (@lem313789 A lt2 f a) (@lem313788 A f a lt2)). Qed.
Lemma lem313791 {A : Type'} (lt2 : type1402 A) (f : A -> A) (a : A) (s : nat -> A) : term417 A lt2 f a s.
Proof. exact (@lem313790 A lt2 f a s). Qed.
Lemma lem313792 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term417 A lt2 f a s) = (term379 A s lt2 f a).
Proof. exact (eq_refl (term417 A lt2 f a s)). Qed.
Lemma lem313793 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term379 A s lt2 f a.
Proof. exact (EQ_MP (@lem313792 A s lt2 f a) (@lem313791 A lt2 f a s)). Qed.
Lemma lem313794 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) (P : A -> Prop) : term418 A s lt2 f a P.
Proof. exact (@lem313793 A s lt2 f a P). Qed.
Lemma lem313795 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : (term418 A s lt2 f a P) = (term365 A P s lt2 f a).
Proof. exact (eq_refl (term418 A s lt2 f a P)). Qed.
Lemma lem313796 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term365 A P s lt2 f a.
Proof. exact (EQ_MP (@lem313795 A P s lt2 f a) (@lem313794 A s lt2 f a P)). Qed.
Lemma lem313798 {A : Type'} (P : A -> Prop) (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (a : A) : term365 A P s lt2 f a.
Proof. exact (@lem312687 A P s lt2 f a (@lem313796 A P s lt2 f a)). Qed.
Lemma lem313799 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (a : A) (h1 : P a) : term374 A P s lt2 f a.
Proof. exact (@lem313798 A P s lt2 f a (@lem310249 A P a h1)). Qed.
Lemma lem313800 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term372 A P s lt2 f a.
Proof. exact (@lem313799 A s lt2 f P a h2 (@lem310247 A lt2 P h1)). Qed.
Lemma lem313801 {A : Type'} (s : nat -> A) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term370 A s lt2 f a.
Proof. exact (@lem313800 A s f lt2 P a h2 h3 (@lem311163 A P lt2 f h1)). Qed.
Lemma lem313802 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term364 A lt2 f a.
Proof. exact (@lem313801 A s f lt2 P a h1 h2 h3 (@lem311164 A a f s h4)). Qed.
Lemma lem313803 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (@lem313802 A lt2 P a f s h1 h2 h4 h5 (@lem312671 A lt2 f a h3)). Qed.
Lemma lem313804 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : (term178 A lt2 f a) = False.
Proof. exact (prop_ext (fun h6 : term178 A lt2 f a => @lem313803 A lt2 P a f s h1 h2 h3 h4 h5) (fun h6 : False => @lem312671 A lt2 f a h3)). Qed.
Lemma lem313805 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term178 A lt2 f a) (h4 : P a) (h5 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem313804 A lt2 P a f s h1 h2 h3 h4 h5) (@lem312671 A lt2 f a h3)). Qed.
Lemma lem313806 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term364 A lt2 f a.
Proof. exact (fun h0 : term178 A lt2 f a => @lem313805 A lt2 P a f s h1 h2 h0 h3 h4). Qed.
Lemma lem313807 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term154 A lt2 f a.
Proof. exact (EQ_MP (@lem312670 A lt2 f a) (@lem313806 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem313809 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem313810 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term363 A P lt2 f s n) = (term419 A P lt2 f s n).
Proof. exact (@lem313809 (term363 A P lt2 f s n)). Qed.
Lemma lem313811 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term419 A P lt2 f s n) = (term363 A P lt2 f s n).
Proof. exact (SYM (@lem313810 A P lt2 f s n)). Qed.
Lemma lem313812 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term420 A P lt2 f s n) : term420 A P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem313815 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term421 A a P lt2 f s n) : term421 A a P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem313816 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term422 A a P lt2 f s n.
Proof. exact (fun h0 : term421 A a P lt2 f s n => @lem313815 A a P lt2 f s n h0). Qed.
Lemma lem313817 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term422 A a P lt2 f s n) : term422 A a P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem313818 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term421 A a P lt2 f s n) : term421 A a P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem313819 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term421 A a P lt2 f s n) (h2 : term422 A a P lt2 f s n) : term421 A a P lt2 f s n.
Proof. exact (@lem313817 A a P lt2 f s n h2 (@lem313818 A a P lt2 f s n h1)). Qed.
Lemma lem313820 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term421 A a P lt2 f s n) : term423 A a P lt2 f s n.
Proof. exact (fun h0 : term422 A a P lt2 f s n => @lem313819 A a P lt2 f s n h1 h0). Qed.
Lemma lem313821 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term422 A a P lt2 f s n) : term422 A a P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem313822 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term421 A a P lt2 f s n) (h2 : term422 A a P lt2 f s n) : term421 A a P lt2 f s n.
Proof. exact (@lem313820 A a P lt2 f s n h1 (@lem313821 A a P lt2 f s n h2)). Qed.
Lemma lem313823 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term422 A a P lt2 f s n) : term422 A a P lt2 f s n.
Proof. exact (fun h0 : term421 A a P lt2 f s n => @lem313822 A a P lt2 f s n h0 h1). Qed.
Lemma lem313824 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term424 A a P lt2 f s n.
Proof. exact (fun h0 : term422 A a P lt2 f s n => @lem313823 A a P lt2 f s n h0). Qed.
Lemma lem313827 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term422 A a P lt2 f s n.
Proof. exact (@lem313824 A a P lt2 f s n (@lem313816 A a P lt2 f s n)). Qed.
Lemma lem313828 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term422 A a P lt2 f s n.
Proof. exact (@lem313827 A a P lt2 f s n). Qed.
Lemma lem313916 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem313917 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term419 A P lt2 f s n) = (term425 A P lt2 f s n).
Proof. exact (@lem313916 (term420 A P lt2 f s n)). Qed.
Lemma lem313919 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem313920 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term425 A P lt2 f s n) = (term363 A P lt2 f s n).
Proof. exact (@lem313919 (term363 A P lt2 f s n)). Qed.
Lemma lem313923 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term419 A P lt2 f s n) = (term363 A P lt2 f s n).
Proof. exact (TRANS (@lem313917 A P lt2 f s n) (@lem313920 A P lt2 f s n)). Qed.
Lemma lem313924 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term327 A P lt2 s n) = (term327 A P lt2 s n).
Proof. exact (eq_refl (term327 A P lt2 s n)). Qed.
Lemma lem313925 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term426 A P lt2 f s n) = (term427 A P lt2 f s n).
Proof. exact (MK_COMB (@lem313924 A P lt2 s n) (@lem313923 A P lt2 f s n)). Qed.
Lemma lem313928 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (eq_refl (term261 A a f s)). Qed.
Lemma lem313929 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term428 A a P lt2 f s n) = (term429 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem313928 A a f s) (@lem313925 A P lt2 f s n)). Qed.
Lemma lem313932 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (eq_refl (term264 A P lt2 f)). Qed.
Lemma lem313933 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term430 A a P lt2 f s n) = (term431 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem313932 A P lt2 f) (@lem313929 A a P lt2 f s n)). Qed.
Lemma lem313936 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (eq_refl (term20 A lt2 P)). Qed.
Lemma lem313937 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term432 A a P lt2 f s n) = (term433 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem313936 A lt2 P) (@lem313933 A a P lt2 f s n)). Qed.
Lemma lem313940 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem313941 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term421 A a P lt2 f s n) = (term434 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem313940 A P a) (@lem313937 A a P lt2 f s n)). Qed.
Lemma lem313944 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term435 A P lt2 f s n) = (term436 A P lt2 f s n).
Proof. exact (fun_ext (fun a : A => @lem313941 A a P lt2 f s n)). Qed.
Lemma lem313945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem313946 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term437 A P lt2 f s n) = (term438 A P lt2 f s n).
Proof. exact (MK_COMB (@lem313945 A) (@lem313944 A P lt2 f s n)). Qed.
Lemma lem313951 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term439 A lt2 f s n) = (term440 A lt2 f s n).
Proof. exact (fun_ext (fun P : A -> Prop => @lem313946 A P lt2 f s n)). Qed.
Lemma lem313952 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem313953 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term441 A lt2 f s n) = (term442 A lt2 f s n).
Proof. exact (MK_COMB (@lem313952 A) (@lem313951 A lt2 f s n)). Qed.
Lemma lem313958 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term443 A f s n) = (term444 A f s n).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem313953 A lt2 f s n)). Qed.
Lemma lem313959 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem313960 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term445 A f s n) = (term446 A f s n).
Proof. exact (MK_COMB (@lem313959 A) (@lem313958 A f s n)). Qed.
Lemma lem313965 {A : Type'} (s : nat -> A) (n : nat) : (term447 A s n) = (term448 A s n).
Proof. exact (fun_ext (fun f : A -> A => @lem313960 A f s n)). Qed.
Lemma lem313966 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem313967 {A : Type'} (s : nat -> A) (n : nat) : (term449 A s n) = (term450 A s n).
Proof. exact (MK_COMB (@lem313966 A) (@lem313965 A s n)). Qed.
Lemma lem313972 {A : Type'} (n : nat) : (term451 A n) = (term452 A n).
Proof. exact (fun_ext (fun s : nat -> A => @lem313967 A s n)). Qed.
Lemma lem313973 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem313974 {A : Type'} (n : nat) : (term453 A n) = (term454 A n).
Proof. exact (MK_COMB (@lem313973 A) (@lem313972 A n)). Qed.
Lemma lem313979 {A : Type'} : (term455 A) = (term456 A).
Proof. exact (fun_ext (fun n : nat => @lem313974 A n)). Qed.
Lemma lem313980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem313989 {A : Type'} : (term457 A) = (term458 A).
Proof. exact (MK_COMB (@lem313980) (@lem313979 A)). Qed.
Lemma lem314002 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term427 A P lt2 f s n) = (term427 A P lt2 f s n).
Proof. exact (eq_refl (term427 A P lt2 f s n)). Qed.
Lemma lem314003 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : ((term215 A s n) = (term216 A f s n)) = ((term215 A s n) = (term216 A f s n)).
Proof. exact (eq_refl ((term215 A s n) = (term216 A f s n))). Qed.
Lemma lem314004 {A : Type'} (f : A -> A) (s : nat -> A) : (term290 A f s) = (term290 A f s).
Proof. exact (fun_ext (fun n : nat => @lem314003 A f s n)). Qed.
Lemma lem314005 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem314006 {A : Type'} (f : A -> A) (s : nat -> A) : (term213 A f s) = (term213 A f s).
Proof. exact (MK_COMB (@lem314005) (@lem314004 A f s)). Qed.
Lemma lem314009 {A : Type'} (s : nat -> A) (a : A) : (term291 A s a) = (term291 A s a).
Proof. exact (eq_refl (term291 A s a)). Qed.
Lemma lem314010 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term212 A a f s) = (term212 A a f s).
Proof. exact (MK_COMB (@lem314009 A s a) (@lem314006 A f s)). Qed.
Lemma lem314011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem314012 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) : (term261 A a f s) = (term261 A a f s).
Proof. exact (MK_COMB (@lem314011) (@lem314010 A a f s)). Qed.
Lemma lem314013 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term429 A a P lt2 f s n) = (term429 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem314012 A a f s) (@lem314002 A P lt2 f s n)). Qed.
Lemma lem314022 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term200 A P lt2 f x).
Proof. exact (eq_refl (term200 A P lt2 f x)). Qed.
Lemma lem314023 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term202 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem314022 A P lt2 f x)). Qed.
Lemma lem314024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314025 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term204 A P lt2 f).
Proof. exact (MK_COMB (@lem314024 A) (@lem314023 A P lt2 f)). Qed.
Lemma lem314026 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem314027 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term264 A P lt2 f) = (term264 A P lt2 f).
Proof. exact (MK_COMB (@lem314026) (@lem314025 A P lt2 f)). Qed.
Lemma lem314028 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term431 A a P lt2 f s n) = (term431 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem314027 A P lt2 f) (@lem314013 A a P lt2 f s n)). Qed.
Lemma lem314035 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term41 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term41 A lt2 x P y)). Qed.
Lemma lem314036 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term42 A lt2 x P) = (term42 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem314035 A lt2 x P y)). Qed.
Lemma lem314037 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314038 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term43 A lt2 x P) = (term43 A lt2 x P).
Proof. exact (MK_COMB (@lem314037 A) (@lem314036 A lt2 x P)). Qed.
Lemma lem314041 {A : Type'} (P : A -> Prop) (x : A) : (term44 A P x) = (term44 A P x).
Proof. exact (eq_refl (term44 A P x)). Qed.
Lemma lem314042 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term45 A lt2 x P) = (term45 A lt2 x P).
Proof. exact (MK_COMB (@lem314041 A P x) (@lem314038 A lt2 x P)). Qed.
Lemma lem314043 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term46 A lt2 P) = (term46 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem314042 A lt2 x P)). Qed.
Lemma lem314044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem314045 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term8 A lt2 P) = (term8 A lt2 P).
Proof. exact (MK_COMB (@lem314044 A) (@lem314043 A lt2 P)). Qed.
Lemma lem314046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem314047 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term9 A lt2 P).
Proof. exact (MK_COMB (@lem314046) (@lem314045 A lt2 P)). Qed.
Lemma lem314048 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem314049 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term20 A lt2 P) = (term20 A lt2 P).
Proof. exact (MK_COMB (@lem314048) (@lem314047 A lt2 P)). Qed.
Lemma lem314050 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term433 A a P lt2 f s n) = (term433 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem314049 A lt2 P) (@lem314028 A a P lt2 f s n)). Qed.
Lemma lem314053 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = (term23 A P a).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem314054 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term434 A a P lt2 f s n) = (term434 A a P lt2 f s n).
Proof. exact (MK_COMB (@lem314053 A P a) (@lem314050 A a P lt2 f s n)). Qed.
Lemma lem314055 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term436 A P lt2 f s n) = (term436 A P lt2 f s n).
Proof. exact (fun_ext (fun a : A => @lem314054 A a P lt2 f s n)). Qed.
Lemma lem314056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314057 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term438 A P lt2 f s n) = (term438 A P lt2 f s n).
Proof. exact (MK_COMB (@lem314056 A) (@lem314055 A P lt2 f s n)). Qed.
Lemma lem314058 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term440 A lt2 f s n) = (term440 A lt2 f s n).
Proof. exact (fun_ext (fun P : A -> Prop => @lem314057 A P lt2 f s n)). Qed.
Lemma lem314059 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem314060 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term442 A lt2 f s n) = (term442 A lt2 f s n).
Proof. exact (MK_COMB (@lem314059 A) (@lem314058 A lt2 f s n)). Qed.
Lemma lem314061 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term444 A f s n) = (term444 A f s n).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem314060 A lt2 f s n)). Qed.
Lemma lem314062 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem314063 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term446 A f s n) = (term446 A f s n).
Proof. exact (MK_COMB (@lem314062 A) (@lem314061 A f s n)). Qed.
Lemma lem314064 {A : Type'} (s : nat -> A) (n : nat) : (term448 A s n) = (term448 A s n).
Proof. exact (fun_ext (fun f : A -> A => @lem314063 A f s n)). Qed.
Lemma lem314065 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem314066 {A : Type'} (s : nat -> A) (n : nat) : (term450 A s n) = (term450 A s n).
Proof. exact (MK_COMB (@lem314065 A) (@lem314064 A s n)). Qed.
Lemma lem314067 {A : Type'} (n : nat) : (term452 A n) = (term452 A n).
Proof. exact (fun_ext (fun s : nat -> A => @lem314066 A s n)). Qed.
Lemma lem314068 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem314069 {A : Type'} (n : nat) : (term454 A n) = (term454 A n).
Proof. exact (MK_COMB (@lem314068 A) (@lem314067 A n)). Qed.
Lemma lem314070 {A : Type'} : (term456 A) = (term456 A).
Proof. exact (fun_ext (fun n : nat => @lem314069 A n)). Qed.
Lemma lem314071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem314072 {A : Type'} : (term458 A) = (term458 A).
Proof. exact (MK_COMB (@lem314071) (@lem314070 A)). Qed.
Lemma lem314159 {A : Type'} : (term457 A) = (term458 A).
Proof. exact (TRANS (@lem313989 A) (@lem314072 A)). Qed.
Lemma lem314160 {A : Type'} : (term458 A) = (term457 A).
Proof. exact (SYM (@lem314159 A)). Qed.
Lemma lem314162 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term9 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem314163 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term204 A P lt2 f.
Proof. exact (h1). Qed.
Lemma lem314167 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem314168 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term363 A P lt2 f s n) = (term419 A P lt2 f s n).
Proof. exact (@lem314167 (term363 A P lt2 f s n)). Qed.
Lemma lem314169 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term419 A P lt2 f s n) = (term363 A P lt2 f s n).
Proof. exact (SYM (@lem314168 A P lt2 f s n)). Qed.
Lemma lem314170 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term420 A P lt2 f s n) : term420 A P lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem314181 {A : Type'} (P : A -> Prop) (y : A) : (term49 A P y) = (P y).
Proof. exact (@lem16933 (P y)). Qed.
Lemma lem314183 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term50 A lt2 y x) = (term50 A lt2 y x).
Proof. exact (eq_refl (term50 A lt2 y x)). Qed.
Lemma lem314184 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term51 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (MK_COMB (@lem314183 A lt2 y x) (@lem314181 A P y)). Qed.
Lemma lem314185 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term51 A lt2 x P y).
Proof. exact (@lem17362 (lt2 y x) (term54 A P y)). Qed.
Lemma lem314186 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term53 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem314185 A lt2 x P y) (@lem314184 A lt2 x P y)). Qed.
Lemma lem314187 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem314188 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term58 A lt2 x P).
Proof. exact (@lem314187 A (term42 A lt2 x P)). Qed.
Lemma lem314189 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term59 A lt2 x P y) = (term41 A lt2 x P y).
Proof. exact (eq_refl (term59 A lt2 x P y)). Qed.
Lemma lem314190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem314191 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term53 A lt2 x P y).
Proof. exact (MK_COMB (@lem314190) (@lem314189 A lt2 x P y)). Qed.
Lemma lem314192 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term60 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (TRANS (@lem314191 A lt2 x P y) (@lem314186 A lt2 x P y)). Qed.
Lemma lem314193 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term61 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem314192 A lt2 x P y)). Qed.
Lemma lem314194 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem314195 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term58 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem314194 A) (@lem314193 A lt2 x P)). Qed.
Lemma lem314196 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term57 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (TRANS (@lem314188 A lt2 x P) (@lem314195 A lt2 x P)). Qed.
Lemma lem314198 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem314199 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term65 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem314198 A P x) (@lem314196 A lt2 x P)). Qed.
Lemma lem314200 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term65 A lt2 x P).
Proof. exact (@lem17045 (P x) (term43 A lt2 x P)). Qed.
Lemma lem314201 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term67 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem314200 A lt2 x P) (@lem314199 A lt2 x P)). Qed.
Lemma lem314202 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem314203 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term70 A lt2 P).
Proof. exact (@lem314202 A (term46 A lt2 P)). Qed.
Lemma lem314204 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term71 A lt2 P x) = (term45 A lt2 x P).
Proof. exact (eq_refl (term71 A lt2 P x)). Qed.
Lemma lem314205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem314206 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term67 A lt2 x P).
Proof. exact (MK_COMB (@lem314205) (@lem314204 A lt2 x P)). Qed.
Lemma lem314207 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term72 A lt2 P x) = (term66 A lt2 x P).
Proof. exact (TRANS (@lem314206 A lt2 x P) (@lem314201 A lt2 x P)). Qed.
Lemma lem314208 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term73 A lt2 P) = (term74 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem314207 A lt2 x P)). Qed.
Lemma lem314209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314210 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term70 A lt2 P) = (term75 A lt2 P).
Proof. exact (MK_COMB (@lem314209 A) (@lem314208 A lt2 P)). Qed.
Lemma lem314211 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term75 A lt2 P).
Proof. exact (TRANS (@lem314203 A lt2 P) (@lem314210 A lt2 P)). Qed.
Lemma lem314294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem314295 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem314294 A P Q). Qed.
Lemma lem314296 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term79 A lt2 x P).
Proof. exact (@lem314295 A (term54 A P x) (term62 A lt2 x P)). Qed.
Lemma lem314297 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem314298 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term81 A lt2 x P) = (term62 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem314297 A lt2 x P y)). Qed.
Lemma lem314299 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem314300 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term82 A lt2 x P) = (term63 A lt2 x P).
Proof. exact (MK_COMB (@lem314299 A) (@lem314298 A lt2 x P)). Qed.
Lemma lem314301 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem314302 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term78 A lt2 x P) = (term66 A lt2 x P).
Proof. exact (MK_COMB (@lem314301 A P x) (@lem314300 A lt2 x P)). Qed.
Lemma lem314303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem314304 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term83 A lt2 x P) = (term84 A lt2 x P).
Proof. exact (MK_COMB (@lem314303) (@lem314302 A lt2 x P)). Qed.
Lemma lem314305 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term80 A lt2 x P y) = (term52 A lt2 x P y).
Proof. exact (eq_refl (term80 A lt2 x P y)). Qed.
Lemma lem314306 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term64 A P x).
Proof. exact (eq_refl (term64 A P x)). Qed.
Lemma lem314307 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term85 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (MK_COMB (@lem314306 A P x) (@lem314305 A lt2 x P y)). Qed.
Lemma lem314308 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term87 A lt2 x P) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem314307 A lt2 x P y)). Qed.
Lemma lem314309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem314310 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term79 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem314309 A) (@lem314308 A lt2 x P)). Qed.
Lemma lem314311 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : ((term78 A lt2 x P) = (term79 A lt2 x P)) = ((term66 A lt2 x P) = (term89 A lt2 x P)).
Proof. exact (MK_COMB (@lem314304 A lt2 x P) (@lem314310 A lt2 x P)). Qed.
Lemma lem314312 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term66 A lt2 x P) = (term89 A lt2 x P).
Proof. exact (EQ_MP (@lem314311 A lt2 x P) (@lem314296 A lt2 x P)). Qed.
Lemma lem314313 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term74 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem314312 A lt2 x P)). Qed.
Lemma lem314314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314315 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem314314 A) (@lem314313 A lt2 P)). Qed.
Lemma lem314317 {A B : Type'} (P : type1413 A B) : (term92 A B P) = (term93 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem314318 {A : Type'} (P : type1402 A) : (term94 A P) = (term95 A P).
Proof. exact (@lem314317 A A P). Qed.
Lemma lem314319 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term97 A lt2 P).
Proof. exact (@lem314318 A (term98 A lt2 P)). Qed.
Lemma lem314320 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem314321 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem314322 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term101 A lt2 x P y).
Proof. exact (MK_COMB (@lem314320 A lt2 x P) (@lem314321 A y)). Qed.
Lemma lem314323 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term101 A lt2 x P y) = (term86 A lt2 x P y).
Proof. exact (eq_refl (term101 A lt2 x P y)). Qed.
Lemma lem314324 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) (y : A) : (term100 A lt2 P x y) = (term86 A lt2 x P y).
Proof. exact (TRANS (@lem314322 A lt2 x P y) (@lem314323 A lt2 x P y)). Qed.
Lemma lem314325 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term102 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (fun_ext (fun y : A => @lem314324 A lt2 x P y)). Qed.
Lemma lem314326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem314327 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term103 A lt2 P x) = (term89 A lt2 x P).
Proof. exact (MK_COMB (@lem314326 A) (@lem314325 A lt2 x P)). Qed.
Lemma lem314328 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term104 A lt2 P) = (term90 A lt2 P).
Proof. exact (fun_ext (fun x : A => @lem314327 A lt2 x P)). Qed.
Lemma lem314329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314330 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term96 A lt2 P) = (term91 A lt2 P).
Proof. exact (MK_COMB (@lem314329 A) (@lem314328 A lt2 P)). Qed.
Lemma lem314331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem314332 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term105 A lt2 P) = (term106 A lt2 P).
Proof. exact (MK_COMB (@lem314331) (@lem314330 A lt2 P)). Qed.
Lemma lem314333 {A : Type'} (lt2 : type1402 A) (x : A) (P : A -> Prop) : (term99 A lt2 P x) = (term88 A lt2 x P).
Proof. exact (eq_refl (term99 A lt2 P x)). Qed.
Lemma lem314334 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem314335 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term108 A lt2 P y x).
Proof. exact (MK_COMB (@lem314333 A lt2 x P) (@lem314334 A y x)). Qed.
Lemma lem314336 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term108 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (eq_refl (term108 A lt2 P y x)). Qed.
Lemma lem314337 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) (x : A) : (term107 A lt2 P y x) = (term109 A lt2 P y x).
Proof. exact (TRANS (@lem314335 A lt2 P y x) (@lem314336 A lt2 P y x)). Qed.
Lemma lem314338 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term110 A lt2 P y) = (term111 A lt2 P y).
Proof. exact (fun_ext (fun x : A => @lem314337 A lt2 P y x)). Qed.
Lemma lem314339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314340 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (y : A -> A) : (term112 A lt2 P y) = (term113 A lt2 P y).
Proof. exact (MK_COMB (@lem314339 A) (@lem314338 A lt2 P y)). Qed.
Lemma lem314341 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term114 A lt2 P) = (term115 A lt2 P).
Proof. exact (fun_ext (fun y : A -> A => @lem314340 A lt2 P y)). Qed.
Lemma lem314342 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem314343 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term97 A lt2 P) = (term116 A lt2 P).
Proof. exact (MK_COMB (@lem314342 A) (@lem314341 A lt2 P)). Qed.
Lemma lem314344 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : ((term96 A lt2 P) = (term97 A lt2 P)) = ((term91 A lt2 P) = (term116 A lt2 P)).
Proof. exact (MK_COMB (@lem314332 A lt2 P) (@lem314343 A lt2 P)). Qed.
Lemma lem314345 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term91 A lt2 P) = (term116 A lt2 P).
Proof. exact (EQ_MP (@lem314344 A lt2 P) (@lem314319 A lt2 P)). Qed.
Lemma lem314347 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term75 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem314315 A lt2 P) (@lem314345 A lt2 P)). Qed.
Lemma lem314348 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term9 A lt2 P) = (term116 A lt2 P).
Proof. exact (TRANS (@lem314211 A lt2 P) (@lem314347 A lt2 P)). Qed.
Lemma lem314349 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term116 A lt2 P.
Proof. exact (EQ_MP (@lem314348 A lt2 P) (@lem314162 A lt2 P h1)). Qed.
Lemma lem314360 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term200 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (@lem17265 (P x) (term182 A P lt2 f x)). Qed.
Lemma lem314361 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term202 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem314360 A P lt2 f x)). Qed.
Lemma lem314362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314415 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term204 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem314362 A) (@lem314361 A P lt2 f)). Qed.
Lemma lem314416 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem314415 A P lt2 f) (@lem314163 A P lt2 f h1)). Qed.
Lemma lem314443 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term244 A P lt2 s n.
Proof. exact (h1). Qed.
Lemma lem314454 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term420 A P lt2 f s n) = (term459 A P lt2 f s n).
Proof. exact (@lem17045 (term353 A P f s n) (term362 A lt2 f s n)). Qed.
Lemma lem314483 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term292 A P lt2 f x).
Proof. exact (eq_refl (term292 A P lt2 f x)). Qed.
Lemma lem314484 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term293 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem314483 A P lt2 f x)). Qed.
Lemma lem314485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314486 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term294 A P lt2 f).
Proof. exact (MK_COMB (@lem314485 A) (@lem314484 A P lt2 f)). Qed.
Lemma lem314487 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term294 A P lt2 f.
Proof. exact (EQ_MP (@lem314486 A P lt2 f) (@lem314416 A P lt2 f h1)). Qed.
Lemma lem314536 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term244 A P lt2 s n.
Proof. exact (h1). Qed.
Lemma lem314566 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term420 A P lt2 f s n) : term459 A P lt2 f s n.
Proof. exact (EQ_MP (@lem314454 A P lt2 f s n) (@lem314170 A P lt2 f s n h1)). Qed.
Lemma lem314621 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term304 A P lt2 f x).
Proof. exact (@lem19490 (term155 A P f x) (term54 A P x) (term154 A lt2 f x)). Qed.
Lemma lem314622 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term305 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem314621 A P lt2 f x)). Qed.
Lemma lem314623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314625 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term306 A P lt2 f).
Proof. exact (MK_COMB (@lem314623 A) (@lem314622 A P lt2 f)). Qed.
Lemma lem314626 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term306 A P lt2 f.
Proof. exact (EQ_MP (@lem314625 A P lt2 f) (@lem314487 A P lt2 f h1)). Qed.
Lemma lem314672 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term460 A P f s n) : term460 A P f s n.
Proof. exact (h1). Qed.
Lemma lem314694 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (x : A) : (term292 A P lt2 f x) = (term304 A P lt2 f x).
Proof. exact (@lem19490 (term155 A P f x) (term54 A P x) (term154 A lt2 f x)). Qed.
Lemma lem314695 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term293 A P lt2 f) = (term305 A P lt2 f).
Proof. exact (fun_ext (fun x : A => @lem314694 A P lt2 f x)). Qed.
Lemma lem314696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem314698 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) : (term294 A P lt2 f) = (term306 A P lt2 f).
Proof. exact (MK_COMB (@lem314696 A) (@lem314695 A P lt2 f)). Qed.
Lemma lem314699 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term306 A P lt2 f.
Proof. exact (EQ_MP (@lem314698 A P lt2 f) (@lem314487 A P lt2 f h1)). Qed.
Lemma lem314745 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term461 A lt2 f s n) : term461 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem314746 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term307 A P lt2 f _6882.
Proof. exact (@lem314626 A P lt2 f h1 _6882). Qed.
Lemma lem314747 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6882 : A) : (term307 A P lt2 f _6882) = (term304 A P lt2 f _6882).
Proof. exact (eq_refl (term307 A P lt2 f _6882)). Qed.
Lemma lem314748 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term304 A P lt2 f _6882.
Proof. exact (EQ_MP (@lem314747 A P lt2 f _6882) (@lem314746 A _6882 P lt2 f h1)). Qed.
Lemma lem314755 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term307 A P lt2 f _6885.
Proof. exact (@lem314699 A P lt2 f h1 _6885). Qed.
Lemma lem314756 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6885 : A) : (term307 A P lt2 f _6885) = (term304 A P lt2 f _6885).
Proof. exact (eq_refl (term307 A P lt2 f _6885)). Qed.
Lemma lem314757 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term304 A P lt2 f _6885.
Proof. exact (EQ_MP (@lem314756 A P lt2 f _6885) (@lem314755 A _6885 P lt2 f h1)). Qed.
Lemma lem314783 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term460 A P f s n) : term460 A P f s n.
Proof. exact (h1). Qed.
Lemma lem314819 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term461 A lt2 f s n) : term461 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem314927 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term460 A P f s n) : term460 A P f s n.
Proof. exact (h1). Qed.
Lemma lem314969 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term160 A P f _6882.
Proof. exact (proj1 (@lem314748 A _6882 P lt2 f h1)). Qed.
Lemma lem315067 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term461 A lt2 f s n) : term461 A lt2 f s n.
Proof. exact (h1). Qed.
Lemma lem315109 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term160 A P f _6885.
Proof. exact (proj1 (@lem314757 A _6885 P lt2 f h1)). Qed.
Lemma lem315123 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term159 A P lt2 f _6885.
Proof. exact (proj2 (@lem314757 A _6885 P lt2 f h1)). Qed.
Lemma lem315200 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term239 A P s n.
Proof. exact (proj1 (@lem314536 A P lt2 s n h1)). Qed.
Lemma lem315201 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term308 A P s n.
Proof. exact (fun h0 : term309 A P s n => @lem315200 A P lt2 s n h1). Qed.
Lemma lem315203 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315204 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term308 A P s n) = (term239 A P s n).
Proof. exact (@lem315203 (term239 A P s n)). Qed.
Lemma lem315205 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term239 A P s n.
Proof. exact (EQ_MP (@lem315204 A P s n) (@lem315201 A P lt2 s n h1)). Qed.
Lemma lem315211 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem315212 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : (term160 A P f _6882) = (term163 A f P _6882).
Proof. exact (@lem315211 (term155 A P f _6882) (term54 A P _6882)). Qed.
Lemma lem315218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315219 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : (term164 A P f _6882) = (term165 A f P _6882).
Proof. exact (MK_COMB (@lem315218) (@lem315212 A f P _6882)). Qed.
Lemma lem315225 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : (term163 A f P _6882) = (term163 A f P _6882).
Proof. exact (eq_refl (term163 A f P _6882)). Qed.
Lemma lem315226 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : ((term160 A P f _6882) = (term163 A f P _6882)) = ((term163 A f P _6882) = (term163 A f P _6882)).
Proof. exact (MK_COMB (@lem315219 A f P _6882) (@lem315225 A f P _6882)). Qed.
Lemma lem315228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem315229 (x : Prop) : (x = x) = True.
Proof. exact (@lem315228 Prop x). Qed.
Lemma lem315230 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : ((term163 A f P _6882) = (term163 A f P _6882)) = True.
Proof. exact (@lem315229 (term163 A f P _6882)). Qed.
Lemma lem315231 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : ((term160 A P f _6882) = (term163 A f P _6882)) = True.
Proof. exact (TRANS (@lem315226 A f P _6882) (@lem315230 A f P _6882)). Qed.
Lemma lem315232 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : True = ((term160 A P f _6882) = (term163 A f P _6882)).
Proof. exact (SYM (@lem315231 A f P _6882)). Qed.
Lemma lem315233 {A : Type'} (f : A -> A) (P : A -> Prop) (_6882 : A) : (term160 A P f _6882) = (term163 A f P _6882).
Proof. exact (EQ_MP (@lem315232 A f P _6882) (@lem0)). Qed.
Lemma lem315234 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term163 A f P _6882.
Proof. exact (EQ_MP (@lem315233 A f P _6882) (@lem314969 A _6882 P lt2 f h1)). Qed.
Lemma lem315236 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem315237 {A : Type'} (P : A -> Prop) (f : A -> A) (_6882 : A) : (term163 A f P _6882) = (term167 A P f _6882).
Proof. exact (@lem315236 (term54 A P _6882) (term155 A P f _6882)). Qed.
Lemma lem315239 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem315240 {A : Type'} (P : A -> Prop) (_6882 : A) : (term49 A P _6882) = (P _6882).
Proof. exact (@lem315239 (P _6882)). Qed.
Lemma lem315241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315242 {A : Type'} (P : A -> Prop) (_6882 : A) : (term168 A P _6882) = (term23 A P _6882).
Proof. exact (MK_COMB (@lem315241) (@lem315240 A P _6882)). Qed.
Lemma lem315243 {A : Type'} (P : A -> Prop) (f : A -> A) (_6882 : A) : (term155 A P f _6882) = (term155 A P f _6882).
Proof. exact (eq_refl (term155 A P f _6882)). Qed.
Lemma lem315244 {A : Type'} (P : A -> Prop) (f : A -> A) (_6882 : A) : (term167 A P f _6882) = (term169 A P f _6882).
Proof. exact (MK_COMB (@lem315242 A P _6882) (@lem315243 A P f _6882)). Qed.
Lemma lem315245 {A : Type'} (P : A -> Prop) (f : A -> A) (_6882 : A) : (term163 A f P _6882) = (term169 A P f _6882).
Proof. exact (TRANS (@lem315237 A P f _6882) (@lem315244 A P f _6882)). Qed.
Lemma lem315248 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term169 A P f _6882.
Proof. exact (EQ_MP (@lem315245 A P f _6882) (@lem315234 A _6882 P lt2 f h1)). Qed.
Lemma lem315249 {A : Type'} (_6882 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term169 A P f _6882.
Proof. exact (@lem315248 A _6882 P lt2 f h1). Qed.
Lemma lem315250 {A : Type'} (s : nat -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term462 A P f s n.
Proof. exact (@lem315249 A (s n) P lt2 f h1). Qed.
Lemma lem315253 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term353 A P f s n.
Proof. exact (@lem315250 A s n P lt2 f h1 (@lem315205 A P lt2 s n h2)). Qed.
Lemma lem315254 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term463 A P f s n.
Proof. exact (fun h0 : term460 A P f s n => @lem315253 A f P lt2 s n h1 h2). Qed.
Lemma lem315256 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315257 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) : (term463 A P f s n) = (term353 A P f s n).
Proof. exact (@lem315256 (term353 A P f s n)). Qed.
Lemma lem315258 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term353 A P f s n.
Proof. exact (EQ_MP (@lem315257 A P f s n) (@lem315254 A f P lt2 s n h1 h2)). Qed.
Lemma lem315261 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem315263 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) : (term460 A P f s n) = (term464 A P f s n).
Proof. exact (@lem315261 (term353 A P f s n)). Qed.
Lemma lem315266 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term460 A P f s n) : term464 A P f s n.
Proof. exact (EQ_MP (@lem315263 A P f s n) (@lem314927 A P f s n h1)). Qed.
Lemma lem315269 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (@lem315266 A P f s n h2 (@lem315258 A f P lt2 s n h1 h3)). Qed.
Lemma lem315270 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : term184.
Proof. exact (fun h0 : ~ False => @lem315269 A f P lt2 s n h1 h2 h3). Qed.
Lemma lem315272 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315273 : term184 = False.
Proof. exact (@lem315272 False). Qed.
Lemma lem315274 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315273) (@lem315270 A f P lt2 s n h1 h2 h3)). Qed.
Lemma lem315351 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term239 A P s n.
Proof. exact (proj1 (@lem314536 A P lt2 s n h1)). Qed.
Lemma lem315352 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term308 A P s n.
Proof. exact (fun h0 : term309 A P s n => @lem315351 A P lt2 s n h1). Qed.
Lemma lem315354 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315355 {A : Type'} (P : A -> Prop) (s : nat -> A) (n : nat) : (term308 A P s n) = (term239 A P s n).
Proof. exact (@lem315354 (term239 A P s n)). Qed.
Lemma lem315356 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term244 A P lt2 s n) : term239 A P s n.
Proof. exact (EQ_MP (@lem315355 A P s n) (@lem315352 A P lt2 s n h1)). Qed.
Lemma lem315362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem315363 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : (term160 A P f _6885) = (term163 A f P _6885).
Proof. exact (@lem315362 (term155 A P f _6885) (term54 A P _6885)). Qed.
Lemma lem315369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315370 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : (term164 A P f _6885) = (term165 A f P _6885).
Proof. exact (MK_COMB (@lem315369) (@lem315363 A f P _6885)). Qed.
Lemma lem315376 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : (term163 A f P _6885) = (term163 A f P _6885).
Proof. exact (eq_refl (term163 A f P _6885)). Qed.
Lemma lem315377 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term160 A P f _6885) = (term163 A f P _6885)) = ((term163 A f P _6885) = (term163 A f P _6885)).
Proof. exact (MK_COMB (@lem315370 A f P _6885) (@lem315376 A f P _6885)). Qed.
Lemma lem315379 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem315380 (x : Prop) : (x = x) = True.
Proof. exact (@lem315379 Prop x). Qed.
Lemma lem315381 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term163 A f P _6885) = (term163 A f P _6885)) = True.
Proof. exact (@lem315380 (term163 A f P _6885)). Qed.
Lemma lem315382 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term160 A P f _6885) = (term163 A f P _6885)) = True.
Proof. exact (TRANS (@lem315377 A f P _6885) (@lem315381 A f P _6885)). Qed.
Lemma lem315383 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : True = ((term160 A P f _6885) = (term163 A f P _6885)).
Proof. exact (SYM (@lem315382 A f P _6885)). Qed.
Lemma lem315384 {A : Type'} (f : A -> A) (P : A -> Prop) (_6885 : A) : (term160 A P f _6885) = (term163 A f P _6885).
Proof. exact (EQ_MP (@lem315383 A f P _6885) (@lem0)). Qed.
Lemma lem315385 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term163 A f P _6885.
Proof. exact (EQ_MP (@lem315384 A f P _6885) (@lem315109 A _6885 P lt2 f h1)). Qed.
Lemma lem315387 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem315388 {A : Type'} (P : A -> Prop) (f : A -> A) (_6885 : A) : (term163 A f P _6885) = (term167 A P f _6885).
Proof. exact (@lem315387 (term54 A P _6885) (term155 A P f _6885)). Qed.
Lemma lem315390 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem315391 {A : Type'} (P : A -> Prop) (_6885 : A) : (term49 A P _6885) = (P _6885).
Proof. exact (@lem315390 (P _6885)). Qed.
Lemma lem315392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315393 {A : Type'} (P : A -> Prop) (_6885 : A) : (term168 A P _6885) = (term23 A P _6885).
Proof. exact (MK_COMB (@lem315392) (@lem315391 A P _6885)). Qed.
Lemma lem315394 {A : Type'} (P : A -> Prop) (f : A -> A) (_6885 : A) : (term155 A P f _6885) = (term155 A P f _6885).
Proof. exact (eq_refl (term155 A P f _6885)). Qed.
Lemma lem315395 {A : Type'} (P : A -> Prop) (f : A -> A) (_6885 : A) : (term167 A P f _6885) = (term169 A P f _6885).
Proof. exact (MK_COMB (@lem315393 A P _6885) (@lem315394 A P f _6885)). Qed.
Lemma lem315396 {A : Type'} (P : A -> Prop) (f : A -> A) (_6885 : A) : (term163 A f P _6885) = (term169 A P f _6885).
Proof. exact (TRANS (@lem315388 A P f _6885) (@lem315395 A P f _6885)). Qed.
Lemma lem315399 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term169 A P f _6885.
Proof. exact (EQ_MP (@lem315396 A P f _6885) (@lem315385 A _6885 P lt2 f h1)). Qed.
Lemma lem315400 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term169 A P f _6885.
Proof. exact (@lem315399 A _6885 P lt2 f h1). Qed.
Lemma lem315401 {A : Type'} (s : nat -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term462 A P f s n.
Proof. exact (@lem315400 A (s n) P lt2 f h1). Qed.
Lemma lem315404 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term353 A P f s n.
Proof. exact (@lem315401 A s n P lt2 f h1 (@lem315356 A P lt2 s n h2)). Qed.
Lemma lem315405 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term463 A P f s n.
Proof. exact (fun h0 : term460 A P f s n => @lem315404 A f P lt2 s n h1 h2). Qed.
Lemma lem315407 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315408 {A : Type'} (P : A -> Prop) (f : A -> A) (s : nat -> A) (n : nat) : (term463 A P f s n) = (term353 A P f s n).
Proof. exact (@lem315407 (term353 A P f s n)). Qed.
Lemma lem315409 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term353 A P f s n.
Proof. exact (EQ_MP (@lem315408 A P f s n) (@lem315405 A f P lt2 s n h1 h2)). Qed.
Lemma lem315415 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem315416 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : (term159 A P lt2 f _6885) = (term172 A lt2 f P _6885).
Proof. exact (@lem315415 (term154 A lt2 f _6885) (term54 A P _6885)). Qed.
Lemma lem315422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315423 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : (term173 A P lt2 f _6885) = (term174 A lt2 f P _6885).
Proof. exact (MK_COMB (@lem315422) (@lem315416 A lt2 f P _6885)). Qed.
Lemma lem315429 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : (term172 A lt2 f P _6885) = (term172 A lt2 f P _6885).
Proof. exact (eq_refl (term172 A lt2 f P _6885)). Qed.
Lemma lem315430 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term159 A P lt2 f _6885) = (term172 A lt2 f P _6885)) = ((term172 A lt2 f P _6885) = (term172 A lt2 f P _6885)).
Proof. exact (MK_COMB (@lem315423 A lt2 f P _6885) (@lem315429 A lt2 f P _6885)). Qed.
Lemma lem315432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem315433 (x : Prop) : (x = x) = True.
Proof. exact (@lem315432 Prop x). Qed.
Lemma lem315434 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term172 A lt2 f P _6885) = (term172 A lt2 f P _6885)) = True.
Proof. exact (@lem315433 (term172 A lt2 f P _6885)). Qed.
Lemma lem315435 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : ((term159 A P lt2 f _6885) = (term172 A lt2 f P _6885)) = True.
Proof. exact (TRANS (@lem315430 A lt2 f P _6885) (@lem315434 A lt2 f P _6885)). Qed.
Lemma lem315436 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : True = ((term159 A P lt2 f _6885) = (term172 A lt2 f P _6885)).
Proof. exact (SYM (@lem315435 A lt2 f P _6885)). Qed.
Lemma lem315437 {A : Type'} (lt2 : type1402 A) (f : A -> A) (P : A -> Prop) (_6885 : A) : (term159 A P lt2 f _6885) = (term172 A lt2 f P _6885).
Proof. exact (EQ_MP (@lem315436 A lt2 f P _6885) (@lem0)). Qed.
Lemma lem315438 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term172 A lt2 f P _6885.
Proof. exact (EQ_MP (@lem315437 A lt2 f P _6885) (@lem315123 A _6885 P lt2 f h1)). Qed.
Lemma lem315440 (b : Prop) (a : Prop) : (a \/ b) = (term166 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem315441 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6885 : A) : (term172 A lt2 f P _6885) = (term175 A P lt2 f _6885).
Proof. exact (@lem315440 (term54 A P _6885) (term154 A lt2 f _6885)). Qed.
Lemma lem315443 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem315444 {A : Type'} (P : A -> Prop) (_6885 : A) : (term49 A P _6885) = (P _6885).
Proof. exact (@lem315443 (P _6885)). Qed.
Lemma lem315445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315446 {A : Type'} (P : A -> Prop) (_6885 : A) : (term168 A P _6885) = (term23 A P _6885).
Proof. exact (MK_COMB (@lem315445) (@lem315444 A P _6885)). Qed.
Lemma lem315447 {A : Type'} (lt2 : type1402 A) (f : A -> A) (_6885 : A) : (term154 A lt2 f _6885) = (term154 A lt2 f _6885).
Proof. exact (eq_refl (term154 A lt2 f _6885)). Qed.
Lemma lem315448 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6885 : A) : (term175 A P lt2 f _6885) = (term176 A P lt2 f _6885).
Proof. exact (MK_COMB (@lem315446 A P _6885) (@lem315447 A lt2 f _6885)). Qed.
Lemma lem315449 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (_6885 : A) : (term172 A lt2 f P _6885) = (term176 A P lt2 f _6885).
Proof. exact (TRANS (@lem315441 A P lt2 f _6885) (@lem315448 A P lt2 f _6885)). Qed.
Lemma lem315452 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6885.
Proof. exact (EQ_MP (@lem315449 A P lt2 f _6885) (@lem315438 A _6885 P lt2 f h1)). Qed.
Lemma lem315453 {A : Type'} (_6885 : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term176 A P lt2 f _6885.
Proof. exact (@lem315452 A _6885 P lt2 f h1). Qed.
Lemma lem315454 {A : Type'} (s : nat -> A) (n : nat) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (h1 : term204 A P lt2 f) : term465 A P lt2 f s n.
Proof. exact (@lem315453 A (term216 A f s n) P lt2 f h1). Qed.
Lemma lem315457 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term362 A lt2 f s n.
Proof. exact (@lem315454 A s n P lt2 f h1 (@lem315409 A f P lt2 s n h1 h2)). Qed.
Lemma lem315458 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term466 A lt2 f s n.
Proof. exact (fun h0 : term461 A lt2 f s n => @lem315457 A f P lt2 s n h1 h2). Qed.
Lemma lem315460 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315461 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term466 A lt2 f s n) = (term362 A lt2 f s n).
Proof. exact (@lem315460 (term362 A lt2 f s n)). Qed.
Lemma lem315462 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term244 A P lt2 s n) : term362 A lt2 f s n.
Proof. exact (EQ_MP (@lem315461 A lt2 f s n) (@lem315458 A f P lt2 s n h1 h2)). Qed.
Lemma lem315465 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem315467 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term461 A lt2 f s n) = (term467 A lt2 f s n).
Proof. exact (@lem315465 (term362 A lt2 f s n)). Qed.
Lemma lem315470 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (h1 : term461 A lt2 f s n) : term467 A lt2 f s n.
Proof. exact (EQ_MP (@lem315467 A lt2 f s n) (@lem315067 A lt2 f s n h1)). Qed.
Lemma lem315473 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (@lem315470 A lt2 f s n h2 (@lem315462 A f P lt2 s n h1 h3)). Qed.
Lemma lem315474 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : term184.
Proof. exact (fun h0 : ~ False => @lem315473 A f P lt2 s n h1 h2 h3). Qed.
Lemma lem315476 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem315477 : term184 = False.
Proof. exact (@lem315476 False). Qed.
Lemma lem315478 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315477) (@lem315474 A f P lt2 s n h1 h2 h3)). Qed.
Lemma lem315479 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : (term461 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term461 A lt2 f s n => @lem315478 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem315067 A lt2 f s n h2)). Qed.
Lemma lem315481 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315479 A f P lt2 s n h1 h2 h3) (@lem315067 A lt2 f s n h2)). Qed.
Lemma lem315482 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : (term460 A P f s n) = False.
Proof. exact (prop_ext (fun h4 : term460 A P f s n => @lem315274 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314927 A P f s n h2)). Qed.
Lemma lem315484 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315482 A f P lt2 s n h1 h2 h3) (@lem314927 A P f s n h2)). Qed.
Lemma lem315485 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : (term461 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term461 A lt2 f s n => @lem315481 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314819 A lt2 f s n h2)). Qed.
Lemma lem315486 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315485 A f P lt2 s n h1 h2 h3) (@lem314819 A lt2 f s n h2)). Qed.
Lemma lem315487 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : (term460 A P f s n) = False.
Proof. exact (prop_ext (fun h4 : term460 A P f s n => @lem315484 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314783 A P f s n h2)). Qed.
Lemma lem315488 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315487 A f P lt2 s n h1 h2 h3) (@lem314783 A P f s n h2)). Qed.
Lemma lem315489 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : (term461 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term461 A lt2 f s n => @lem315486 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314745 A lt2 f s n h2)). Qed.
Lemma lem315490 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315489 A f P lt2 s n h1 h2 h3) (@lem314745 A lt2 f s n h2)). Qed.
Lemma lem315491 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : (term460 A P f s n) = False.
Proof. exact (prop_ext (fun h4 : term460 A P f s n => @lem315488 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314672 A P f s n h2)). Qed.
Lemma lem315492 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315491 A f P lt2 s n h1 h2 h3) (@lem314672 A P f s n h2)). Qed.
Lemma lem315493 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : (term461 A lt2 f s n) = False.
Proof. exact (prop_ext (fun h4 : term461 A lt2 f s n => @lem315490 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314745 A lt2 f s n h2)). Qed.
Lemma lem315494 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term461 A lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315493 A f P lt2 s n h1 h2 h3) (@lem314745 A lt2 f s n h2)). Qed.
Lemma lem315495 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : (term460 A P f s n) = False.
Proof. exact (prop_ext (fun h4 : term460 A P f s n => @lem315492 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314672 A P f s n h2)). Qed.
Lemma lem315496 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term460 A P f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315495 A f P lt2 s n h1 h2 h3) (@lem314672 A P f s n h2)). Qed.
Lemma lem315497 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term420 A P lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (or_elim (@lem314566 A P lt2 f s n h2) (fun h0 : term460 A P f s n => @lem315496 A f P lt2 s n h1 h0 h3) (fun h0 : term461 A lt2 f s n => @lem315494 A f P lt2 s n h1 h0 h3)). Qed.
Lemma lem315498 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term420 A P lt2 f s n) (h3 : term244 A P lt2 s n) : (term244 A P lt2 s n) = False.
Proof. exact (prop_ext (fun h4 : term244 A P lt2 s n => @lem315497 A f P lt2 s n h1 h2 h3) (fun h4 : False => @lem314536 A P lt2 s n h3)). Qed.
Lemma lem315499 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term420 A P lt2 f s n) (h3 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315498 A f P lt2 s n h1 h2 h3) (@lem314536 A P lt2 s n h3)). Qed.
Lemma lem315500 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : term244 A P lt2 s n) : False.
Proof. exact (ex_elim (@lem314349 A lt2 P h2) (fun y : A -> A => fun h0 : term115 A lt2 P y => @lem315499 A f P lt2 s n h1 h3 h4)). Qed.
Lemma lem315501 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : term244 A P lt2 s n) : (term244 A P lt2 s n) = False.
Proof. exact (prop_ext (fun h5 : term244 A P lt2 s n => @lem315500 A f P lt2 s n h1 h2 h3 h4) (fun h5 : False => @lem314443 A P lt2 s n h4)). Qed.
Lemma lem315502 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315501 A f P lt2 s n h1 h2 h3 h4) (@lem314443 A P lt2 s n h4)). Qed.
Lemma lem315503 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : term244 A P lt2 s n) : (term420 A P lt2 f s n) = False.
Proof. exact (prop_ext (fun h5 : term420 A P lt2 f s n => @lem315502 A f P lt2 s n h1 h2 h3 h4) (fun h5 : False => @lem314170 A P lt2 f s n h3)). Qed.
Lemma lem315504 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : term244 A P lt2 s n) : False.
Proof. exact (EQ_MP (@lem315503 A f P lt2 s n h1 h2 h3 h4) (@lem314170 A P lt2 f s n h3)). Qed.
Lemma lem315505 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term244 A P lt2 s n) : term419 A P lt2 f s n.
Proof. exact (fun h0 : term420 A P lt2 f s n => @lem315504 A f P lt2 s n h1 h2 h0 h3). Qed.
Lemma lem315506 {A : Type'} (f : A -> A) (P : A -> Prop) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term244 A P lt2 s n) : term363 A P lt2 f s n.
Proof. exact (EQ_MP (@lem314169 A P lt2 f s n) (@lem315505 A f P lt2 s n h1 h2 h3)). Qed.
Lemma lem315507 {A : Type'} (s : nat -> A) (n : nat) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) : term427 A P lt2 f s n.
Proof. exact (fun h0 : term244 A P lt2 s n => @lem315506 A f P lt2 s n h1 h2 h0). Qed.
Lemma lem315508 {A : Type'} (a : A) (s : nat -> A) (n : nat) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) : term429 A a P lt2 f s n.
Proof. exact (fun h0 : term212 A a f s => @lem315507 A s n f lt2 P h1 h2). Qed.
Lemma lem315509 {A : Type'} (a : A) (f : A -> A) (s : nat -> A) (n : nat) (lt2 : type1402 A) (P : A -> Prop) (h1 : term9 A lt2 P) : term431 A a P lt2 f s n.
Proof. exact (fun h0 : term204 A P lt2 f => @lem315508 A a s n f lt2 P h0 h1). Qed.
Lemma lem315510 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term433 A a P lt2 f s n.
Proof. exact (fun h0 : term9 A lt2 P => @lem315509 A a f s n lt2 P h0). Qed.
Lemma lem315511 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term434 A a P lt2 f s n.
Proof. exact (fun h0 : P a => @lem315510 A a P lt2 f s n). Qed.
Lemma lem315516 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term438 A P lt2 f s n.
Proof. exact (fun a : A => @lem315511 A a P lt2 f s n). Qed.
Lemma lem315521 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term442 A lt2 f s n.
Proof. exact (fun P : A -> Prop => @lem315516 A P lt2 f s n). Qed.
Lemma lem315526 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : term446 A f s n.
Proof. exact (fun lt2 : type1402 A => @lem315521 A lt2 f s n). Qed.
Lemma lem315531 {A : Type'} (s : nat -> A) (n : nat) : term450 A s n.
Proof. exact (fun f : A -> A => @lem315526 A f s n). Qed.
Lemma lem315536 {A : Type'} (n : nat) : term454 A n.
Proof. exact (fun s : nat -> A => @lem315531 A s n). Qed.
Lemma lem315541 {A : Type'} : term458 A.
Proof. exact (fun n : nat => @lem315536 A n). Qed.
Lemma lem315542 {A : Type'} : term457 A.
Proof. exact (EQ_MP (@lem314160 A) (@lem315541 A)). Qed.
Lemma lem315543 {A : Type'} (n : nat) : term468 A n.
Proof. exact (@lem315542 A n). Qed.
Lemma lem315544 {A : Type'} (n : nat) : (term468 A n) = (term453 A n).
Proof. exact (eq_refl (term468 A n)). Qed.
Lemma lem315545 {A : Type'} (n : nat) : term453 A n.
Proof. exact (EQ_MP (@lem315544 A n) (@lem315543 A n)). Qed.
Lemma lem315546 {A : Type'} (n : nat) (s : nat -> A) : term469 A n s.
Proof. exact (@lem315545 A n s). Qed.
Lemma lem315547 {A : Type'} (s : nat -> A) (n : nat) : (term469 A n s) = (term449 A s n).
Proof. exact (eq_refl (term469 A n s)). Qed.
Lemma lem315548 {A : Type'} (s : nat -> A) (n : nat) : term449 A s n.
Proof. exact (EQ_MP (@lem315547 A s n) (@lem315546 A n s)). Qed.
Lemma lem315549 {A : Type'} (s : nat -> A) (n : nat) (f : A -> A) : term470 A s n f.
Proof. exact (@lem315548 A s n f). Qed.
Lemma lem315550 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : (term470 A s n f) = (term445 A f s n).
Proof. exact (eq_refl (term470 A s n f)). Qed.
Lemma lem315551 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) : term445 A f s n.
Proof. exact (EQ_MP (@lem315550 A f s n) (@lem315549 A s n f)). Qed.
Lemma lem315552 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) (lt2 : type1402 A) : term471 A f s n lt2.
Proof. exact (@lem315551 A f s n lt2). Qed.
Lemma lem315553 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term471 A f s n lt2) = (term441 A lt2 f s n).
Proof. exact (eq_refl (term471 A f s n lt2)). Qed.
Lemma lem315554 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term441 A lt2 f s n.
Proof. exact (EQ_MP (@lem315553 A lt2 f s n) (@lem315552 A f s n lt2)). Qed.
Lemma lem315555 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (P : A -> Prop) : term472 A lt2 f s n P.
Proof. exact (@lem315554 A lt2 f s n P). Qed.
Lemma lem315556 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term472 A lt2 f s n P) = (term437 A P lt2 f s n).
Proof. exact (eq_refl (term472 A lt2 f s n P)). Qed.
Lemma lem315557 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term437 A P lt2 f s n.
Proof. exact (EQ_MP (@lem315556 A P lt2 f s n) (@lem315555 A lt2 f s n P)). Qed.
Lemma lem315558 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (a : A) : term473 A P lt2 f s n a.
Proof. exact (@lem315557 A P lt2 f s n a). Qed.
Lemma lem315559 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : (term473 A P lt2 f s n a) = (term421 A a P lt2 f s n).
Proof. exact (eq_refl (term473 A P lt2 f s n a)). Qed.
Lemma lem315560 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term421 A a P lt2 f s n.
Proof. exact (EQ_MP (@lem315559 A a P lt2 f s n) (@lem315558 A P lt2 f s n a)). Qed.
Lemma lem315562 {A : Type'} (a : A) (P : A -> Prop) (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) : term421 A a P lt2 f s n.
Proof. exact (@lem313828 A a P lt2 f s n (@lem315560 A a P lt2 f s n)). Qed.
Lemma lem315563 {A : Type'} (lt2 : type1402 A) (f : A -> A) (s : nat -> A) (n : nat) (P : A -> Prop) (a : A) (h1 : P a) : term432 A a P lt2 f s n.
Proof. exact (@lem315562 A a P lt2 f s n (@lem310249 A P a h1)). Qed.
Lemma lem315564 {A : Type'} (f : A -> A) (s : nat -> A) (n : nat) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term430 A a P lt2 f s n.
Proof. exact (@lem315563 A lt2 f s n P a h2 (@lem310247 A lt2 P h1)). Qed.
Lemma lem315565 {A : Type'} (s : nat -> A) (n : nat) (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term428 A a P lt2 f s n.
Proof. exact (@lem315564 A f s n lt2 P a h2 h3 (@lem311163 A P lt2 f h1)). Qed.
Lemma lem315566 {A : Type'} (n : nat) (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term426 A P lt2 f s n.
Proof. exact (@lem315565 A s n f lt2 P a h1 h2 h3 (@lem311164 A a f s h4)). Qed.
Lemma lem315567 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term244 A P lt2 s n) (h5 : term212 A a f s) : term419 A P lt2 f s n.
Proof. exact (@lem315566 A n lt2 P a f s h1 h2 h3 h5 (@lem312577 A P lt2 s n h4)). Qed.
Lemma lem315568 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : P a) (h5 : term244 A P lt2 s n) (h6 : term212 A a f s) : False.
Proof. exact (@lem315567 A P lt2 n a f s h1 h2 h4 h5 h6 (@lem313812 A P lt2 f s n h3)). Qed.
Lemma lem315569 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : P a) (h5 : term244 A P lt2 s n) (h6 : term212 A a f s) : (term420 A P lt2 f s n) = False.
Proof. exact (prop_ext (fun h7 : term420 A P lt2 f s n => @lem315568 A P lt2 n a f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem313812 A P lt2 f s n h3)). Qed.
Lemma lem315570 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : term420 A P lt2 f s n) (h4 : P a) (h5 : term244 A P lt2 s n) (h6 : term212 A a f s) : False.
Proof. exact (EQ_MP (@lem315569 A P lt2 n a f s h1 h2 h3 h4 h5 h6) (@lem313812 A P lt2 f s n h3)). Qed.
Lemma lem315571 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term244 A P lt2 s n) (h5 : term212 A a f s) : term419 A P lt2 f s n.
Proof. exact (fun h0 : term420 A P lt2 f s n => @lem315570 A P lt2 n a f s h1 h2 h0 h3 h4 h5). Qed.
Lemma lem315572 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term244 A P lt2 s n) (h5 : term212 A a f s) : term363 A P lt2 f s n.
Proof. exact (EQ_MP (@lem313811 A P lt2 f s n) (@lem315571 A P lt2 n a f s h1 h2 h3 h4 h5)). Qed.
Lemma lem315573 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (n : nat) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term244 A P lt2 s n) (h5 : term212 A a f s) : term329 A P lt2 s n.
Proof. exact (EQ_MP (@lem312666 A P lt2 n a f s h5) (@lem315572 A P lt2 n a f s h1 h2 h3 h4 h5)). Qed.
Lemma lem315574 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term322 A P lt2 s.
Proof. exact (EQ_MP (@lem312621 A lt2 P a f s h3 h4) (@lem313807 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315575 {A : Type'} (n : nat) (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term331 A P lt2 s n.
Proof. exact (fun h0 : term244 A P lt2 s n => @lem315573 A P lt2 n a f s h1 h2 h3 h0 h4). Qed.
Lemma lem315580 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term335 A P lt2 s.
Proof. exact (fun n : nat => @lem315575 A n lt2 P a f s h1 h2 h3 h4). Qed.
Lemma lem315581 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term337 A P lt2 s.
Proof. exact (conj (@lem315574 A lt2 P a f s h1 h2 h3 h4) (@lem315580 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315582 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term224 A P lt2 s.
Proof. exact (@lem312576 A P lt2 s (@lem315581 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315583 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : (term224 A P lt2 s) = (term223 A lt2 f s).
Proof. exact (prop_ext (fun h5 : term224 A P lt2 s => @lem312553 A lt2 P a f s h1 h5 h2 h3 h4) (fun h5 : term223 A lt2 f s => @lem315582 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315584 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term223 A lt2 f s.
Proof. exact (EQ_MP (@lem315583 A lt2 P a f s h1 h2 h3 h4) (@lem315582 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315585 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term3 A lt2 s.
Proof. exact (EQ_MP (@lem311196 A lt2 a f s h4) (@lem315584 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315586 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (f : A -> A) (s : nat -> A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) (h4 : term212 A a f s) : term2 A lt2.
Proof. exact (ex_intro (term474 A lt2) s (@lem315585 A lt2 P a f s h1 h2 h3 h4)). Qed.
Lemma lem315587 {A : Type'} (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term2 A lt2.
Proof. exact (ex_elim (@lem309993 A a f) (fun s : nat -> A => fun h0 : term475 A a f s => @lem315586 A lt2 P a f s h1 h2 h3 h0)). Qed.
Lemma lem315588 {A : Type'} (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : (term204 A P lt2 f) = (term2 A lt2).
Proof. exact (prop_ext (fun h4 : term204 A P lt2 f => @lem315587 A f lt2 P a h1 h2 h3) (fun h4 : term2 A lt2 => @lem311163 A P lt2 f h1)). Qed.
Lemma lem315589 {A : Type'} (f : A -> A) (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term204 A P lt2 f) (h2 : term9 A lt2 P) (h3 : P a) : term2 A lt2.
Proof. exact (EQ_MP (@lem315588 A f lt2 P a h1 h2 h3) (@lem311163 A P lt2 f h1)). Qed.
Lemma lem315590 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term207 A P lt2) (h2 : term9 A lt2 P) (h3 : P a) : term2 A lt2.
Proof. exact (ex_elim (@lem311162 A P lt2 h1) (fun f : A -> A => fun h0 : term206 A P lt2 f => @lem315589 A f lt2 P a h0 h2 h3)). Qed.
Lemma lem315591 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term211 A P lt2.
Proof. exact (fun h0 : term207 A P lt2 => @lem315590 A lt2 P a h0 h1 h2). Qed.
Lemma lem315592 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term210 A P lt2.
Proof. exact (EQ_MP (@lem311161 A P lt2) (@lem315591 A lt2 P a h1 h2)). Qed.
Lemma lem315593 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term10 A P lt2) (h2 : term9 A lt2 P) (h3 : P a) : term2 A lt2.
Proof. exact (@lem315592 A lt2 P a h2 h3 (@lem310250 A P lt2 h1)). Qed.
Lemma lem315594 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : (term10 A P lt2) = (term2 A lt2).
Proof. exact (prop_ext (fun h3 : term10 A P lt2 => @lem315593 A lt2 P a h3 h1 h2) (fun h3 : term2 A lt2 => @lem311102 A lt2 P a h1 h2)). Qed.
Lemma lem315595 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term2 A lt2.
Proof. exact (EQ_MP (@lem315594 A lt2 P a h1 h2) (@lem311102 A lt2 P a h1 h2)). Qed.
Lemma lem315596 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term6 A lt2 P) : term9 A lt2 P.
Proof. exact (proj2 (@lem310246 A lt2 P h1)). Qed.
Lemma lem315597 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term6 A lt2 P) : term7 A P.
Proof. exact (proj1 (@lem310246 A lt2 P h1)). Qed.
Lemma lem315598 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : (term9 A lt2 P) = (term2 A lt2).
Proof. exact (prop_ext (fun h3 : term9 A lt2 P => @lem315595 A lt2 P a h1 h2) (fun h3 : term2 A lt2 => @lem310247 A lt2 P h1)). Qed.
Lemma lem315599 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (a : A) (h1 : term9 A lt2 P) (h2 : P a) : term2 A lt2.
Proof. exact (EQ_MP (@lem315598 A lt2 P a h1 h2) (@lem310247 A lt2 P h1)). Qed.
Lemma lem315600 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term7 A P) (h2 : term9 A lt2 P) : term2 A lt2.
Proof. exact (ex_elim (@lem310248 A P h1) (fun a : A => fun h0 : term397 A P a => @lem315599 A lt2 P a h2 h0)). Qed.
Lemma lem315601 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term7 A P) (h2 : term6 A lt2 P) : (term9 A lt2 P) = (term2 A lt2).
Proof. exact (prop_ext (fun h3 : term9 A lt2 P => @lem315600 A lt2 P h1 h3) (fun h3 : term2 A lt2 => @lem315596 A lt2 P h2)). Qed.
Lemma lem315602 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term7 A P) (h2 : term6 A lt2 P) : term2 A lt2.
Proof. exact (EQ_MP (@lem315601 A lt2 P h1 h2) (@lem315596 A lt2 P h2)). Qed.
Lemma lem315603 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term6 A lt2 P) : (term7 A P) = (term2 A lt2).
Proof. exact (prop_ext (fun h2 : term7 A P => @lem315602 A lt2 P h2 h1) (fun h2 : term2 A lt2 => @lem315597 A lt2 P h1)). Qed.
Lemma lem315604 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term6 A lt2 P) : term2 A lt2.
Proof. exact (EQ_MP (@lem315603 A lt2 P h1) (@lem315597 A lt2 P h1)). Qed.
Lemma lem315605 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term476 A P lt2.
Proof. exact (fun h0 : term6 A lt2 P => @lem315604 A lt2 P h0). Qed.
Lemma lem315606 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term1 A lt2 P) : term2 A lt2.
Proof. exact (@lem315605 A P lt2 (@lem310245 A lt2 P h1)). Qed.
Lemma lem315614 {A B : Type'} (f : A -> B) (y : A) : (term477 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem315615 {A : Type'} (f : A -> Prop) (y : A) : (term398 A f y) = (f y).
Proof. exact (@lem315614 A Prop f y). Qed.
Lemma lem315616 {A : Type'} (s : nat -> A) (x : A) : (term478 A s x) = (term479 A s x).
Proof. exact (@lem315615 A (term480 A s) x). Qed.
Lemma lem315617 {A : Type'} (y : A) (s : nat -> A) : (term479 A s y) = (term481 A y s).
Proof. exact (eq_refl (term479 A s y)). Qed.
Lemma lem315618 {A : Type'} (s : nat -> A) : (term482 A s) = (term480 A s).
Proof. exact (fun_ext (fun y : A => @lem315617 A y s)). Qed.
Lemma lem315619 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem315620 {A : Type'} (s : nat -> A) (x : A) : (term478 A s x) = (term479 A s x).
Proof. exact (MK_COMB (@lem315618 A s) (@lem315619 A x)). Qed.
Lemma lem315621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315622 {A : Type'} (s : nat -> A) (x : A) : (term483 A s x) = (term484 A s x).
Proof. exact (MK_COMB (@lem315621) (@lem315620 A s x)). Qed.
Lemma lem315623 {A : Type'} (x : A) (s : nat -> A) : (term479 A s x) = (term481 A x s).
Proof. exact (eq_refl (term479 A s x)). Qed.
Lemma lem315624 {A : Type'} (x : A) (s : nat -> A) : ((term478 A s x) = (term479 A s x)) = ((term479 A s x) = (term481 A x s)).
Proof. exact (MK_COMB (@lem315622 A s x) (@lem315623 A x s)). Qed.
Lemma lem315625 {A : Type'} (x : A) (s : nat -> A) : (term479 A s x) = (term481 A x s).
Proof. exact (EQ_MP (@lem315624 A x s) (@lem315616 A s x)). Qed.
Lemma lem315632 {A : Type'} (s : nat -> A) : (term482 A s) = (term480 A s).
Proof. exact (fun_ext (fun x : A => @lem315625 A x s)). Qed.
Lemma lem315633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem315634 {A : Type'} (s : nat -> A) : (term485 A s) = (term486 A s).
Proof. exact (MK_COMB (@lem315633 A) (@lem315632 A s)). Qed.
Lemma lem315639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315640 {A : Type'} (s : nat -> A) : (term487 A s) = (term488 A s).
Proof. exact (MK_COMB (@lem315639) (@lem315634 A s)). Qed.
Lemma lem315648 {A B : Type'} (f : A -> B) (y : A) : (term477 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem315649 {A : Type'} (f : A -> Prop) (y : A) : (term398 A f y) = (f y).
Proof. exact (@lem315648 A Prop f y). Qed.
Lemma lem315650 {A : Type'} (s : nat -> A) (x : A) : (term478 A s x) = (term479 A s x).
Proof. exact (@lem315649 A (term480 A s) x). Qed.
Lemma lem315651 {A : Type'} (y : A) (s : nat -> A) : (term479 A s y) = (term481 A y s).
Proof. exact (eq_refl (term479 A s y)). Qed.
Lemma lem315652 {A : Type'} (s : nat -> A) : (term482 A s) = (term480 A s).
Proof. exact (fun_ext (fun y : A => @lem315651 A y s)). Qed.
Lemma lem315653 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem315654 {A : Type'} (s : nat -> A) (x : A) : (term478 A s x) = (term479 A s x).
Proof. exact (MK_COMB (@lem315652 A s) (@lem315653 A x)). Qed.
Lemma lem315655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315656 {A : Type'} (s : nat -> A) (x : A) : (term483 A s x) = (term484 A s x).
Proof. exact (MK_COMB (@lem315655) (@lem315654 A s x)). Qed.
Lemma lem315657 {A : Type'} (x : A) (s : nat -> A) : (term479 A s x) = (term481 A x s).
Proof. exact (eq_refl (term479 A s x)). Qed.
Lemma lem315658 {A : Type'} (x : A) (s : nat -> A) : ((term478 A s x) = (term479 A s x)) = ((term479 A s x) = (term481 A x s)).
Proof. exact (MK_COMB (@lem315656 A s x) (@lem315657 A x s)). Qed.
Lemma lem315659 {A : Type'} (x : A) (s : nat -> A) : (term479 A s x) = (term481 A x s).
Proof. exact (EQ_MP (@lem315658 A x s) (@lem315650 A s x)). Qed.
Lemma lem315666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem315667 {A : Type'} (x : A) (s : nat -> A) : (term489 A s x) = (term490 A x s).
Proof. exact (MK_COMB (@lem315666) (@lem315659 A x s)). Qed.
Lemma lem315675 {A B : Type'} (f : A -> B) (y : A) : (term477 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem315676 {A : Type'} (f : A -> Prop) (y : A) : (term398 A f y) = (f y).
Proof. exact (@lem315675 A Prop f y). Qed.
Lemma lem315677 {A : Type'} (s : nat -> A) (y : A) : (term478 A s y) = (term479 A s y).
Proof. exact (@lem315676 A (term480 A s) y). Qed.
Lemma lem315678 {A : Type'} (y : A) (s : nat -> A) : (term479 A s y) = (term481 A y s).
Proof. exact (eq_refl (term479 A s y)). Qed.
Lemma lem315679 {A : Type'} (s : nat -> A) : (term482 A s) = (term480 A s).
Proof. exact (fun_ext (fun y : A => @lem315678 A y s)). Qed.
Lemma lem315680 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem315681 {A : Type'} (s : nat -> A) (y : A) : (term478 A s y) = (term479 A s y).
Proof. exact (MK_COMB (@lem315679 A s) (@lem315680 A y)). Qed.
Lemma lem315682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem315683 {A : Type'} (s : nat -> A) (y : A) : (term483 A s y) = (term484 A s y).
Proof. exact (MK_COMB (@lem315682) (@lem315681 A s y)). Qed.
Lemma lem315684 {A : Type'} (y : A) (s : nat -> A) : (term479 A s y) = (term481 A y s).
Proof. exact (eq_refl (term479 A s y)). Qed.
Lemma lem315685 {A : Type'} (y : A) (s : nat -> A) : ((term478 A s y) = (term479 A s y)) = ((term479 A s y) = (term481 A y s)).
Proof. exact (MK_COMB (@lem315683 A s y) (@lem315684 A y s)). Qed.
Lemma lem315686 {A : Type'} (y : A) (s : nat -> A) : (term479 A s y) = (term481 A y s).
Proof. exact (EQ_MP (@lem315685 A y s) (@lem315677 A s y)). Qed.
Lemma lem315693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315694 {A : Type'} (y : A) (s : nat -> A) : (term491 A s y) = (term492 A y s).
Proof. exact (MK_COMB (@lem315693) (@lem315686 A y s)). Qed.
Lemma lem315695 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term493 A lt2 y x) = (term493 A lt2 y x).
Proof. exact (eq_refl (term493 A lt2 y x)). Qed.
Lemma lem315696 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term494 A lt2 x s y) = (term495 A lt2 x y s).
Proof. exact (MK_COMB (@lem315695 A lt2 y x) (@lem315694 A y s)). Qed.
Lemma lem315699 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term496 A lt2 x s) = (term497 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem315696 A lt2 x y s)). Qed.
Lemma lem315700 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem315701 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term498 A lt2 x s) = (term499 A lt2 x s).
Proof. exact (MK_COMB (@lem315700 A) (@lem315699 A lt2 x s)). Qed.
Lemma lem315706 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term500 A lt2 x s) = (term501 A lt2 x s).
Proof. exact (MK_COMB (@lem315667 A x s) (@lem315701 A lt2 x s)). Qed.
Lemma lem315709 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term502 A lt2 s) = (term503 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem315706 A lt2 x s)). Qed.
Lemma lem315710 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem315711 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term504 A lt2 s) = (term505 A lt2 s).
Proof. exact (MK_COMB (@lem315710 A) (@lem315709 A lt2 s)). Qed.
Lemma lem315716 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term506 A lt2 s) = (term507 A lt2 s).
Proof. exact (MK_COMB (@lem315640 A s) (@lem315711 A lt2 s)). Qed.
Lemma lem315719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315720 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term508 A lt2 s) = (term509 A lt2 s).
Proof. exact (MK_COMB (@lem315719) (@lem315716 A lt2 s)). Qed.
Lemma lem315721 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term509 A lt2 s) = (term508 A lt2 s).
Proof. exact (SYM (@lem315720 A lt2 s)). Qed.
Lemma lem315722 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term507 A lt2 s) : term507 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315725 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term510 A lt2 s) : term510 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315726 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term511 A lt2 s.
Proof. exact (fun h0 : term510 A lt2 s => @lem315725 A lt2 s h0). Qed.
Lemma lem315727 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term511 A lt2 s) : term511 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315728 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term510 A lt2 s) : term510 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315729 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term510 A lt2 s) (h2 : term511 A lt2 s) : term510 A lt2 s.
Proof. exact (@lem315727 A lt2 s h2 (@lem315728 A lt2 s h1)). Qed.
Lemma lem315730 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term510 A lt2 s) : term512 A lt2 s.
Proof. exact (fun h0 : term511 A lt2 s => @lem315729 A lt2 s h1 h0). Qed.
Lemma lem315731 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term511 A lt2 s) : term511 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315732 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term510 A lt2 s) (h2 : term511 A lt2 s) : term510 A lt2 s.
Proof. exact (@lem315730 A lt2 s h1 (@lem315731 A lt2 s h2)). Qed.
Lemma lem315733 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term511 A lt2 s) : term511 A lt2 s.
Proof. exact (fun h0 : term510 A lt2 s => @lem315732 A lt2 s h0 h1). Qed.
Lemma lem315734 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term513 A lt2 s.
Proof. exact (fun h0 : term511 A lt2 s => @lem315733 A lt2 s h0). Qed.
Lemma lem315737 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term511 A lt2 s.
Proof. exact (@lem315734 A lt2 s (@lem315726 A lt2 s)). Qed.
Lemma lem315738 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term511 A lt2 s.
Proof. exact (@lem315737 A lt2 s). Qed.
Lemma lem315754 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem315755 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term514 A lt2 s) = (term509 A lt2 s).
Proof. exact (@lem315754 (term507 A lt2 s)). Qed.
Lemma lem315830 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term515 A lt2 s) = (term515 A lt2 s).
Proof. exact (eq_refl (term515 A lt2 s)). Qed.
Lemma lem315831 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term510 A lt2 s) = (term516 A lt2 s).
Proof. exact (MK_COMB (@lem315830 A lt2 s) (@lem315755 A lt2 s)). Qed.
Lemma lem315834 {A : Type'} (s : nat -> A) : (term517 A s) = (term518 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem315831 A lt2 s)). Qed.
Lemma lem315835 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem315836 {A : Type'} (s : nat -> A) : (term519 A s) = (term520 A s).
Proof. exact (MK_COMB (@lem315835 A) (@lem315834 A s)). Qed.
Lemma lem315841 {A : Type'} : (term521 A) = (term522 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem315836 A s)). Qed.
Lemma lem315842 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem315851 {A : Type'} : (term523 A) = (term524 A).
Proof. exact (MK_COMB (@lem315842 A) (@lem315841 A)). Qed.
Lemma lem315852 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (y = (s n)) = (y = (s n)).
Proof. exact (eq_refl (y = (s n))). Qed.
Lemma lem315853 {A : Type'} (y : A) (s : nat -> A) : (term525 A y s) = (term525 A y s).
Proof. exact (fun_ext (fun n : nat => @lem315852 A y s n)). Qed.
Lemma lem315854 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem315855 {A : Type'} (y : A) (s : nat -> A) : (term481 A y s) = (term481 A y s).
Proof. exact (MK_COMB (@lem315854) (@lem315853 A y s)). Qed.
Lemma lem315856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315857 {A : Type'} (y : A) (s : nat -> A) : (term492 A y s) = (term492 A y s).
Proof. exact (MK_COMB (@lem315856) (@lem315855 A y s)). Qed.
Lemma lem315860 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term493 A lt2 y x) = (term493 A lt2 y x).
Proof. exact (eq_refl (term493 A lt2 y x)). Qed.
Lemma lem315861 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term495 A lt2 x y s) = (term495 A lt2 x y s).
Proof. exact (MK_COMB (@lem315860 A lt2 y x) (@lem315857 A y s)). Qed.
Lemma lem315862 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term497 A lt2 x s) = (term497 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem315861 A lt2 x y s)). Qed.
Lemma lem315863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem315864 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term499 A lt2 x s) = (term499 A lt2 x s).
Proof. exact (MK_COMB (@lem315863 A) (@lem315862 A lt2 x s)). Qed.
Lemma lem315865 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (x = (s n)) = (x = (s n)).
Proof. exact (eq_refl (x = (s n))). Qed.
Lemma lem315866 {A : Type'} (x : A) (s : nat -> A) : (term525 A x s) = (term525 A x s).
Proof. exact (fun_ext (fun n : nat => @lem315865 A x s n)). Qed.
Lemma lem315867 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem315868 {A : Type'} (x : A) (s : nat -> A) : (term481 A x s) = (term481 A x s).
Proof. exact (MK_COMB (@lem315867) (@lem315866 A x s)). Qed.
Lemma lem315869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem315870 {A : Type'} (x : A) (s : nat -> A) : (term490 A x s) = (term490 A x s).
Proof. exact (MK_COMB (@lem315869) (@lem315868 A x s)). Qed.
Lemma lem315871 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term501 A lt2 x s) = (term501 A lt2 x s).
Proof. exact (MK_COMB (@lem315870 A x s) (@lem315864 A lt2 x s)). Qed.
Lemma lem315872 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term503 A lt2 s) = (term503 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem315871 A lt2 x s)). Qed.
Lemma lem315873 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem315874 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term505 A lt2 s) = (term505 A lt2 s).
Proof. exact (MK_COMB (@lem315873 A) (@lem315872 A lt2 s)). Qed.
Lemma lem315875 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (x = (s n)) = (x = (s n)).
Proof. exact (eq_refl (x = (s n))). Qed.
Lemma lem315876 {A : Type'} (x : A) (s : nat -> A) : (term525 A x s) = (term525 A x s).
Proof. exact (fun_ext (fun n : nat => @lem315875 A x s n)). Qed.
Lemma lem315877 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem315878 {A : Type'} (x : A) (s : nat -> A) : (term481 A x s) = (term481 A x s).
Proof. exact (MK_COMB (@lem315877) (@lem315876 A x s)). Qed.
Lemma lem315879 {A : Type'} (s : nat -> A) : (term480 A s) = (term480 A s).
Proof. exact (fun_ext (fun x : A => @lem315878 A x s)). Qed.
Lemma lem315880 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem315881 {A : Type'} (s : nat -> A) : (term486 A s) = (term486 A s).
Proof. exact (MK_COMB (@lem315880 A) (@lem315879 A s)). Qed.
Lemma lem315882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315883 {A : Type'} (s : nat -> A) : (term488 A s) = (term488 A s).
Proof. exact (MK_COMB (@lem315882) (@lem315881 A s)). Qed.
Lemma lem315884 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term507 A lt2 s) = (term507 A lt2 s).
Proof. exact (MK_COMB (@lem315883 A s) (@lem315874 A lt2 s)). Qed.
Lemma lem315885 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315886 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term509 A lt2 s) = (term509 A lt2 s).
Proof. exact (MK_COMB (@lem315885) (@lem315884 A lt2 s)). Qed.
Lemma lem315887 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem315888 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem315887 A lt2 s n)). Qed.
Lemma lem315889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem315890 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem315889) (@lem315888 A lt2 s)). Qed.
Lemma lem315891 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem315892 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term515 A lt2 s) = (term515 A lt2 s).
Proof. exact (MK_COMB (@lem315891) (@lem315890 A lt2 s)). Qed.
Lemma lem315893 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term516 A lt2 s) = (term516 A lt2 s).
Proof. exact (MK_COMB (@lem315892 A lt2 s) (@lem315886 A lt2 s)). Qed.
Lemma lem315894 {A : Type'} (s : nat -> A) : (term518 A s) = (term518 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem315893 A lt2 s)). Qed.
Lemma lem315895 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem315896 {A : Type'} (s : nat -> A) : (term520 A s) = (term520 A s).
Proof. exact (MK_COMB (@lem315895 A) (@lem315894 A s)). Qed.
Lemma lem315897 {A : Type'} : (term522 A) = (term522 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem315896 A s)). Qed.
Lemma lem315898 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem315899 {A : Type'} : (term524 A) = (term524 A).
Proof. exact (MK_COMB (@lem315898 A) (@lem315897 A)). Qed.
Lemma lem315964 {A : Type'} : (term523 A) = (term524 A).
Proof. exact (TRANS (@lem315851 A) (@lem315899 A)). Qed.
Lemma lem315965 {A : Type'} : (term524 A) = (term523 A).
Proof. exact (SYM (@lem315964 A)). Qed.
Lemma lem315966 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term3 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315967 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term507 A lt2 s) : term507 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem315968 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem315969 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem315968 A lt2 s n)). Qed.
Lemma lem315970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem315979 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem315970) (@lem315969 A lt2 s)). Qed.
Lemma lem315980 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term3 A lt2 s.
Proof. exact (EQ_MP (@lem315979 A lt2 s) (@lem315966 A lt2 s h1)). Qed.
Lemma lem315982 (P : nat -> Prop) : (term526 P) = (term527 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem315983 {A : Type'} (x : A) (s : nat -> A) : (term492 A x s) = (term528 A x s).
Proof. exact (@lem315982 (term525 A x s)). Qed.
Lemma lem315984 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term529 A x s n) = (x = (s n)).
Proof. exact (eq_refl (term529 A x s n)). Qed.
Lemma lem315985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315987 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term530 A x s n) = (term531 A x s n).
Proof. exact (MK_COMB (@lem315985) (@lem315984 A x s n)). Qed.
Lemma lem315988 {A : Type'} (x : A) (s : nat -> A) : (term532 A x s) = (term533 A x s).
Proof. exact (fun_ext (fun n : nat => @lem315987 A x s n)). Qed.
Lemma lem315989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem315990 {A : Type'} (x : A) (s : nat -> A) : (term528 A x s) = (term534 A x s).
Proof. exact (MK_COMB (@lem315989) (@lem315988 A x s)). Qed.
Lemma lem315991 {A : Type'} (x : A) (s : nat -> A) : (term492 A x s) = (term534 A x s).
Proof. exact (TRANS (@lem315983 A x s) (@lem315990 A x s)). Qed.
Lemma lem315992 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem315993 {A : Type'} (s : nat -> A) : (term535 A s) = (term536 A s).
Proof. exact (@lem315992 A (term480 A s)). Qed.
Lemma lem315994 {A : Type'} (x : A) (s : nat -> A) : (term479 A s x) = (term481 A x s).
Proof. exact (eq_refl (term479 A s x)). Qed.
Lemma lem315995 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem315996 {A : Type'} (x : A) (s : nat -> A) : (term491 A s x) = (term492 A x s).
Proof. exact (MK_COMB (@lem315995) (@lem315994 A x s)). Qed.
Lemma lem315997 {A : Type'} (x : A) (s : nat -> A) : (term491 A s x) = (term534 A x s).
Proof. exact (TRANS (@lem315996 A x s) (@lem315991 A x s)). Qed.
Lemma lem315998 {A : Type'} (s : nat -> A) : (term537 A s) = (term538 A s).
Proof. exact (fun_ext (fun x : A => @lem315997 A x s)). Qed.
Lemma lem315999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316000 {A : Type'} (s : nat -> A) : (term536 A s) = (term539 A s).
Proof. exact (MK_COMB (@lem315999 A) (@lem315998 A s)). Qed.
Lemma lem316001 {A : Type'} (s : nat -> A) : (term535 A s) = (term539 A s).
Proof. exact (TRANS (@lem315993 A s) (@lem316000 A s)). Qed.
Lemma lem316002 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (x = (s n)) = (x = (s n)).
Proof. exact (eq_refl (x = (s n))). Qed.
Lemma lem316003 {A : Type'} (x : A) (s : nat -> A) : (term525 A x s) = (term525 A x s).
Proof. exact (fun_ext (fun n : nat => @lem316002 A x s n)). Qed.
Lemma lem316004 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem316005 {A : Type'} (x : A) (s : nat -> A) : (term481 A x s) = (term481 A x s).
Proof. exact (MK_COMB (@lem316004) (@lem316003 A x s)). Qed.
Lemma lem316008 (P : nat -> Prop) : (term526 P) = (term527 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem316009 {A : Type'} (y : A) (s : nat -> A) : (term492 A y s) = (term528 A y s).
Proof. exact (@lem316008 (term525 A y s)). Qed.
Lemma lem316010 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (term529 A y s n) = (y = (s n)).
Proof. exact (eq_refl (term529 A y s n)). Qed.
Lemma lem316011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem316013 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (term530 A y s n) = (term531 A y s n).
Proof. exact (MK_COMB (@lem316011) (@lem316010 A y s n)). Qed.
Lemma lem316014 {A : Type'} (y : A) (s : nat -> A) : (term532 A y s) = (term533 A y s).
Proof. exact (fun_ext (fun n : nat => @lem316013 A y s n)). Qed.
Lemma lem316015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316016 {A : Type'} (y : A) (s : nat -> A) : (term528 A y s) = (term534 A y s).
Proof. exact (MK_COMB (@lem316015) (@lem316014 A y s)). Qed.
Lemma lem316017 {A : Type'} (y : A) (s : nat -> A) : (term492 A y s) = (term534 A y s).
Proof. exact (TRANS (@lem316009 A y s) (@lem316016 A y s)). Qed.
Lemma lem316019 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term540 A lt2 y x) = (term540 A lt2 y x).
Proof. exact (eq_refl (term540 A lt2 y x)). Qed.
Lemma lem316020 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term541 A lt2 x y s) = (term542 A lt2 x y s).
Proof. exact (MK_COMB (@lem316019 A lt2 y x) (@lem316017 A y s)). Qed.
Lemma lem316021 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term495 A lt2 x y s) = (term541 A lt2 x y s).
Proof. exact (@lem17265 (lt2 y x) (term492 A y s)). Qed.
Lemma lem316022 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term495 A lt2 x y s) = (term542 A lt2 x y s).
Proof. exact (TRANS (@lem316021 A lt2 x y s) (@lem316020 A lt2 x y s)). Qed.
Lemma lem316023 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term497 A lt2 x s) = (term543 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem316022 A lt2 x y s)). Qed.
Lemma lem316024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316025 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term499 A lt2 x s) = (term544 A lt2 x s).
Proof. exact (MK_COMB (@lem316024 A) (@lem316023 A lt2 x s)). Qed.
Lemma lem316026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem316027 {A : Type'} (x : A) (s : nat -> A) : (term490 A x s) = (term490 A x s).
Proof. exact (MK_COMB (@lem316026) (@lem316005 A x s)). Qed.
Lemma lem316028 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term501 A lt2 x s) = (term545 A lt2 x s).
Proof. exact (MK_COMB (@lem316027 A x s) (@lem316025 A lt2 x s)). Qed.
Lemma lem316029 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term503 A lt2 s) = (term546 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem316028 A lt2 x s)). Qed.
Lemma lem316030 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem316031 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term505 A lt2 s) = (term547 A lt2 s).
Proof. exact (MK_COMB (@lem316030 A) (@lem316029 A lt2 s)). Qed.
Lemma lem316032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem316033 {A : Type'} (s : nat -> A) : (term548 A s) = (term549 A s).
Proof. exact (MK_COMB (@lem316032) (@lem316001 A s)). Qed.
Lemma lem316034 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term550 A lt2 s) = (term551 A lt2 s).
Proof. exact (MK_COMB (@lem316033 A s) (@lem316031 A lt2 s)). Qed.
Lemma lem316035 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term507 A lt2 s) = (term550 A lt2 s).
Proof. exact (@lem17265 (term486 A s) (term505 A lt2 s)). Qed.
Lemma lem316036 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term507 A lt2 s) = (term551 A lt2 s).
Proof. exact (TRANS (@lem316035 A lt2 s) (@lem316034 A lt2 s)). Qed.
Lemma lem316151 {A : Type'} (P : A -> Prop) (Q : Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem316152 (P : nat -> Prop) (Q : Prop) : (term554 P Q) = (term555 P Q).
Proof. exact (@lem316151 nat P Q). Qed.
Lemma lem316153 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term556 A lt2 x s) = (term557 A lt2 x s).
Proof. exact (@lem316152 (term525 A x s) (term544 A lt2 x s)). Qed.
Lemma lem316154 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term529 A x s n) = (x = (s n)).
Proof. exact (eq_refl (term529 A x s n)). Qed.
Lemma lem316155 {A : Type'} (x : A) (s : nat -> A) : (term558 A x s) = (term525 A x s).
Proof. exact (fun_ext (fun n : nat => @lem316154 A x s n)). Qed.
Lemma lem316156 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem316157 {A : Type'} (x : A) (s : nat -> A) : (term559 A x s) = (term481 A x s).
Proof. exact (MK_COMB (@lem316156) (@lem316155 A x s)). Qed.
Lemma lem316158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem316159 {A : Type'} (x : A) (s : nat -> A) : (term560 A x s) = (term490 A x s).
Proof. exact (MK_COMB (@lem316158) (@lem316157 A x s)). Qed.
Lemma lem316160 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term544 A lt2 x s) = (term544 A lt2 x s).
Proof. exact (eq_refl (term544 A lt2 x s)). Qed.
Lemma lem316161 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term556 A lt2 x s) = (term545 A lt2 x s).
Proof. exact (MK_COMB (@lem316159 A x s) (@lem316160 A lt2 x s)). Qed.
Lemma lem316162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316163 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term561 A lt2 x s) = (term562 A lt2 x s).
Proof. exact (MK_COMB (@lem316162) (@lem316161 A lt2 x s)). Qed.
Lemma lem316164 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term529 A x s n) = (x = (s n)).
Proof. exact (eq_refl (term529 A x s n)). Qed.
Lemma lem316165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem316166 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term563 A x s n) = (term564 A x s n).
Proof. exact (MK_COMB (@lem316165) (@lem316164 A x s n)). Qed.
Lemma lem316167 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term544 A lt2 x s) = (term544 A lt2 x s).
Proof. exact (eq_refl (term544 A lt2 x s)). Qed.
Lemma lem316168 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term565 A n lt2 x s) = (term566 A n lt2 x s).
Proof. exact (MK_COMB (@lem316166 A x s n) (@lem316167 A lt2 x s)). Qed.
Lemma lem316169 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term567 A lt2 x s) = (term568 A lt2 x s).
Proof. exact (fun_ext (fun n : nat => @lem316168 A n lt2 x s)). Qed.
Lemma lem316170 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem316171 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term557 A lt2 x s) = (term569 A lt2 x s).
Proof. exact (MK_COMB (@lem316170) (@lem316169 A lt2 x s)). Qed.
Lemma lem316172 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : ((term556 A lt2 x s) = (term557 A lt2 x s)) = ((term545 A lt2 x s) = (term569 A lt2 x s)).
Proof. exact (MK_COMB (@lem316163 A lt2 x s) (@lem316171 A lt2 x s)). Qed.
Lemma lem316173 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term545 A lt2 x s) = (term569 A lt2 x s).
Proof. exact (EQ_MP (@lem316172 A lt2 x s) (@lem316153 A lt2 x s)). Qed.
Lemma lem316174 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term546 A lt2 s) = (term570 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem316173 A lt2 x s)). Qed.
Lemma lem316175 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem316176 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term547 A lt2 s) = (term571 A lt2 s).
Proof. exact (MK_COMB (@lem316175 A) (@lem316174 A lt2 s)). Qed.
Lemma lem316177 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (eq_refl (term549 A s)). Qed.
Lemma lem316178 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term551 A lt2 s) = (term572 A lt2 s).
Proof. exact (MK_COMB (@lem316177 A s) (@lem316176 A lt2 s)). Qed.
Lemma lem316180 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem316181 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem316180 A P Q). Qed.
Lemma lem316182 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term573 A lt2 s) = (term574 A lt2 s).
Proof. exact (@lem316181 A (term539 A s) (term570 A lt2 s)). Qed.
Lemma lem316183 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term575 A lt2 s x) = (term569 A lt2 x s).
Proof. exact (eq_refl (term575 A lt2 s x)). Qed.
Lemma lem316184 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term576 A lt2 s) = (term570 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem316183 A lt2 x s)). Qed.
Lemma lem316185 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem316186 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term577 A lt2 s) = (term571 A lt2 s).
Proof. exact (MK_COMB (@lem316185 A) (@lem316184 A lt2 s)). Qed.
Lemma lem316187 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (eq_refl (term549 A s)). Qed.
Lemma lem316188 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term573 A lt2 s) = (term572 A lt2 s).
Proof. exact (MK_COMB (@lem316187 A s) (@lem316186 A lt2 s)). Qed.
Lemma lem316189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316190 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term578 A lt2 s) = (term579 A lt2 s).
Proof. exact (MK_COMB (@lem316189) (@lem316188 A lt2 s)). Qed.
Lemma lem316191 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term575 A lt2 s x) = (term569 A lt2 x s).
Proof. exact (eq_refl (term575 A lt2 s x)). Qed.
Lemma lem316192 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (eq_refl (term549 A s)). Qed.
Lemma lem316193 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term580 A lt2 s x) = (term581 A lt2 x s).
Proof. exact (MK_COMB (@lem316192 A s) (@lem316191 A lt2 x s)). Qed.
Lemma lem316194 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term582 A lt2 s) = (term583 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem316193 A lt2 x s)). Qed.
Lemma lem316195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem316196 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term574 A lt2 s) = (term584 A lt2 s).
Proof. exact (MK_COMB (@lem316195 A) (@lem316194 A lt2 s)). Qed.
Lemma lem316197 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term573 A lt2 s) = (term574 A lt2 s)) = ((term572 A lt2 s) = (term584 A lt2 s)).
Proof. exact (MK_COMB (@lem316190 A lt2 s) (@lem316196 A lt2 s)). Qed.
Lemma lem316198 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term572 A lt2 s) = (term584 A lt2 s).
Proof. exact (EQ_MP (@lem316197 A lt2 s) (@lem316182 A lt2 s)). Qed.
Lemma lem316200 {A : Type'} (P : Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem316201 (P : Prop) (Q : nat -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem316200 nat P Q). Qed.
Lemma lem316202 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term587 A lt2 x s) = (term588 A lt2 x s).
Proof. exact (@lem316201 (term539 A s) (term568 A lt2 x s)). Qed.
Lemma lem316203 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term589 A lt2 x s n) = (term566 A n lt2 x s).
Proof. exact (eq_refl (term589 A lt2 x s n)). Qed.
Lemma lem316204 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term590 A lt2 x s) = (term568 A lt2 x s).
Proof. exact (fun_ext (fun n : nat => @lem316203 A n lt2 x s)). Qed.
Lemma lem316205 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem316206 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term591 A lt2 x s) = (term569 A lt2 x s).
Proof. exact (MK_COMB (@lem316205) (@lem316204 A lt2 x s)). Qed.
Lemma lem316207 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (eq_refl (term549 A s)). Qed.
Lemma lem316208 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term587 A lt2 x s) = (term581 A lt2 x s).
Proof. exact (MK_COMB (@lem316207 A s) (@lem316206 A lt2 x s)). Qed.
Lemma lem316209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316210 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term592 A lt2 x s) = (term593 A lt2 x s).
Proof. exact (MK_COMB (@lem316209) (@lem316208 A lt2 x s)). Qed.
Lemma lem316211 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term589 A lt2 x s n) = (term566 A n lt2 x s).
Proof. exact (eq_refl (term589 A lt2 x s n)). Qed.
Lemma lem316212 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (eq_refl (term549 A s)). Qed.
Lemma lem316213 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term594 A lt2 x s n) = (term595 A n lt2 x s).
Proof. exact (MK_COMB (@lem316212 A s) (@lem316211 A n lt2 x s)). Qed.
Lemma lem316214 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term596 A lt2 x s) = (term597 A lt2 x s).
Proof. exact (fun_ext (fun n : nat => @lem316213 A n lt2 x s)). Qed.
Lemma lem316215 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem316216 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term588 A lt2 x s) = (term598 A lt2 x s).
Proof. exact (MK_COMB (@lem316215) (@lem316214 A lt2 x s)). Qed.
Lemma lem316217 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : ((term587 A lt2 x s) = (term588 A lt2 x s)) = ((term581 A lt2 x s) = (term598 A lt2 x s)).
Proof. exact (MK_COMB (@lem316210 A lt2 x s) (@lem316216 A lt2 x s)). Qed.
Lemma lem316218 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term581 A lt2 x s) = (term598 A lt2 x s).
Proof. exact (EQ_MP (@lem316217 A lt2 x s) (@lem316202 A lt2 x s)). Qed.
Lemma lem316219 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term583 A lt2 s) = (term599 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem316218 A lt2 x s)). Qed.
Lemma lem316220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem316221 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term584 A lt2 s) = (term600 A lt2 s).
Proof. exact (MK_COMB (@lem316220 A) (@lem316219 A lt2 s)). Qed.
Lemma lem316222 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term572 A lt2 s) = (term600 A lt2 s).
Proof. exact (TRANS (@lem316198 A lt2 s) (@lem316221 A lt2 s)). Qed.
Lemma lem316224 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term551 A lt2 s) = (term600 A lt2 s).
Proof. exact (TRANS (@lem316178 A lt2 s) (@lem316222 A lt2 s)). Qed.
Lemma lem316225 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term507 A lt2 s) = (term600 A lt2 s).
Proof. exact (TRANS (@lem316036 A lt2 s) (@lem316224 A lt2 s)). Qed.
Lemma lem316226 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term507 A lt2 s) : term600 A lt2 s.
Proof. exact (EQ_MP (@lem316225 A lt2 s) (@lem315967 A lt2 s h1)). Qed.
Lemma lem316227 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term598 A lt2 x s) : term598 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem316228 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term595 A n lt2 x s) : term595 A n lt2 x s.
Proof. exact (h1). Qed.
Lemma lem316239 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem316240 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem316239 A lt2 s n)). Qed.
Lemma lem316241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316242 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem316241) (@lem316240 A lt2 s)). Qed.
Lemma lem316243 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term3 A lt2 s.
Proof. exact (EQ_MP (@lem316242 A lt2 s) (@lem315980 A lt2 s h1)). Qed.
Lemma lem316252 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (term531 A y s n) = (term531 A y s n).
Proof. exact (eq_refl (term531 A y s n)). Qed.
Lemma lem316253 {A : Type'} (y : A) (s : nat -> A) : (term533 A y s) = (term533 A y s).
Proof. exact (fun_ext (fun n : nat => @lem316252 A y s n)). Qed.
Lemma lem316254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316255 {A : Type'} (y : A) (s : nat -> A) : (term534 A y s) = (term534 A y s).
Proof. exact (MK_COMB (@lem316254) (@lem316253 A y s)). Qed.
Lemma lem316264 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term540 A lt2 y x) = (term540 A lt2 y x).
Proof. exact (eq_refl (term540 A lt2 y x)). Qed.
Lemma lem316265 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term542 A lt2 x y s) = (term542 A lt2 x y s).
Proof. exact (MK_COMB (@lem316264 A lt2 y x) (@lem316255 A y s)). Qed.
Lemma lem316266 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term543 A lt2 x s) = (term543 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem316265 A lt2 x y s)). Qed.
Lemma lem316267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316268 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term544 A lt2 x s) = (term544 A lt2 x s).
Proof. exact (MK_COMB (@lem316267 A) (@lem316266 A lt2 x s)). Qed.
Lemma lem316277 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term564 A x s n) = (term564 A x s n).
Proof. exact (eq_refl (term564 A x s n)). Qed.
Lemma lem316278 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term566 A n lt2 x s) = (term566 A n lt2 x s).
Proof. exact (MK_COMB (@lem316277 A x s n) (@lem316268 A lt2 x s)). Qed.
Lemma lem316287 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term531 A x s n) = (term531 A x s n).
Proof. exact (eq_refl (term531 A x s n)). Qed.
Lemma lem316288 {A : Type'} (x : A) (s : nat -> A) : (term533 A x s) = (term533 A x s).
Proof. exact (fun_ext (fun n : nat => @lem316287 A x s n)). Qed.
Lemma lem316289 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316290 {A : Type'} (x : A) (s : nat -> A) : (term534 A x s) = (term534 A x s).
Proof. exact (MK_COMB (@lem316289) (@lem316288 A x s)). Qed.
Lemma lem316291 {A : Type'} (s : nat -> A) : (term538 A s) = (term538 A s).
Proof. exact (fun_ext (fun x : A => @lem316290 A x s)). Qed.
Lemma lem316292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316293 {A : Type'} (s : nat -> A) : (term539 A s) = (term539 A s).
Proof. exact (MK_COMB (@lem316292 A) (@lem316291 A s)). Qed.
Lemma lem316294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem316295 {A : Type'} (s : nat -> A) : (term549 A s) = (term549 A s).
Proof. exact (MK_COMB (@lem316294) (@lem316293 A s)). Qed.
Lemma lem316296 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) : (term595 A n lt2 x s) = (term595 A n lt2 x s).
Proof. exact (MK_COMB (@lem316295 A s) (@lem316278 A n lt2 x s)). Qed.
Lemma lem316297 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term595 A n lt2 x s) : term595 A n lt2 x s.
Proof. exact (EQ_MP (@lem316296 A n lt2 x s) (@lem316228 A n lt2 x s h1)). Qed.
Lemma lem316298 {A : Type'} (s : nat -> A) (h1 : term539 A s) : term539 A s.
Proof. exact (h1). Qed.
Lemma lem316299 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term566 A n lt2 x s.
Proof. exact (h1). Qed.
Lemma lem316300 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term544 A lt2 x s.
Proof. exact (proj2 (@lem316299 A n lt2 x s h1)). Qed.
Lemma lem316310 {A : Type'} (x : A) (s : nat -> A) (n : nat) : (term531 A x s n) = (term531 A x s n).
Proof. exact (eq_refl (term531 A x s n)). Qed.
Lemma lem316311 {A : Type'} (x : A) (s : nat -> A) : (term533 A x s) = (term533 A x s).
Proof. exact (fun_ext (fun n : nat => @lem316310 A x s n)). Qed.
Lemma lem316312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316313 {A : Type'} (x : A) (s : nat -> A) : (term534 A x s) = (term534 A x s).
Proof. exact (MK_COMB (@lem316312) (@lem316311 A x s)). Qed.
Lemma lem316314 {A : Type'} (s : nat -> A) : (term538 A s) = (term538 A s).
Proof. exact (fun_ext (fun x : A => @lem316313 A x s)). Qed.
Lemma lem316315 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316317 {A : Type'} (s : nat -> A) : (term539 A s) = (term539 A s).
Proof. exact (MK_COMB (@lem316315 A) (@lem316314 A s)). Qed.
Lemma lem316318 {A : Type'} (s : nat -> A) (h1 : term539 A s) : term539 A s.
Proof. exact (EQ_MP (@lem316317 A s) (@lem316298 A s h1)). Qed.
Lemma lem316320 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term219 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (eq_refl (term219 A lt2 s n)). Qed.
Lemma lem316321 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term221 A lt2 s) = (term221 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem316320 A lt2 s n)). Qed.
Lemma lem316322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316324 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term3 A lt2 s) = (term3 A lt2 s).
Proof. exact (MK_COMB (@lem316322) (@lem316321 A lt2 s)). Qed.
Lemma lem316325 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term3 A lt2 s.
Proof. exact (EQ_MP (@lem316324 A lt2 s) (@lem316243 A lt2 s h1)). Qed.
Lemma lem316331 {A : Type'} (P : Prop) (Q : A -> Prop) : (term601 A P Q) = (term602 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem316332 (P : Prop) (Q : nat -> Prop) : (term603 P Q) = (term604 P Q).
Proof. exact (@lem316331 nat P Q). Qed.
Lemma lem316333 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term605 A lt2 x y s) = (term606 A lt2 x y s).
Proof. exact (@lem316332 (term607 A lt2 y x) (term533 A y s)). Qed.
Lemma lem316334 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (term608 A y s n) = (term531 A y s n).
Proof. exact (eq_refl (term608 A y s n)). Qed.
Lemma lem316335 {A : Type'} (y : A) (s : nat -> A) : (term609 A y s) = (term533 A y s).
Proof. exact (fun_ext (fun n : nat => @lem316334 A y s n)). Qed.
Lemma lem316336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316337 {A : Type'} (y : A) (s : nat -> A) : (term610 A y s) = (term534 A y s).
Proof. exact (MK_COMB (@lem316336) (@lem316335 A y s)). Qed.
Lemma lem316338 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term540 A lt2 y x) = (term540 A lt2 y x).
Proof. exact (eq_refl (term540 A lt2 y x)). Qed.
Lemma lem316339 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term605 A lt2 x y s) = (term542 A lt2 x y s).
Proof. exact (MK_COMB (@lem316338 A lt2 y x) (@lem316337 A y s)). Qed.
Lemma lem316340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316341 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term611 A lt2 x y s) = (term612 A lt2 x y s).
Proof. exact (MK_COMB (@lem316340) (@lem316339 A lt2 x y s)). Qed.
Lemma lem316342 {A : Type'} (y : A) (s : nat -> A) (n : nat) : (term608 A y s n) = (term531 A y s n).
Proof. exact (eq_refl (term608 A y s n)). Qed.
Lemma lem316343 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term540 A lt2 y x) = (term540 A lt2 y x).
Proof. exact (eq_refl (term540 A lt2 y x)). Qed.
Lemma lem316344 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) (n : nat) : (term613 A lt2 x y s n) = (term614 A lt2 x y s n).
Proof. exact (MK_COMB (@lem316343 A lt2 y x) (@lem316342 A y s n)). Qed.
Lemma lem316345 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term615 A lt2 x y s) = (term616 A lt2 x y s).
Proof. exact (fun_ext (fun n : nat => @lem316344 A lt2 x y s n)). Qed.
Lemma lem316346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316347 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term606 A lt2 x y s) = (term617 A lt2 x y s).
Proof. exact (MK_COMB (@lem316346) (@lem316345 A lt2 x y s)). Qed.
Lemma lem316348 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : ((term605 A lt2 x y s) = (term606 A lt2 x y s)) = ((term542 A lt2 x y s) = (term617 A lt2 x y s)).
Proof. exact (MK_COMB (@lem316341 A lt2 x y s) (@lem316347 A lt2 x y s)). Qed.
Lemma lem316349 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term542 A lt2 x y s) = (term617 A lt2 x y s).
Proof. exact (EQ_MP (@lem316348 A lt2 x y s) (@lem316333 A lt2 x y s)). Qed.
Lemma lem316350 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term543 A lt2 x s) = (term618 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem316349 A lt2 x y s)). Qed.
Lemma lem316351 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316352 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term544 A lt2 x s) = (term619 A lt2 x s).
Proof. exact (MK_COMB (@lem316351 A) (@lem316350 A lt2 x s)). Qed.
Lemma lem316359 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) (n : nat) : (term614 A lt2 x y s n) = (term614 A lt2 x y s n).
Proof. exact (eq_refl (term614 A lt2 x y s n)). Qed.
Lemma lem316360 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term616 A lt2 x y s) = (term616 A lt2 x y s).
Proof. exact (fun_ext (fun n : nat => @lem316359 A lt2 x y s n)). Qed.
Lemma lem316361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem316362 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (s : nat -> A) : (term617 A lt2 x y s) = (term617 A lt2 x y s).
Proof. exact (MK_COMB (@lem316361) (@lem316360 A lt2 x y s)). Qed.
Lemma lem316363 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term618 A lt2 x s) = (term618 A lt2 x s).
Proof. exact (fun_ext (fun y : A => @lem316362 A lt2 x y s)). Qed.
Lemma lem316364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem316365 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term619 A lt2 x s) = (term619 A lt2 x s).
Proof. exact (MK_COMB (@lem316364 A) (@lem316363 A lt2 x s)). Qed.
Lemma lem316366 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) : (term544 A lt2 x s) = (term619 A lt2 x s).
Proof. exact (TRANS (@lem316352 A lt2 x s) (@lem316365 A lt2 x s)). Qed.
Lemma lem316367 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term619 A lt2 x s.
Proof. exact (EQ_MP (@lem316366 A lt2 x s) (@lem316300 A n lt2 x s h1)). Qed.
Lemma lem316371 {A : Type'} (_6961 : A) (s : nat -> A) (h1 : term539 A s) : term620 A s _6961.
Proof. exact (@lem316318 A s h1 _6961). Qed.
Lemma lem316372 {A : Type'} (_6961 : A) (s : nat -> A) : (term620 A s _6961) = (term534 A _6961 s).
Proof. exact (eq_refl (term620 A s _6961)). Qed.
Lemma lem316373 {A : Type'} (_6961 : A) (s : nat -> A) (h1 : term539 A s) : term534 A _6961 s.
Proof. exact (EQ_MP (@lem316372 A _6961 s) (@lem316371 A _6961 s h1)). Qed.
Lemma lem316374 {A : Type'} (_6961 : A) (_6962 : nat) (s : nat -> A) (h1 : term539 A s) : term608 A _6961 s _6962.
Proof. exact (@lem316373 A _6961 s h1 _6962). Qed.
Lemma lem316375 {A : Type'} (_6961 : A) (s : nat -> A) (_6962 : nat) : (term608 A _6961 s _6962) = (term531 A _6961 s _6962).
Proof. exact (eq_refl (term608 A _6961 s _6962)). Qed.
Lemma lem316377 {A : Type'} (_6963 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term242 A lt2 s _6963.
Proof. exact (@lem316325 A lt2 s h1 _6963). Qed.
Lemma lem316378 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_6963 : nat) : (term242 A lt2 s _6963) = (term219 A lt2 s _6963).
Proof. exact (eq_refl (term242 A lt2 s _6963)). Qed.
Lemma lem316380 {A : Type'} (_6964 : A) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term621 A lt2 x s _6964.
Proof. exact (@lem316367 A n lt2 x s h1 _6964). Qed.
Lemma lem316381 {A : Type'} (lt2 : type1402 A) (x : A) (_6964 : A) (s : nat -> A) : (term621 A lt2 x s _6964) = (term617 A lt2 x _6964 s).
Proof. exact (eq_refl (term621 A lt2 x s _6964)). Qed.
Lemma lem316382 {A : Type'} (_6964 : A) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term617 A lt2 x _6964 s.
Proof. exact (EQ_MP (@lem316381 A lt2 x _6964 s) (@lem316380 A _6964 n lt2 x s h1)). Qed.
Lemma lem316383 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term622 A lt2 x _6964 s _6965.
Proof. exact (@lem316382 A _6964 n lt2 x s h1 _6965). Qed.
Lemma lem316384 {A : Type'} (lt2 : type1402 A) (x : A) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term622 A lt2 x _6964 s _6965) = (term614 A lt2 x _6964 s _6965).
Proof. exact (eq_refl (term622 A lt2 x _6964 s _6965)). Qed.
Lemma lem316389 {A : Type'} (_6961 : A) (_6962 : nat) (s : nat -> A) (h1 : term539 A s) : term531 A _6961 s _6962.
Proof. exact (EQ_MP (@lem316375 A _6961 s _6962) (@lem316374 A _6961 _6962 s h1)). Qed.
Lemma lem316393 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : x = (s n).
Proof. exact (proj1 (@lem316299 A n lt2 x s h1)). Qed.
Lemma lem316399 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term614 A lt2 x _6964 s _6965.
Proof. exact (EQ_MP (@lem316384 A lt2 x _6964 s _6965) (@lem316383 A _6964 _6965 n lt2 x s h1)). Qed.
Lemma lem316428 {A : Type'} (lt2 : type1402 A) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term623 A lt2 _6964 s _6965) = (term623 A lt2 _6964 s _6965).
Proof. exact (eq_refl (term623 A lt2 _6964 s _6965)). Qed.
Lemma lem316429 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : (term624 A lt2 _6964 s _6965 x) = (term625 A lt2 _6964 _6965 s n).
Proof. exact (MK_COMB (@lem316428 A lt2 _6964 s _6965) (@lem316393 A n lt2 x s h1)). Qed.
Lemma lem316430 {A : Type'} (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term625 A lt2 _6964 _6965 s n) = (term626 A lt2 n _6964 s _6965).
Proof. exact (eq_refl (term625 A lt2 _6964 _6965 s n)). Qed.
Lemma lem316431 {A : Type'} (lt2 : type1402 A) (_6964 : A) (s : nat -> A) (_6965 : nat) (x : A) : (term627 A lt2 _6964 s _6965 x) = (term627 A lt2 _6964 s _6965 x).
Proof. exact (eq_refl (term627 A lt2 _6964 s _6965 x)). Qed.
Lemma lem316432 {A : Type'} (x : A) (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : ((term624 A lt2 _6964 s _6965 x) = (term625 A lt2 _6964 _6965 s n)) = ((term624 A lt2 _6964 s _6965 x) = (term626 A lt2 n _6964 s _6965)).
Proof. exact (MK_COMB (@lem316431 A lt2 _6964 s _6965 x) (@lem316430 A lt2 n _6964 s _6965)). Qed.
Lemma lem316433 {A : Type'} (lt2 : type1402 A) (x : A) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term624 A lt2 _6964 s _6965 x) = (term614 A lt2 x _6964 s _6965).
Proof. exact (eq_refl (term624 A lt2 _6964 s _6965 x)). Qed.
Lemma lem316434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem316435 {A : Type'} (lt2 : type1402 A) (x : A) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term627 A lt2 _6964 s _6965 x) = (term628 A lt2 x _6964 s _6965).
Proof. exact (MK_COMB (@lem316434) (@lem316433 A lt2 x _6964 s _6965)). Qed.
Lemma lem316436 {A : Type'} (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term626 A lt2 n _6964 s _6965) = (term626 A lt2 n _6964 s _6965).
Proof. exact (eq_refl (term626 A lt2 n _6964 s _6965)). Qed.
Lemma lem316437 {A : Type'} (x : A) (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : ((term624 A lt2 _6964 s _6965 x) = (term626 A lt2 n _6964 s _6965)) = ((term614 A lt2 x _6964 s _6965) = (term626 A lt2 n _6964 s _6965)).
Proof. exact (MK_COMB (@lem316435 A lt2 x _6964 s _6965) (@lem316436 A lt2 n _6964 s _6965)). Qed.
Lemma lem316438 {A : Type'} (x : A) (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : ((term624 A lt2 _6964 s _6965 x) = (term625 A lt2 _6964 _6965 s n)) = ((term614 A lt2 x _6964 s _6965) = (term626 A lt2 n _6964 s _6965)).
Proof. exact (TRANS (@lem316432 A x lt2 n _6964 s _6965) (@lem316437 A x lt2 n _6964 s _6965)). Qed.
Lemma lem316439 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : (term614 A lt2 x _6964 s _6965) = (term626 A lt2 n _6964 s _6965).
Proof. exact (EQ_MP (@lem316438 A x lt2 n _6964 s _6965) (@lem316429 A _6964 _6965 n lt2 x s h1)). Qed.
Lemma lem316440 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term626 A lt2 n _6964 s _6965.
Proof. exact (EQ_MP (@lem316439 A _6964 _6965 n lt2 x s h1) (@lem316399 A _6964 _6965 n lt2 x s h1)). Qed.
Lemma lem316481 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem316482 {A : Type'} (x : A) : x = x.
Proof. exact (@lem316481 A x). Qed.
Lemma lem316483 {A : Type'} (s : nat -> A) (_6980 : nat) : (s _6980) = (s _6980).
Proof. exact (@lem316482 A (s _6980)). Qed.
Lemma lem316484 {A : Type'} (s : nat -> A) (_6980 : nat) : term629 A s _6980.
Proof. exact (fun h0 : term630 A s _6980 => @lem316483 A s _6980). Qed.
Lemma lem316486 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem316487 {A : Type'} (s : nat -> A) (_6980 : nat) : (term629 A s _6980) = ((s _6980) = (s _6980)).
Proof. exact (@lem316486 ((s _6980) = (s _6980))). Qed.
Lemma lem316488 {A : Type'} (s : nat -> A) (_6980 : nat) : (s _6980) = (s _6980).
Proof. exact (EQ_MP (@lem316487 A s _6980) (@lem316484 A s _6980)). Qed.
Lemma lem316491 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem316493 {A : Type'} (_6961 : A) (s : nat -> A) (_6962 : nat) : (term531 A _6961 s _6962) = (term631 A _6961 s _6962).
Proof. exact (@lem316491 (_6961 = (s _6962))). Qed.
Lemma lem316496 {A : Type'} (_6961 : A) (_6962 : nat) (s : nat -> A) (h1 : term539 A s) : term631 A _6961 s _6962.
Proof. exact (EQ_MP (@lem316493 A _6961 s _6962) (@lem316389 A _6961 _6962 s h1)). Qed.
Lemma lem316497 {A : Type'} (_6961 : A) (_6962 : nat) (s : nat -> A) (h1 : term539 A s) : term631 A _6961 s _6962.
Proof. exact (@lem316496 A _6961 _6962 s h1). Qed.
Lemma lem316498 {A : Type'} (_6980 : nat) (s : nat -> A) (h1 : term539 A s) : term632 A s _6980.
Proof. exact (@lem316497 A (s _6980) _6980 s h1). Qed.
Lemma lem316501 {A : Type'} (s : nat -> A) (h1 : term539 A s) : False.
Proof. exact (@lem316498 A (@el nat) s h1 (@lem316488 A s (@el nat))). Qed.
Lemma lem316502 {A : Type'} (s : nat -> A) (h1 : term539 A s) : term184.
Proof. exact (fun h0 : ~ False => @lem316501 A s h1). Qed.
Lemma lem316504 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem316505 : term184 = False.
Proof. exact (@lem316504 False). Qed.
Lemma lem316506 {A : Type'} (s : nat -> A) (h1 : term539 A s) : False.
Proof. exact (EQ_MP (@lem316505) (@lem316502 A s h1)). Qed.
Lemma lem316547 {A : Type'} (_6963 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term219 A lt2 s _6963.
Proof. exact (EQ_MP (@lem316378 A lt2 s _6963) (@lem316377 A _6963 lt2 s h1)). Qed.
Lemma lem316548 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term219 A lt2 s n.
Proof. exact (@lem316547 A n lt2 s h1). Qed.
Lemma lem316549 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term633 A lt2 s n.
Proof. exact (fun h0 : term634 A lt2 s n => @lem316548 A n lt2 s h1). Qed.
Lemma lem316551 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem316552 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term633 A lt2 s n) = (term219 A lt2 s n).
Proof. exact (@lem316551 (term219 A lt2 s n)). Qed.
Lemma lem316553 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term219 A lt2 s n.
Proof. exact (EQ_MP (@lem316552 A lt2 s n) (@lem316549 A n lt2 s h1)). Qed.
Lemma lem316555 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem316556 {A : Type'} (x : A) : x = x.
Proof. exact (@lem316555 A x). Qed.
Lemma lem316557 {A : Type'} (s : nat -> A) (n : nat) : (term215 A s n) = (term215 A s n).
Proof. exact (@lem316556 A (term215 A s n)). Qed.
Lemma lem316558 {A : Type'} (s : nat -> A) (n : nat) : term635 A s n.
Proof. exact (fun h0 : term636 A s n => @lem316557 A s n). Qed.
Lemma lem316560 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem316561 {A : Type'} (s : nat -> A) (n : nat) : (term635 A s n) = ((term215 A s n) = (term215 A s n)).
Proof. exact (@lem316560 ((term215 A s n) = (term215 A s n))). Qed.
Lemma lem316562 {A : Type'} (s : nat -> A) (n : nat) : (term215 A s n) = (term215 A s n).
Proof. exact (EQ_MP (@lem316561 A s n) (@lem316558 A s n)). Qed.
Lemma lem316564 (a : Prop) (b : Prop) : (term179 a b) = (term180 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem316565 {A : Type'} (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term626 A lt2 n _6964 s _6965) = (term637 A lt2 n _6964 s _6965).
Proof. exact (@lem316564 (term638 A lt2 _6964 s n) (_6964 = (s _6965))). Qed.
Lemma lem316567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem316568 {A : Type'} (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term637 A lt2 n _6964 s _6965) = (term639 A lt2 n _6964 s _6965).
Proof. exact (@lem316567 (term640 A lt2 n _6964 s _6965)). Qed.
Lemma lem316569 {A : Type'} (lt2 : type1402 A) (n : nat) (_6964 : A) (s : nat -> A) (_6965 : nat) : (term626 A lt2 n _6964 s _6965) = (term639 A lt2 n _6964 s _6965).
Proof. exact (TRANS (@lem316565 A lt2 n _6964 s _6965) (@lem316568 A lt2 n _6964 s _6965)). Qed.
Lemma lem316571 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term641 A lt2 s n.
Proof. exact (conj (@lem316553 A n lt2 s h1) (@lem316562 A s n)). Qed.
Lemma lem316573 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term639 A lt2 n _6964 s _6965.
Proof. exact (EQ_MP (@lem316569 A lt2 n _6964 s _6965) (@lem316440 A _6964 _6965 n lt2 x s h1)). Qed.
Lemma lem316574 {A : Type'} (_6964 : A) (_6965 : nat) (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term639 A lt2 n _6964 s _6965.
Proof. exact (@lem316573 A _6964 _6965 n lt2 x s h1). Qed.
Lemma lem316575 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term566 A n lt2 x s) : term642 A lt2 s n.
Proof. exact (@lem316574 A (term215 A s n) (S n) n lt2 x s h1). Qed.
Lemma lem316578 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term566 A n lt2 x s) : False.
Proof. exact (@lem316575 A n lt2 x s h2 (@lem316571 A n lt2 s h1)). Qed.
Lemma lem316579 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term566 A n lt2 x s) : term184.
Proof. exact (fun h0 : ~ False => @lem316578 A n lt2 x s h1 h2). Qed.
Lemma lem316581 (p : Prop) : (term162 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem316582 : term184 = False.
Proof. exact (@lem316581 False). Qed.
Lemma lem316584 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term566 A n lt2 x s) : False.
Proof. exact (EQ_MP (@lem316582) (@lem316579 A n lt2 x s h1 h2)). Qed.
Lemma lem316585 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term566 A n lt2 x s) : (term3 A lt2 s) = False.
Proof. exact (prop_ext (fun h3 : term3 A lt2 s => @lem316584 A n lt2 x s h1 h2) (fun h3 : False => @lem316325 A lt2 s h1)). Qed.
Lemma lem316586 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term566 A n lt2 x s) : False.
Proof. exact (EQ_MP (@lem316585 A n lt2 x s h1 h2) (@lem316325 A lt2 s h1)). Qed.
Lemma lem316587 {A : Type'} (s : nat -> A) (h1 : term539 A s) : (term539 A s) = False.
Proof. exact (prop_ext (fun h2 : term539 A s => @lem316506 A s h1) (fun h2 : False => @lem316318 A s h1)). Qed.
Lemma lem316588 {A : Type'} (s : nat -> A) (h1 : term539 A s) : False.
Proof. exact (EQ_MP (@lem316587 A s h1) (@lem316318 A s h1)). Qed.
Lemma lem316589 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term595 A n lt2 x s) : False.
Proof. exact (or_elim (@lem316297 A n lt2 x s h2) (fun h0 : term539 A s => @lem316588 A s h0) (fun h0 : term566 A n lt2 x s => @lem316586 A n lt2 x s h1 h0)). Qed.
Lemma lem316590 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term595 A n lt2 x s) : (term595 A n lt2 x s) = False.
Proof. exact (prop_ext (fun h3 : term595 A n lt2 x s => @lem316589 A n lt2 x s h1 h2) (fun h3 : False => @lem316297 A n lt2 x s h2)). Qed.
Lemma lem316591 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term595 A n lt2 x s) : False.
Proof. exact (EQ_MP (@lem316590 A n lt2 x s h1 h2) (@lem316297 A n lt2 x s h2)). Qed.
Lemma lem316592 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term595 A n lt2 x s) : (term3 A lt2 s) = False.
Proof. exact (prop_ext (fun h3 : term3 A lt2 s => @lem316591 A n lt2 x s h1 h2) (fun h3 : False => @lem316243 A lt2 s h1)). Qed.
Lemma lem316593 {A : Type'} (n : nat) (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term595 A n lt2 x s) : False.
Proof. exact (EQ_MP (@lem316592 A n lt2 x s h1 h2) (@lem316243 A lt2 s h1)). Qed.
Lemma lem316594 {A : Type'} (lt2 : type1402 A) (x : A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term598 A lt2 x s) : False.
Proof. exact (ex_elim (@lem316227 A lt2 x s h2) (fun n : nat => fun h0 : term597 A lt2 x s n => @lem316593 A n lt2 x s h1 h0)). Qed.
Lemma lem316595 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : False.
Proof. exact (ex_elim (@lem316226 A lt2 s h2) (fun x : A => fun h0 : term599 A lt2 s x => @lem316594 A lt2 x s h1 h0)). Qed.
Lemma lem316596 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : (term3 A lt2 s) = False.
Proof. exact (prop_ext (fun h3 : term3 A lt2 s => @lem316595 A lt2 s h1 h2) (fun h3 : False => @lem315980 A lt2 s h1)). Qed.
Lemma lem316597 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : False.
Proof. exact (EQ_MP (@lem316596 A lt2 s h1 h2) (@lem315980 A lt2 s h1)). Qed.
Lemma lem316598 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term514 A lt2 s.
Proof. exact (fun h0 : term507 A lt2 s => @lem316597 A lt2 s h1 h0). Qed.
Lemma lem316599 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term514 A lt2 s) = (term509 A lt2 s).
Proof. exact (@lem69 (term507 A lt2 s)). Qed.
Lemma lem316600 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term509 A lt2 s.
Proof. exact (EQ_MP (@lem316599 A lt2 s) (@lem316598 A lt2 s h1)). Qed.
Lemma lem316601 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term516 A lt2 s.
Proof. exact (fun h0 : term3 A lt2 s => @lem316600 A lt2 s h0). Qed.
Lemma lem316606 {A : Type'} (s : nat -> A) : term520 A s.
Proof. exact (fun lt2 : type1402 A => @lem316601 A lt2 s). Qed.
Lemma lem316611 {A : Type'} : term524 A.
Proof. exact (fun s : nat -> A => @lem316606 A s). Qed.
Lemma lem316612 {A : Type'} : term523 A.
Proof. exact (EQ_MP (@lem315965 A) (@lem316611 A)). Qed.
Lemma lem316613 {A : Type'} (s : nat -> A) : term643 A s.
Proof. exact (@lem316612 A s). Qed.
Lemma lem316614 {A : Type'} (s : nat -> A) : (term643 A s) = (term519 A s).
Proof. exact (eq_refl (term643 A s)). Qed.
Lemma lem316615 {A : Type'} (s : nat -> A) : term519 A s.
Proof. exact (EQ_MP (@lem316614 A s) (@lem316613 A s)). Qed.
Lemma lem316616 {A : Type'} (s : nat -> A) (lt2 : type1402 A) : term644 A s lt2.
Proof. exact (@lem316615 A s lt2). Qed.
Lemma lem316617 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term644 A s lt2) = (term510 A lt2 s).
Proof. exact (eq_refl (term644 A s lt2)). Qed.
Lemma lem316618 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term510 A lt2 s.
Proof. exact (EQ_MP (@lem316617 A lt2 s) (@lem316616 A s lt2)). Qed.
Lemma lem316620 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term510 A lt2 s.
Proof. exact (@lem315738 A lt2 s (@lem316618 A lt2 s)). Qed.
Lemma lem316621 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term514 A lt2 s.
Proof. exact (@lem316620 A lt2 s (@lem310223 A lt2 s h1)). Qed.
Lemma lem316622 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : False.
Proof. exact (@lem316621 A lt2 s h1 (@lem315722 A lt2 s h2)). Qed.
Lemma lem316623 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : (term507 A lt2 s) = False.
Proof. exact (prop_ext (fun h3 : term507 A lt2 s => @lem316622 A lt2 s h1 h2) (fun h3 : False => @lem315722 A lt2 s h2)). Qed.
Lemma lem316624 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) (h2 : term507 A lt2 s) : False.
Proof. exact (EQ_MP (@lem316623 A lt2 s h1 h2) (@lem315722 A lt2 s h2)). Qed.
Lemma lem316625 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term514 A lt2 s.
Proof. exact (fun h0 : term507 A lt2 s => @lem316624 A lt2 s h1 h0). Qed.
Lemma lem316626 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term514 A lt2 s) = (term509 A lt2 s).
Proof. exact (@lem69 (term507 A lt2 s)). Qed.
Lemma lem316627 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term509 A lt2 s.
Proof. exact (EQ_MP (@lem316626 A lt2 s) (@lem316625 A lt2 s h1)). Qed.
Lemma lem316628 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term508 A lt2 s.
Proof. exact (EQ_MP (@lem315721 A lt2 s) (@lem316627 A lt2 s h1)). Qed.
Lemma lem316629 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term3 A lt2 s) : term0 A lt2.
Proof. exact (ex_intro (term645 A lt2) (term480 A s) (@lem316628 A lt2 s h1)). Qed.
Lemma lem316630 {A : Type'} (lt2 : type1402 A) (h1 : term2 A lt2) : term0 A lt2.
Proof. exact (ex_elim (@lem310222 A lt2 h1) (fun s : nat -> A => fun h0 : term474 A lt2 s => @lem316629 A lt2 s h0)). Qed.
Lemma lem316631 {A : Type'} (lt2 : type1402 A) : term646 A lt2.
Proof. exact (fun h0 : term2 A lt2 => @lem316630 A lt2 h0). Qed.
Lemma lem316632 {A : Type'} (lt2 : type1402 A) (h1 : term0 A lt2) : term2 A lt2.
Proof. exact (ex_elim (@lem310220 A lt2 h1) (fun P : A -> Prop => fun h0 : term645 A lt2 P => @lem315606 A lt2 P h0)). Qed.
Lemma lem316633 {A : Type'} (lt2 : type1402 A) : term647 A lt2.
Proof. exact (fun h0 : term0 A lt2 => @lem316632 A lt2 h0). Qed.
Lemma lem316634 {A : Type'} (lt2 : type1402 A) : term648 A lt2.
Proof. exact (conj (@lem316633 A lt2) (@lem316631 A lt2)). Qed.
Lemma lem316635 {A : Type'} (lt2 : type1402 A) : (term648 A lt2) = ((term0 A lt2) = (term2 A lt2)).
Proof. exact (@lem32 (term0 A lt2) (term2 A lt2)). Qed.
Lemma lem316636 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = (term2 A lt2).
Proof. exact (EQ_MP (@lem316635 A lt2) (@lem316634 A lt2)). Qed.
