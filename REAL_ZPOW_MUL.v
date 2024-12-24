Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_MUL_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_POW_MUL_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3175239 (x : real) : term0 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem3175240 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3175241 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3175240 x) (@lem3175239 x)). Qed.
Lemma lem3175242 (x : real) (y : real) : term2 x y.
Proof. exact (@lem3175241 x y). Qed.
Lemma lem3175243 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem3175245 (x : real) : term5 x.
Proof. exact (@lem1595570 x). Qed.
Lemma lem3175246 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem3175247 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem3175246 x) (@lem3175245 x)). Qed.
Lemma lem3175248 (x : real) (y : real) : term7 x y.
Proof. exact (@lem3175247 x y). Qed.
Lemma lem3175249 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem3175250 (x : real) (y : real) : term8 x y.
Proof. exact (EQ_MP (@lem3175249 x y) (@lem3175248 x y)). Qed.
Lemma lem3175251 (x : real) (y : real) (n : nat) : term9 x y n.
Proof. exact (@lem3175250 x y n). Qed.
Lemma lem3175252 (x : real) (y : real) (n : nat) : (term9 x y n) = ((term10 x y n) = (term11 x y n)).
Proof. exact (eq_refl (term9 x y n)). Qed.
Lemma lem3175254 : term12.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3175255 (x : real) : term13 x.
Proof. exact (@lem3175254 x). Qed.
Lemma lem3175256 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem3175257 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem3175256 x) (@lem3175255 x)). Qed.
Lemma lem3175258 (x : real) (n : nat) : term15 x n.
Proof. exact (@lem3175257 x n). Qed.
Lemma lem3175259 (x : real) (n : nat) : (term15 x n) = ((term16 x n) = (term17 x n)).
Proof. exact (eq_refl (term15 x n)). Qed.
Lemma lem3175261 : term18.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3175262 (x : real) : term19 x.
Proof. exact (@lem3175261 x). Qed.
Lemma lem3175263 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem3175264 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem3175263 x) (@lem3175262 x)). Qed.
Lemma lem3175265 (x : real) (n : nat) : term21 x n.
Proof. exact (@lem3175264 x n). Qed.
Lemma lem3175266 (x : real) (n : nat) : (term21 x n) = ((term22 x n) = (real_pow x n)).
Proof. exact (eq_refl (term21 x n)). Qed.
Lemma lem3175268 (P : int -> Prop) : term23 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3175269 (P : int -> Prop) : (term23 P) = ((term24 P) = (term25 P)).
Proof. exact (eq_refl (term23 P)). Qed.
Lemma lem3175288 (P : int -> Prop) : (term24 P) = (term25 P).
Proof. exact (EQ_MP (@lem3175269 P) (@lem3175268 P)). Qed.
Lemma lem3175289 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem3175288 (term28 x y)). Qed.
Lemma lem3175290 (x : real) (y : real) (n : int) : (term29 x y n) = ((term30 x y n) = (term31 x y n)).
Proof. exact (eq_refl (term29 x y n)). Qed.
Lemma lem3175291 (x : real) (y : real) : (term32 x y) = (term28 x y).
Proof. exact (fun_ext (fun n : int => @lem3175290 x y n)). Qed.
Lemma lem3175292 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3175293 (x : real) (y : real) : (term26 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem3175292) (@lem3175291 x y)). Qed.
Lemma lem3175294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3175295 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem3175294) (@lem3175293 x y)). Qed.
Lemma lem3175296 (x : real) (y : real) (n : nat) : (term36 x y n) = ((term37 x y n) = (term38 x y n)).
Proof. exact (eq_refl (term36 x y n)). Qed.
Lemma lem3175297 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (fun_ext (fun n : nat => @lem3175296 x y n)). Qed.
Lemma lem3175298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175299 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem3175298) (@lem3175297 x y)). Qed.
Lemma lem3175300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3175301 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem3175300) (@lem3175299 x y)). Qed.
Lemma lem3175302 (x : real) (y : real) (n : nat) : (term45 x y n) = ((term46 x y n) = (term47 x y n)).
Proof. exact (eq_refl (term45 x y n)). Qed.
Lemma lem3175303 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (fun_ext (fun n : nat => @lem3175302 x y n)). Qed.
Lemma lem3175304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175305 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem3175304) (@lem3175303 x y)). Qed.
Lemma lem3175306 (x : real) (y : real) : (term27 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem3175301 x y) (@lem3175305 x y)). Qed.
Lemma lem3175307 (x : real) (y : real) : ((term26 x y) = (term27 x y)) = ((term33 x y) = (term52 x y)).
Proof. exact (MK_COMB (@lem3175295 x y) (@lem3175306 x y)). Qed.
Lemma lem3175308 (x : real) (y : real) : (term33 x y) = (term52 x y).
Proof. exact (EQ_MP (@lem3175307 x y) (@lem3175289 x y)). Qed.
Lemma lem3175320 (x : real) (n : nat) : (term22 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3175266 x n) (@lem3175265 x n)). Qed.
Lemma lem3175321 (x : real) (y : real) (n : nat) : (term37 x y n) = (term10 x y n).
Proof. exact (@lem3175320 (real_mul x y) n). Qed.
Lemma lem3175323 (x : real) (y : real) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (EQ_MP (@lem3175252 x y n) (@lem3175251 x y n)). Qed.
Lemma lem3175324 (x : real) (y : real) (n : nat) : (term37 x y n) = (term11 x y n).
Proof. exact (TRANS (@lem3175321 x y n) (@lem3175323 x y n)). Qed.
Lemma lem3175325 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175326 (x : real) (y : real) (n : nat) : (term53 x y n) = (term54 x y n).
Proof. exact (MK_COMB (@lem3175325) (@lem3175324 x y n)). Qed.
Lemma lem3175328 (x : real) (n : nat) : (term22 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3175266 x n) (@lem3175265 x n)). Qed.
Lemma lem3175329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175330 (x : real) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem3175329) (@lem3175328 x n)). Qed.
Lemma lem3175332 (x : real) (n : nat) : (term22 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3175266 x n) (@lem3175265 x n)). Qed.
Lemma lem3175333 (y : real) (n : nat) : (term22 y n) = (real_pow y n).
Proof. exact (@lem3175332 y n). Qed.
Lemma lem3175334 (x : real) (y : real) (n : nat) : (term38 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem3175330 x n) (@lem3175333 y n)). Qed.
Lemma lem3175335 (x : real) (y : real) (n : nat) : ((term37 x y n) = (term38 x y n)) = ((term11 x y n) = (term11 x y n)).
Proof. exact (MK_COMB (@lem3175326 x y n) (@lem3175334 x y n)). Qed.
Lemma lem3175337 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175338 (x : real) : (x = x) = True.
Proof. exact (@lem3175337 real x). Qed.
Lemma lem3175339 (x : real) (y : real) (n : nat) : ((term11 x y n) = (term11 x y n)) = True.
Proof. exact (@lem3175338 (term11 x y n)). Qed.
Lemma lem3175340 (x : real) (y : real) (n : nat) : ((term37 x y n) = (term38 x y n)) = True.
Proof. exact (TRANS (@lem3175335 x y n) (@lem3175339 x y n)). Qed.
Lemma lem3175341 (x : real) (y : real) : (term40 x y) = term57.
Proof. exact (fun_ext (fun n : nat => @lem3175340 x y n)). Qed.
Lemma lem3175342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175343 (x : real) (y : real) : (term42 x y) = term58.
Proof. exact (MK_COMB (@lem3175342) (@lem3175341 x y)). Qed.
Lemma lem3175345 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175346 (t : Prop) : (term60 t) = t.
Proof. exact (@lem3175345 nat t). Qed.
Lemma lem3175347 : term58 = True.
Proof. exact (@lem3175346 True). Qed.
Lemma lem3175348 (x : real) (y : real) : (term42 x y) = True.
Proof. exact (TRANS (@lem3175343 x y) (@lem3175347)). Qed.
Lemma lem3175349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3175350 (x : real) (y : real) : (term44 x y) = (and True).
Proof. exact (MK_COMB (@lem3175349) (@lem3175348 x y)). Qed.
Lemma lem3175360 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3175259 x n) (@lem3175258 x n)). Qed.
Lemma lem3175361 (x : real) (y : real) (n : nat) : (term46 x y n) = (term61 x y n).
Proof. exact (@lem3175360 (real_mul x y) n). Qed.
Lemma lem3175363 (x : real) (y : real) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (EQ_MP (@lem3175252 x y n) (@lem3175251 x y n)). Qed.
Lemma lem3175364 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3175365 (x : real) (y : real) (n : nat) : (term61 x y n) = (term62 x y n).
Proof. exact (MK_COMB (@lem3175364) (@lem3175363 x y n)). Qed.
Lemma lem3175367 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem3175243 x y) (@lem3175242 x y)). Qed.
Lemma lem3175368 (x : real) (y : real) (n : nat) : (term62 x y n) = (term63 x y n).
Proof. exact (@lem3175367 (real_pow x n) (real_pow y n)). Qed.
Lemma lem3175369 (x : real) (y : real) (n : nat) : (term61 x y n) = (term63 x y n).
Proof. exact (TRANS (@lem3175365 x y n) (@lem3175368 x y n)). Qed.
Lemma lem3175370 (x : real) (y : real) (n : nat) : (term46 x y n) = (term63 x y n).
Proof. exact (TRANS (@lem3175361 x y n) (@lem3175369 x y n)). Qed.
Lemma lem3175371 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3175372 (x : real) (y : real) (n : nat) : (term64 x y n) = (term65 x y n).
Proof. exact (MK_COMB (@lem3175371) (@lem3175370 x y n)). Qed.
Lemma lem3175374 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3175259 x n) (@lem3175258 x n)). Qed.
Lemma lem3175375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3175376 (x : real) (n : nat) : (term66 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem3175375) (@lem3175374 x n)). Qed.
Lemma lem3175378 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem3175259 x n) (@lem3175258 x n)). Qed.
Lemma lem3175379 (y : real) (n : nat) : (term16 y n) = (term17 y n).
Proof. exact (@lem3175378 y n). Qed.
Lemma lem3175380 (x : real) (y : real) (n : nat) : (term47 x y n) = (term63 x y n).
Proof. exact (MK_COMB (@lem3175376 x n) (@lem3175379 y n)). Qed.
Lemma lem3175381 (x : real) (y : real) (n : nat) : ((term46 x y n) = (term47 x y n)) = ((term63 x y n) = (term63 x y n)).
Proof. exact (MK_COMB (@lem3175372 x y n) (@lem3175380 x y n)). Qed.
Lemma lem3175383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3175384 (x : real) : (x = x) = True.
Proof. exact (@lem3175383 real x). Qed.
Lemma lem3175385 (x : real) (y : real) (n : nat) : ((term63 x y n) = (term63 x y n)) = True.
Proof. exact (@lem3175384 (term63 x y n)). Qed.
Lemma lem3175386 (x : real) (y : real) (n : nat) : ((term46 x y n) = (term47 x y n)) = True.
Proof. exact (TRANS (@lem3175381 x y n) (@lem3175385 x y n)). Qed.
Lemma lem3175387 (x : real) (y : real) : (term49 x y) = term57.
Proof. exact (fun_ext (fun n : nat => @lem3175386 x y n)). Qed.
Lemma lem3175388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3175389 (x : real) (y : real) : (term51 x y) = term58.
Proof. exact (MK_COMB (@lem3175388) (@lem3175387 x y)). Qed.
Lemma lem3175391 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175392 (t : Prop) : (term60 t) = t.
Proof. exact (@lem3175391 nat t). Qed.
Lemma lem3175393 : term58 = True.
Proof. exact (@lem3175392 True). Qed.
Lemma lem3175394 (x : real) (y : real) : (term51 x y) = True.
Proof. exact (TRANS (@lem3175389 x y) (@lem3175393)). Qed.
Lemma lem3175395 (x : real) (y : real) : (term52 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem3175350 x y) (@lem3175394 x y)). Qed.
Lemma lem3175397 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3175398 : (True /\ True) = True.
Proof. exact (@lem3175397 True). Qed.
Lemma lem3175399 (x : real) (y : real) : (term52 x y) = True.
Proof. exact (TRANS (@lem3175395 x y) (@lem3175398)). Qed.
Lemma lem3175400 (x : real) (y : real) : (term33 x y) = True.
Proof. exact (TRANS (@lem3175308 x y) (@lem3175399 x y)). Qed.
Lemma lem3175401 (x : real) : (term68 x) = term69.
Proof. exact (fun_ext (fun y : real => @lem3175400 x y)). Qed.
Lemma lem3175402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175403 (x : real) : (term70 x) = term71.
Proof. exact (MK_COMB (@lem3175402) (@lem3175401 x)). Qed.
Lemma lem3175405 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175406 (t : Prop) : (term72 t) = t.
Proof. exact (@lem3175405 real t). Qed.
Lemma lem3175407 : term71 = True.
Proof. exact (@lem3175406 True). Qed.
Lemma lem3175408 (x : real) : (term70 x) = True.
Proof. exact (TRANS (@lem3175403 x) (@lem3175407)). Qed.
Lemma lem3175409 : term73 = term69.
Proof. exact (fun_ext (fun x : real => @lem3175408 x)). Qed.
Lemma lem3175410 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3175411 : term74 = term71.
Proof. exact (MK_COMB (@lem3175410) (@lem3175409)). Qed.
Lemma lem3175413 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3175414 (t : Prop) : (term72 t) = t.
Proof. exact (@lem3175413 real t). Qed.
Lemma lem3175415 : term71 = True.
Proof. exact (@lem3175414 True). Qed.
Lemma lem3175416 : term74 = True.
Proof. exact (TRANS (@lem3175411) (@lem3175415)). Qed.
Lemma lem3175417 : True = term74.
Proof. exact (SYM (@lem3175416)). Qed.
Lemma lem3175418 : term74.
Proof. exact (EQ_MP (@lem3175417) (@lem0)). Qed.
