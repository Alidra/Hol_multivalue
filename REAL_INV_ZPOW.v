Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_ZPOW_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_POW_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3174261 (x : real) : term0 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem3174262 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3174264 (x : real) : term2 x.
Proof. exact (@lem1595722 x). Qed.
Lemma lem3174265 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem3174266 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem3174265 x) (@lem3174264 x)). Qed.
Lemma lem3174267 (x : real) (n : nat) : term4 x n.
Proof. exact (@lem3174266 x n). Qed.
Lemma lem3174268 (x : real) (n : nat) : (term4 x n) = ((term5 x n) = (term6 x n)).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem3174270 : term7.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3174271 (x : real) : term8 x.
Proof. exact (@lem3174270 x). Qed.
Lemma lem3174272 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem3174273 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem3174272 x) (@lem3174271 x)). Qed.
Lemma lem3174274 (x : real) (n : nat) : term10 x n.
Proof. exact (@lem3174273 x n). Qed.
Lemma lem3174275 (x : real) (n : nat) : (term10 x n) = ((term11 x n) = (term5 x n)).
Proof. exact (eq_refl (term10 x n)). Qed.
Lemma lem3174277 : term12.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3174278 (x : real) : term13 x.
Proof. exact (@lem3174277 x). Qed.
Lemma lem3174279 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem3174280 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem3174279 x) (@lem3174278 x)). Qed.
Lemma lem3174281 (x : real) (n : nat) : term15 x n.
Proof. exact (@lem3174280 x n). Qed.
Lemma lem3174282 (x : real) (n : nat) : (term15 x n) = ((term16 x n) = (real_pow x n)).
Proof. exact (eq_refl (term15 x n)). Qed.
Lemma lem3174284 (P : int -> Prop) : term17 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3174285 (P : int -> Prop) : (term17 P) = ((term18 P) = (term19 P)).
Proof. exact (eq_refl (term17 P)). Qed.
Lemma lem3174298 (P : int -> Prop) : (term18 P) = (term19 P).
Proof. exact (EQ_MP (@lem3174285 P) (@lem3174284 P)). Qed.
Lemma lem3174299 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem3174298 (term22 x)). Qed.
Lemma lem3174300 (x : real) (n : int) : (term23 x n) = ((term24 x n) = (term25 x n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem3174301 (x : real) : (term26 x) = (term22 x).
Proof. exact (fun_ext (fun n : int => @lem3174300 x n)). Qed.
Lemma lem3174302 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3174303 (x : real) : (term20 x) = (term27 x).
Proof. exact (MK_COMB (@lem3174302) (@lem3174301 x)). Qed.
Lemma lem3174304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3174305 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem3174304) (@lem3174303 x)). Qed.
Lemma lem3174306 (x : real) (n : nat) : (term30 x n) = ((term31 x n) = (term32 x n)).
Proof. exact (eq_refl (term30 x n)). Qed.
Lemma lem3174307 (x : real) : (term33 x) = (term34 x).
Proof. exact (fun_ext (fun n : nat => @lem3174306 x n)). Qed.
Lemma lem3174308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174309 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem3174308) (@lem3174307 x)). Qed.
Lemma lem3174310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174311 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3174310) (@lem3174309 x)). Qed.
Lemma lem3174312 (x : real) (n : nat) : (term39 x n) = ((term40 x n) = (term41 x n)).
Proof. exact (eq_refl (term39 x n)). Qed.
Lemma lem3174313 (x : real) : (term42 x) = (term43 x).
Proof. exact (fun_ext (fun n : nat => @lem3174312 x n)). Qed.
Lemma lem3174314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174315 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem3174314) (@lem3174313 x)). Qed.
Lemma lem3174316 (x : real) : (term21 x) = (term46 x).
Proof. exact (MK_COMB (@lem3174311 x) (@lem3174315 x)). Qed.
Lemma lem3174317 (x : real) : ((term20 x) = (term21 x)) = ((term27 x) = (term46 x)).
Proof. exact (MK_COMB (@lem3174305 x) (@lem3174316 x)). Qed.
Lemma lem3174318 (x : real) : (term27 x) = (term46 x).
Proof. exact (EQ_MP (@lem3174317 x) (@lem3174299 x)). Qed.
Lemma lem3174330 (x : real) (n : nat) : (term16 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174282 x n) (@lem3174281 x n)). Qed.
Lemma lem3174331 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3174332 (x : real) (n : nat) : (term31 x n) = (term5 x n).
Proof. exact (MK_COMB (@lem3174331) (@lem3174330 x n)). Qed.
Lemma lem3174333 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174334 (x : real) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (MK_COMB (@lem3174333) (@lem3174332 x n)). Qed.
Lemma lem3174336 (x : real) (n : nat) : (term16 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174282 x n) (@lem3174281 x n)). Qed.
Lemma lem3174337 (x : real) (n : nat) : (term32 x n) = (term6 x n).
Proof. exact (@lem3174336 (real_inv x) n). Qed.
Lemma lem3174338 (x : real) (n : nat) : ((term31 x n) = (term32 x n)) = ((term5 x n) = (term6 x n)).
Proof. exact (MK_COMB (@lem3174334 x n) (@lem3174337 x n)). Qed.
Lemma lem3174341 (x : real) : (term34 x) = (term49 x).
Proof. exact (fun_ext (fun n : nat => @lem3174338 x n)). Qed.
Lemma lem3174342 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174343 (x : real) : (term36 x) = (term3 x).
Proof. exact (MK_COMB (@lem3174342) (@lem3174341 x)). Qed.
Lemma lem3174350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174351 (x : real) : (term38 x) = (term50 x).
Proof. exact (MK_COMB (@lem3174350) (@lem3174343 x)). Qed.
Lemma lem3174361 (x : real) (n : nat) : (term11 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem3174275 x n) (@lem3174274 x n)). Qed.
Lemma lem3174362 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3174363 (x : real) (n : nat) : (term40 x n) = (term51 x n).
Proof. exact (MK_COMB (@lem3174362) (@lem3174361 x n)). Qed.
Lemma lem3174364 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174365 (x : real) (n : nat) : (term52 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem3174364) (@lem3174363 x n)). Qed.
Lemma lem3174367 (x : real) (n : nat) : (term11 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem3174275 x n) (@lem3174274 x n)). Qed.
Lemma lem3174368 (x : real) (n : nat) : (term41 x n) = (term54 x n).
Proof. exact (@lem3174367 (real_inv x) n). Qed.
Lemma lem3174369 (x : real) (n : nat) : ((term40 x n) = (term41 x n)) = ((term51 x n) = (term54 x n)).
Proof. exact (MK_COMB (@lem3174365 x n) (@lem3174368 x n)). Qed.
Lemma lem3174372 (x : real) : (term43 x) = (term55 x).
Proof. exact (fun_ext (fun n : nat => @lem3174369 x n)). Qed.
Lemma lem3174373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174374 (x : real) : (term45 x) = (term56 x).
Proof. exact (MK_COMB (@lem3174373) (@lem3174372 x)). Qed.
Lemma lem3174381 (x : real) : (term46 x) = (term57 x).
Proof. exact (MK_COMB (@lem3174351 x) (@lem3174374 x)). Qed.
Lemma lem3174384 (x : real) : (term27 x) = (term57 x).
Proof. exact (TRANS (@lem3174318 x) (@lem3174381 x)). Qed.
Lemma lem3174385 : term58 = term59.
Proof. exact (fun_ext (fun x : real => @lem3174384 x)). Qed.
Lemma lem3174386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174387 : term60 = term61.
Proof. exact (MK_COMB (@lem3174386) (@lem3174385)). Qed.
Lemma lem3174394 : term61 = term60.
Proof. exact (SYM (@lem3174387)). Qed.
Lemma lem3174408 (x : real) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem3174268 x n) (@lem3174267 x n)). Qed.
Lemma lem3174409 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174410 (x : real) (n : nat) : (term48 x n) = (term62 x n).
Proof. exact (MK_COMB (@lem3174409) (@lem3174408 x n)). Qed.
Lemma lem3174411 (x : real) (n : nat) : (term6 x n) = (term6 x n).
Proof. exact (eq_refl (term6 x n)). Qed.
Lemma lem3174412 (x : real) (n : nat) : ((term5 x n) = (term6 x n)) = ((term6 x n) = (term6 x n)).
Proof. exact (MK_COMB (@lem3174410 x n) (@lem3174411 x n)). Qed.
Lemma lem3174414 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3174415 (x : real) : (x = x) = True.
Proof. exact (@lem3174414 real x). Qed.
Lemma lem3174416 (x : real) (n : nat) : ((term6 x n) = (term6 x n)) = True.
Proof. exact (@lem3174415 (term6 x n)). Qed.
Lemma lem3174417 (x : real) (n : nat) : ((term5 x n) = (term6 x n)) = True.
Proof. exact (TRANS (@lem3174412 x n) (@lem3174416 x n)). Qed.
Lemma lem3174418 (x : real) : (term49 x) = term63.
Proof. exact (fun_ext (fun n : nat => @lem3174417 x n)). Qed.
Lemma lem3174419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174420 (x : real) : (term3 x) = term64.
Proof. exact (MK_COMB (@lem3174419) (@lem3174418 x)). Qed.
Lemma lem3174422 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174423 (t : Prop) : (term66 t) = t.
Proof. exact (@lem3174422 nat t). Qed.
Lemma lem3174424 : term64 = True.
Proof. exact (@lem3174423 True). Qed.
Lemma lem3174425 (x : real) : (term3 x) = True.
Proof. exact (TRANS (@lem3174420 x) (@lem3174424)). Qed.
Lemma lem3174426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174427 (x : real) : (term50 x) = (and True).
Proof. exact (MK_COMB (@lem3174426) (@lem3174425 x)). Qed.
Lemma lem3174435 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem3174262 x) (@lem3174261 x)). Qed.
Lemma lem3174436 (x : real) (n : nat) : (term51 x n) = (real_pow x n).
Proof. exact (@lem3174435 (real_pow x n)). Qed.
Lemma lem3174437 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174438 (x : real) (n : nat) : (term53 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem3174437) (@lem3174436 x n)). Qed.
Lemma lem3174440 (x : real) (n : nat) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem3174268 x n) (@lem3174267 x n)). Qed.
Lemma lem3174441 (x : real) (n : nat) : (term54 x n) = (term68 x n).
Proof. exact (@lem3174440 (real_inv x) n). Qed.
Lemma lem3174443 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem3174262 x) (@lem3174261 x)). Qed.
Lemma lem3174444 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem3174445 (x : real) : (term69 x) = (real_pow x).
Proof. exact (MK_COMB (@lem3174444) (@lem3174443 x)). Qed.
Lemma lem3174446 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3174447 (x : real) (n : nat) : (term68 x n) = (real_pow x n).
Proof. exact (MK_COMB (@lem3174445 x) (@lem3174446 n)). Qed.
Lemma lem3174448 (x : real) (n : nat) : (term54 x n) = (real_pow x n).
Proof. exact (TRANS (@lem3174441 x n) (@lem3174447 x n)). Qed.
Lemma lem3174449 (x : real) (n : nat) : ((term51 x n) = (term54 x n)) = ((real_pow x n) = (real_pow x n)).
Proof. exact (MK_COMB (@lem3174438 x n) (@lem3174448 x n)). Qed.
Lemma lem3174451 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3174452 (x : real) : (x = x) = True.
Proof. exact (@lem3174451 real x). Qed.
Lemma lem3174453 (x : real) (n : nat) : ((real_pow x n) = (real_pow x n)) = True.
Proof. exact (@lem3174452 (real_pow x n)). Qed.
Lemma lem3174454 (x : real) (n : nat) : ((term51 x n) = (term54 x n)) = True.
Proof. exact (TRANS (@lem3174449 x n) (@lem3174453 x n)). Qed.
Lemma lem3174455 (x : real) : (term55 x) = term63.
Proof. exact (fun_ext (fun n : nat => @lem3174454 x n)). Qed.
Lemma lem3174456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174457 (x : real) : (term56 x) = term64.
Proof. exact (MK_COMB (@lem3174456) (@lem3174455 x)). Qed.
Lemma lem3174459 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174460 (t : Prop) : (term66 t) = t.
Proof. exact (@lem3174459 nat t). Qed.
Lemma lem3174461 : term64 = True.
Proof. exact (@lem3174460 True). Qed.
Lemma lem3174462 (x : real) : (term56 x) = True.
Proof. exact (TRANS (@lem3174457 x) (@lem3174461)). Qed.
Lemma lem3174463 (x : real) : (term57 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3174427 x) (@lem3174462 x)). Qed.
Lemma lem3174465 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3174466 : (True /\ True) = True.
Proof. exact (@lem3174465 True). Qed.
Lemma lem3174467 (x : real) : (term57 x) = True.
Proof. exact (TRANS (@lem3174463 x) (@lem3174466)). Qed.
Lemma lem3174468 : term59 = term70.
Proof. exact (fun_ext (fun x : real => @lem3174467 x)). Qed.
Lemma lem3174469 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174470 : term61 = term71.
Proof. exact (MK_COMB (@lem3174469) (@lem3174468)). Qed.
Lemma lem3174472 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174473 (t : Prop) : (term72 t) = t.
Proof. exact (@lem3174472 real t). Qed.
Lemma lem3174474 : term71 = True.
Proof. exact (@lem3174473 True). Qed.
Lemma lem3174475 : term61 = True.
Proof. exact (TRANS (@lem3174470) (@lem3174474)). Qed.
Lemma lem3174476 : True = term61.
Proof. exact (SYM (@lem3174475)). Qed.
Lemma lem3174477 : term61.
Proof. exact (EQ_MP (@lem3174476) (@lem0)). Qed.
Lemma lem3174478 : term60.
Proof. exact (EQ_MP (@lem3174394) (@lem3174477)). Qed.
