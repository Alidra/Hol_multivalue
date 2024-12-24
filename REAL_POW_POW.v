Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_POW_term_abbrevs.
Require Import MULT_CLAUSES_spec.
Require Import REAL_POW_ADD_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1640306 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1640307 (x : real) (m : nat) : term1 x m.
Proof. exact (@lem1640306 (term2 x m)). Qed.
Lemma lem1640308 (x : real) (m : nat) : (term3 x m) = ((term4 x m) = (term5 x m)).
Proof. exact (eq_refl (term3 x m)). Qed.
Lemma lem1640309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640310 (x : real) (m : nat) : (term6 x m) = (term7 x m).
Proof. exact (MK_COMB (@lem1640309) (@lem1640308 x m)). Qed.
Lemma lem1640311 (x : real) (m : nat) (n : nat) : (term8 x m n) = ((term9 x m n) = (term10 x m n)).
Proof. exact (eq_refl (term8 x m n)). Qed.
Lemma lem1640312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640313 (x : real) (m : nat) (n : nat) : (term11 x m n) = (term12 x m n).
Proof. exact (MK_COMB (@lem1640312) (@lem1640311 x m n)). Qed.
Lemma lem1640314 (x : real) (m : nat) (n : nat) : (term13 x m n) = ((term14 x m n) = (term15 x m n)).
Proof. exact (eq_refl (term13 x m n)). Qed.
Lemma lem1640315 (x : real) (m : nat) (n : nat) : (term16 x m n) = (term17 x m n).
Proof. exact (MK_COMB (@lem1640313 x m n) (@lem1640314 x m n)). Qed.
Lemma lem1640316 (x : real) (m : nat) : (term18 x m) = (term19 x m).
Proof. exact (fun_ext (fun n : nat => @lem1640315 x m n)). Qed.
Lemma lem1640317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1640318 (x : real) (m : nat) : (term20 x m) = (term21 x m).
Proof. exact (MK_COMB (@lem1640317) (@lem1640316 x m)). Qed.
Lemma lem1640319 (x : real) (m : nat) : (term22 x m) = (term23 x m).
Proof. exact (MK_COMB (@lem1640310 x m) (@lem1640318 x m)). Qed.
Lemma lem1640320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640321 (x : real) (m : nat) : (term24 x m) = (term25 x m).
Proof. exact (MK_COMB (@lem1640320) (@lem1640319 x m)). Qed.
Lemma lem1640322 (x : real) (m : nat) (n : nat) : (term8 x m n) = ((term9 x m n) = (term10 x m n)).
Proof. exact (eq_refl (term8 x m n)). Qed.
Lemma lem1640323 (x : real) (m : nat) : (term26 x m) = (term2 x m).
Proof. exact (fun_ext (fun n : nat => @lem1640322 x m n)). Qed.
Lemma lem1640324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1640325 (x : real) (m : nat) : (term27 x m) = (term28 x m).
Proof. exact (MK_COMB (@lem1640324) (@lem1640323 x m)). Qed.
Lemma lem1640326 (x : real) (m : nat) : (term1 x m) = (term29 x m).
Proof. exact (MK_COMB (@lem1640321 x m) (@lem1640325 x m)). Qed.
Lemma lem1640327 (x : real) (m : nat) : term29 x m.
Proof. exact (EQ_MP (@lem1640326 x m) (@lem1640307 x m)). Qed.
Lemma lem1640338 : term30.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1640364 : term31.
Proof. exact (proj1 (@lem1640338)). Qed.
Lemma lem1640365 (m : nat) : term32 m.
Proof. exact (@lem1640364 m). Qed.
Lemma lem1640366 (m : nat) : (term32 m) = ((term33 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1640380 (x : real) : (term34 x) = term35.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1640381 (x : real) (m : nat) : (term4 x m) = term35.
Proof. exact (@lem1640380 (real_pow x m)). Qed.
Lemma lem1640382 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1640383 (x : real) (m : nat) : (term36 x m) = term37.
Proof. exact (MK_COMB (@lem1640382) (@lem1640381 x m)). Qed.
Lemma lem1640385 (m : nat) : (term33 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1640366 m) (@lem1640365 m)). Qed.
Lemma lem1640386 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1640387 (m : nat) (x : real) : (term5 x m) = (term34 x).
Proof. exact (MK_COMB (@lem1640386 x) (@lem1640385 m)). Qed.
Lemma lem1640389 (x : real) : (term34 x) = term35.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1640390 (x : real) (m : nat) : (term5 x m) = term35.
Proof. exact (TRANS (@lem1640387 m x) (@lem1640389 x)). Qed.
Lemma lem1640391 (x : real) (m : nat) : ((term4 x m) = (term5 x m)) = (term35 = term35).
Proof. exact (MK_COMB (@lem1640383 x m) (@lem1640390 x m)). Qed.
Lemma lem1640393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1640394 (x : real) : (x = x) = True.
Proof. exact (@lem1640393 real x). Qed.
Lemma lem1640395 : (term35 = term35) = True.
Proof. exact (@lem1640394 term35). Qed.
Lemma lem1640396 (x : real) (m : nat) : ((term4 x m) = (term5 x m)) = True.
Proof. exact (TRANS (@lem1640391 x m) (@lem1640395)). Qed.
Lemma lem1640397 (x : real) (m : nat) : True = ((term4 x m) = (term5 x m)).
Proof. exact (SYM (@lem1640396 x m)). Qed.
Lemma lem1640398 (x : real) (m : nat) : (term4 x m) = (term5 x m).
Proof. exact (EQ_MP (@lem1640397 x m) (@lem0)). Qed.
Lemma lem1640399 (x : real) : term38 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem1640400 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1640401 (x : real) : term39 x.
Proof. exact (EQ_MP (@lem1640400 x) (@lem1640399 x)). Qed.
Lemma lem1640402 (x : real) (m : nat) : term40 x m.
Proof. exact (@lem1640401 x m). Qed.
Lemma lem1640403 (m : nat) (x : real) : (term40 x m) = (term41 m x).
Proof. exact (eq_refl (term40 x m)). Qed.
Lemma lem1640404 (m : nat) (x : real) : term41 m x.
Proof. exact (EQ_MP (@lem1640403 m x) (@lem1640402 x m)). Qed.
Lemma lem1640405 (m : nat) (x : real) (n : nat) : term42 m x n.
Proof. exact (@lem1640404 m x n). Qed.
Lemma lem1640406 (m : nat) (x : real) (n : nat) : (term42 m x n) = ((term43 x m n) = (term44 m x n)).
Proof. exact (eq_refl (term42 m x n)). Qed.
Lemma lem1640408 : term30.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1640409 : term45.
Proof. exact (proj2 (@lem1640408)). Qed.
Lemma lem1640410 : term46.
Proof. exact (proj2 (@lem1640409)). Qed.
Lemma lem1640411 : term47.
Proof. exact (proj2 (@lem1640410)). Qed.
Lemma lem1640412 : term48.
Proof. exact (proj2 (@lem1640411)). Qed.
Lemma lem1640413 (m : nat) : term49 m.
Proof. exact (@lem1640412 m). Qed.
Lemma lem1640414 (m : nat) : (term49 m) = (term50 m).
Proof. exact (eq_refl (term49 m)). Qed.
Lemma lem1640415 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem1640414 m) (@lem1640413 m)). Qed.
Lemma lem1640416 (m : nat) (n : nat) : term51 m n.
Proof. exact (@lem1640415 m n). Qed.
Lemma lem1640417 (m : nat) (n : nat) : (term51 m n) = ((term52 m n) = (term53 m n)).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem1640442 (x : real) : term54 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1640443 (x : real) (n : nat) : term55 x n.
Proof. exact (@lem1640442 x n). Qed.
Lemma lem1640444 (x : real) (n : nat) : (term55 x n) = ((term56 x n) = (term57 x n)).
Proof. exact (eq_refl (term55 x n)). Qed.
Lemma lem1640450 (x : real) (n : nat) : (term56 x n) = (term57 x n).
Proof. exact (EQ_MP (@lem1640444 x n) (@lem1640443 x n)). Qed.
Lemma lem1640451 (x : real) (m : nat) (n : nat) : (term14 x m n) = (term58 x m n).
Proof. exact (@lem1640450 (real_pow x m) n). Qed.
Lemma lem1640453 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : (term9 x m n) = (term10 x m n).
Proof. exact (h1). Qed.
Lemma lem1640454 (x : real) (m : nat) : (term59 x m) = (term59 x m).
Proof. exact (eq_refl (term59 x m)). Qed.
Lemma lem1640455 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : (term58 x m n) = (term60 x m n).
Proof. exact (MK_COMB (@lem1640454 x m) (@lem1640453 x m n h1)). Qed.
Lemma lem1640456 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : (term14 x m n) = (term60 x m n).
Proof. exact (TRANS (@lem1640451 x m n) (@lem1640455 x m n h1)). Qed.
Lemma lem1640457 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1640458 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : (term61 x m n) = (term62 x m n).
Proof. exact (MK_COMB (@lem1640457) (@lem1640456 x m n h1)). Qed.
Lemma lem1640460 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (EQ_MP (@lem1640417 m n) (@lem1640416 m n)). Qed.
Lemma lem1640461 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1640462 (x : real) (m : nat) (n : nat) : (term15 x m n) = (term63 x m n).
Proof. exact (MK_COMB (@lem1640461 x) (@lem1640460 m n)). Qed.
Lemma lem1640464 (m : nat) (x : real) (n : nat) : (term43 x m n) = (term44 m x n).
Proof. exact (EQ_MP (@lem1640406 m x n) (@lem1640405 m x n)). Qed.
Lemma lem1640465 (x : real) (m : nat) (n : nat) : (term63 x m n) = (term60 x m n).
Proof. exact (@lem1640464 m x (Nat.mul m n)). Qed.
Lemma lem1640466 (x : real) (m : nat) (n : nat) : (term15 x m n) = (term60 x m n).
Proof. exact (TRANS (@lem1640462 x m n) (@lem1640465 x m n)). Qed.
Lemma lem1640467 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : ((term14 x m n) = (term15 x m n)) = ((term60 x m n) = (term60 x m n)).
Proof. exact (MK_COMB (@lem1640458 x m n h1) (@lem1640466 x m n)). Qed.
Lemma lem1640469 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1640470 (x : real) : (x = x) = True.
Proof. exact (@lem1640469 real x). Qed.
Lemma lem1640471 (x : real) (m : nat) (n : nat) : ((term60 x m n) = (term60 x m n)) = True.
Proof. exact (@lem1640470 (term60 x m n)). Qed.
Lemma lem1640472 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : ((term14 x m n) = (term15 x m n)) = True.
Proof. exact (TRANS (@lem1640467 x m n h1) (@lem1640471 x m n)). Qed.
Lemma lem1640473 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : True = ((term14 x m n) = (term15 x m n)).
Proof. exact (SYM (@lem1640472 x m n h1)). Qed.
Lemma lem1640474 (x : real) (m : nat) (n : nat) (h1 : (term9 x m n) = (term10 x m n)) : (term14 x m n) = (term15 x m n).
Proof. exact (EQ_MP (@lem1640473 x m n h1) (@lem0)). Qed.
Lemma lem1640475 (x : real) (m : nat) (n : nat) : term17 x m n.
Proof. exact (fun h0 : (term9 x m n) = (term10 x m n) => @lem1640474 x m n h0). Qed.
Lemma lem1640480 (x : real) (m : nat) : term21 x m.
Proof. exact (fun n : nat => @lem1640475 x m n). Qed.
Lemma lem1640481 (x : real) (m : nat) : term23 x m.
Proof. exact (conj (@lem1640398 x m) (@lem1640480 x m)). Qed.
Lemma lem1640482 (x : real) (m : nat) : term28 x m.
Proof. exact (@lem1640327 x m (@lem1640481 x m)). Qed.
Lemma lem1640487 (x : real) : term64 x.
Proof. exact (fun m : nat => @lem1640482 x m). Qed.
Lemma lem1640492 : term65.
Proof. exact (fun x : real => @lem1640487 x). Qed.
