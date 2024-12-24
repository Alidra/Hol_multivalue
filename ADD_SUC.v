Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SUC_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm77238_spec.
Lemma lem77334 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem77335 : term1.
Proof. exact (@lem77334 term2). Qed.
Lemma lem77336 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem77337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77338 : term5 = term6.
Proof. exact (MK_COMB (@lem77337) (@lem77336)). Qed.
Lemma lem77339 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77341 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem77340) (@lem77339 m)). Qed.
Lemma lem77342 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem77343 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem77341 m) (@lem77342 m)). Qed.
Lemma lem77344 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem77343 m)). Qed.
Lemma lem77345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77346 : term17 = term18.
Proof. exact (MK_COMB (@lem77345) (@lem77344)). Qed.
Lemma lem77347 : term19 = term20.
Proof. exact (MK_COMB (@lem77338) (@lem77346)). Qed.
Lemma lem77348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77349 : term21 = term22.
Proof. exact (MK_COMB (@lem77348) (@lem77347)). Qed.
Lemma lem77350 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77351 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem77350 m)). Qed.
Lemma lem77352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77353 : term24 = term25.
Proof. exact (MK_COMB (@lem77352) (@lem77351)). Qed.
Lemma lem77354 : term1 = term26.
Proof. exact (MK_COMB (@lem77349) (@lem77353)). Qed.
Lemma lem77355 : term26.
Proof. exact (EQ_MP (@lem77354) (@lem77335)). Qed.
Lemma lem77356 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem77364 : term27.
Proof. exact (proj1 (@lem77238)). Qed.
Lemma lem77365 (n : nat) : term28 n.
Proof. exact (@lem77364 n). Qed.
Lemma lem77366 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem77375 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem77366 n) (@lem77365 n)). Qed.
Lemma lem77376 (n : nat) : (term30 n) = (S n).
Proof. exact (@lem77375 (S n)). Qed.
Lemma lem77377 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77378 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem77377) (@lem77376 n)). Qed.
Lemma lem77380 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem77366 n) (@lem77365 n)). Qed.
Lemma lem77381 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77382 (n : nat) : (term33 n) = (S n).
Proof. exact (MK_COMB (@lem77381) (@lem77380 n)). Qed.
Lemma lem77383 (n : nat) : ((term30 n) = (term33 n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem77378 n) (@lem77382 n)). Qed.
Lemma lem77385 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77386 (x : nat) : (x = x) = True.
Proof. exact (@lem77385 nat x). Qed.
Lemma lem77387 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem77386 (S n)). Qed.
Lemma lem77388 (n : nat) : ((term30 n) = (term33 n)) = True.
Proof. exact (TRANS (@lem77383 n) (@lem77387 n)). Qed.
Lemma lem77389 : term34 = term35.
Proof. exact (fun_ext (fun n : nat => @lem77388 n)). Qed.
Lemma lem77390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77391 : term4 = term36.
Proof. exact (MK_COMB (@lem77390) (@lem77389)). Qed.
Lemma lem77393 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77394 (t : Prop) : (term38 t) = t.
Proof. exact (@lem77393 nat t). Qed.
Lemma lem77395 : term36 = True.
Proof. exact (@lem77394 True). Qed.
Lemma lem77396 : term4 = True.
Proof. exact (TRANS (@lem77391) (@lem77395)). Qed.
Lemma lem77397 : True = term4.
Proof. exact (SYM (@lem77396)). Qed.
Lemma lem77398 : term4.
Proof. exact (EQ_MP (@lem77397) (@lem0)). Qed.
Lemma lem77399 : term39.
Proof. exact (proj2 (@lem77238)). Qed.
Lemma lem77400 (m : nat) : term40 m.
Proof. exact (@lem77399 m). Qed.
Lemma lem77401 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem77402 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem77401 m) (@lem77400 m)). Qed.
Lemma lem77403 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem77402 m n). Qed.
Lemma lem77404 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem77410 (n : nat) (m : nat) (h1 : term8 m) : term45 m n.
Proof. exact (@lem77356 m h1 n). Qed.
Lemma lem77411 (m : nat) (n : nat) : (term45 m n) = ((term46 m n) = (term44 m n)).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem77420 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem77404 m n) (@lem77403 m n)). Qed.
Lemma lem77421 (m : nat) (n : nat) : (term47 m n) = (term48 m n).
Proof. exact (@lem77420 m (S n)). Qed.
Lemma lem77423 (n : nat) (m : nat) (h1 : term8 m) : (term46 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem77411 m n) (@lem77410 n m h1)). Qed.
Lemma lem77424 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77425 (n : nat) (m : nat) (h1 : term8 m) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem77424) (@lem77423 n m h1)). Qed.
Lemma lem77426 (n : nat) (m : nat) (h1 : term8 m) : (term47 m n) = (term49 m n).
Proof. exact (TRANS (@lem77421 m n) (@lem77425 n m h1)). Qed.
Lemma lem77427 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77428 (n : nat) (m : nat) (h1 : term8 m) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem77427) (@lem77426 n m h1)). Qed.
Lemma lem77430 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem77404 m n) (@lem77403 m n)). Qed.
Lemma lem77431 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77432 (m : nat) (n : nat) : (term52 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem77431) (@lem77430 m n)). Qed.
Lemma lem77433 (n : nat) (m : nat) (h1 : term8 m) : ((term47 m n) = (term52 m n)) = ((term49 m n) = (term49 m n)).
Proof. exact (MK_COMB (@lem77428 n m h1) (@lem77432 m n)). Qed.
Lemma lem77435 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77436 (x : nat) : (x = x) = True.
Proof. exact (@lem77435 nat x). Qed.
Lemma lem77437 (m : nat) (n : nat) : ((term49 m n) = (term49 m n)) = True.
Proof. exact (@lem77436 (term49 m n)). Qed.
Lemma lem77438 (n : nat) (m : nat) (h1 : term8 m) : ((term47 m n) = (term52 m n)) = True.
Proof. exact (TRANS (@lem77433 n m h1) (@lem77437 m n)). Qed.
Lemma lem77439 (m : nat) (h1 : term8 m) : (term53 m) = term35.
Proof. exact (fun_ext (fun n : nat => @lem77438 n m h1)). Qed.
Lemma lem77440 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77441 (m : nat) (h1 : term8 m) : (term12 m) = term36.
Proof. exact (MK_COMB (@lem77440) (@lem77439 m h1)). Qed.
Lemma lem77443 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77444 (t : Prop) : (term38 t) = t.
Proof. exact (@lem77443 nat t). Qed.
Lemma lem77445 : term36 = True.
Proof. exact (@lem77444 True). Qed.
Lemma lem77446 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem77441 m h1) (@lem77445)). Qed.
Lemma lem77447 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem77446 m h1)). Qed.
Lemma lem77448 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem77447 m h1) (@lem0)). Qed.
Lemma lem77449 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem77448 m h0). Qed.
Lemma lem77454 : term18.
Proof. exact (fun m : nat => @lem77449 m). Qed.
Lemma lem77455 : term20.
Proof. exact (conj (@lem77398) (@lem77454)). Qed.
Lemma lem77456 : term25.
Proof. exact (@lem77355 (@lem77455)). Qed.
