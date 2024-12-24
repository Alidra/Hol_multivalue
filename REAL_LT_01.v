Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_01_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1367247_spec.
Require Import thm1386578_spec.
Require Import thm1483448_spec.
Require Import thm1483519_spec.
Require Import thm1483531_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1499332 : term0 = term1.
Proof. exact (@lem1483531 term2 term3). Qed.
Lemma lem1499338 : term4 = term5.
Proof. exact (@lem1483519 term2 term3). Qed.
Lemma lem1499340 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1499341 : term8 = term9.
Proof. exact (@lem1499340 term10 term10). Qed.
Lemma lem1499342 : (term11 = (BIT1 0)) = (term12 = term10).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1499343 : term12 = term10.
Proof. exact (EQ_MP (@lem1499342) (@lem940073)). Qed.
Lemma lem1499344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1499345 : term13 = term3.
Proof. exact (MK_COMB (@lem1499344) (@lem1499343)). Qed.
Lemma lem1499346 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1499347 : term9 = term14.
Proof. exact (MK_COMB (@lem1499346) (@lem1499345)). Qed.
Lemma lem1499348 : term8 = term14.
Proof. exact (TRANS (@lem1499341) (@lem1499347)). Qed.
Lemma lem1499349 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1499350 : term5 = term16.
Proof. exact (MK_COMB (@lem1499349) (@lem1499348)). Qed.
Lemma lem1499351 : term16 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1499352 : term5 = term14.
Proof. exact (TRANS (@lem1499350) (@lem1499351)). Qed.
Lemma lem1499354 : term4 = term14.
Proof. exact (TRANS (@lem1499338) (@lem1499352)). Qed.
Lemma lem1499355 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1499356 : term17 = term18.
Proof. exact (MK_COMB (@lem1499355) (@lem1499354)). Qed.
Lemma lem1499357 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1499358 : term1 = term19.
Proof. exact (MK_COMB (@lem1499356) (@lem1499357)). Qed.
Lemma lem1499368 : term0 = term19.
Proof. exact (TRANS (@lem1499332) (@lem1499358)). Qed.
Lemma lem1499372 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1499374 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1499375 : term19 = term22.
Proof. exact (@lem1499374 term10 (NUMERAL 0)). Qed.
Lemma lem1499376 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1499377 : term23 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1499378 (h1 : term23 = (BIT1 0)) : (term10 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1499379 : (term23 = (BIT1 0)) = ((term10 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term23 = (BIT1 0) => @lem1499378 h1) (fun h1 : (term10 = (NUMERAL 0)) = False => @lem1499377)). Qed.
Lemma lem1499380 : (term10 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1499379) (@lem1499377)). Qed.
Lemma lem1499381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1499382 : term24 = (and False).
Proof. exact (MK_COMB (@lem1499381) (@lem1499380)). Qed.
Lemma lem1499383 : term22 = (False /\ True).
Proof. exact (MK_COMB (@lem1499382) (@lem1499376)). Qed.
Lemma lem1499385 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1499386 : term22 = False.
Proof. exact (TRANS (@lem1499383) (@lem1499385)). Qed.
Lemma lem1499387 : term19 = False.
Proof. exact (TRANS (@lem1499375) (@lem1499386)). Qed.
Lemma lem1499388 (h1 : term19) : False.
Proof. exact (EQ_MP (@lem1499387) (@lem1499372 h1)). Qed.
Lemma lem1499390 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1499391 (h1 : term19) : term19 = False.
Proof. exact (prop_ext (fun h2 : term19 => @lem1499388 h1) (fun h2 : False => @lem1499390 h1)). Qed.
Lemma lem1499392 (h1 : term19) : False.
Proof. exact (EQ_MP (@lem1499391 h1) (@lem1499390 h1)). Qed.
Lemma lem1499393 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1499394 (h1 : term0) : term19.
Proof. exact (EQ_MP (@lem1499368) (@lem1499393 h1)). Qed.
Lemma lem1499395 (h1 : term0) : term19 = False.
Proof. exact (prop_ext (fun h2 : term19 => @lem1499392 h2) (fun h2 : False => @lem1499394 h1)). Qed.
Lemma lem1499396 (h1 : term0) : False.
Proof. exact (EQ_MP (@lem1499395 h1) (@lem1499394 h1)). Qed.
Lemma lem1499397 : term25.
Proof. exact (fun h0 : term0 => @lem1499396 h0). Qed.
Lemma lem1499398 : term26.
Proof. exact (@lem1386578 term27). Qed.
Lemma lem1499399 : term27.
Proof. exact (@lem1499398 (@lem1499397)). Qed.
