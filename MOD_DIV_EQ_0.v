Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_DIV_EQ_0_term_abbrevs.
Require Import IMP_CONJ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm163281_spec.
Require Import thm165614_spec.
Require Import thm1842_spec.
Require Import thm196345_spec.
Require Import thm196348_spec.
Require Import thm37_spec.
Require Import thm43_spec.
Require Import thm43208_spec.
Require Import thm51_spec.
Require Import thm7315_spec.
Require Import thm82_spec.
Require Import thm892_spec.
Lemma lem196352 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem196354 : term1.
Proof. exact (EQ_MP (@lem196348) (@lem196345)). Qed.
Lemma lem196356 : term2.
Proof. exact (EQ_MP (@lem163281) (@lem165614)). Qed.
Lemma lem196357 (m : nat) : term3 m.
Proof. exact (@lem196356 m). Qed.
Lemma lem196358 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem196359 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem196358 m) (@lem196357 m)). Qed.
Lemma lem196360 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem196359 m n). Qed.
Lemma lem196361 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term0 n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem196363 (m : nat) : term7 m.
Proof. exact (@lem196354 m). Qed.
Lemma lem196364 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem196365 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem196364 m) (@lem196363 m)). Qed.
Lemma lem196366 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem196365 m n). Qed.
Lemma lem196367 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem196369 (n : nat) : term11 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem196372 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem196367 m n) (@lem196366 m n)). Qed.
Lemma lem196375 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem196372 (Nat.modulo m n) n). Qed.
Lemma lem196376 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem196377 (m : nat) (n : nat) (h1 : term0 n) : ((term13 m n) = (NUMERAL 0)) = (term6 m n).
Proof. exact (@lem196375 m n (@lem196376 n h1)). Qed.
Lemma lem196378 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem43 (term6 m n) ((term13 m n) = (NUMERAL 0))). Qed.
Lemma lem196379 (m : nat) (n : nat) (h1 : term0 n) : term15 m n.
Proof. exact (@lem196378 m n (@lem196377 m n h1)). Qed.
Lemma lem196382 (m : nat) (n : nat) (h1 : term6 m n) : term6 m n.
Proof. exact (h1). Qed.
Lemma lem196383 (m : nat) (n : nat) (h1 : term0 n) (h2 : term6 m n) : (term13 m n) = (NUMERAL 0).
Proof. exact (@lem196379 m n h1 (@lem196382 m n h2)). Qed.
Lemma lem196384 (m : nat) (n : nat) (h1 : term6 m n) : term16 m n.
Proof. exact (fun h0 : term0 n => @lem196383 m n h0 h1). Qed.
Lemma lem196385 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun h0 : term6 m n => @lem196384 m n h0). Qed.
Lemma lem196387 (p : Prop) (q : Prop) (r : Prop) : (term18 p q r) = (term19 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem196388 (m : nat) (n : nat) : (term17 m n) = (term20 m n).
Proof. exact (@lem196387 (term6 m n) (term0 n) ((term13 m n) = (NUMERAL 0))). Qed.
Lemma lem196389 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem196388 m n) (@lem196385 m n)). Qed.
Lemma lem196391 (m : nat) (n : nat) : (term6 m n) = (term0 n).
Proof. exact (EQ_MP (@lem196361 m n) (@lem196360 m n)). Qed.
Lemma lem196393 (n : nat) (h1 : term0 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem196369 n (@lem196352 n h1)). Qed.
Lemma lem196394 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem196395 (n : nat) (h1 : term0 n) : (term0 n) = (~ False).
Proof. exact (MK_COMB (@lem196394) (@lem196393 n h1)). Qed.
Lemma lem196397 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem196398 (n : nat) (h1 : term0 n) : (term0 n) = True.
Proof. exact (TRANS (@lem196395 n h1) (@lem196397)). Qed.
Lemma lem196399 (m : nat) (n : nat) (h1 : term0 n) : (term6 m n) = True.
Proof. exact (TRANS (@lem196391 m n) (@lem196398 n h1)). Qed.
Lemma lem196400 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem43 True (term6 m n)). Qed.
Lemma lem196401 (m : nat) (n : nat) (h1 : term0 n) : term22 m n.
Proof. exact (@lem196400 m n (@lem196399 m n h1)). Qed.
Lemma lem196404 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem196405 (m : nat) (n : nat) (h1 : True) (h2 : term0 n) : term6 m n.
Proof. exact (@lem196401 m n h2 (@lem196404 h1)). Qed.
Lemma lem196406 (m : nat) (n : nat) (h1 : term0 n) : term22 m n.
Proof. exact (fun h0 : True => @lem196405 m n h0 h1). Qed.
Lemma lem196408 (n : nat) (h1 : term0 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem196369 n (@lem196352 n h1)). Qed.
Lemma lem196411 (n : nat) : term23 n.
Proof. exact (@lem37 (n = (NUMERAL 0)) False). Qed.
Lemma lem196412 (n : nat) (h1 : term0 n) : term24 n.
Proof. exact (@lem196411 n (@lem196408 n h1)). Qed.
Lemma lem196413 (n : nat) : term25 n.
Proof. exact (@lem7315 False (n = (NUMERAL 0))). Qed.
Lemma lem196414 (n : nat) (h1 : term0 n) : term26 n.
Proof. exact (@lem196413 n (@lem196412 n h1)). Qed.
Lemma lem196416 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem196417 : term27.
Proof. exact (@lem43 True (~ False)). Qed.
Lemma lem196418 : term28.
Proof. exact (@lem196417 (@lem196416)). Qed.
Lemma lem196421 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem196422 (h1 : True) : ~ False.
Proof. exact (@lem196418 (@lem196421 h1)). Qed.
Lemma lem196423 : term28.
Proof. exact (fun h0 : True => @lem196422 h0). Qed.
Lemma lem196424 (n : nat) : term29 n.
Proof. exact (@lem51 (~ False) True (term0 n)). Qed.
Lemma lem196425 (n : nat) : term30 n.
Proof. exact (@lem196424 n (@lem196423)). Qed.
Lemma lem196426 (n : nat) (h1 : term0 n) : term31 n.
Proof. exact (@lem196425 n (@lem196414 n h1)). Qed.
Lemma lem196427 (n : nat) (h1 : term0 n) : term32 n.
Proof. exact (fun h0 : True => @lem196426 n h1). Qed.
Lemma lem196428 (m : nat) (n : nat) (h1 : term0 n) : term33 m n.
Proof. exact (conj (@lem196406 m n h1) (@lem196427 n h1)). Qed.
Lemma lem196429 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem43208 True True (term6 m n) (term0 n)). Qed.
Lemma lem196430 (m : nat) (n : nat) (h1 : term0 n) : term35 m n.
Proof. exact (@lem196429 m n (@lem196428 m n h1)). Qed.
Lemma lem196432 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem196433 : (True /\ True) = True.
Proof. exact (@lem196432 True). Qed.
Lemma lem196434 : term36.
Proof. exact (@lem43 True (True /\ True)). Qed.
Lemma lem196435 : term37.
Proof. exact (@lem196434 (@lem196433)). Qed.
Lemma lem196438 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem196439 (h1 : True) : True /\ True.
Proof. exact (@lem196435 (@lem196438 h1)). Qed.
Lemma lem196440 : term37.
Proof. exact (fun h0 : True => @lem196439 h0). Qed.
Lemma lem196441 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem51 (True /\ True) True (term39 m n)). Qed.
Lemma lem196442 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem196441 m n (@lem196440)). Qed.
Lemma lem196443 (m : nat) (n : nat) (h1 : term0 n) : term41 m n.
Proof. exact (@lem196442 m n (@lem196430 m n h1)). Qed.
Lemma lem196444 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem51 (term39 m n) True ((term13 m n) = (NUMERAL 0))). Qed.
Lemma lem196445 (m : nat) (n : nat) (h1 : term0 n) : term43 m n.
Proof. exact (@lem196444 m n (@lem196443 m n h1)). Qed.
Lemma lem196446 (m : nat) (n : nat) (h1 : term0 n) : term44 m n.
Proof. exact (@lem196445 m n h1 (@lem196389 m n)). Qed.
Lemma lem196447 (m : nat) (n : nat) (h1 : term44 m n) : term44 m n.
Proof. exact (h1). Qed.
Lemma lem196448 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem196449 (m : nat) (n : nat) (h1 : True) (h2 : term44 m n) : (term13 m n) = (NUMERAL 0).
Proof. exact (@lem196447 m n h2 (@lem196448 h1)). Qed.
Lemma lem196450 (m : nat) (n : nat) (h1 : True) : term45 m n.
Proof. exact (fun h0 : term44 m n => @lem196449 m n h1 h0). Qed.
Lemma lem196451 (m : nat) (n : nat) (h1 : term44 m n) : term44 m n.
Proof. exact (h1). Qed.
Lemma lem196452 (m : nat) (n : nat) (h1 : True) (h2 : term44 m n) : (term13 m n) = (NUMERAL 0).
Proof. exact (@lem196450 m n h1 (@lem196451 m n h2)). Qed.
Lemma lem196453 (m : nat) (n : nat) (h1 : term44 m n) : term44 m n.
Proof. exact (fun h0 : True => @lem196452 m n h0 h1). Qed.
Lemma lem196454 (m : nat) (n : nat) : term46 m n.
Proof. exact (fun h0 : term44 m n => @lem196453 m n h0). Qed.
Lemma lem196457 (m : nat) (n : nat) (h1 : term0 n) : term44 m n.
Proof. exact (@lem196454 m n (@lem196446 m n h1)). Qed.
Lemma lem196458 (m : nat) (n : nat) (h1 : term0 n) : (term13 m n) = (NUMERAL 0).
Proof. exact (@lem196457 m n h1 (@lem0)). Qed.
Lemma lem196459 (m : nat) (n : nat) : term16 m n.
Proof. exact (fun h0 : term0 n => @lem196458 m n h0). Qed.
Lemma lem196464 (m : nat) : term47 m.
Proof. exact (fun n : nat => @lem196459 m n). Qed.
Lemma lem196469 : term48.
Proof. exact (fun m : nat => @lem196464 m). Qed.
