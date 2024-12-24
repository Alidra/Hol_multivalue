Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_spec.
Require Import FINITE_RULES_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUBSET_EMPTY_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3596306 {A : Type'} (x : A) (t : A -> Prop) : term0 A x t.
Proof. exact (@lem9784 (@IN A x t)). Qed.
Lemma lem3596307 {A : Type'} (x : A) (t : A -> Prop) : (term0 A x t) = (term1 A x t).
Proof. exact (eq_refl (term0 A x t)). Qed.
Lemma lem3596308 {A : Type'} (x : A) (t : A -> Prop) : term1 A x t.
Proof. exact (EQ_MP (@lem3596307 A x t) (@lem3596306 A x t)). Qed.
Lemma lem3596309 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3596310 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : term2 A x t.
Proof. exact (h1). Qed.
Lemma lem3596321 {A : Type'} : term3 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem3596322 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3596323 {A : Type'} (x : A) (h1 : term3 A) : term4 A x.
Proof. exact (@lem3596322 A h1 x). Qed.
Lemma lem3596324 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3596325 {A : Type'} (x : A) (h1 : term3 A) : term5 A x.
Proof. exact (EQ_MP (@lem3596324 A x) (@lem3596323 A x h1)). Qed.
Lemma lem3596326 {A : Type'} (x : A) (s : A -> Prop) (h1 : term3 A) : term6 A x s.
Proof. exact (@lem3596325 A x h1 s). Qed.
Lemma lem3596327 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (term7 A x s).
Proof. exact (eq_refl (term6 A x s)). Qed.
Lemma lem3596328 {A : Type'} (x : A) (s : A -> Prop) (h1 : term3 A) : term7 A x s.
Proof. exact (EQ_MP (@lem3596327 A x s) (@lem3596326 A x s h1)). Qed.
Lemma lem3596329 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3596330 {A : Type'} (x : A) (s : A -> Prop) (h1 : term3 A) (h2 : @FINITE A s) : term8 A x s.
Proof. exact (@lem3596328 A x s h1 (@lem3596329 A s h2)). Qed.
Lemma lem3596331 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term9 A x s.
Proof. exact (fun h0 : term3 A => @lem3596330 A x s h0 h1). Qed.
Lemma lem3596332 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3596333 {A : Type'} (x : A) (s : A -> Prop) (h1 : term3 A) (h2 : @FINITE A s) : term8 A x s.
Proof. exact (@lem3596331 A x s h2 (@lem3596332 A h1)). Qed.
Lemma lem3596334 {A : Type'} (x : A) (s : A -> Prop) (h1 : term3 A) : term7 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3596333 A x s h1 h0). Qed.
Lemma lem3596335 {A : Type'} (x : A) (h1 : term3 A) : term5 A x.
Proof. exact (fun s : A -> Prop => @lem3596334 A x s h1). Qed.
Lemma lem3596336 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun x : A => @lem3596335 A x h1). Qed.
Lemma lem3596337 {A : Type'} : term10 A.
Proof. exact (fun h0 : term3 A => @lem3596336 A h0). Qed.
Lemma lem3596338 {A : Type'} : term3 A.
Proof. exact (@lem3596337 A (@lem3596321 A)). Qed.
Lemma lem3596339 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3596338 A x). Qed.
Lemma lem3596340 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3596341 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem3596340 A x) (@lem3596339 A x)). Qed.
Lemma lem3596342 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (@lem3596341 A x s). Qed.
Lemma lem3596343 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (term7 A x s).
Proof. exact (eq_refl (term6 A x s)). Qed.
Lemma lem3596355 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3596356 {A : Type'} (FINITE' : type686 A) (h1 : term11 A) : term12 A FINITE'.
Proof. exact (@lem3596355 A h1 FINITE'). Qed.
Lemma lem3596357 {A : Type'} (FINITE' : type686 A) : (term12 A FINITE') = (term13 A FINITE').
Proof. exact (eq_refl (term12 A FINITE')). Qed.
Lemma lem3596358 {A : Type'} (FINITE' : type686 A) (h1 : term11 A) : term13 A FINITE'.
Proof. exact (EQ_MP (@lem3596357 A FINITE') (@lem3596356 A FINITE' h1)). Qed.
Lemma lem3596359 {A : Type'} (FINITE' : type686 A) (h1 : term14 A FINITE') : term14 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3596360 {A : Type'} (FINITE' : type686 A) (h1 : term11 A) (h2 : term14 A FINITE') : term15 A FINITE'.
Proof. exact (@lem3596358 A FINITE' h1 (@lem3596359 A FINITE' h2)). Qed.
Lemma lem3596361 {A : Type'} (FINITE' : type686 A) (h1 : term14 A FINITE') : term16 A FINITE'.
Proof. exact (fun h0 : term11 A => @lem3596360 A FINITE' h0 h1). Qed.
Lemma lem3596362 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3596363 {A : Type'} (FINITE' : type686 A) (h1 : term11 A) (h2 : term14 A FINITE') : term15 A FINITE'.
Proof. exact (@lem3596361 A FINITE' h2 (@lem3596362 A h1)). Qed.
Lemma lem3596364 {A : Type'} (FINITE' : type686 A) (h1 : term11 A) : term13 A FINITE'.
Proof. exact (fun h0 : term14 A FINITE' => @lem3596363 A FINITE' h1 h0). Qed.
Lemma lem3596365 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (fun FINITE' : type686 A => @lem3596364 A FINITE' h1). Qed.
Lemma lem3596366 {A : Type'} : term17 A.
Proof. exact (fun h0 : term11 A => @lem3596365 A h0). Qed.
Lemma lem3596367 {A : Type'} : term11 A.
Proof. exact (@lem3596366 A (@lem3197567 A)). Qed.
Lemma lem3596368 {A : Type'} (FINITE' : type686 A) : term12 A FINITE'.
Proof. exact (@lem3596367 A FINITE'). Qed.
Lemma lem3596369 {A : Type'} (FINITE' : type686 A) : (term12 A FINITE') = (term13 A FINITE').
Proof. exact (eq_refl (term12 A FINITE')). Qed.
Lemma lem3596371 {A : Type'} (P : Prop) : term18 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3596372 {A : Type'} (P : Prop) : (term18 A P) = (term19 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem3596373 {A : Type'} (P : Prop) : term19 A P.
Proof. exact (EQ_MP (@lem3596372 A P) (@lem3596371 A P)). Qed.
Lemma lem3596374 {A : Type'} (P : Prop) (Q : A -> Prop) : term20 A P Q.
Proof. exact (@lem3596373 A P Q). Qed.
Lemma lem3596375 {A : Type'} (P : Prop) (Q : A -> Prop) : (term20 A P Q) = ((term21 A P Q) = (term22 A P Q)).
Proof. exact (eq_refl (term20 A P Q)). Qed.
Lemma lem3596377 {A B : Type'} (P : type1413 A B) : term23 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem3596378 {A B : Type'} (P : type1413 A B) : (term23 A B P) = ((term24 A B P) = (term25 A B P)).
Proof. exact (eq_refl (term23 A B P)). Qed.
Lemma lem3596381 {A B : Type'} (P : type1413 A B) : (term24 A B P) = (term25 A B P).
Proof. exact (EQ_MP (@lem3596378 A B P) (@lem3596377 A B P)). Qed.
Lemma lem3596382 {A : Type'} (P : type639 A) : (term26 A P) = (term27 A P).
Proof. exact (@lem3596381 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3596383 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (@lem3596382 A (term30 A)). Qed.
Lemma lem3596384 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (eq_refl (term31 A s)). Qed.
Lemma lem3596385 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3596386 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3596384 A s) (@lem3596385 A t)). Qed.
Lemma lem3596387 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term34 A s t) = (term35 A t s).
Proof. exact (eq_refl (term34 A s t)). Qed.
Lemma lem3596388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A s t) = (term35 A t s).
Proof. exact (TRANS (@lem3596386 A s t) (@lem3596387 A t s)). Qed.
Lemma lem3596389 {A : Type'} (s : A -> Prop) : (term36 A s) = (term32 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3596388 A t s)). Qed.
Lemma lem3596390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596391 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3596390 A) (@lem3596389 A s)). Qed.
Lemma lem3596392 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596391 A s)). Qed.
Lemma lem3596393 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596394 {A : Type'} : (term28 A) = (term41 A).
Proof. exact (MK_COMB (@lem3596393 A) (@lem3596392 A)). Qed.
Lemma lem3596395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3596396 {A : Type'} : (term42 A) = (term43 A).
Proof. exact (MK_COMB (@lem3596395) (@lem3596394 A)). Qed.
Lemma lem3596397 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (eq_refl (term31 A s)). Qed.
Lemma lem3596398 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3596399 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3596397 A s) (@lem3596398 A t)). Qed.
Lemma lem3596400 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term34 A s t) = (term35 A t s).
Proof. exact (eq_refl (term34 A s t)). Qed.
Lemma lem3596401 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A s t) = (term35 A t s).
Proof. exact (TRANS (@lem3596399 A s t) (@lem3596400 A t s)). Qed.
Lemma lem3596402 {A : Type'} (t : A -> Prop) : (term44 A t) = (term45 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596401 A t s)). Qed.
Lemma lem3596403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596404 {A : Type'} (t : A -> Prop) : (term46 A t) = (term47 A t).
Proof. exact (MK_COMB (@lem3596403 A) (@lem3596402 A t)). Qed.
Lemma lem3596405 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3596404 A t)). Qed.
Lemma lem3596406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596407 {A : Type'} : (term29 A) = (term50 A).
Proof. exact (MK_COMB (@lem3596406 A) (@lem3596405 A)). Qed.
Lemma lem3596408 {A : Type'} : ((term28 A) = (term29 A)) = ((term41 A) = (term50 A)).
Proof. exact (MK_COMB (@lem3596396 A) (@lem3596407 A)). Qed.
Lemma lem3596409 {A : Type'} : (term41 A) = (term50 A).
Proof. exact (EQ_MP (@lem3596408 A) (@lem3596383 A)). Qed.
Lemma lem3596410 {A : Type'} : (term50 A) = (term41 A).
Proof. exact (SYM (@lem3596409 A)). Qed.
Lemma lem3596420 (p : Prop) (q : Prop) (r : Prop) : (term51 p q r) = (term52 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3596421 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term35 A t s) = (term53 A t s).
Proof. exact (@lem3596420 (@FINITE A t) (@SUBSET A s t) (@FINITE A s)). Qed.
Lemma lem3596426 {A : Type'} (t : A -> Prop) : (term45 A t) = (term54 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596421 A t s)). Qed.
Lemma lem3596427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596428 {A : Type'} (t : A -> Prop) : (term47 A t) = (term55 A t).
Proof. exact (MK_COMB (@lem3596427 A) (@lem3596426 A t)). Qed.
Lemma lem3596433 {A : Type'} : (term49 A) = (term56 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3596428 A t)). Qed.
Lemma lem3596434 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596435 {A : Type'} : (term50 A) = (term57 A).
Proof. exact (MK_COMB (@lem3596434 A) (@lem3596433 A)). Qed.
Lemma lem3596440 {A : Type'} : (term57 A) = (term50 A).
Proof. exact (SYM (@lem3596435 A)). Qed.
Lemma lem3596446 {A : Type'} (P : Prop) (Q : A -> Prop) : (term21 A P Q) = (term22 A P Q).
Proof. exact (EQ_MP (@lem3596375 A P Q) (@lem3596374 A P Q)). Qed.
Lemma lem3596447 {A : Type'} (P : Prop) (Q : type686 A) : (term58 A P Q) = (term59 A P Q).
Proof. exact (@lem3596446 (A -> Prop) P Q). Qed.
Lemma lem3596448 {A : Type'} (t : A -> Prop) : (term60 A t) = (term61 A t).
Proof. exact (@lem3596447 A (@FINITE A t) (term62 A t)). Qed.
Lemma lem3596449 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term64 A t s).
Proof. exact (eq_refl (term63 A t s)). Qed.
Lemma lem3596450 {A : Type'} (t : A -> Prop) : (term65 A t) = (term65 A t).
Proof. exact (eq_refl (term65 A t)). Qed.
Lemma lem3596451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term66 A t s) = (term53 A t s).
Proof. exact (MK_COMB (@lem3596450 A t) (@lem3596449 A t s)). Qed.
Lemma lem3596452 {A : Type'} (t : A -> Prop) : (term67 A t) = (term54 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596451 A t s)). Qed.
Lemma lem3596453 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596454 {A : Type'} (t : A -> Prop) : (term60 A t) = (term55 A t).
Proof. exact (MK_COMB (@lem3596453 A) (@lem3596452 A t)). Qed.
Lemma lem3596455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3596456 {A : Type'} (t : A -> Prop) : (term68 A t) = (term69 A t).
Proof. exact (MK_COMB (@lem3596455) (@lem3596454 A t)). Qed.
Lemma lem3596457 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term64 A t s).
Proof. exact (eq_refl (term63 A t s)). Qed.
Lemma lem3596458 {A : Type'} (t : A -> Prop) : (term70 A t) = (term62 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596457 A t s)). Qed.
Lemma lem3596459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596460 {A : Type'} (t : A -> Prop) : (term71 A t) = (term72 A t).
Proof. exact (MK_COMB (@lem3596459 A) (@lem3596458 A t)). Qed.
Lemma lem3596461 {A : Type'} (t : A -> Prop) : (term65 A t) = (term65 A t).
Proof. exact (eq_refl (term65 A t)). Qed.
Lemma lem3596462 {A : Type'} (t : A -> Prop) : (term61 A t) = (term73 A t).
Proof. exact (MK_COMB (@lem3596461 A t) (@lem3596460 A t)). Qed.
Lemma lem3596463 {A : Type'} (t : A -> Prop) : ((term60 A t) = (term61 A t)) = ((term55 A t) = (term73 A t)).
Proof. exact (MK_COMB (@lem3596456 A t) (@lem3596462 A t)). Qed.
Lemma lem3596464 {A : Type'} (t : A -> Prop) : (term55 A t) = (term73 A t).
Proof. exact (EQ_MP (@lem3596463 A t) (@lem3596448 A t)). Qed.
Lemma lem3596477 {A : Type'} : (term56 A) = (term74 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3596464 A t)). Qed.
Lemma lem3596478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596479 {A : Type'} : (term57 A) = (term75 A).
Proof. exact (MK_COMB (@lem3596478 A) (@lem3596477 A)). Qed.
Lemma lem3596504 {A : Type'} : (term75 A) = (term57 A).
Proof. exact (SYM (@lem3596479 A)). Qed.
Lemma lem3596506 {A : Type'} (FINITE' : type686 A) : term13 A FINITE'.
Proof. exact (EQ_MP (@lem3596369 A FINITE') (@lem3596368 A FINITE')). Qed.
Lemma lem3596507 {A : Type'} (FINITE' : type686 A) : term13 A FINITE'.
Proof. exact (@lem3596506 A FINITE'). Qed.
Lemma lem3596508 {A : Type'} : term76 A.
Proof. exact (@lem3596507 A (term77 A)). Qed.
Lemma lem3596509 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (eq_refl (term78 A)). Qed.
Lemma lem3596510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3596511 {A : Type'} : (term80 A) = (term81 A).
Proof. exact (MK_COMB (@lem3596510) (@lem3596509 A)). Qed.
Lemma lem3596512 {A : Type'} (s : A -> Prop) : (term82 A s) = (term72 A s).
Proof. exact (eq_refl (term82 A s)). Qed.
Lemma lem3596513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596514 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem3596513) (@lem3596512 A s)). Qed.
Lemma lem3596515 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term86 A x s).
Proof. exact (eq_refl (term85 A x s)). Qed.
Lemma lem3596516 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term88 A x s).
Proof. exact (MK_COMB (@lem3596514 A s) (@lem3596515 A x s)). Qed.
Lemma lem3596517 {A : Type'} (x : A) : (term89 A x) = (term90 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596516 A x s)). Qed.
Lemma lem3596518 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596519 {A : Type'} (x : A) : (term91 A x) = (term92 A x).
Proof. exact (MK_COMB (@lem3596518 A) (@lem3596517 A x)). Qed.
Lemma lem3596520 {A : Type'} : (term93 A) = (term94 A).
Proof. exact (fun_ext (fun x : A => @lem3596519 A x)). Qed.
Lemma lem3596521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3596522 {A : Type'} : (term95 A) = (term96 A).
Proof. exact (MK_COMB (@lem3596521 A) (@lem3596520 A)). Qed.
Lemma lem3596523 {A : Type'} : (term97 A) = (term98 A).
Proof. exact (MK_COMB (@lem3596511 A) (@lem3596522 A)). Qed.
Lemma lem3596524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596525 {A : Type'} : (term99 A) = (term100 A).
Proof. exact (MK_COMB (@lem3596524) (@lem3596523 A)). Qed.
Lemma lem3596526 {A : Type'} (t : A -> Prop) : (term82 A t) = (term72 A t).
Proof. exact (eq_refl (term82 A t)). Qed.
Lemma lem3596527 {A : Type'} (t : A -> Prop) : (term65 A t) = (term65 A t).
Proof. exact (eq_refl (term65 A t)). Qed.
Lemma lem3596528 {A : Type'} (t : A -> Prop) : (term101 A t) = (term73 A t).
Proof. exact (MK_COMB (@lem3596527 A t) (@lem3596526 A t)). Qed.
Lemma lem3596529 {A : Type'} : (term102 A) = (term74 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3596528 A t)). Qed.
Lemma lem3596530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596531 {A : Type'} : (term103 A) = (term75 A).
Proof. exact (MK_COMB (@lem3596530 A) (@lem3596529 A)). Qed.
Lemma lem3596532 {A : Type'} : (term76 A) = (term104 A).
Proof. exact (MK_COMB (@lem3596525 A) (@lem3596531 A)). Qed.
Lemma lem3596533 {A : Type'} : term104 A.
Proof. exact (EQ_MP (@lem3596532 A) (@lem3596508 A)). Qed.
Lemma lem3596535 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3596536 {A : Type'} : (term79 A) = (term106 A).
Proof. exact (@lem3596535 (term79 A)). Qed.
Lemma lem3596537 {A : Type'} : (term106 A) = (term79 A).
Proof. exact (SYM (@lem3596536 A)). Qed.
Lemma lem3596538 {A : Type'} (h1 : term107 A) : term107 A.
Proof. exact (h1). Qed.
Lemma lem3596539 {A : Type'} : term108 A.
Proof. exact (@lem3220121 A). Qed.
Lemma lem3596541 {A : Type'} : term109 A.
Proof. exact (@lem3197565 A). Qed.
Lemma lem3596545 {A : Type'} (h1 : term110 A) : term110 A.
Proof. exact (h1). Qed.
Lemma lem3596546 {A : Type'} : term111 A.
Proof. exact (fun h0 : term110 A => @lem3596545 A h0). Qed.
Lemma lem3596547 {A : Type'} (h1 : term111 A) : term111 A.
Proof. exact (h1). Qed.
Lemma lem3596548 {A : Type'} (h1 : term110 A) : term110 A.
Proof. exact (h1). Qed.
Lemma lem3596549 {A : Type'} (h1 : term110 A) (h2 : term111 A) : term110 A.
Proof. exact (@lem3596547 A h2 (@lem3596548 A h1)). Qed.
Lemma lem3596550 {A : Type'} (h1 : term110 A) : term112 A.
Proof. exact (fun h0 : term111 A => @lem3596549 A h1 h0). Qed.
Lemma lem3596551 {A : Type'} (h1 : term111 A) : term111 A.
Proof. exact (h1). Qed.
Lemma lem3596552 {A : Type'} (h1 : term110 A) (h2 : term111 A) : term110 A.
Proof. exact (@lem3596550 A h1 (@lem3596551 A h2)). Qed.
Lemma lem3596553 {A : Type'} (h1 : term111 A) : term111 A.
Proof. exact (fun h0 : term110 A => @lem3596552 A h0 h1). Qed.
Lemma lem3596554 {A : Type'} : term113 A.
Proof. exact (fun h0 : term111 A => @lem3596553 A h0). Qed.
Lemma lem3596557 {A : Type'} : term111 A.
Proof. exact (@lem3596554 A (@lem3596546 A)). Qed.
Lemma lem3596558 {A : Type'} : term111 A.
Proof. exact (@lem3596557 A). Qed.
Lemma lem3596582 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3596583 {A : Type'} : (term114 A) = (term115 A).
Proof. exact (@lem3596582 (term108 A)). Qed.
Lemma lem3596588 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (eq_refl (term116 A)). Qed.
Lemma lem3596589 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem3596588 A) (@lem3596583 A)). Qed.
Lemma lem3596592 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (eq_refl (term119 A)). Qed.
Lemma lem3596599 {A : Type'} : (term110 A) = (term120 A).
Proof. exact (MK_COMB (@lem3596592 A) (@lem3596589 A)). Qed.
Lemma lem3596604 {A : Type'} (s : A -> Prop) : ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A))) = ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A))).
Proof. exact (eq_refl ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A)))). Qed.
Lemma lem3596605 {A : Type'} : (term121 A) = (term121 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596604 A s)). Qed.
Lemma lem3596606 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596607 {A : Type'} : (term108 A) = (term108 A).
Proof. exact (MK_COMB (@lem3596606 A) (@lem3596605 A)). Qed.
Lemma lem3596608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3596609 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (MK_COMB (@lem3596608) (@lem3596607 A)). Qed.
Lemma lem3596614 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term7 A x s).
Proof. exact (eq_refl (term7 A x s)). Qed.
Lemma lem3596615 {A : Type'} (x : A) : (term122 A x) = (term122 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596614 A x s)). Qed.
Lemma lem3596616 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596617 {A : Type'} (x : A) : (term5 A x) = (term5 A x).
Proof. exact (MK_COMB (@lem3596616 A) (@lem3596615 A x)). Qed.
Lemma lem3596618 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (fun_ext (fun x : A => @lem3596617 A x)). Qed.
Lemma lem3596619 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3596620 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem3596619 A) (@lem3596618 A)). Qed.
Lemma lem3596623 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3596624 {A : Type'} : (term109 A) = (term109 A).
Proof. exact (MK_COMB (@lem3596623 A) (@lem3596620 A)). Qed.
Lemma lem3596625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596626 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem3596625) (@lem3596624 A)). Qed.
Lemma lem3596627 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem3596626 A) (@lem3596609 A)). Qed.
Lemma lem3596632 {A : Type'} (s : A -> Prop) : (term125 A s) = (term125 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem3596633 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596632 A s)). Qed.
Lemma lem3596634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596635 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (MK_COMB (@lem3596634 A) (@lem3596633 A)). Qed.
Lemma lem3596636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3596637 {A : Type'} : (term107 A) = (term107 A).
Proof. exact (MK_COMB (@lem3596636) (@lem3596635 A)). Qed.
Lemma lem3596638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596639 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (MK_COMB (@lem3596638) (@lem3596637 A)). Qed.
Lemma lem3596640 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (MK_COMB (@lem3596639 A) (@lem3596627 A)). Qed.
Lemma lem3596677 {A : Type'} : (term110 A) = (term120 A).
Proof. exact (TRANS (@lem3596599 A) (@lem3596640 A)). Qed.
Lemma lem3596678 {A : Type'} : (term120 A) = (term110 A).
Proof. exact (SYM (@lem3596677 A)). Qed.
Lemma lem3596679 {A : Type'} (h1 : term107 A) : term107 A.
Proof. exact (h1). Qed.
Lemma lem3596680 {A : Type'} (h1 : term109 A) : term109 A.
Proof. exact (h1). Qed.
Lemma lem3596681 {A : Type'} (h1 : term108 A) : term108 A.
Proof. exact (h1). Qed.
Lemma lem3596688 {A : Type'} (s : A -> Prop) : (term127 A s) = (term128 A s).
Proof. exact (@lem17362 (@SUBSET A s (@EMPTY A)) (@FINITE A s)). Qed.
Lemma lem3596689 {A : Type'} (P : type686 A) : (term129 A P) = (term130 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3596690 {A : Type'} : (term107 A) = (term131 A).
Proof. exact (@lem3596689 A (term126 A)). Qed.
Lemma lem3596691 {A : Type'} (s : A -> Prop) : (term132 A s) = (term125 A s).
Proof. exact (eq_refl (term132 A s)). Qed.
Lemma lem3596692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3596693 {A : Type'} (s : A -> Prop) : (term133 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem3596692) (@lem3596691 A s)). Qed.
Lemma lem3596694 {A : Type'} (s : A -> Prop) : (term133 A s) = (term128 A s).
Proof. exact (TRANS (@lem3596693 A s) (@lem3596688 A s)). Qed.
Lemma lem3596695 {A : Type'} : (term134 A) = (term135 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596694 A s)). Qed.
Lemma lem3596696 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3596697 {A : Type'} : (term131 A) = (term136 A).
Proof. exact (MK_COMB (@lem3596696 A) (@lem3596695 A)). Qed.
Lemma lem3596750 {A : Type'} : (term107 A) = (term136 A).
Proof. exact (TRANS (@lem3596690 A) (@lem3596697 A)). Qed.
Lemma lem3596751 {A : Type'} (h1 : term107 A) : term136 A.
Proof. exact (EQ_MP (@lem3596750 A) (@lem3596679 A h1)). Qed.
Lemma lem3596759 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term137 A x s).
Proof. exact (@lem17265 (@FINITE A s) (term8 A x s)). Qed.
Lemma lem3596760 {A : Type'} (x : A) : (term122 A x) = (term138 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596759 A x s)). Qed.
Lemma lem3596761 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596762 {A : Type'} (x : A) : (term5 A x) = (term139 A x).
Proof. exact (MK_COMB (@lem3596761 A) (@lem3596760 A x)). Qed.
Lemma lem3596763 {A : Type'} : (term123 A) = (term140 A).
Proof. exact (fun_ext (fun x : A => @lem3596762 A x)). Qed.
Lemma lem3596764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3596765 {A : Type'} : (term3 A) = (term141 A).
Proof. exact (MK_COMB (@lem3596764 A) (@lem3596763 A)). Qed.
Lemma lem3596767 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3596824 {A : Type'} : (term109 A) = (term142 A).
Proof. exact (MK_COMB (@lem3596767 A) (@lem3596765 A)). Qed.
Lemma lem3596825 {A : Type'} (h1 : term109 A) : term142 A.
Proof. exact (EQ_MP (@lem3596824 A) (@lem3596680 A h1)). Qed.
Lemma lem3596840 {A : Type'} (s : A -> Prop) : ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A))) = (term143 A s).
Proof. exact (@lem17784 (@SUBSET A s (@EMPTY A)) (s = (@EMPTY A))). Qed.
Lemma lem3596841 {A : Type'} : (term121 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596840 A s)). Qed.
Lemma lem3596842 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596843 {A : Type'} : (term108 A) = (term145 A).
Proof. exact (MK_COMB (@lem3596842 A) (@lem3596841 A)). Qed.
Lemma lem3596845 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3596846 {A : Type'} (P : type686 A) (Q : type686 A) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem3596845 (A -> Prop) P Q). Qed.
Lemma lem3596847 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (@lem3596846 A (term152 A) (term153 A)). Qed.
Lemma lem3596848 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (eq_refl (term154 A s)). Qed.
Lemma lem3596849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3596850 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (MK_COMB (@lem3596849) (@lem3596848 A s)). Qed.
Lemma lem3596851 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (eq_refl (term158 A s)). Qed.
Lemma lem3596852 {A : Type'} (s : A -> Prop) : (term160 A s) = (term143 A s).
Proof. exact (MK_COMB (@lem3596850 A s) (@lem3596851 A s)). Qed.
Lemma lem3596853 {A : Type'} : (term161 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596852 A s)). Qed.
Lemma lem3596854 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596855 {A : Type'} : (term150 A) = (term145 A).
Proof. exact (MK_COMB (@lem3596854 A) (@lem3596853 A)). Qed.
Lemma lem3596856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3596857 {A : Type'} : (term162 A) = (term163 A).
Proof. exact (MK_COMB (@lem3596856) (@lem3596855 A)). Qed.
Lemma lem3596858 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (eq_refl (term154 A s)). Qed.
Lemma lem3596859 {A : Type'} : (term164 A) = (term152 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596858 A s)). Qed.
Lemma lem3596860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596861 {A : Type'} : (term165 A) = (term166 A).
Proof. exact (MK_COMB (@lem3596860 A) (@lem3596859 A)). Qed.
Lemma lem3596862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3596863 {A : Type'} : (term167 A) = (term168 A).
Proof. exact (MK_COMB (@lem3596862) (@lem3596861 A)). Qed.
Lemma lem3596864 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (eq_refl (term158 A s)). Qed.
Lemma lem3596865 {A : Type'} : (term169 A) = (term153 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596864 A s)). Qed.
Lemma lem3596866 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596867 {A : Type'} : (term170 A) = (term171 A).
Proof. exact (MK_COMB (@lem3596866 A) (@lem3596865 A)). Qed.
Lemma lem3596868 {A : Type'} : (term151 A) = (term172 A).
Proof. exact (MK_COMB (@lem3596863 A) (@lem3596867 A)). Qed.
Lemma lem3596869 {A : Type'} : ((term150 A) = (term151 A)) = ((term145 A) = (term172 A)).
Proof. exact (MK_COMB (@lem3596857 A) (@lem3596868 A)). Qed.
Lemma lem3596968 {A : Type'} : (term145 A) = (term172 A).
Proof. exact (EQ_MP (@lem3596869 A) (@lem3596847 A)). Qed.
Lemma lem3596969 {A : Type'} : (term108 A) = (term172 A).
Proof. exact (TRANS (@lem3596843 A) (@lem3596968 A)). Qed.
Lemma lem3596970 {A : Type'} (h1 : term108 A) : term172 A.
Proof. exact (EQ_MP (@lem3596969 A) (@lem3596681 A h1)). Qed.
Lemma lem3596986 {A : Type'} (x : A) (s : A -> Prop) : (term137 A x s) = (term137 A x s).
Proof. exact (eq_refl (term137 A x s)). Qed.
Lemma lem3596987 {A : Type'} (x : A) : (term138 A x) = (term138 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3596986 A x s)). Qed.
Lemma lem3596988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3596989 {A : Type'} (x : A) : (term139 A x) = (term139 A x).
Proof. exact (MK_COMB (@lem3596988 A) (@lem3596987 A x)). Qed.
Lemma lem3596990 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (fun_ext (fun x : A => @lem3596989 A x)). Qed.
Lemma lem3596991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3596992 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (MK_COMB (@lem3596991 A) (@lem3596990 A)). Qed.
Lemma lem3596997 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (eq_refl (term124 A)). Qed.
Lemma lem3596998 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem3596997 A) (@lem3596992 A)). Qed.
Lemma lem3596999 {A : Type'} (h1 : term109 A) : term142 A.
Proof. exact (EQ_MP (@lem3596998 A) (@lem3596825 A h1)). Qed.
Lemma lem3597014 {A : Type'} (s : A -> Prop) : (term159 A s) = (term159 A s).
Proof. exact (eq_refl (term159 A s)). Qed.
Lemma lem3597015 {A : Type'} : (term153 A) = (term153 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3597014 A s)). Qed.
Lemma lem3597016 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597017 {A : Type'} : (term171 A) = (term171 A).
Proof. exact (MK_COMB (@lem3597016 A) (@lem3597015 A)). Qed.
Lemma lem3597032 {A : Type'} (s : A -> Prop) : (term155 A s) = (term155 A s).
Proof. exact (eq_refl (term155 A s)). Qed.
Lemma lem3597033 {A : Type'} : (term152 A) = (term152 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3597032 A s)). Qed.
Lemma lem3597034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597035 {A : Type'} : (term166 A) = (term166 A).
Proof. exact (MK_COMB (@lem3597034 A) (@lem3597033 A)). Qed.
Lemma lem3597036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3597037 {A : Type'} : (term168 A) = (term168 A).
Proof. exact (MK_COMB (@lem3597036) (@lem3597035 A)). Qed.
Lemma lem3597038 {A : Type'} : (term172 A) = (term172 A).
Proof. exact (MK_COMB (@lem3597037 A) (@lem3597017 A)). Qed.
Lemma lem3597039 {A : Type'} (h1 : term108 A) : term172 A.
Proof. exact (EQ_MP (@lem3597038 A) (@lem3596970 A h1)). Qed.
Lemma lem3597053 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : term128 A s.
Proof. exact (h1). Qed.
Lemma lem3597056 {A : Type'} (h1 : term108 A) : term171 A.
Proof. exact (proj2 (@lem3597039 A h1)). Qed.
Lemma lem3597088 {A : Type'} (s : A -> Prop) : (term159 A s) = (term159 A s).
Proof. exact (eq_refl (term159 A s)). Qed.
Lemma lem3597089 {A : Type'} : (term153 A) = (term153 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3597088 A s)). Qed.
Lemma lem3597090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597092 {A : Type'} : (term171 A) = (term171 A).
Proof. exact (MK_COMB (@lem3597090 A) (@lem3597089 A)). Qed.
Lemma lem3597093 {A : Type'} (h1 : term108 A) : term171 A.
Proof. exact (EQ_MP (@lem3597092 A) (@lem3597056 A h1)). Qed.
Lemma lem3597117 {A : Type'} (_38965 : A -> Prop) (h1 : term108 A) : term158 A _38965.
Proof. exact (@lem3597093 A h1 _38965). Qed.
Lemma lem3597118 {A : Type'} (_38965 : A -> Prop) : (term158 A _38965) = (term159 A _38965).
Proof. exact (eq_refl (term158 A _38965)). Qed.
Lemma lem3597129 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : term173 A s.
Proof. exact (proj2 (@lem3597053 A s h1)). Qed.
Lemma lem3597141 {A : Type'} (_38965 : A -> Prop) (h1 : term108 A) : term159 A _38965.
Proof. exact (EQ_MP (@lem3597118 A _38965) (@lem3597117 A _38965 h1)). Qed.
Lemma lem3597150 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3597151 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) (h1 : _38968 = _38969) : _38968 = _38969.
Proof. exact (h1). Qed.
Lemma lem3597152 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) (h1 : _38968 = _38969) : (@FINITE A _38968) = (@FINITE A _38969).
Proof. exact (MK_COMB (@lem3597150 A) (@lem3597151 A _38968 _38969 h1)). Qed.
Lemma lem3597154 (b : Prop) (a : Prop) : term174 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3597155 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : term175 A _38969 _38968.
Proof. exact (@lem3597154 (@FINITE A _38969) (@FINITE A _38968)). Qed.
Lemma lem3597156 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) (h1 : _38968 = _38969) : term176 A _38969 _38968.
Proof. exact (@lem3597155 A _38969 _38968 (@lem3597152 A _38968 _38969 h1)). Qed.
Lemma lem3597157 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : term177 A _38969 _38968.
Proof. exact (fun h0 : _38968 = _38969 => @lem3597156 A _38968 _38969 h0). Qed.
Lemma lem3597159 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3597160 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term177 A _38969 _38968) = (term179 A _38969 _38968).
Proof. exact (@lem3597159 (_38968 = _38969) (term176 A _38969 _38968)). Qed.
Lemma lem3597161 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : term179 A _38969 _38968.
Proof. exact (EQ_MP (@lem3597160 A _38969 _38968) (@lem3597157 A _38969 _38968)). Qed.
Lemma lem3597197 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term180 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem3597201 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : @SUBSET A s (@EMPTY A).
Proof. exact (proj1 (@lem3597053 A s h1)). Qed.
Lemma lem3597202 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : term181 A s.
Proof. exact (fun h0 : term182 A s => @lem3597201 A s h1). Qed.
Lemma lem3597204 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597205 {A : Type'} (s : A -> Prop) : (term181 A s) = (@SUBSET A s (@EMPTY A)).
Proof. exact (@lem3597204 (@SUBSET A s (@EMPTY A))). Qed.
Lemma lem3597206 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : @SUBSET A s (@EMPTY A).
Proof. exact (EQ_MP (@lem3597205 A s) (@lem3597202 A s h1)). Qed.
Lemma lem3597212 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3597213 {A : Type'} (_38965 : A -> Prop) : (term159 A _38965) = (term184 A _38965).
Proof. exact (@lem3597212 (_38965 = (@EMPTY A)) (term182 A _38965)). Qed.
Lemma lem3597221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3597222 {A : Type'} (_38965 : A -> Prop) : (term185 A _38965) = (term186 A _38965).
Proof. exact (MK_COMB (@lem3597221) (@lem3597213 A _38965)). Qed.
Lemma lem3597230 {A : Type'} (_38965 : A -> Prop) : (term184 A _38965) = (term184 A _38965).
Proof. exact (eq_refl (term184 A _38965)). Qed.
Lemma lem3597231 {A : Type'} (_38965 : A -> Prop) : ((term159 A _38965) = (term184 A _38965)) = ((term184 A _38965) = (term184 A _38965)).
Proof. exact (MK_COMB (@lem3597222 A _38965) (@lem3597230 A _38965)). Qed.
Lemma lem3597233 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3597234 (x : Prop) : (x = x) = True.
Proof. exact (@lem3597233 Prop x). Qed.
Lemma lem3597235 {A : Type'} (_38965 : A -> Prop) : ((term184 A _38965) = (term184 A _38965)) = True.
Proof. exact (@lem3597234 (term184 A _38965)). Qed.
Lemma lem3597236 {A : Type'} (_38965 : A -> Prop) : ((term159 A _38965) = (term184 A _38965)) = True.
Proof. exact (TRANS (@lem3597231 A _38965) (@lem3597235 A _38965)). Qed.
Lemma lem3597237 {A : Type'} (_38965 : A -> Prop) : True = ((term159 A _38965) = (term184 A _38965)).
Proof. exact (SYM (@lem3597236 A _38965)). Qed.
Lemma lem3597238 {A : Type'} (_38965 : A -> Prop) : (term159 A _38965) = (term184 A _38965).
Proof. exact (EQ_MP (@lem3597237 A _38965) (@lem0)). Qed.
Lemma lem3597239 {A : Type'} (_38965 : A -> Prop) (h1 : term108 A) : term184 A _38965.
Proof. exact (EQ_MP (@lem3597238 A _38965) (@lem3597141 A _38965 h1)). Qed.
Lemma lem3597241 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3597242 {A : Type'} (_38965 : A -> Prop) : (term184 A _38965) = (term188 A _38965).
Proof. exact (@lem3597241 (term182 A _38965) (_38965 = (@EMPTY A))). Qed.
Lemma lem3597244 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3597245 {A : Type'} (_38965 : A -> Prop) : (term190 A _38965) = (@SUBSET A _38965 (@EMPTY A)).
Proof. exact (@lem3597244 (@SUBSET A _38965 (@EMPTY A))). Qed.
Lemma lem3597246 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597247 {A : Type'} (_38965 : A -> Prop) : (term191 A _38965) = (term192 A _38965).
Proof. exact (MK_COMB (@lem3597246) (@lem3597245 A _38965)). Qed.
Lemma lem3597248 {A : Type'} (_38965 : A -> Prop) : (_38965 = (@EMPTY A)) = (_38965 = (@EMPTY A)).
Proof. exact (eq_refl (_38965 = (@EMPTY A))). Qed.
Lemma lem3597249 {A : Type'} (_38965 : A -> Prop) : (term188 A _38965) = (term193 A _38965).
Proof. exact (MK_COMB (@lem3597247 A _38965) (@lem3597248 A _38965)). Qed.
Lemma lem3597250 {A : Type'} (_38965 : A -> Prop) : (term184 A _38965) = (term193 A _38965).
Proof. exact (TRANS (@lem3597242 A _38965) (@lem3597249 A _38965)). Qed.
Lemma lem3597253 {A : Type'} (_38965 : A -> Prop) (h1 : term108 A) : term193 A _38965.
Proof. exact (EQ_MP (@lem3597250 A _38965) (@lem3597239 A _38965 h1)). Qed.
Lemma lem3597254 {A : Type'} (_38965 : A -> Prop) (h1 : term108 A) : term193 A _38965.
Proof. exact (@lem3597253 A _38965 h1). Qed.
Lemma lem3597255 {A : Type'} (s : A -> Prop) (h1 : term108 A) : term193 A s.
Proof. exact (@lem3597254 A s h1). Qed.
Lemma lem3597258 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : s = (@EMPTY A).
Proof. exact (@lem3597255 A s h1 (@lem3597206 A s h2)). Qed.
Lemma lem3597259 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : term194 A s.
Proof. exact (fun h0 : term195 A s => @lem3597258 A s h1 h2). Qed.
Lemma lem3597261 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597262 {A : Type'} (s : A -> Prop) : (term194 A s) = (s = (@EMPTY A)).
Proof. exact (@lem3597261 (s = (@EMPTY A))). Qed.
Lemma lem3597263 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem3597262 A s) (@lem3597259 A s h1 h2)). Qed.
Lemma lem3597265 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3597266 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3597265 A x). Qed.
Lemma lem3597267 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem3597266 A s). Qed.
Lemma lem3597268 {A : Type'} (s : A -> Prop) : term196 A s.
Proof. exact (fun h0 : term197 A s => @lem3597267 A s). Qed.
Lemma lem3597270 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597271 {A : Type'} (s : A -> Prop) : (term196 A s) = (s = s).
Proof. exact (@lem3597270 (s = s)). Qed.
Lemma lem3597272 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3597271 A s) (@lem3597268 A s)). Qed.
Lemma lem3597290 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3597291 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term198 A x y z) = (term199 A y x z).
Proof. exact (@lem3597290 (y = z) (term200 A x z)). Qed.
Lemma lem3597301 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (eq_refl (term201 A x y)). Qed.
Lemma lem3597302 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term180 A x y z) = (term202 A y x z).
Proof. exact (MK_COMB (@lem3597301 A x y) (@lem3597291 A y x z)). Qed.
Lemma lem3597306 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3597307 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term202 A y x z) = (term204 A y x z).
Proof. exact (@lem3597306 (y = z) (term200 A x y) (term200 A x z)). Qed.
Lemma lem3597329 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term180 A x y z) = (term204 A y x z).
Proof. exact (TRANS (@lem3597302 A y x z) (@lem3597307 A y x z)). Qed.
Lemma lem3597330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3597331 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term205 A x y z) = (term206 A y x z).
Proof. exact (MK_COMB (@lem3597330) (@lem3597329 A y x z)). Qed.
Lemma lem3597353 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term204 A y x z).
Proof. exact (eq_refl (term204 A y x z)). Qed.
Lemma lem3597354 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term180 A x y z) = (term204 A y x z)) = ((term204 A y x z) = (term204 A y x z)).
Proof. exact (MK_COMB (@lem3597331 A y x z) (@lem3597353 A y x z)). Qed.
Lemma lem3597356 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3597357 (x : Prop) : (x = x) = True.
Proof. exact (@lem3597356 Prop x). Qed.
Lemma lem3597358 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term204 A y x z) = (term204 A y x z)) = True.
Proof. exact (@lem3597357 (term204 A y x z)). Qed.
Lemma lem3597359 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term180 A x y z) = (term204 A y x z)) = True.
Proof. exact (TRANS (@lem3597354 A y x z) (@lem3597358 A y x z)). Qed.
Lemma lem3597360 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : True = ((term180 A x y z) = (term204 A y x z)).
Proof. exact (SYM (@lem3597359 A y x z)). Qed.
Lemma lem3597361 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term180 A x y z) = (term204 A y x z).
Proof. exact (EQ_MP (@lem3597360 A y x z) (@lem0)). Qed.
Lemma lem3597362 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term204 A y x z.
Proof. exact (EQ_MP (@lem3597361 A y x z) (@lem3597197 A x y z)). Qed.
Lemma lem3597364 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3597365 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term207 A x y z).
Proof. exact (@lem3597364 (term208 A y x z) (y = z)). Qed.
Lemma lem3597367 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3597368 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term211 A y x z) = (term212 A y x z).
Proof. exact (@lem3597367 (term200 A x y) (term200 A x z)). Qed.
Lemma lem3597370 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3597371 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (x = y).
Proof. exact (@lem3597370 (x = y)). Qed.
Lemma lem3597372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3597373 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term214 A x y) = (term215 A x y).
Proof. exact (MK_COMB (@lem3597372) (@lem3597371 A x y)). Qed.
Lemma lem3597375 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3597376 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term213 A x z) = (x = z).
Proof. exact (@lem3597375 (x = z)). Qed.
Lemma lem3597377 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term212 A y x z) = (term216 A y x z).
Proof. exact (MK_COMB (@lem3597373 A x y) (@lem3597376 A x z)). Qed.
Lemma lem3597378 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term211 A y x z) = (term216 A y x z).
Proof. exact (TRANS (@lem3597368 A y x z) (@lem3597377 A y x z)). Qed.
Lemma lem3597379 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597380 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term217 A y x z) = (term218 A y x z).
Proof. exact (MK_COMB (@lem3597379) (@lem3597378 A y x z)). Qed.
Lemma lem3597381 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3597382 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term207 A x y z) = (term219 A x y z).
Proof. exact (MK_COMB (@lem3597380 A y x z) (@lem3597381 A y z)). Qed.
Lemma lem3597383 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term219 A x y z).
Proof. exact (TRANS (@lem3597365 A x y z) (@lem3597382 A x y z)). Qed.
Lemma lem3597385 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : term220 A s.
Proof. exact (conj (@lem3597263 A s h1 h2) (@lem3597272 A s)). Qed.
Lemma lem3597387 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term219 A x y z.
Proof. exact (EQ_MP (@lem3597383 A x y z) (@lem3597362 A y x z)). Qed.
Lemma lem3597388 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term219 A x y z.
Proof. exact (@lem3597387 A x y z). Qed.
Lemma lem3597389 {A : Type'} (s : A -> Prop) : term221 A s.
Proof. exact (@lem3597388 A s (@EMPTY A) s). Qed.
Lemma lem3597392 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : (@EMPTY A) = s.
Proof. exact (@lem3597389 A s (@lem3597385 A s h1 h2)). Qed.
Lemma lem3597393 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : term222 A s.
Proof. exact (fun h0 : term223 A s => @lem3597392 A s h1 h2). Qed.
Lemma lem3597395 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597396 {A : Type'} (s : A -> Prop) : (term222 A s) = ((@EMPTY A) = s).
Proof. exact (@lem3597395 ((@EMPTY A) = s)). Qed.
Lemma lem3597397 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term128 A s) : (@EMPTY A) = s.
Proof. exact (EQ_MP (@lem3597396 A s) (@lem3597393 A s h1 h2)). Qed.
Lemma lem3597399 {A : Type'} (h1 : term109 A) : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3596999 A h1)). Qed.
Lemma lem3597400 {A : Type'} (h1 : term109 A) : term224 A.
Proof. exact (fun h0 : term225 A => @lem3597399 A h1). Qed.
Lemma lem3597402 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597403 {A : Type'} : (term224 A) = (@FINITE A (@EMPTY A)).
Proof. exact (@lem3597402 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3597404 {A : Type'} (h1 : term109 A) : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem3597403 A) (@lem3597400 A h1)). Qed.
Lemma lem3597410 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3597411 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term179 A _38969 _38968) = (term226 A _38969 _38968).
Proof. exact (@lem3597410 (@FINITE A _38969) (term200 A _38968 _38969) (term173 A _38968)). Qed.
Lemma lem3597429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3597430 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term227 A _38969 _38968) = (term228 A _38969 _38968).
Proof. exact (MK_COMB (@lem3597429) (@lem3597411 A _38969 _38968)). Qed.
Lemma lem3597448 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term226 A _38969 _38968) = (term226 A _38969 _38968).
Proof. exact (eq_refl (term226 A _38969 _38968)). Qed.
Lemma lem3597449 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : ((term179 A _38969 _38968) = (term226 A _38969 _38968)) = ((term226 A _38969 _38968) = (term226 A _38969 _38968)).
Proof. exact (MK_COMB (@lem3597430 A _38969 _38968) (@lem3597448 A _38969 _38968)). Qed.
Lemma lem3597451 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3597452 (x : Prop) : (x = x) = True.
Proof. exact (@lem3597451 Prop x). Qed.
Lemma lem3597453 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : ((term226 A _38969 _38968) = (term226 A _38969 _38968)) = True.
Proof. exact (@lem3597452 (term226 A _38969 _38968)). Qed.
Lemma lem3597454 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : ((term179 A _38969 _38968) = (term226 A _38969 _38968)) = True.
Proof. exact (TRANS (@lem3597449 A _38969 _38968) (@lem3597453 A _38969 _38968)). Qed.
Lemma lem3597455 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : True = ((term179 A _38969 _38968) = (term226 A _38969 _38968)).
Proof. exact (SYM (@lem3597454 A _38969 _38968)). Qed.
Lemma lem3597456 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term179 A _38969 _38968) = (term226 A _38969 _38968).
Proof. exact (EQ_MP (@lem3597455 A _38969 _38968) (@lem0)). Qed.
Lemma lem3597457 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : term226 A _38969 _38968.
Proof. exact (EQ_MP (@lem3597456 A _38969 _38968) (@lem3597161 A _38969 _38968)). Qed.
Lemma lem3597459 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3597460 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : (term226 A _38969 _38968) = (term229 A _38968 _38969).
Proof. exact (@lem3597459 (term230 A _38969 _38968) (@FINITE A _38969)). Qed.
Lemma lem3597462 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3597463 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term231 A _38969 _38968) = (term232 A _38969 _38968).
Proof. exact (@lem3597462 (term200 A _38968 _38969) (term173 A _38968)). Qed.
Lemma lem3597465 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3597466 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : (term213 A _38968 _38969) = (_38968 = _38969).
Proof. exact (@lem3597465 (_38968 = _38969)). Qed.
Lemma lem3597467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3597468 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : (term214 A _38968 _38969) = (term215 A _38968 _38969).
Proof. exact (MK_COMB (@lem3597467) (@lem3597466 A _38968 _38969)). Qed.
Lemma lem3597470 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3597471 {A : Type'} (_38968 : A -> Prop) : (term233 A _38968) = (@FINITE A _38968).
Proof. exact (@lem3597470 (@FINITE A _38968)). Qed.
Lemma lem3597472 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term232 A _38969 _38968) = (term234 A _38969 _38968).
Proof. exact (MK_COMB (@lem3597468 A _38968 _38969) (@lem3597471 A _38968)). Qed.
Lemma lem3597473 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term231 A _38969 _38968) = (term234 A _38969 _38968).
Proof. exact (TRANS (@lem3597463 A _38969 _38968) (@lem3597472 A _38969 _38968)). Qed.
Lemma lem3597474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597475 {A : Type'} (_38969 : A -> Prop) (_38968 : A -> Prop) : (term235 A _38969 _38968) = (term236 A _38969 _38968).
Proof. exact (MK_COMB (@lem3597474) (@lem3597473 A _38969 _38968)). Qed.
Lemma lem3597476 {A : Type'} (_38969 : A -> Prop) : (@FINITE A _38969) = (@FINITE A _38969).
Proof. exact (eq_refl (@FINITE A _38969)). Qed.
Lemma lem3597477 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : (term229 A _38968 _38969) = (term237 A _38968 _38969).
Proof. exact (MK_COMB (@lem3597475 A _38969 _38968) (@lem3597476 A _38969)). Qed.
Lemma lem3597478 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : (term226 A _38969 _38968) = (term237 A _38968 _38969).
Proof. exact (TRANS (@lem3597460 A _38968 _38969) (@lem3597477 A _38968 _38969)). Qed.
Lemma lem3597480 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : term238 A s.
Proof. exact (conj (@lem3597397 A s h1 h3) (@lem3597404 A h2)). Qed.
Lemma lem3597482 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : term237 A _38968 _38969.
Proof. exact (EQ_MP (@lem3597478 A _38968 _38969) (@lem3597457 A _38969 _38968)). Qed.
Lemma lem3597483 {A : Type'} (_38968 : A -> Prop) (_38969 : A -> Prop) : term237 A _38968 _38969.
Proof. exact (@lem3597482 A _38968 _38969). Qed.
Lemma lem3597484 {A : Type'} (s : A -> Prop) : term239 A s.
Proof. exact (@lem3597483 A (@EMPTY A) s). Qed.
Lemma lem3597487 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : @FINITE A s.
Proof. exact (@lem3597484 A s (@lem3597480 A s h1 h2 h3)). Qed.
Lemma lem3597488 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : term240 A s.
Proof. exact (fun h0 : term173 A s => @lem3597487 A s h1 h2 h3). Qed.
Lemma lem3597490 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597491 {A : Type'} (s : A -> Prop) : (term240 A s) = (@FINITE A s).
Proof. exact (@lem3597490 (@FINITE A s)). Qed.
Lemma lem3597492 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3597491 A s) (@lem3597488 A s h1 h2 h3)). Qed.
Lemma lem3597495 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3597497 {A : Type'} (s : A -> Prop) : (term173 A s) = (term241 A s).
Proof. exact (@lem3597495 (@FINITE A s)). Qed.
Lemma lem3597500 {A : Type'} (s : A -> Prop) (h1 : term128 A s) : term241 A s.
Proof. exact (EQ_MP (@lem3597497 A s) (@lem3597129 A s h1)). Qed.
Lemma lem3597503 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : False.
Proof. exact (@lem3597500 A s h3 (@lem3597492 A s h1 h2 h3)). Qed.
Lemma lem3597504 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : term242.
Proof. exact (fun h0 : ~ False => @lem3597503 A s h1 h2 h3). Qed.
Lemma lem3597506 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3597507 : term242 = False.
Proof. exact (@lem3597506 False). Qed.
Lemma lem3597508 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : False.
Proof. exact (EQ_MP (@lem3597507) (@lem3597504 A s h1 h2 h3)). Qed.
Lemma lem3597509 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : (term128 A s) = False.
Proof. exact (prop_ext (fun h4 : term128 A s => @lem3597508 A s h1 h2 h3) (fun h4 : False => @lem3597053 A s h3)). Qed.
Lemma lem3597510 {A : Type'} (s : A -> Prop) (h1 : term108 A) (h2 : term109 A) (h3 : term128 A s) : False.
Proof. exact (EQ_MP (@lem3597509 A s h1 h2 h3) (@lem3597053 A s h3)). Qed.
Lemma lem3597511 {A : Type'} (h1 : term108 A) (h2 : term107 A) (h3 : term109 A) : False.
Proof. exact (ex_elim (@lem3596751 A h2) (fun s : A -> Prop => fun h0 : term135 A s => @lem3597510 A s h1 h3 h0)). Qed.
Lemma lem3597512 {A : Type'} (h1 : term107 A) (h2 : term109 A) : term114 A.
Proof. exact (fun h0 : term108 A => @lem3597511 A h0 h1 h2). Qed.
Lemma lem3597513 {A : Type'} : (term114 A) = (term115 A).
Proof. exact (@lem69 (term108 A)). Qed.
Lemma lem3597514 {A : Type'} (h1 : term107 A) (h2 : term109 A) : term115 A.
Proof. exact (EQ_MP (@lem3597513 A) (@lem3597512 A h1 h2)). Qed.
Lemma lem3597515 {A : Type'} (h1 : term107 A) : term118 A.
Proof. exact (fun h0 : term109 A => @lem3597514 A h1 h0). Qed.
Lemma lem3597516 {A : Type'} : term120 A.
Proof. exact (fun h0 : term107 A => @lem3597515 A h0). Qed.
Lemma lem3597517 {A : Type'} : term110 A.
Proof. exact (EQ_MP (@lem3596678 A) (@lem3597516 A)). Qed.
Lemma lem3597519 {A : Type'} : term110 A.
Proof. exact (@lem3596558 A (@lem3597517 A)). Qed.
Lemma lem3597520 {A : Type'} (h1 : term107 A) : term117 A.
Proof. exact (@lem3597519 A (@lem3596538 A h1)). Qed.
Lemma lem3597521 {A : Type'} (h1 : term107 A) : term114 A.
Proof. exact (@lem3597520 A h1 (@lem3596541 A)). Qed.
Lemma lem3597522 {A : Type'} (h1 : term107 A) : False.
Proof. exact (@lem3597521 A h1 (@lem3596539 A)). Qed.
Lemma lem3597523 {A : Type'} (h1 : term107 A) : (term107 A) = False.
Proof. exact (prop_ext (fun h2 : term107 A => @lem3597522 A h1) (fun h2 : False => @lem3596538 A h1)). Qed.
Lemma lem3597524 {A : Type'} (h1 : term107 A) : False.
Proof. exact (EQ_MP (@lem3597523 A h1) (@lem3596538 A h1)). Qed.
Lemma lem3597525 {A : Type'} : term106 A.
Proof. exact (fun h0 : term107 A => @lem3597524 A h0). Qed.
Lemma lem3597526 {A : Type'} : term79 A.
Proof. exact (EQ_MP (@lem3596537 A) (@lem3597525 A)). Qed.
Lemma lem3597527 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (h1). Qed.
Lemma lem3597528 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term243 A t x u) : term243 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597529 {A : Type'} (t : A -> Prop) (x : A) (h1 : term244 A t x) : term244 A t x.
Proof. exact (h1). Qed.
Lemma lem3597531 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (EQ_MP (@lem3596343 A x s) (@lem3596342 A x s)). Qed.
Lemma lem3597532 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (@lem3597531 A x s). Qed.
Lemma lem3597533 {A : Type'} (t : A -> Prop) (x : A) : term245 A t x.
Proof. exact (@lem3597532 A x (@DELETE A t x)). Qed.
Lemma lem3597534 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (h1). Qed.
Lemma lem3597535 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term63 A u s'.
Proof. exact (@lem3597534 A u h1 s'). Qed.
Lemma lem3597536 {A : Type'} (u : A -> Prop) (s' : A -> Prop) : (term63 A u s') = (term64 A u s').
Proof. exact (eq_refl (term63 A u s')). Qed.
Lemma lem3597537 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (EQ_MP (@lem3597536 A u s') (@lem3597535 A s' u h1)). Qed.
Lemma lem3597538 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A s' u) : @SUBSET A s' u.
Proof. exact (h1). Qed.
Lemma lem3597539 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) (h2 : @SUBSET A s' u) : @FINITE A s'.
Proof. exact (@lem3597537 A s' u h1 (@lem3597538 A s' u h2)). Qed.
Lemma lem3597540 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A s' u) : term246 A u s'.
Proof. exact (fun h0 : term72 A u => @lem3597539 A s' u h0 h1). Qed.
Lemma lem3597541 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (h1). Qed.
Lemma lem3597542 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) (h2 : @SUBSET A s' u) : @FINITE A s'.
Proof. exact (@lem3597540 A s' u h2 (@lem3597541 A u h1)). Qed.
Lemma lem3597543 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (fun h0 : @SUBSET A s' u => @lem3597542 A s' u h1 h0). Qed.
Lemma lem3597544 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (fun s' : A -> Prop => @lem3597543 A s' u h1). Qed.
Lemma lem3597545 {A : Type'} (u : A -> Prop) : term247 A u.
Proof. exact (fun h0 : term72 A u => @lem3597544 A u h0). Qed.
Lemma lem3597546 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (@lem3597545 A u (@lem3597527 A u h1)). Qed.
Lemma lem3597547 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term63 A u s'.
Proof. exact (@lem3597546 A u h1 s'). Qed.
Lemma lem3597548 {A : Type'} (u : A -> Prop) (s' : A -> Prop) : (term63 A u s') = (term64 A u s').
Proof. exact (eq_refl (term63 A u s')). Qed.
Lemma lem3597551 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (EQ_MP (@lem3597548 A u s') (@lem3597547 A s' u h1)). Qed.
Lemma lem3597552 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (@lem3597551 A s' u h1). Qed.
Lemma lem3597553 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) : term248 A u t x.
Proof. exact (@lem3597552 A (@DELETE A t x) u h1). Qed.
Lemma lem3597557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3597558 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (@lem3597557 A s t). Qed.
Lemma lem3597559 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term243 A t x u) = (term250 A t x u).
Proof. exact (@lem3597558 A t (@INSERT A x u)). Qed.
Lemma lem3597566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597567 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term251 A t x u) = (term252 A t x u).
Proof. exact (MK_COMB (@lem3597566) (@lem3597559 A t x u)). Qed.
Lemma lem3597569 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3597570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (@lem3597569 A s t). Qed.
Lemma lem3597571 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term253 A t x u) = (term254 A t x u).
Proof. exact (@lem3597570 A (@DELETE A t x) u). Qed.
Lemma lem3597578 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term255 A t x u) = (term256 A t x u).
Proof. exact (MK_COMB (@lem3597567 A t x u) (@lem3597571 A t x u)). Qed.
Lemma lem3597581 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term256 A t x u) = (term255 A t x u).
Proof. exact (SYM (@lem3597578 A t x u)). Qed.
Lemma lem3597591 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3597592 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3597591 A P x). Qed.
Lemma lem3597593 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3597592 A t x'). Qed.
Lemma lem3597594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597595 {A : Type'} (t : A -> Prop) (x' : A) : (term257 A x' t) = (term258 A t x').
Proof. exact (MK_COMB (@lem3597594) (@lem3597593 A t x')). Qed.
Lemma lem3597597 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3597598 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (@lem3597597 A y x s). Qed.
Lemma lem3597599 {A : Type'} (x : A) (x' : A) (u : A -> Prop) : (term259 A x' x u) = (term260 A x x' u).
Proof. exact (@lem3597598 A x x' u). Qed.
Lemma lem3597605 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3597606 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3597605 A P x). Qed.
Lemma lem3597607 {A : Type'} (u : A -> Prop) (x' : A) : (@IN A x' u) = (u x').
Proof. exact (@lem3597606 A u x'). Qed.
Lemma lem3597608 {A : Type'} (x' : A) (x : A) : (term261 A x' x) = (term261 A x' x).
Proof. exact (eq_refl (term261 A x' x)). Qed.
Lemma lem3597609 {A : Type'} (x : A) (u : A -> Prop) (x' : A) : (term260 A x x' u) = (term262 A x u x').
Proof. exact (MK_COMB (@lem3597608 A x' x) (@lem3597607 A u x')). Qed.
Lemma lem3597612 {A : Type'} (x : A) (u : A -> Prop) (x' : A) : (term259 A x' x u) = (term262 A x u x').
Proof. exact (TRANS (@lem3597599 A x x' u) (@lem3597609 A x u x')). Qed.
Lemma lem3597613 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term263 A t x' x u) = (term264 A t x u x').
Proof. exact (MK_COMB (@lem3597595 A t x') (@lem3597612 A x u x')). Qed.
Lemma lem3597616 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term265 A t x u) = (term266 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597613 A t x u x')). Qed.
Lemma lem3597617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597618 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term250 A t x u) = (term267 A t x u).
Proof. exact (MK_COMB (@lem3597617 A) (@lem3597616 A t x u)). Qed.
Lemma lem3597623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597624 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term252 A t x u) = (term268 A t x u).
Proof. exact (MK_COMB (@lem3597623) (@lem3597618 A t x u)). Qed.
Lemma lem3597632 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term269 A x s y) = (term270 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3597633 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term269 A x s y) = (term270 A s x y).
Proof. exact (@lem3597632 A s x y). Qed.
Lemma lem3597634 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term269 A x' t x) = (term270 A t x' x).
Proof. exact (@lem3597633 A t x' x). Qed.
Lemma lem3597638 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3597639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3597638 A P x). Qed.
Lemma lem3597640 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3597639 A t x'). Qed.
Lemma lem3597641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3597642 {A : Type'} (t : A -> Prop) (x' : A) : (term271 A x' t) = (term272 A t x').
Proof. exact (MK_COMB (@lem3597641) (@lem3597640 A t x')). Qed.
Lemma lem3597645 {A : Type'} (x' : A) (x : A) : (term273 A x' x) = (term273 A x' x).
Proof. exact (eq_refl (term273 A x' x)). Qed.
Lemma lem3597646 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term270 A t x' x) = (term274 A t x' x).
Proof. exact (MK_COMB (@lem3597642 A t x') (@lem3597645 A x' x)). Qed.
Lemma lem3597649 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term269 A x' t x) = (term274 A t x' x).
Proof. exact (TRANS (@lem3597634 A t x' x) (@lem3597646 A t x' x)). Qed.
Lemma lem3597650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597651 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term275 A x' t x) = (term276 A t x' x).
Proof. exact (MK_COMB (@lem3597650) (@lem3597649 A t x' x)). Qed.
Lemma lem3597653 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3597654 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3597653 A P x). Qed.
Lemma lem3597655 {A : Type'} (u : A -> Prop) (x' : A) : (@IN A x' u) = (u x').
Proof. exact (@lem3597654 A u x'). Qed.
Lemma lem3597656 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term277 A t x x' u) = (term278 A t x u x').
Proof. exact (MK_COMB (@lem3597651 A t x' x) (@lem3597655 A u x')). Qed.
Lemma lem3597659 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term279 A t x u) = (term280 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597656 A t x u x')). Qed.
Lemma lem3597660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597661 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term254 A t x u) = (term281 A t x u).
Proof. exact (MK_COMB (@lem3597660 A) (@lem3597659 A t x u)). Qed.
Lemma lem3597666 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term256 A t x u) = (term282 A t x u).
Proof. exact (MK_COMB (@lem3597624 A t x u) (@lem3597661 A t x u)). Qed.
Lemma lem3597669 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term282 A t x u) = (term256 A t x u).
Proof. exact (SYM (@lem3597666 A t x u)). Qed.
Lemma lem3597671 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3597672 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term282 A t x u) = (term283 A t x u).
Proof. exact (@lem3597671 (term282 A t x u)). Qed.
Lemma lem3597673 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term283 A t x u) = (term282 A t x u).
Proof. exact (SYM (@lem3597672 A t x u)). Qed.
Lemma lem3597674 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term284 A t x u) : term284 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597677 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term283 A t x u) : term283 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597678 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term285 A t x u.
Proof. exact (fun h0 : term283 A t x u => @lem3597677 A t x u h0). Qed.
Lemma lem3597679 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term285 A t x u) : term285 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597680 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term283 A t x u) : term283 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597681 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term283 A t x u) (h2 : term285 A t x u) : term283 A t x u.
Proof. exact (@lem3597679 A t x u h2 (@lem3597680 A t x u h1)). Qed.
Lemma lem3597682 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term283 A t x u) : term286 A t x u.
Proof. exact (fun h0 : term285 A t x u => @lem3597681 A t x u h1 h0). Qed.
Lemma lem3597683 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term285 A t x u) : term285 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597684 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term283 A t x u) (h2 : term285 A t x u) : term283 A t x u.
Proof. exact (@lem3597682 A t x u h1 (@lem3597683 A t x u h2)). Qed.
Lemma lem3597685 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term285 A t x u) : term285 A t x u.
Proof. exact (fun h0 : term283 A t x u => @lem3597684 A t x u h0 h1). Qed.
Lemma lem3597686 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term287 A t x u.
Proof. exact (fun h0 : term285 A t x u => @lem3597685 A t x u h0). Qed.
Lemma lem3597689 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term285 A t x u.
Proof. exact (@lem3597686 A t x u (@lem3597678 A t x u)). Qed.
Lemma lem3597690 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term285 A t x u.
Proof. exact (@lem3597689 A t x u). Qed.
Lemma lem3597704 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3597705 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term283 A t x u) = (term288 A t x u).
Proof. exact (@lem3597704 (term284 A t x u)). Qed.
Lemma lem3597707 (t : Prop) : (term189 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3597708 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term288 A t x u) = (term282 A t x u).
Proof. exact (@lem3597707 (term282 A t x u)). Qed.
Lemma lem3597711 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term283 A t x u) = (term282 A t x u).
Proof. exact (TRANS (@lem3597705 A t x u) (@lem3597708 A t x u)). Qed.
Lemma lem3597728 {A : Type'} (x : A) (u : A -> Prop) : (term289 A x u) = (term290 A x u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3597711 A t x u)). Qed.
Lemma lem3597729 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597730 {A : Type'} (x : A) (u : A -> Prop) : (term291 A x u) = (term292 A x u).
Proof. exact (MK_COMB (@lem3597729 A) (@lem3597728 A x u)). Qed.
Lemma lem3597735 {A : Type'} (u : A -> Prop) : (term293 A u) = (term294 A u).
Proof. exact (fun_ext (fun x : A => @lem3597730 A x u)). Qed.
Lemma lem3597736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597737 {A : Type'} (u : A -> Prop) : (term295 A u) = (term296 A u).
Proof. exact (MK_COMB (@lem3597736 A) (@lem3597735 A u)). Qed.
Lemma lem3597742 {A : Type'} : (term297 A) = (term298 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3597737 A u)). Qed.
Lemma lem3597743 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597752 {A : Type'} : (term299 A) = (term300 A).
Proof. exact (MK_COMB (@lem3597743 A) (@lem3597742 A)). Qed.
Lemma lem3597763 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term278 A t x u x') = (term278 A t x u x').
Proof. exact (eq_refl (term278 A t x u x')). Qed.
Lemma lem3597764 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term280 A t x u) = (term280 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597763 A t x u x')). Qed.
Lemma lem3597765 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597766 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term281 A t x u) = (term281 A t x u).
Proof. exact (MK_COMB (@lem3597765 A) (@lem3597764 A t x u)). Qed.
Lemma lem3597775 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term264 A t x u x') = (term264 A t x u x').
Proof. exact (eq_refl (term264 A t x u x')). Qed.
Lemma lem3597776 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term266 A t x u) = (term266 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597775 A t x u x')). Qed.
Lemma lem3597777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597778 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term267 A t x u) = (term267 A t x u).
Proof. exact (MK_COMB (@lem3597777 A) (@lem3597776 A t x u)). Qed.
Lemma lem3597779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3597780 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term268 A t x u) = (term268 A t x u).
Proof. exact (MK_COMB (@lem3597779) (@lem3597778 A t x u)). Qed.
Lemma lem3597781 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term282 A t x u) = (term282 A t x u).
Proof. exact (MK_COMB (@lem3597780 A t x u) (@lem3597766 A t x u)). Qed.
Lemma lem3597782 {A : Type'} (x : A) (u : A -> Prop) : (term290 A x u) = (term290 A x u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3597781 A t x u)). Qed.
Lemma lem3597783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597784 {A : Type'} (x : A) (u : A -> Prop) : (term292 A x u) = (term292 A x u).
Proof. exact (MK_COMB (@lem3597783 A) (@lem3597782 A x u)). Qed.
Lemma lem3597785 {A : Type'} (u : A -> Prop) : (term294 A u) = (term294 A u).
Proof. exact (fun_ext (fun x : A => @lem3597784 A x u)). Qed.
Lemma lem3597786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597787 {A : Type'} (u : A -> Prop) : (term296 A u) = (term296 A u).
Proof. exact (MK_COMB (@lem3597786 A) (@lem3597785 A u)). Qed.
Lemma lem3597788 {A : Type'} : (term298 A) = (term298 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3597787 A u)). Qed.
Lemma lem3597789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3597790 {A : Type'} : (term300 A) = (term300 A).
Proof. exact (MK_COMB (@lem3597789 A) (@lem3597788 A)). Qed.
Lemma lem3597833 {A : Type'} : (term299 A) = (term300 A).
Proof. exact (TRANS (@lem3597752 A) (@lem3597790 A)). Qed.
Lemma lem3597834 {A : Type'} : (term300 A) = (term299 A).
Proof. exact (SYM (@lem3597833 A)). Qed.
Lemma lem3597835 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term267 A t x u.
Proof. exact (h1). Qed.
Lemma lem3597838 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3597839 {A : Type'} (u : A -> Prop) (x' : A) : (u x') = (term301 A u x').
Proof. exact (@lem3597838 (u x')). Qed.
Lemma lem3597840 {A : Type'} (u : A -> Prop) (x' : A) : (term301 A u x') = (u x').
Proof. exact (SYM (@lem3597839 A u x')). Qed.
Lemma lem3597841 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3597852 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term264 A t x u x') = (term303 A t x u x').
Proof. exact (@lem17265 (t x') (term262 A x u x')). Qed.
Lemma lem3597853 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term266 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597852 A t x u x')). Qed.
Lemma lem3597854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597907 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term267 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3597854 A) (@lem3597853 A t x u)). Qed.
Lemma lem3597908 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3597907 A t x u) (@lem3597835 A t x u h1)). Qed.
Lemma lem3597918 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term274 A t x' x.
Proof. exact (h1). Qed.
Lemma lem3597924 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3597943 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term303 A t x u x') = (term303 A t x u x').
Proof. exact (eq_refl (term303 A t x u x')). Qed.
Lemma lem3597944 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term304 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597943 A t x u x')). Qed.
Lemma lem3597945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597946 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term305 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3597945 A) (@lem3597944 A t x u)). Qed.
Lemma lem3597947 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3597946 A t x u) (@lem3597908 A t x u h1)). Qed.
Lemma lem3597961 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term274 A t x' x.
Proof. exact (h1). Qed.
Lemma lem3597967 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3597983 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term303 A t x u x') = (term303 A t x u x').
Proof. exact (eq_refl (term303 A t x u x')). Qed.
Lemma lem3597984 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term304 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3597983 A t x u x')). Qed.
Lemma lem3597985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3597987 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term305 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3597985 A) (@lem3597984 A t x u)). Qed.
Lemma lem3597988 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3597987 A t x u) (@lem3597947 A t x u h1)). Qed.
Lemma lem3597992 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3598001 {A : Type'} (_38978 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term306 A t x u _38978.
Proof. exact (@lem3597988 A t x u h1 _38978). Qed.
Lemma lem3598002 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (_38978 : A) : (term306 A t x u _38978) = (term303 A t x u _38978).
Proof. exact (eq_refl (term306 A t x u _38978)). Qed.
Lemma lem3598013 {A : Type'} (_38978 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term303 A t x u _38978.
Proof. exact (EQ_MP (@lem3598002 A t x u _38978) (@lem3598001 A _38978 t x u h1)). Qed.
Lemma lem3598015 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3598019 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term273 A x' x.
Proof. exact (proj2 (@lem3597961 A t x' x h1)). Qed.
Lemma lem3598047 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : t x'.
Proof. exact (proj1 (@lem3597961 A t x' x h1)). Qed.
Lemma lem3598048 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term307 A t x'.
Proof. exact (fun h0 : term302 A t x' => @lem3598047 A t x' x h1). Qed.
Lemma lem3598050 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598051 {A : Type'} (t : A -> Prop) (x' : A) : (term307 A t x') = (t x').
Proof. exact (@lem3598050 (t x')). Qed.
Lemma lem3598052 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : t x'.
Proof. exact (EQ_MP (@lem3598051 A t x') (@lem3598048 A t x' x h1)). Qed.
Lemma lem3598054 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3598055 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term308 A u x'.
Proof. exact (fun h0 : u x' => @lem3598054 A u x' h1). Qed.
Lemma lem3598057 (p : Prop) : (term309 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3598058 {A : Type'} (u : A -> Prop) (x' : A) : (term308 A u x') = (term302 A u x').
Proof. exact (@lem3598057 (u x')). Qed.
Lemma lem3598059 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (EQ_MP (@lem3598058 A u x') (@lem3598055 A u x' h1)). Qed.
Lemma lem3598065 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3598066 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term303 A t x u _38978) = (term310 A x t u _38978).
Proof. exact (@lem3598065 (_38978 = x) (term302 A t _38978) (u _38978)). Qed.
Lemma lem3598082 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3598083 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_38978 : A) : (term311 A t u _38978) = (term312 A u t _38978).
Proof. exact (@lem3598082 (u _38978) (term302 A t _38978)). Qed.
Lemma lem3598089 {A : Type'} (_38978 : A) (x : A) : (term261 A _38978 x) = (term261 A _38978 x).
Proof. exact (eq_refl (term261 A _38978 x)). Qed.
Lemma lem3598090 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (_38978 : A) : (term310 A x t u _38978) = (term313 A x u t _38978).
Proof. exact (MK_COMB (@lem3598089 A _38978 x) (@lem3598083 A u t _38978)). Qed.
Lemma lem3598094 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3598095 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term313 A x u t _38978) = (term314 A u x t _38978).
Proof. exact (@lem3598094 (u _38978) (_38978 = x) (term302 A t _38978)). Qed.
Lemma lem3598113 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term310 A x t u _38978) = (term314 A u x t _38978).
Proof. exact (TRANS (@lem3598090 A x u t _38978) (@lem3598095 A u x t _38978)). Qed.
Lemma lem3598114 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term303 A t x u _38978) = (term314 A u x t _38978).
Proof. exact (TRANS (@lem3598066 A x t u _38978) (@lem3598113 A u x t _38978)). Qed.
Lemma lem3598115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3598116 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term315 A t x u _38978) = (term316 A u x t _38978).
Proof. exact (MK_COMB (@lem3598115) (@lem3598114 A u x t _38978)). Qed.
Lemma lem3598132 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3598133 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_38978 : A) : (term311 A t u _38978) = (term312 A u t _38978).
Proof. exact (@lem3598132 (u _38978) (term302 A t _38978)). Qed.
Lemma lem3598139 {A : Type'} (_38978 : A) (x : A) : (term261 A _38978 x) = (term261 A _38978 x).
Proof. exact (eq_refl (term261 A _38978 x)). Qed.
Lemma lem3598140 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (_38978 : A) : (term310 A x t u _38978) = (term313 A x u t _38978).
Proof. exact (MK_COMB (@lem3598139 A _38978 x) (@lem3598133 A u t _38978)). Qed.
Lemma lem3598144 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3598145 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term313 A x u t _38978) = (term314 A u x t _38978).
Proof. exact (@lem3598144 (u _38978) (_38978 = x) (term302 A t _38978)). Qed.
Lemma lem3598163 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : (term310 A x t u _38978) = (term314 A u x t _38978).
Proof. exact (TRANS (@lem3598140 A x u t _38978) (@lem3598145 A u x t _38978)). Qed.
Lemma lem3598164 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : ((term303 A t x u _38978) = (term310 A x t u _38978)) = ((term314 A u x t _38978) = (term314 A u x t _38978)).
Proof. exact (MK_COMB (@lem3598116 A u x t _38978) (@lem3598163 A u x t _38978)). Qed.
Lemma lem3598166 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3598167 (x : Prop) : (x = x) = True.
Proof. exact (@lem3598166 Prop x). Qed.
Lemma lem3598168 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_38978 : A) : ((term314 A u x t _38978) = (term314 A u x t _38978)) = True.
Proof. exact (@lem3598167 (term314 A u x t _38978)). Qed.
Lemma lem3598169 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (_38978 : A) : ((term303 A t x u _38978) = (term310 A x t u _38978)) = True.
Proof. exact (TRANS (@lem3598164 A u x t _38978) (@lem3598168 A u x t _38978)). Qed.
Lemma lem3598170 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (_38978 : A) : True = ((term303 A t x u _38978) = (term310 A x t u _38978)).
Proof. exact (SYM (@lem3598169 A x t u _38978)). Qed.
Lemma lem3598171 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term303 A t x u _38978) = (term310 A x t u _38978).
Proof. exact (EQ_MP (@lem3598170 A x t u _38978) (@lem0)). Qed.
Lemma lem3598172 {A : Type'} (_38978 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term310 A x t u _38978.
Proof. exact (EQ_MP (@lem3598171 A x t u _38978) (@lem3598013 A _38978 t x u h1)). Qed.
Lemma lem3598174 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3598175 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) (x : A) : (term310 A x t u _38978) = (term317 A t u _38978 x).
Proof. exact (@lem3598174 (term311 A t u _38978) (_38978 = x)). Qed.
Lemma lem3598177 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3598178 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term318 A t u _38978) = (term319 A t u _38978).
Proof. exact (@lem3598177 (term302 A t _38978) (u _38978)). Qed.
Lemma lem3598180 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3598181 {A : Type'} (t : A -> Prop) (_38978 : A) : (term320 A t _38978) = (t _38978).
Proof. exact (@lem3598180 (t _38978)). Qed.
Lemma lem3598182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3598183 {A : Type'} (t : A -> Prop) (_38978 : A) : (term321 A t _38978) = (term272 A t _38978).
Proof. exact (MK_COMB (@lem3598182) (@lem3598181 A t _38978)). Qed.
Lemma lem3598184 {A : Type'} (u : A -> Prop) (_38978 : A) : (term302 A u _38978) = (term302 A u _38978).
Proof. exact (eq_refl (term302 A u _38978)). Qed.
Lemma lem3598185 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term319 A t u _38978) = (term322 A t u _38978).
Proof. exact (MK_COMB (@lem3598183 A t _38978) (@lem3598184 A u _38978)). Qed.
Lemma lem3598186 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term318 A t u _38978) = (term322 A t u _38978).
Proof. exact (TRANS (@lem3598178 A t u _38978) (@lem3598185 A t u _38978)). Qed.
Lemma lem3598187 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3598188 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) : (term323 A t u _38978) = (term324 A t u _38978).
Proof. exact (MK_COMB (@lem3598187) (@lem3598186 A t u _38978)). Qed.
Lemma lem3598189 {A : Type'} (_38978 : A) (x : A) : (_38978 = x) = (_38978 = x).
Proof. exact (eq_refl (_38978 = x)). Qed.
Lemma lem3598190 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) (x : A) : (term317 A t u _38978 x) = (term325 A t u _38978 x).
Proof. exact (MK_COMB (@lem3598188 A t u _38978) (@lem3598189 A _38978 x)). Qed.
Lemma lem3598191 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_38978 : A) (x : A) : (term310 A x t u _38978) = (term325 A t u _38978 x).
Proof. exact (TRANS (@lem3598175 A t u _38978 x) (@lem3598190 A t u _38978 x)). Qed.
Lemma lem3598193 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term302 A u x') (h2 : term274 A t x' x) : term322 A t u x'.
Proof. exact (conj (@lem3598052 A t x' x h2) (@lem3598059 A u x' h1)). Qed.
Lemma lem3598195 {A : Type'} (_38978 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term325 A t u _38978 x.
Proof. exact (EQ_MP (@lem3598191 A t u _38978 x) (@lem3598172 A _38978 t x u h1)). Qed.
Lemma lem3598196 {A : Type'} (_38978 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term325 A t u _38978 x.
Proof. exact (@lem3598195 A _38978 t x u h1). Qed.
Lemma lem3598197 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term325 A t u x' x.
Proof. exact (@lem3598196 A x' t x u h1). Qed.
Lemma lem3598200 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : x' = x.
Proof. exact (@lem3598197 A x' t x u h1 (@lem3598193 A u t x' x h2 h3)). Qed.
Lemma lem3598201 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : term326 A x' x.
Proof. exact (fun h0 : term273 A x' x => @lem3598200 A u t x' x h1 h2 h3). Qed.
Lemma lem3598203 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598204 {A : Type'} (x' : A) (x : A) : (term326 A x' x) = (x' = x).
Proof. exact (@lem3598203 (x' = x)). Qed.
Lemma lem3598205 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : x' = x.
Proof. exact (EQ_MP (@lem3598204 A x' x) (@lem3598201 A u t x' x h1 h2 h3)). Qed.
Lemma lem3598208 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3598210 {A : Type'} (x' : A) (x : A) : (term273 A x' x) = (term327 A x' x).
Proof. exact (@lem3598208 (x' = x)). Qed.
Lemma lem3598213 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term327 A x' x.
Proof. exact (EQ_MP (@lem3598210 A x' x) (@lem3598019 A t x' x h1)). Qed.
Lemma lem3598216 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (@lem3598213 A t x' x h3 (@lem3598205 A u t x' x h1 h2 h3)). Qed.
Lemma lem3598217 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : term242.
Proof. exact (fun h0 : ~ False => @lem3598216 A u t x' x h1 h2 h3). Qed.
Lemma lem3598219 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598220 : term242 = False.
Proof. exact (@lem3598219 False). Qed.
Lemma lem3598221 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598220) (@lem3598217 A u t x' x h1 h2 h3)). Qed.
Lemma lem3598222 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598221 A u t x' x h1 h2 h3) (fun h4 : False => @lem3598015 A u x' h2)). Qed.
Lemma lem3598223 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598222 A u t x' x h1 h2 h3) (@lem3598015 A u x' h2)). Qed.
Lemma lem3598224 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598223 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597992 A u x' h2)). Qed.
Lemma lem3598225 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598224 A u t x' x h1 h2 h3) (@lem3597992 A u x' h2)). Qed.
Lemma lem3598226 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598225 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597992 A u x' h2)). Qed.
Lemma lem3598227 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598226 A u t x' x h1 h2 h3) (@lem3597992 A u x' h2)). Qed.
Lemma lem3598228 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598227 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597967 A u x' h2)). Qed.
Lemma lem3598229 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598228 A u t x' x h1 h2 h3) (@lem3597967 A u x' h2)). Qed.
Lemma lem3598230 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term274 A t x' x) = False.
Proof. exact (prop_ext (fun h4 : term274 A t x' x => @lem3598229 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597961 A t x' x h3)). Qed.
Lemma lem3598231 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598230 A u t x' x h1 h2 h3) (@lem3597961 A t x' x h3)). Qed.
Lemma lem3598232 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598231 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597924 A u x' h2)). Qed.
Lemma lem3598233 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598232 A u t x' x h1 h2 h3) (@lem3597924 A u x' h2)). Qed.
Lemma lem3598234 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term274 A t x' x) = False.
Proof. exact (prop_ext (fun h4 : term274 A t x' x => @lem3598233 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597918 A t x' x h3)). Qed.
Lemma lem3598235 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598234 A u t x' x h1 h2 h3) (@lem3597918 A t x' x h3)). Qed.
Lemma lem3598236 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : (term302 A u x') = False.
Proof. exact (prop_ext (fun h4 : term302 A u x' => @lem3598235 A u t x' x h1 h2 h3) (fun h4 : False => @lem3597841 A u x' h2)). Qed.
Lemma lem3598237 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term302 A u x') (h3 : term274 A t x' x) : False.
Proof. exact (EQ_MP (@lem3598236 A u t x' x h1 h2 h3) (@lem3597841 A u x' h2)). Qed.
Lemma lem3598238 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term274 A t x' x) : term301 A u x'.
Proof. exact (fun h0 : term302 A u x' => @lem3598237 A u t x' x h1 h0 h2). Qed.
Lemma lem3598239 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term267 A t x u) (h2 : term274 A t x' x) : u x'.
Proof. exact (EQ_MP (@lem3597840 A u x') (@lem3598238 A u t x' x h1 h2)). Qed.
Lemma lem3598240 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term278 A t x u x'.
Proof. exact (fun h0 : term274 A t x' x => @lem3598239 A u t x' x h1 h0). Qed.
Lemma lem3598245 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term281 A t x u.
Proof. exact (fun x' : A => @lem3598240 A x' t x u h1). Qed.
Lemma lem3598246 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term282 A t x u.
Proof. exact (fun h0 : term267 A t x u => @lem3598245 A t x u h0). Qed.
Lemma lem3598251 {A : Type'} (x : A) (u : A -> Prop) : term292 A x u.
Proof. exact (fun t : A -> Prop => @lem3598246 A t x u). Qed.
Lemma lem3598256 {A : Type'} (u : A -> Prop) : term296 A u.
Proof. exact (fun x : A => @lem3598251 A x u). Qed.
Lemma lem3598261 {A : Type'} : term300 A.
Proof. exact (fun u : A -> Prop => @lem3598256 A u). Qed.
Lemma lem3598262 {A : Type'} : term299 A.
Proof. exact (EQ_MP (@lem3597834 A) (@lem3598261 A)). Qed.
Lemma lem3598263 {A : Type'} (u : A -> Prop) : term328 A u.
Proof. exact (@lem3598262 A u). Qed.
Lemma lem3598264 {A : Type'} (u : A -> Prop) : (term328 A u) = (term295 A u).
Proof. exact (eq_refl (term328 A u)). Qed.
Lemma lem3598265 {A : Type'} (u : A -> Prop) : term295 A u.
Proof. exact (EQ_MP (@lem3598264 A u) (@lem3598263 A u)). Qed.
Lemma lem3598266 {A : Type'} (u : A -> Prop) (x : A) : term329 A u x.
Proof. exact (@lem3598265 A u x). Qed.
Lemma lem3598267 {A : Type'} (x : A) (u : A -> Prop) : (term329 A u x) = (term291 A x u).
Proof. exact (eq_refl (term329 A u x)). Qed.
Lemma lem3598268 {A : Type'} (x : A) (u : A -> Prop) : term291 A x u.
Proof. exact (EQ_MP (@lem3598267 A x u) (@lem3598266 A u x)). Qed.
Lemma lem3598269 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) : term330 A x u t.
Proof. exact (@lem3598268 A x u t). Qed.
Lemma lem3598270 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term330 A x u t) = (term283 A t x u).
Proof. exact (eq_refl (term330 A x u t)). Qed.
Lemma lem3598271 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term283 A t x u.
Proof. exact (EQ_MP (@lem3598270 A t x u) (@lem3598269 A x u t)). Qed.
Lemma lem3598273 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term283 A t x u.
Proof. exact (@lem3597690 A t x u (@lem3598271 A t x u)). Qed.
Lemma lem3598274 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term284 A t x u) : False.
Proof. exact (@lem3598273 A t x u (@lem3597674 A t x u h1)). Qed.
Lemma lem3598275 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term284 A t x u) : (term284 A t x u) = False.
Proof. exact (prop_ext (fun h2 : term284 A t x u => @lem3598274 A t x u h1) (fun h2 : False => @lem3597674 A t x u h1)). Qed.
Lemma lem3598276 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term284 A t x u) : False.
Proof. exact (EQ_MP (@lem3598275 A t x u h1) (@lem3597674 A t x u h1)). Qed.
Lemma lem3598277 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term283 A t x u.
Proof. exact (fun h0 : term284 A t x u => @lem3598276 A t x u h0). Qed.
Lemma lem3598278 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term282 A t x u.
Proof. exact (EQ_MP (@lem3597673 A t x u) (@lem3598277 A t x u)). Qed.
Lemma lem3598279 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term256 A t x u.
Proof. exact (EQ_MP (@lem3597669 A t x u) (@lem3598278 A t x u)). Qed.
Lemma lem3598280 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : term255 A t x u.
Proof. exact (EQ_MP (@lem3597581 A t x u) (@lem3598279 A t x u)). Qed.
Lemma lem3598281 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term243 A t x u) : term253 A t x u.
Proof. exact (@lem3598280 A t x u (@lem3597528 A t x u h1)). Qed.
Lemma lem3598282 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term243 A t x u) : term331 A t x.
Proof. exact (@lem3597553 A t x u h1 (@lem3598281 A t x u h2)). Qed.
Lemma lem3598283 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term243 A t x u) : term244 A t x.
Proof. exact (@lem3597533 A t x (@lem3598282 A t x u h1 h2)). Qed.
Lemma lem3598284 {A : Type'} (x : A) (t : A -> Prop) (h1 : (term332 A t x) = t) : (term332 A t x) = t.
Proof. exact (h1). Qed.
Lemma lem3598327 {A : Type'} : (term333 A) = (term333 A).
Proof. exact (eq_refl (term333 A)). Qed.
Lemma lem3598328 {A : Type'} (x : A) (t : A -> Prop) (h1 : (term332 A t x) = t) : (term334 A t x) = (term335 A t).
Proof. exact (MK_COMB (@lem3598327 A) (@lem3598284 A x t h1)). Qed.
Lemma lem3598329 {A : Type'} (t : A -> Prop) : (term335 A t) = (@FINITE A t).
Proof. exact (eq_refl (term335 A t)). Qed.
Lemma lem3598330 {A : Type'} (t : A -> Prop) (x : A) : (term336 A t x) = (term336 A t x).
Proof. exact (eq_refl (term336 A t x)). Qed.
Lemma lem3598331 {A : Type'} (x : A) (t : A -> Prop) : ((term334 A t x) = (term335 A t)) = ((term334 A t x) = (@FINITE A t)).
Proof. exact (MK_COMB (@lem3598330 A t x) (@lem3598329 A t)). Qed.
Lemma lem3598332 {A : Type'} (t : A -> Prop) (x : A) : (term334 A t x) = (term244 A t x).
Proof. exact (eq_refl (term334 A t x)). Qed.
Lemma lem3598333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3598334 {A : Type'} (t : A -> Prop) (x : A) : (term336 A t x) = (term337 A t x).
Proof. exact (MK_COMB (@lem3598333) (@lem3598332 A t x)). Qed.
Lemma lem3598335 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem3598336 {A : Type'} (x : A) (t : A -> Prop) : ((term334 A t x) = (@FINITE A t)) = ((term244 A t x) = (@FINITE A t)).
Proof. exact (MK_COMB (@lem3598334 A t x) (@lem3598335 A t)). Qed.
Lemma lem3598337 {A : Type'} (x : A) (t : A -> Prop) : ((term334 A t x) = (term335 A t)) = ((term244 A t x) = (@FINITE A t)).
Proof. exact (TRANS (@lem3598331 A x t) (@lem3598336 A x t)). Qed.
Lemma lem3598338 {A : Type'} (x : A) (t : A -> Prop) (h1 : (term332 A t x) = t) : (term244 A t x) = (@FINITE A t).
Proof. exact (EQ_MP (@lem3598337 A x t) (@lem3598328 A x t h1)). Qed.
Lemma lem3598339 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : (term332 A t x) = t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3598338 A x t h2) (@lem3597529 A t x h1)). Qed.
Lemma lem3598359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term338 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3598360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term338 A s t).
Proof. exact (@lem3598359 A s t). Qed.
Lemma lem3598361 {A : Type'} (x : A) (t : A -> Prop) : ((term332 A t x) = t) = (term339 A x t).
Proof. exact (@lem3598360 A (term332 A t x) t). Qed.
Lemma lem3598370 {A : Type'} (x : A) (t : A -> Prop) : (term257 A x t) = (term257 A x t).
Proof. exact (eq_refl (term257 A x t)). Qed.
Lemma lem3598371 {A : Type'} (x : A) (t : A -> Prop) : (term340 A x t) = (term341 A x t).
Proof. exact (MK_COMB (@lem3598370 A x t) (@lem3598361 A x t)). Qed.
Lemma lem3598374 {A : Type'} (x : A) (t : A -> Prop) : (term341 A x t) = (term340 A x t).
Proof. exact (SYM (@lem3598371 A x t)). Qed.
Lemma lem3598378 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3598379 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3598378 A P x). Qed.
Lemma lem3598380 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3598379 A t x). Qed.
Lemma lem3598381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3598382 {A : Type'} (t : A -> Prop) (x : A) : (term257 A x t) = (term258 A t x).
Proof. exact (MK_COMB (@lem3598381) (@lem3598380 A t x)). Qed.
Lemma lem3598390 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3598391 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (@lem3598390 A y x s). Qed.
Lemma lem3598392 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : (term342 A x' t x) = (term343 A x' t x).
Proof. exact (@lem3598391 A x x' (@DELETE A t x)). Qed.
Lemma lem3598398 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term269 A x s y) = (term270 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3598399 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term269 A x s y) = (term270 A s x y).
Proof. exact (@lem3598398 A s x y). Qed.
Lemma lem3598400 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term269 A x' t x) = (term270 A t x' x).
Proof. exact (@lem3598399 A t x' x). Qed.
Lemma lem3598404 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3598405 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3598404 A P x). Qed.
Lemma lem3598406 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3598405 A t x'). Qed.
Lemma lem3598407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3598408 {A : Type'} (t : A -> Prop) (x' : A) : (term271 A x' t) = (term272 A t x').
Proof. exact (MK_COMB (@lem3598407) (@lem3598406 A t x')). Qed.
Lemma lem3598411 {A : Type'} (x' : A) (x : A) : (term273 A x' x) = (term273 A x' x).
Proof. exact (eq_refl (term273 A x' x)). Qed.
Lemma lem3598412 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term270 A t x' x) = (term274 A t x' x).
Proof. exact (MK_COMB (@lem3598408 A t x') (@lem3598411 A x' x)). Qed.
Lemma lem3598415 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term269 A x' t x) = (term274 A t x' x).
Proof. exact (TRANS (@lem3598400 A t x' x) (@lem3598412 A t x' x)). Qed.
Lemma lem3598416 {A : Type'} (x' : A) (x : A) : (term261 A x' x) = (term261 A x' x).
Proof. exact (eq_refl (term261 A x' x)). Qed.
Lemma lem3598417 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term343 A x' t x) = (term344 A t x' x).
Proof. exact (MK_COMB (@lem3598416 A x' x) (@lem3598415 A t x' x)). Qed.
Lemma lem3598420 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term342 A x' t x) = (term344 A t x' x).
Proof. exact (TRANS (@lem3598392 A x' t x) (@lem3598417 A t x' x)). Qed.
Lemma lem3598421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3598422 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term345 A x' t x) = (term346 A t x' x).
Proof. exact (MK_COMB (@lem3598421) (@lem3598420 A t x' x)). Qed.
Lemma lem3598424 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3598425 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3598424 A P x). Qed.
Lemma lem3598426 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3598425 A t x'). Qed.
Lemma lem3598427 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : ((term342 A x' t x) = (@IN A x' t)) = ((term344 A t x' x) = (t x')).
Proof. exact (MK_COMB (@lem3598422 A t x' x) (@lem3598426 A t x')). Qed.
Lemma lem3598430 {A : Type'} (x : A) (t : A -> Prop) : (term347 A x t) = (term348 A x t).
Proof. exact (fun_ext (fun x' : A => @lem3598427 A x t x')). Qed.
Lemma lem3598431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3598432 {A : Type'} (x : A) (t : A -> Prop) : (term339 A x t) = (term349 A x t).
Proof. exact (MK_COMB (@lem3598431 A) (@lem3598430 A x t)). Qed.
Lemma lem3598437 {A : Type'} (x : A) (t : A -> Prop) : (term341 A x t) = (term350 A x t).
Proof. exact (MK_COMB (@lem3598382 A t x) (@lem3598432 A x t)). Qed.
Lemma lem3598440 {A : Type'} (x : A) (t : A -> Prop) : (term350 A x t) = (term341 A x t).
Proof. exact (SYM (@lem3598437 A x t)). Qed.
Lemma lem3598442 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3598443 {A : Type'} (x : A) (t : A -> Prop) : (term350 A x t) = (term351 A x t).
Proof. exact (@lem3598442 (term350 A x t)). Qed.
Lemma lem3598444 {A : Type'} (x : A) (t : A -> Prop) : (term351 A x t) = (term350 A x t).
Proof. exact (SYM (@lem3598443 A x t)). Qed.
Lemma lem3598445 {A : Type'} (x : A) (t : A -> Prop) (h1 : term352 A x t) : term352 A x t.
Proof. exact (h1). Qed.
Lemma lem3598448 {A : Type'} (x : A) (t : A -> Prop) (h1 : term351 A x t) : term351 A x t.
Proof. exact (h1). Qed.
Lemma lem3598449 {A : Type'} (x : A) (t : A -> Prop) : term353 A x t.
Proof. exact (fun h0 : term351 A x t => @lem3598448 A x t h0). Qed.
Lemma lem3598450 {A : Type'} (x : A) (t : A -> Prop) (h1 : term353 A x t) : term353 A x t.
Proof. exact (h1). Qed.
Lemma lem3598451 {A : Type'} (x : A) (t : A -> Prop) (h1 : term351 A x t) : term351 A x t.
Proof. exact (h1). Qed.
Lemma lem3598452 {A : Type'} (x : A) (t : A -> Prop) (h1 : term351 A x t) (h2 : term353 A x t) : term351 A x t.
Proof. exact (@lem3598450 A x t h2 (@lem3598451 A x t h1)). Qed.
Lemma lem3598453 {A : Type'} (x : A) (t : A -> Prop) (h1 : term351 A x t) : term354 A x t.
Proof. exact (fun h0 : term353 A x t => @lem3598452 A x t h1 h0). Qed.
Lemma lem3598454 {A : Type'} (x : A) (t : A -> Prop) (h1 : term353 A x t) : term353 A x t.
Proof. exact (h1). Qed.
Lemma lem3598455 {A : Type'} (x : A) (t : A -> Prop) (h1 : term351 A x t) (h2 : term353 A x t) : term351 A x t.
Proof. exact (@lem3598453 A x t h1 (@lem3598454 A x t h2)). Qed.
Lemma lem3598456 {A : Type'} (x : A) (t : A -> Prop) (h1 : term353 A x t) : term353 A x t.
Proof. exact (fun h0 : term351 A x t => @lem3598455 A x t h0 h1). Qed.
Lemma lem3598457 {A : Type'} (x : A) (t : A -> Prop) : term355 A x t.
Proof. exact (fun h0 : term353 A x t => @lem3598456 A x t h0). Qed.
Lemma lem3598460 {A : Type'} (x : A) (t : A -> Prop) : term353 A x t.
Proof. exact (@lem3598457 A x t (@lem3598449 A x t)). Qed.
Lemma lem3598461 {A : Type'} (x : A) (t : A -> Prop) : term353 A x t.
Proof. exact (@lem3598460 A x t). Qed.
Lemma lem3598471 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3598472 {A : Type'} (x : A) (t : A -> Prop) : (term351 A x t) = (term356 A x t).
Proof. exact (@lem3598471 (term352 A x t)). Qed.
Lemma lem3598474 (t : Prop) : (term189 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3598475 {A : Type'} (x : A) (t : A -> Prop) : (term356 A x t) = (term350 A x t).
Proof. exact (@lem3598474 (term350 A x t)). Qed.
Lemma lem3598478 {A : Type'} (x : A) (t : A -> Prop) : (term351 A x t) = (term350 A x t).
Proof. exact (TRANS (@lem3598472 A x t) (@lem3598475 A x t)). Qed.
Lemma lem3598487 {A : Type'} (t : A -> Prop) : (term357 A t) = (term358 A t).
Proof. exact (fun_ext (fun x : A => @lem3598478 A x t)). Qed.
Lemma lem3598488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3598489 {A : Type'} (t : A -> Prop) : (term359 A t) = (term360 A t).
Proof. exact (MK_COMB (@lem3598488 A) (@lem3598487 A t)). Qed.
Lemma lem3598494 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3598489 A t)). Qed.
Lemma lem3598495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3598504 {A : Type'} : (term363 A) = (term364 A).
Proof. exact (MK_COMB (@lem3598495 A) (@lem3598494 A)). Qed.
Lemma lem3598519 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : ((term344 A t x' x) = (t x')) = ((term344 A t x' x) = (t x')).
Proof. exact (eq_refl ((term344 A t x' x) = (t x'))). Qed.
Lemma lem3598520 {A : Type'} (x : A) (t : A -> Prop) : (term348 A x t) = (term348 A x t).
Proof. exact (fun_ext (fun x' : A => @lem3598519 A x t x')). Qed.
Lemma lem3598521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3598522 {A : Type'} (x : A) (t : A -> Prop) : (term349 A x t) = (term349 A x t).
Proof. exact (MK_COMB (@lem3598521 A) (@lem3598520 A x t)). Qed.
Lemma lem3598525 {A : Type'} (t : A -> Prop) (x : A) : (term258 A t x) = (term258 A t x).
Proof. exact (eq_refl (term258 A t x)). Qed.
Lemma lem3598526 {A : Type'} (x : A) (t : A -> Prop) : (term350 A x t) = (term350 A x t).
Proof. exact (MK_COMB (@lem3598525 A t x) (@lem3598522 A x t)). Qed.
Lemma lem3598527 {A : Type'} (t : A -> Prop) : (term358 A t) = (term358 A t).
Proof. exact (fun_ext (fun x : A => @lem3598526 A x t)). Qed.
Lemma lem3598528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3598529 {A : Type'} (t : A -> Prop) : (term360 A t) = (term360 A t).
Proof. exact (MK_COMB (@lem3598528 A) (@lem3598527 A t)). Qed.
Lemma lem3598530 {A : Type'} : (term362 A) = (term362 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3598529 A t)). Qed.
Lemma lem3598531 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3598532 {A : Type'} : (term364 A) = (term364 A).
Proof. exact (MK_COMB (@lem3598531 A) (@lem3598530 A)). Qed.
Lemma lem3598559 {A : Type'} : (term363 A) = (term364 A).
Proof. exact (TRANS (@lem3598504 A) (@lem3598532 A)). Qed.
Lemma lem3598560 {A : Type'} : (term364 A) = (term363 A).
Proof. exact (SYM (@lem3598559 A)). Qed.
Lemma lem3598563 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3598564 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : ((term344 A t x' x) = (t x')) = (term365 A x t x').
Proof. exact (@lem3598563 ((term344 A t x' x) = (t x'))). Qed.
Lemma lem3598565 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term365 A x t x') = ((term344 A t x' x) = (t x')).
Proof. exact (SYM (@lem3598564 A x t x')). Qed.
Lemma lem3598566 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term366 A x t x') : term366 A x t x'.
Proof. exact (h1). Qed.
Lemma lem3598572 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598580 {A : Type'} (x' : A) (x : A) : (term367 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3598582 {A : Type'} (t : A -> Prop) (x' : A) : (term368 A t x') = (term368 A t x').
Proof. exact (eq_refl (term368 A t x')). Qed.
Lemma lem3598583 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term369 A t x' x) = (term370 A t x' x).
Proof. exact (MK_COMB (@lem3598582 A t x') (@lem3598580 A x' x)). Qed.
Lemma lem3598584 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term371 A t x' x) = (term369 A t x' x).
Proof. exact (@lem17045 (t x') (term273 A x' x)). Qed.
Lemma lem3598585 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term371 A t x' x) = (term370 A t x' x).
Proof. exact (TRANS (@lem3598584 A t x' x) (@lem3598583 A t x' x)). Qed.
Lemma lem3598590 {A : Type'} (x' : A) (x : A) : (term372 A x' x) = (term372 A x' x).
Proof. exact (eq_refl (term372 A x' x)). Qed.
Lemma lem3598591 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term373 A t x' x) = (term374 A t x' x).
Proof. exact (MK_COMB (@lem3598590 A x' x) (@lem3598585 A t x' x)). Qed.
Lemma lem3598592 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term375 A t x' x) = (term373 A t x' x).
Proof. exact (@lem17160 (x' = x) (term274 A t x' x)). Qed.
Lemma lem3598593 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term375 A t x' x) = (term374 A t x' x).
Proof. exact (TRANS (@lem3598592 A t x' x) (@lem3598591 A t x' x)). Qed.
Lemma lem3598598 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (t x').
Proof. exact (eq_refl (t x')). Qed.
Lemma lem3598599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3598600 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term376 A t x' x) = (term377 A t x' x).
Proof. exact (MK_COMB (@lem3598599) (@lem3598593 A t x' x)). Qed.
Lemma lem3598601 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term378 A x t x') = (term379 A x t x').
Proof. exact (MK_COMB (@lem3598600 A t x' x) (@lem3598598 A t x')). Qed.
Lemma lem3598606 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term380 A x t x') = (term380 A x t x').
Proof. exact (eq_refl (term380 A x t x')). Qed.
Lemma lem3598607 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term381 A x t x') = (term382 A x t x').
Proof. exact (MK_COMB (@lem3598606 A x t x') (@lem3598601 A x t x')). Qed.
Lemma lem3598608 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term366 A x t x') = (term381 A x t x').
Proof. exact (@lem17646 (term344 A t x' x) (t x')). Qed.
Lemma lem3598613 {A : Type'} (x : A) (t : A -> Prop) (x' : A) : (term366 A x t x') = (term382 A x t x').
Proof. exact (TRANS (@lem3598608 A x t x') (@lem3598607 A x t x')). Qed.
Lemma lem3598618 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598680 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term366 A x t x') : term382 A x t x'.
Proof. exact (EQ_MP (@lem3598613 A x t x') (@lem3598566 A x t x' h1)). Qed.
Lemma lem3598681 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term383 A x t x') : term383 A x t x'.
Proof. exact (h1). Qed.
Lemma lem3598682 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : term379 A x t x'.
Proof. exact (h1). Qed.
Lemma lem3598684 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term383 A x t x') : term344 A t x' x.
Proof. exact (proj1 (@lem3598681 A x t x' h1)). Qed.
Lemma lem3598686 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term274 A t x' x.
Proof. exact (h1). Qed.
Lemma lem3598690 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : term374 A t x' x.
Proof. exact (proj1 (@lem3598682 A x t x' h1)). Qed.
Lemma lem3598691 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : term370 A t x' x.
Proof. exact (proj2 (@lem3598690 A x t x' h1)). Qed.
Lemma lem3598698 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598706 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3598738 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term302 A t x') : term302 A t x'.
Proof. exact (h1). Qed.
Lemma lem3598754 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3598756 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598758 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term383 A x t x') : term302 A t x'.
Proof. exact (proj2 (@lem3598681 A x t x' h1)). Qed.
Lemma lem3598760 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3598764 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term383 A x t x') : term302 A t x'.
Proof. exact (proj2 (@lem3598681 A x t x' h1)). Qed.
Lemma lem3598776 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term302 A t x') : term302 A t x'.
Proof. exact (h1). Qed.
Lemma lem3598782 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : term273 A x' x.
Proof. exact (proj1 (@lem3598690 A x t x' h1)). Qed.
Lemma lem3598784 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3598812 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598813 {A : Type'} (t : A -> Prop) : (term384 A t) = (term384 A t).
Proof. exact (eq_refl (term384 A t)). Qed.
Lemma lem3598814 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term385 A t x') = (term385 A t x).
Proof. exact (MK_COMB (@lem3598813 A t) (@lem3598760 A x' x h1)). Qed.
Lemma lem3598815 {A : Type'} (t : A -> Prop) (x : A) : (term385 A t x) = (term302 A t x).
Proof. exact (eq_refl (term385 A t x)). Qed.
Lemma lem3598816 {A : Type'} (t : A -> Prop) (x' : A) : (term386 A t x') = (term386 A t x').
Proof. exact (eq_refl (term386 A t x')). Qed.
Lemma lem3598817 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term385 A t x') = (term385 A t x)) = ((term385 A t x') = (term302 A t x)).
Proof. exact (MK_COMB (@lem3598816 A t x') (@lem3598815 A t x)). Qed.
Lemma lem3598818 {A : Type'} (t : A -> Prop) (x' : A) : (term385 A t x') = (term302 A t x').
Proof. exact (eq_refl (term385 A t x')). Qed.
Lemma lem3598819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3598820 {A : Type'} (t : A -> Prop) (x' : A) : (term386 A t x') = (term387 A t x').
Proof. exact (MK_COMB (@lem3598819) (@lem3598818 A t x')). Qed.
Lemma lem3598821 {A : Type'} (t : A -> Prop) (x : A) : (term302 A t x) = (term302 A t x).
Proof. exact (eq_refl (term302 A t x)). Qed.
Lemma lem3598822 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term385 A t x') = (term302 A t x)) = ((term302 A t x') = (term302 A t x)).
Proof. exact (MK_COMB (@lem3598820 A t x') (@lem3598821 A t x)). Qed.
Lemma lem3598823 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term385 A t x') = (term385 A t x)) = ((term302 A t x') = (term302 A t x)).
Proof. exact (TRANS (@lem3598817 A x' t x) (@lem3598822 A x' t x)). Qed.
Lemma lem3598824 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term302 A t x') = (term302 A t x).
Proof. exact (EQ_MP (@lem3598823 A x' t x) (@lem3598814 A t x' x h1)). Qed.
Lemma lem3598825 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term383 A x t x') (h2 : x' = x) : term302 A t x.
Proof. exact (EQ_MP (@lem3598824 A t x' x h2) (@lem3598758 A x t x' h1)). Qed.
Lemma lem3598867 {A : Type'} (x : A) : (term388 A x) = (term388 A x).
Proof. exact (eq_refl (term388 A x)). Qed.
Lemma lem3598868 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term389 A x x') = (term390 A x).
Proof. exact (MK_COMB (@lem3598867 A x) (@lem3598784 A x' x h1)). Qed.
Lemma lem3598869 {A : Type'} (x : A) : (term390 A x) = (term391 A x).
Proof. exact (eq_refl (term390 A x)). Qed.
Lemma lem3598870 {A : Type'} (x : A) (x' : A) : (term392 A x x') = (term392 A x x').
Proof. exact (eq_refl (term392 A x x')). Qed.
Lemma lem3598871 {A : Type'} (x' : A) (x : A) : ((term389 A x x') = (term390 A x)) = ((term389 A x x') = (term391 A x)).
Proof. exact (MK_COMB (@lem3598870 A x x') (@lem3598869 A x)). Qed.
Lemma lem3598872 {A : Type'} (x' : A) (x : A) : (term389 A x x') = (term273 A x' x).
Proof. exact (eq_refl (term389 A x x')). Qed.
Lemma lem3598873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3598874 {A : Type'} (x' : A) (x : A) : (term392 A x x') = (term393 A x' x).
Proof. exact (MK_COMB (@lem3598873) (@lem3598872 A x' x)). Qed.
Lemma lem3598875 {A : Type'} (x : A) : (term391 A x) = (term391 A x).
Proof. exact (eq_refl (term391 A x)). Qed.
Lemma lem3598876 {A : Type'} (x' : A) (x : A) : ((term389 A x x') = (term391 A x)) = ((term273 A x' x) = (term391 A x)).
Proof. exact (MK_COMB (@lem3598874 A x' x) (@lem3598875 A x)). Qed.
Lemma lem3598877 {A : Type'} (x' : A) (x : A) : ((term389 A x x') = (term390 A x)) = ((term273 A x' x) = (term391 A x)).
Proof. exact (TRANS (@lem3598871 A x' x) (@lem3598876 A x' x)). Qed.
Lemma lem3598878 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term273 A x' x) = (term391 A x).
Proof. exact (EQ_MP (@lem3598877 A x' x) (@lem3598868 A x' x h1)). Qed.
Lemma lem3598879 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : term391 A x.
Proof. exact (EQ_MP (@lem3598878 A x' x h2) (@lem3598782 A x t x' h1)). Qed.
Lemma lem3598881 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3598882 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term307 A t x.
Proof. exact (fun h0 : term302 A t x => @lem3598881 A t x h1). Qed.
Lemma lem3598884 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598885 {A : Type'} (t : A -> Prop) (x : A) : (term307 A t x) = (t x).
Proof. exact (@lem3598884 (t x)). Qed.
Lemma lem3598886 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3598885 A t x) (@lem3598882 A t x h1)). Qed.
Lemma lem3598889 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3598891 {A : Type'} (t : A -> Prop) (x : A) : (term302 A t x) = (term394 A t x).
Proof. exact (@lem3598889 (t x)). Qed.
Lemma lem3598894 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term383 A x t x') (h2 : x' = x) : term394 A t x.
Proof. exact (EQ_MP (@lem3598891 A t x) (@lem3598825 A t x' x h1 h2)). Qed.
Lemma lem3598897 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (@lem3598894 A t x' x h2 h3 (@lem3598886 A t x h1)). Qed.
Lemma lem3598898 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : term242.
Proof. exact (fun h0 : ~ False => @lem3598897 A t x' x h1 h2 h3). Qed.
Lemma lem3598900 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598901 : term242 = False.
Proof. exact (@lem3598900 False). Qed.
Lemma lem3598902 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3598901) (@lem3598898 A t x' x h1 h2 h3)). Qed.
Lemma lem3598918 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : t x'.
Proof. exact (proj1 (@lem3598686 A t x' x h1)). Qed.
Lemma lem3598919 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : term307 A t x'.
Proof. exact (fun h0 : term302 A t x' => @lem3598918 A t x' x h1). Qed.
Lemma lem3598921 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598922 {A : Type'} (t : A -> Prop) (x' : A) : (term307 A t x') = (t x').
Proof. exact (@lem3598921 (t x')). Qed.
Lemma lem3598923 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term274 A t x' x) : t x'.
Proof. exact (EQ_MP (@lem3598922 A t x') (@lem3598919 A t x' x h1)). Qed.
Lemma lem3598926 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3598928 {A : Type'} (t : A -> Prop) (x' : A) : (term302 A t x') = (term394 A t x').
Proof. exact (@lem3598926 (t x')). Qed.
Lemma lem3598931 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term383 A x t x') : term394 A t x'.
Proof. exact (EQ_MP (@lem3598928 A t x') (@lem3598764 A x t x' h1)). Qed.
Lemma lem3598934 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term274 A t x' x) (h2 : term383 A x t x') : False.
Proof. exact (@lem3598931 A x t x' h2 (@lem3598923 A t x' x h1)). Qed.
Lemma lem3598935 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term274 A t x' x) (h2 : term383 A x t x') : term242.
Proof. exact (fun h0 : ~ False => @lem3598934 A x t x' h1 h2). Qed.
Lemma lem3598937 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598938 : term242 = False.
Proof. exact (@lem3598937 False). Qed.
Lemma lem3598939 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term274 A t x' x) (h2 : term383 A x t x') : False.
Proof. exact (EQ_MP (@lem3598938) (@lem3598935 A x t x' h1 h2)). Qed.
Lemma lem3598955 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : t x'.
Proof. exact (proj2 (@lem3598682 A x t x' h1)). Qed.
Lemma lem3598956 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : term307 A t x'.
Proof. exact (fun h0 : term302 A t x' => @lem3598955 A x t x' h1). Qed.
Lemma lem3598958 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598959 {A : Type'} (t : A -> Prop) (x' : A) : (term307 A t x') = (t x').
Proof. exact (@lem3598958 (t x')). Qed.
Lemma lem3598960 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : t x'.
Proof. exact (EQ_MP (@lem3598959 A t x') (@lem3598956 A x t x' h1)). Qed.
Lemma lem3598963 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3598965 {A : Type'} (t : A -> Prop) (x' : A) : (term302 A t x') = (term394 A t x').
Proof. exact (@lem3598963 (t x')). Qed.
Lemma lem3598968 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term302 A t x') : term394 A t x'.
Proof. exact (EQ_MP (@lem3598965 A t x') (@lem3598776 A t x' h1)). Qed.
Lemma lem3598971 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : False.
Proof. exact (@lem3598968 A t x' h1 (@lem3598960 A x t x' h2)). Qed.
Lemma lem3598972 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : term242.
Proof. exact (fun h0 : ~ False => @lem3598971 A x t x' h1 h2). Qed.
Lemma lem3598974 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598975 : term242 = False.
Proof. exact (@lem3598974 False). Qed.
Lemma lem3598976 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : False.
Proof. exact (EQ_MP (@lem3598975) (@lem3598972 A x t x' h1 h2)). Qed.
Lemma lem3598992 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3598993 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3598992 A x). Qed.
Lemma lem3598994 {A : Type'} (x : A) : term395 A x.
Proof. exact (fun h0 : term391 A x => @lem3598993 A x). Qed.
Lemma lem3598996 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3598997 {A : Type'} (x : A) : (term395 A x) = (x = x).
Proof. exact (@lem3598996 (x = x)). Qed.
Lemma lem3598998 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3598997 A x) (@lem3598994 A x)). Qed.
Lemma lem3599001 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3599003 {A : Type'} (x : A) : (term391 A x) = (term396 A x).
Proof. exact (@lem3599001 (x = x)). Qed.
Lemma lem3599006 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : term396 A x.
Proof. exact (EQ_MP (@lem3599003 A x) (@lem3598879 A t x' x h1 h2)). Qed.
Lemma lem3599009 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : False.
Proof. exact (@lem3599006 A t x' x h1 h2 (@lem3598998 A x)). Qed.
Lemma lem3599010 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : term242.
Proof. exact (fun h0 : ~ False => @lem3599009 A t x' x h1 h2). Qed.
Lemma lem3599012 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3599013 : term242 = False.
Proof. exact (@lem3599012 False). Qed.
Lemma lem3599015 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599013) (@lem3599010 A t x' x h1 h2)). Qed.
Lemma lem3599016 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3598902 A t x' x h1 h2 h3) (fun h4 : False => @lem3598812 A t x h1)). Qed.
Lemma lem3599018 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599016 A t x' x h1 h2 h3) (@lem3598812 A t x h1)). Qed.
Lemma lem3599019 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3599015 A t x' x h1 h2) (fun h3 : False => @lem3598784 A x' x h2)). Qed.
Lemma lem3599020 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599019 A t x' x h1 h2) (@lem3598784 A x' x h2)). Qed.
Lemma lem3599021 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : (term302 A t x') = False.
Proof. exact (prop_ext (fun h3 : term302 A t x' => @lem3598976 A x t x' h1 h2) (fun h3 : False => @lem3598776 A t x' h1)). Qed.
Lemma lem3599022 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : False.
Proof. exact (EQ_MP (@lem3599021 A x t x' h1 h2) (@lem3598776 A t x' h1)). Qed.
Lemma lem3599023 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3599018 A t x' x h1 h2 h3) (fun h4 : False => @lem3598760 A x' x h3)). Qed.
Lemma lem3599024 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599023 A t x' x h1 h2 h3) (@lem3598760 A x' x h3)). Qed.
Lemma lem3599025 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3599024 A t x' x h1 h2 h3) (fun h4 : False => @lem3598756 A t x h1)). Qed.
Lemma lem3599026 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599025 A t x' x h1 h2 h3) (@lem3598756 A t x h1)). Qed.
Lemma lem3599027 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3599020 A t x' x h1 h2) (fun h3 : False => @lem3598754 A x' x h2)). Qed.
Lemma lem3599028 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599027 A t x' x h1 h2) (@lem3598754 A x' x h2)). Qed.
Lemma lem3599029 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : (term302 A t x') = False.
Proof. exact (prop_ext (fun h3 : term302 A t x' => @lem3599022 A x t x' h1 h2) (fun h3 : False => @lem3598738 A t x' h1)). Qed.
Lemma lem3599030 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : False.
Proof. exact (EQ_MP (@lem3599029 A x t x' h1 h2) (@lem3598738 A t x' h1)). Qed.
Lemma lem3599031 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3599026 A t x' x h1 h2 h3) (fun h4 : False => @lem3598706 A x' x h3)). Qed.
Lemma lem3599032 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599031 A t x' x h1 h2 h3) (@lem3598706 A x' x h3)). Qed.
Lemma lem3599033 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3599032 A t x' x h1 h2 h3) (fun h4 : False => @lem3598698 A t x h1)). Qed.
Lemma lem3599034 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599033 A t x' x h1 h2 h3) (@lem3598698 A t x h1)). Qed.
Lemma lem3599035 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3599028 A t x' x h1 h2) (fun h3 : False => @lem3598754 A x' x h2)). Qed.
Lemma lem3599036 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term379 A x t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599035 A t x' x h1 h2) (@lem3598754 A x' x h2)). Qed.
Lemma lem3599037 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : (term302 A t x') = False.
Proof. exact (prop_ext (fun h3 : term302 A t x' => @lem3599030 A x t x' h1 h2) (fun h3 : False => @lem3598738 A t x' h1)). Qed.
Lemma lem3599038 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x') (h2 : term379 A x t x') : False.
Proof. exact (EQ_MP (@lem3599037 A x t x' h1 h2) (@lem3598738 A t x' h1)). Qed.
Lemma lem3599039 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3599034 A t x' x h1 h2 h3) (fun h4 : False => @lem3598706 A x' x h3)). Qed.
Lemma lem3599040 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599039 A t x' x h1 h2 h3) (@lem3598706 A x' x h3)). Qed.
Lemma lem3599041 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3599040 A t x' x h1 h2 h3) (fun h4 : False => @lem3598698 A t x h1)). Qed.
Lemma lem3599042 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term383 A x t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3599041 A t x' x h1 h2 h3) (@lem3598698 A t x h1)). Qed.
Lemma lem3599043 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term379 A x t x') : False.
Proof. exact (or_elim (@lem3598691 A x t x' h1) (fun h0 : term302 A t x' => @lem3599038 A x t x' h0 h1) (fun h0 : x' = x => @lem3599036 A t x' x h1 h0)). Qed.
Lemma lem3599044 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : t x) (h2 : term383 A x t x') : False.
Proof. exact (or_elim (@lem3598684 A x t x' h2) (fun h0 : x' = x => @lem3599042 A t x' x h1 h2 h0) (fun h0 : term274 A t x' x => @lem3598939 A x t x' h0 h2)). Qed.
Lemma lem3599045 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : False.
Proof. exact (or_elim (@lem3598680 A x t x' h1) (fun h0 : term383 A x t x' => @lem3599044 A x t x' h2 h0) (fun h0 : term379 A x t x' => @lem3599043 A x t x' h0)). Qed.
Lemma lem3599046 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3599045 A x' t x h1 h2) (fun h3 : False => @lem3598618 A t x h2)). Qed.
Lemma lem3599047 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3599046 A x' t x h1 h2) (@lem3598618 A t x h2)). Qed.
Lemma lem3599048 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3599047 A x' t x h1 h2) (fun h3 : False => @lem3598572 A t x h2)). Qed.
Lemma lem3599049 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3599048 A x' t x h1 h2) (@lem3598572 A t x h2)). Qed.
Lemma lem3599050 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : (term366 A x t x') = False.
Proof. exact (prop_ext (fun h3 : term366 A x t x' => @lem3599049 A x' t x h1 h2) (fun h3 : False => @lem3598566 A x t x' h1)). Qed.
Lemma lem3599051 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : term366 A x t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3599050 A x' t x h1 h2) (@lem3598566 A x t x' h1)). Qed.
Lemma lem3599052 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : term365 A x t x'.
Proof. exact (fun h0 : term366 A x t x' => @lem3599051 A x' t x h0 h1). Qed.
Lemma lem3599053 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : (term344 A t x' x) = (t x').
Proof. exact (EQ_MP (@lem3598565 A x t x') (@lem3599052 A x' t x h1)). Qed.
Lemma lem3599058 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term349 A x t.
Proof. exact (fun x' : A => @lem3599053 A x' t x h1). Qed.
Lemma lem3599059 {A : Type'} (x : A) (t : A -> Prop) : term350 A x t.
Proof. exact (fun h0 : t x => @lem3599058 A t x h0). Qed.
Lemma lem3599064 {A : Type'} (t : A -> Prop) : term360 A t.
Proof. exact (fun x : A => @lem3599059 A x t). Qed.
Lemma lem3599069 {A : Type'} : term364 A.
Proof. exact (fun t : A -> Prop => @lem3599064 A t). Qed.
Lemma lem3599070 {A : Type'} : term363 A.
Proof. exact (EQ_MP (@lem3598560 A) (@lem3599069 A)). Qed.
Lemma lem3599071 {A : Type'} (t : A -> Prop) : term397 A t.
Proof. exact (@lem3599070 A t). Qed.
Lemma lem3599072 {A : Type'} (t : A -> Prop) : (term397 A t) = (term359 A t).
Proof. exact (eq_refl (term397 A t)). Qed.
Lemma lem3599073 {A : Type'} (t : A -> Prop) : term359 A t.
Proof. exact (EQ_MP (@lem3599072 A t) (@lem3599071 A t)). Qed.
Lemma lem3599074 {A : Type'} (t : A -> Prop) (x : A) : term398 A t x.
Proof. exact (@lem3599073 A t x). Qed.
Lemma lem3599075 {A : Type'} (x : A) (t : A -> Prop) : (term398 A t x) = (term351 A x t).
Proof. exact (eq_refl (term398 A t x)). Qed.
Lemma lem3599076 {A : Type'} (x : A) (t : A -> Prop) : term351 A x t.
Proof. exact (EQ_MP (@lem3599075 A x t) (@lem3599074 A t x)). Qed.
Lemma lem3599078 {A : Type'} (x : A) (t : A -> Prop) : term351 A x t.
Proof. exact (@lem3598461 A x t (@lem3599076 A x t)). Qed.
Lemma lem3599079 {A : Type'} (x : A) (t : A -> Prop) (h1 : term352 A x t) : False.
Proof. exact (@lem3599078 A x t (@lem3598445 A x t h1)). Qed.
Lemma lem3599080 {A : Type'} (x : A) (t : A -> Prop) (h1 : term352 A x t) : (term352 A x t) = False.
Proof. exact (prop_ext (fun h2 : term352 A x t => @lem3599079 A x t h1) (fun h2 : False => @lem3598445 A x t h1)). Qed.
Lemma lem3599081 {A : Type'} (x : A) (t : A -> Prop) (h1 : term352 A x t) : False.
Proof. exact (EQ_MP (@lem3599080 A x t h1) (@lem3598445 A x t h1)). Qed.
Lemma lem3599082 {A : Type'} (x : A) (t : A -> Prop) : term351 A x t.
Proof. exact (fun h0 : term352 A x t => @lem3599081 A x t h0). Qed.
Lemma lem3599083 {A : Type'} (x : A) (t : A -> Prop) : term350 A x t.
Proof. exact (EQ_MP (@lem3598444 A x t) (@lem3599082 A x t)). Qed.
Lemma lem3599084 {A : Type'} (x : A) (t : A -> Prop) : term341 A x t.
Proof. exact (EQ_MP (@lem3598440 A x t) (@lem3599083 A x t)). Qed.
Lemma lem3599085 {A : Type'} (x : A) (t : A -> Prop) : term340 A x t.
Proof. exact (EQ_MP (@lem3598374 A x t) (@lem3599084 A x t)). Qed.
Lemma lem3599086 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term332 A t x) = t.
Proof. exact (@lem3599085 A x t (@lem3596309 A x t h1)). Qed.
Lemma lem3599094 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3599099 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : (term332 A t x) = t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3599094 A t) (@lem3598339 A x t h1 h2)). Qed.
Lemma lem3599100 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : (term332 A t x) = t) : True = (@FINITE A t).
Proof. exact (SYM (@lem3599099 A x t h1 h2)). Qed.
Lemma lem3599102 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : (term332 A t x) = t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3599100 A x t h1 h2) (@lem0)). Qed.
Lemma lem3599103 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : @IN A x t) : ((term332 A t x) = t) = (@FINITE A t).
Proof. exact (prop_ext (fun h3 : (term332 A t x) = t => @lem3599102 A x t h1 h3) (fun h3 : @FINITE A t => @lem3599086 A x t h2)). Qed.
Lemma lem3599104 {A : Type'} (x : A) (t : A -> Prop) (h1 : term244 A t x) (h2 : @IN A x t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3599103 A x t h1 h2) (@lem3599086 A x t h2)). Qed.
Lemma lem3599105 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (h1). Qed.
Lemma lem3599106 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term63 A u s'.
Proof. exact (@lem3599105 A u h1 s'). Qed.
Lemma lem3599107 {A : Type'} (u : A -> Prop) (s' : A -> Prop) : (term63 A u s') = (term64 A u s').
Proof. exact (eq_refl (term63 A u s')). Qed.
Lemma lem3599108 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (EQ_MP (@lem3599107 A u s') (@lem3599106 A s' u h1)). Qed.
Lemma lem3599109 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A s' u) : @SUBSET A s' u.
Proof. exact (h1). Qed.
Lemma lem3599110 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) (h2 : @SUBSET A s' u) : @FINITE A s'.
Proof. exact (@lem3599108 A s' u h1 (@lem3599109 A s' u h2)). Qed.
Lemma lem3599111 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A s' u) : term246 A u s'.
Proof. exact (fun h0 : term72 A u => @lem3599110 A s' u h0 h1). Qed.
Lemma lem3599112 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (h1). Qed.
Lemma lem3599113 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) (h2 : @SUBSET A s' u) : @FINITE A s'.
Proof. exact (@lem3599111 A s' u h2 (@lem3599112 A u h1)). Qed.
Lemma lem3599114 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (fun h0 : @SUBSET A s' u => @lem3599113 A s' u h1 h0). Qed.
Lemma lem3599115 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (fun s' : A -> Prop => @lem3599114 A s' u h1). Qed.
Lemma lem3599116 {A : Type'} (u : A -> Prop) : term247 A u.
Proof. exact (fun h0 : term72 A u => @lem3599115 A u h0). Qed.
Lemma lem3599117 {A : Type'} (u : A -> Prop) (h1 : term72 A u) : term72 A u.
Proof. exact (@lem3599116 A u (@lem3597527 A u h1)). Qed.
Lemma lem3599118 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term63 A u s'.
Proof. exact (@lem3599117 A u h1 s'). Qed.
Lemma lem3599119 {A : Type'} (u : A -> Prop) (s' : A -> Prop) : (term63 A u s') = (term64 A u s').
Proof. exact (eq_refl (term63 A u s')). Qed.
Lemma lem3599122 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (EQ_MP (@lem3599119 A u s') (@lem3599118 A s' u h1)). Qed.
Lemma lem3599123 {A : Type'} (s' : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u s'.
Proof. exact (@lem3599122 A s' u h1). Qed.
Lemma lem3599124 {A : Type'} (t : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term64 A u t.
Proof. exact (@lem3599123 A t u h1). Qed.
Lemma lem3599130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3599131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (@lem3599130 A s t). Qed.
Lemma lem3599132 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term243 A t x u) = (term250 A t x u).
Proof. exact (@lem3599131 A t (@INSERT A x u)). Qed.
Lemma lem3599139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599140 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term251 A t x u) = (term252 A t x u).
Proof. exact (MK_COMB (@lem3599139) (@lem3599132 A t x u)). Qed.
Lemma lem3599142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3599143 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term249 A s t).
Proof. exact (@lem3599142 A s t). Qed.
Lemma lem3599144 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term249 A t u).
Proof. exact (@lem3599143 A t u). Qed.
Lemma lem3599151 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term399 A x t u) = (term400 A x t u).
Proof. exact (MK_COMB (@lem3599140 A t x u) (@lem3599144 A t u)). Qed.
Lemma lem3599154 {A : Type'} (x : A) (t : A -> Prop) : (term401 A x t) = (term401 A x t).
Proof. exact (eq_refl (term401 A x t)). Qed.
Lemma lem3599155 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term402 A x t u) = (term403 A x t u).
Proof. exact (MK_COMB (@lem3599154 A x t) (@lem3599151 A x t u)). Qed.
Lemma lem3599158 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term403 A x t u) = (term402 A x t u).
Proof. exact (SYM (@lem3599155 A x t u)). Qed.
Lemma lem3599162 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3599163 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3599162 A P x). Qed.
Lemma lem3599164 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3599163 A t x). Qed.
Lemma lem3599165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3599166 {A : Type'} (t : A -> Prop) (x : A) : (term2 A x t) = (term302 A t x).
Proof. exact (MK_COMB (@lem3599165) (@lem3599164 A t x)). Qed.
Lemma lem3599167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599168 {A : Type'} (t : A -> Prop) (x : A) : (term401 A x t) = (term404 A t x).
Proof. exact (MK_COMB (@lem3599167) (@lem3599166 A t x)). Qed.
Lemma lem3599178 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3599179 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3599178 A P x). Qed.
Lemma lem3599180 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3599179 A t x'). Qed.
Lemma lem3599181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599182 {A : Type'} (t : A -> Prop) (x' : A) : (term257 A x' t) = (term258 A t x').
Proof. exact (MK_COMB (@lem3599181) (@lem3599180 A t x')). Qed.
Lemma lem3599184 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3599185 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term259 A x y s) = (term260 A y x s).
Proof. exact (@lem3599184 A y x s). Qed.
Lemma lem3599186 {A : Type'} (x : A) (x' : A) (u : A -> Prop) : (term259 A x' x u) = (term260 A x x' u).
Proof. exact (@lem3599185 A x x' u). Qed.
Lemma lem3599192 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3599193 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3599192 A P x). Qed.
Lemma lem3599194 {A : Type'} (u : A -> Prop) (x' : A) : (@IN A x' u) = (u x').
Proof. exact (@lem3599193 A u x'). Qed.
Lemma lem3599195 {A : Type'} (x' : A) (x : A) : (term261 A x' x) = (term261 A x' x).
Proof. exact (eq_refl (term261 A x' x)). Qed.
Lemma lem3599196 {A : Type'} (x : A) (u : A -> Prop) (x' : A) : (term260 A x x' u) = (term262 A x u x').
Proof. exact (MK_COMB (@lem3599195 A x' x) (@lem3599194 A u x')). Qed.
Lemma lem3599199 {A : Type'} (x : A) (u : A -> Prop) (x' : A) : (term259 A x' x u) = (term262 A x u x').
Proof. exact (TRANS (@lem3599186 A x x' u) (@lem3599196 A x u x')). Qed.
Lemma lem3599200 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term263 A t x' x u) = (term264 A t x u x').
Proof. exact (MK_COMB (@lem3599182 A t x') (@lem3599199 A x u x')). Qed.
Lemma lem3599203 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term265 A t x u) = (term266 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3599200 A t x u x')). Qed.
Lemma lem3599204 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599205 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term250 A t x u) = (term267 A t x u).
Proof. exact (MK_COMB (@lem3599204 A) (@lem3599203 A t x u)). Qed.
Lemma lem3599210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599211 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term252 A t x u) = (term268 A t x u).
Proof. exact (MK_COMB (@lem3599210) (@lem3599205 A t x u)). Qed.
Lemma lem3599219 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3599220 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3599219 A P x). Qed.
Lemma lem3599221 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3599220 A t x). Qed.
Lemma lem3599222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599223 {A : Type'} (t : A -> Prop) (x : A) : (term257 A x t) = (term258 A t x).
Proof. exact (MK_COMB (@lem3599222) (@lem3599221 A t x)). Qed.
Lemma lem3599225 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3599226 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3599225 A P x). Qed.
Lemma lem3599227 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3599226 A u x). Qed.
Lemma lem3599228 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term405 A t x u) = (term406 A t u x).
Proof. exact (MK_COMB (@lem3599223 A t x) (@lem3599227 A u x)). Qed.
Lemma lem3599231 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term407 A t u) = (term408 A t u).
Proof. exact (fun_ext (fun x : A => @lem3599228 A t u x)). Qed.
Lemma lem3599232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599233 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term249 A t u) = (term409 A t u).
Proof. exact (MK_COMB (@lem3599232 A) (@lem3599231 A t u)). Qed.
Lemma lem3599238 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term400 A x t u) = (term410 A x t u).
Proof. exact (MK_COMB (@lem3599211 A t x u) (@lem3599233 A t u)). Qed.
Lemma lem3599241 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term403 A x t u) = (term411 A x t u).
Proof. exact (MK_COMB (@lem3599168 A t x) (@lem3599238 A x t u)). Qed.
Lemma lem3599244 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term411 A x t u) = (term403 A x t u).
Proof. exact (SYM (@lem3599241 A x t u)). Qed.
Lemma lem3599246 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3599247 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term411 A x t u) = (term412 A x t u).
Proof. exact (@lem3599246 (term411 A x t u)). Qed.
Lemma lem3599248 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term412 A x t u) = (term411 A x t u).
Proof. exact (SYM (@lem3599247 A x t u)). Qed.
Lemma lem3599249 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term413 A x t u) : term413 A x t u.
Proof. exact (h1). Qed.
Lemma lem3599252 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term412 A x t u) : term412 A x t u.
Proof. exact (h1). Qed.
Lemma lem3599253 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term414 A x t u.
Proof. exact (fun h0 : term412 A x t u => @lem3599252 A x t u h0). Qed.
Lemma lem3599254 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term414 A x t u) : term414 A x t u.
Proof. exact (h1). Qed.
Lemma lem3599255 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term412 A x t u) : term412 A x t u.
Proof. exact (h1). Qed.
Lemma lem3599256 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term412 A x t u) (h2 : term414 A x t u) : term412 A x t u.
Proof. exact (@lem3599254 A x t u h2 (@lem3599255 A x t u h1)). Qed.
Lemma lem3599257 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term412 A x t u) : term415 A x t u.
Proof. exact (fun h0 : term414 A x t u => @lem3599256 A x t u h1 h0). Qed.
Lemma lem3599258 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term414 A x t u) : term414 A x t u.
Proof. exact (h1). Qed.
Lemma lem3599259 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term412 A x t u) (h2 : term414 A x t u) : term412 A x t u.
Proof. exact (@lem3599257 A x t u h1 (@lem3599258 A x t u h2)). Qed.
Lemma lem3599260 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term414 A x t u) : term414 A x t u.
Proof. exact (fun h0 : term412 A x t u => @lem3599259 A x t u h0 h1). Qed.
Lemma lem3599261 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term416 A x t u.
Proof. exact (fun h0 : term414 A x t u => @lem3599260 A x t u h0). Qed.
Lemma lem3599264 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term414 A x t u.
Proof. exact (@lem3599261 A x t u (@lem3599253 A x t u)). Qed.
Lemma lem3599265 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term414 A x t u.
Proof. exact (@lem3599264 A x t u). Qed.
Lemma lem3599279 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3599280 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term412 A x t u) = (term417 A x t u).
Proof. exact (@lem3599279 (term413 A x t u)). Qed.
Lemma lem3599282 (t : Prop) : (term189 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3599283 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term417 A x t u) = (term411 A x t u).
Proof. exact (@lem3599282 (term411 A x t u)). Qed.
Lemma lem3599286 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term412 A x t u) = (term411 A x t u).
Proof. exact (TRANS (@lem3599280 A x t u) (@lem3599283 A x t u)). Qed.
Lemma lem3599303 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term418 A t u) = (term419 A t u).
Proof. exact (fun_ext (fun x : A => @lem3599286 A x t u)). Qed.
Lemma lem3599304 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599305 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term420 A t u) = (term421 A t u).
Proof. exact (MK_COMB (@lem3599304 A) (@lem3599303 A t u)). Qed.
Lemma lem3599310 {A : Type'} (u : A -> Prop) : (term422 A u) = (term423 A u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3599305 A t u)). Qed.
Lemma lem3599311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3599312 {A : Type'} (u : A -> Prop) : (term424 A u) = (term425 A u).
Proof. exact (MK_COMB (@lem3599311 A) (@lem3599310 A u)). Qed.
Lemma lem3599317 {A : Type'} : (term426 A) = (term427 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3599312 A u)). Qed.
Lemma lem3599318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3599327 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (MK_COMB (@lem3599318 A) (@lem3599317 A)). Qed.
Lemma lem3599332 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term406 A t u x) = (term406 A t u x).
Proof. exact (eq_refl (term406 A t u x)). Qed.
Lemma lem3599333 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term408 A t u) = (term408 A t u).
Proof. exact (fun_ext (fun x : A => @lem3599332 A t u x)). Qed.
Lemma lem3599334 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599335 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term409 A t u) = (term409 A t u).
Proof. exact (MK_COMB (@lem3599334 A) (@lem3599333 A t u)). Qed.
Lemma lem3599344 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term264 A t x u x') = (term264 A t x u x').
Proof. exact (eq_refl (term264 A t x u x')). Qed.
Lemma lem3599345 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term266 A t x u) = (term266 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3599344 A t x u x')). Qed.
Lemma lem3599346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599347 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term267 A t x u) = (term267 A t x u).
Proof. exact (MK_COMB (@lem3599346 A) (@lem3599345 A t x u)). Qed.
Lemma lem3599348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599349 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term268 A t x u) = (term268 A t x u).
Proof. exact (MK_COMB (@lem3599348) (@lem3599347 A t x u)). Qed.
Lemma lem3599350 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term410 A x t u) = (term410 A x t u).
Proof. exact (MK_COMB (@lem3599349 A t x u) (@lem3599335 A t u)). Qed.
Lemma lem3599355 {A : Type'} (t : A -> Prop) (x : A) : (term404 A t x) = (term404 A t x).
Proof. exact (eq_refl (term404 A t x)). Qed.
Lemma lem3599356 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term411 A x t u) = (term411 A x t u).
Proof. exact (MK_COMB (@lem3599355 A t x) (@lem3599350 A x t u)). Qed.
Lemma lem3599357 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term419 A t u) = (term419 A t u).
Proof. exact (fun_ext (fun x : A => @lem3599356 A x t u)). Qed.
Lemma lem3599358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599359 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term421 A t u) = (term421 A t u).
Proof. exact (MK_COMB (@lem3599358 A) (@lem3599357 A t u)). Qed.
Lemma lem3599360 {A : Type'} (u : A -> Prop) : (term423 A u) = (term423 A u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3599359 A t u)). Qed.
Lemma lem3599361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3599362 {A : Type'} (u : A -> Prop) : (term425 A u) = (term425 A u).
Proof. exact (MK_COMB (@lem3599361 A) (@lem3599360 A u)). Qed.
Lemma lem3599363 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3599362 A u)). Qed.
Lemma lem3599364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3599365 {A : Type'} : (term429 A) = (term429 A).
Proof. exact (MK_COMB (@lem3599364 A) (@lem3599363 A)). Qed.
Lemma lem3599408 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (TRANS (@lem3599327 A) (@lem3599365 A)). Qed.
Lemma lem3599409 {A : Type'} : (term429 A) = (term428 A).
Proof. exact (SYM (@lem3599408 A)). Qed.
Lemma lem3599411 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term267 A t x u.
Proof. exact (h1). Qed.
Lemma lem3599414 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3599415 {A : Type'} (u : A -> Prop) (x' : A) : (u x') = (term301 A u x').
Proof. exact (@lem3599414 (u x')). Qed.
Lemma lem3599416 {A : Type'} (u : A -> Prop) (x' : A) : (term301 A u x') = (u x').
Proof. exact (SYM (@lem3599415 A u x')). Qed.
Lemma lem3599417 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3599423 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (h1). Qed.
Lemma lem3599434 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term264 A t x u x') = (term303 A t x u x').
Proof. exact (@lem17265 (t x') (term262 A x u x')). Qed.
Lemma lem3599435 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term266 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3599434 A t x u x')). Qed.
Lemma lem3599436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599489 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term267 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3599436 A) (@lem3599435 A t x u)). Qed.
Lemma lem3599490 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3599489 A t x u) (@lem3599411 A t x u h1)). Qed.
Lemma lem3599496 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599502 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3599508 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (h1). Qed.
Lemma lem3599527 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term303 A t x u x') = (term303 A t x u x').
Proof. exact (eq_refl (term303 A t x u x')). Qed.
Lemma lem3599528 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term304 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3599527 A t x u x')). Qed.
Lemma lem3599529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599530 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term305 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3599529 A) (@lem3599528 A t x u)). Qed.
Lemma lem3599531 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3599530 A t x u) (@lem3599490 A t x u h1)). Qed.
Lemma lem3599535 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599541 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3599545 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (h1). Qed.
Lemma lem3599559 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (x' : A) : (term303 A t x u x') = (term303 A t x u x').
Proof. exact (eq_refl (term303 A t x u x')). Qed.
Lemma lem3599560 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term304 A t x u) = (term304 A t x u).
Proof. exact (fun_ext (fun x' : A => @lem3599559 A t x u x')). Qed.
Lemma lem3599561 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3599563 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term305 A t x u) = (term305 A t x u).
Proof. exact (MK_COMB (@lem3599561 A) (@lem3599560 A t x u)). Qed.
Lemma lem3599564 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term305 A t x u.
Proof. exact (EQ_MP (@lem3599563 A t x u) (@lem3599531 A t x u h1)). Qed.
Lemma lem3599568 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599572 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3599573 {A : Type'} (_39013 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term306 A t x u _39013.
Proof. exact (@lem3599564 A t x u h1 _39013). Qed.
Lemma lem3599574 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (_39013 : A) : (term306 A t x u _39013) = (term303 A t x u _39013).
Proof. exact (eq_refl (term306 A t x u _39013)). Qed.
Lemma lem3599577 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (h1). Qed.
Lemma lem3599587 {A : Type'} (_39013 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term303 A t x u _39013.
Proof. exact (EQ_MP (@lem3599574 A t x u _39013) (@lem3599573 A _39013 t x u h1)). Qed.
Lemma lem3599589 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599591 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term302 A u x'.
Proof. exact (h1). Qed.
Lemma lem3599604 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3599605 {A : Type'} (_39016 : A) (_39017 : A) (h1 : _39016 = _39017) : _39016 = _39017.
Proof. exact (h1). Qed.
Lemma lem3599606 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) (h1 : _39016 = _39017) : (t _39016) = (t _39017).
Proof. exact (MK_COMB (@lem3599604 A t) (@lem3599605 A _39016 _39017 h1)). Qed.
Lemma lem3599608 (b : Prop) (a : Prop) : term174 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3599609 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : term430 A _39017 t _39016.
Proof. exact (@lem3599608 (t _39017) (t _39016)). Qed.
Lemma lem3599610 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) (h1 : _39016 = _39017) : term431 A _39017 t _39016.
Proof. exact (@lem3599609 A _39017 t _39016 (@lem3599606 A t _39016 _39017 h1)). Qed.
Lemma lem3599611 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : term432 A _39017 t _39016.
Proof. exact (fun h0 : _39016 = _39017 => @lem3599610 A t _39016 _39017 h0). Qed.
Lemma lem3599613 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3599614 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : (term432 A _39017 t _39016) = (term433 A _39017 t _39016).
Proof. exact (@lem3599613 (_39016 = _39017) (term431 A _39017 t _39016)). Qed.
Lemma lem3599615 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : term433 A _39017 t _39016.
Proof. exact (EQ_MP (@lem3599614 A _39017 t _39016) (@lem3599611 A _39017 t _39016)). Qed.
Lemma lem3599619 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599620 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term307 A t x'.
Proof. exact (fun h0 : term302 A t x' => @lem3599619 A t x' h1). Qed.
Lemma lem3599622 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3599623 {A : Type'} (t : A -> Prop) (x' : A) : (term307 A t x') = (t x').
Proof. exact (@lem3599622 (t x')). Qed.
Lemma lem3599624 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3599623 A t x') (@lem3599620 A t x' h1)). Qed.
Lemma lem3599626 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (h1). Qed.
Lemma lem3599627 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term308 A t x.
Proof. exact (fun h0 : t x => @lem3599626 A t x h1). Qed.
Lemma lem3599629 (p : Prop) : (term309 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3599630 {A : Type'} (t : A -> Prop) (x : A) : (term308 A t x) = (term302 A t x).
Proof. exact (@lem3599629 (t x)). Qed.
Lemma lem3599631 {A : Type'} (t : A -> Prop) (x : A) (h1 : term302 A t x) : term302 A t x.
Proof. exact (EQ_MP (@lem3599630 A t x) (@lem3599627 A t x h1)). Qed.
Lemma lem3599633 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3599634 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term307 A t x'.
Proof. exact (fun h0 : term302 A t x' => @lem3599633 A t x' h1). Qed.
Lemma lem3599636 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3599637 {A : Type'} (t : A -> Prop) (x' : A) : (term307 A t x') = (t x').
Proof. exact (@lem3599636 (t x')). Qed.
Lemma lem3599638 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3599637 A t x') (@lem3599634 A t x' h1)). Qed.
Lemma lem3599640 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3599641 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) : (term433 A _39017 t _39016) = (term434 A t _39016 _39017).
Proof. exact (@lem3599640 (term431 A _39017 t _39016) (term273 A _39016 _39017)). Qed.
Lemma lem3599643 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3599644 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : (term435 A _39017 t _39016) = (term436 A _39017 t _39016).
Proof. exact (@lem3599643 (t _39017) (term302 A t _39016)). Qed.
Lemma lem3599646 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3599647 {A : Type'} (t : A -> Prop) (_39016 : A) : (term320 A t _39016) = (t _39016).
Proof. exact (@lem3599646 (t _39016)). Qed.
Lemma lem3599648 {A : Type'} (t : A -> Prop) (_39017 : A) : (term437 A t _39017) = (term437 A t _39017).
Proof. exact (eq_refl (term437 A t _39017)). Qed.
Lemma lem3599649 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : (term436 A _39017 t _39016) = (term438 A _39017 t _39016).
Proof. exact (MK_COMB (@lem3599648 A t _39017) (@lem3599647 A t _39016)). Qed.
Lemma lem3599650 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : (term435 A _39017 t _39016) = (term438 A _39017 t _39016).
Proof. exact (TRANS (@lem3599644 A _39017 t _39016) (@lem3599649 A _39017 t _39016)). Qed.
Lemma lem3599651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599652 {A : Type'} (_39017 : A) (t : A -> Prop) (_39016 : A) : (term439 A _39017 t _39016) = (term440 A _39017 t _39016).
Proof. exact (MK_COMB (@lem3599651) (@lem3599650 A _39017 t _39016)). Qed.
Lemma lem3599653 {A : Type'} (_39016 : A) (_39017 : A) : (term273 A _39016 _39017) = (term273 A _39016 _39017).
Proof. exact (eq_refl (term273 A _39016 _39017)). Qed.
Lemma lem3599654 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) : (term434 A t _39016 _39017) = (term441 A t _39016 _39017).
Proof. exact (MK_COMB (@lem3599652 A _39017 t _39016) (@lem3599653 A _39016 _39017)). Qed.
Lemma lem3599655 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) : (term433 A _39017 t _39016) = (term441 A t _39016 _39017).
Proof. exact (TRANS (@lem3599641 A t _39016 _39017) (@lem3599654 A t _39016 _39017)). Qed.
Lemma lem3599657 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x) (h2 : t x') : term438 A x t x'.
Proof. exact (conj (@lem3599631 A t x h1) (@lem3599638 A t x' h2)). Qed.
Lemma lem3599659 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) : term441 A t _39016 _39017.
Proof. exact (EQ_MP (@lem3599655 A t _39016 _39017) (@lem3599615 A _39017 t _39016)). Qed.
Lemma lem3599660 {A : Type'} (t : A -> Prop) (_39016 : A) (_39017 : A) : term441 A t _39016 _39017.
Proof. exact (@lem3599659 A t _39016 _39017). Qed.
Lemma lem3599661 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : term441 A t x' x.
Proof. exact (@lem3599660 A t x' x). Qed.
Lemma lem3599664 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x) (h2 : t x') : term273 A x' x.
Proof. exact (@lem3599661 A t x' x (@lem3599657 A x t x' h1 h2)). Qed.
Lemma lem3599665 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x) (h2 : t x') : term442 A x' x.
Proof. exact (fun h0 : x' = x => @lem3599664 A x t x' h1 h2). Qed.
Lemma lem3599667 (p : Prop) : (term309 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3599668 {A : Type'} (x' : A) (x : A) : (term442 A x' x) = (term273 A x' x).
Proof. exact (@lem3599667 (x' = x)). Qed.
Lemma lem3599669 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x) (h2 : t x') : term273 A x' x.
Proof. exact (EQ_MP (@lem3599668 A x' x) (@lem3599665 A x t x' h1 h2)). Qed.
Lemma lem3599675 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3599676 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (_39013 : A) : (term303 A t x u _39013) = (term310 A x t u _39013).
Proof. exact (@lem3599675 (_39013 = x) (term302 A t _39013) (u _39013)). Qed.
Lemma lem3599692 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3599693 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39013 : A) : (term311 A t u _39013) = (term312 A u t _39013).
Proof. exact (@lem3599692 (u _39013) (term302 A t _39013)). Qed.
Lemma lem3599699 {A : Type'} (_39013 : A) (x : A) : (term261 A _39013 x) = (term261 A _39013 x).
Proof. exact (eq_refl (term261 A _39013 x)). Qed.
Lemma lem3599700 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (_39013 : A) : (term310 A x t u _39013) = (term313 A x u t _39013).
Proof. exact (MK_COMB (@lem3599699 A _39013 x) (@lem3599693 A u t _39013)). Qed.
Lemma lem3599704 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3599705 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : (term313 A x u t _39013) = (term314 A u x t _39013).
Proof. exact (@lem3599704 (u _39013) (_39013 = x) (term302 A t _39013)). Qed.
Lemma lem3599723 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : (term310 A x t u _39013) = (term314 A u x t _39013).
Proof. exact (TRANS (@lem3599700 A x u t _39013) (@lem3599705 A u x t _39013)). Qed.
Lemma lem3599724 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : (term303 A t x u _39013) = (term314 A u x t _39013).
Proof. exact (TRANS (@lem3599676 A x t u _39013) (@lem3599723 A u x t _39013)). Qed.
Lemma lem3599725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3599726 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : (term315 A t x u _39013) = (term316 A u x t _39013).
Proof. exact (MK_COMB (@lem3599725) (@lem3599724 A u x t _39013)). Qed.
Lemma lem3599740 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3599741 {A : Type'} (x : A) (t : A -> Prop) (_39013 : A) : (term370 A t _39013 x) = (term443 A x t _39013).
Proof. exact (@lem3599740 (_39013 = x) (term302 A t _39013)). Qed.
Lemma lem3599749 {A : Type'} (u : A -> Prop) (_39013 : A) : (term444 A u _39013) = (term444 A u _39013).
Proof. exact (eq_refl (term444 A u _39013)). Qed.
Lemma lem3599750 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : (term445 A u t _39013 x) = (term314 A u x t _39013).
Proof. exact (MK_COMB (@lem3599749 A u _39013) (@lem3599741 A x t _39013)). Qed.
Lemma lem3599761 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : ((term303 A t x u _39013) = (term445 A u t _39013 x)) = ((term314 A u x t _39013) = (term314 A u x t _39013)).
Proof. exact (MK_COMB (@lem3599726 A u x t _39013) (@lem3599750 A u x t _39013)). Qed.
Lemma lem3599763 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3599764 (x : Prop) : (x = x) = True.
Proof. exact (@lem3599763 Prop x). Qed.
Lemma lem3599765 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (_39013 : A) : ((term314 A u x t _39013) = (term314 A u x t _39013)) = True.
Proof. exact (@lem3599764 (term314 A u x t _39013)). Qed.
Lemma lem3599766 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39013 : A) (x : A) : ((term303 A t x u _39013) = (term445 A u t _39013 x)) = True.
Proof. exact (TRANS (@lem3599761 A u x t _39013) (@lem3599765 A u x t _39013)). Qed.
Lemma lem3599767 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39013 : A) (x : A) : True = ((term303 A t x u _39013) = (term445 A u t _39013 x)).
Proof. exact (SYM (@lem3599766 A u t _39013 x)). Qed.
Lemma lem3599768 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_39013 : A) (x : A) : (term303 A t x u _39013) = (term445 A u t _39013 x).
Proof. exact (EQ_MP (@lem3599767 A u t _39013 x) (@lem0)). Qed.
Lemma lem3599769 {A : Type'} (_39013 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term445 A u t _39013 x.
Proof. exact (EQ_MP (@lem3599768 A u t _39013 x) (@lem3599587 A _39013 t x u h1)). Qed.
Lemma lem3599771 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3599772 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (_39013 : A) : (term445 A u t _39013 x) = (term446 A t x u _39013).
Proof. exact (@lem3599771 (term370 A t _39013 x) (u _39013)). Qed.
Lemma lem3599774 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3599775 {A : Type'} (t : A -> Prop) (_39013 : A) (x : A) : (term447 A t _39013 x) = (term448 A t _39013 x).
Proof. exact (@lem3599774 (term302 A t _39013) (_39013 = x)). Qed.
Lemma lem3599777 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3599778 {A : Type'} (t : A -> Prop) (_39013 : A) : (term320 A t _39013) = (t _39013).
Proof. exact (@lem3599777 (t _39013)). Qed.
Lemma lem3599779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3599780 {A : Type'} (t : A -> Prop) (_39013 : A) : (term321 A t _39013) = (term272 A t _39013).
Proof. exact (MK_COMB (@lem3599779) (@lem3599778 A t _39013)). Qed.
Lemma lem3599781 {A : Type'} (_39013 : A) (x : A) : (term273 A _39013 x) = (term273 A _39013 x).
Proof. exact (eq_refl (term273 A _39013 x)). Qed.
Lemma lem3599782 {A : Type'} (t : A -> Prop) (_39013 : A) (x : A) : (term448 A t _39013 x) = (term274 A t _39013 x).
Proof. exact (MK_COMB (@lem3599780 A t _39013) (@lem3599781 A _39013 x)). Qed.
Lemma lem3599783 {A : Type'} (t : A -> Prop) (_39013 : A) (x : A) : (term447 A t _39013 x) = (term274 A t _39013 x).
Proof. exact (TRANS (@lem3599775 A t _39013 x) (@lem3599782 A t _39013 x)). Qed.
Lemma lem3599784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3599785 {A : Type'} (t : A -> Prop) (_39013 : A) (x : A) : (term449 A t _39013 x) = (term276 A t _39013 x).
Proof. exact (MK_COMB (@lem3599784) (@lem3599783 A t _39013 x)). Qed.
Lemma lem3599786 {A : Type'} (u : A -> Prop) (_39013 : A) : (u _39013) = (u _39013).
Proof. exact (eq_refl (u _39013)). Qed.
Lemma lem3599787 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (_39013 : A) : (term446 A t x u _39013) = (term278 A t x u _39013).
Proof. exact (MK_COMB (@lem3599785 A t _39013 x) (@lem3599786 A u _39013)). Qed.
Lemma lem3599788 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (_39013 : A) : (term445 A u t _39013 x) = (term278 A t x u _39013).
Proof. exact (TRANS (@lem3599772 A t x u _39013) (@lem3599787 A t x u _39013)). Qed.
Lemma lem3599790 {A : Type'} (x : A) (t : A -> Prop) (x' : A) (h1 : term302 A t x) (h2 : t x') : term274 A t x' x.
Proof. exact (conj (@lem3599624 A t x' h2) (@lem3599669 A x t x' h1 h2)). Qed.
Lemma lem3599792 {A : Type'} (_39013 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term278 A t x u _39013.
Proof. exact (EQ_MP (@lem3599788 A t x u _39013) (@lem3599769 A _39013 t x u h1)). Qed.
Lemma lem3599793 {A : Type'} (_39013 : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term278 A t x u _39013.
Proof. exact (@lem3599792 A _39013 t x u h1). Qed.
Lemma lem3599794 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term267 A t x u) : term278 A t x u x'.
Proof. exact (@lem3599793 A x' t x u h1). Qed.
Lemma lem3599797 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : t x') : u x'.
Proof. exact (@lem3599794 A x' t x u h1 (@lem3599790 A x t x' h2 h3)). Qed.
Lemma lem3599798 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : t x') : term307 A u x'.
Proof. exact (fun h0 : term302 A u x' => @lem3599797 A u x t x' h1 h2 h3). Qed.
Lemma lem3599800 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3599801 {A : Type'} (u : A -> Prop) (x' : A) : (term307 A u x') = (u x').
Proof. exact (@lem3599800 (u x')). Qed.
Lemma lem3599802 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : t x') : u x'.
Proof. exact (EQ_MP (@lem3599801 A u x') (@lem3599798 A u x t x' h1 h2 h3)). Qed.
Lemma lem3599805 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3599807 {A : Type'} (u : A -> Prop) (x' : A) : (term302 A u x') = (term394 A u x').
Proof. exact (@lem3599805 (u x')). Qed.
Lemma lem3599810 {A : Type'} (u : A -> Prop) (x' : A) (h1 : term302 A u x') : term394 A u x'.
Proof. exact (EQ_MP (@lem3599807 A u x') (@lem3599591 A u x' h1)). Qed.
Lemma lem3599813 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (@lem3599810 A u x' h3 (@lem3599802 A u x t x' h1 h2 h4)). Qed.
Lemma lem3599814 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : term242.
Proof. exact (fun h0 : ~ False => @lem3599813 A x u t x' h1 h2 h3 h4). Qed.
Lemma lem3599816 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3599817 : term242 = False.
Proof. exact (@lem3599816 False). Qed.
Lemma lem3599818 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599817) (@lem3599814 A x u t x' h1 h2 h3 h4)). Qed.
Lemma lem3599819 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599818 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599591 A u x' h3)). Qed.
Lemma lem3599820 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599819 A x u t x' h1 h2 h3 h4) (@lem3599591 A u x' h3)). Qed.
Lemma lem3599821 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (t x') = False.
Proof. exact (prop_ext (fun h5 : t x' => @lem3599820 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599589 A t x' h4)). Qed.
Lemma lem3599822 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599821 A x u t x' h1 h2 h3 h4) (@lem3599589 A t x' h4)). Qed.
Lemma lem3599823 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A t x) = False.
Proof. exact (prop_ext (fun h5 : term302 A t x => @lem3599822 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599577 A t x h2)). Qed.
Lemma lem3599824 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599823 A x u t x' h1 h2 h3 h4) (@lem3599577 A t x h2)). Qed.
Lemma lem3599825 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599824 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599572 A u x' h3)). Qed.
Lemma lem3599826 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599825 A x u t x' h1 h2 h3 h4) (@lem3599572 A u x' h3)). Qed.
Lemma lem3599827 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (t x') = False.
Proof. exact (prop_ext (fun h5 : t x' => @lem3599826 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599568 A t x' h4)). Qed.
Lemma lem3599828 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599827 A x u t x' h1 h2 h3 h4) (@lem3599568 A t x' h4)). Qed.
Lemma lem3599829 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A t x) = False.
Proof. exact (prop_ext (fun h5 : term302 A t x => @lem3599828 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599545 A t x h2)). Qed.
Lemma lem3599830 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599829 A x u t x' h1 h2 h3 h4) (@lem3599545 A t x h2)). Qed.
Lemma lem3599831 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599830 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599572 A u x' h3)). Qed.
Lemma lem3599832 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599831 A x u t x' h1 h2 h3 h4) (@lem3599572 A u x' h3)). Qed.
Lemma lem3599833 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (t x') = False.
Proof. exact (prop_ext (fun h5 : t x' => @lem3599832 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599568 A t x' h4)). Qed.
Lemma lem3599834 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599833 A x u t x' h1 h2 h3 h4) (@lem3599568 A t x' h4)). Qed.
Lemma lem3599835 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A t x) = False.
Proof. exact (prop_ext (fun h5 : term302 A t x => @lem3599834 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599545 A t x h2)). Qed.
Lemma lem3599836 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599835 A x u t x' h1 h2 h3 h4) (@lem3599545 A t x h2)). Qed.
Lemma lem3599837 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599836 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599541 A u x' h3)). Qed.
Lemma lem3599838 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599837 A x u t x' h1 h2 h3 h4) (@lem3599541 A u x' h3)). Qed.
Lemma lem3599839 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (t x') = False.
Proof. exact (prop_ext (fun h5 : t x' => @lem3599838 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599535 A t x' h4)). Qed.
Lemma lem3599840 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599839 A x u t x' h1 h2 h3 h4) (@lem3599535 A t x' h4)). Qed.
Lemma lem3599841 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A t x) = False.
Proof. exact (prop_ext (fun h5 : term302 A t x => @lem3599840 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599508 A t x h2)). Qed.
Lemma lem3599842 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599841 A x u t x' h1 h2 h3 h4) (@lem3599508 A t x h2)). Qed.
Lemma lem3599843 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599842 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599502 A u x' h3)). Qed.
Lemma lem3599844 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599843 A x u t x' h1 h2 h3 h4) (@lem3599502 A u x' h3)). Qed.
Lemma lem3599845 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (t x') = False.
Proof. exact (prop_ext (fun h5 : t x' => @lem3599844 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599496 A t x' h4)). Qed.
Lemma lem3599846 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599845 A x u t x' h1 h2 h3 h4) (@lem3599496 A t x' h4)). Qed.
Lemma lem3599847 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A t x) = False.
Proof. exact (prop_ext (fun h5 : term302 A t x => @lem3599846 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599423 A t x h2)). Qed.
Lemma lem3599848 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599847 A x u t x' h1 h2 h3 h4) (@lem3599423 A t x h2)). Qed.
Lemma lem3599849 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : (term302 A u x') = False.
Proof. exact (prop_ext (fun h5 : term302 A u x' => @lem3599848 A x u t x' h1 h2 h3 h4) (fun h5 : False => @lem3599417 A u x' h3)). Qed.
Lemma lem3599850 {A : Type'} (x : A) (u : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : term302 A u x') (h4 : t x') : False.
Proof. exact (EQ_MP (@lem3599849 A x u t x' h1 h2 h3 h4) (@lem3599417 A u x' h3)). Qed.
Lemma lem3599851 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : t x') : term301 A u x'.
Proof. exact (fun h0 : term302 A u x' => @lem3599850 A x u t x' h1 h2 h0 h3). Qed.
Lemma lem3599852 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (x' : A) (h1 : term267 A t x u) (h2 : term302 A t x) (h3 : t x') : u x'.
Proof. exact (EQ_MP (@lem3599416 A u x') (@lem3599851 A u x t x' h1 h2 h3)). Qed.
Lemma lem3599853 {A : Type'} (x' : A) (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term267 A t x u) (h2 : term302 A t x) : term406 A t u x'.
Proof. exact (fun h0 : t x' => @lem3599852 A u x t x' h1 h2 h0). Qed.
Lemma lem3599858 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term267 A t x u) (h2 : term302 A t x) : term409 A t u.
Proof. exact (fun x' : A => @lem3599853 A x' u t x h1 h2). Qed.
Lemma lem3599859 {A : Type'} (u : A -> Prop) (t : A -> Prop) (x : A) (h1 : term302 A t x) : term410 A x t u.
Proof. exact (fun h0 : term267 A t x u => @lem3599858 A u t x h0 h1). Qed.
Lemma lem3599860 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term411 A x t u.
Proof. exact (fun h0 : term302 A t x => @lem3599859 A u t x h0). Qed.
Lemma lem3599865 {A : Type'} (t : A -> Prop) (u : A -> Prop) : term421 A t u.
Proof. exact (fun x : A => @lem3599860 A x t u). Qed.
Lemma lem3599870 {A : Type'} (u : A -> Prop) : term425 A u.
Proof. exact (fun t : A -> Prop => @lem3599865 A t u). Qed.
Lemma lem3599875 {A : Type'} : term429 A.
Proof. exact (fun u : A -> Prop => @lem3599870 A u). Qed.
Lemma lem3599876 {A : Type'} : term428 A.
Proof. exact (EQ_MP (@lem3599409 A) (@lem3599875 A)). Qed.
Lemma lem3599877 {A : Type'} (u : A -> Prop) : term450 A u.
Proof. exact (@lem3599876 A u). Qed.
Lemma lem3599878 {A : Type'} (u : A -> Prop) : (term450 A u) = (term424 A u).
Proof. exact (eq_refl (term450 A u)). Qed.
Lemma lem3599879 {A : Type'} (u : A -> Prop) : term424 A u.
Proof. exact (EQ_MP (@lem3599878 A u) (@lem3599877 A u)). Qed.
Lemma lem3599880 {A : Type'} (u : A -> Prop) (t : A -> Prop) : term451 A u t.
Proof. exact (@lem3599879 A u t). Qed.
Lemma lem3599881 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term451 A u t) = (term420 A t u).
Proof. exact (eq_refl (term451 A u t)). Qed.
Lemma lem3599882 {A : Type'} (t : A -> Prop) (u : A -> Prop) : term420 A t u.
Proof. exact (EQ_MP (@lem3599881 A t u) (@lem3599880 A u t)). Qed.
Lemma lem3599883 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : term452 A t u x.
Proof. exact (@lem3599882 A t u x). Qed.
Lemma lem3599884 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : (term452 A t u x) = (term412 A x t u).
Proof. exact (eq_refl (term452 A t u x)). Qed.
Lemma lem3599885 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term412 A x t u.
Proof. exact (EQ_MP (@lem3599884 A x t u) (@lem3599883 A t u x)). Qed.
Lemma lem3599887 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term412 A x t u.
Proof. exact (@lem3599265 A x t u (@lem3599885 A x t u)). Qed.
Lemma lem3599888 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term413 A x t u) : False.
Proof. exact (@lem3599887 A x t u (@lem3599249 A x t u h1)). Qed.
Lemma lem3599889 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term413 A x t u) : (term413 A x t u) = False.
Proof. exact (prop_ext (fun h2 : term413 A x t u => @lem3599888 A x t u h1) (fun h2 : False => @lem3599249 A x t u h1)). Qed.
Lemma lem3599890 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term413 A x t u) : False.
Proof. exact (EQ_MP (@lem3599889 A x t u h1) (@lem3599249 A x t u h1)). Qed.
Lemma lem3599891 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term412 A x t u.
Proof. exact (fun h0 : term413 A x t u => @lem3599890 A x t u h0). Qed.
Lemma lem3599892 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term411 A x t u.
Proof. exact (EQ_MP (@lem3599248 A x t u) (@lem3599891 A x t u)). Qed.
Lemma lem3599893 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term403 A x t u.
Proof. exact (EQ_MP (@lem3599244 A x t u) (@lem3599892 A x t u)). Qed.
Lemma lem3599894 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) : term402 A x t u.
Proof. exact (EQ_MP (@lem3599158 A x t u) (@lem3599893 A x t u)). Qed.
Lemma lem3599895 {A : Type'} (u : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) : term399 A x t u.
Proof. exact (@lem3599894 A x t u (@lem3596310 A x t h1)). Qed.
Lemma lem3599896 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term2 A x t) (h2 : term243 A t x u) : @SUBSET A t u.
Proof. exact (@lem3599895 A u x t h1 (@lem3597528 A t x u h2)). Qed.
Lemma lem3599897 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term2 A x t) (h3 : term243 A t x u) : @FINITE A t.
Proof. exact (@lem3599124 A t u h1 (@lem3599896 A t x u h2 h3)). Qed.
Lemma lem3599898 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term244 A t x) (h3 : term243 A t x u) : @FINITE A t.
Proof. exact (or_elim (@lem3596308 A x t) (fun h0 : @IN A x t => @lem3599104 A x t h2 h0) (fun h0 : term2 A x t => @lem3599897 A t x u h1 h0 h3)). Qed.
Lemma lem3599899 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term244 A t x) (h3 : term243 A t x u) : (term244 A t x) = (@FINITE A t).
Proof. exact (prop_ext (fun h4 : term244 A t x => @lem3599898 A t x u h1 h2 h3) (fun h4 : @FINITE A t => @lem3597529 A t x h2)). Qed.
Lemma lem3599900 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term244 A t x) (h3 : term243 A t x u) : @FINITE A t.
Proof. exact (EQ_MP (@lem3599899 A t x u h1 h2 h3) (@lem3597529 A t x h2)). Qed.
Lemma lem3599901 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term243 A t x u) : (term244 A t x) = (@FINITE A t).
Proof. exact (prop_ext (fun h3 : term244 A t x => @lem3599900 A t x u h1 h3 h2) (fun h3 : @FINITE A t => @lem3598283 A t x u h1 h2)). Qed.
Lemma lem3599902 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) (h1 : term72 A u) (h2 : term243 A t x u) : @FINITE A t.
Proof. exact (EQ_MP (@lem3599901 A t x u h1 h2) (@lem3598283 A t x u h1 h2)). Qed.
Lemma lem3599903 {A : Type'} (x : A) (t : A -> Prop) (u : A -> Prop) (h1 : term72 A u) : term453 A x u t.
Proof. exact (fun h0 : term243 A t x u => @lem3599902 A t x u h1 h0). Qed.
Lemma lem3599908 {A : Type'} (x : A) (u : A -> Prop) (h1 : term72 A u) : term86 A x u.
Proof. exact (fun t : A -> Prop => @lem3599903 A x t u h1). Qed.
Lemma lem3599909 {A : Type'} (x : A) (u : A -> Prop) : term88 A x u.
Proof. exact (fun h0 : term72 A u => @lem3599908 A x u h0). Qed.
Lemma lem3599914 {A : Type'} (x : A) : term92 A x.
Proof. exact (fun u : A -> Prop => @lem3599909 A x u). Qed.
Lemma lem3599919 {A : Type'} : term96 A.
Proof. exact (fun x : A => @lem3599914 A x). Qed.
Lemma lem3599920 {A : Type'} : term98 A.
Proof. exact (conj (@lem3597526 A) (@lem3599919 A)). Qed.
Lemma lem3599921 {A : Type'} : term75 A.
Proof. exact (@lem3596533 A (@lem3599920 A)). Qed.
Lemma lem3599922 {A : Type'} : term57 A.
Proof. exact (EQ_MP (@lem3596504 A) (@lem3599921 A)). Qed.
Lemma lem3599923 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem3596440 A) (@lem3599922 A)). Qed.
Lemma lem3599924 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3596410 A) (@lem3599923 A)). Qed.
