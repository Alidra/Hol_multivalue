Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_EQ_term_abbrevs.
Require Import REAL_SGN_EQ_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309351 : term0.
Proof. exact (proj2 (@lem1740125)). Qed.
Lemma lem2309352 : term1.
Proof. exact (proj2 (@lem2309351)). Qed.
Lemma lem2309353 (x : int) : term2 x.
Proof. exact (@lem2309352 (real_of_int x)). Qed.
Lemma lem2309354 (x : int) : (term2 x) = (((term3 x) = term4) = (term5 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2309355 (x : int) : ((term3 x) = term4) = (term5 x).
Proof. exact (EQ_MP (@lem2309354 x) (@lem2309353 x)). Qed.
Lemma lem2309357 (x : int) : (term3 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309358 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309359 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2309358) (@lem2309357 x)). Qed.
Lemma lem2309361 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309362 : term10 = term11.
Proof. exact (@lem2309361 term12). Qed.
Lemma lem2309363 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2309364 : term4 = term13.
Proof. exact (MK_COMB (@lem2309363) (@lem2309362)). Qed.
Lemma lem2309366 (x : int) : (term14 x) = (term15 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2309367 : term13 = term16.
Proof. exact (@lem2309366 term17). Qed.
Lemma lem2309368 : term4 = term16.
Proof. exact (TRANS (@lem2309364) (@lem2309367)). Qed.
Lemma lem2309369 (x : int) : ((term3 x) = term4) = ((term6 x) = term16).
Proof. exact (MK_COMB (@lem2309359 x) (@lem2309368)). Qed.
Lemma lem2309371 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309372 (x : int) : ((term6 x) = term16) = ((int_sgn x) = term18).
Proof. exact (@lem2309371 (int_sgn x) term18). Qed.
Lemma lem2309373 (x : int) : ((term3 x) = term4) = ((int_sgn x) = term18).
Proof. exact (TRANS (@lem2309369 x) (@lem2309372 x)). Qed.
Lemma lem2309374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309375 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2309374) (@lem2309373 x)). Qed.
Lemma lem2309377 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309378 : term21 = term22.
Proof. exact (@lem2309377 (NUMERAL 0)). Qed.
Lemma lem2309379 (x : int) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2309380 (x : int) : (term5 x) = (term24 x).
Proof. exact (MK_COMB (@lem2309379 x) (@lem2309378)). Qed.
Lemma lem2309382 (x : int) (y : int) : (term25 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309383 (x : int) : (term24 x) = (term26 x).
Proof. exact (@lem2309382 x term27). Qed.
Lemma lem2309384 (x : int) : (term5 x) = (term26 x).
Proof. exact (TRANS (@lem2309380 x) (@lem2309383 x)). Qed.
Lemma lem2309385 (x : int) : (((term3 x) = term4) = (term5 x)) = (((int_sgn x) = term18) = (term26 x)).
Proof. exact (MK_COMB (@lem2309375 x) (@lem2309384 x)). Qed.
Lemma lem2309386 (x : int) : ((int_sgn x) = term18) = (term26 x).
Proof. exact (EQ_MP (@lem2309385 x) (@lem2309355 x)). Qed.
Lemma lem2309387 : term28.
Proof. exact (fun x : int => @lem2309386 x). Qed.
Lemma lem2309388 : term29.
Proof. exact (proj1 (@lem2309351)). Qed.
Lemma lem2309389 (x : int) : term30 x.
Proof. exact (@lem2309388 (real_of_int x)). Qed.
Lemma lem2309390 (x : int) : (term30 x) = (((term3 x) = term10) = (term31 x)).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem2309391 (x : int) : ((term3 x) = term10) = (term31 x).
Proof. exact (EQ_MP (@lem2309390 x) (@lem2309389 x)). Qed.
Lemma lem2309393 (x : int) : (term3 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309394 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309395 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2309394) (@lem2309393 x)). Qed.
Lemma lem2309397 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309398 : term10 = term11.
Proof. exact (@lem2309397 term12). Qed.
Lemma lem2309399 (x : int) : ((term3 x) = term10) = ((term6 x) = term11).
Proof. exact (MK_COMB (@lem2309395 x) (@lem2309398)). Qed.
Lemma lem2309401 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309402 (x : int) : ((term6 x) = term11) = ((int_sgn x) = term17).
Proof. exact (@lem2309401 (int_sgn x) term17). Qed.
Lemma lem2309403 (x : int) : ((term3 x) = term10) = ((int_sgn x) = term17).
Proof. exact (TRANS (@lem2309399 x) (@lem2309402 x)). Qed.
Lemma lem2309404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309405 (x : int) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem2309404) (@lem2309403 x)). Qed.
Lemma lem2309407 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309408 : term21 = term22.
Proof. exact (@lem2309407 (NUMERAL 0)). Qed.
Lemma lem2309409 (x : int) : (term34 x) = (term34 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem2309410 (x : int) : (term31 x) = (term35 x).
Proof. exact (MK_COMB (@lem2309409 x) (@lem2309408)). Qed.
Lemma lem2309412 (x : int) (y : int) : (term36 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309413 (x : int) : (term35 x) = (term37 x).
Proof. exact (@lem2309412 x term27). Qed.
Lemma lem2309414 (x : int) : (term31 x) = (term37 x).
Proof. exact (TRANS (@lem2309410 x) (@lem2309413 x)). Qed.
Lemma lem2309415 (x : int) : (((term3 x) = term10) = (term31 x)) = (((int_sgn x) = term17) = (term37 x)).
Proof. exact (MK_COMB (@lem2309405 x) (@lem2309414 x)). Qed.
Lemma lem2309416 (x : int) : ((int_sgn x) = term17) = (term37 x).
Proof. exact (EQ_MP (@lem2309415 x) (@lem2309391 x)). Qed.
Lemma lem2309417 : term38.
Proof. exact (fun x : int => @lem2309416 x). Qed.
Lemma lem2309418 : term39.
Proof. exact (conj (@lem2309417) (@lem2309387)). Qed.
Lemma lem2309419 : term40.
Proof. exact (proj1 (@lem1740125)). Qed.
Lemma lem2309420 (x : int) : term41 x.
Proof. exact (@lem2309419 (real_of_int x)). Qed.
Lemma lem2309421 (x : int) : (term41 x) = (((term3 x) = term21) = ((real_of_int x) = term21)).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem2309422 (x : int) : ((term3 x) = term21) = ((real_of_int x) = term21).
Proof. exact (EQ_MP (@lem2309421 x) (@lem2309420 x)). Qed.
Lemma lem2309424 (x : int) : (term3 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309425 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309426 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2309425) (@lem2309424 x)). Qed.
Lemma lem2309428 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309429 : term21 = term22.
Proof. exact (@lem2309428 (NUMERAL 0)). Qed.
Lemma lem2309430 (x : int) : ((term3 x) = term21) = ((term6 x) = term22).
Proof. exact (MK_COMB (@lem2309426 x) (@lem2309429)). Qed.
Lemma lem2309432 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309433 (x : int) : ((term6 x) = term22) = ((int_sgn x) = term27).
Proof. exact (@lem2309432 (int_sgn x) term27). Qed.
Lemma lem2309434 (x : int) : ((term3 x) = term21) = ((int_sgn x) = term27).
Proof. exact (TRANS (@lem2309430 x) (@lem2309433 x)). Qed.
Lemma lem2309435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309436 (x : int) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem2309435) (@lem2309434 x)). Qed.
Lemma lem2309438 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309439 : term21 = term22.
Proof. exact (@lem2309438 (NUMERAL 0)). Qed.
Lemma lem2309440 (x : int) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem2309441 (x : int) : ((real_of_int x) = term21) = ((real_of_int x) = term22).
Proof. exact (MK_COMB (@lem2309440 x) (@lem2309439)). Qed.
Lemma lem2309443 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309444 (x : int) : ((real_of_int x) = term22) = (x = term27).
Proof. exact (@lem2309443 x term27). Qed.
Lemma lem2309445 (x : int) : ((real_of_int x) = term21) = (x = term27).
Proof. exact (TRANS (@lem2309441 x) (@lem2309444 x)). Qed.
Lemma lem2309446 (x : int) : (((term3 x) = term21) = ((real_of_int x) = term21)) = (((int_sgn x) = term27) = (x = term27)).
Proof. exact (MK_COMB (@lem2309436 x) (@lem2309445 x)). Qed.
Lemma lem2309447 (x : int) : ((int_sgn x) = term27) = (x = term27).
Proof. exact (EQ_MP (@lem2309446 x) (@lem2309422 x)). Qed.
Lemma lem2309448 : term45.
Proof. exact (fun x : int => @lem2309447 x). Qed.
Lemma lem2309449 : term46.
Proof. exact (conj (@lem2309448) (@lem2309418)). Qed.
