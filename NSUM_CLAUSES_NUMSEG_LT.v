Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_NUMSEG_LT_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_LT_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Lemma lem7047280 {_123501 : Type'} (f : nat -> _123501) (op : type1400 _123501) : term0 _123501 f op.
Proof. exact (@lem6194987 _123501 f op). Qed.
Lemma lem7047281 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : (term0 _123501 f op) = (term1 _123501 op f).
Proof. exact (eq_refl (term0 _123501 f op)). Qed.
Lemma lem7047284 {_123501 : Type'} (op : type1400 _123501) (f : nat -> _123501) : term1 _123501 op f.
Proof. exact (EQ_MP (@lem7047281 _123501 op f) (@lem7047280 _123501 f op)). Qed.
Lemma lem7047285 (op : type1606) (f : nat -> nat) : term2 op f.
Proof. exact (@lem7047284 nat op f). Qed.
Lemma lem7047286 (f : nat -> nat) : term3 f.
Proof. exact (@lem7047285 Nat.add f). Qed.
Lemma lem7047287 (f : nat -> nat) : term4 f.
Proof. exact (@lem7047286 f (@lem6924403)). Qed.
Lemma lem7047299 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7047300 (f : nat -> nat) : (term5 f) = (term5 f).
Proof. exact (eq_refl (term5 f)). Qed.
Lemma lem7047301 (f : nat -> nat) : ((term6 f) = (@neutral nat Nat.add)) = ((term6 f) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7047300 f) (@lem7047299)). Qed.
Lemma lem7047304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047305 (f : nat -> nat) : (term7 f) = (term8 f).
Proof. exact (MK_COMB (@lem7047304) (@lem7047301 f)). Qed.
Lemma lem7047320 (f : nat -> nat) : (term9 f) = (term9 f).
Proof. exact (eq_refl (term9 f)). Qed.
Lemma lem7047321 (f : nat -> nat) : (term4 f) = (term10 f).
Proof. exact (MK_COMB (@lem7047305 f) (@lem7047320 f)). Qed.
Lemma lem7047324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7047325 (f : nat -> nat) : (term11 f) = (term12 f).
Proof. exact (MK_COMB (@lem7047324) (@lem7047321 f)). Qed.
Lemma lem7047331 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047332 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047331 nat). Qed.
Lemma lem7047337 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem7047338 : term14 = term15.
Proof. exact (MK_COMB (@lem7047332) (@lem7047337)). Qed.
Lemma lem7047339 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047340 (f : nat -> nat) : (term16 f) = (term6 f).
Proof. exact (MK_COMB (@lem7047338) (@lem7047339 f)). Qed.
Lemma lem7047341 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047342 (f : nat -> nat) : (term17 f) = (term5 f).
Proof. exact (MK_COMB (@lem7047341) (@lem7047340 f)). Qed.
Lemma lem7047343 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7047344 (f : nat -> nat) : ((term16 f) = (NUMERAL 0)) = ((term6 f) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7047342 f) (@lem7047343)). Qed.
Lemma lem7047347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047348 (f : nat -> nat) : (term18 f) = (term8 f).
Proof. exact (MK_COMB (@lem7047347) (@lem7047344 f)). Qed.
Lemma lem7047356 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047357 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047356 nat). Qed.
Lemma lem7047362 (k : nat) : (term19 k) = (term19 k).
Proof. exact (eq_refl (term19 k)). Qed.
Lemma lem7047363 (k : nat) : (term20 k) = (term21 k).
Proof. exact (MK_COMB (@lem7047357) (@lem7047362 k)). Qed.
Lemma lem7047364 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047365 (k : nat) (f : nat -> nat) : (term22 k f) = (term23 k f).
Proof. exact (MK_COMB (@lem7047363 k) (@lem7047364 f)). Qed.
Lemma lem7047366 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047367 (k : nat) (f : nat -> nat) : (term24 k f) = (term25 k f).
Proof. exact (MK_COMB (@lem7047366) (@lem7047365 k f)). Qed.
Lemma lem7047369 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7047370 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7047369 nat). Qed.
Lemma lem7047375 (k : nat) : (term26 k) = (term26 k).
Proof. exact (eq_refl (term26 k)). Qed.
Lemma lem7047376 (k : nat) : (term27 k) = (term28 k).
Proof. exact (MK_COMB (@lem7047370) (@lem7047375 k)). Qed.
Lemma lem7047377 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047378 (k : nat) (f : nat -> nat) : (term29 k f) = (term30 k f).
Proof. exact (MK_COMB (@lem7047376 k) (@lem7047377 f)). Qed.
Lemma lem7047379 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7047380 (k : nat) (f : nat -> nat) : (term31 k f) = (term32 k f).
Proof. exact (MK_COMB (@lem7047379) (@lem7047378 k f)). Qed.
Lemma lem7047381 (f : nat -> nat) (k : nat) : (f k) = (f k).
Proof. exact (eq_refl (f k)). Qed.
Lemma lem7047382 (f : nat -> nat) (k : nat) : (term33 f k) = (term34 f k).
Proof. exact (MK_COMB (@lem7047380 k f) (@lem7047381 f k)). Qed.
Lemma lem7047383 (f : nat -> nat) (k : nat) : ((term22 k f) = (term33 f k)) = ((term23 k f) = (term34 f k)).
Proof. exact (MK_COMB (@lem7047367 k f) (@lem7047382 f k)). Qed.
Lemma lem7047386 (f : nat -> nat) : (term35 f) = (term36 f).
Proof. exact (fun_ext (fun k : nat => @lem7047383 f k)). Qed.
Lemma lem7047387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047388 (f : nat -> nat) : (term37 f) = (term9 f).
Proof. exact (MK_COMB (@lem7047387) (@lem7047386 f)). Qed.
Lemma lem7047393 (f : nat -> nat) : (term38 f) = (term10 f).
Proof. exact (MK_COMB (@lem7047348 f) (@lem7047388 f)). Qed.
Lemma lem7047396 (f : nat -> nat) : (term39 f) = (term40 f).
Proof. exact (MK_COMB (@lem7047325 f) (@lem7047393 f)). Qed.
Lemma lem7047398 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7047399 (f : nat -> nat) : (term40 f) = True.
Proof. exact (@lem7047398 (term10 f)). Qed.
Lemma lem7047402 (f : nat -> nat) : (term41 f) = (term41 f).
Proof. exact (eq_refl (term41 f)). Qed.
Lemma lem7047403 (f : nat -> nat) : (term41 f) = ((term40 f) = True).
Proof. exact (eq_refl (term41 f)). Qed.
Lemma lem7047404 (f : nat -> nat) : (term42 f) = (term42 f).
Proof. exact (eq_refl (term42 f)). Qed.
Lemma lem7047405 (f : nat -> nat) : ((term41 f) = (term41 f)) = ((term41 f) = ((term40 f) = True)).
Proof. exact (MK_COMB (@lem7047404 f) (@lem7047403 f)). Qed.
Lemma lem7047406 (f : nat -> nat) : (term41 f) = ((term40 f) = True).
Proof. exact (eq_refl (term41 f)). Qed.
Lemma lem7047407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7047408 (f : nat -> nat) : (term42 f) = (term43 f).
Proof. exact (MK_COMB (@lem7047407) (@lem7047406 f)). Qed.
Lemma lem7047409 (f : nat -> nat) : ((term40 f) = True) = ((term40 f) = True).
Proof. exact (eq_refl ((term40 f) = True)). Qed.
Lemma lem7047410 (f : nat -> nat) : ((term41 f) = ((term40 f) = True)) = (((term40 f) = True) = ((term40 f) = True)).
Proof. exact (MK_COMB (@lem7047408 f) (@lem7047409 f)). Qed.
Lemma lem7047411 (f : nat -> nat) : ((term41 f) = (term41 f)) = (((term40 f) = True) = ((term40 f) = True)).
Proof. exact (TRANS (@lem7047405 f) (@lem7047410 f)). Qed.
Lemma lem7047412 (f : nat -> nat) : ((term40 f) = True) = ((term40 f) = True).
Proof. exact (EQ_MP (@lem7047411 f) (@lem7047402 f)). Qed.
Lemma lem7047413 (f : nat -> nat) : (term40 f) = True.
Proof. exact (EQ_MP (@lem7047412 f) (@lem7047399 f)). Qed.
Lemma lem7047414 (f : nat -> nat) : (term39 f) = True.
Proof. exact (TRANS (@lem7047396 f) (@lem7047413 f)). Qed.
Lemma lem7047415 (f : nat -> nat) : True = (term39 f).
Proof. exact (SYM (@lem7047414 f)). Qed.
Lemma lem7047416 (f : nat -> nat) : term39 f.
Proof. exact (EQ_MP (@lem7047415 f) (@lem0)). Qed.
Lemma lem7047417 (f : nat -> nat) : term38 f.
Proof. exact (@lem7047416 f (@lem7047287 f)). Qed.
