Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_MUL_term_abbrevs.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import MULT_ASSOC_spec.
Require Import NADD_MUL_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1279299 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1279300 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1279301 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1279300 n) (@lem1279299 n)). Qed.
Lemma lem1279302 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1279304 (n : nat) : term2 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1279305 (n : nat) : (term2 n) = ((term3 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1279307 (m : nat) : term4 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem1279308 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1279309 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1279308 m) (@lem1279307 m)). Qed.
Lemma lem1279310 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1279309 m n). Qed.
Lemma lem1279311 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1279312 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1279311 m n) (@lem1279310 m n)). Qed.
Lemma lem1279313 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem1279312 m n p). Qed.
Lemma lem1279314 (m : nat) (n : nat) (p : nat) : (term8 m n p) = ((term9 m n p) = (term10 m n p)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1279316 (x : nadd) : term11 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1279317 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1279318 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1279317 x) (@lem1279316 x)). Qed.
Lemma lem1279319 (x : nadd) (y : nadd) : term13 x y.
Proof. exact (@lem1279318 x y). Qed.
Lemma lem1279320 (x : nadd) (y : nadd) : (term13 x y) = ((term14 x y) = (term15 x y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1279322 (k : nat) : term16 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1279323 (k : nat) : (term16 k) = ((term17 k) = (term18 k)).
Proof. exact (eq_refl (term16 k)). Qed.
Lemma lem1279325 (x : nadd) : term19 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1279326 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1279327 (x : nadd) : term20 x.
Proof. exact (EQ_MP (@lem1279326 x) (@lem1279325 x)). Qed.
Lemma lem1279328 (x : nadd) (y : nadd) : term21 x y.
Proof. exact (@lem1279327 x y). Qed.
Lemma lem1279329 (x : nadd) (y : nadd) : (term21 x y) = ((nadd_eq x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1279340 (x : nadd) (y : nadd) : (nadd_eq x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1279329 x y) (@lem1279328 x y)). Qed.
Lemma lem1279341 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (@lem1279340 (term25 m n) (term26 m n)). Qed.
Lemma lem1279351 (x : nadd) (y : nadd) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1279320 x y) (@lem1279319 x y)). Qed.
Lemma lem1279352 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (@lem1279351 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1279354 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1279323 k) (@lem1279322 k)). Qed.
Lemma lem1279355 (m : nat) : (term17 m) = (term18 m).
Proof. exact (@lem1279354 m). Qed.
Lemma lem1279357 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1279323 k) (@lem1279322 k)). Qed.
Lemma lem1279358 (n : nat) : (term17 n) = (term18 n).
Proof. exact (@lem1279357 n). Qed.
Lemma lem1279359 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279360 (n : nat) (n' : nat) : (term29 n n') = (term30 n n').
Proof. exact (MK_COMB (@lem1279358 n) (@lem1279359 n')). Qed.
Lemma lem1279362 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1279363 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1279362 nat nat f y). Qed.
Lemma lem1279364 (n : nat) (n' : nat) : (term33 n n') = (term30 n n').
Proof. exact (@lem1279363 (term18 n) n'). Qed.
Lemma lem1279365 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term30 n n')). Qed.
Lemma lem1279366 (n : nat) : (term34 n) = (term18 n).
Proof. exact (fun_ext (fun n' : nat => @lem1279365 n n')). Qed.
Lemma lem1279367 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279368 (n : nat) (n' : nat) : (term33 n n') = (term30 n n').
Proof. exact (MK_COMB (@lem1279366 n) (@lem1279367 n')). Qed.
Lemma lem1279369 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1279370 (n : nat) (n' : nat) : (term35 n n') = (term36 n n').
Proof. exact (MK_COMB (@lem1279369) (@lem1279368 n n')). Qed.
Lemma lem1279371 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term30 n n')). Qed.
Lemma lem1279372 (n : nat) (n' : nat) : ((term33 n n') = (term30 n n')) = ((term30 n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem1279370 n n') (@lem1279371 n n')). Qed.
Lemma lem1279373 (n : nat) (n' : nat) : (term30 n n') = (Nat.mul n n').
Proof. exact (EQ_MP (@lem1279372 n n') (@lem1279364 n n')). Qed.
Lemma lem1279374 (n : nat) (n' : nat) : (term29 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem1279360 n n') (@lem1279373 n n')). Qed.
Lemma lem1279375 (m : nat) (n : nat) (n' : nat) : (term37 m n n') = (term38 m n n').
Proof. exact (MK_COMB (@lem1279355 m) (@lem1279374 n n')). Qed.
Lemma lem1279377 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1279378 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1279377 nat nat f y). Qed.
Lemma lem1279379 (m : nat) (n : nat) (n' : nat) : (term39 m n n') = (term38 m n n').
Proof. exact (@lem1279378 (term18 m) (Nat.mul n n')). Qed.
Lemma lem1279380 (m : nat) (n : nat) : (term30 m n) = (Nat.mul m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1279381 (m : nat) : (term34 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem1279380 m n)). Qed.
Lemma lem1279382 (n : nat) (n' : nat) : (Nat.mul n n') = (Nat.mul n n').
Proof. exact (eq_refl (Nat.mul n n')). Qed.
Lemma lem1279383 (m : nat) (n : nat) (n' : nat) : (term39 m n n') = (term38 m n n').
Proof. exact (MK_COMB (@lem1279381 m) (@lem1279382 n n')). Qed.
Lemma lem1279384 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1279385 (m : nat) (n : nat) (n' : nat) : (term40 m n n') = (term41 m n n').
Proof. exact (MK_COMB (@lem1279384) (@lem1279383 m n n')). Qed.
Lemma lem1279386 (m : nat) (n : nat) (n' : nat) : (term38 m n n') = (term9 m n n').
Proof. exact (eq_refl (term38 m n n')). Qed.
Lemma lem1279387 (m : nat) (n : nat) (n' : nat) : ((term39 m n n') = (term38 m n n')) = ((term38 m n n') = (term9 m n n')).
Proof. exact (MK_COMB (@lem1279385 m n n') (@lem1279386 m n n')). Qed.
Lemma lem1279388 (m : nat) (n : nat) (n' : nat) : (term38 m n n') = (term9 m n n').
Proof. exact (EQ_MP (@lem1279387 m n n') (@lem1279379 m n n')). Qed.
Lemma lem1279389 (m : nat) (n : nat) (n' : nat) : (term37 m n n') = (term9 m n n').
Proof. exact (TRANS (@lem1279375 m n n') (@lem1279388 m n n')). Qed.
Lemma lem1279390 (m : nat) (n : nat) : (term28 m n) = (term42 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1279389 m n n')). Qed.
Lemma lem1279391 (m : nat) (n : nat) : (term27 m n) = (term42 m n).
Proof. exact (TRANS (@lem1279352 m n) (@lem1279390 m n)). Qed.
Lemma lem1279392 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279393 (m : nat) (n : nat) (n' : nat) : (term43 m n n') = (term44 m n n').
Proof. exact (MK_COMB (@lem1279391 m n) (@lem1279392 n')). Qed.
Lemma lem1279395 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1279396 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1279395 nat nat f y). Qed.
Lemma lem1279397 (m : nat) (n : nat) (n' : nat) : (term45 m n n') = (term44 m n n').
Proof. exact (@lem1279396 (term42 m n) n'). Qed.
Lemma lem1279398 (m : nat) (n : nat) (n' : nat) : (term44 m n n') = (term9 m n n').
Proof. exact (eq_refl (term44 m n n')). Qed.
Lemma lem1279399 (m : nat) (n : nat) : (term46 m n) = (term42 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1279398 m n n')). Qed.
Lemma lem1279400 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279401 (m : nat) (n : nat) (n' : nat) : (term45 m n n') = (term44 m n n').
Proof. exact (MK_COMB (@lem1279399 m n) (@lem1279400 n')). Qed.
Lemma lem1279402 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1279403 (m : nat) (n : nat) (n' : nat) : (term47 m n n') = (term48 m n n').
Proof. exact (MK_COMB (@lem1279402) (@lem1279401 m n n')). Qed.
Lemma lem1279404 (m : nat) (n : nat) (n' : nat) : (term44 m n n') = (term9 m n n').
Proof. exact (eq_refl (term44 m n n')). Qed.
Lemma lem1279405 (m : nat) (n : nat) (n' : nat) : ((term45 m n n') = (term44 m n n')) = ((term44 m n n') = (term9 m n n')).
Proof. exact (MK_COMB (@lem1279403 m n n') (@lem1279404 m n n')). Qed.
Lemma lem1279406 (m : nat) (n : nat) (n' : nat) : (term44 m n n') = (term9 m n n').
Proof. exact (EQ_MP (@lem1279405 m n n') (@lem1279397 m n n')). Qed.
Lemma lem1279407 (m : nat) (n : nat) (n' : nat) : (term43 m n n') = (term9 m n n').
Proof. exact (TRANS (@lem1279393 m n n') (@lem1279406 m n n')). Qed.
Lemma lem1279408 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1279409 (m : nat) (n : nat) (n' : nat) : (term49 m n n') = (term50 m n n').
Proof. exact (MK_COMB (@lem1279408) (@lem1279407 m n n')). Qed.
Lemma lem1279411 (k : nat) : (term17 k) = (term18 k).
Proof. exact (EQ_MP (@lem1279323 k) (@lem1279322 k)). Qed.
Lemma lem1279412 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (@lem1279411 (Nat.mul m n)). Qed.
Lemma lem1279413 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279414 (m : nat) (n : nat) (n' : nat) : (term53 m n n') = (term54 m n n').
Proof. exact (MK_COMB (@lem1279412 m n) (@lem1279413 n')). Qed.
Lemma lem1279416 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1279417 (f : nat -> nat) (y : nat) : (term32 f y) = (f y).
Proof. exact (@lem1279416 nat nat f y). Qed.
Lemma lem1279418 (m : nat) (n : nat) (n' : nat) : (term55 m n n') = (term54 m n n').
Proof. exact (@lem1279417 (term52 m n) n'). Qed.
Lemma lem1279419 (m : nat) (n : nat) (n' : nat) : (term54 m n n') = (term10 m n n').
Proof. exact (eq_refl (term54 m n n')). Qed.
Lemma lem1279420 (m : nat) (n : nat) : (term56 m n) = (term52 m n).
Proof. exact (fun_ext (fun n' : nat => @lem1279419 m n n')). Qed.
Lemma lem1279421 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1279422 (m : nat) (n : nat) (n' : nat) : (term55 m n n') = (term54 m n n').
Proof. exact (MK_COMB (@lem1279420 m n) (@lem1279421 n')). Qed.
Lemma lem1279423 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1279424 (m : nat) (n : nat) (n' : nat) : (term57 m n n') = (term58 m n n').
Proof. exact (MK_COMB (@lem1279423) (@lem1279422 m n n')). Qed.
Lemma lem1279425 (m : nat) (n : nat) (n' : nat) : (term54 m n n') = (term10 m n n').
Proof. exact (eq_refl (term54 m n n')). Qed.
Lemma lem1279426 (m : nat) (n : nat) (n' : nat) : ((term55 m n n') = (term54 m n n')) = ((term54 m n n') = (term10 m n n')).
Proof. exact (MK_COMB (@lem1279424 m n n') (@lem1279425 m n n')). Qed.
Lemma lem1279427 (m : nat) (n : nat) (n' : nat) : (term54 m n n') = (term10 m n n').
Proof. exact (EQ_MP (@lem1279426 m n n') (@lem1279418 m n n')). Qed.
Lemma lem1279428 (m : nat) (n : nat) (n' : nat) : (term53 m n n') = (term10 m n n').
Proof. exact (TRANS (@lem1279414 m n n') (@lem1279427 m n n')). Qed.
Lemma lem1279429 (m : nat) (n : nat) (n' : nat) : (term59 m n n') = (term60 m n n').
Proof. exact (MK_COMB (@lem1279409 m n n') (@lem1279428 m n n')). Qed.
Lemma lem1279430 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1279431 (m : nat) (n : nat) (n' : nat) : (term61 m n n') = (term62 m n n').
Proof. exact (MK_COMB (@lem1279430) (@lem1279429 m n n')). Qed.
Lemma lem1279432 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1279433 (m : nat) (n : nat) (n' : nat) : (term63 m n n') = (term64 m n n').
Proof. exact (MK_COMB (@lem1279432) (@lem1279431 m n n')). Qed.
Lemma lem1279434 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1279435 (m : nat) (n : nat) (n' : nat) (B : nat) : (term65 m n n' B) = (term66 m n n' B).
Proof. exact (MK_COMB (@lem1279433 m n n') (@lem1279434 B)). Qed.
Lemma lem1279436 (m : nat) (n : nat) (B : nat) : (term67 m n B) = (term68 m n B).
Proof. exact (fun_ext (fun n' : nat => @lem1279435 m n n' B)). Qed.
Lemma lem1279437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279438 (m : nat) (n : nat) (B : nat) : (term69 m n B) = (term70 m n B).
Proof. exact (MK_COMB (@lem1279437) (@lem1279436 m n B)). Qed.
Lemma lem1279443 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (fun_ext (fun B : nat => @lem1279438 m n B)). Qed.
Lemma lem1279444 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1279445 (m : nat) (n : nat) : (term24 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem1279444) (@lem1279443 m n)). Qed.
Lemma lem1279450 (m : nat) (n : nat) : (term23 m n) = (term73 m n).
Proof. exact (TRANS (@lem1279341 m n) (@lem1279445 m n)). Qed.
Lemma lem1279451 (m : nat) : (term74 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem1279450 m n)). Qed.
Lemma lem1279452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279453 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem1279452) (@lem1279451 m)). Qed.
Lemma lem1279458 : term78 = term79.
Proof. exact (fun_ext (fun m : nat => @lem1279453 m)). Qed.
Lemma lem1279459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279460 : term80 = term81.
Proof. exact (MK_COMB (@lem1279459) (@lem1279458)). Qed.
Lemma lem1279465 : term81 = term80.
Proof. exact (SYM (@lem1279460)). Qed.
Lemma lem1279485 (m : nat) (n : nat) (p : nat) : (term9 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1279314 m n p) (@lem1279313 m n p)). Qed.
Lemma lem1279486 (m : nat) (n : nat) (n' : nat) : (term9 m n n') = (term10 m n n').
Proof. exact (@lem1279485 m n n'). Qed.
Lemma lem1279487 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1279488 (m : nat) (n : nat) (n' : nat) : (term50 m n n') = (term82 m n n').
Proof. exact (MK_COMB (@lem1279487) (@lem1279486 m n n')). Qed.
Lemma lem1279489 (m : nat) (n : nat) (n' : nat) : (term10 m n n') = (term10 m n n').
Proof. exact (eq_refl (term10 m n n')). Qed.
Lemma lem1279490 (m : nat) (n : nat) (n' : nat) : (term60 m n n') = (term83 m n n').
Proof. exact (MK_COMB (@lem1279488 m n n') (@lem1279489 m n n')). Qed.
Lemma lem1279491 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1279492 (m : nat) (n : nat) (n' : nat) : (term62 m n n') = (term84 m n n').
Proof. exact (MK_COMB (@lem1279491) (@lem1279490 m n n')). Qed.
Lemma lem1279494 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1279305 n) (@lem1279304 n)). Qed.
Lemma lem1279495 (m : nat) (n : nat) (n' : nat) : (term84 m n n') = (NUMERAL 0).
Proof. exact (@lem1279494 (term10 m n n')). Qed.
Lemma lem1279496 (m : nat) (n : nat) (n' : nat) : (term62 m n n') = (NUMERAL 0).
Proof. exact (TRANS (@lem1279492 m n n') (@lem1279495 m n n')). Qed.
Lemma lem1279497 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1279498 (m : nat) (n : nat) (n' : nat) : (term64 m n n') = term85.
Proof. exact (MK_COMB (@lem1279497) (@lem1279496 m n n')). Qed.
Lemma lem1279499 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1279500 (m : nat) (n : nat) (n' : nat) (B : nat) : (term66 m n n' B) = (term1 B).
Proof. exact (MK_COMB (@lem1279498 m n n') (@lem1279499 B)). Qed.
Lemma lem1279502 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1279302 n) (@lem1279301 n)). Qed.
Lemma lem1279503 (B : nat) : (term1 B) = True.
Proof. exact (@lem1279502 B). Qed.
Lemma lem1279504 (m : nat) (n : nat) (n' : nat) (B : nat) : (term66 m n n' B) = True.
Proof. exact (TRANS (@lem1279500 m n n' B) (@lem1279503 B)). Qed.
Lemma lem1279505 (m : nat) (n : nat) (B : nat) : (term68 m n B) = term86.
Proof. exact (fun_ext (fun n' : nat => @lem1279504 m n n' B)). Qed.
Lemma lem1279506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279507 (m : nat) (n : nat) (B : nat) : (term70 m n B) = term87.
Proof. exact (MK_COMB (@lem1279506) (@lem1279505 m n B)). Qed.
Lemma lem1279509 {A : Type'} (t : Prop) : (term88 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1279510 (t : Prop) : (term89 t) = t.
Proof. exact (@lem1279509 nat t). Qed.
Lemma lem1279511 : term87 = True.
Proof. exact (@lem1279510 True). Qed.
Lemma lem1279512 (m : nat) (n : nat) (B : nat) : (term70 m n B) = True.
Proof. exact (TRANS (@lem1279507 m n B) (@lem1279511)). Qed.
Lemma lem1279513 (m : nat) (n : nat) : (term72 m n) = term86.
Proof. exact (fun_ext (fun B : nat => @lem1279512 m n B)). Qed.
Lemma lem1279514 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1279515 (m : nat) (n : nat) : (term73 m n) = term90.
Proof. exact (MK_COMB (@lem1279514) (@lem1279513 m n)). Qed.
Lemma lem1279517 {A : Type'} (t : Prop) : (term91 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1279518 (t : Prop) : (term92 t) = t.
Proof. exact (@lem1279517 nat t). Qed.
Lemma lem1279519 : term90 = True.
Proof. exact (@lem1279518 True). Qed.
Lemma lem1279520 (m : nat) (n : nat) : (term73 m n) = True.
Proof. exact (TRANS (@lem1279515 m n) (@lem1279519)). Qed.
Lemma lem1279521 (m : nat) : (term75 m) = term86.
Proof. exact (fun_ext (fun n : nat => @lem1279520 m n)). Qed.
Lemma lem1279522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279523 (m : nat) : (term77 m) = term87.
Proof. exact (MK_COMB (@lem1279522) (@lem1279521 m)). Qed.
Lemma lem1279525 {A : Type'} (t : Prop) : (term88 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1279526 (t : Prop) : (term89 t) = t.
Proof. exact (@lem1279525 nat t). Qed.
Lemma lem1279527 : term87 = True.
Proof. exact (@lem1279526 True). Qed.
Lemma lem1279528 (m : nat) : (term77 m) = True.
Proof. exact (TRANS (@lem1279523 m) (@lem1279527)). Qed.
Lemma lem1279529 : term79 = term86.
Proof. exact (fun_ext (fun m : nat => @lem1279528 m)). Qed.
Lemma lem1279530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279531 : term81 = term87.
Proof. exact (MK_COMB (@lem1279530) (@lem1279529)). Qed.
Lemma lem1279533 {A : Type'} (t : Prop) : (term88 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1279534 (t : Prop) : (term89 t) = t.
Proof. exact (@lem1279533 nat t). Qed.
Lemma lem1279535 : term87 = True.
Proof. exact (@lem1279534 True). Qed.
Lemma lem1279536 : term81 = True.
Proof. exact (TRANS (@lem1279531) (@lem1279535)). Qed.
Lemma lem1279537 : True = term81.
Proof. exact (SYM (@lem1279536)). Qed.
Lemma lem1279538 : term81.
Proof. exact (EQ_MP (@lem1279537) (@lem0)). Qed.
Lemma lem1279539 : term80.
Proof. exact (EQ_MP (@lem1279465) (@lem1279538)). Qed.
