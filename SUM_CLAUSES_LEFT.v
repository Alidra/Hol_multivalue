Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_LEFT_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import NUMSEG_LREC_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982749_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988318_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7223342 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (term0 m n) = (dotdot m n).
Proof. exact (h1). Qed.
Lemma lem7223343 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (dotdot m n) = (term0 m n).
Proof. exact (SYM (@lem7223342 m n h1)). Qed.
Lemma lem7223344 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (dotdot m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem7223345 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (term0 m n) = (dotdot m n).
Proof. exact (SYM (@lem7223344 m n h1)). Qed.
Lemma lem7223346 (m : nat) (n : nat) : ((term0 m n) = (dotdot m n)) = ((dotdot m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (dotdot m n) => @lem7223343 m n h1) (fun h1 : (dotdot m n) = (term0 m n) => @lem7223345 m n h1)). Qed.
Lemma lem7223347 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7223348 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem7223347 m n) (@lem7223346 m n)). Qed.
Lemma lem7223349 (m : nat) : (term4 m) = (term5 m).
Proof. exact (fun_ext (fun n : nat => @lem7223348 m n)). Qed.
Lemma lem7223350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223351 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem7223350) (@lem7223349 m)). Qed.
Lemma lem7223352 : term8 = term9.
Proof. exact (fun_ext (fun m : nat => @lem7223351 m)). Qed.
Lemma lem7223353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223354 : term10 = term11.
Proof. exact (MK_COMB (@lem7223353) (@lem7223352)). Qed.
Lemma lem7223355 : term11.
Proof. exact (EQ_MP (@lem7223354) (@lem5357842)). Qed.
Lemma lem7223356 (m : nat) : term12 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7223357 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem7223358 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem7223357 m) (@lem7223356 m)). Qed.
Lemma lem7223359 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem7223358 m n). Qed.
Lemma lem7223360 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem7223361 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem7223360 m n) (@lem7223359 m n)). Qed.
Lemma lem7223362 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem7223361 m n p). Qed.
Lemma lem7223363 (m : nat) (p : nat) (n : nat) : (term16 m n p) = ((term17 p m n) = (term18 m p n)).
Proof. exact (eq_refl (term16 m n p)). Qed.
Lemma lem7223365 (m : nat) : term19 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7223366 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem7223367 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem7223366 m) (@lem7223365 m)). Qed.
Lemma lem7223368 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem7223367 m n). Qed.
Lemma lem7223369 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem7223370 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem7223369 m n) (@lem7223368 m n)). Qed.
Lemma lem7223371 (m : nat) (n : nat) : (term22 m n) = ((term22 m n) = True).
Proof. exact (@lem7 (term22 m n)). Qed.
Lemma lem7223373 {_131524 : Type'} : term23 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7223374 {_131524 : Type'} (x : _131524) : term24 _131524 x.
Proof. exact (@lem7223373 _131524 x). Qed.
Lemma lem7223375 {_131524 : Type'} (x : _131524) : (term24 _131524 x) = (term25 _131524 x).
Proof. exact (eq_refl (term24 _131524 x)). Qed.
Lemma lem7223376 {_131524 : Type'} (x : _131524) : term25 _131524 x.
Proof. exact (EQ_MP (@lem7223375 _131524 x) (@lem7223374 _131524 x)). Qed.
Lemma lem7223377 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term26 _131524 x f.
Proof. exact (@lem7223376 _131524 x f). Qed.
Lemma lem7223378 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term26 _131524 x f) = (term27 _131524 x f).
Proof. exact (eq_refl (term26 _131524 x f)). Qed.
Lemma lem7223379 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term27 _131524 x f.
Proof. exact (EQ_MP (@lem7223378 _131524 x f) (@lem7223377 _131524 x f)). Qed.
Lemma lem7223380 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term28 _131524 x f s.
Proof. exact (@lem7223379 _131524 x f s). Qed.
Lemma lem7223381 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term28 _131524 x f s) = (term29 _131524 x s f).
Proof. exact (eq_refl (term28 _131524 x f s)). Qed.
Lemma lem7223382 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term29 _131524 x s f.
Proof. exact (EQ_MP (@lem7223381 _131524 x s f) (@lem7223380 _131524 x f s)). Qed.
Lemma lem7223383 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7223384 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term30 _131524 x s f) = (term31 _131524 x s f).
Proof. exact (@lem7223382 _131524 x s f (@lem7223383 _131524 s h1)). Qed.
Lemma lem7223394 (m : nat) : term32 m.
Proof. exact (@lem7223355 m). Qed.
Lemma lem7223395 (m : nat) : (term32 m) = (term7 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem7223396 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem7223395 m) (@lem7223394 m)). Qed.
Lemma lem7223397 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem7223396 m n). Qed.
Lemma lem7223398 (m : nat) (n : nat) : (term33 m n) = (term3 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem7223399 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7223398 m n) (@lem7223397 m n)). Qed.
Lemma lem7223400 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7223401 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term0 m n).
Proof. exact (@lem7223399 m n (@lem7223400 m n h1)). Qed.
Lemma lem7223422 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term34 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7223423 (p : Prop) (q : Prop) (p' : Prop) : term35 p q p'.
Proof. exact (fun q' : Prop => @lem7223422 p q p' q'). Qed.
Lemma lem7223424 (p : Prop) (q : Prop) : term36 p q.
Proof. exact (fun p' : Prop => @lem7223423 p q p'). Qed.
Lemma lem7223425 (m : nat) (n : nat) (f : nat -> real) : term37 m n f.
Proof. exact (@lem7223424 (Peano.le m n) ((term38 m n f) = (term39 m n f))). Qed.
Lemma lem7223426 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term40 m n f p'.
Proof. exact (@lem7223425 m n f p'). Qed.
Lemma lem7223427 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : (term40 m n f p') = (term41 m n f p').
Proof. exact (eq_refl (term40 m n f p')). Qed.
Lemma lem7223428 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) : term41 m n f p'.
Proof. exact (EQ_MP (@lem7223427 m n f p') (@lem7223426 m n f p')). Qed.
Lemma lem7223429 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term42 m n f p' q'.
Proof. exact (@lem7223428 m n f p' q'). Qed.
Lemma lem7223430 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : (term42 m n f p' q') = (term43 m n f p' q').
Proof. exact (eq_refl (term42 m n f p' q')). Qed.
Lemma lem7223431 (m : nat) (n : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term43 m n f p' q'.
Proof. exact (EQ_MP (@lem7223430 m n f p' q') (@lem7223429 m n f p' q')). Qed.
Lemma lem7223432 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem7223433 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term44 f m n q'.
Proof. exact (@lem7223431 m n f (Peano.le m n) q'). Qed.
Lemma lem7223434 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term45 f m n q'.
Proof. exact (@lem7223433 f m n q' (@lem7223432 m n)). Qed.
Lemma lem7223435 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7223436 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7223441 (m : nat) (n : nat) : term3 m n.
Proof. exact (fun h0 : Peano.le m n => @lem7223401 m n h0). Qed.
Lemma lem7223443 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7223436 m n) (@lem7223435 m n h1)). Qed.
Lemma lem7223444 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem7223443 m n h1)). Qed.
Lemma lem7223445 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem7223444 m n h1) (@lem0)). Qed.
Lemma lem7223446 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term0 m n).
Proof. exact (@lem7223441 m n (@lem7223445 m n h1)). Qed.
Lemma lem7223452 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7223453 (m : nat) (n : nat) (h1 : Peano.le m n) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem7223452) (@lem7223446 m n h1)). Qed.
Lemma lem7223459 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7223460 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n f) = (term48 m n f).
Proof. exact (MK_COMB (@lem7223453 m n h1) (@lem7223459 f)). Qed.
Lemma lem7223462 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term29 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7223384 _131524 x f s h0). Qed.
Lemma lem7223463 (x : nat) (s : nat -> Prop) (f : nat -> real) : term49 x s f.
Proof. exact (@lem7223462 nat x s f). Qed.
Lemma lem7223464 (m : nat) (n : nat) (f : nat -> real) : term50 m n f.
Proof. exact (@lem7223463 m (term51 m n) f). Qed.
Lemma lem7223466 (m : nat) (n : nat) : (term22 m n) = True.
Proof. exact (EQ_MP (@lem7223371 m n) (@lem7223370 m n)). Qed.
Lemma lem7223467 (m : nat) (n : nat) : (term52 m n) = True.
Proof. exact (@lem7223466 (term53 m) n). Qed.
Lemma lem7223468 (m : nat) (n : nat) : True = (term52 m n).
Proof. exact (SYM (@lem7223467 m n)). Qed.
Lemma lem7223469 (m : nat) (n : nat) : term52 m n.
Proof. exact (EQ_MP (@lem7223468 m n) (@lem0)). Qed.
Lemma lem7223470 (m : nat) (n : nat) (f : nat -> real) : (term48 m n f) = (term54 m n f).
Proof. exact (@lem7223464 m n f (@lem7223469 m n)). Qed.
Lemma lem7223472 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7223473 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7223472 _2963 g t e g' t' e'). Qed.
Lemma lem7223474 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7223473 _2963 g t e g' t'). Qed.
Lemma lem7223475 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7223474 _2963 g t e g'). Qed.
Lemma lem7223476 (g : Prop) (t : real) (e : real) : term59 g t e.
Proof. exact (@lem7223475 real g t e). Qed.
Lemma lem7223477 (m : nat) (n : nat) (f : nat -> real) : term60 m n f.
Proof. exact (@lem7223476 (term61 m n) (term62 m n f) (term39 m n f)). Qed.
Lemma lem7223478 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : term63 m n f g'.
Proof. exact (@lem7223477 m n f g'). Qed.
Lemma lem7223479 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : (term63 m n f g') = (term64 m n f g').
Proof. exact (eq_refl (term63 m n f g')). Qed.
Lemma lem7223480 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : term64 m n f g'.
Proof. exact (EQ_MP (@lem7223479 m n f g') (@lem7223478 m n f g')). Qed.
Lemma lem7223481 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : term65 m n f g' t'.
Proof. exact (@lem7223480 m n f g' t'). Qed.
Lemma lem7223482 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : (term65 m n f g' t') = (term66 m n f g' t').
Proof. exact (eq_refl (term65 m n f g' t')). Qed.
Lemma lem7223483 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : term66 m n f g' t'.
Proof. exact (EQ_MP (@lem7223482 m n f g' t') (@lem7223481 m n f g' t')). Qed.
Lemma lem7223484 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term67 m n f g' t' e'.
Proof. exact (@lem7223483 m n f g' t' e'). Qed.
Lemma lem7223485 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : (term67 m n f g' t' e') = (term68 m n f g' t' e').
Proof. exact (eq_refl (term67 m n f g' t' e')). Qed.
Lemma lem7223486 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term68 m n f g' t' e'.
Proof. exact (EQ_MP (@lem7223485 m n f g' t' e') (@lem7223484 m n f g' t' e')). Qed.
Lemma lem7223488 (m : nat) (p : nat) (n : nat) : (term17 p m n) = (term18 m p n).
Proof. exact (EQ_MP (@lem7223363 m p n) (@lem7223362 m n p)). Qed.
Lemma lem7223489 (m : nat) (n : nat) : (term61 m n) = (term69 m n).
Proof. exact (@lem7223488 (term53 m) m n). Qed.
Lemma lem7223493 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7223436 m n) (@lem7223435 m n h1)). Qed.
Lemma lem7223494 (m : nat) : (term70 m) = (term70 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem7223495 (m : nat) (n : nat) (h1 : Peano.le m n) : (term69 m n) = (term71 m).
Proof. exact (MK_COMB (@lem7223494 m) (@lem7223493 m n h1)). Qed.
Lemma lem7223497 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7223498 (m : nat) : (term71 m) = (term72 m).
Proof. exact (@lem7223497 (term72 m)). Qed.
Lemma lem7223499 (m : nat) (n : nat) (h1 : Peano.le m n) : (term69 m n) = (term72 m).
Proof. exact (TRANS (@lem7223495 m n h1) (@lem7223498 m)). Qed.
Lemma lem7223500 (m : nat) (n : nat) (h1 : Peano.le m n) : (term61 m n) = (term72 m).
Proof. exact (TRANS (@lem7223489 m n) (@lem7223499 m n h1)). Qed.
Lemma lem7223501 (n : nat) (f : nat -> real) (m : nat) (t' : real) (e' : real) : term73 n f m t' e'.
Proof. exact (@lem7223486 m n f (term72 m) t' e'). Qed.
Lemma lem7223502 (f : nat -> real) (t' : real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term74 n f m t' e'.
Proof. exact (@lem7223501 n f m t' e' (@lem7223500 m n h1)). Qed.
Lemma lem7223511 (m : nat) (n : nat) (f : nat -> real) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7223512 (m : nat) (n : nat) (f : nat -> real) : term75 m n f.
Proof. exact (fun h0 : term72 m => @lem7223511 m n f). Qed.
Lemma lem7223513 (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term76 m n f e'.
Proof. exact (@lem7223502 f (term62 m n f) e' m n h1). Qed.
Lemma lem7223514 (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : Peano.le m n) : term77 m n f e'.
Proof. exact (@lem7223513 f e' m n h1 (@lem7223512 m n f)). Qed.
Lemma lem7223523 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7223524 (m : nat) (n : nat) (f : nat -> real) : term78 m n f.
Proof. exact (fun h0 : term79 m => @lem7223523 m n f). Qed.
Lemma lem7223525 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : term80 m n f.
Proof. exact (@lem7223514 f (term39 m n f) m n h1). Qed.
Lemma lem7223526 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term54 m n f) = (term81 m n f).
Proof. exact (@lem7223525 f m n h1 (@lem7223524 m n f)). Qed.
Lemma lem7223580 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term48 m n f) = (term81 m n f).
Proof. exact (TRANS (@lem7223470 m n f) (@lem7223526 f m n h1)). Qed.
Lemma lem7223581 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n f) = (term81 m n f).
Proof. exact (TRANS (@lem7223460 f m n h1) (@lem7223580 f m n h1)). Qed.
Lemma lem7223582 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7223583 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term82 m n f) = (term83 m n f).
Proof. exact (MK_COMB (@lem7223582) (@lem7223581 f m n h1)). Qed.
Lemma lem7223642 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7223643 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term38 m n f) = (term39 m n f)) = ((term81 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7223583 f m n h1) (@lem7223642 m n f)). Qed.
Lemma lem7223704 (m : nat) (n : nat) (f : nat -> real) : term84 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7223643 f m n h0). Qed.
Lemma lem7223705 (m : nat) (n : nat) (f : nat -> real) : term85 m n f.
Proof. exact (@lem7223434 f m n ((term81 m n f) = (term39 m n f))). Qed.
Lemma lem7223706 (m : nat) (n : nat) (f : nat -> real) : (term86 m n f) = (term87 m n f).
Proof. exact (@lem7223705 m n f (@lem7223704 m n f)). Qed.
Lemma lem7223850 (m : nat) (f : nat -> real) : (term88 m f) = (term89 m f).
Proof. exact (fun_ext (fun n : nat => @lem7223706 m n f)). Qed.
Lemma lem7223994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7223995 (m : nat) (f : nat -> real) : (term90 m f) = (term91 m f).
Proof. exact (MK_COMB (@lem7223994) (@lem7223850 m f)). Qed.
Lemma lem7224143 (f : nat -> real) : (term92 f) = (term93 f).
Proof. exact (fun_ext (fun m : nat => @lem7223995 m f)). Qed.
Lemma lem7224291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224292 (f : nat -> real) : (term94 f) = (term95 f).
Proof. exact (MK_COMB (@lem7224291) (@lem7224143 f)). Qed.
Lemma lem7224444 : term96 = term97.
Proof. exact (fun_ext (fun f : nat -> real => @lem7224292 f)). Qed.
Lemma lem7224596 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7224597 : term98 = term99.
Proof. exact (MK_COMB (@lem7224596) (@lem7224444)). Qed.
Lemma lem7224753 : term99 = term98.
Proof. exact (SYM (@lem7224597)). Qed.
Lemma lem7224774 (m : nat) (h1 : (term72 m) = False) : (term72 m) = False.
Proof. exact (h1). Qed.
Lemma lem7224775 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7224776 (m : nat) (h1 : (term72 m) = False) : (term100 m) = (@COND real False).
Proof. exact (MK_COMB (@lem7224775) (@lem7224774 m h1)). Qed.
Lemma lem7224777 (m : nat) (n : nat) (f : nat -> real) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7224778 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term101 m n f) = (term102 m n f).
Proof. exact (MK_COMB (@lem7224776 m h1) (@lem7224777 m n f)). Qed.
Lemma lem7224779 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7224780 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term81 m n f) = (term103 m n f).
Proof. exact (MK_COMB (@lem7224778 n f m h1) (@lem7224779 m n f)). Qed.
Lemma lem7224782 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7224783 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7224782 real t1 t2). Qed.
Lemma lem7224784 (m : nat) (n : nat) (f : nat -> real) : (term103 m n f) = (term39 m n f).
Proof. exact (@lem7224783 (term62 m n f) (term39 m n f)). Qed.
Lemma lem7224785 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term81 m n f) = (term39 m n f).
Proof. exact (TRANS (@lem7224780 n f m h1) (@lem7224784 m n f)). Qed.
Lemma lem7224786 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7224787 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term83 m n f) = (term104 m n f).
Proof. exact (MK_COMB (@lem7224786) (@lem7224785 n f m h1)). Qed.
Lemma lem7224788 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7224789 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : ((term81 m n f) = (term39 m n f)) = ((term39 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7224787 n f m h1) (@lem7224788 m n f)). Qed.
Lemma lem7224791 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7224792 (x : real) : (x = x) = True.
Proof. exact (@lem7224791 real x). Qed.
Lemma lem7224793 (m : nat) (n : nat) (f : nat -> real) : ((term39 m n f) = (term39 m n f)) = True.
Proof. exact (@lem7224792 (term39 m n f)). Qed.
Lemma lem7224794 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : ((term81 m n f) = (term39 m n f)) = True.
Proof. exact (TRANS (@lem7224789 n f m h1) (@lem7224793 m n f)). Qed.
Lemma lem7224795 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7224796 (f : nat -> real) (n : nat) (m : nat) (h1 : (term72 m) = False) : (term87 m n f) = (term105 m n).
Proof. exact (MK_COMB (@lem7224795 m n) (@lem7224794 n f m h1)). Qed.
Lemma lem7224798 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7224799 (m : nat) (n : nat) : (term105 m n) = True.
Proof. exact (@lem7224798 (Peano.le m n)). Qed.
Lemma lem7224800 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term87 m n f) = True.
Proof. exact (TRANS (@lem7224796 f n m h1) (@lem7224799 m n)). Qed.
Lemma lem7224801 (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term89 m f) = term106.
Proof. exact (fun_ext (fun n : nat => @lem7224800 n f m h1)). Qed.
Lemma lem7224802 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224803 (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term91 m f) = term107.
Proof. exact (MK_COMB (@lem7224802) (@lem7224801 f m h1)). Qed.
Lemma lem7224805 {A : Type'} (t : Prop) : (term108 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7224806 (t : Prop) : (term109 t) = t.
Proof. exact (@lem7224805 nat t). Qed.
Lemma lem7224807 : term107 = True.
Proof. exact (@lem7224806 True). Qed.
Lemma lem7224808 (f : nat -> real) (m : nat) (h1 : (term72 m) = False) : (term91 m f) = True.
Proof. exact (TRANS (@lem7224803 f m h1) (@lem7224807)). Qed.
Lemma lem7224809 (m : nat) (f : nat -> real) : term110 m f.
Proof. exact (fun h0 : (term72 m) = False => @lem7224808 f m h0). Qed.
Lemma lem7224811 (m : nat) (h1 : (term72 m) = True) : (term72 m) = True.
Proof. exact (h1). Qed.
Lemma lem7224812 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7224813 (m : nat) (h1 : (term72 m) = True) : (term100 m) = (@COND real True).
Proof. exact (MK_COMB (@lem7224812) (@lem7224811 m h1)). Qed.
Lemma lem7224814 (m : nat) (n : nat) (f : nat -> real) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7224815 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term101 m n f) = (term111 m n f).
Proof. exact (MK_COMB (@lem7224813 m h1) (@lem7224814 m n f)). Qed.
Lemma lem7224816 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7224817 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term81 m n f) = (term112 m n f).
Proof. exact (MK_COMB (@lem7224815 n f m h1) (@lem7224816 m n f)). Qed.
Lemma lem7224819 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7224820 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7224819 real t2 t1). Qed.
Lemma lem7224821 (m : nat) (n : nat) (f : nat -> real) : (term112 m n f) = (term62 m n f).
Proof. exact (@lem7224820 (term39 m n f) (term62 m n f)). Qed.
Lemma lem7224822 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term81 m n f) = (term62 m n f).
Proof. exact (TRANS (@lem7224817 n f m h1) (@lem7224821 m n f)). Qed.
Lemma lem7224823 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7224824 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term83 m n f) = (term113 m n f).
Proof. exact (MK_COMB (@lem7224823) (@lem7224822 n f m h1)). Qed.
Lemma lem7224825 (m : nat) (n : nat) (f : nat -> real) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7224826 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : ((term81 m n f) = (term39 m n f)) = ((term62 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7224824 n f m h1) (@lem7224825 m n f)). Qed.
Lemma lem7224829 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7224830 (n : nat) (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term87 m n f) = (term114 m n f).
Proof. exact (MK_COMB (@lem7224829 m n) (@lem7224826 n f m h1)). Qed.
Lemma lem7224833 (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term89 m f) = (term115 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224830 n f m h1)). Qed.
Lemma lem7224834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224835 (f : nat -> real) (m : nat) (h1 : (term72 m) = True) : (term91 m f) = (term116 m f).
Proof. exact (MK_COMB (@lem7224834) (@lem7224833 f m h1)). Qed.
Lemma lem7224840 (m : nat) (f : nat -> real) : term117 m f.
Proof. exact (fun h0 : (term72 m) = True => @lem7224835 f m h0). Qed.
Lemma lem7224841 (m : nat) (f : nat -> real) : term118 m f.
Proof. exact (conj (@lem7224809 m f) (@lem7224840 m f)). Qed.
Lemma lem7224843 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term119 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7224844 (f : nat -> real) (m : nat) : term120 f m.
Proof. exact (@lem7224843 (term91 m f) (term116 m f) (term72 m) True). Qed.
Lemma lem7224845 (f : nat -> real) (m : nat) : (term91 m f) = (term121 f m).
Proof. exact (@lem7224844 f m (@lem7224841 m f)). Qed.
Lemma lem7224847 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7224848 (m : nat) : (term122 m) = True.
Proof. exact (@lem7224847 (term72 m)). Qed.
Lemma lem7224853 (m : nat) (f : nat -> real) : (term123 m f) = (term123 m f).
Proof. exact (eq_refl (term123 m f)). Qed.
Lemma lem7224854 (m : nat) (f : nat -> real) : (term121 f m) = (term124 m f).
Proof. exact (MK_COMB (@lem7224853 m f) (@lem7224848 m)). Qed.
Lemma lem7224856 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7224857 (m : nat) (f : nat -> real) : (term124 m f) = (term125 m f).
Proof. exact (@lem7224856 (term125 m f)). Qed.
Lemma lem7224858 (m : nat) (f : nat -> real) : (term121 f m) = (term125 m f).
Proof. exact (TRANS (@lem7224854 m f) (@lem7224857 m f)). Qed.
Lemma lem7224859 (m : nat) (f : nat -> real) : (term91 m f) = (term125 m f).
Proof. exact (TRANS (@lem7224845 f m) (@lem7224858 m f)). Qed.
Lemma lem7224864 (m : nat) (n : nat) (f : nat -> real) : (term114 m n f) = (term114 m n f).
Proof. exact (eq_refl (term114 m n f)). Qed.
Lemma lem7224865 (m : nat) (f : nat -> real) : (term115 m f) = (term115 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224864 m n f)). Qed.
Lemma lem7224866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224867 (m : nat) (f : nat -> real) : (term116 m f) = (term116 m f).
Proof. exact (MK_COMB (@lem7224866) (@lem7224865 m f)). Qed.
Lemma lem7224872 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224873 (m : nat) (f : nat -> real) : (term125 m f) = (term125 m f).
Proof. exact (MK_COMB (@lem7224872 m) (@lem7224867 m f)). Qed.
Lemma lem7224874 (m : nat) (f : nat -> real) : (term127 m f) = (term127 m f).
Proof. exact (eq_refl (term127 m f)). Qed.
Lemma lem7224875 (m : nat) (f : nat -> real) : ((term91 m f) = (term125 m f)) = ((term91 m f) = (term125 m f)).
Proof. exact (MK_COMB (@lem7224874 m f) (@lem7224873 m f)). Qed.
Lemma lem7224876 (m : nat) (f : nat -> real) : (term91 m f) = (term125 m f).
Proof. exact (EQ_MP (@lem7224875 m f) (@lem7224859 m f)). Qed.
Lemma lem7224877 (f : nat -> real) : (term93 f) = (term128 f).
Proof. exact (fun_ext (fun m : nat => @lem7224876 m f)). Qed.
Lemma lem7224878 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224879 (f : nat -> real) : (term95 f) = (term129 f).
Proof. exact (MK_COMB (@lem7224878) (@lem7224877 f)). Qed.
Lemma lem7224880 : term97 = term130.
Proof. exact (fun_ext (fun f : nat -> real => @lem7224879 f)). Qed.
Lemma lem7224881 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7224883 : term99 = term131.
Proof. exact (MK_COMB (@lem7224881) (@lem7224880)). Qed.
Lemma lem7224891 (m : nat) (n : nat) (f : nat -> real) : (term114 m n f) = (term132 m n f).
Proof. exact (@lem17265 (Peano.le m n) ((term62 m n f) = (term39 m n f))). Qed.
Lemma lem7224892 (m : nat) (f : nat -> real) : (term115 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224891 m n f)). Qed.
Lemma lem7224893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224894 (m : nat) (f : nat -> real) : (term116 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7224893) (@lem7224892 m f)). Qed.
Lemma lem7224896 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224897 (m : nat) (f : nat -> real) : (term125 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7224896 m) (@lem7224894 m f)). Qed.
Lemma lem7224898 (f : nat -> real) : (term128 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7224897 m f)). Qed.
Lemma lem7224899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224900 (f : nat -> real) : (term129 f) = (term137 f).
Proof. exact (MK_COMB (@lem7224899) (@lem7224898 f)). Qed.
Lemma lem7224901 : term130 = term138.
Proof. exact (fun_ext (fun f : nat -> real => @lem7224900 f)). Qed.
Lemma lem7224902 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7224903 : term131 = term139.
Proof. exact (MK_COMB (@lem7224902) (@lem7224901)). Qed.
Lemma lem7224904 : term99 = term139.
Proof. exact (TRANS (@lem7224883) (@lem7224903)). Qed.
Lemma lem7224905 (m : nat) (n : nat) (f : nat -> real) : (term132 m n f) = (term132 m n f).
Proof. exact (eq_refl (term132 m n f)). Qed.
Lemma lem7224906 (m : nat) (f : nat -> real) : (term133 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224905 m n f)). Qed.
Lemma lem7224907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224908 (m : nat) (f : nat -> real) : (term134 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7224907) (@lem7224906 m f)). Qed.
Lemma lem7224911 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224912 (m : nat) (f : nat -> real) : (term135 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7224911 m) (@lem7224908 m f)). Qed.
Lemma lem7224913 (f : nat -> real) : (term136 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7224912 m f)). Qed.
Lemma lem7224914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224915 (f : nat -> real) : (term137 f) = (term137 f).
Proof. exact (MK_COMB (@lem7224914) (@lem7224913 f)). Qed.
Lemma lem7224916 : term138 = term138.
Proof. exact (fun_ext (fun f : nat -> real => @lem7224915 f)). Qed.
Lemma lem7224917 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7224918 : term139 = term139.
Proof. exact (MK_COMB (@lem7224917) (@lem7224916)). Qed.
Lemma lem7224943 : term99 = term139.
Proof. exact (TRANS (@lem7224904) (@lem7224918)). Qed.
Lemma lem7224958 (m : nat) (n : nat) (f : nat -> real) : (term132 m n f) = (term132 m n f).
Proof. exact (eq_refl (term132 m n f)). Qed.
Lemma lem7224959 (m : nat) (f : nat -> real) : (term133 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224958 m n f)). Qed.
Lemma lem7224960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224961 (m : nat) (f : nat -> real) : (term134 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7224960) (@lem7224959 m f)). Qed.
Lemma lem7224976 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224977 (m : nat) (f : nat -> real) : (term135 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7224976 m) (@lem7224961 m f)). Qed.
Lemma lem7224978 (f : nat -> real) : (term136 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7224977 m f)). Qed.
Lemma lem7224979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224980 (f : nat -> real) : (term137 f) = (term137 f).
Proof. exact (MK_COMB (@lem7224979) (@lem7224978 f)). Qed.
Lemma lem7224981 : term138 = term138.
Proof. exact (fun_ext (fun f : nat -> real => @lem7224980 f)). Qed.
Lemma lem7224982 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7224983 : term139 = term139.
Proof. exact (MK_COMB (@lem7224982) (@lem7224981)). Qed.
Lemma lem7224984 : term99 = term139.
Proof. exact (TRANS (@lem7224943) (@lem7224983)). Qed.
Lemma lem7224986 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7224987 (P : Prop) (Q : nat -> Prop) : (term142 P Q) = (term143 P Q).
Proof. exact (@lem7224986 nat P Q). Qed.
Lemma lem7224988 (m : nat) (f : nat -> real) : (term144 m f) = (term145 m f).
Proof. exact (@lem7224987 (term79 m) (term133 m f)). Qed.
Lemma lem7224989 (m : nat) (n : nat) (f : nat -> real) : (term146 m f n) = (term132 m n f).
Proof. exact (eq_refl (term146 m f n)). Qed.
Lemma lem7224990 (m : nat) (f : nat -> real) : (term147 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224989 m n f)). Qed.
Lemma lem7224991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7224992 (m : nat) (f : nat -> real) : (term148 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7224991) (@lem7224990 m f)). Qed.
Lemma lem7224993 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224994 (m : nat) (f : nat -> real) : (term144 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7224993 m) (@lem7224992 m f)). Qed.
Lemma lem7224995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7224996 (m : nat) (f : nat -> real) : (term149 m f) = (term150 m f).
Proof. exact (MK_COMB (@lem7224995) (@lem7224994 m f)). Qed.
Lemma lem7224997 (m : nat) (n : nat) (f : nat -> real) : (term146 m f n) = (term132 m n f).
Proof. exact (eq_refl (term146 m f n)). Qed.
Lemma lem7224998 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7224999 (m : nat) (n : nat) (f : nat -> real) : (term151 m f n) = (term152 m n f).
Proof. exact (MK_COMB (@lem7224998 m) (@lem7224997 m n f)). Qed.
Lemma lem7225000 (m : nat) (f : nat -> real) : (term153 m f) = (term154 m f).
Proof. exact (fun_ext (fun n : nat => @lem7224999 m n f)). Qed.
Lemma lem7225001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7225002 (m : nat) (f : nat -> real) : (term145 m f) = (term155 m f).
Proof. exact (MK_COMB (@lem7225001) (@lem7225000 m f)). Qed.
Lemma lem7225003 (m : nat) (f : nat -> real) : ((term144 m f) = (term145 m f)) = ((term135 m f) = (term155 m f)).
Proof. exact (MK_COMB (@lem7224996 m f) (@lem7225002 m f)). Qed.
Lemma lem7225004 (m : nat) (f : nat -> real) : (term135 m f) = (term155 m f).
Proof. exact (EQ_MP (@lem7225003 m f) (@lem7224988 m f)). Qed.
Lemma lem7225005 (f : nat -> real) : (term136 f) = (term156 f).
Proof. exact (fun_ext (fun m : nat => @lem7225004 m f)). Qed.
Lemma lem7225006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7225007 (f : nat -> real) : (term137 f) = (term157 f).
Proof. exact (MK_COMB (@lem7225006) (@lem7225005 f)). Qed.
Lemma lem7225008 : term138 = term158.
Proof. exact (fun_ext (fun f : nat -> real => @lem7225007 f)). Qed.
Lemma lem7225009 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7225010 : term139 = term159.
Proof. exact (MK_COMB (@lem7225009) (@lem7225008)). Qed.
Lemma lem7225011 : term99 = term159.
Proof. exact (TRANS (@lem7224984) (@lem7225010)). Qed.
Lemma lem7225013 (m : nat) (n : nat) : (Peano.le m n) = (term160 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7225014 (m : nat) : (term72 m) = (term161 m).
Proof. exact (@lem7225013 (term53 m) m). Qed.
Lemma lem7225016 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7225017 (m : nat) : (term164 m) = (term165 m).
Proof. exact (@lem7225016 m term166). Qed.
Lemma lem7225018 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7225019 (m : nat) : (term167 m) = (term168 m).
Proof. exact (MK_COMB (@lem7225018) (@lem7225017 m)). Qed.
Lemma lem7225020 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem7225021 (m : nat) : (term161 m) = (term169 m).
Proof. exact (MK_COMB (@lem7225019 m) (@lem7225020 m)). Qed.
Lemma lem7225022 (m : nat) : (term72 m) = (term169 m).
Proof. exact (TRANS (@lem7225014 m) (@lem7225021 m)). Qed.
Lemma lem7225023 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7225024 (m : nat) : (term79 m) = (term170 m).
Proof. exact (MK_COMB (@lem7225023) (@lem7225022 m)). Qed.
Lemma lem7225025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7225026 (m : nat) : (term126 m) = (term171 m).
Proof. exact (MK_COMB (@lem7225025) (@lem7225024 m)). Qed.
Lemma lem7225028 (m : nat) (n : nat) : (Peano.le m n) = (term160 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7225029 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7225030 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (MK_COMB (@lem7225029) (@lem7225028 m n)). Qed.
Lemma lem7225031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7225032 (m : nat) (n : nat) : (term174 m n) = (term175 m n).
Proof. exact (MK_COMB (@lem7225031) (@lem7225030 m n)). Qed.
Lemma lem7225035 (m : nat) (n : nat) (f : nat -> real) : ((term62 m n f) = (term39 m n f)) = ((term62 m n f) = (term39 m n f)).
Proof. exact (eq_refl ((term62 m n f) = (term39 m n f))). Qed.
Lemma lem7225036 (m : nat) (n : nat) (f : nat -> real) : (term132 m n f) = (term176 m n f).
Proof. exact (MK_COMB (@lem7225032 m n) (@lem7225035 m n f)). Qed.
Lemma lem7225037 (m : nat) (n : nat) (f : nat -> real) : (term152 m n f) = (term177 m n f).
Proof. exact (MK_COMB (@lem7225026 m) (@lem7225036 m n f)). Qed.
Lemma lem7225038 (m : nat) (f : nat -> real) : (term154 m f) = (term178 m f).
Proof. exact (fun_ext (fun n : nat => @lem7225037 m n f)). Qed.
Lemma lem7225039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7225040 (m : nat) (f : nat -> real) : (term155 m f) = (term179 m f).
Proof. exact (MK_COMB (@lem7225039) (@lem7225038 m f)). Qed.
Lemma lem7225041 (f : nat -> real) : (term156 f) = (term180 f).
Proof. exact (fun_ext (fun m : nat => @lem7225040 m f)). Qed.
Lemma lem7225042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7225043 (f : nat -> real) : (term157 f) = (term181 f).
Proof. exact (MK_COMB (@lem7225042) (@lem7225041 f)). Qed.
Lemma lem7225044 : term158 = term182.
Proof. exact (fun_ext (fun f : nat -> real => @lem7225043 f)). Qed.
Lemma lem7225045 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7225046 : term159 = term183.
Proof. exact (MK_COMB (@lem7225045) (@lem7225044)). Qed.
Lemma lem7225047 : term99 = term183.
Proof. exact (TRANS (@lem7225011) (@lem7225046)). Qed.
Lemma lem7225048 (m : nat) : term184 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7225049 (m : nat) : (term184 m) = (term185 m).
Proof. exact (eq_refl (term184 m)). Qed.
Lemma lem7225050 (m : nat) : term185 m.
Proof. exact (EQ_MP (@lem7225049 m) (@lem7225048 m)). Qed.
Lemma lem7225051 (n : nat) : term184 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7225052 (n : nat) : (term184 n) = (term185 n).
Proof. exact (eq_refl (term184 n)). Qed.
Lemma lem7225053 (n : nat) : term185 n.
Proof. exact (EQ_MP (@lem7225052 n) (@lem7225051 n)). Qed.
Lemma lem7225054 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term186 _96845 _96846 m n f) = (term187 _96845 _96846 m n f).
Proof. exact (@lem2318604 (term187 _96845 _96846 m n f)). Qed.
Lemma lem7225072 (_96845 : int) : (term188 _96845) = (term189 _96845).
Proof. exact (@lem16933 (term189 _96845)). Qed.
Lemma lem7225075 (_96845 : int) (_96846 : int) : (term190 _96845 _96846) = (int_le _96845 _96846).
Proof. exact (@lem16933 (int_le _96845 _96846)). Qed.
Lemma lem7225076 (m : nat) (n : nat) (f : nat -> real) : (term191 m n f) = (term191 m n f).
Proof. exact (eq_refl (term191 m n f)). Qed.
Lemma lem7225077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225078 (_96845 : int) (_96846 : int) : (term192 _96845 _96846) = (term193 _96845 _96846).
Proof. exact (MK_COMB (@lem7225077) (@lem7225075 _96845 _96846)). Qed.
Lemma lem7225079 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term194 _96845 _96846 m n f) = (term195 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225078 _96845 _96846) (@lem7225076 m n f)). Qed.
Lemma lem7225080 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term196 _96845 _96846 m n f) = (term194 _96845 _96846 m n f).
Proof. exact (@lem17160 (term197 _96845 _96846) ((term62 m n f) = (term39 m n f))). Qed.
Lemma lem7225081 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term196 _96845 _96846 m n f) = (term195 _96845 _96846 m n f).
Proof. exact (TRANS (@lem7225080 _96845 _96846 m n f) (@lem7225079 _96845 _96846 m n f)). Qed.
Lemma lem7225082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225083 (_96845 : int) : (term198 _96845) = (term199 _96845).
Proof. exact (MK_COMB (@lem7225082) (@lem7225072 _96845)). Qed.
Lemma lem7225084 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term200 _96845 _96846 m n f) = (term201 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225083 _96845) (@lem7225081 _96845 _96846 m n f)). Qed.
Lemma lem7225085 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term202 _96845 _96846 m n f) = (term200 _96845 _96846 m n f).
Proof. exact (@lem17160 (term203 _96845) (term204 _96845 _96846 m n f)). Qed.
Lemma lem7225086 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term202 _96845 _96846 m n f) = (term201 _96845 _96846 m n f).
Proof. exact (TRANS (@lem7225085 _96845 _96846 m n f) (@lem7225084 _96845 _96846 m n f)). Qed.
Lemma lem7225088 (_96846 : int) : (term205 _96846) = (term205 _96846).
Proof. exact (eq_refl (term205 _96846)). Qed.
Lemma lem7225089 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term206 _96845 _96846 m n f) = (term207 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225088 _96846) (@lem7225086 _96845 _96846 m n f)). Qed.
Lemma lem7225090 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term208 _96845 _96846 m n f) = (term206 _96845 _96846 m n f).
Proof. exact (@lem17362 (term209 _96846) (term210 _96845 _96846 m n f)). Qed.
Lemma lem7225091 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term208 _96845 _96846 m n f) = (term207 _96845 _96846 m n f).
Proof. exact (TRANS (@lem7225090 _96845 _96846 m n f) (@lem7225089 _96845 _96846 m n f)). Qed.
Lemma lem7225093 (_96845 : int) : (term205 _96845) = (term205 _96845).
Proof. exact (eq_refl (term205 _96845)). Qed.
Lemma lem7225094 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term211 _96845 _96846 m n f) = (term212 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225093 _96845) (@lem7225091 _96845 _96846 m n f)). Qed.
Lemma lem7225095 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term213 _96845 _96846 m n f) = (term211 _96845 _96846 m n f).
Proof. exact (@lem17362 (term209 _96845) (term214 _96845 _96846 m n f)). Qed.
Lemma lem7225117 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term213 _96845 _96846 m n f) = (term212 _96845 _96846 m n f).
Proof. exact (TRANS (@lem7225095 _96845 _96846 m n f) (@lem7225094 _96845 _96846 m n f)). Qed.
Lemma lem7225120 (x : int) (y : int) : (int_le x y) = (term215 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7225121 (_96845 : int) : (term209 _96845) = (term216 _96845).
Proof. exact (@lem7225120 term217 _96845). Qed.
Lemma lem7225123 (n : nat) : (term218 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7225124 : term219 = term220.
Proof. exact (@lem7225123 (NUMERAL 0)). Qed.
Lemma lem7225125 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225126 : term221 = term222.
Proof. exact (MK_COMB (@lem7225125) (@lem7225124)). Qed.
Lemma lem7225127 (_96845 : int) : (real_of_int _96845) = (real_of_int _96845).
Proof. exact (eq_refl (real_of_int _96845)). Qed.
Lemma lem7225128 (_96845 : int) : (term216 _96845) = (term223 _96845).
Proof. exact (MK_COMB (@lem7225126) (@lem7225127 _96845)). Qed.
Lemma lem7225130 (_96845 : int) : (term209 _96845) = (term223 _96845).
Proof. exact (TRANS (@lem7225121 _96845) (@lem7225128 _96845)). Qed.
Lemma lem7225133 (x : int) (y : int) : (int_le x y) = (term215 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7225134 (_96846 : int) : (term209 _96846) = (term216 _96846).
Proof. exact (@lem7225133 term217 _96846). Qed.
Lemma lem7225136 (n : nat) : (term218 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7225137 : term219 = term220.
Proof. exact (@lem7225136 (NUMERAL 0)). Qed.
Lemma lem7225138 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225139 : term221 = term222.
Proof. exact (MK_COMB (@lem7225138) (@lem7225137)). Qed.
Lemma lem7225140 (_96846 : int) : (real_of_int _96846) = (real_of_int _96846).
Proof. exact (eq_refl (real_of_int _96846)). Qed.
Lemma lem7225141 (_96846 : int) : (term216 _96846) = (term223 _96846).
Proof. exact (MK_COMB (@lem7225139) (@lem7225140 _96846)). Qed.
Lemma lem7225143 (_96846 : int) : (term209 _96846) = (term223 _96846).
Proof. exact (TRANS (@lem7225134 _96846) (@lem7225141 _96846)). Qed.
Lemma lem7225146 (x : int) (y : int) : (int_le x y) = (term215 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7225147 (_96845 : int) : (term189 _96845) = (term224 _96845).
Proof. exact (@lem7225146 (term225 _96845) _96845). Qed.
Lemma lem7225149 (x : int) (y : int) : (term226 x y) = (term227 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7225150 (_96845 : int) : (term228 _96845) = (term229 _96845).
Proof. exact (@lem7225149 _96845 term230). Qed.
Lemma lem7225152 (n : nat) : (term218 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7225153 : term231 = term232.
Proof. exact (@lem7225152 term166). Qed.
Lemma lem7225154 (_96845 : int) : (term233 _96845) = (term233 _96845).
Proof. exact (eq_refl (term233 _96845)). Qed.
Lemma lem7225155 (_96845 : int) : (term229 _96845) = (term234 _96845).
Proof. exact (MK_COMB (@lem7225154 _96845) (@lem7225153)). Qed.
Lemma lem7225156 (_96845 : int) : (term228 _96845) = (term234 _96845).
Proof. exact (TRANS (@lem7225150 _96845) (@lem7225155 _96845)). Qed.
Lemma lem7225157 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225158 (_96845 : int) : (term235 _96845) = (term236 _96845).
Proof. exact (MK_COMB (@lem7225157) (@lem7225156 _96845)). Qed.
Lemma lem7225159 (_96845 : int) : (real_of_int _96845) = (real_of_int _96845).
Proof. exact (eq_refl (real_of_int _96845)). Qed.
Lemma lem7225160 (_96845 : int) : (term224 _96845) = (term237 _96845).
Proof. exact (MK_COMB (@lem7225158 _96845) (@lem7225159 _96845)). Qed.
Lemma lem7225162 (_96845 : int) : (term189 _96845) = (term237 _96845).
Proof. exact (TRANS (@lem7225147 _96845) (@lem7225160 _96845)). Qed.
Lemma lem7225165 (x : int) (y : int) : (int_le x y) = (term215 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7225167 (_96845 : int) (_96846 : int) : (int_le _96845 _96846) = (term215 _96845 _96846).
Proof. exact (@lem7225165 _96845 _96846). Qed.
Lemma lem7225174 (m : nat) (n : nat) (f : nat -> real) : (term191 m n f) = (term191 m n f).
Proof. exact (eq_refl (term191 m n f)). Qed.
Lemma lem7225175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225176 (_96845 : int) (_96846 : int) : (term193 _96845 _96846) = (term238 _96845 _96846).
Proof. exact (MK_COMB (@lem7225175) (@lem7225167 _96845 _96846)). Qed.
Lemma lem7225177 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term195 _96845 _96846 m n f) = (term239 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225176 _96845 _96846) (@lem7225174 m n f)). Qed.
Lemma lem7225178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225179 (_96845 : int) : (term199 _96845) = (term240 _96845).
Proof. exact (MK_COMB (@lem7225178) (@lem7225162 _96845)). Qed.
Lemma lem7225180 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term201 _96845 _96846 m n f) = (term241 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225179 _96845) (@lem7225177 _96845 _96846 m n f)). Qed.
Lemma lem7225181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225182 (_96846 : int) : (term205 _96846) = (term242 _96846).
Proof. exact (MK_COMB (@lem7225181) (@lem7225143 _96846)). Qed.
Lemma lem7225183 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term207 _96845 _96846 m n f) = (term243 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225182 _96846) (@lem7225180 _96845 _96846 m n f)). Qed.
Lemma lem7225184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225185 (_96845 : int) : (term205 _96845) = (term242 _96845).
Proof. exact (MK_COMB (@lem7225184) (@lem7225130 _96845)). Qed.
Lemma lem7225186 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term212 _96845 _96846 m n f) = (term244 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225185 _96845) (@lem7225183 _96845 _96846 m n f)). Qed.
Lemma lem7225187 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term213 _96845 _96846 m n f) = (term244 _96845 _96846 m n f).
Proof. exact (TRANS (@lem7225117 _96845 _96846 m n f) (@lem7225186 _96845 _96846 m n f)). Qed.
Lemma lem7225191 (t : Prop) : (term245 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7225239 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term246 _96845 _96846 m n f) = (term244 _96845 _96846 m n f).
Proof. exact (@lem7225191 (term244 _96845 _96846 m n f)). Qed.
Lemma lem7225240 (_96845 : int) : (term223 _96845) = (term247 _96845).
Proof. exact (@lem1988287 (real_of_int _96845) term220). Qed.
Lemma lem7225246 (_96845 : int) : (term248 _96845) = (term249 _96845).
Proof. exact (@lem1982792 (real_of_int _96845) term220). Qed.
Lemma lem7225248 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225249 : term220 = term251.
Proof. exact (@lem7225248 (NUMERAL 0)). Qed.
Lemma lem7225251 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225252 : term254 = term255.
Proof. exact (@lem7225251 term166). Qed.
Lemma lem7225253 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225254 : term256 = term257.
Proof. exact (MK_COMB (@lem7225253) (@lem7225252)). Qed.
Lemma lem7225255 : term258 = term259.
Proof. exact (MK_COMB (@lem7225254) (@lem7225249)). Qed.
Lemma lem7225256 : term259 = term260.
Proof. exact (@lem1981613 term254 term220 term232 term232). Qed.
Lemma lem7225258 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225259 : term263 = term264.
Proof. exact (@lem7225258 term166 term166). Qed.
Lemma lem7225260 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225261 : term266 = term166.
Proof. exact (EQ_MP (@lem7225260) (@lem940073)). Qed.
Lemma lem7225262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225263 : term264 = term232.
Proof. exact (MK_COMB (@lem7225262) (@lem7225261)). Qed.
Lemma lem7225264 : term263 = term232.
Proof. exact (TRANS (@lem7225259) (@lem7225263)). Qed.
Lemma lem7225266 (x : nat) : (term267 x) = term220.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7225267 : term258 = term220.
Proof. exact (@lem7225266 term166). Qed.
Lemma lem7225268 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7225269 : term268 = term269.
Proof. exact (MK_COMB (@lem7225268) (@lem7225267)). Qed.
Lemma lem7225270 : term260 = term251.
Proof. exact (MK_COMB (@lem7225269) (@lem7225264)). Qed.
Lemma lem7225271 : term259 = term251.
Proof. exact (TRANS (@lem7225256) (@lem7225270)). Qed.
Lemma lem7225272 : term258 = term251.
Proof. exact (TRANS (@lem7225255) (@lem7225271)). Qed.
Lemma lem7225274 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7225275 : term251 = term220.
Proof. exact (@lem7225274 term220). Qed.
Lemma lem7225276 : term258 = term220.
Proof. exact (TRANS (@lem7225272) (@lem7225275)). Qed.
Lemma lem7225277 (_96845 : int) : (term233 _96845) = (term233 _96845).
Proof. exact (eq_refl (term233 _96845)). Qed.
Lemma lem7225278 (_96845 : int) : (term249 _96845) = (term271 _96845).
Proof. exact (MK_COMB (@lem7225277 _96845) (@lem7225276)). Qed.
Lemma lem7225279 (_96845 : int) : (term271 _96845) = (real_of_int _96845).
Proof. exact (@lem1982723 (real_of_int _96845)). Qed.
Lemma lem7225280 (_96845 : int) : (term249 _96845) = (real_of_int _96845).
Proof. exact (TRANS (@lem7225278 _96845) (@lem7225279 _96845)). Qed.
Lemma lem7225282 (_96845 : int) : (term248 _96845) = (real_of_int _96845).
Proof. exact (TRANS (@lem7225246 _96845) (@lem7225280 _96845)). Qed.
Lemma lem7225283 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7225284 (_96845 : int) : (term272 _96845) = (term273 _96845).
Proof. exact (MK_COMB (@lem7225283) (@lem7225282 _96845)). Qed.
Lemma lem7225285 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225286 (_96845 : int) : (term247 _96845) = (term274 _96845).
Proof. exact (MK_COMB (@lem7225284 _96845) (@lem7225285)). Qed.
Lemma lem7225287 (_96845 : int) : (term223 _96845) = (term274 _96845).
Proof. exact (TRANS (@lem7225240 _96845) (@lem7225286 _96845)). Qed.
Lemma lem7225288 (_96846 : int) : (term223 _96846) = (term247 _96846).
Proof. exact (@lem1988287 (real_of_int _96846) term220). Qed.
Lemma lem7225294 (_96846 : int) : (term248 _96846) = (term249 _96846).
Proof. exact (@lem1982792 (real_of_int _96846) term220). Qed.
Lemma lem7225296 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225297 : term220 = term251.
Proof. exact (@lem7225296 (NUMERAL 0)). Qed.
Lemma lem7225299 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225300 : term254 = term255.
Proof. exact (@lem7225299 term166). Qed.
Lemma lem7225301 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225302 : term256 = term257.
Proof. exact (MK_COMB (@lem7225301) (@lem7225300)). Qed.
Lemma lem7225303 : term258 = term259.
Proof. exact (MK_COMB (@lem7225302) (@lem7225297)). Qed.
Lemma lem7225304 : term259 = term260.
Proof. exact (@lem1981613 term254 term220 term232 term232). Qed.
Lemma lem7225306 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225307 : term263 = term264.
Proof. exact (@lem7225306 term166 term166). Qed.
Lemma lem7225308 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225309 : term266 = term166.
Proof. exact (EQ_MP (@lem7225308) (@lem940073)). Qed.
Lemma lem7225310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225311 : term264 = term232.
Proof. exact (MK_COMB (@lem7225310) (@lem7225309)). Qed.
Lemma lem7225312 : term263 = term232.
Proof. exact (TRANS (@lem7225307) (@lem7225311)). Qed.
Lemma lem7225314 (x : nat) : (term267 x) = term220.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7225315 : term258 = term220.
Proof. exact (@lem7225314 term166). Qed.
Lemma lem7225316 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7225317 : term268 = term269.
Proof. exact (MK_COMB (@lem7225316) (@lem7225315)). Qed.
Lemma lem7225318 : term260 = term251.
Proof. exact (MK_COMB (@lem7225317) (@lem7225312)). Qed.
Lemma lem7225319 : term259 = term251.
Proof. exact (TRANS (@lem7225304) (@lem7225318)). Qed.
Lemma lem7225320 : term258 = term251.
Proof. exact (TRANS (@lem7225303) (@lem7225319)). Qed.
Lemma lem7225322 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7225323 : term251 = term220.
Proof. exact (@lem7225322 term220). Qed.
Lemma lem7225324 : term258 = term220.
Proof. exact (TRANS (@lem7225320) (@lem7225323)). Qed.
Lemma lem7225325 (_96846 : int) : (term233 _96846) = (term233 _96846).
Proof. exact (eq_refl (term233 _96846)). Qed.
Lemma lem7225326 (_96846 : int) : (term249 _96846) = (term271 _96846).
Proof. exact (MK_COMB (@lem7225325 _96846) (@lem7225324)). Qed.
Lemma lem7225327 (_96846 : int) : (term271 _96846) = (real_of_int _96846).
Proof. exact (@lem1982723 (real_of_int _96846)). Qed.
Lemma lem7225328 (_96846 : int) : (term249 _96846) = (real_of_int _96846).
Proof. exact (TRANS (@lem7225326 _96846) (@lem7225327 _96846)). Qed.
Lemma lem7225330 (_96846 : int) : (term248 _96846) = (real_of_int _96846).
Proof. exact (TRANS (@lem7225294 _96846) (@lem7225328 _96846)). Qed.
Lemma lem7225331 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7225332 (_96846 : int) : (term272 _96846) = (term273 _96846).
Proof. exact (MK_COMB (@lem7225331) (@lem7225330 _96846)). Qed.
Lemma lem7225333 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225334 (_96846 : int) : (term247 _96846) = (term274 _96846).
Proof. exact (MK_COMB (@lem7225332 _96846) (@lem7225333)). Qed.
Lemma lem7225335 (_96846 : int) : (term223 _96846) = (term274 _96846).
Proof. exact (TRANS (@lem7225288 _96846) (@lem7225334 _96846)). Qed.
Lemma lem7225336 (_96845 : int) : (term237 _96845) = (term275 _96845).
Proof. exact (@lem1988287 (real_of_int _96845) (term234 _96845)). Qed.
Lemma lem7225348 (_96845 : int) : (term276 _96845) = (term277 _96845).
Proof. exact (@lem1982792 (real_of_int _96845) (term234 _96845)). Qed.
Lemma lem7225349 (_96845 : int) : (term278 _96845) = (term279 _96845).
Proof. exact (@lem1982781 (real_of_int _96845) term254 term232). Qed.
Lemma lem7225351 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225352 : term232 = term280.
Proof. exact (@lem7225351 term166). Qed.
Lemma lem7225354 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225355 : term254 = term255.
Proof. exact (@lem7225354 term166). Qed.
Lemma lem7225356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225357 : term256 = term257.
Proof. exact (MK_COMB (@lem7225356) (@lem7225355)). Qed.
Lemma lem7225358 : term281 = term282.
Proof. exact (MK_COMB (@lem7225357) (@lem7225352)). Qed.
Lemma lem7225359 : term282 = term283.
Proof. exact (@lem1981613 term254 term232 term232 term232). Qed.
Lemma lem7225361 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225362 : term263 = term264.
Proof. exact (@lem7225361 term166 term166). Qed.
Lemma lem7225363 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225364 : term266 = term166.
Proof. exact (EQ_MP (@lem7225363) (@lem940073)). Qed.
Lemma lem7225365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225366 : term264 = term232.
Proof. exact (MK_COMB (@lem7225365) (@lem7225364)). Qed.
Lemma lem7225367 : term263 = term232.
Proof. exact (TRANS (@lem7225362) (@lem7225366)). Qed.
Lemma lem7225369 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7225370 : term281 = term286.
Proof. exact (@lem7225369 term166 term166). Qed.
Lemma lem7225371 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225372 : term266 = term166.
Proof. exact (EQ_MP (@lem7225371) (@lem940073)). Qed.
Lemma lem7225373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225374 : term264 = term232.
Proof. exact (MK_COMB (@lem7225373) (@lem7225372)). Qed.
Lemma lem7225375 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225376 : term286 = term254.
Proof. exact (MK_COMB (@lem7225375) (@lem7225374)). Qed.
Lemma lem7225377 : term281 = term254.
Proof. exact (TRANS (@lem7225370) (@lem7225376)). Qed.
Lemma lem7225378 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7225379 : term287 = term288.
Proof. exact (MK_COMB (@lem7225378) (@lem7225377)). Qed.
Lemma lem7225380 : term283 = term255.
Proof. exact (MK_COMB (@lem7225379) (@lem7225367)). Qed.
Lemma lem7225381 : term282 = term255.
Proof. exact (TRANS (@lem7225359) (@lem7225380)). Qed.
Lemma lem7225382 : term281 = term255.
Proof. exact (TRANS (@lem7225358) (@lem7225381)). Qed.
Lemma lem7225384 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7225385 : term255 = term254.
Proof. exact (@lem7225384 term254). Qed.
Lemma lem7225386 : term281 = term254.
Proof. exact (TRANS (@lem7225382) (@lem7225385)). Qed.
Lemma lem7225389 (_96845 : int) : (term289 _96845) = (term289 _96845).
Proof. exact (eq_refl (term289 _96845)). Qed.
Lemma lem7225390 (_96845 : int) : (term279 _96845) = (term290 _96845).
Proof. exact (MK_COMB (@lem7225389 _96845) (@lem7225386)). Qed.
Lemma lem7225391 (_96845 : int) : (term278 _96845) = (term290 _96845).
Proof. exact (TRANS (@lem7225349 _96845) (@lem7225390 _96845)). Qed.
Lemma lem7225392 (_96845 : int) : (term233 _96845) = (term233 _96845).
Proof. exact (eq_refl (term233 _96845)). Qed.
Lemma lem7225393 (_96845 : int) : (term277 _96845) = (term291 _96845).
Proof. exact (MK_COMB (@lem7225392 _96845) (@lem7225391 _96845)). Qed.
Lemma lem7225394 (_96845 : int) : (term291 _96845) = (term292 _96845).
Proof. exact (@lem1982763 (real_of_int _96845) (term293 _96845) term254). Qed.
Lemma lem7225395 (_96845 : int) : (term294 _96845) = (term295 _96845).
Proof. exact (@lem1982715 term254 (real_of_int _96845)). Qed.
Lemma lem7225397 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225398 : term232 = term280.
Proof. exact (@lem7225397 term166). Qed.
Lemma lem7225400 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225401 : term254 = term255.
Proof. exact (@lem7225400 term166). Qed.
Lemma lem7225402 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7225403 : term296 = term297.
Proof. exact (MK_COMB (@lem7225402) (@lem7225401)). Qed.
Lemma lem7225404 : term298 = term299.
Proof. exact (MK_COMB (@lem7225403) (@lem7225398)). Qed.
Lemma lem7225405 : term300.
Proof. exact (@lem1981473 term254 term232 term232 term232 term220 term232). Qed.
Lemma lem7225407 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225408 : term302 = term303.
Proof. exact (@lem7225407 (NUMERAL 0) term166). Qed.
Lemma lem7225409 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225410 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225411 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225410 h1) (fun h1 : term303 = True => @lem7225409)). Qed.
Lemma lem7225412 : term303 = True.
Proof. exact (EQ_MP (@lem7225411) (@lem7225409)). Qed.
Lemma lem7225413 : term302 = True.
Proof. exact (TRANS (@lem7225408) (@lem7225412)). Qed.
Lemma lem7225414 : True = term302.
Proof. exact (SYM (@lem7225413)). Qed.
Lemma lem7225415 : term302.
Proof. exact (EQ_MP (@lem7225414) (@lem0)). Qed.
Lemma lem7225416 : term305.
Proof. exact (@lem7225405 (@lem7225415)). Qed.
Lemma lem7225418 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225419 : term302 = term303.
Proof. exact (@lem7225418 (NUMERAL 0) term166). Qed.
Lemma lem7225420 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225421 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225422 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225421 h1) (fun h1 : term303 = True => @lem7225420)). Qed.
Lemma lem7225423 : term303 = True.
Proof. exact (EQ_MP (@lem7225422) (@lem7225420)). Qed.
Lemma lem7225424 : term302 = True.
Proof. exact (TRANS (@lem7225419) (@lem7225423)). Qed.
Lemma lem7225425 : True = term302.
Proof. exact (SYM (@lem7225424)). Qed.
Lemma lem7225426 : term302.
Proof. exact (EQ_MP (@lem7225425) (@lem0)). Qed.
Lemma lem7225427 : term306.
Proof. exact (@lem7225416 (@lem7225426)). Qed.
Lemma lem7225429 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225430 : term302 = term303.
Proof. exact (@lem7225429 (NUMERAL 0) term166). Qed.
Lemma lem7225431 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225432 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225433 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225432 h1) (fun h1 : term303 = True => @lem7225431)). Qed.
Lemma lem7225434 : term303 = True.
Proof. exact (EQ_MP (@lem7225433) (@lem7225431)). Qed.
Lemma lem7225435 : term302 = True.
Proof. exact (TRANS (@lem7225430) (@lem7225434)). Qed.
Lemma lem7225436 : True = term302.
Proof. exact (SYM (@lem7225435)). Qed.
Lemma lem7225437 : term302.
Proof. exact (EQ_MP (@lem7225436) (@lem0)). Qed.
Lemma lem7225438 : term307.
Proof. exact (@lem7225427 (@lem7225437)). Qed.
Lemma lem7225440 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225441 : term263 = term264.
Proof. exact (@lem7225440 term166 term166). Qed.
Lemma lem7225442 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225443 : term266 = term166.
Proof. exact (EQ_MP (@lem7225442) (@lem940073)). Qed.
Lemma lem7225444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225445 : term264 = term232.
Proof. exact (MK_COMB (@lem7225444) (@lem7225443)). Qed.
Lemma lem7225446 : term263 = term232.
Proof. exact (TRANS (@lem7225441) (@lem7225445)). Qed.
Lemma lem7225448 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7225449 : term281 = term286.
Proof. exact (@lem7225448 term166 term166). Qed.
Lemma lem7225450 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225451 : term266 = term166.
Proof. exact (EQ_MP (@lem7225450) (@lem940073)). Qed.
Lemma lem7225452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225453 : term264 = term232.
Proof. exact (MK_COMB (@lem7225452) (@lem7225451)). Qed.
Lemma lem7225454 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225455 : term286 = term254.
Proof. exact (MK_COMB (@lem7225454) (@lem7225453)). Qed.
Lemma lem7225456 : term281 = term254.
Proof. exact (TRANS (@lem7225449) (@lem7225455)). Qed.
Lemma lem7225457 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7225458 : term308 = term296.
Proof. exact (MK_COMB (@lem7225457) (@lem7225456)). Qed.
Lemma lem7225459 : term309 = term298.
Proof. exact (MK_COMB (@lem7225458) (@lem7225446)). Qed.
Lemma lem7225461 (m : nat) : (term310 m) = term220.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7225462 : term298 = term220.
Proof. exact (@lem7225461 term166). Qed.
Lemma lem7225463 : term309 = term220.
Proof. exact (TRANS (@lem7225459) (@lem7225462)). Qed.
Lemma lem7225464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225465 : term311 = term312.
Proof. exact (MK_COMB (@lem7225464) (@lem7225463)). Qed.
Lemma lem7225466 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem7225467 : term313 = term314.
Proof. exact (MK_COMB (@lem7225465) (@lem7225466)). Qed.
Lemma lem7225469 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225470 : term314 = term220.
Proof. exact (@lem7225469 term166). Qed.
Lemma lem7225471 : term313 = term220.
Proof. exact (TRANS (@lem7225467) (@lem7225470)). Qed.
Lemma lem7225473 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225474 : term263 = term264.
Proof. exact (@lem7225473 term166 term166). Qed.
Lemma lem7225475 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225476 : term266 = term166.
Proof. exact (EQ_MP (@lem7225475) (@lem940073)). Qed.
Lemma lem7225477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225478 : term264 = term232.
Proof. exact (MK_COMB (@lem7225477) (@lem7225476)). Qed.
Lemma lem7225479 : term263 = term232.
Proof. exact (TRANS (@lem7225474) (@lem7225478)). Qed.
Lemma lem7225480 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem7225481 : term316 = term314.
Proof. exact (MK_COMB (@lem7225480) (@lem7225479)). Qed.
Lemma lem7225483 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225484 : term314 = term220.
Proof. exact (@lem7225483 term166). Qed.
Lemma lem7225485 : term316 = term220.
Proof. exact (TRANS (@lem7225481) (@lem7225484)). Qed.
Lemma lem7225486 : term220 = term316.
Proof. exact (SYM (@lem7225485)). Qed.
Lemma lem7225487 : term313 = term316.
Proof. exact (TRANS (@lem7225471) (@lem7225486)). Qed.
Lemma lem7225488 : term299 = term251.
Proof. exact (@lem7225438 (@lem7225487)). Qed.
Lemma lem7225489 : term298 = term251.
Proof. exact (TRANS (@lem7225404) (@lem7225488)). Qed.
Lemma lem7225491 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7225492 : term251 = term220.
Proof. exact (@lem7225491 term220). Qed.
Lemma lem7225493 : term298 = term220.
Proof. exact (TRANS (@lem7225489) (@lem7225492)). Qed.
Lemma lem7225494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225495 : term317 = term312.
Proof. exact (MK_COMB (@lem7225494) (@lem7225493)). Qed.
Lemma lem7225496 (_96845 : int) : (real_of_int _96845) = (real_of_int _96845).
Proof. exact (eq_refl (real_of_int _96845)). Qed.
Lemma lem7225497 (_96845 : int) : (term295 _96845) = (term318 _96845).
Proof. exact (MK_COMB (@lem7225495) (@lem7225496 _96845)). Qed.
Lemma lem7225498 (_96845 : int) : (term294 _96845) = (term318 _96845).
Proof. exact (TRANS (@lem7225395 _96845) (@lem7225497 _96845)). Qed.
Lemma lem7225499 (_96845 : int) : (term318 _96845) = term220.
Proof. exact (@lem1982719 (real_of_int _96845)). Qed.
Lemma lem7225500 (_96845 : int) : (term294 _96845) = term220.
Proof. exact (TRANS (@lem7225498 _96845) (@lem7225499 _96845)). Qed.
Lemma lem7225501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7225502 (_96845 : int) : (term319 _96845) = term320.
Proof. exact (MK_COMB (@lem7225501) (@lem7225500 _96845)). Qed.
Lemma lem7225503 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem7225504 (_96845 : int) : (term292 _96845) = term321.
Proof. exact (MK_COMB (@lem7225502 _96845) (@lem7225503)). Qed.
Lemma lem7225505 (_96845 : int) : (term291 _96845) = term321.
Proof. exact (TRANS (@lem7225394 _96845) (@lem7225504 _96845)). Qed.
Lemma lem7225506 : term321 = term254.
Proof. exact (@lem1982721 term254). Qed.
Lemma lem7225507 (_96845 : int) : (term291 _96845) = term254.
Proof. exact (TRANS (@lem7225505 _96845) (@lem7225506)). Qed.
Lemma lem7225508 (_96845 : int) : (term277 _96845) = term254.
Proof. exact (TRANS (@lem7225393 _96845) (@lem7225507 _96845)). Qed.
Lemma lem7225510 (_96845 : int) : (term276 _96845) = term254.
Proof. exact (TRANS (@lem7225348 _96845) (@lem7225508 _96845)). Qed.
Lemma lem7225511 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7225512 (_96845 : int) : (term322 _96845) = term323.
Proof. exact (MK_COMB (@lem7225511) (@lem7225510 _96845)). Qed.
Lemma lem7225513 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225514 (_96845 : int) : (term275 _96845) = term324.
Proof. exact (MK_COMB (@lem7225512 _96845) (@lem7225513)). Qed.
Lemma lem7225515 (_96845 : int) : (term237 _96845) = term324.
Proof. exact (TRANS (@lem7225336 _96845) (@lem7225514 _96845)). Qed.
Lemma lem7225516 (_96846 : int) (_96845 : int) : (term215 _96845 _96846) = (term325 _96846 _96845).
Proof. exact (@lem1988287 (real_of_int _96846) (real_of_int _96845)). Qed.
Lemma lem7225522 (_96846 : int) (_96845 : int) : (term326 _96846 _96845) = (term327 _96846 _96845).
Proof. exact (@lem1982792 (real_of_int _96846) (real_of_int _96845)). Qed.
Lemma lem7225527 (_96845 : int) (_96846 : int) : (term327 _96846 _96845) = (term328 _96845 _96846).
Proof. exact (@lem1982761 (term293 _96845) (real_of_int _96846)). Qed.
Lemma lem7225529 (_96845 : int) (_96846 : int) : (term326 _96846 _96845) = (term328 _96845 _96846).
Proof. exact (TRANS (@lem7225522 _96846 _96845) (@lem7225527 _96845 _96846)). Qed.
Lemma lem7225530 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7225531 (_96845 : int) (_96846 : int) : (term329 _96846 _96845) = (term330 _96845 _96846).
Proof. exact (MK_COMB (@lem7225530) (@lem7225529 _96845 _96846)). Qed.
Lemma lem7225532 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225533 (_96845 : int) (_96846 : int) : (term325 _96846 _96845) = (term331 _96845 _96846).
Proof. exact (MK_COMB (@lem7225531 _96845 _96846) (@lem7225532)). Qed.
Lemma lem7225534 (_96845 : int) (_96846 : int) : (term215 _96845 _96846) = (term331 _96845 _96846).
Proof. exact (TRANS (@lem7225516 _96846 _96845) (@lem7225533 _96845 _96846)). Qed.
Lemma lem7225535 (m : nat) (n : nat) (f : nat -> real) : (term191 m n f) = (term332 m n f).
Proof. exact (@lem1988318 (term62 m n f) (term39 m n f)). Qed.
Lemma lem7225547 (m : nat) (n : nat) (f : nat -> real) : (term333 m n f) = (term334 m n f).
Proof. exact (@lem1982792 (term62 m n f) (term39 m n f)). Qed.
Lemma lem7225554 (m : nat) (n : nat) (f : nat -> real) : (term335 m n f) = (term336 m n f).
Proof. exact (@lem1982781 (f m) term254 (term62 m n f)). Qed.
Lemma lem7225555 (m : nat) (n : nat) (f : nat -> real) : (term337 m n f) = (term337 m n f).
Proof. exact (eq_refl (term337 m n f)). Qed.
Lemma lem7225556 (m : nat) (n : nat) (f : nat -> real) : (term334 m n f) = (term338 m n f).
Proof. exact (MK_COMB (@lem7225555 m n f) (@lem7225554 m n f)). Qed.
Lemma lem7225557 (m : nat) (n : nat) (f : nat -> real) : (term338 m n f) = (term339 m n f).
Proof. exact (@lem1982757 (term340 f m) (term62 m n f) (term341 m n f)). Qed.
Lemma lem7225558 (m : nat) (n : nat) (f : nat -> real) : (term342 m n f) = (term343 m n f).
Proof. exact (@lem1982715 term254 (term62 m n f)). Qed.
Lemma lem7225560 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225561 : term232 = term280.
Proof. exact (@lem7225560 term166). Qed.
Lemma lem7225563 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225564 : term254 = term255.
Proof. exact (@lem7225563 term166). Qed.
Lemma lem7225565 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7225566 : term296 = term297.
Proof. exact (MK_COMB (@lem7225565) (@lem7225564)). Qed.
Lemma lem7225567 : term298 = term299.
Proof. exact (MK_COMB (@lem7225566) (@lem7225561)). Qed.
Lemma lem7225568 : term300.
Proof. exact (@lem1981473 term254 term232 term232 term232 term220 term232). Qed.
Lemma lem7225570 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225571 : term302 = term303.
Proof. exact (@lem7225570 (NUMERAL 0) term166). Qed.
Lemma lem7225572 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225573 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225574 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225573 h1) (fun h1 : term303 = True => @lem7225572)). Qed.
Lemma lem7225575 : term303 = True.
Proof. exact (EQ_MP (@lem7225574) (@lem7225572)). Qed.
Lemma lem7225576 : term302 = True.
Proof. exact (TRANS (@lem7225571) (@lem7225575)). Qed.
Lemma lem7225577 : True = term302.
Proof. exact (SYM (@lem7225576)). Qed.
Lemma lem7225578 : term302.
Proof. exact (EQ_MP (@lem7225577) (@lem0)). Qed.
Lemma lem7225579 : term305.
Proof. exact (@lem7225568 (@lem7225578)). Qed.
Lemma lem7225581 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225582 : term302 = term303.
Proof. exact (@lem7225581 (NUMERAL 0) term166). Qed.
Lemma lem7225583 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225584 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225585 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225584 h1) (fun h1 : term303 = True => @lem7225583)). Qed.
Lemma lem7225586 : term303 = True.
Proof. exact (EQ_MP (@lem7225585) (@lem7225583)). Qed.
Lemma lem7225587 : term302 = True.
Proof. exact (TRANS (@lem7225582) (@lem7225586)). Qed.
Lemma lem7225588 : True = term302.
Proof. exact (SYM (@lem7225587)). Qed.
Lemma lem7225589 : term302.
Proof. exact (EQ_MP (@lem7225588) (@lem0)). Qed.
Lemma lem7225590 : term306.
Proof. exact (@lem7225579 (@lem7225589)). Qed.
Lemma lem7225592 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225593 : term302 = term303.
Proof. exact (@lem7225592 (NUMERAL 0) term166). Qed.
Lemma lem7225594 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225595 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225596 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225595 h1) (fun h1 : term303 = True => @lem7225594)). Qed.
Lemma lem7225597 : term303 = True.
Proof. exact (EQ_MP (@lem7225596) (@lem7225594)). Qed.
Lemma lem7225598 : term302 = True.
Proof. exact (TRANS (@lem7225593) (@lem7225597)). Qed.
Lemma lem7225599 : True = term302.
Proof. exact (SYM (@lem7225598)). Qed.
Lemma lem7225600 : term302.
Proof. exact (EQ_MP (@lem7225599) (@lem0)). Qed.
Lemma lem7225601 : term307.
Proof. exact (@lem7225590 (@lem7225600)). Qed.
Lemma lem7225603 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225604 : term263 = term264.
Proof. exact (@lem7225603 term166 term166). Qed.
Lemma lem7225605 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225606 : term266 = term166.
Proof. exact (EQ_MP (@lem7225605) (@lem940073)). Qed.
Lemma lem7225607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225608 : term264 = term232.
Proof. exact (MK_COMB (@lem7225607) (@lem7225606)). Qed.
Lemma lem7225609 : term263 = term232.
Proof. exact (TRANS (@lem7225604) (@lem7225608)). Qed.
Lemma lem7225611 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7225612 : term281 = term286.
Proof. exact (@lem7225611 term166 term166). Qed.
Lemma lem7225613 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225614 : term266 = term166.
Proof. exact (EQ_MP (@lem7225613) (@lem940073)). Qed.
Lemma lem7225615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225616 : term264 = term232.
Proof. exact (MK_COMB (@lem7225615) (@lem7225614)). Qed.
Lemma lem7225617 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225618 : term286 = term254.
Proof. exact (MK_COMB (@lem7225617) (@lem7225616)). Qed.
Lemma lem7225619 : term281 = term254.
Proof. exact (TRANS (@lem7225612) (@lem7225618)). Qed.
Lemma lem7225620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7225621 : term308 = term296.
Proof. exact (MK_COMB (@lem7225620) (@lem7225619)). Qed.
Lemma lem7225622 : term309 = term298.
Proof. exact (MK_COMB (@lem7225621) (@lem7225609)). Qed.
Lemma lem7225624 (m : nat) : (term310 m) = term220.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7225625 : term298 = term220.
Proof. exact (@lem7225624 term166). Qed.
Lemma lem7225626 : term309 = term220.
Proof. exact (TRANS (@lem7225622) (@lem7225625)). Qed.
Lemma lem7225627 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225628 : term311 = term312.
Proof. exact (MK_COMB (@lem7225627) (@lem7225626)). Qed.
Lemma lem7225629 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem7225630 : term313 = term314.
Proof. exact (MK_COMB (@lem7225628) (@lem7225629)). Qed.
Lemma lem7225632 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225633 : term314 = term220.
Proof. exact (@lem7225632 term166). Qed.
Lemma lem7225634 : term313 = term220.
Proof. exact (TRANS (@lem7225630) (@lem7225633)). Qed.
Lemma lem7225636 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225637 : term263 = term264.
Proof. exact (@lem7225636 term166 term166). Qed.
Lemma lem7225638 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225639 : term266 = term166.
Proof. exact (EQ_MP (@lem7225638) (@lem940073)). Qed.
Lemma lem7225640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225641 : term264 = term232.
Proof. exact (MK_COMB (@lem7225640) (@lem7225639)). Qed.
Lemma lem7225642 : term263 = term232.
Proof. exact (TRANS (@lem7225637) (@lem7225641)). Qed.
Lemma lem7225643 : term312 = term312.
Proof. exact (eq_refl term312). Qed.
Lemma lem7225644 : term316 = term314.
Proof. exact (MK_COMB (@lem7225643) (@lem7225642)). Qed.
Lemma lem7225646 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225647 : term314 = term220.
Proof. exact (@lem7225646 term166). Qed.
Lemma lem7225648 : term316 = term220.
Proof. exact (TRANS (@lem7225644) (@lem7225647)). Qed.
Lemma lem7225649 : term220 = term316.
Proof. exact (SYM (@lem7225648)). Qed.
Lemma lem7225650 : term313 = term316.
Proof. exact (TRANS (@lem7225634) (@lem7225649)). Qed.
Lemma lem7225651 : term299 = term251.
Proof. exact (@lem7225601 (@lem7225650)). Qed.
Lemma lem7225652 : term298 = term251.
Proof. exact (TRANS (@lem7225567) (@lem7225651)). Qed.
Lemma lem7225654 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7225655 : term251 = term220.
Proof. exact (@lem7225654 term220). Qed.
Lemma lem7225656 : term298 = term220.
Proof. exact (TRANS (@lem7225652) (@lem7225655)). Qed.
Lemma lem7225657 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225658 : term317 = term312.
Proof. exact (MK_COMB (@lem7225657) (@lem7225656)). Qed.
Lemma lem7225659 (m : nat) (n : nat) (f : nat -> real) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7225660 (m : nat) (n : nat) (f : nat -> real) : (term343 m n f) = (term344 m n f).
Proof. exact (MK_COMB (@lem7225658) (@lem7225659 m n f)). Qed.
Lemma lem7225661 (m : nat) (n : nat) (f : nat -> real) : (term342 m n f) = (term344 m n f).
Proof. exact (TRANS (@lem7225558 m n f) (@lem7225660 m n f)). Qed.
Lemma lem7225662 (m : nat) (n : nat) (f : nat -> real) : (term344 m n f) = term220.
Proof. exact (@lem1982719 (term62 m n f)). Qed.
Lemma lem7225663 (m : nat) (n : nat) (f : nat -> real) : (term342 m n f) = term220.
Proof. exact (TRANS (@lem7225661 m n f) (@lem7225662 m n f)). Qed.
Lemma lem7225664 (f : nat -> real) (m : nat) : (term345 f m) = (term345 f m).
Proof. exact (eq_refl (term345 f m)). Qed.
Lemma lem7225665 (n : nat) (f : nat -> real) (m : nat) : (term339 m n f) = (term346 f m).
Proof. exact (MK_COMB (@lem7225664 f m) (@lem7225663 m n f)). Qed.
Lemma lem7225666 (n : nat) (f : nat -> real) (m : nat) : (term338 m n f) = (term346 f m).
Proof. exact (TRANS (@lem7225557 m n f) (@lem7225665 n f m)). Qed.
Lemma lem7225667 (f : nat -> real) (m : nat) : (term346 f m) = (term340 f m).
Proof. exact (@lem1982723 (term340 f m)). Qed.
Lemma lem7225668 (n : nat) (f : nat -> real) (m : nat) : (term338 m n f) = (term340 f m).
Proof. exact (TRANS (@lem7225666 n f m) (@lem7225667 f m)). Qed.
Lemma lem7225669 (n : nat) (f : nat -> real) (m : nat) : (term334 m n f) = (term340 f m).
Proof. exact (TRANS (@lem7225556 m n f) (@lem7225668 n f m)). Qed.
Lemma lem7225671 (n : nat) (f : nat -> real) (m : nat) : (term333 m n f) = (term340 f m).
Proof. exact (TRANS (@lem7225547 m n f) (@lem7225669 n f m)). Qed.
Lemma lem7225672 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225673 (n : nat) (f : nat -> real) (m : nat) : (term347 m n f) = (term348 f m).
Proof. exact (MK_COMB (@lem7225672) (@lem7225671 n f m)). Qed.
Lemma lem7225674 (f : nat -> real) (m : nat) : (term348 f m) = (term349 f m).
Proof. exact (@lem1982785 (term340 f m)). Qed.
Lemma lem7225675 (f : nat -> real) (m : nat) : (term349 f m) = (term350 f m).
Proof. exact (@lem1982749 term254 term254 (f m)). Qed.
Lemma lem7225677 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225678 : term254 = term255.
Proof. exact (@lem7225677 term166). Qed.
Lemma lem7225680 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225681 : term254 = term255.
Proof. exact (@lem7225680 term166). Qed.
Lemma lem7225682 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225683 : term256 = term257.
Proof. exact (MK_COMB (@lem7225682) (@lem7225681)). Qed.
Lemma lem7225684 : term351 = term352.
Proof. exact (MK_COMB (@lem7225683) (@lem7225678)). Qed.
Lemma lem7225685 : term352 = term353.
Proof. exact (@lem1981613 term254 term254 term232 term232). Qed.
Lemma lem7225687 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7225688 : term263 = term264.
Proof. exact (@lem7225687 term166 term166). Qed.
Lemma lem7225689 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225690 : term266 = term166.
Proof. exact (EQ_MP (@lem7225689) (@lem940073)). Qed.
Lemma lem7225691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225692 : term264 = term232.
Proof. exact (MK_COMB (@lem7225691) (@lem7225690)). Qed.
Lemma lem7225693 : term263 = term232.
Proof. exact (TRANS (@lem7225688) (@lem7225692)). Qed.
Lemma lem7225695 (m : nat) (n : nat) : (term354 m n) = (term262 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7225696 : term351 = term264.
Proof. exact (@lem7225695 term166 term166). Qed.
Lemma lem7225697 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225698 : term266 = term166.
Proof. exact (EQ_MP (@lem7225697) (@lem940073)). Qed.
Lemma lem7225699 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225700 : term264 = term232.
Proof. exact (MK_COMB (@lem7225699) (@lem7225698)). Qed.
Lemma lem7225701 : term351 = term232.
Proof. exact (TRANS (@lem7225696) (@lem7225700)). Qed.
Lemma lem7225702 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7225703 : term355 = term356.
Proof. exact (MK_COMB (@lem7225702) (@lem7225701)). Qed.
Lemma lem7225704 : term353 = term280.
Proof. exact (MK_COMB (@lem7225703) (@lem7225693)). Qed.
Lemma lem7225705 : term352 = term280.
Proof. exact (TRANS (@lem7225685) (@lem7225704)). Qed.
Lemma lem7225706 : term351 = term280.
Proof. exact (TRANS (@lem7225684) (@lem7225705)). Qed.
Lemma lem7225708 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7225709 : term280 = term232.
Proof. exact (@lem7225708 term232). Qed.
Lemma lem7225710 : term351 = term232.
Proof. exact (TRANS (@lem7225706) (@lem7225709)). Qed.
Lemma lem7225711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7225712 : term357 = term358.
Proof. exact (MK_COMB (@lem7225711) (@lem7225710)). Qed.
Lemma lem7225713 (f : nat -> real) (m : nat) : (f m) = (f m).
Proof. exact (eq_refl (f m)). Qed.
Lemma lem7225714 (f : nat -> real) (m : nat) : (term350 f m) = (term359 f m).
Proof. exact (MK_COMB (@lem7225712) (@lem7225713 f m)). Qed.
Lemma lem7225715 (f : nat -> real) (m : nat) : (term349 f m) = (term359 f m).
Proof. exact (TRANS (@lem7225675 f m) (@lem7225714 f m)). Qed.
Lemma lem7225716 (f : nat -> real) (m : nat) : (term359 f m) = (f m).
Proof. exact (@lem1982709 (f m)). Qed.
Lemma lem7225717 (f : nat -> real) (m : nat) : (term349 f m) = (f m).
Proof. exact (TRANS (@lem7225715 f m) (@lem7225716 f m)). Qed.
Lemma lem7225718 (f : nat -> real) (m : nat) : (term348 f m) = (f m).
Proof. exact (TRANS (@lem7225674 f m) (@lem7225717 f m)). Qed.
Lemma lem7225719 (m : nat) (n : nat) (f : nat -> real) : (term360 m n f) = (term360 m n f).
Proof. exact (eq_refl (term360 m n f)). Qed.
Lemma lem7225720 (n : nat) (f : nat -> real) (m : nat) : ((term347 m n f) = (term348 f m)) = ((term347 m n f) = (f m)).
Proof. exact (MK_COMB (@lem7225719 m n f) (@lem7225718 f m)). Qed.
Lemma lem7225721 (n : nat) (f : nat -> real) (m : nat) : (term347 m n f) = (f m).
Proof. exact (EQ_MP (@lem7225720 n f m) (@lem7225673 n f m)). Qed.
Lemma lem7225722 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7225723 (n : nat) (f : nat -> real) (m : nat) : (term361 m n f) = (term362 f m).
Proof. exact (MK_COMB (@lem7225722) (@lem7225721 n f m)). Qed.
Lemma lem7225724 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225725 (n : nat) (f : nat -> real) (m : nat) : (term363 m n f) = (term364 f m).
Proof. exact (MK_COMB (@lem7225723 n f m) (@lem7225724)). Qed.
Lemma lem7225726 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7225727 (n : nat) (f : nat -> real) (m : nat) : (term365 m n f) = (term366 f m).
Proof. exact (MK_COMB (@lem7225726) (@lem7225671 n f m)). Qed.
Lemma lem7225728 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem7225729 (n : nat) (f : nat -> real) (m : nat) : (term367 m n f) = (term368 f m).
Proof. exact (MK_COMB (@lem7225727 n f m) (@lem7225728)). Qed.
Lemma lem7225730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7225731 (n : nat) (f : nat -> real) (m : nat) : (term369 m n f) = (term370 f m).
Proof. exact (MK_COMB (@lem7225730) (@lem7225729 n f m)). Qed.
Lemma lem7225732 (n : nat) (f : nat -> real) (m : nat) : (term332 m n f) = (term371 f m).
Proof. exact (MK_COMB (@lem7225731 n f m) (@lem7225725 n f m)). Qed.
Lemma lem7225733 (n : nat) (f : nat -> real) (m : nat) : (term191 m n f) = (term371 f m).
Proof. exact (TRANS (@lem7225535 m n f) (@lem7225732 n f m)). Qed.
Lemma lem7225734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225735 (_96845 : int) (_96846 : int) : (term238 _96845 _96846) = (term372 _96845 _96846).
Proof. exact (MK_COMB (@lem7225734) (@lem7225534 _96845 _96846)). Qed.
Lemma lem7225736 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term239 _96845 _96846 m n f) = (term373 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225735 _96845 _96846) (@lem7225733 n f m)). Qed.
Lemma lem7225737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225738 (_96845 : int) : (term240 _96845) = term374.
Proof. exact (MK_COMB (@lem7225737) (@lem7225515 _96845)). Qed.
Lemma lem7225739 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term241 _96845 _96846 m n f) = (term375 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225738 _96845) (@lem7225736 n _96845 _96846 f m)). Qed.
Lemma lem7225740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225741 (_96846 : int) : (term242 _96846) = (term376 _96846).
Proof. exact (MK_COMB (@lem7225740) (@lem7225335 _96846)). Qed.
Lemma lem7225742 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term243 _96845 _96846 m n f) = (term377 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225741 _96846) (@lem7225739 n _96845 _96846 f m)). Qed.
Lemma lem7225743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225744 (_96845 : int) : (term242 _96845) = (term376 _96845).
Proof. exact (MK_COMB (@lem7225743) (@lem7225287 _96845)). Qed.
Lemma lem7225745 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term244 _96845 _96846 m n f) = (term378 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225744 _96845) (@lem7225742 n _96845 _96846 f m)). Qed.
Lemma lem7225752 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term246 _96845 _96846 m n f) = (term378 _96845 _96846 f m).
Proof. exact (TRANS (@lem7225239 _96845 _96846 m n f) (@lem7225745 n _96845 _96846 f m)). Qed.
Lemma lem7225769 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term373 _96845 _96846 f m) = (term379 _96845 _96846 f m).
Proof. exact (@lem19158 (term368 f m) (term331 _96845 _96846) (term364 f m)). Qed.
Lemma lem7225772 : term374 = term374.
Proof. exact (eq_refl term374). Qed.
Lemma lem7225773 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term375 _96845 _96846 f m) = (term380 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225772) (@lem7225769 _96845 _96846 f m)). Qed.
Lemma lem7225780 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term380 _96845 _96846 f m) = (term381 _96845 _96846 f m).
Proof. exact (@lem19158 (term382 _96845 _96846 f m) term324 (term383 _96845 _96846 f m)). Qed.
Lemma lem7225781 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term375 _96845 _96846 f m) = (term381 _96845 _96846 f m).
Proof. exact (TRANS (@lem7225773 _96845 _96846 f m) (@lem7225780 _96845 _96846 f m)). Qed.
Lemma lem7225784 (_96846 : int) : (term376 _96846) = (term376 _96846).
Proof. exact (eq_refl (term376 _96846)). Qed.
Lemma lem7225785 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term377 _96845 _96846 f m) = (term384 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225784 _96846) (@lem7225781 _96845 _96846 f m)). Qed.
Lemma lem7225792 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term384 _96845 _96846 f m) = (term385 _96845 _96846 f m).
Proof. exact (@lem19158 (term386 _96845 _96846 f m) (term274 _96846) (term387 _96845 _96846 f m)). Qed.
Lemma lem7225793 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term377 _96845 _96846 f m) = (term385 _96845 _96846 f m).
Proof. exact (TRANS (@lem7225785 _96845 _96846 f m) (@lem7225792 _96845 _96846 f m)). Qed.
Lemma lem7225796 (_96845 : int) : (term376 _96845) = (term376 _96845).
Proof. exact (eq_refl (term376 _96845)). Qed.
Lemma lem7225797 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term378 _96845 _96846 f m) = (term388 _96845 _96846 f m).
Proof. exact (MK_COMB (@lem7225796 _96845) (@lem7225793 _96845 _96846 f m)). Qed.
Lemma lem7225804 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term388 _96845 _96846 f m) = (term389 _96845 _96846 f m).
Proof. exact (@lem19158 (term390 _96845 _96846 f m) (term274 _96845) (term391 _96845 _96846 f m)). Qed.
Lemma lem7225805 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term378 _96845 _96846 f m) = (term389 _96845 _96846 f m).
Proof. exact (TRANS (@lem7225797 _96845 _96846 f m) (@lem7225804 _96845 _96846 f m)). Qed.
Lemma lem7225806 (n : nat) (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) : (term246 _96845 _96846 m n f) = (term389 _96845 _96846 f m).
Proof. exact (TRANS (@lem7225752 n _96845 _96846 f m) (@lem7225805 _96845 _96846 f m)). Qed.
Lemma lem7225816 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term389 _96845 _96846 f m) : term389 _96845 _96846 f m.
Proof. exact (h1). Qed.
Lemma lem7225817 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term392 _96845 _96846 f m) : term392 _96845 _96846 f m.
Proof. exact (h1). Qed.
Lemma lem7225818 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term392 _96845 _96846 f m) : term390 _96845 _96846 f m.
Proof. exact (proj2 (@lem7225817 _96845 _96846 f m h1)). Qed.
Lemma lem7225820 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term392 _96845 _96846 f m) : term386 _96845 _96846 f m.
Proof. exact (proj2 (@lem7225818 _96845 _96846 f m h1)). Qed.
Lemma lem7225823 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term392 _96845 _96846 f m) : term324.
Proof. exact (proj1 (@lem7225820 _96845 _96846 f m h1)). Qed.
Lemma lem7225827 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7225828 : term324 = term393.
Proof. exact (@lem7225827 term220 term254). Qed.
Lemma lem7225830 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225831 : term254 = term255.
Proof. exact (@lem7225830 term166). Qed.
Lemma lem7225833 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225834 : term220 = term251.
Proof. exact (@lem7225833 (NUMERAL 0)). Qed.
Lemma lem7225835 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225836 : term222 = term394.
Proof. exact (MK_COMB (@lem7225835) (@lem7225834)). Qed.
Lemma lem7225837 : term393 = term395.
Proof. exact (MK_COMB (@lem7225836) (@lem7225831)). Qed.
Lemma lem7225838 : term396.
Proof. exact (@lem1980026 term220 term232 term254 term232). Qed.
Lemma lem7225840 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225841 : term302 = term303.
Proof. exact (@lem7225840 (NUMERAL 0) term166). Qed.
Lemma lem7225842 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225843 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225844 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225843 h1) (fun h1 : term303 = True => @lem7225842)). Qed.
Lemma lem7225845 : term303 = True.
Proof. exact (EQ_MP (@lem7225844) (@lem7225842)). Qed.
Lemma lem7225846 : term302 = True.
Proof. exact (TRANS (@lem7225841) (@lem7225845)). Qed.
Lemma lem7225847 : True = term302.
Proof. exact (SYM (@lem7225846)). Qed.
Lemma lem7225848 : term302.
Proof. exact (EQ_MP (@lem7225847) (@lem0)). Qed.
Lemma lem7225849 : term397.
Proof. exact (@lem7225838 (@lem7225848)). Qed.
Lemma lem7225851 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225852 : term302 = term303.
Proof. exact (@lem7225851 (NUMERAL 0) term166). Qed.
Lemma lem7225853 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225854 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225855 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225854 h1) (fun h1 : term303 = True => @lem7225853)). Qed.
Lemma lem7225856 : term303 = True.
Proof. exact (EQ_MP (@lem7225855) (@lem7225853)). Qed.
Lemma lem7225857 : term302 = True.
Proof. exact (TRANS (@lem7225852) (@lem7225856)). Qed.
Lemma lem7225858 : True = term302.
Proof. exact (SYM (@lem7225857)). Qed.
Lemma lem7225859 : term302.
Proof. exact (EQ_MP (@lem7225858) (@lem0)). Qed.
Lemma lem7225860 : term395 = term398.
Proof. exact (@lem7225849 (@lem7225859)). Qed.
Lemma lem7225862 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7225863 : term281 = term286.
Proof. exact (@lem7225862 term166 term166). Qed.
Lemma lem7225864 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225865 : term266 = term166.
Proof. exact (EQ_MP (@lem7225864) (@lem940073)). Qed.
Lemma lem7225866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225867 : term264 = term232.
Proof. exact (MK_COMB (@lem7225866) (@lem7225865)). Qed.
Lemma lem7225868 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225869 : term286 = term254.
Proof. exact (MK_COMB (@lem7225868) (@lem7225867)). Qed.
Lemma lem7225870 : term281 = term254.
Proof. exact (TRANS (@lem7225863) (@lem7225869)). Qed.
Lemma lem7225872 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225873 : term314 = term220.
Proof. exact (@lem7225872 term166). Qed.
Lemma lem7225874 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225875 : term399 = term222.
Proof. exact (MK_COMB (@lem7225874) (@lem7225873)). Qed.
Lemma lem7225876 : term398 = term393.
Proof. exact (MK_COMB (@lem7225875) (@lem7225870)). Qed.
Lemma lem7225878 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7225879 : term393 = term402.
Proof. exact (@lem7225878 (NUMERAL 0) term166). Qed.
Lemma lem7225880 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225881 (h1 : term304 = (BIT1 0)) : (term166 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7225882 : (term304 = (BIT1 0)) = ((term166 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225881 h1) (fun h1 : (term166 = (NUMERAL 0)) = False => @lem7225880)). Qed.
Lemma lem7225883 : (term166 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7225882) (@lem7225880)). Qed.
Lemma lem7225884 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7225885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225886 : term403 = (and True).
Proof. exact (MK_COMB (@lem7225885) (@lem7225884)). Qed.
Lemma lem7225887 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7225886) (@lem7225883)). Qed.
Lemma lem7225889 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7225890 : term402 = False.
Proof. exact (TRANS (@lem7225887) (@lem7225889)). Qed.
Lemma lem7225891 : term393 = False.
Proof. exact (TRANS (@lem7225879) (@lem7225890)). Qed.
Lemma lem7225892 : term398 = False.
Proof. exact (TRANS (@lem7225876) (@lem7225891)). Qed.
Lemma lem7225893 : term395 = False.
Proof. exact (TRANS (@lem7225860) (@lem7225892)). Qed.
Lemma lem7225894 : term393 = False.
Proof. exact (TRANS (@lem7225837) (@lem7225893)). Qed.
Lemma lem7225895 : term324 = False.
Proof. exact (TRANS (@lem7225828) (@lem7225894)). Qed.
Lemma lem7225896 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term392 _96845 _96846 f m) : False.
Proof. exact (EQ_MP (@lem7225895) (@lem7225823 _96845 _96846 f m h1)). Qed.
Lemma lem7225897 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term404 _96845 _96846 f m) : term404 _96845 _96846 f m.
Proof. exact (h1). Qed.
Lemma lem7225898 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term404 _96845 _96846 f m) : term391 _96845 _96846 f m.
Proof. exact (proj2 (@lem7225897 _96845 _96846 f m h1)). Qed.
Lemma lem7225900 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term404 _96845 _96846 f m) : term387 _96845 _96846 f m.
Proof. exact (proj2 (@lem7225898 _96845 _96846 f m h1)). Qed.
Lemma lem7225903 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term404 _96845 _96846 f m) : term324.
Proof. exact (proj1 (@lem7225900 _96845 _96846 f m h1)). Qed.
Lemma lem7225907 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7225908 : term324 = term393.
Proof. exact (@lem7225907 term220 term254). Qed.
Lemma lem7225910 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7225911 : term254 = term255.
Proof. exact (@lem7225910 term166). Qed.
Lemma lem7225913 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7225914 : term220 = term251.
Proof. exact (@lem7225913 (NUMERAL 0)). Qed.
Lemma lem7225915 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225916 : term222 = term394.
Proof. exact (MK_COMB (@lem7225915) (@lem7225914)). Qed.
Lemma lem7225917 : term393 = term395.
Proof. exact (MK_COMB (@lem7225916) (@lem7225911)). Qed.
Lemma lem7225918 : term396.
Proof. exact (@lem1980026 term220 term232 term254 term232). Qed.
Lemma lem7225920 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225921 : term302 = term303.
Proof. exact (@lem7225920 (NUMERAL 0) term166). Qed.
Lemma lem7225922 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225923 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225924 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225923 h1) (fun h1 : term303 = True => @lem7225922)). Qed.
Lemma lem7225925 : term303 = True.
Proof. exact (EQ_MP (@lem7225924) (@lem7225922)). Qed.
Lemma lem7225926 : term302 = True.
Proof. exact (TRANS (@lem7225921) (@lem7225925)). Qed.
Lemma lem7225927 : True = term302.
Proof. exact (SYM (@lem7225926)). Qed.
Lemma lem7225928 : term302.
Proof. exact (EQ_MP (@lem7225927) (@lem0)). Qed.
Lemma lem7225929 : term397.
Proof. exact (@lem7225918 (@lem7225928)). Qed.
Lemma lem7225931 (m : nat) (n : nat) : (term301 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7225932 : term302 = term303.
Proof. exact (@lem7225931 (NUMERAL 0) term166). Qed.
Lemma lem7225933 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225934 (h1 : term304 = (BIT1 0)) : term303 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7225935 : (term304 = (BIT1 0)) = (term303 = True).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225934 h1) (fun h1 : term303 = True => @lem7225933)). Qed.
Lemma lem7225936 : term303 = True.
Proof. exact (EQ_MP (@lem7225935) (@lem7225933)). Qed.
Lemma lem7225937 : term302 = True.
Proof. exact (TRANS (@lem7225932) (@lem7225936)). Qed.
Lemma lem7225938 : True = term302.
Proof. exact (SYM (@lem7225937)). Qed.
Lemma lem7225939 : term302.
Proof. exact (EQ_MP (@lem7225938) (@lem0)). Qed.
Lemma lem7225940 : term395 = term398.
Proof. exact (@lem7225929 (@lem7225939)). Qed.
Lemma lem7225942 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7225943 : term281 = term286.
Proof. exact (@lem7225942 term166 term166). Qed.
Lemma lem7225944 : (term265 = (BIT1 0)) = (term266 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7225945 : term266 = term166.
Proof. exact (EQ_MP (@lem7225944) (@lem940073)). Qed.
Lemma lem7225946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7225947 : term264 = term232.
Proof. exact (MK_COMB (@lem7225946) (@lem7225945)). Qed.
Lemma lem7225948 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7225949 : term286 = term254.
Proof. exact (MK_COMB (@lem7225948) (@lem7225947)). Qed.
Lemma lem7225950 : term281 = term254.
Proof. exact (TRANS (@lem7225943) (@lem7225949)). Qed.
Lemma lem7225952 (x : nat) : (term315 x) = term220.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7225953 : term314 = term220.
Proof. exact (@lem7225952 term166). Qed.
Lemma lem7225954 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7225955 : term399 = term222.
Proof. exact (MK_COMB (@lem7225954) (@lem7225953)). Qed.
Lemma lem7225956 : term398 = term393.
Proof. exact (MK_COMB (@lem7225955) (@lem7225950)). Qed.
Lemma lem7225958 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7225959 : term393 = term402.
Proof. exact (@lem7225958 (NUMERAL 0) term166). Qed.
Lemma lem7225960 : term304 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7225961 (h1 : term304 = (BIT1 0)) : (term166 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7225962 : (term304 = (BIT1 0)) = ((term166 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term304 = (BIT1 0) => @lem7225961 h1) (fun h1 : (term166 = (NUMERAL 0)) = False => @lem7225960)). Qed.
Lemma lem7225963 : (term166 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7225962) (@lem7225960)). Qed.
Lemma lem7225964 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7225965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7225966 : term403 = (and True).
Proof. exact (MK_COMB (@lem7225965) (@lem7225964)). Qed.
Lemma lem7225967 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7225966) (@lem7225963)). Qed.
Lemma lem7225969 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7225970 : term402 = False.
Proof. exact (TRANS (@lem7225967) (@lem7225969)). Qed.
Lemma lem7225971 : term393 = False.
Proof. exact (TRANS (@lem7225959) (@lem7225970)). Qed.
Lemma lem7225972 : term398 = False.
Proof. exact (TRANS (@lem7225956) (@lem7225971)). Qed.
Lemma lem7225973 : term395 = False.
Proof. exact (TRANS (@lem7225940) (@lem7225972)). Qed.
Lemma lem7225974 : term393 = False.
Proof. exact (TRANS (@lem7225917) (@lem7225973)). Qed.
Lemma lem7225975 : term324 = False.
Proof. exact (TRANS (@lem7225908) (@lem7225974)). Qed.
Lemma lem7225976 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term404 _96845 _96846 f m) : False.
Proof. exact (EQ_MP (@lem7225975) (@lem7225903 _96845 _96846 f m h1)). Qed.
Lemma lem7225977 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term389 _96845 _96846 f m) : False.
Proof. exact (or_elim (@lem7225816 _96845 _96846 f m h1) (fun h0 : term392 _96845 _96846 f m => @lem7225896 _96845 _96846 f m h0) (fun h0 : term404 _96845 _96846 f m => @lem7225976 _96845 _96846 f m h0)). Qed.
Lemma lem7225979 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term389 _96845 _96846 f m) : term389 _96845 _96846 f m.
Proof. exact (h1). Qed.
Lemma lem7225980 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term389 _96845 _96846 f m) : (term389 _96845 _96846 f m) = False.
Proof. exact (prop_ext (fun h2 : term389 _96845 _96846 f m => @lem7225977 _96845 _96846 f m h1) (fun h2 : False => @lem7225979 _96845 _96846 f m h1)). Qed.
Lemma lem7225981 (_96845 : int) (_96846 : int) (f : nat -> real) (m : nat) (h1 : term389 _96845 _96846 f m) : False.
Proof. exact (EQ_MP (@lem7225980 _96845 _96846 f m h1) (@lem7225979 _96845 _96846 f m h1)). Qed.
Lemma lem7225982 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) (h1 : term246 _96845 _96846 m n f) : term246 _96845 _96846 m n f.
Proof. exact (h1). Qed.
Lemma lem7225983 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) (h1 : term246 _96845 _96846 m n f) : term389 _96845 _96846 f m.
Proof. exact (EQ_MP (@lem7225806 n _96845 _96846 f m) (@lem7225982 _96845 _96846 m n f h1)). Qed.
Lemma lem7225984 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) (h1 : term246 _96845 _96846 m n f) : (term389 _96845 _96846 f m) = False.
Proof. exact (prop_ext (fun h2 : term389 _96845 _96846 f m => @lem7225981 _96845 _96846 f m h2) (fun h2 : False => @lem7225983 _96845 _96846 m n f h1)). Qed.
Lemma lem7225985 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) (h1 : term246 _96845 _96846 m n f) : False.
Proof. exact (EQ_MP (@lem7225984 _96845 _96846 m n f h1) (@lem7225983 _96845 _96846 m n f h1)). Qed.
Lemma lem7225986 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : term405 _96845 _96846 m n f.
Proof. exact (fun h0 : term246 _96845 _96846 m n f => @lem7225985 _96845 _96846 m n f h0). Qed.
Lemma lem7225987 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : term406 _96845 _96846 m n f.
Proof. exact (@lem1386578 (term407 _96845 _96846 m n f)). Qed.
Lemma lem7225990 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : term407 _96845 _96846 m n f.
Proof. exact (@lem7225987 _96845 _96846 m n f (@lem7225986 _96845 _96846 m n f)). Qed.
Lemma lem7225991 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term244 _96845 _96846 m n f) = (term213 _96845 _96846 m n f).
Proof. exact (SYM (@lem7225187 _96845 _96846 m n f)). Qed.
Lemma lem7225992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7225993 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : (term407 _96845 _96846 m n f) = (term186 _96845 _96846 m n f).
Proof. exact (MK_COMB (@lem7225992) (@lem7225991 _96845 _96846 m n f)). Qed.
Lemma lem7225994 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : term186 _96845 _96846 m n f.
Proof. exact (EQ_MP (@lem7225993 _96845 _96846 m n f) (@lem7225990 _96845 _96846 m n f)). Qed.
Lemma lem7225995 (_96845 : int) (_96846 : int) (m : nat) (n : nat) (f : nat -> real) : term187 _96845 _96846 m n f.
Proof. exact (EQ_MP (@lem7225054 _96845 _96846 m n f) (@lem7225994 _96845 _96846 m n f)). Qed.
Lemma lem7225996 (m : nat) (n : nat) (f : nat -> real) : term408 m n f.
Proof. exact (@lem7225995 (int_of_num m) (int_of_num n) m n f). Qed.
Lemma lem7225997 (m : nat) (n : nat) (f : nat -> real) : term409 m n f.
Proof. exact (@lem7225996 m n f (@lem7225050 m)). Qed.
Lemma lem7225998 (m : nat) (n : nat) (f : nat -> real) : term177 m n f.
Proof. exact (@lem7225997 m n f (@lem7225053 n)). Qed.
Lemma lem7225999 (m : nat) (f : nat -> real) : term179 m f.
Proof. exact (fun n : nat => @lem7225998 m n f). Qed.
Lemma lem7226000 (f : nat -> real) : term181 f.
Proof. exact (fun m : nat => @lem7225999 m f). Qed.
Lemma lem7226001 : term183.
Proof. exact (fun f : nat -> real => @lem7226000 f). Qed.
Lemma lem7226002 : term183 = term99.
Proof. exact (SYM (@lem7225047)). Qed.
Lemma lem7226003 : term99.
Proof. exact (EQ_MP (@lem7226002) (@lem7226001)). Qed.
Lemma lem7226004 : term99 = (term99 = True).
Proof. exact (@lem7 term99). Qed.
Lemma lem7226005 : term99 = True.
Proof. exact (EQ_MP (@lem7226004) (@lem7226003)). Qed.
Lemma lem7226006 : True = term99.
Proof. exact (SYM (@lem7226005)). Qed.
Lemma lem7226007 : term99.
Proof. exact (EQ_MP (@lem7226006) (@lem0)). Qed.
Lemma lem7226008 : term98.
Proof. exact (EQ_MP (@lem7224753) (@lem7226007)). Qed.
