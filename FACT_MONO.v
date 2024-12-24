Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FACT_MONO_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LE_0_spec.
Require Import LE_EXISTS_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_SUC_spec.
Require Import LE_TRANS_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm146107_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Lemma lem146289 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem146290 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem146291 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem146290 n) (@lem146289 n)). Qed.
Lemma lem146292 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem146294 (m : nat) : term2 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem146295 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem146296 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem146295 m) (@lem146294 m)). Qed.
Lemma lem146297 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem146296 m n). Qed.
Lemma lem146298 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem146300 (m : nat) : term6 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem146301 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem146302 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem146301 m) (@lem146300 m)). Qed.
Lemma lem146303 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem146302 m n). Qed.
Lemma lem146304 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem146305 (m : nat) (n : nat) : term9 m n.
Proof. exact (EQ_MP (@lem146304 m n) (@lem146303 m n)). Qed.
Lemma lem146306 (m : nat) (n : nat) (p : nat) : term10 m n p.
Proof. exact (@lem146305 m n p). Qed.
Lemma lem146307 (m : nat) (n : nat) (p : nat) : (term10 m n p) = ((term11 m n p) = (term12 m n p)).
Proof. exact (eq_refl (term10 m n p)). Qed.
Lemma lem146309 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem146311 : term14.
Proof. exact (proj2 (@lem146309)). Qed.
Lemma lem146314 : term15.
Proof. exact (proj1 (@lem146311)). Qed.
Lemma lem146320 (n : nat) (h1 : (term16 n) = n) : (term16 n) = n.
Proof. exact (h1). Qed.
Lemma lem146321 (n : nat) (h1 : (term16 n) = n) : n = (term16 n).
Proof. exact (SYM (@lem146320 n h1)). Qed.
Lemma lem146322 (n : nat) (h1 : n = (term16 n)) : n = (term16 n).
Proof. exact (h1). Qed.
Lemma lem146323 (n : nat) (h1 : n = (term16 n)) : (term16 n) = n.
Proof. exact (SYM (@lem146322 n h1)). Qed.
Lemma lem146324 (n : nat) : ((term16 n) = n) = (n = (term16 n)).
Proof. exact (prop_ext (fun h1 : (term16 n) = n => @lem146321 n h1) (fun h1 : n = (term16 n) => @lem146323 n h1)). Qed.
Lemma lem146325 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem146324 n)). Qed.
Lemma lem146326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146327 : term15 = term19.
Proof. exact (MK_COMB (@lem146326) (@lem146325)). Qed.
Lemma lem146328 : term19.
Proof. exact (EQ_MP (@lem146327) (@lem146314)). Qed.
Lemma lem146329 (n : nat) : term20 n.
Proof. exact (@lem146328 n). Qed.
Lemma lem146330 (n : nat) : (term20 n) = (n = (term16 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem146332 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem146333 (m : nat) (h1 : term21) : term22 m.
Proof. exact (@lem146332 h1 m). Qed.
Lemma lem146334 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem146335 (m : nat) (h1 : term21) : term23 m.
Proof. exact (EQ_MP (@lem146334 m) (@lem146333 m h1)). Qed.
Lemma lem146336 (m : nat) (n : nat) (h1 : term21) : term24 m n.
Proof. exact (@lem146335 m h1 n). Qed.
Lemma lem146337 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem146338 (n : nat) (m : nat) (h1 : term21) : term25 n m.
Proof. exact (EQ_MP (@lem146337 n m) (@lem146336 m n h1)). Qed.
Lemma lem146339 (n : nat) (m : nat) (p : nat) (h1 : term21) : term26 n m p.
Proof. exact (@lem146338 n m h1 p). Qed.
Lemma lem146340 (n : nat) (m : nat) (p : nat) : (term26 n m p) = (term27 n m p).
Proof. exact (eq_refl (term26 n m p)). Qed.
Lemma lem146341 (n : nat) (m : nat) (p : nat) (h1 : term21) : term27 n m p.
Proof. exact (EQ_MP (@lem146340 n m p) (@lem146339 n m p h1)). Qed.
Lemma lem146342 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term28 m n p.
Proof. exact (h1). Qed.
Lemma lem146343 (m : nat) (n : nat) (p : nat) (h1 : term21) (h2 : term28 m n p) : Peano.le m p.
Proof. exact (@lem146341 n m p h1 (@lem146342 m n p h2)). Qed.
Lemma lem146344 (m : nat) (n : nat) (p : nat) (h1 : term28 m n p) : term29 m p.
Proof. exact (fun h0 : term21 => @lem146343 m n p h0 h1). Qed.
Lemma lem146345 (m : nat) (p : nat) (h1 : term30 m p) : term30 m p.
Proof. exact (h1). Qed.
Lemma lem146346 (m : nat) (p : nat) (h1 : term30 m p) : term29 m p.
Proof. exact (ex_elim (@lem146345 m p h1) (fun n : nat => fun h0 : term31 m p n => @lem146344 m n p h0)). Qed.
Lemma lem146347 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem146348 (m : nat) (p : nat) (h1 : term21) (h2 : term30 m p) : Peano.le m p.
Proof. exact (@lem146346 m p h2 (@lem146347 h1)). Qed.
Lemma lem146349 (m : nat) (p : nat) (h1 : term21) : term32 m p.
Proof. exact (fun h0 : term30 m p => @lem146348 m p h1 h0). Qed.
Lemma lem146350 (m : nat) (h1 : term21) : term33 m.
Proof. exact (fun p : nat => @lem146349 m p h1). Qed.
Lemma lem146351 (h1 : term21) : term34.
Proof. exact (fun m : nat => @lem146350 m h1). Qed.
Lemma lem146352 : term35.
Proof. exact (fun h0 : term21 => @lem146351 h0). Qed.
Lemma lem146353 : term34.
Proof. exact (@lem146352 (@lem93743)). Qed.
Lemma lem146354 (m : nat) : term36 m.
Proof. exact (@lem146353 m). Qed.
Lemma lem146355 (m : nat) : (term36 m) = (term33 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem146356 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem146355 m) (@lem146354 m)). Qed.
Lemma lem146357 (m : nat) (p : nat) : term37 m p.
Proof. exact (@lem146356 m p). Qed.
Lemma lem146358 (m : nat) (p : nat) : (term37 m p) = (term32 m p).
Proof. exact (eq_refl (term37 m p)). Qed.
Lemma lem146360 : term38.
Proof. exact (proj2 (@lem146107)). Qed.
Lemma lem146361 (n : nat) : term39 n.
Proof. exact (@lem146360 n). Qed.
Lemma lem146362 (n : nat) : (term39 n) = ((term40 n) = (term41 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem146365 (n : nat) : term42 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem146366 (n : nat) : (term42 n) = (Peano.le n n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem146367 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem146366 n) (@lem146365 n)). Qed.
Lemma lem146368 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem146370 : term43.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem146371 : term44.
Proof. exact (proj2 (@lem146370)). Qed.
Lemma lem146372 : term45.
Proof. exact (proj2 (@lem146371)). Qed.
Lemma lem146373 (m : nat) : term46 m.
Proof. exact (@lem146372 m). Qed.
Lemma lem146374 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem146375 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem146374 m) (@lem146373 m)). Qed.
Lemma lem146376 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem146375 m n). Qed.
Lemma lem146377 (m : nat) (n : nat) : (term48 m n) = ((term49 m n) = (term50 m n)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem146386 : term51.
Proof. exact (proj1 (@lem146370)). Qed.
Lemma lem146387 (m : nat) : term52 m.
Proof. exact (@lem146386 m). Qed.
Lemma lem146388 (m : nat) : (term52 m) = ((term53 m) = m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem146394 (m : nat) : term54 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem146395 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem146396 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem146395 m) (@lem146394 m)). Qed.
Lemma lem146397 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem146396 m n). Qed.
Lemma lem146398 (n : nat) (m : nat) : (term56 m n) = ((Peano.le m n) = (term57 n m)).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem146400 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem146402 (n : nat) (m : nat) : (Peano.le m n) = (term57 n m).
Proof. exact (EQ_MP (@lem146398 n m) (@lem146397 m n)). Qed.
Lemma lem146409 (m : nat) (n : nat) (h1 : Peano.le m n) : term57 n m.
Proof. exact (EQ_MP (@lem146402 n m) (@lem146400 m n h1)). Qed.
Lemma lem146410 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem146411 (m : nat) : (term58 m) = (term58 m).
Proof. exact (eq_refl (term58 m)). Qed.
Lemma lem146412 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term59 m n) = (term60 m d).
Proof. exact (MK_COMB (@lem146411 m) (@lem146410 n m d h1)). Qed.
Lemma lem146413 (m : nat) (d : nat) : (term60 m d) = (term61 m d).
Proof. exact (eq_refl (term60 m d)). Qed.
Lemma lem146414 (m : nat) (n : nat) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem146415 (n : nat) (m : nat) (d : nat) : ((term59 m n) = (term60 m d)) = ((term59 m n) = (term61 m d)).
Proof. exact (MK_COMB (@lem146414 m n) (@lem146413 m d)). Qed.
Lemma lem146416 (m : nat) (n : nat) : (term59 m n) = (term63 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem146417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem146418 (m : nat) (n : nat) : (term62 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem146417) (@lem146416 m n)). Qed.
Lemma lem146419 (m : nat) (d : nat) : (term61 m d) = (term61 m d).
Proof. exact (eq_refl (term61 m d)). Qed.
Lemma lem146420 (n : nat) (m : nat) (d : nat) : ((term59 m n) = (term61 m d)) = ((term63 m n) = (term61 m d)).
Proof. exact (MK_COMB (@lem146418 m n) (@lem146419 m d)). Qed.
Lemma lem146421 (n : nat) (m : nat) (d : nat) : ((term59 m n) = (term60 m d)) = ((term63 m n) = (term61 m d)).
Proof. exact (TRANS (@lem146415 n m d) (@lem146420 n m d)). Qed.
Lemma lem146422 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term63 m n) = (term61 m d).
Proof. exact (EQ_MP (@lem146421 n m d) (@lem146412 n m d h1)). Qed.
Lemma lem146423 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term61 m d) = (term63 m n).
Proof. exact (SYM (@lem146422 n m d h1)). Qed.
Lemma lem146425 (P : nat -> Prop) : term65 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem146426 (m : nat) : term66 m.
Proof. exact (@lem146425 (term67 m)). Qed.
Lemma lem146427 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem146428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem146429 (m : nat) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem146428) (@lem146427 m)). Qed.
Lemma lem146430 (m : nat) (d : nat) : (term72 m d) = (term61 m d).
Proof. exact (eq_refl (term72 m d)). Qed.
Lemma lem146431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem146432 (m : nat) (d : nat) : (term73 m d) = (term74 m d).
Proof. exact (MK_COMB (@lem146431) (@lem146430 m d)). Qed.
Lemma lem146433 (m : nat) (d : nat) : (term75 m d) = (term76 m d).
Proof. exact (eq_refl (term75 m d)). Qed.
Lemma lem146434 (m : nat) (d : nat) : (term77 m d) = (term78 m d).
Proof. exact (MK_COMB (@lem146432 m d) (@lem146433 m d)). Qed.
Lemma lem146435 (m : nat) : (term79 m) = (term80 m).
Proof. exact (fun_ext (fun d : nat => @lem146434 m d)). Qed.
Lemma lem146436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146437 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem146436) (@lem146435 m)). Qed.
Lemma lem146438 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem146429 m) (@lem146437 m)). Qed.
Lemma lem146439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem146440 (m : nat) : (term85 m) = (term86 m).
Proof. exact (MK_COMB (@lem146439) (@lem146438 m)). Qed.
Lemma lem146441 (m : nat) (d : nat) : (term72 m d) = (term61 m d).
Proof. exact (eq_refl (term72 m d)). Qed.
Lemma lem146442 (m : nat) : (term87 m) = (term67 m).
Proof. exact (fun_ext (fun d : nat => @lem146441 m d)). Qed.
Lemma lem146443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146444 (m : nat) : (term88 m) = (term89 m).
Proof. exact (MK_COMB (@lem146443) (@lem146442 m)). Qed.
Lemma lem146445 (m : nat) : (term66 m) = (term90 m).
Proof. exact (MK_COMB (@lem146440 m) (@lem146444 m)). Qed.
Lemma lem146446 (m : nat) : term90 m.
Proof. exact (EQ_MP (@lem146445 m) (@lem146426 m)). Qed.
Lemma lem146447 (m : nat) (d : nat) (h1 : term61 m d) : term61 m d.
Proof. exact (h1). Qed.
Lemma lem146451 (m : nat) : (term53 m) = m.
Proof. exact (EQ_MP (@lem146388 m) (@lem146387 m)). Qed.
Lemma lem146452 : Factorial.fact = Factorial.fact.
Proof. exact (eq_refl Factorial.fact). Qed.
Lemma lem146453 (m : nat) : (term91 m) = (Factorial.fact m).
Proof. exact (MK_COMB (@lem146452) (@lem146451 m)). Qed.
Lemma lem146454 (m : nat) : (term92 m) = (term92 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem146455 (m : nat) : (term69 m) = (term93 m).
Proof. exact (MK_COMB (@lem146454 m) (@lem146453 m)). Qed.
Lemma lem146457 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem146368 n) (@lem146367 n)). Qed.
Lemma lem146458 (m : nat) : (term93 m) = True.
Proof. exact (@lem146457 (Factorial.fact m)). Qed.
Lemma lem146459 (m : nat) : (term69 m) = True.
Proof. exact (TRANS (@lem146455 m) (@lem146458 m)). Qed.
Lemma lem146460 (m : nat) : True = (term69 m).
Proof. exact (SYM (@lem146459 m)). Qed.
Lemma lem146461 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem146460 m) (@lem0)). Qed.
Lemma lem146465 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (EQ_MP (@lem146377 m n) (@lem146376 m n)). Qed.
Lemma lem146466 (m : nat) (d : nat) : (term49 m d) = (term50 m d).
Proof. exact (@lem146465 m d). Qed.
Lemma lem146467 : Factorial.fact = Factorial.fact.
Proof. exact (eq_refl Factorial.fact). Qed.
Lemma lem146468 (m : nat) (d : nat) : (term94 m d) = (term95 m d).
Proof. exact (MK_COMB (@lem146467) (@lem146466 m d)). Qed.
Lemma lem146469 (m : nat) : (term92 m) = (term92 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem146470 (m : nat) (d : nat) : (term76 m d) = (term96 m d).
Proof. exact (MK_COMB (@lem146469 m) (@lem146468 m d)). Qed.
Lemma lem146473 (m : nat) (d : nat) : (term96 m d) = (term76 m d).
Proof. exact (SYM (@lem146470 m d)). Qed.
Lemma lem146475 (n : nat) : (term40 n) = (term41 n).
Proof. exact (EQ_MP (@lem146362 n) (@lem146361 n)). Qed.
Lemma lem146476 (m : nat) (d : nat) : (term95 m d) = (term97 m d).
Proof. exact (@lem146475 (Nat.add m d)). Qed.
Lemma lem146477 (m : nat) : (term92 m) = (term92 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem146478 (m : nat) (d : nat) : (term96 m d) = (term98 m d).
Proof. exact (MK_COMB (@lem146477 m) (@lem146476 m d)). Qed.
Lemma lem146479 (m : nat) (d : nat) : (term98 m d) = (term96 m d).
Proof. exact (SYM (@lem146478 m d)). Qed.
Lemma lem146481 (m : nat) (p : nat) : term32 m p.
Proof. exact (EQ_MP (@lem146358 m p) (@lem146357 m p)). Qed.
Lemma lem146482 (m : nat) (d : nat) : term99 m d.
Proof. exact (@lem146481 (Factorial.fact m) (term97 m d)). Qed.
Lemma lem146483 (m : nat) (d : nat) : (term61 m d) = ((term61 m d) = True).
Proof. exact (@lem7 (term61 m d)). Qed.
Lemma lem146488 (m : nat) (d : nat) (h1 : term61 m d) : (term61 m d) = True.
Proof. exact (EQ_MP (@lem146483 m d) (@lem146447 m d h1)). Qed.
Lemma lem146489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem146490 (m : nat) (d : nat) (h1 : term61 m d) : (term100 m d) = (and True).
Proof. exact (MK_COMB (@lem146489) (@lem146488 m d h1)). Qed.
Lemma lem146491 (m : nat) (d : nat) : (term101 m d) = (term101 m d).
Proof. exact (eq_refl (term101 m d)). Qed.
Lemma lem146492 (m : nat) (d : nat) (h1 : term61 m d) : (term102 m d) = (term103 m d).
Proof. exact (MK_COMB (@lem146490 m d h1) (@lem146491 m d)). Qed.
Lemma lem146494 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem146495 (m : nat) (d : nat) : (term103 m d) = (term101 m d).
Proof. exact (@lem146494 (term101 m d)). Qed.
Lemma lem146496 (m : nat) (d : nat) (h1 : term61 m d) : (term102 m d) = (term101 m d).
Proof. exact (TRANS (@lem146492 m d h1) (@lem146495 m d)). Qed.
Lemma lem146497 (m : nat) (d : nat) (h1 : term61 m d) : (term101 m d) = (term102 m d).
Proof. exact (SYM (@lem146496 m d h1)). Qed.
Lemma lem146499 (n : nat) : n = (term16 n).
Proof. exact (EQ_MP (@lem146330 n) (@lem146329 n)). Qed.
Lemma lem146500 (m : nat) (d : nat) : (term104 m d) = (term105 m d).
Proof. exact (@lem146499 (term104 m d)). Qed.
Lemma lem146501 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem146502 (m : nat) (d : nat) : (term106 m d) = (term107 m d).
Proof. exact (MK_COMB (@lem146501) (@lem146500 m d)). Qed.
Lemma lem146503 (m : nat) (d : nat) : (term97 m d) = (term97 m d).
Proof. exact (eq_refl (term97 m d)). Qed.
Lemma lem146504 (m : nat) (d : nat) : (term101 m d) = (term108 m d).
Proof. exact (MK_COMB (@lem146502 m d) (@lem146503 m d)). Qed.
Lemma lem146505 (m : nat) (d : nat) : (term108 m d) = (term101 m d).
Proof. exact (SYM (@lem146504 m d)). Qed.
Lemma lem146507 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem146307 m n p) (@lem146306 m n p)). Qed.
Lemma lem146508 (m : nat) (d : nat) : (term108 m d) = (term109 m d).
Proof. exact (@lem146507 term110 (term50 m d) (term104 m d)). Qed.
Lemma lem146513 (m : nat) (d : nat) : (term109 m d) = (term108 m d).
Proof. exact (SYM (@lem146508 m d)). Qed.
Lemma lem146517 : term110 = term111.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem146518 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem146519 : term112 = term113.
Proof. exact (MK_COMB (@lem146518) (@lem146517)). Qed.
Lemma lem146520 (m : nat) (d : nat) : (term50 m d) = (term50 m d).
Proof. exact (eq_refl (term50 m d)). Qed.
Lemma lem146521 (m : nat) (d : nat) : (term114 m d) = (term115 m d).
Proof. exact (MK_COMB (@lem146519) (@lem146520 m d)). Qed.
Lemma lem146523 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem146298 m n) (@lem146297 m n)). Qed.
Lemma lem146524 (m : nat) (d : nat) : (term115 m d) = (term116 m d).
Proof. exact (@lem146523 (NUMERAL 0) (Nat.add m d)). Qed.
Lemma lem146526 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem146292 n) (@lem146291 n)). Qed.
Lemma lem146527 (m : nat) (d : nat) : (term116 m d) = True.
Proof. exact (@lem146526 (Nat.add m d)). Qed.
Lemma lem146528 (m : nat) (d : nat) : (term115 m d) = True.
Proof. exact (TRANS (@lem146524 m d) (@lem146527 m d)). Qed.
Lemma lem146529 (m : nat) (d : nat) : (term114 m d) = True.
Proof. exact (TRANS (@lem146521 m d) (@lem146528 m d)). Qed.
Lemma lem146530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem146531 (m : nat) (d : nat) : (term117 m d) = (or True).
Proof. exact (MK_COMB (@lem146530) (@lem146529 m d)). Qed.
Lemma lem146534 (m : nat) (d : nat) : ((term104 m d) = (NUMERAL 0)) = ((term104 m d) = (NUMERAL 0)).
Proof. exact (eq_refl ((term104 m d) = (NUMERAL 0))). Qed.
Lemma lem146535 (m : nat) (d : nat) : (term109 m d) = (term118 m d).
Proof. exact (MK_COMB (@lem146531 m d) (@lem146534 m d)). Qed.
Lemma lem146537 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem146538 (m : nat) (d : nat) : (term118 m d) = True.
Proof. exact (@lem146537 ((term104 m d) = (NUMERAL 0))). Qed.
Lemma lem146539 (m : nat) (d : nat) : (term109 m d) = True.
Proof. exact (TRANS (@lem146535 m d) (@lem146538 m d)). Qed.
Lemma lem146540 (m : nat) (d : nat) : True = (term109 m d).
Proof. exact (SYM (@lem146539 m d)). Qed.
Lemma lem146541 (m : nat) (d : nat) : term109 m d.
Proof. exact (EQ_MP (@lem146540 m d) (@lem0)). Qed.
Lemma lem146542 (m : nat) (d : nat) : term108 m d.
Proof. exact (EQ_MP (@lem146513 m d) (@lem146541 m d)). Qed.
Lemma lem146543 (m : nat) (d : nat) : term101 m d.
Proof. exact (EQ_MP (@lem146505 m d) (@lem146542 m d)). Qed.
Lemma lem146544 (m : nat) (d : nat) (h1 : term61 m d) : term102 m d.
Proof. exact (EQ_MP (@lem146497 m d h1) (@lem146543 m d)). Qed.
Lemma lem146545 (m : nat) (d : nat) (h1 : term61 m d) : term119 m d.
Proof. exact (ex_intro (term120 m d) (term104 m d) (@lem146544 m d h1)). Qed.
Lemma lem146546 (m : nat) (d : nat) (h1 : term61 m d) : term98 m d.
Proof. exact (@lem146482 m d (@lem146545 m d h1)). Qed.
Lemma lem146547 (m : nat) (d : nat) (h1 : term61 m d) : term96 m d.
Proof. exact (EQ_MP (@lem146479 m d) (@lem146546 m d h1)). Qed.
Lemma lem146548 (m : nat) (d : nat) (h1 : term61 m d) : term76 m d.
Proof. exact (EQ_MP (@lem146473 m d) (@lem146547 m d h1)). Qed.
Lemma lem146549 (m : nat) (d : nat) : term78 m d.
Proof. exact (fun h0 : term61 m d => @lem146548 m d h0). Qed.
Lemma lem146554 (m : nat) : term82 m.
Proof. exact (fun d : nat => @lem146549 m d). Qed.
Lemma lem146555 (m : nat) : term84 m.
Proof. exact (conj (@lem146461 m) (@lem146554 m)). Qed.
Lemma lem146556 (m : nat) : term89 m.
Proof. exact (@lem146446 m (@lem146555 m)). Qed.
Lemma lem146557 (m : nat) (d : nat) : term72 m d.
Proof. exact (@lem146556 m d). Qed.
Lemma lem146558 (m : nat) (d : nat) : (term72 m d) = (term61 m d).
Proof. exact (eq_refl (term72 m d)). Qed.
Lemma lem146559 (m : nat) (d : nat) : term61 m d.
Proof. exact (EQ_MP (@lem146558 m d) (@lem146557 m d)). Qed.
Lemma lem146560 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term63 m n.
Proof. exact (EQ_MP (@lem146423 n m d h1) (@lem146559 m d)). Qed.
Lemma lem146561 (m : nat) (n : nat) (h1 : Peano.le m n) : term63 m n.
Proof. exact (ex_elim (@lem146409 m n h1) (fun d : nat => fun h0 : term121 n m d => @lem146560 n m d h0)). Qed.
Lemma lem146562 (m : nat) (n : nat) : term122 m n.
Proof. exact (fun h0 : Peano.le m n => @lem146561 m n h0). Qed.
Lemma lem146567 (m : nat) : term123 m.
Proof. exact (fun n : nat => @lem146562 m n). Qed.
Lemma lem146572 : term124.
Proof. exact (fun m : nat => @lem146567 m). Qed.
