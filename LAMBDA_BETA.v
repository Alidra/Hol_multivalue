Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_BETA_term_abbrevs.
Require Import DIMINDEX_FINITE_IMAGE_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDEX_INJ_spec.
Require Import SELECT_UNIQUE_spec.
Require Import finite_index_spec.
Require Import lambda_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7614851_spec.
Require Import thm9425_spec.
Lemma lem7618354 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7618355 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7618356 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7618355 t1) (@lem7618354 t1)). Qed.
Lemma lem7618357 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7618356 t1 t2). Qed.
Lemma lem7618358 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7618359 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7618358 t1 t2) (@lem7618357 t1 t2)). Qed.
Lemma lem7618360 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7618359 t1 t2 t3). Qed.
Lemma lem7618361 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7618362 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7618361 t1 t2 t3) (@lem7618360 t1 t2 t3)). Qed.
Lemma lem7618363 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7618362 t1 t2 t3)). Qed.
Lemma lem7618364 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7618365 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term8 A P.
Proof. exact (@lem7618364 A h1 P). Qed.
Lemma lem7618366 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem7618367 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (EQ_MP (@lem7618366 A P) (@lem7618365 A P h1)). Qed.
Lemma lem7618368 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term10 A P x.
Proof. exact (@lem7618367 A P h1 x). Qed.
Lemma lem7618369 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem7618370 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (EQ_MP (@lem7618369 A P x) (@lem7618368 A P x h1)). Qed.
Lemma lem7618371 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term12 A P x.
Proof. exact (h1). Qed.
Lemma lem7618372 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem7618370 A P x h2 (@lem7618371 A P x h1)). Qed.
Lemma lem7618373 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term13 A P x.
Proof. exact (fun h0 : term7 A => @lem7618372 A P x h1 h0). Qed.
Lemma lem7618374 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7618375 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem7618373 A P x h1 (@lem7618374 A h2)). Qed.
Lemma lem7618376 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (fun h0 : term12 A P x => @lem7618375 A P x h0 h1). Qed.
Lemma lem7618377 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (fun x : A => @lem7618376 A P x h1). Qed.
Lemma lem7618378 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun P : A -> Prop => @lem7618377 A P h1). Qed.
Lemma lem7618379 {A : Type'} : term14 A.
Proof. exact (fun h0 : term7 A => @lem7618378 A h0). Qed.
Lemma lem7618380 {A : Type'} : term7 A.
Proof. exact (@lem7618379 A (@lem9522 A)). Qed.
Lemma lem7618381 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (@lem7618380 A P). Qed.
Lemma lem7618382 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem7618383 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (EQ_MP (@lem7618382 A P) (@lem7618381 A P)). Qed.
Lemma lem7618384 {A : Type'} (P : A -> Prop) (x : A) : term10 A P x.
Proof. exact (@lem7618383 A P x). Qed.
Lemma lem7618385 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem7618400 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7618401 {A B : Type'} (r : type35 A B) : (True = ((term15 A B r) = r)) = ((term15 A B r) = r).
Proof. exact (@lem7618400 ((term15 A B r) = r)). Qed.
Lemma lem7618404 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (fun_ext (fun r : type35 A B => @lem7618401 A B r)). Qed.
Lemma lem7618405 {A B : Type'} : (@all ((finite_image B) -> A)) = (@all ((finite_image B) -> A)).
Proof. exact (eq_refl (@all ((finite_image B) -> A))). Qed.
Lemma lem7618406 {A B : Type'} : (term18 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7618405 A B) (@lem7618404 A B)). Qed.
Lemma lem7618411 {A B : Type'} : (term20 A B) = (term20 A B).
Proof. exact (eq_refl (term20 A B)). Qed.
Lemma lem7618412 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem7618411 A B) (@lem7618406 A B)). Qed.
Lemma lem7618415 {A B : Type'} : term22 A B.
Proof. exact (EQ_MP (@lem7618412 A B) (@lem7614851 A B)). Qed.
Lemma lem7618416 {A B : Type'} : term19 A B.
Proof. exact (proj2 (@lem7618415 A B)). Qed.
Lemma lem7618417 {A B : Type'} (r : type35 A B) : term23 A B r.
Proof. exact (@lem7618416 A B r). Qed.
Lemma lem7618418 {A B : Type'} (r : type35 A B) : (term23 A B r) = ((term15 A B r) = r).
Proof. exact (eq_refl (term23 A B r)). Qed.
Lemma lem7618424 {_139760 _139770 : Type'} (x : cart _139760 _139770) : term24 _139760 _139770 x.
Proof. exact (@lem7616152 _139760 _139770 x). Qed.
Lemma lem7618425 {_139760 _139770 : Type'} (x : cart _139760 _139770) : (term24 _139760 _139770 x) = (term25 _139760 _139770 x).
Proof. exact (eq_refl (term24 _139760 _139770 x)). Qed.
Lemma lem7618426 {_139760 _139770 : Type'} (x : cart _139760 _139770) : term25 _139760 _139770 x.
Proof. exact (EQ_MP (@lem7618425 _139760 _139770 x) (@lem7618424 _139760 _139770 x)). Qed.
Lemma lem7618427 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : term26 _139760 _139770 x i.
Proof. exact (@lem7618426 _139760 _139770 x i). Qed.
Lemma lem7618428 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : (term26 _139760 _139770 x i) = ((@dollar _139760 _139770 x i) = (term27 _139760 _139770 x i)).
Proof. exact (eq_refl (term26 _139760 _139770 x i)). Qed.
Lemma lem7618430 {A B : Type'} (g : nat -> A) : term28 A B g.
Proof. exact (@lem7618353 A B g). Qed.
Lemma lem7618431 {A B : Type'} (g : nat -> A) : (term28 A B g) = ((@lambda A B g) = (term29 A B g)).
Proof. exact (eq_refl (term28 A B g)). Qed.
Lemma lem7618444 {A B : Type'} (g : nat -> A) : (@lambda A B g) = (term29 A B g).
Proof. exact (EQ_MP (@lem7618431 A B g) (@lem7618430 A B g)). Qed.
Lemma lem7618445 {A B : Type'} (g : nat -> A) : (@lambda A B g) = (term29 A B g).
Proof. exact (@lem7618444 A B g). Qed.
Lemma lem7618456 {A B : Type'} : (@dollar A B) = (@dollar A B).
Proof. exact (eq_refl (@dollar A B)). Qed.
Lemma lem7618457 {A B : Type'} (g : nat -> A) : (term30 A B g) = (term31 A B g).
Proof. exact (MK_COMB (@lem7618456 A B) (@lem7618445 A B g)). Qed.
Lemma lem7618458 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7618459 {A B : Type'} (g : nat -> A) (i : nat) : (term32 A B g i) = (term33 A B g i).
Proof. exact (MK_COMB (@lem7618457 A B g) (@lem7618458 i)). Qed.
Lemma lem7618460 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7618461 {A B : Type'} (g : nat -> A) (i : nat) : (term34 A B g i) = (term35 A B g i).
Proof. exact (MK_COMB (@lem7618460 A) (@lem7618459 A B g i)). Qed.
Lemma lem7618462 {A : Type'} (g : nat -> A) (i : nat) : (g i) = (g i).
Proof. exact (eq_refl (g i)). Qed.
Lemma lem7618463 {A B : Type'} (g : nat -> A) (i : nat) : ((term32 A B g i) = (g i)) = ((term33 A B g i) = (g i)).
Proof. exact (MK_COMB (@lem7618461 A B g i) (@lem7618462 A g i)). Qed.
Lemma lem7618466 {B : Type'} (i : nat) : (term36 B i) = (term36 B i).
Proof. exact (eq_refl (term36 B i)). Qed.
Lemma lem7618467 {A B : Type'} (g : nat -> A) (i : nat) : (term37 A B g i) = (term38 A B g i).
Proof. exact (MK_COMB (@lem7618466 B i) (@lem7618463 A B g i)). Qed.
Lemma lem7618470 {A B : Type'} (g : nat -> A) : (term39 A B g) = (term40 A B g).
Proof. exact (fun_ext (fun i : nat => @lem7618467 A B g i)). Qed.
Lemma lem7618471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618472 {A B : Type'} (g : nat -> A) : (term41 A B g) = (term42 A B g).
Proof. exact (MK_COMB (@lem7618471) (@lem7618470 A B g)). Qed.
Lemma lem7618477 {A B : Type'} (g : nat -> A) : (term42 A B g) = (term41 A B g).
Proof. exact (SYM (@lem7618472 A B g)). Qed.
Lemma lem7618478 {A B : Type'} (P : type24 A B) : (term43 A B P) = (ex P).
Proof. exact (@lem9425 (cart A B) P). Qed.
Lemma lem7618479 {A B : Type'} (g : nat -> A) : (term44 A B g) = (term45 A B g).
Proof. exact (@lem7618478 A B (term46 A B g)). Qed.
Lemma lem7618480 {A B : Type'} (g : nat -> A) : (term44 A B g) = (term42 A B g).
Proof. exact (eq_refl (term44 A B g)). Qed.
Lemma lem7618481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7618482 {A B : Type'} (g : nat -> A) : (term47 A B g) = (term48 A B g).
Proof. exact (MK_COMB (@lem7618481) (@lem7618480 A B g)). Qed.
Lemma lem7618483 {A B : Type'} (g : nat -> A) : (term45 A B g) = (term45 A B g).
Proof. exact (eq_refl (term45 A B g)). Qed.
Lemma lem7618484 {A B : Type'} (g : nat -> A) : ((term44 A B g) = (term45 A B g)) = ((term42 A B g) = (term45 A B g)).
Proof. exact (MK_COMB (@lem7618482 A B g) (@lem7618483 A B g)). Qed.
Lemma lem7618485 {A B : Type'} (g : nat -> A) : (term42 A B g) = (term45 A B g).
Proof. exact (EQ_MP (@lem7618484 A B g) (@lem7618479 A B g)). Qed.
Lemma lem7618486 {A B : Type'} (g : nat -> A) : (term45 A B g) = (term42 A B g).
Proof. exact (SYM (@lem7618485 A B g)). Qed.
Lemma lem7618498 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : (@dollar _139760 _139770 x i) = (term27 _139760 _139770 x i).
Proof. exact (EQ_MP (@lem7618428 _139760 _139770 x i) (@lem7618427 _139760 _139770 x i)). Qed.
Lemma lem7618499 {A B : Type'} (x : cart A B) (i : nat) : (@dollar A B x i) = (term27 A B x i).
Proof. exact (@lem7618498 A B x i). Qed.
Lemma lem7618500 {A B : Type'} (g : nat -> A) (i : nat) : (term49 A B g i) = (term50 A B g i).
Proof. exact (@lem7618499 A B (term51 A B g) i). Qed.
Lemma lem7618502 {A B : Type'} (r : type35 A B) : (term15 A B r) = r.
Proof. exact (EQ_MP (@lem7618418 A B r) (@lem7618417 A B r)). Qed.
Lemma lem7618503 {A B : Type'} (r : type35 A B) : (term15 A B r) = r.
Proof. exact (@lem7618502 A B r). Qed.
Lemma lem7618504 {A B : Type'} (g : nat -> A) : (term52 A B g) = (term53 A B g).
Proof. exact (@lem7618503 A B (term53 A B g)). Qed.
Lemma lem7618511 {B : Type'} (i : nat) : (@finite_index B i) = (@finite_index B i).
Proof. exact (eq_refl (@finite_index B i)). Qed.
Lemma lem7618512 {A B : Type'} (g : nat -> A) (i : nat) : (term50 A B g i) = (term54 A B g i).
Proof. exact (MK_COMB (@lem7618504 A B g) (@lem7618511 B i)). Qed.
Lemma lem7618514 {A B : Type'} (f : A -> B) (y : A) : (term55 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7618515 {A B : Type'} (f : type35 A B) (y : finite_image B) : (term56 A B f y) = (f y).
Proof. exact (@lem7618514 (finite_image B) A f y). Qed.
Lemma lem7618516 {A B : Type'} (g : nat -> A) (i : nat) : (term57 A B g i) = (term54 A B g i).
Proof. exact (@lem7618515 A B (term53 A B g) (@finite_index B i)). Qed.
Lemma lem7618517 {A B : Type'} (g : nat -> A) (k : finite_image B) : (term58 A B g k) = (term59 A B g k).
Proof. exact (eq_refl (term58 A B g k)). Qed.
Lemma lem7618518 {A B : Type'} (g : nat -> A) : (term60 A B g) = (term53 A B g).
Proof. exact (fun_ext (fun k : finite_image B => @lem7618517 A B g k)). Qed.
Lemma lem7618519 {B : Type'} (i : nat) : (@finite_index B i) = (@finite_index B i).
Proof. exact (eq_refl (@finite_index B i)). Qed.
Lemma lem7618520 {A B : Type'} (g : nat -> A) (i : nat) : (term57 A B g i) = (term54 A B g i).
Proof. exact (MK_COMB (@lem7618518 A B g) (@lem7618519 B i)). Qed.
Lemma lem7618521 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7618522 {A B : Type'} (g : nat -> A) (i : nat) : (term61 A B g i) = (term62 A B g i).
Proof. exact (MK_COMB (@lem7618521 A) (@lem7618520 A B g i)). Qed.
Lemma lem7618523 {A B : Type'} (g : nat -> A) (i : nat) : (term54 A B g i) = (term63 A B g i).
Proof. exact (eq_refl (term54 A B g i)). Qed.
Lemma lem7618524 {A B : Type'} (g : nat -> A) (i : nat) : ((term57 A B g i) = (term54 A B g i)) = ((term54 A B g i) = (term63 A B g i)).
Proof. exact (MK_COMB (@lem7618522 A B g i) (@lem7618523 A B g i)). Qed.
Lemma lem7618525 {A B : Type'} (g : nat -> A) (i : nat) : (term54 A B g i) = (term63 A B g i).
Proof. exact (EQ_MP (@lem7618524 A B g i) (@lem7618516 A B g i)). Qed.
Lemma lem7618532 {A B : Type'} (g : nat -> A) (i : nat) : (term50 A B g i) = (term63 A B g i).
Proof. exact (TRANS (@lem7618512 A B g i) (@lem7618525 A B g i)). Qed.
Lemma lem7618533 {A B : Type'} (g : nat -> A) (i : nat) : (term49 A B g i) = (term63 A B g i).
Proof. exact (TRANS (@lem7618500 A B g i) (@lem7618532 A B g i)). Qed.
Lemma lem7618534 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7618535 {A B : Type'} (g : nat -> A) (i : nat) : (term64 A B g i) = (term65 A B g i).
Proof. exact (MK_COMB (@lem7618534 A) (@lem7618533 A B g i)). Qed.
Lemma lem7618536 {A : Type'} (g : nat -> A) (i : nat) : (g i) = (g i).
Proof. exact (eq_refl (g i)). Qed.
Lemma lem7618537 {A B : Type'} (g : nat -> A) (i : nat) : ((term49 A B g i) = (g i)) = ((term63 A B g i) = (g i)).
Proof. exact (MK_COMB (@lem7618535 A B g i) (@lem7618536 A g i)). Qed.
Lemma lem7618540 {B : Type'} (i : nat) : (term36 B i) = (term36 B i).
Proof. exact (eq_refl (term36 B i)). Qed.
Lemma lem7618541 {A B : Type'} (g : nat -> A) (i : nat) : (term66 A B g i) = (term67 A B g i).
Proof. exact (MK_COMB (@lem7618540 B i) (@lem7618537 A B g i)). Qed.
Lemma lem7618544 {A B : Type'} (g : nat -> A) : (term68 A B g) = (term69 A B g).
Proof. exact (fun_ext (fun i : nat => @lem7618541 A B g i)). Qed.
Lemma lem7618545 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618546 {A B : Type'} (g : nat -> A) : (term70 A B g) = (term71 A B g).
Proof. exact (MK_COMB (@lem7618545) (@lem7618544 A B g)). Qed.
Lemma lem7618551 {A B : Type'} (g : nat -> A) : (term71 A B g) = (term70 A B g).
Proof. exact (SYM (@lem7618546 A B g)). Qed.
Lemma lem7618552 {B : Type'} (i : nat) (h1 : term72 B i) : term72 B i.
Proof. exact (h1). Qed.
Lemma lem7618553 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7618554 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7618555 {A : Type'} (g : nat -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7618557 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (EQ_MP (@lem7618385 A P x) (@lem7618384 A P x)). Qed.
Lemma lem7618558 (P : nat -> Prop) (x : nat) : term75 P x.
Proof. exact (@lem7618557 nat P x). Qed.
Lemma lem7618559 {B : Type'} (i : nat) : term76 B i.
Proof. exact (@lem7618558 (term77 B i) i). Qed.
Lemma lem7618563 {A B : Type'} (f : A -> B) (y : A) : (term55 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7618564 (f : nat -> Prop) (y : nat) : (term78 f y) = (f y).
Proof. exact (@lem7618563 nat Prop f y). Qed.
Lemma lem7618565 {B : Type'} (i : nat) (y : nat) : (term79 B i y) = (term80 B i y).
Proof. exact (@lem7618564 (term77 B i) y). Qed.
Lemma lem7618566 {B : Type'} (i' : nat) (i : nat) : (term80 B i i') = (term81 B i' i).
Proof. exact (eq_refl (term80 B i i')). Qed.
Lemma lem7618567 {B : Type'} (i : nat) : (term82 B i) = (term77 B i).
Proof. exact (fun_ext (fun i' : nat => @lem7618566 B i' i)). Qed.
Lemma lem7618568 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7618569 {B : Type'} (i : nat) (y : nat) : (term79 B i y) = (term80 B i y).
Proof. exact (MK_COMB (@lem7618567 B i) (@lem7618568 y)). Qed.
Lemma lem7618570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7618571 {B : Type'} (i : nat) (y : nat) : (term83 B i y) = (term84 B i y).
Proof. exact (MK_COMB (@lem7618570) (@lem7618569 B i y)). Qed.
Lemma lem7618572 {B : Type'} (y : nat) (i : nat) : (term80 B i y) = (term81 B y i).
Proof. exact (eq_refl (term80 B i y)). Qed.
Lemma lem7618573 {B : Type'} (y : nat) (i : nat) : ((term79 B i y) = (term80 B i y)) = ((term80 B i y) = (term81 B y i)).
Proof. exact (MK_COMB (@lem7618571 B i y) (@lem7618572 B y i)). Qed.
Lemma lem7618574 {B : Type'} (y : nat) (i : nat) : (term80 B i y) = (term81 B y i).
Proof. exact (EQ_MP (@lem7618573 B y i) (@lem7618565 B i y)). Qed.
Lemma lem7618581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7618582 {B : Type'} (y : nat) (i : nat) : (term84 B i y) = (term85 B y i).
Proof. exact (MK_COMB (@lem7618581) (@lem7618574 B y i)). Qed.
Lemma lem7618585 (y : nat) (i : nat) : (y = i) = (y = i).
Proof. exact (eq_refl (y = i)). Qed.
Lemma lem7618586 {B : Type'} (y : nat) (i : nat) : ((term80 B i y) = (y = i)) = ((term81 B y i) = (y = i)).
Proof. exact (MK_COMB (@lem7618582 B y i) (@lem7618585 y i)). Qed.
Lemma lem7618589 {B : Type'} (y : nat) (i : nat) : ((term81 B y i) = (y = i)) = ((term80 B i y) = (y = i)).
Proof. exact (SYM (@lem7618586 B y i)). Qed.
Lemma lem7618591 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7618592 {B : Type'} (y : nat) (i : nat) : ((term81 B y i) = (y = i)) = (term87 B y i).
Proof. exact (@lem7618591 ((term81 B y i) = (y = i))). Qed.
Lemma lem7618593 {B : Type'} (y : nat) (i : nat) : (term87 B y i) = ((term81 B y i) = (y = i)).
Proof. exact (SYM (@lem7618592 B y i)). Qed.
Lemma lem7618594 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) : term88 B y i.
Proof. exact (h1). Qed.
Lemma lem7618595 {B : Type'} : term89 B.
Proof. exact (@lem7612100 B). Qed.
Lemma lem7618599 {B : Type'} : term90 B.
Proof. exact (@lem7608063 B). Qed.
Lemma lem7618603 {A B : Type'} (y : nat) (i : nat) (h1 : term91 A B y i) : term91 A B y i.
Proof. exact (h1). Qed.
Lemma lem7618604 {A B : Type'} (y : nat) (i : nat) : term92 A B y i.
Proof. exact (fun h0 : term91 A B y i => @lem7618603 A B y i h0). Qed.
Lemma lem7618605 {A B : Type'} (y : nat) (i : nat) (h1 : term92 A B y i) : term92 A B y i.
Proof. exact (h1). Qed.
Lemma lem7618606 {A B : Type'} (y : nat) (i : nat) (h1 : term91 A B y i) : term91 A B y i.
Proof. exact (h1). Qed.
Lemma lem7618607 {A B : Type'} (y : nat) (i : nat) (h1 : term91 A B y i) (h2 : term92 A B y i) : term91 A B y i.
Proof. exact (@lem7618605 A B y i h2 (@lem7618606 A B y i h1)). Qed.
Lemma lem7618608 {A B : Type'} (y : nat) (i : nat) (h1 : term91 A B y i) : term93 A B y i.
Proof. exact (fun h0 : term92 A B y i => @lem7618607 A B y i h1 h0). Qed.
Lemma lem7618609 {A B : Type'} (y : nat) (i : nat) (h1 : term92 A B y i) : term92 A B y i.
Proof. exact (h1). Qed.
Lemma lem7618610 {A B : Type'} (y : nat) (i : nat) (h1 : term91 A B y i) (h2 : term92 A B y i) : term91 A B y i.
Proof. exact (@lem7618608 A B y i h1 (@lem7618609 A B y i h2)). Qed.
Lemma lem7618611 {A B : Type'} (y : nat) (i : nat) (h1 : term92 A B y i) : term92 A B y i.
Proof. exact (fun h0 : term91 A B y i => @lem7618610 A B y i h0 h1). Qed.
Lemma lem7618612 {A B : Type'} (y : nat) (i : nat) : term94 A B y i.
Proof. exact (fun h0 : term92 A B y i => @lem7618611 A B y i h0). Qed.
Lemma lem7618615 {A B : Type'} (y : nat) (i : nat) : term92 A B y i.
Proof. exact (@lem7618612 A B y i (@lem7618604 A B y i)). Qed.
Lemma lem7618616 {A B : Type'} (y : nat) (i : nat) : term92 A B y i.
Proof. exact (@lem7618615 A B y i). Qed.
Lemma lem7618674 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7618675 {B : Type'} : (term95 B) = (term96 B).
Proof. exact (@lem7618674 (term89 B)). Qed.
Lemma lem7618692 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (eq_refl (term97 A)). Qed.
Lemma lem7618693 {A B : Type'} : (term98 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem7618692 A) (@lem7618675 B)). Qed.
Lemma lem7618696 {B : Type'} : (term100 B) = (term100 B).
Proof. exact (eq_refl (term100 B)). Qed.
Lemma lem7618697 {A B : Type'} : (term101 A B) = (term102 A B).
Proof. exact (MK_COMB (@lem7618696 B) (@lem7618693 A B)). Qed.
Lemma lem7618700 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (eq_refl (term100 A)). Qed.
Lemma lem7618701 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (MK_COMB (@lem7618700 A) (@lem7618697 A B)). Qed.
Lemma lem7618704 {B : Type'} (y : nat) (i : nat) : (term105 B y i) = (term105 B y i).
Proof. exact (eq_refl (term105 B y i)). Qed.
Lemma lem7618705 {A B : Type'} (y : nat) (i : nat) : (term106 A B y i) = (term107 A B y i).
Proof. exact (MK_COMB (@lem7618704 B y i) (@lem7618701 A B)). Qed.
Lemma lem7618708 {B : Type'} (i : nat) : (term108 B i) = (term108 B i).
Proof. exact (eq_refl (term108 B i)). Qed.
Lemma lem7618709 {A B : Type'} (y : nat) (i : nat) : (term109 A B y i) = (term110 A B y i).
Proof. exact (MK_COMB (@lem7618708 B i) (@lem7618705 A B y i)). Qed.
Lemma lem7618712 (i : nat) : (term111 i) = (term111 i).
Proof. exact (eq_refl (term111 i)). Qed.
Lemma lem7618713 {A B : Type'} (y : nat) (i : nat) : (term91 A B y i) = (term112 A B y i).
Proof. exact (MK_COMB (@lem7618712 i) (@lem7618709 A B y i)). Qed.
Lemma lem7618716 {A B : Type'} (i : nat) : (term113 A B i) = (term114 A B i).
Proof. exact (fun_ext (fun y : nat => @lem7618713 A B y i)). Qed.
Lemma lem7618717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618718 {A B : Type'} (i : nat) : (term115 A B i) = (term116 A B i).
Proof. exact (MK_COMB (@lem7618717) (@lem7618716 A B i)). Qed.
Lemma lem7618723 {A B : Type'} : (term117 A B) = (term118 A B).
Proof. exact (fun_ext (fun i : nat => @lem7618718 A B i)). Qed.
Lemma lem7618724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618733 {A B : Type'} : (term119 A B) = (term120 A B).
Proof. exact (MK_COMB (@lem7618724) (@lem7618723 A B)). Qed.
Lemma lem7618754 {B : Type'} (i : nat) (j : nat) : (term121 B i j) = (term121 B i j).
Proof. exact (eq_refl (term121 B i j)). Qed.
Lemma lem7618755 {B : Type'} (i : nat) : (term122 B i) = (term122 B i).
Proof. exact (fun_ext (fun j : nat => @lem7618754 B i j)). Qed.
Lemma lem7618756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618757 {B : Type'} (i : nat) : (term123 B i) = (term123 B i).
Proof. exact (MK_COMB (@lem7618756) (@lem7618755 B i)). Qed.
Lemma lem7618758 {B : Type'} : (term124 B) = (term124 B).
Proof. exact (fun_ext (fun i : nat => @lem7618757 B i)). Qed.
Lemma lem7618759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618760 {B : Type'} : (term89 B) = (term89 B).
Proof. exact (MK_COMB (@lem7618759) (@lem7618758 B)). Qed.
Lemma lem7618761 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7618762 {B : Type'} : (term96 B) = (term96 B).
Proof. exact (MK_COMB (@lem7618761) (@lem7618760 B)). Qed.
Lemma lem7618783 {A : Type'} (i : nat) (j : nat) : (term121 A i j) = (term121 A i j).
Proof. exact (eq_refl (term121 A i j)). Qed.
Lemma lem7618784 {A : Type'} (i : nat) : (term122 A i) = (term122 A i).
Proof. exact (fun_ext (fun j : nat => @lem7618783 A i j)). Qed.
Lemma lem7618785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618786 {A : Type'} (i : nat) : (term123 A i) = (term123 A i).
Proof. exact (MK_COMB (@lem7618785) (@lem7618784 A i)). Qed.
Lemma lem7618787 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (fun_ext (fun i : nat => @lem7618786 A i)). Qed.
Lemma lem7618788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618789 {A : Type'} : (term89 A) = (term89 A).
Proof. exact (MK_COMB (@lem7618788) (@lem7618787 A)). Qed.
Lemma lem7618790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7618791 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem7618790) (@lem7618789 A)). Qed.
Lemma lem7618792 {A B : Type'} : (term99 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem7618791 A) (@lem7618762 B)). Qed.
Lemma lem7618793 {B : Type'} (s : type33 B) (t : B -> Prop) : ((@dimindex (finite_image B) s) = (@dimindex B t)) = ((@dimindex (finite_image B) s) = (@dimindex B t)).
Proof. exact (eq_refl ((@dimindex (finite_image B) s) = (@dimindex B t))). Qed.
Lemma lem7618794 {B : Type'} (s : type33 B) : (term125 B s) = (term125 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7618793 B s t)). Qed.
Lemma lem7618795 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7618796 {B : Type'} (s : type33 B) : (term126 B s) = (term126 B s).
Proof. exact (MK_COMB (@lem7618795 B) (@lem7618794 B s)). Qed.
Lemma lem7618797 {B : Type'} : (term127 B) = (term127 B).
Proof. exact (fun_ext (fun s : type33 B => @lem7618796 B s)). Qed.
Lemma lem7618798 {B : Type'} : (@all ((finite_image B) -> Prop)) = (@all ((finite_image B) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image B) -> Prop))). Qed.
Lemma lem7618799 {B : Type'} : (term90 B) = (term90 B).
Proof. exact (MK_COMB (@lem7618798 B) (@lem7618797 B)). Qed.
Lemma lem7618800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7618801 {B : Type'} : (term100 B) = (term100 B).
Proof. exact (MK_COMB (@lem7618800) (@lem7618799 B)). Qed.
Lemma lem7618802 {A B : Type'} : (term102 A B) = (term102 A B).
Proof. exact (MK_COMB (@lem7618801 B) (@lem7618792 A B)). Qed.
Lemma lem7618803 {A : Type'} (s : type33 A) (t : A -> Prop) : ((@dimindex (finite_image A) s) = (@dimindex A t)) = ((@dimindex (finite_image A) s) = (@dimindex A t)).
Proof. exact (eq_refl ((@dimindex (finite_image A) s) = (@dimindex A t))). Qed.
Lemma lem7618804 {A : Type'} (s : type33 A) : (term125 A s) = (term125 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7618803 A s t)). Qed.
Lemma lem7618805 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7618806 {A : Type'} (s : type33 A) : (term126 A s) = (term126 A s).
Proof. exact (MK_COMB (@lem7618805 A) (@lem7618804 A s)). Qed.
Lemma lem7618807 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun s : type33 A => @lem7618806 A s)). Qed.
Lemma lem7618808 {A : Type'} : (@all ((finite_image A) -> Prop)) = (@all ((finite_image A) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image A) -> Prop))). Qed.
Lemma lem7618809 {A : Type'} : (term90 A) = (term90 A).
Proof. exact (MK_COMB (@lem7618808 A) (@lem7618807 A)). Qed.
Lemma lem7618810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7618811 {A : Type'} : (term100 A) = (term100 A).
Proof. exact (MK_COMB (@lem7618810) (@lem7618809 A)). Qed.
Lemma lem7618812 {A B : Type'} : (term104 A B) = (term104 A B).
Proof. exact (MK_COMB (@lem7618811 A) (@lem7618802 A B)). Qed.
Lemma lem7618829 {B : Type'} (y : nat) (i : nat) : (term105 B y i) = (term105 B y i).
Proof. exact (eq_refl (term105 B y i)). Qed.
Lemma lem7618830 {A B : Type'} (y : nat) (i : nat) : (term107 A B y i) = (term107 A B y i).
Proof. exact (MK_COMB (@lem7618829 B y i) (@lem7618812 A B)). Qed.
Lemma lem7618833 {B : Type'} (i : nat) : (term108 B i) = (term108 B i).
Proof. exact (eq_refl (term108 B i)). Qed.
Lemma lem7618834 {A B : Type'} (y : nat) (i : nat) : (term110 A B y i) = (term110 A B y i).
Proof. exact (MK_COMB (@lem7618833 B i) (@lem7618830 A B y i)). Qed.
Lemma lem7618837 (i : nat) : (term111 i) = (term111 i).
Proof. exact (eq_refl (term111 i)). Qed.
Lemma lem7618838 {A B : Type'} (y : nat) (i : nat) : (term112 A B y i) = (term112 A B y i).
Proof. exact (MK_COMB (@lem7618837 i) (@lem7618834 A B y i)). Qed.
Lemma lem7618839 {A B : Type'} (i : nat) : (term114 A B i) = (term114 A B i).
Proof. exact (fun_ext (fun y : nat => @lem7618838 A B y i)). Qed.
Lemma lem7618840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618841 {A B : Type'} (i : nat) : (term116 A B i) = (term116 A B i).
Proof. exact (MK_COMB (@lem7618840) (@lem7618839 A B i)). Qed.
Lemma lem7618842 {A B : Type'} : (term118 A B) = (term118 A B).
Proof. exact (fun_ext (fun i : nat => @lem7618841 A B i)). Qed.
Lemma lem7618843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7618844 {A B : Type'} : (term120 A B) = (term120 A B).
Proof. exact (MK_COMB (@lem7618843) (@lem7618842 A B)). Qed.
Lemma lem7618939 {A B : Type'} : (term119 A B) = (term120 A B).
Proof. exact (TRANS (@lem7618733 A B) (@lem7618844 A B)). Qed.
Lemma lem7618940 {A B : Type'} : (term120 A B) = (term119 A B).
Proof. exact (SYM (@lem7618939 A B)). Qed.
Lemma lem7618943 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) : term88 B y i.
Proof. exact (h1). Qed.
Lemma lem7618947 {B : Type'} (h1 : term89 B) : term89 B.
Proof. exact (h1). Qed.
Lemma lem7618953 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7618959 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7618970 {B : Type'} (y : nat) (i : nat) : (term128 B y i) = (term129 B y i).
Proof. exact (@lem17045 (term73 B y) ((@finite_index B y) = (@finite_index B i))). Qed.
Lemma lem7618975 (y : nat) : (term130 y) = (term130 y).
Proof. exact (eq_refl (term130 y)). Qed.
Lemma lem7618976 {B : Type'} (y : nat) (i : nat) : (term131 B y i) = (term132 B y i).
Proof. exact (MK_COMB (@lem7618975 y) (@lem7618970 B y i)). Qed.
Lemma lem7618977 {B : Type'} (y : nat) (i : nat) : (term133 B y i) = (term131 B y i).
Proof. exact (@lem17045 (term74 y) (term134 B y i)). Qed.
Lemma lem7618978 {B : Type'} (y : nat) (i : nat) : (term133 B y i) = (term132 B y i).
Proof. exact (TRANS (@lem7618977 B y i) (@lem7618976 B y i)). Qed.
Lemma lem7618983 (y : nat) (i : nat) : (y = i) = (y = i).
Proof. exact (eq_refl (y = i)). Qed.
Lemma lem7618984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7618985 {B : Type'} (y : nat) (i : nat) : (term135 B y i) = (term136 B y i).
Proof. exact (MK_COMB (@lem7618984) (@lem7618978 B y i)). Qed.
Lemma lem7618986 {B : Type'} (y : nat) (i : nat) : (term137 B y i) = (term138 B y i).
Proof. exact (MK_COMB (@lem7618985 B y i) (@lem7618983 y i)). Qed.
Lemma lem7618991 {B : Type'} (y : nat) (i : nat) : (term139 B y i) = (term139 B y i).
Proof. exact (eq_refl (term139 B y i)). Qed.
Lemma lem7618992 {B : Type'} (y : nat) (i : nat) : (term140 B y i) = (term141 B y i).
Proof. exact (MK_COMB (@lem7618991 B y i) (@lem7618986 B y i)). Qed.
Lemma lem7618993 {B : Type'} (y : nat) (i : nat) : (term88 B y i) = (term140 B y i).
Proof. exact (@lem17646 (term81 B y i) (y = i)). Qed.
Lemma lem7618998 {B : Type'} (y : nat) (i : nat) : (term88 B y i) = (term141 B y i).
Proof. exact (TRANS (@lem7618993 B y i) (@lem7618992 B y i)). Qed.
Lemma lem7619150 {B : Type'} (j : nat) : (term142 B j) = (term143 B j).
Proof. exact (@lem17045 (term74 j) (term73 B j)). Qed.
Lemma lem7619152 {B : Type'} (i : nat) : (term144 B i) = (term144 B i).
Proof. exact (eq_refl (term144 B i)). Qed.
Lemma lem7619153 {B : Type'} (i : nat) (j : nat) : (term145 B i j) = (term146 B i j).
Proof. exact (MK_COMB (@lem7619152 B i) (@lem7619150 B j)). Qed.
Lemma lem7619154 {B : Type'} (i : nat) (j : nat) : (term147 B i j) = (term145 B i j).
Proof. exact (@lem17045 (term73 B i) (term72 B j)). Qed.
Lemma lem7619155 {B : Type'} (i : nat) (j : nat) : (term147 B i j) = (term146 B i j).
Proof. exact (TRANS (@lem7619154 B i j) (@lem7619153 B i j)). Qed.
Lemma lem7619157 (i : nat) : (term130 i) = (term130 i).
Proof. exact (eq_refl (term130 i)). Qed.
Lemma lem7619158 {B : Type'} (i : nat) (j : nat) : (term148 B i j) = (term149 B i j).
Proof. exact (MK_COMB (@lem7619157 i) (@lem7619155 B i j)). Qed.
Lemma lem7619159 {B : Type'} (i : nat) (j : nat) : (term150 B i j) = (term148 B i j).
Proof. exact (@lem17045 (term74 i) (term151 B i j)). Qed.
Lemma lem7619160 {B : Type'} (i : nat) (j : nat) : (term150 B i j) = (term149 B i j).
Proof. exact (TRANS (@lem7619159 B i j) (@lem7619158 B i j)). Qed.
Lemma lem7619175 {B : Type'} (i : nat) (j : nat) : (((@finite_index B i) = (@finite_index B j)) = (i = j)) = (term152 B i j).
Proof. exact (@lem17784 ((@finite_index B i) = (@finite_index B j)) (i = j)). Qed.
Lemma lem7619176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7619177 {B : Type'} (i : nat) (j : nat) : (term153 B i j) = (term154 B i j).
Proof. exact (MK_COMB (@lem7619176) (@lem7619160 B i j)). Qed.
Lemma lem7619178 {B : Type'} (i : nat) (j : nat) : (term155 B i j) = (term156 B i j).
Proof. exact (MK_COMB (@lem7619177 B i j) (@lem7619175 B i j)). Qed.
Lemma lem7619179 {B : Type'} (i : nat) (j : nat) : (term121 B i j) = (term155 B i j).
Proof. exact (@lem17265 (term157 B i j) (((@finite_index B i) = (@finite_index B j)) = (i = j))). Qed.
Lemma lem7619180 {B : Type'} (i : nat) (j : nat) : (term121 B i j) = (term156 B i j).
Proof. exact (TRANS (@lem7619179 B i j) (@lem7619178 B i j)). Qed.
Lemma lem7619181 {B : Type'} (i : nat) : (term122 B i) = (term158 B i).
Proof. exact (fun_ext (fun j : nat => @lem7619180 B i j)). Qed.
Lemma lem7619182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619183 {B : Type'} (i : nat) : (term123 B i) = (term159 B i).
Proof. exact (MK_COMB (@lem7619182) (@lem7619181 B i)). Qed.
Lemma lem7619184 {B : Type'} : (term124 B) = (term160 B).
Proof. exact (fun_ext (fun i : nat => @lem7619183 B i)). Qed.
Lemma lem7619185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619242 {B : Type'} : (term89 B) = (term161 B).
Proof. exact (MK_COMB (@lem7619185) (@lem7619184 B)). Qed.
Lemma lem7619243 {B : Type'} (h1 : term89 B) : term161 B.
Proof. exact (EQ_MP (@lem7619242 B) (@lem7618947 B h1)). Qed.
Lemma lem7619253 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7619261 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7619351 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) : term141 B y i.
Proof. exact (EQ_MP (@lem7618998 B y i) (@lem7618943 B y i h1)). Qed.
Lemma lem7619576 {B : Type'} (i : nat) (j : nat) : (term156 B i j) = (term156 B i j).
Proof. exact (eq_refl (term156 B i j)). Qed.
Lemma lem7619577 {B : Type'} (i : nat) : (term158 B i) = (term158 B i).
Proof. exact (fun_ext (fun j : nat => @lem7619576 B i j)). Qed.
Lemma lem7619578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619579 {B : Type'} (i : nat) : (term159 B i) = (term159 B i).
Proof. exact (MK_COMB (@lem7619578) (@lem7619577 B i)). Qed.
Lemma lem7619580 {B : Type'} : (term160 B) = (term160 B).
Proof. exact (fun_ext (fun i : nat => @lem7619579 B i)). Qed.
Lemma lem7619581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619582 {B : Type'} : (term161 B) = (term161 B).
Proof. exact (MK_COMB (@lem7619581) (@lem7619580 B)). Qed.
Lemma lem7619583 {B : Type'} (h1 : term89 B) : term161 B.
Proof. exact (EQ_MP (@lem7619582 B) (@lem7619243 B h1)). Qed.
Lemma lem7619584 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term162 B y i.
Proof. exact (h1). Qed.
Lemma lem7619585 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : term138 B y i.
Proof. exact (h1). Qed.
Lemma lem7619587 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term81 B y i.
Proof. exact (proj1 (@lem7619584 B y i h1)). Qed.
Lemma lem7619588 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term134 B y i.
Proof. exact (proj2 (@lem7619587 B y i h1)). Qed.
Lemma lem7619593 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : term132 B y i.
Proof. exact (proj1 (@lem7619585 B y i h1)). Qed.
Lemma lem7619595 {B : Type'} (y : nat) (i : nat) (h1 : term129 B y i) : term129 B y i.
Proof. exact (h1). Qed.
Lemma lem7619601 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7619605 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7619729 {B : Type'} (i : nat) (j : nat) : (term156 B i j) = (term163 B i j).
Proof. exact (@lem19490 (term164 B i j) (term149 B i j) (term165 B i j)). Qed.
Lemma lem7619730 {B : Type'} (i : nat) : (term158 B i) = (term166 B i).
Proof. exact (fun_ext (fun j : nat => @lem7619729 B i j)). Qed.
Lemma lem7619731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619732 {B : Type'} (i : nat) : (term159 B i) = (term167 B i).
Proof. exact (MK_COMB (@lem7619731) (@lem7619730 B i)). Qed.
Lemma lem7619733 {B : Type'} : (term160 B) = (term168 B).
Proof. exact (fun_ext (fun i : nat => @lem7619732 B i)). Qed.
Lemma lem7619734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7619736 {B : Type'} : (term161 B) = (term169 B).
Proof. exact (MK_COMB (@lem7619734) (@lem7619733 B)). Qed.
Lemma lem7619737 {B : Type'} (h1 : term89 B) : term169 B.
Proof. exact (EQ_MP (@lem7619736 B) (@lem7619583 B h1)). Qed.
Lemma lem7619757 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7619901 (y : nat) (h1 : term170 y) : term170 y.
Proof. exact (h1). Qed.
Lemma lem7619909 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7620049 {B : Type'} (y : nat) (h1 : term171 B y) : term171 B y.
Proof. exact (h1). Qed.
Lemma lem7620197 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) : term172 B y i.
Proof. exact (h1). Qed.
Lemma lem7620216 {B : Type'} (_98076 : nat) (h1 : term89 B) : term173 B _98076.
Proof. exact (@lem7619737 B h1 _98076). Qed.
Lemma lem7620217 {B : Type'} (_98076 : nat) : (term173 B _98076) = (term167 B _98076).
Proof. exact (eq_refl (term173 B _98076)). Qed.
Lemma lem7620218 {B : Type'} (_98076 : nat) (h1 : term89 B) : term167 B _98076.
Proof. exact (EQ_MP (@lem7620217 B _98076) (@lem7620216 B _98076 h1)). Qed.
Lemma lem7620219 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term174 B _98076 _98077.
Proof. exact (@lem7620218 B _98076 h1 _98077). Qed.
Lemma lem7620220 {B : Type'} (_98076 : nat) (_98077 : nat) : (term174 B _98076 _98077) = (term163 B _98076 _98077).
Proof. exact (eq_refl (term174 B _98076 _98077)). Qed.
Lemma lem7620221 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term163 B _98076 _98077.
Proof. exact (EQ_MP (@lem7620220 B _98076 _98077) (@lem7620219 B _98076 _98077 h1)). Qed.
Lemma lem7620294 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term175 B _98076 _98077.
Proof. exact (proj2 (@lem7620221 B _98076 _98077 h1)). Qed.
Lemma lem7620311 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7620313 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7620319 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term176 y i.
Proof. exact (proj2 (@lem7619584 B y i h1)). Qed.
Lemma lem7620361 {B : Type'} (_98076 : nat) (_98077 : nat) : (term175 B _98076 _98077) = (term177 B _98076 _98077).
Proof. exact (@lem7618363 (term170 _98076) (term146 B _98076 _98077) (term165 B _98076 _98077)). Qed.
Lemma lem7620362 {B : Type'} (_98076 : nat) (_98077 : nat) : (term178 B _98076 _98077) = (term179 B _98076 _98077).
Proof. exact (@lem7618363 (term171 B _98076) (term143 B _98077) (term165 B _98076 _98077)). Qed.
Lemma lem7620369 {B : Type'} (_98076 : nat) (_98077 : nat) : (term180 B _98076 _98077) = (term181 B _98076 _98077).
Proof. exact (@lem7618363 (term170 _98077) (term171 B _98077) (term165 B _98076 _98077)). Qed.
Lemma lem7620370 {B : Type'} (_98076 : nat) : (term144 B _98076) = (term144 B _98076).
Proof. exact (eq_refl (term144 B _98076)). Qed.
Lemma lem7620373 {B : Type'} (_98076 : nat) (_98077 : nat) : (term179 B _98076 _98077) = (term182 B _98076 _98077).
Proof. exact (MK_COMB (@lem7620370 B _98076) (@lem7620369 B _98076 _98077)). Qed.
Lemma lem7620374 {B : Type'} (_98076 : nat) (_98077 : nat) : (term178 B _98076 _98077) = (term182 B _98076 _98077).
Proof. exact (TRANS (@lem7620362 B _98076 _98077) (@lem7620373 B _98076 _98077)). Qed.
Lemma lem7620375 (_98076 : nat) : (term130 _98076) = (term130 _98076).
Proof. exact (eq_refl (term130 _98076)). Qed.
Lemma lem7620378 {B : Type'} (_98076 : nat) (_98077 : nat) : (term177 B _98076 _98077) = (term183 B _98076 _98077).
Proof. exact (MK_COMB (@lem7620375 _98076) (@lem7620374 B _98076 _98077)). Qed.
Lemma lem7620380 {B : Type'} (_98076 : nat) (_98077 : nat) : (term175 B _98076 _98077) = (term183 B _98076 _98077).
Proof. exact (TRANS (@lem7620361 B _98076 _98077) (@lem7620378 B _98076 _98077)). Qed.
Lemma lem7620381 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term183 B _98076 _98077.
Proof. exact (EQ_MP (@lem7620380 B _98076 _98077) (@lem7620294 B _98076 _98077 h1)). Qed.
Lemma lem7620439 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7620447 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : y = i.
Proof. exact (proj2 (@lem7619585 B y i h1)). Qed.
Lemma lem7620449 (y : nat) (h1 : term170 y) : term170 y.
Proof. exact (h1). Qed.
Lemma lem7620565 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7620571 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : y = i.
Proof. exact (proj2 (@lem7619585 B y i h1)). Qed.
Lemma lem7620573 {B : Type'} (y : nat) (h1 : term171 B y) : term171 B y.
Proof. exact (h1). Qed.
Lemma lem7620695 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : y = i.
Proof. exact (proj2 (@lem7619585 B y i h1)). Qed.
Lemma lem7620697 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) : term172 B y i.
Proof. exact (h1). Qed.
Lemma lem7620837 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7620880 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem7620881 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term185 y) = (term185 i).
Proof. exact (MK_COMB (@lem7620880) (@lem7620447 B y i h1)). Qed.
Lemma lem7620882 (i : nat) : (term185 i) = (term170 i).
Proof. exact (eq_refl (term185 i)). Qed.
Lemma lem7620883 (y : nat) : (term186 y) = (term186 y).
Proof. exact (eq_refl (term186 y)). Qed.
Lemma lem7620884 (y : nat) (i : nat) : ((term185 y) = (term185 i)) = ((term185 y) = (term170 i)).
Proof. exact (MK_COMB (@lem7620883 y) (@lem7620882 i)). Qed.
Lemma lem7620885 (y : nat) : (term185 y) = (term170 y).
Proof. exact (eq_refl (term185 y)). Qed.
Lemma lem7620886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7620887 (y : nat) : (term186 y) = (term187 y).
Proof. exact (MK_COMB (@lem7620886) (@lem7620885 y)). Qed.
Lemma lem7620888 (i : nat) : (term170 i) = (term170 i).
Proof. exact (eq_refl (term170 i)). Qed.
Lemma lem7620889 (y : nat) (i : nat) : ((term185 y) = (term170 i)) = ((term170 y) = (term170 i)).
Proof. exact (MK_COMB (@lem7620887 y) (@lem7620888 i)). Qed.
Lemma lem7620890 (y : nat) (i : nat) : ((term185 y) = (term185 i)) = ((term170 y) = (term170 i)).
Proof. exact (TRANS (@lem7620884 y i) (@lem7620889 y i)). Qed.
Lemma lem7620891 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term170 y) = (term170 i).
Proof. exact (EQ_MP (@lem7620890 y i) (@lem7620881 B y i h1)). Qed.
Lemma lem7620892 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) : term170 i.
Proof. exact (EQ_MP (@lem7620891 B y i h2) (@lem7620449 y h1)). Qed.
Lemma lem7620990 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7621019 {B : Type'} : (term188 B) = (term188 B).
Proof. exact (eq_refl (term188 B)). Qed.
Lemma lem7621020 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term189 B y) = (term189 B i).
Proof. exact (MK_COMB (@lem7621019 B) (@lem7620571 B y i h1)). Qed.
Lemma lem7621021 {B : Type'} (i : nat) : (term189 B i) = (term171 B i).
Proof. exact (eq_refl (term189 B i)). Qed.
Lemma lem7621022 {B : Type'} (y : nat) : (term190 B y) = (term190 B y).
Proof. exact (eq_refl (term190 B y)). Qed.
Lemma lem7621023 {B : Type'} (y : nat) (i : nat) : ((term189 B y) = (term189 B i)) = ((term189 B y) = (term171 B i)).
Proof. exact (MK_COMB (@lem7621022 B y) (@lem7621021 B i)). Qed.
Lemma lem7621024 {B : Type'} (y : nat) : (term189 B y) = (term171 B y).
Proof. exact (eq_refl (term189 B y)). Qed.
Lemma lem7621025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7621026 {B : Type'} (y : nat) : (term190 B y) = (term191 B y).
Proof. exact (MK_COMB (@lem7621025) (@lem7621024 B y)). Qed.
Lemma lem7621027 {B : Type'} (i : nat) : (term171 B i) = (term171 B i).
Proof. exact (eq_refl (term171 B i)). Qed.
Lemma lem7621028 {B : Type'} (y : nat) (i : nat) : ((term189 B y) = (term171 B i)) = ((term171 B y) = (term171 B i)).
Proof. exact (MK_COMB (@lem7621026 B y) (@lem7621027 B i)). Qed.
Lemma lem7621029 {B : Type'} (y : nat) (i : nat) : ((term189 B y) = (term189 B i)) = ((term171 B y) = (term171 B i)).
Proof. exact (TRANS (@lem7621023 B y i) (@lem7621028 B y i)). Qed.
Lemma lem7621030 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term171 B y) = (term171 B i).
Proof. exact (EQ_MP (@lem7621029 B y i) (@lem7621020 B y i h1)). Qed.
Lemma lem7621031 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) : term171 B i.
Proof. exact (EQ_MP (@lem7621030 B y i h2) (@lem7620573 B y h1)). Qed.
Lemma lem7621158 {B : Type'} (i : nat) : (term192 B i) = (term192 B i).
Proof. exact (eq_refl (term192 B i)). Qed.
Lemma lem7621159 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term193 B i y) = (term194 B i).
Proof. exact (MK_COMB (@lem7621158 B i) (@lem7620695 B y i h1)). Qed.
Lemma lem7621160 {B : Type'} (i : nat) : (term194 B i) = (term195 B i).
Proof. exact (eq_refl (term194 B i)). Qed.
Lemma lem7621161 {B : Type'} (i : nat) (y : nat) : (term196 B i y) = (term196 B i y).
Proof. exact (eq_refl (term196 B i y)). Qed.
Lemma lem7621162 {B : Type'} (y : nat) (i : nat) : ((term193 B i y) = (term194 B i)) = ((term193 B i y) = (term195 B i)).
Proof. exact (MK_COMB (@lem7621161 B i y) (@lem7621160 B i)). Qed.
Lemma lem7621163 {B : Type'} (y : nat) (i : nat) : (term193 B i y) = (term172 B y i).
Proof. exact (eq_refl (term193 B i y)). Qed.
Lemma lem7621164 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7621165 {B : Type'} (y : nat) (i : nat) : (term196 B i y) = (term197 B y i).
Proof. exact (MK_COMB (@lem7621164) (@lem7621163 B y i)). Qed.
Lemma lem7621166 {B : Type'} (i : nat) : (term195 B i) = (term195 B i).
Proof. exact (eq_refl (term195 B i)). Qed.
Lemma lem7621167 {B : Type'} (y : nat) (i : nat) : ((term193 B i y) = (term195 B i)) = ((term172 B y i) = (term195 B i)).
Proof. exact (MK_COMB (@lem7621165 B y i) (@lem7621166 B i)). Qed.
Lemma lem7621168 {B : Type'} (y : nat) (i : nat) : ((term193 B i y) = (term194 B i)) = ((term172 B y i) = (term195 B i)).
Proof. exact (TRANS (@lem7621162 B y i) (@lem7621167 B y i)). Qed.
Lemma lem7621169 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) : (term172 B y i) = (term195 B i).
Proof. exact (EQ_MP (@lem7621168 B y i) (@lem7621159 B y i h1)). Qed.
Lemma lem7621170 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : term195 B i.
Proof. exact (EQ_MP (@lem7621169 B y i h2) (@lem7620697 B y i h1)). Qed.
Lemma lem7621325 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term74 y.
Proof. exact (proj1 (@lem7619587 B y i h1)). Qed.
Lemma lem7621326 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term198 y.
Proof. exact (fun h0 : term170 y => @lem7621325 B y i h1). Qed.
Lemma lem7621328 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621329 (y : nat) : (term198 y) = (term74 y).
Proof. exact (@lem7621328 (term74 y)). Qed.
Lemma lem7621330 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term74 y.
Proof. exact (EQ_MP (@lem7621329 y) (@lem7621326 B y i h1)). Qed.
Lemma lem7621332 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term73 B y.
Proof. exact (proj1 (@lem7619588 B y i h1)). Qed.
Lemma lem7621333 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term200 B y.
Proof. exact (fun h0 : term171 B y => @lem7621332 B y i h1). Qed.
Lemma lem7621335 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621336 {B : Type'} (y : nat) : (term200 B y) = (term73 B y).
Proof. exact (@lem7621335 (term73 B y)). Qed.
Lemma lem7621337 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term73 B y.
Proof. exact (EQ_MP (@lem7621336 B y) (@lem7621333 B y i h1)). Qed.
Lemma lem7621339 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7621340 (i : nat) (h1 : term74 i) : term198 i.
Proof. exact (fun h0 : term170 i => @lem7621339 i h1). Qed.
Lemma lem7621342 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621343 (i : nat) : (term198 i) = (term74 i).
Proof. exact (@lem7621342 (term74 i)). Qed.
Lemma lem7621344 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (EQ_MP (@lem7621343 i) (@lem7621340 i h1)). Qed.
Lemma lem7621346 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7621347 {B : Type'} (i : nat) (h1 : term73 B i) : term200 B i.
Proof. exact (fun h0 : term171 B i => @lem7621346 B i h1). Qed.
Lemma lem7621349 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621350 {B : Type'} (i : nat) : (term200 B i) = (term73 B i).
Proof. exact (@lem7621349 (term73 B i)). Qed.
Lemma lem7621351 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (EQ_MP (@lem7621350 B i) (@lem7621347 B i h1)). Qed.
Lemma lem7621353 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : (@finite_index B y) = (@finite_index B i).
Proof. exact (proj2 (@lem7619588 B y i h1)). Qed.
Lemma lem7621354 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term201 B y i.
Proof. exact (fun h0 : term172 B y i => @lem7621353 B y i h1). Qed.
Lemma lem7621356 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621357 {B : Type'} (y : nat) (i : nat) : (term201 B y i) = ((@finite_index B y) = (@finite_index B i)).
Proof. exact (@lem7621356 ((@finite_index B y) = (@finite_index B i))). Qed.
Lemma lem7621358 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : (@finite_index B y) = (@finite_index B i).
Proof. exact (EQ_MP (@lem7621357 B y i) (@lem7621354 B y i h1)). Qed.
Lemma lem7621364 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621365 {B : Type'} (_98076 : nat) (_98077 : nat) : (term183 B _98076 _98077) = (term202 B _98076 _98077).
Proof. exact (@lem7621364 (term171 B _98076) (term170 _98076) (term181 B _98076 _98077)). Qed.
Lemma lem7621389 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621390 {B : Type'} (_98076 : nat) (_98077 : nat) : (term181 B _98076 _98077) = (term203 B _98076 _98077).
Proof. exact (@lem7621389 (term171 B _98077) (term170 _98077) (term165 B _98076 _98077)). Qed.
Lemma lem7621414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7621415 {B : Type'} (_98076 : nat) (_98077 : nat) : (term165 B _98076 _98077) = (term204 B _98076 _98077).
Proof. exact (@lem7621414 (_98076 = _98077) (term172 B _98076 _98077)). Qed.
Lemma lem7621425 (_98077 : nat) : (term130 _98077) = (term130 _98077).
Proof. exact (eq_refl (term130 _98077)). Qed.
Lemma lem7621426 {B : Type'} (_98076 : nat) (_98077 : nat) : (term205 B _98076 _98077) = (term206 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621425 _98077) (@lem7621415 B _98076 _98077)). Qed.
Lemma lem7621430 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621431 {B : Type'} (_98076 : nat) (_98077 : nat) : (term206 B _98076 _98077) = (term207 B _98076 _98077).
Proof. exact (@lem7621430 (_98076 = _98077) (term170 _98077) (term172 B _98076 _98077)). Qed.
Lemma lem7621451 {B : Type'} (_98076 : nat) (_98077 : nat) : (term205 B _98076 _98077) = (term207 B _98076 _98077).
Proof. exact (TRANS (@lem7621426 B _98076 _98077) (@lem7621431 B _98076 _98077)). Qed.
Lemma lem7621452 {B : Type'} (_98077 : nat) : (term144 B _98077) = (term144 B _98077).
Proof. exact (eq_refl (term144 B _98077)). Qed.
Lemma lem7621453 {B : Type'} (_98076 : nat) (_98077 : nat) : (term203 B _98076 _98077) = (term208 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621452 B _98077) (@lem7621451 B _98076 _98077)). Qed.
Lemma lem7621457 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621458 {B : Type'} (_98076 : nat) (_98077 : nat) : (term208 B _98076 _98077) = (term209 B _98076 _98077).
Proof. exact (@lem7621457 (_98076 = _98077) (term171 B _98077) (term210 B _98076 _98077)). Qed.
Lemma lem7621488 {B : Type'} (_98076 : nat) (_98077 : nat) : (term203 B _98076 _98077) = (term209 B _98076 _98077).
Proof. exact (TRANS (@lem7621453 B _98076 _98077) (@lem7621458 B _98076 _98077)). Qed.
Lemma lem7621489 {B : Type'} (_98076 : nat) (_98077 : nat) : (term181 B _98076 _98077) = (term209 B _98076 _98077).
Proof. exact (TRANS (@lem7621390 B _98076 _98077) (@lem7621488 B _98076 _98077)). Qed.
Lemma lem7621490 (_98076 : nat) : (term130 _98076) = (term130 _98076).
Proof. exact (eq_refl (term130 _98076)). Qed.
Lemma lem7621491 {B : Type'} (_98076 : nat) (_98077 : nat) : (term211 B _98076 _98077) = (term212 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621490 _98076) (@lem7621489 B _98076 _98077)). Qed.
Lemma lem7621495 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621496 {B : Type'} (_98076 : nat) (_98077 : nat) : (term212 B _98076 _98077) = (term213 B _98076 _98077).
Proof. exact (@lem7621495 (_98076 = _98077) (term170 _98076) (term214 B _98076 _98077)). Qed.
Lemma lem7621512 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621513 {B : Type'} (_98076 : nat) (_98077 : nat) : (term215 B _98076 _98077) = (term216 B _98076 _98077).
Proof. exact (@lem7621512 (term171 B _98077) (term170 _98076) (term210 B _98076 _98077)). Qed.
Lemma lem7621541 (_98076 : nat) (_98077 : nat) : (term217 _98076 _98077) = (term217 _98076 _98077).
Proof. exact (eq_refl (term217 _98076 _98077)). Qed.
Lemma lem7621542 {B : Type'} (_98076 : nat) (_98077 : nat) : (term213 B _98076 _98077) = (term218 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621541 _98076 _98077) (@lem7621513 B _98076 _98077)). Qed.
Lemma lem7621553 {B : Type'} (_98076 : nat) (_98077 : nat) : (term212 B _98076 _98077) = (term218 B _98076 _98077).
Proof. exact (TRANS (@lem7621496 B _98076 _98077) (@lem7621542 B _98076 _98077)). Qed.
Lemma lem7621554 {B : Type'} (_98076 : nat) (_98077 : nat) : (term211 B _98076 _98077) = (term218 B _98076 _98077).
Proof. exact (TRANS (@lem7621491 B _98076 _98077) (@lem7621553 B _98076 _98077)). Qed.
Lemma lem7621555 {B : Type'} (_98076 : nat) : (term144 B _98076) = (term144 B _98076).
Proof. exact (eq_refl (term144 B _98076)). Qed.
Lemma lem7621556 {B : Type'} (_98076 : nat) (_98077 : nat) : (term202 B _98076 _98077) = (term219 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621555 B _98076) (@lem7621554 B _98076 _98077)). Qed.
Lemma lem7621560 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621561 {B : Type'} (_98076 : nat) (_98077 : nat) : (term219 B _98076 _98077) = (term220 B _98076 _98077).
Proof. exact (@lem7621560 (_98076 = _98077) (term171 B _98076) (term216 B _98076 _98077)). Qed.
Lemma lem7621611 {B : Type'} (_98076 : nat) (_98077 : nat) : (term202 B _98076 _98077) = (term220 B _98076 _98077).
Proof. exact (TRANS (@lem7621556 B _98076 _98077) (@lem7621561 B _98076 _98077)). Qed.
Lemma lem7621612 {B : Type'} (_98076 : nat) (_98077 : nat) : (term183 B _98076 _98077) = (term220 B _98076 _98077).
Proof. exact (TRANS (@lem7621365 B _98076 _98077) (@lem7621611 B _98076 _98077)). Qed.
Lemma lem7621613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7621614 {B : Type'} (_98076 : nat) (_98077 : nat) : (term221 B _98076 _98077) = (term222 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621613) (@lem7621612 B _98076 _98077)). Qed.
Lemma lem7621630 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621631 {B : Type'} (_98076 : nat) (_98077 : nat) : (term223 B _98076 _98077) = (term224 B _98076 _98077).
Proof. exact (@lem7621630 (term171 B _98076) (term170 _98076) (term225 B _98076 _98077)). Qed.
Lemma lem7621655 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621656 {B : Type'} (_98076 : nat) (_98077 : nat) : (term225 B _98076 _98077) = (term214 B _98076 _98077).
Proof. exact (@lem7621655 (term171 B _98077) (term170 _98077) (term172 B _98076 _98077)). Qed.
Lemma lem7621674 (_98076 : nat) : (term130 _98076) = (term130 _98076).
Proof. exact (eq_refl (term130 _98076)). Qed.
Lemma lem7621675 {B : Type'} (_98076 : nat) (_98077 : nat) : (term226 B _98076 _98077) = (term215 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621674 _98076) (@lem7621656 B _98076 _98077)). Qed.
Lemma lem7621679 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7621680 {B : Type'} (_98076 : nat) (_98077 : nat) : (term215 B _98076 _98077) = (term216 B _98076 _98077).
Proof. exact (@lem7621679 (term171 B _98077) (term170 _98076) (term210 B _98076 _98077)). Qed.
Lemma lem7621708 {B : Type'} (_98076 : nat) (_98077 : nat) : (term226 B _98076 _98077) = (term216 B _98076 _98077).
Proof. exact (TRANS (@lem7621675 B _98076 _98077) (@lem7621680 B _98076 _98077)). Qed.
Lemma lem7621709 {B : Type'} (_98076 : nat) : (term144 B _98076) = (term144 B _98076).
Proof. exact (eq_refl (term144 B _98076)). Qed.
Lemma lem7621710 {B : Type'} (_98076 : nat) (_98077 : nat) : (term224 B _98076 _98077) = (term227 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621709 B _98076) (@lem7621708 B _98076 _98077)). Qed.
Lemma lem7621721 {B : Type'} (_98076 : nat) (_98077 : nat) : (term223 B _98076 _98077) = (term227 B _98076 _98077).
Proof. exact (TRANS (@lem7621631 B _98076 _98077) (@lem7621710 B _98076 _98077)). Qed.
Lemma lem7621722 (_98076 : nat) (_98077 : nat) : (term217 _98076 _98077) = (term217 _98076 _98077).
Proof. exact (eq_refl (term217 _98076 _98077)). Qed.
Lemma lem7621723 {B : Type'} (_98076 : nat) (_98077 : nat) : (term228 B _98076 _98077) = (term220 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621722 _98076 _98077) (@lem7621721 B _98076 _98077)). Qed.
Lemma lem7621734 {B : Type'} (_98076 : nat) (_98077 : nat) : ((term183 B _98076 _98077) = (term228 B _98076 _98077)) = ((term220 B _98076 _98077) = (term220 B _98076 _98077)).
Proof. exact (MK_COMB (@lem7621614 B _98076 _98077) (@lem7621723 B _98076 _98077)). Qed.
Lemma lem7621736 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7621737 (x : Prop) : (x = x) = True.
Proof. exact (@lem7621736 Prop x). Qed.
Lemma lem7621738 {B : Type'} (_98076 : nat) (_98077 : nat) : ((term220 B _98076 _98077) = (term220 B _98076 _98077)) = True.
Proof. exact (@lem7621737 (term220 B _98076 _98077)). Qed.
Lemma lem7621739 {B : Type'} (_98076 : nat) (_98077 : nat) : ((term183 B _98076 _98077) = (term228 B _98076 _98077)) = True.
Proof. exact (TRANS (@lem7621734 B _98076 _98077) (@lem7621738 B _98076 _98077)). Qed.
Lemma lem7621740 {B : Type'} (_98076 : nat) (_98077 : nat) : True = ((term183 B _98076 _98077) = (term228 B _98076 _98077)).
Proof. exact (SYM (@lem7621739 B _98076 _98077)). Qed.
Lemma lem7621741 {B : Type'} (_98076 : nat) (_98077 : nat) : (term183 B _98076 _98077) = (term228 B _98076 _98077).
Proof. exact (EQ_MP (@lem7621740 B _98076 _98077) (@lem0)). Qed.
Lemma lem7621742 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term228 B _98076 _98077.
Proof. exact (EQ_MP (@lem7621741 B _98076 _98077) (@lem7620381 B _98076 _98077 h1)). Qed.
Lemma lem7621744 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7621745 {B : Type'} (_98076 : nat) (_98077 : nat) : (term228 B _98076 _98077) = (term230 B _98076 _98077).
Proof. exact (@lem7621744 (term223 B _98076 _98077) (_98076 = _98077)). Qed.
Lemma lem7621747 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7621748 {B : Type'} (_98076 : nat) (_98077 : nat) : (term233 B _98076 _98077) = (term234 B _98076 _98077).
Proof. exact (@lem7621747 (term170 _98076) (term235 B _98076 _98077)). Qed.
Lemma lem7621750 (a : Prop) : (term236 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7621751 (_98076 : nat) : (term237 _98076) = (term74 _98076).
Proof. exact (@lem7621750 (term74 _98076)). Qed.
Lemma lem7621752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7621753 (_98076 : nat) : (term238 _98076) = (term239 _98076).
Proof. exact (MK_COMB (@lem7621752) (@lem7621751 _98076)). Qed.
Lemma lem7621755 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7621756 {B : Type'} (_98076 : nat) (_98077 : nat) : (term240 B _98076 _98077) = (term241 B _98076 _98077).
Proof. exact (@lem7621755 (term171 B _98076) (term225 B _98076 _98077)). Qed.
Lemma lem7621758 (a : Prop) : (term236 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7621759 {B : Type'} (_98076 : nat) : (term242 B _98076) = (term73 B _98076).
Proof. exact (@lem7621758 (term73 B _98076)). Qed.
Lemma lem7621760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7621761 {B : Type'} (_98076 : nat) : (term243 B _98076) = (term244 B _98076).
Proof. exact (MK_COMB (@lem7621760) (@lem7621759 B _98076)). Qed.
Lemma lem7621763 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7621764 {B : Type'} (_98076 : nat) (_98077 : nat) : (term245 B _98076 _98077) = (term246 B _98076 _98077).
Proof. exact (@lem7621763 (term170 _98077) (term247 B _98076 _98077)). Qed.
Lemma lem7621766 (a : Prop) : (term236 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7621767 (_98077 : nat) : (term237 _98077) = (term74 _98077).
Proof. exact (@lem7621766 (term74 _98077)). Qed.
Lemma lem7621768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7621769 (_98077 : nat) : (term238 _98077) = (term239 _98077).
Proof. exact (MK_COMB (@lem7621768) (@lem7621767 _98077)). Qed.
Lemma lem7621771 (a : Prop) (b : Prop) : (term231 a b) = (term232 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7621772 {B : Type'} (_98076 : nat) (_98077 : nat) : (term248 B _98076 _98077) = (term249 B _98076 _98077).
Proof. exact (@lem7621771 (term171 B _98077) (term172 B _98076 _98077)). Qed.
Lemma lem7621774 (a : Prop) : (term236 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7621775 {B : Type'} (_98077 : nat) : (term242 B _98077) = (term73 B _98077).
Proof. exact (@lem7621774 (term73 B _98077)). Qed.
Lemma lem7621776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7621777 {B : Type'} (_98077 : nat) : (term243 B _98077) = (term244 B _98077).
Proof. exact (MK_COMB (@lem7621776) (@lem7621775 B _98077)). Qed.
Lemma lem7621779 (a : Prop) : (term236 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7621780 {B : Type'} (_98076 : nat) (_98077 : nat) : (term250 B _98076 _98077) = ((@finite_index B _98076) = (@finite_index B _98077)).
Proof. exact (@lem7621779 ((@finite_index B _98076) = (@finite_index B _98077))). Qed.
Lemma lem7621781 {B : Type'} (_98076 : nat) (_98077 : nat) : (term249 B _98076 _98077) = (term251 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621777 B _98077) (@lem7621780 B _98076 _98077)). Qed.
Lemma lem7621782 {B : Type'} (_98076 : nat) (_98077 : nat) : (term248 B _98076 _98077) = (term251 B _98076 _98077).
Proof. exact (TRANS (@lem7621772 B _98076 _98077) (@lem7621781 B _98076 _98077)). Qed.
Lemma lem7621783 {B : Type'} (_98076 : nat) (_98077 : nat) : (term246 B _98076 _98077) = (term252 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621769 _98077) (@lem7621782 B _98076 _98077)). Qed.
Lemma lem7621784 {B : Type'} (_98076 : nat) (_98077 : nat) : (term245 B _98076 _98077) = (term252 B _98076 _98077).
Proof. exact (TRANS (@lem7621764 B _98076 _98077) (@lem7621783 B _98076 _98077)). Qed.
Lemma lem7621785 {B : Type'} (_98076 : nat) (_98077 : nat) : (term241 B _98076 _98077) = (term253 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621761 B _98076) (@lem7621784 B _98076 _98077)). Qed.
Lemma lem7621786 {B : Type'} (_98076 : nat) (_98077 : nat) : (term240 B _98076 _98077) = (term253 B _98076 _98077).
Proof. exact (TRANS (@lem7621756 B _98076 _98077) (@lem7621785 B _98076 _98077)). Qed.
Lemma lem7621787 {B : Type'} (_98076 : nat) (_98077 : nat) : (term234 B _98076 _98077) = (term254 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621753 _98076) (@lem7621786 B _98076 _98077)). Qed.
Lemma lem7621788 {B : Type'} (_98076 : nat) (_98077 : nat) : (term233 B _98076 _98077) = (term254 B _98076 _98077).
Proof. exact (TRANS (@lem7621748 B _98076 _98077) (@lem7621787 B _98076 _98077)). Qed.
Lemma lem7621789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7621790 {B : Type'} (_98076 : nat) (_98077 : nat) : (term255 B _98076 _98077) = (term256 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621789) (@lem7621788 B _98076 _98077)). Qed.
Lemma lem7621791 (_98076 : nat) (_98077 : nat) : (_98076 = _98077) = (_98076 = _98077).
Proof. exact (eq_refl (_98076 = _98077)). Qed.
Lemma lem7621792 {B : Type'} (_98076 : nat) (_98077 : nat) : (term230 B _98076 _98077) = (term257 B _98076 _98077).
Proof. exact (MK_COMB (@lem7621790 B _98076 _98077) (@lem7621791 _98076 _98077)). Qed.
Lemma lem7621793 {B : Type'} (_98076 : nat) (_98077 : nat) : (term228 B _98076 _98077) = (term257 B _98076 _98077).
Proof. exact (TRANS (@lem7621745 B _98076 _98077) (@lem7621792 B _98076 _98077)). Qed.
Lemma lem7621795 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) (h2 : term73 B i) : term251 B y i.
Proof. exact (conj (@lem7621351 B i h2) (@lem7621358 B y i h1)). Qed.
Lemma lem7621796 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) (h2 : term73 B i) (h3 : term74 i) : term252 B y i.
Proof. exact (conj (@lem7621344 i h3) (@lem7621795 B y i h1 h2)). Qed.
Lemma lem7621797 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) (h2 : term73 B i) (h3 : term74 i) : term253 B y i.
Proof. exact (conj (@lem7621337 B y i h1) (@lem7621796 B y i h1 h2 h3)). Qed.
Lemma lem7621798 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) (h2 : term73 B i) (h3 : term74 i) : term254 B y i.
Proof. exact (conj (@lem7621330 B y i h1) (@lem7621797 B y i h1 h2 h3)). Qed.
Lemma lem7621800 {B : Type'} (_98076 : nat) (_98077 : nat) (h1 : term89 B) : term257 B _98076 _98077.
Proof. exact (EQ_MP (@lem7621793 B _98076 _98077) (@lem7621742 B _98076 _98077 h1)). Qed.
Lemma lem7621801 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) : term257 B y i.
Proof. exact (@lem7621800 B y i h1). Qed.
Lemma lem7621804 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : y = i.
Proof. exact (@lem7621801 B y i h1 (@lem7621798 B y i h2 h3 h4)). Qed.
Lemma lem7621805 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : term258 y i.
Proof. exact (fun h0 : term176 y i => @lem7621804 B y i h1 h2 h3 h4). Qed.
Lemma lem7621807 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621808 (y : nat) (i : nat) : (term258 y i) = (y = i).
Proof. exact (@lem7621807 (y = i)). Qed.
Lemma lem7621809 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : y = i.
Proof. exact (EQ_MP (@lem7621808 y i) (@lem7621805 B y i h1 h2 h3 h4)). Qed.
Lemma lem7621812 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7621814 (y : nat) (i : nat) : (term176 y i) = (term259 y i).
Proof. exact (@lem7621812 (y = i)). Qed.
Lemma lem7621817 {B : Type'} (y : nat) (i : nat) (h1 : term162 B y i) : term259 y i.
Proof. exact (EQ_MP (@lem7621814 y i) (@lem7620319 B y i h1)). Qed.
Lemma lem7621820 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (@lem7621817 B y i h2 (@lem7621809 B y i h1 h2 h3 h4)). Qed.
Lemma lem7621821 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : term260.
Proof. exact (fun h0 : ~ False => @lem7621820 B y i h1 h2 h3 h4). Qed.
Lemma lem7621823 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621824 : term260 = False.
Proof. exact (@lem7621823 False). Qed.
Lemma lem7621825 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7621824) (@lem7621821 B y i h1 h2 h3 h4)). Qed.
Lemma lem7621924 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (h1). Qed.
Lemma lem7621925 (i : nat) (h1 : term74 i) : term198 i.
Proof. exact (fun h0 : term170 i => @lem7621924 i h1). Qed.
Lemma lem7621927 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621928 (i : nat) : (term198 i) = (term74 i).
Proof. exact (@lem7621927 (term74 i)). Qed.
Lemma lem7621929 (i : nat) (h1 : term74 i) : term74 i.
Proof. exact (EQ_MP (@lem7621928 i) (@lem7621925 i h1)). Qed.
Lemma lem7621932 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7621934 (i : nat) : (term170 i) = (term261 i).
Proof. exact (@lem7621932 (term74 i)). Qed.
Lemma lem7621937 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) : term261 i.
Proof. exact (EQ_MP (@lem7621934 i) (@lem7620892 B y i h1 h2)). Qed.
Lemma lem7621940 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (@lem7621937 B y i h1 h2 (@lem7621929 i h3)). Qed.
Lemma lem7621941 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : term260.
Proof. exact (fun h0 : ~ False => @lem7621940 B y i h1 h2 h3). Qed.
Lemma lem7621943 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7621944 : term260 = False.
Proof. exact (@lem7621943 False). Qed.
Lemma lem7621945 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7621944) (@lem7621941 B y i h1 h2 h3)). Qed.
Lemma lem7622044 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (h1). Qed.
Lemma lem7622045 {B : Type'} (i : nat) (h1 : term73 B i) : term200 B i.
Proof. exact (fun h0 : term171 B i => @lem7622044 B i h1). Qed.
Lemma lem7622047 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7622048 {B : Type'} (i : nat) : (term200 B i) = (term73 B i).
Proof. exact (@lem7622047 (term73 B i)). Qed.
Lemma lem7622049 {B : Type'} (i : nat) (h1 : term73 B i) : term73 B i.
Proof. exact (EQ_MP (@lem7622048 B i) (@lem7622045 B i h1)). Qed.
Lemma lem7622052 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7622054 {B : Type'} (i : nat) : (term171 B i) = (term262 B i).
Proof. exact (@lem7622052 (term73 B i)). Qed.
Lemma lem7622057 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) : term262 B i.
Proof. exact (EQ_MP (@lem7622054 B i) (@lem7621031 B y i h1 h2)). Qed.
Lemma lem7622060 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (@lem7622057 B y i h1 h2 (@lem7622049 B i h3)). Qed.
Lemma lem7622061 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : term260.
Proof. exact (fun h0 : ~ False => @lem7622060 B y i h1 h2 h3). Qed.
Lemma lem7622063 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7622064 : term260 = False.
Proof. exact (@lem7622063 False). Qed.
Lemma lem7622065 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622064) (@lem7622061 B y i h1 h2 h3)). Qed.
Lemma lem7622164 {B : Type'} (x : finite_image B) : x = x.
Proof. exact (@lem21386 (finite_image B) x). Qed.
Lemma lem7622165 {B : Type'} (x : finite_image B) : x = x.
Proof. exact (@lem7622164 B x). Qed.
Lemma lem7622166 {B : Type'} (i : nat) : (@finite_index B i) = (@finite_index B i).
Proof. exact (@lem7622165 B (@finite_index B i)). Qed.
Lemma lem7622167 {B : Type'} (i : nat) : term263 B i.
Proof. exact (fun h0 : term195 B i => @lem7622166 B i). Qed.
Lemma lem7622169 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7622170 {B : Type'} (i : nat) : (term263 B i) = ((@finite_index B i) = (@finite_index B i)).
Proof. exact (@lem7622169 ((@finite_index B i) = (@finite_index B i))). Qed.
Lemma lem7622171 {B : Type'} (i : nat) : (@finite_index B i) = (@finite_index B i).
Proof. exact (EQ_MP (@lem7622170 B i) (@lem7622167 B i)). Qed.
Lemma lem7622174 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7622176 {B : Type'} (i : nat) : (term195 B i) = (term264 B i).
Proof. exact (@lem7622174 ((@finite_index B i) = (@finite_index B i))). Qed.
Lemma lem7622179 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : term264 B i.
Proof. exact (EQ_MP (@lem7622176 B i) (@lem7621170 B y i h1 h2)). Qed.
Lemma lem7622182 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : False.
Proof. exact (@lem7622179 B y i h1 h2 (@lem7622171 B i)). Qed.
Lemma lem7622183 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : term260.
Proof. exact (fun h0 : ~ False => @lem7622182 B y i h1 h2). Qed.
Lemma lem7622185 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7622186 : term260 = False.
Proof. exact (@lem7622185 False). Qed.
Lemma lem7622188 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : False.
Proof. exact (EQ_MP (@lem7622186) (@lem7622183 B y i h1 h2)). Qed.
Lemma lem7622189 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h4 : term73 B i => @lem7622065 B y i h1 h2 h3) (fun h4 : False => @lem7620990 B i h3)). Qed.
Lemma lem7622191 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622189 B y i h1 h2 h3) (@lem7620990 B i h3)). Qed.
Lemma lem7622192 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h4 : term74 i => @lem7621945 B y i h1 h2 h3) (fun h4 : False => @lem7620837 i h3)). Qed.
Lemma lem7622194 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622192 B y i h1 h2 h3) (@lem7620837 i h3)). Qed.
Lemma lem7622195 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : (term172 B y i) = False.
Proof. exact (prop_ext (fun h3 : term172 B y i => @lem7622188 B y i h1 h2) (fun h3 : False => @lem7620697 B y i h1)). Qed.
Lemma lem7622196 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : False.
Proof. exact (EQ_MP (@lem7622195 B y i h1 h2) (@lem7620697 B y i h1)). Qed.
Lemma lem7622197 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term171 B y) = False.
Proof. exact (prop_ext (fun h4 : term171 B y => @lem7622191 B y i h1 h2 h3) (fun h4 : False => @lem7620573 B y h1)). Qed.
Lemma lem7622198 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622197 B y i h1 h2 h3) (@lem7620573 B y h1)). Qed.
Lemma lem7622199 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h4 : term73 B i => @lem7622198 B y i h1 h2 h3) (fun h4 : False => @lem7620565 B i h3)). Qed.
Lemma lem7622200 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622199 B y i h1 h2 h3) (@lem7620565 B i h3)). Qed.
Lemma lem7622201 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term170 y) = False.
Proof. exact (prop_ext (fun h4 : term170 y => @lem7622194 B y i h1 h2 h3) (fun h4 : False => @lem7620449 y h1)). Qed.
Lemma lem7622202 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622201 B y i h1 h2 h3) (@lem7620449 y h1)). Qed.
Lemma lem7622203 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h4 : term74 i => @lem7622202 B y i h1 h2 h3) (fun h4 : False => @lem7620439 i h3)). Qed.
Lemma lem7622204 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622203 B y i h1 h2 h3) (@lem7620439 i h3)). Qed.
Lemma lem7622205 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h5 : term73 B i => @lem7621825 B y i h1 h2 h3 h4) (fun h5 : False => @lem7620313 B i h3)). Qed.
Lemma lem7622206 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622205 B y i h1 h2 h3 h4) (@lem7620313 B i h3)). Qed.
Lemma lem7622207 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h5 : term74 i => @lem7622206 B y i h1 h2 h3 h4) (fun h5 : False => @lem7620311 i h4)). Qed.
Lemma lem7622208 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622207 B y i h1 h2 h3 h4) (@lem7620311 i h4)). Qed.
Lemma lem7622209 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : (term172 B y i) = False.
Proof. exact (prop_ext (fun h3 : term172 B y i => @lem7622196 B y i h1 h2) (fun h3 : False => @lem7620197 B y i h1)). Qed.
Lemma lem7622210 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : False.
Proof. exact (EQ_MP (@lem7622209 B y i h1 h2) (@lem7620197 B y i h1)). Qed.
Lemma lem7622211 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term171 B y) = False.
Proof. exact (prop_ext (fun h4 : term171 B y => @lem7622200 B y i h1 h2 h3) (fun h4 : False => @lem7620049 B y h1)). Qed.
Lemma lem7622212 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622211 B y i h1 h2 h3) (@lem7620049 B y h1)). Qed.
Lemma lem7622213 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h4 : term73 B i => @lem7622212 B y i h1 h2 h3) (fun h4 : False => @lem7619909 B i h3)). Qed.
Lemma lem7622214 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622213 B y i h1 h2 h3) (@lem7619909 B i h3)). Qed.
Lemma lem7622215 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term170 y) = False.
Proof. exact (prop_ext (fun h4 : term170 y => @lem7622204 B y i h1 h2 h3) (fun h4 : False => @lem7619901 y h1)). Qed.
Lemma lem7622216 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622215 B y i h1 h2 h3) (@lem7619901 y h1)). Qed.
Lemma lem7622217 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h4 : term74 i => @lem7622216 B y i h1 h2 h3) (fun h4 : False => @lem7619757 i h3)). Qed.
Lemma lem7622218 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622217 B y i h1 h2 h3) (@lem7619757 i h3)). Qed.
Lemma lem7622219 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h5 : term73 B i => @lem7622208 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619605 B i h3)). Qed.
Lemma lem7622220 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622219 B y i h1 h2 h3 h4) (@lem7619605 B i h3)). Qed.
Lemma lem7622221 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h5 : term74 i => @lem7622220 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619601 i h4)). Qed.
Lemma lem7622222 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622221 B y i h1 h2 h3 h4) (@lem7619601 i h4)). Qed.
Lemma lem7622223 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : (term172 B y i) = False.
Proof. exact (prop_ext (fun h3 : term172 B y i => @lem7622210 B y i h1 h2) (fun h3 : False => @lem7620197 B y i h1)). Qed.
Lemma lem7622224 {B : Type'} (y : nat) (i : nat) (h1 : term172 B y i) (h2 : term138 B y i) : False.
Proof. exact (EQ_MP (@lem7622223 B y i h1 h2) (@lem7620197 B y i h1)). Qed.
Lemma lem7622225 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term171 B y) = False.
Proof. exact (prop_ext (fun h4 : term171 B y => @lem7622214 B y i h1 h2 h3) (fun h4 : False => @lem7620049 B y h1)). Qed.
Lemma lem7622226 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622225 B y i h1 h2 h3) (@lem7620049 B y h1)). Qed.
Lemma lem7622227 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h4 : term73 B i => @lem7622226 B y i h1 h2 h3) (fun h4 : False => @lem7619909 B i h3)). Qed.
Lemma lem7622228 {B : Type'} (y : nat) (i : nat) (h1 : term171 B y) (h2 : term138 B y i) (h3 : term73 B i) : False.
Proof. exact (EQ_MP (@lem7622227 B y i h1 h2 h3) (@lem7619909 B i h3)). Qed.
Lemma lem7622229 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term170 y) = False.
Proof. exact (prop_ext (fun h4 : term170 y => @lem7622218 B y i h1 h2 h3) (fun h4 : False => @lem7619901 y h1)). Qed.
Lemma lem7622230 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622229 B y i h1 h2 h3) (@lem7619901 y h1)). Qed.
Lemma lem7622231 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h4 : term74 i => @lem7622230 B y i h1 h2 h3) (fun h4 : False => @lem7619757 i h3)). Qed.
Lemma lem7622232 {B : Type'} (y : nat) (i : nat) (h1 : term170 y) (h2 : term138 B y i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622231 B y i h1 h2 h3) (@lem7619757 i h3)). Qed.
Lemma lem7622233 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h5 : term73 B i => @lem7622222 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619605 B i h3)). Qed.
Lemma lem7622234 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622233 B y i h1 h2 h3 h4) (@lem7619605 B i h3)). Qed.
Lemma lem7622235 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h5 : term74 i => @lem7622234 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619601 i h4)). Qed.
Lemma lem7622236 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term162 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622235 B y i h1 h2 h3 h4) (@lem7619601 i h4)). Qed.
Lemma lem7622237 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) (h2 : term73 B i) (h3 : term129 B y i) : False.
Proof. exact (or_elim (@lem7619595 B y i h3) (fun h0 : term171 B y => @lem7622228 B y i h0 h1 h2) (fun h0 : term172 B y i => @lem7622224 B y i h0 h1)). Qed.
Lemma lem7622238 {B : Type'} (y : nat) (i : nat) (h1 : term138 B y i) (h2 : term73 B i) (h3 : term74 i) : False.
Proof. exact (or_elim (@lem7619593 B y i h1) (fun h0 : term170 y => @lem7622232 B y i h0 h1 h3) (fun h0 : term129 B y i => @lem7622237 B y i h1 h2 h0)). Qed.
Lemma lem7622239 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (or_elim (@lem7619351 B y i h2) (fun h0 : term162 B y i => @lem7622236 B y i h1 h0 h3 h4) (fun h0 : term138 B y i => @lem7622238 B y i h0 h3 h4)). Qed.
Lemma lem7622240 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h5 : term73 B i => @lem7622239 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619261 B i h3)). Qed.
Lemma lem7622241 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622240 B y i h1 h2 h3 h4) (@lem7619261 B i h3)). Qed.
Lemma lem7622242 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h5 : term74 i => @lem7622241 B y i h1 h2 h3 h4) (fun h5 : False => @lem7619253 i h4)). Qed.
Lemma lem7622243 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622242 B y i h1 h2 h3 h4) (@lem7619253 i h4)). Qed.
Lemma lem7622244 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : (term73 B i) = False.
Proof. exact (prop_ext (fun h5 : term73 B i => @lem7622243 B y i h1 h2 h3 h4) (fun h5 : False => @lem7618959 B i h3)). Qed.
Lemma lem7622245 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622244 B y i h1 h2 h3 h4) (@lem7618959 B i h3)). Qed.
Lemma lem7622246 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : (term74 i) = False.
Proof. exact (prop_ext (fun h5 : term74 i => @lem7622245 B y i h1 h2 h3 h4) (fun h5 : False => @lem7618953 i h4)). Qed.
Lemma lem7622247 {B : Type'} (y : nat) (i : nat) (h1 : term89 B) (h2 : term88 B y i) (h3 : term73 B i) (h4 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622246 B y i h1 h2 h3 h4) (@lem7618953 i h4)). Qed.
Lemma lem7622248 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term95 B.
Proof. exact (fun h0 : term89 B => @lem7622247 B y i h0 h1 h2 h3). Qed.
Lemma lem7622249 {B : Type'} : (term95 B) = (term96 B).
Proof. exact (@lem69 (term89 B)). Qed.
Lemma lem7622250 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term96 B.
Proof. exact (EQ_MP (@lem7622249 B) (@lem7622248 B y i h1 h2 h3)). Qed.
Lemma lem7622251 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term99 A B.
Proof. exact (fun h0 : term89 A => @lem7622250 B y i h1 h2 h3). Qed.
Lemma lem7622252 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term102 A B.
Proof. exact (fun h0 : term90 B => @lem7622251 A B y i h1 h2 h3). Qed.
Lemma lem7622253 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term104 A B.
Proof. exact (fun h0 : term90 A => @lem7622252 A B y i h1 h2 h3). Qed.
Lemma lem7622254 {A B : Type'} (y : nat) (i : nat) (h1 : term73 B i) (h2 : term74 i) : term107 A B y i.
Proof. exact (fun h0 : term88 B y i => @lem7622253 A B y i h0 h1 h2). Qed.
Lemma lem7622255 {A B : Type'} (y : nat) (i : nat) (h1 : term74 i) : term110 A B y i.
Proof. exact (fun h0 : term73 B i => @lem7622254 A B y i h0 h1). Qed.
Lemma lem7622256 {A B : Type'} (y : nat) (i : nat) : term112 A B y i.
Proof. exact (fun h0 : term74 i => @lem7622255 A B y i h0). Qed.
Lemma lem7622261 {A B : Type'} (i : nat) : term116 A B i.
Proof. exact (fun y : nat => @lem7622256 A B y i). Qed.
Lemma lem7622266 {A B : Type'} : term120 A B.
Proof. exact (fun i : nat => @lem7622261 A B i). Qed.
Lemma lem7622267 {A B : Type'} : term119 A B.
Proof. exact (EQ_MP (@lem7618940 A B) (@lem7622266 A B)). Qed.
Lemma lem7622268 {A B : Type'} (i : nat) : term265 A B i.
Proof. exact (@lem7622267 A B i). Qed.
Lemma lem7622269 {A B : Type'} (i : nat) : (term265 A B i) = (term115 A B i).
Proof. exact (eq_refl (term265 A B i)). Qed.
Lemma lem7622270 {A B : Type'} (i : nat) : term115 A B i.
Proof. exact (EQ_MP (@lem7622269 A B i) (@lem7622268 A B i)). Qed.
Lemma lem7622271 {A B : Type'} (i : nat) (y : nat) : term266 A B i y.
Proof. exact (@lem7622270 A B i y). Qed.
Lemma lem7622272 {A B : Type'} (y : nat) (i : nat) : (term266 A B i y) = (term91 A B y i).
Proof. exact (eq_refl (term266 A B i y)). Qed.
Lemma lem7622273 {A B : Type'} (y : nat) (i : nat) : term91 A B y i.
Proof. exact (EQ_MP (@lem7622272 A B y i) (@lem7622271 A B i y)). Qed.
Lemma lem7622275 {A B : Type'} (y : nat) (i : nat) : term91 A B y i.
Proof. exact (@lem7618616 A B y i (@lem7622273 A B y i)). Qed.
Lemma lem7622276 {A B : Type'} (y : nat) (i : nat) (h1 : term74 i) : term109 A B y i.
Proof. exact (@lem7622275 A B y i (@lem7618554 i h1)). Qed.
Lemma lem7622277 {A B : Type'} (y : nat) (i : nat) (h1 : term73 B i) (h2 : term74 i) : term106 A B y i.
Proof. exact (@lem7622276 A B y i h2 (@lem7618553 B i h1)). Qed.
Lemma lem7622278 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term103 A B.
Proof. exact (@lem7622277 A B y i h2 h3 (@lem7618594 B y i h1)). Qed.
Lemma lem7622279 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term101 A B.
Proof. exact (@lem7622278 A B y i h1 h2 h3 (@lem7608063 A)). Qed.
Lemma lem7622280 {A B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term98 A B.
Proof. exact (@lem7622279 A B y i h1 h2 h3 (@lem7618599 B)). Qed.
Lemma lem7622281 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : term95 B.
Proof. exact (@lem7622280 Prop B y i h1 h2 h3 (@lem7612100 Prop)). Qed.
Lemma lem7622282 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : False.
Proof. exact (@lem7622281 B y i h1 h2 h3 (@lem7618595 B)). Qed.
Lemma lem7622283 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : (term88 B y i) = False.
Proof. exact (prop_ext (fun h4 : term88 B y i => @lem7622282 B y i h1 h2 h3) (fun h4 : False => @lem7618594 B y i h1)). Qed.
Lemma lem7622284 {B : Type'} (y : nat) (i : nat) (h1 : term88 B y i) (h2 : term73 B i) (h3 : term74 i) : False.
Proof. exact (EQ_MP (@lem7622283 B y i h1 h2 h3) (@lem7618594 B y i h1)). Qed.
Lemma lem7622285 {B : Type'} (y : nat) (i : nat) (h1 : term73 B i) (h2 : term74 i) : term87 B y i.
Proof. exact (fun h0 : term88 B y i => @lem7622284 B y i h0 h1 h2). Qed.
Lemma lem7622286 {B : Type'} (y : nat) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term81 B y i) = (y = i).
Proof. exact (EQ_MP (@lem7618593 B y i) (@lem7622285 B y i h1 h2)). Qed.
Lemma lem7622287 {B : Type'} (y : nat) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term80 B i y) = (y = i).
Proof. exact (EQ_MP (@lem7618589 B y i) (@lem7622286 B y i h1 h2)). Qed.
Lemma lem7622292 {B : Type'} (i : nat) (h1 : term73 B i) (h2 : term74 i) : term267 B i.
Proof. exact (fun y : nat => @lem7622287 B y i h1 h2). Qed.
Lemma lem7622293 {B : Type'} (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term268 B i) = i.
Proof. exact (@lem7618559 B i (@lem7622292 B i h1 h2)). Qed.
Lemma lem7622294 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term63 A B g i) = (g i).
Proof. exact (MK_COMB (@lem7618555 A g) (@lem7622293 B i h1 h2)). Qed.
Lemma lem7622295 {B : Type'} (i : nat) (h1 : term72 B i) : term73 B i.
Proof. exact (proj2 (@lem7618552 B i h1)). Qed.
Lemma lem7622296 {B : Type'} (i : nat) (h1 : term72 B i) : term74 i.
Proof. exact (proj1 (@lem7618552 B i h1)). Qed.
Lemma lem7622297 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term73 B i) = ((term63 A B g i) = (g i)).
Proof. exact (prop_ext (fun h3 : term73 B i => @lem7622294 A B g i h1 h2) (fun h3 : (term63 A B g i) = (g i) => @lem7618553 B i h1)). Qed.
Lemma lem7622298 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term63 A B g i) = (g i).
Proof. exact (EQ_MP (@lem7622297 A B g i h1 h2) (@lem7618553 B i h1)). Qed.
Lemma lem7622299 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term74 i) = ((term63 A B g i) = (g i)).
Proof. exact (prop_ext (fun h3 : term74 i => @lem7622298 A B g i h1 h2) (fun h3 : (term63 A B g i) = (g i) => @lem7618554 i h2)). Qed.
Lemma lem7622300 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term73 B i) (h2 : term74 i) : (term63 A B g i) = (g i).
Proof. exact (EQ_MP (@lem7622299 A B g i h1 h2) (@lem7618554 i h2)). Qed.
Lemma lem7622301 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term72 B i) (h2 : term74 i) : (term73 B i) = ((term63 A B g i) = (g i)).
Proof. exact (prop_ext (fun h3 : term73 B i => @lem7622300 A B g i h3 h2) (fun h3 : (term63 A B g i) = (g i) => @lem7622295 B i h1)). Qed.
Lemma lem7622302 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term72 B i) (h2 : term74 i) : (term63 A B g i) = (g i).
Proof. exact (EQ_MP (@lem7622301 A B g i h1 h2) (@lem7622295 B i h1)). Qed.
Lemma lem7622303 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term72 B i) : (term74 i) = ((term63 A B g i) = (g i)).
Proof. exact (prop_ext (fun h2 : term74 i => @lem7622302 A B g i h1 h2) (fun h2 : (term63 A B g i) = (g i) => @lem7622296 B i h1)). Qed.
Lemma lem7622304 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term72 B i) : (term63 A B g i) = (g i).
Proof. exact (EQ_MP (@lem7622303 A B g i h1) (@lem7622296 B i h1)). Qed.
Lemma lem7622305 {A B : Type'} (g : nat -> A) (i : nat) : term67 A B g i.
Proof. exact (fun h0 : term72 B i => @lem7622304 A B g i h0). Qed.
Lemma lem7622310 {A B : Type'} (g : nat -> A) : term71 A B g.
Proof. exact (fun i : nat => @lem7622305 A B g i). Qed.
Lemma lem7622311 {A B : Type'} (g : nat -> A) : term70 A B g.
Proof. exact (EQ_MP (@lem7618551 A B g) (@lem7622310 A B g)). Qed.
Lemma lem7622312 {A B : Type'} (g : nat -> A) : term45 A B g.
Proof. exact (ex_intro (term46 A B g) (term51 A B g) (@lem7622311 A B g)). Qed.
Lemma lem7622313 {A B : Type'} (g : nat -> A) : term42 A B g.
Proof. exact (EQ_MP (@lem7618486 A B g) (@lem7622312 A B g)). Qed.
Lemma lem7622314 {A B : Type'} (g : nat -> A) : term41 A B g.
Proof. exact (EQ_MP (@lem7618477 A B g) (@lem7622313 A B g)). Qed.
