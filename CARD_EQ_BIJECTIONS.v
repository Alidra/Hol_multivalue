Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_BIJECTIONS_term_abbrevs.
Require Import CARD_EQ_BIJECTION_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LEFT_AND_EXISTS_THM_spec.
Require Import MONO_EXISTS_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Lemma lem5070397 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5070398 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5070399 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5070398 t1) (@lem5070397 t1)). Qed.
Lemma lem5070400 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5070399 t1 t2). Qed.
Lemma lem5070401 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5070402 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5070401 t1 t2) (@lem5070400 t1 t2)). Qed.
Lemma lem5070403 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5070402 t1 t2 t3). Qed.
Lemma lem5070404 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5070405 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5070404 t1 t2 t3) (@lem5070403 t1 t2 t3)). Qed.
Lemma lem5070406 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5070405 t1 t2 t3)). Qed.
Lemma lem5070407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070408 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term8 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070409 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5070407 A P Q h2 (@lem5070408 A P Q h1)). Qed.
Lemma lem5070410 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term10 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5070409 A P Q h1 h0). Qed.
Lemma lem5070411 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070412 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5070410 A P Q h1 (@lem5070411 A P Q h2)). Qed.
Lemma lem5070413 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term8 A P Q => @lem5070412 A P Q h0 h1). Qed.
Lemma lem5070414 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5070413 A P Q h0). Qed.
Lemma lem5070416 {A : Type'} (P : Prop) : term12 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem5070417 {A : Type'} (P : Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem5070418 {A : Type'} (P : Prop) : term13 A P.
Proof. exact (EQ_MP (@lem5070417 A P) (@lem5070416 A P)). Qed.
Lemma lem5070419 {A : Type'} (P : Prop) (Q : A -> Prop) : term14 A P Q.
Proof. exact (@lem5070418 A P Q). Qed.
Lemma lem5070420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term14 A P Q) = ((term15 A P Q) = (term16 A P Q)).
Proof. exact (eq_refl (term14 A P Q)). Qed.
Lemma lem5070422 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (@lem5881 A P). Qed.
Lemma lem5070423 {A : Type'} (P : A -> Prop) : (term17 A P) = (term18 A P).
Proof. exact (eq_refl (term17 A P)). Qed.
Lemma lem5070424 {A : Type'} (P : A -> Prop) : term18 A P.
Proof. exact (EQ_MP (@lem5070423 A P) (@lem5070422 A P)). Qed.
Lemma lem5070425 {A : Type'} (P : A -> Prop) (Q : Prop) : term19 A P Q.
Proof. exact (@lem5070424 A P Q). Qed.
Lemma lem5070426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term19 A P Q) = ((term20 A P Q) = (term21 A P Q)).
Proof. exact (eq_refl (term19 A P Q)). Qed.
Lemma lem5070428 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term22 _91307 _91308 s f.
Proof. exact (@lem3562737 _91307 _91308 s f). Qed.
Lemma lem5070429 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term22 _91307 _91308 s f) = (term23 _91307 _91308 s f).
Proof. exact (eq_refl (term22 _91307 _91308 s f)). Qed.
Lemma lem5070430 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term23 _91307 _91308 s f.
Proof. exact (EQ_MP (@lem5070429 _91307 _91308 s f) (@lem5070428 _91307 _91308 s f)). Qed.
Lemma lem5070431 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (t : _91308 -> Prop) : term24 _91307 _91308 s f t.
Proof. exact (@lem5070430 _91307 _91308 s f t). Qed.
Lemma lem5070432 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term24 _91307 _91308 s f t) = ((term25 _91307 _91308 t s f) = (term26 _91307 _91308 t s f)).
Proof. exact (eq_refl (term24 _91307 _91308 s f t)). Qed.
Lemma lem5070434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term8 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070436 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5070434 A P Q h2 (@lem5070435 A P Q h1)). Qed.
Lemma lem5070437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) : term10 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5070436 A P Q h1 h0). Qed.
Lemma lem5070438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (h1). Qed.
Lemma lem5070439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term8 A P Q) (h2 : term7 A P Q) : term9 A P Q.
Proof. exact (@lem5070437 A P Q h1 (@lem5070438 A P Q h2)). Qed.
Lemma lem5070440 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term7 A P Q) : term7 A P Q.
Proof. exact (fun h0 : term8 A P Q => @lem5070439 A P Q h0 h1). Qed.
Lemma lem5070441 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (fun h0 : term7 A P Q => @lem5070440 A P Q h0). Qed.
Lemma lem5070443 {A B : Type'} (s : A -> Prop) : term27 A B s.
Proof. exact (@lem5070396 A B s). Qed.
Lemma lem5070444 {A B : Type'} (s : A -> Prop) : (term27 A B s) = (term28 A B s).
Proof. exact (eq_refl (term27 A B s)). Qed.
Lemma lem5070445 {A B : Type'} (s : A -> Prop) : term28 A B s.
Proof. exact (EQ_MP (@lem5070444 A B s) (@lem5070443 A B s)). Qed.
Lemma lem5070446 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term29 A B s t.
Proof. exact (@lem5070445 A B s t). Qed.
Lemma lem5070447 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term29 A B s t) = (term30 A B t s).
Proof. exact (eq_refl (term29 A B s t)). Qed.
Lemma lem5070449 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term31 A B s t) : term31 A B s t.
Proof. exact (h1). Qed.
Lemma lem5070451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term30 A B t s.
Proof. exact (EQ_MP (@lem5070447 A B t s) (@lem5070446 A B s t)). Qed.
Lemma lem5070452 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term30 A B t s.
Proof. exact (@lem5070451 A B t s). Qed.
Lemma lem5070453 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term31 A B s t) : term32 A B t s.
Proof. exact (@lem5070452 A B t s (@lem5070449 A B s t h1)). Qed.
Lemma lem5070455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem5070441 A P Q (@lem7401 A P Q)). Qed.
Lemma lem5070456 {A B : Type'} (P : type572 A B) (Q : type572 A B) : term33 A B P Q.
Proof. exact (@lem5070455 (A -> B) P Q). Qed.
Lemma lem5070457 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term34 A B t s.
Proof. exact (@lem5070456 A B (term35 A B t s) (term36 A B t s)). Qed.
Lemma lem5070458 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term37 A B t s f) = (term38 A B t s f).
Proof. exact (eq_refl (term37 A B t s f)). Qed.
Lemma lem5070459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070460 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term39 A B t s f) = (term40 A B t s f).
Proof. exact (MK_COMB (@lem5070459) (@lem5070458 A B t s f)). Qed.
Lemma lem5070461 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term41 A B t s f) = (term42 A B t s f).
Proof. exact (eq_refl (term41 A B t s f)). Qed.
Lemma lem5070462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term43 A B t s f) = (term44 A B t s f).
Proof. exact (MK_COMB (@lem5070460 A B t s f) (@lem5070461 A B t s f)). Qed.
Lemma lem5070463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term45 A B t s) = (term46 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5070462 A B t s f)). Qed.
Lemma lem5070464 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5070465 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term47 A B t s) = (term48 A B t s).
Proof. exact (MK_COMB (@lem5070464 A B) (@lem5070463 A B t s)). Qed.
Lemma lem5070466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070467 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term49 A B t s) = (term50 A B t s).
Proof. exact (MK_COMB (@lem5070466) (@lem5070465 A B t s)). Qed.
Lemma lem5070468 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term37 A B t s f) = (term38 A B t s f).
Proof. exact (eq_refl (term37 A B t s f)). Qed.
Lemma lem5070469 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term51 A B t s) = (term35 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5070468 A B t s f)). Qed.
Lemma lem5070470 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5070471 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term52 A B t s) = (term32 A B t s).
Proof. exact (MK_COMB (@lem5070470 A B) (@lem5070469 A B t s)). Qed.
Lemma lem5070472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070473 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term53 A B t s) = (term54 A B t s).
Proof. exact (MK_COMB (@lem5070472) (@lem5070471 A B t s)). Qed.
Lemma lem5070474 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term41 A B t s f) = (term42 A B t s f).
Proof. exact (eq_refl (term41 A B t s f)). Qed.
Lemma lem5070475 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term55 A B t s) = (term36 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5070474 A B t s f)). Qed.
Lemma lem5070476 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5070477 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term56 A B t s) = (term57 A B t s).
Proof. exact (MK_COMB (@lem5070476 A B) (@lem5070475 A B t s)). Qed.
Lemma lem5070478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term58 A B t s) = (term59 A B t s).
Proof. exact (MK_COMB (@lem5070473 A B t s) (@lem5070477 A B t s)). Qed.
Lemma lem5070479 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term34 A B t s) = (term60 A B t s).
Proof. exact (MK_COMB (@lem5070467 A B t s) (@lem5070478 A B t s)). Qed.
Lemma lem5070480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term60 A B t s.
Proof. exact (EQ_MP (@lem5070479 A B t s) (@lem5070457 A B t s)). Qed.
Lemma lem5070498 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term25 _91307 _91308 t s f) = (term26 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem5070432 _91307 _91308 t s f) (@lem5070431 _91307 _91308 s f t)). Qed.
Lemma lem5070499 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term25 A B t s f) = (term26 A B t s f).
Proof. exact (@lem5070498 A B t s f). Qed.
Lemma lem5070514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070515 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term61 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem5070514) (@lem5070499 A B t s f)). Qed.
Lemma lem5070534 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term63 A B s f) = (term63 A B s f).
Proof. exact (eq_refl (term63 A B s f)). Qed.
Lemma lem5070535 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term64 A B t s f) = (term65 A B t s f).
Proof. exact (MK_COMB (@lem5070515 A B t s f) (@lem5070534 A B s f)). Qed.
Lemma lem5070538 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (eq_refl (term66 A B s f t)). Qed.
Lemma lem5070539 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term38 A B t s f) = (term67 A B t s f).
Proof. exact (MK_COMB (@lem5070538 A B s f t) (@lem5070535 A B t s f)). Qed.
Lemma lem5070542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070543 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term40 A B t s f) = (term68 A B t s f).
Proof. exact (MK_COMB (@lem5070542) (@lem5070539 A B t s f)). Qed.
Lemma lem5070570 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term42 A B t s f) = (term42 A B t s f).
Proof. exact (eq_refl (term42 A B t s f)). Qed.
Lemma lem5070571 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term44 A B t s f) = (term69 A B t s f).
Proof. exact (MK_COMB (@lem5070543 A B t s f) (@lem5070570 A B t s f)). Qed.
Lemma lem5070574 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term46 A B t s) = (term70 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5070571 A B t s f)). Qed.
Lemma lem5070575 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5070576 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term48 A B t s) = (term71 A B t s).
Proof. exact (MK_COMB (@lem5070575 A B) (@lem5070574 A B t s)). Qed.
Lemma lem5070581 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term71 A B t s) = (term48 A B t s).
Proof. exact (SYM (@lem5070576 A B t s)). Qed.
Lemma lem5070593 {A : Type'} (P : A -> Prop) (Q : Prop) : (term20 A P Q) = (term21 A P Q).
Proof. exact (EQ_MP (@lem5070426 A P Q) (@lem5070425 A P Q)). Qed.
Lemma lem5070594 {A B : Type'} (P : type805 A B) (Q : Prop) : (term72 A B P Q) = (term73 A B P Q).
Proof. exact (@lem5070593 (B -> A) P Q). Qed.
Lemma lem5070595 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term74 A B t s f) = (term75 A B t s f).
Proof. exact (@lem5070594 A B (term76 A B t s f) (term63 A B s f)). Qed.
Lemma lem5070596 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term77 A B t s f g) = (term78 A B t s f g).
Proof. exact (eq_refl (term77 A B t s f g)). Qed.
Lemma lem5070597 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term79 A B t s f) = (term76 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070596 A B t s f g)). Qed.
Lemma lem5070598 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070599 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term80 A B t s f) = (term26 A B t s f).
Proof. exact (MK_COMB (@lem5070598 A B) (@lem5070597 A B t s f)). Qed.
Lemma lem5070600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070601 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term81 A B t s f) = (term62 A B t s f).
Proof. exact (MK_COMB (@lem5070600) (@lem5070599 A B t s f)). Qed.
Lemma lem5070602 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term63 A B s f) = (term63 A B s f).
Proof. exact (eq_refl (term63 A B s f)). Qed.
Lemma lem5070603 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term74 A B t s f) = (term65 A B t s f).
Proof. exact (MK_COMB (@lem5070601 A B t s f) (@lem5070602 A B s f)). Qed.
Lemma lem5070604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5070605 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term82 A B t s f) = (term83 A B t s f).
Proof. exact (MK_COMB (@lem5070604) (@lem5070603 A B t s f)). Qed.
Lemma lem5070606 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term77 A B t s f g) = (term78 A B t s f g).
Proof. exact (eq_refl (term77 A B t s f g)). Qed.
Lemma lem5070607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070608 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term84 A B t s f g) = (term85 A B t s f g).
Proof. exact (MK_COMB (@lem5070607) (@lem5070606 A B t s f g)). Qed.
Lemma lem5070609 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term63 A B s f) = (term63 A B s f).
Proof. exact (eq_refl (term63 A B s f)). Qed.
Lemma lem5070610 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term86 A B t g s f) = (term87 A B t g s f).
Proof. exact (MK_COMB (@lem5070608 A B t s f g) (@lem5070609 A B s f)). Qed.
Lemma lem5070611 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term88 A B t s f) = (term89 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070610 A B t g s f)). Qed.
Lemma lem5070612 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070613 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term75 A B t s f) = (term90 A B t s f).
Proof. exact (MK_COMB (@lem5070612 A B) (@lem5070611 A B t s f)). Qed.
Lemma lem5070614 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term74 A B t s f) = (term75 A B t s f)) = ((term65 A B t s f) = (term90 A B t s f)).
Proof. exact (MK_COMB (@lem5070605 A B t s f) (@lem5070613 A B t s f)). Qed.
Lemma lem5070615 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term65 A B t s f) = (term90 A B t s f).
Proof. exact (EQ_MP (@lem5070614 A B t s f) (@lem5070595 A B t s f)). Qed.
Lemma lem5070650 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (eq_refl (term66 A B s f t)). Qed.
Lemma lem5070651 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term67 A B t s f) = (term91 A B t s f).
Proof. exact (MK_COMB (@lem5070650 A B s f t) (@lem5070615 A B t s f)). Qed.
Lemma lem5070653 {A : Type'} (P : Prop) (Q : A -> Prop) : (term15 A P Q) = (term16 A P Q).
Proof. exact (EQ_MP (@lem5070420 A P Q) (@lem5070419 A P Q)). Qed.
Lemma lem5070654 {A B : Type'} (P : Prop) (Q : type805 A B) : (term92 A B P Q) = (term93 A B P Q).
Proof. exact (@lem5070653 (B -> A) P Q). Qed.
Lemma lem5070655 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term94 A B t s f) = (term95 A B t s f).
Proof. exact (@lem5070654 A B (term96 A B s f t) (term89 A B t s f)). Qed.
Lemma lem5070656 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term97 A B t s f g) = (term87 A B t g s f).
Proof. exact (eq_refl (term97 A B t s f g)). Qed.
Lemma lem5070657 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term98 A B t s f) = (term89 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070656 A B t g s f)). Qed.
Lemma lem5070658 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070659 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term99 A B t s f) = (term90 A B t s f).
Proof. exact (MK_COMB (@lem5070658 A B) (@lem5070657 A B t s f)). Qed.
Lemma lem5070660 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (eq_refl (term66 A B s f t)). Qed.
Lemma lem5070661 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term94 A B t s f) = (term91 A B t s f).
Proof. exact (MK_COMB (@lem5070660 A B s f t) (@lem5070659 A B t s f)). Qed.
Lemma lem5070662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5070663 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term100 A B t s f) = (term101 A B t s f).
Proof. exact (MK_COMB (@lem5070662) (@lem5070661 A B t s f)). Qed.
Lemma lem5070664 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term97 A B t s f g) = (term87 A B t g s f).
Proof. exact (eq_refl (term97 A B t s f g)). Qed.
Lemma lem5070665 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (eq_refl (term66 A B s f t)). Qed.
Lemma lem5070666 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term102 A B t s f g) = (term103 A B t g s f).
Proof. exact (MK_COMB (@lem5070665 A B s f t) (@lem5070664 A B t g s f)). Qed.
Lemma lem5070667 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term104 A B t s f) = (term105 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070666 A B t g s f)). Qed.
Lemma lem5070668 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070669 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term95 A B t s f) = (term106 A B t s f).
Proof. exact (MK_COMB (@lem5070668 A B) (@lem5070667 A B t s f)). Qed.
Lemma lem5070670 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term94 A B t s f) = (term95 A B t s f)) = ((term91 A B t s f) = (term106 A B t s f)).
Proof. exact (MK_COMB (@lem5070663 A B t s f) (@lem5070669 A B t s f)). Qed.
Lemma lem5070671 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term91 A B t s f) = (term106 A B t s f).
Proof. exact (EQ_MP (@lem5070670 A B t s f) (@lem5070655 A B t s f)). Qed.
Lemma lem5070714 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term67 A B t s f) = (term106 A B t s f).
Proof. exact (TRANS (@lem5070651 A B t s f) (@lem5070671 A B t s f)). Qed.
Lemma lem5070715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070716 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term68 A B t s f) = (term107 A B t s f).
Proof. exact (MK_COMB (@lem5070715) (@lem5070714 A B t s f)). Qed.
Lemma lem5070743 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term42 A B t s f) = (term42 A B t s f).
Proof. exact (eq_refl (term42 A B t s f)). Qed.
Lemma lem5070744 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term69 A B t s f) = (term108 A B t s f).
Proof. exact (MK_COMB (@lem5070716 A B t s f) (@lem5070743 A B t s f)). Qed.
Lemma lem5070747 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term108 A B t s f) = (term69 A B t s f).
Proof. exact (SYM (@lem5070744 A B t s f)). Qed.
Lemma lem5070749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem5070414 A P Q (@lem7401 A P Q)). Qed.
Lemma lem5070750 {A B : Type'} (P : type805 A B) (Q : type805 A B) : term109 A B P Q.
Proof. exact (@lem5070749 (B -> A) P Q). Qed.
Lemma lem5070751 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term110 A B t s f.
Proof. exact (@lem5070750 A B (term105 A B t s f) (term111 A B t s f)). Qed.
Lemma lem5070752 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term112 A B t s f g) = (term103 A B t g s f).
Proof. exact (eq_refl (term112 A B t s f g)). Qed.
Lemma lem5070753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070754 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term113 A B t s f g) = (term114 A B t g s f).
Proof. exact (MK_COMB (@lem5070753) (@lem5070752 A B t g s f)). Qed.
Lemma lem5070755 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term115 A B t s f g) = (term116 A B t s f g).
Proof. exact (eq_refl (term115 A B t s f g)). Qed.
Lemma lem5070756 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term117 A B t s f g) = (term118 A B t s f g).
Proof. exact (MK_COMB (@lem5070754 A B t g s f) (@lem5070755 A B t s f g)). Qed.
Lemma lem5070757 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term119 A B t s f) = (term120 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070756 A B t s f g)). Qed.
Lemma lem5070758 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5070759 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term121 A B t s f) = (term122 A B t s f).
Proof. exact (MK_COMB (@lem5070758 A B) (@lem5070757 A B t s f)). Qed.
Lemma lem5070760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070761 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term123 A B t s f) = (term124 A B t s f).
Proof. exact (MK_COMB (@lem5070760) (@lem5070759 A B t s f)). Qed.
Lemma lem5070762 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term112 A B t s f g) = (term103 A B t g s f).
Proof. exact (eq_refl (term112 A B t s f g)). Qed.
Lemma lem5070763 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term125 A B t s f) = (term105 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070762 A B t g s f)). Qed.
Lemma lem5070764 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070765 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term126 A B t s f) = (term106 A B t s f).
Proof. exact (MK_COMB (@lem5070764 A B) (@lem5070763 A B t s f)). Qed.
Lemma lem5070766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070767 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term127 A B t s f) = (term107 A B t s f).
Proof. exact (MK_COMB (@lem5070766) (@lem5070765 A B t s f)). Qed.
Lemma lem5070768 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term115 A B t s f g) = (term116 A B t s f g).
Proof. exact (eq_refl (term115 A B t s f g)). Qed.
Lemma lem5070769 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term128 A B t s f) = (term111 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070768 A B t s f g)). Qed.
Lemma lem5070770 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5070771 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term129 A B t s f) = (term42 A B t s f).
Proof. exact (MK_COMB (@lem5070770 A B) (@lem5070769 A B t s f)). Qed.
Lemma lem5070772 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term130 A B t s f) = (term108 A B t s f).
Proof. exact (MK_COMB (@lem5070767 A B t s f) (@lem5070771 A B t s f)). Qed.
Lemma lem5070773 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term110 A B t s f) = (term131 A B t s f).
Proof. exact (MK_COMB (@lem5070761 A B t s f) (@lem5070772 A B t s f)). Qed.
Lemma lem5070774 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term131 A B t s f.
Proof. exact (EQ_MP (@lem5070773 A B t s f) (@lem5070751 A B t s f)). Qed.
Lemma lem5070776 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5070777 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term122 A B t s f) = (term133 A B t s f).
Proof. exact (@lem5070776 (term122 A B t s f)). Qed.
Lemma lem5070778 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term133 A B t s f) = (term122 A B t s f).
Proof. exact (SYM (@lem5070777 A B t s f)). Qed.
Lemma lem5070779 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term134 A B t s f) : term134 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5070782 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term133 A B t s f) : term133 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5070783 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term135 A B t s f.
Proof. exact (fun h0 : term133 A B t s f => @lem5070782 A B t s f h0). Qed.
Lemma lem5070784 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term135 A B t s f) : term135 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5070785 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term133 A B t s f) : term133 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5070786 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term133 A B t s f) (h2 : term135 A B t s f) : term133 A B t s f.
Proof. exact (@lem5070784 A B t s f h2 (@lem5070785 A B t s f h1)). Qed.
Lemma lem5070787 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term133 A B t s f) : term136 A B t s f.
Proof. exact (fun h0 : term135 A B t s f => @lem5070786 A B t s f h1 h0). Qed.
Lemma lem5070788 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term135 A B t s f) : term135 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5070789 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term133 A B t s f) (h2 : term135 A B t s f) : term133 A B t s f.
Proof. exact (@lem5070787 A B t s f h1 (@lem5070788 A B t s f h2)). Qed.
Lemma lem5070790 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term135 A B t s f) : term135 A B t s f.
Proof. exact (fun h0 : term133 A B t s f => @lem5070789 A B t s f h0 h1). Qed.
Lemma lem5070791 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term137 A B t s f.
Proof. exact (fun h0 : term135 A B t s f => @lem5070790 A B t s f h0). Qed.
Lemma lem5070794 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term135 A B t s f.
Proof. exact (@lem5070791 A B t s f (@lem5070783 A B t s f)). Qed.
Lemma lem5070795 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term135 A B t s f.
Proof. exact (@lem5070794 A B t s f). Qed.
Lemma lem5070809 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5070810 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term133 A B t s f) = (term138 A B t s f).
Proof. exact (@lem5070809 (term134 A B t s f)). Qed.
Lemma lem5070812 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5070813 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term138 A B t s f) = (term122 A B t s f).
Proof. exact (@lem5070812 (term122 A B t s f)). Qed.
Lemma lem5070818 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term133 A B t s f) = (term122 A B t s f).
Proof. exact (TRANS (@lem5070810 A B t s f) (@lem5070813 A B t s f)). Qed.
Lemma lem5070871 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term140 A B s f) = (term141 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5070818 A B t s f)). Qed.
Lemma lem5070872 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5070873 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term142 A B s f) = (term143 A B s f).
Proof. exact (MK_COMB (@lem5070872 B) (@lem5070871 A B s f)). Qed.
Lemma lem5070878 {A B : Type'} (f : A -> B) : (term144 A B f) = (term145 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5070873 A B s f)). Qed.
Lemma lem5070879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5070880 {A B : Type'} (f : A -> B) : (term146 A B f) = (term147 A B f).
Proof. exact (MK_COMB (@lem5070879 A) (@lem5070878 A B f)). Qed.
Lemma lem5070885 {A B : Type'} : (term148 A B) = (term149 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5070880 A B f)). Qed.
Lemma lem5070886 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5070895 {A B : Type'} : (term150 A B) = (term151 A B).
Proof. exact (MK_COMB (@lem5070886 A B) (@lem5070885 A B)). Qed.
Lemma lem5070904 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term152 A B t s f g y) = (term152 A B t s f g y).
Proof. exact (eq_refl (term152 A B t s f g y)). Qed.
Lemma lem5070905 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term153 A B t s f g) = (term153 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5070904 A B t s f g y)). Qed.
Lemma lem5070906 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5070907 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term78 A B t s f g).
Proof. exact (MK_COMB (@lem5070906 B) (@lem5070905 A B t s f g)). Qed.
Lemma lem5070916 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term154 A B s t g f x) = (term154 A B s t g f x).
Proof. exact (eq_refl (term154 A B s t g f x)). Qed.
Lemma lem5070917 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term155 A B s t g f) = (term155 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5070916 A B s t g f x)). Qed.
Lemma lem5070918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5070919 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term156 A B s t g f) = (term156 A B s t g f).
Proof. exact (MK_COMB (@lem5070918 A) (@lem5070917 A B s t g f)). Qed.
Lemma lem5070920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070921 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term157 A B s t g f) = (term157 A B s t g f).
Proof. exact (MK_COMB (@lem5070920) (@lem5070919 A B s t g f)). Qed.
Lemma lem5070922 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term116 A B t s f g) = (term116 A B t s f g).
Proof. exact (MK_COMB (@lem5070921 A B s t g f) (@lem5070907 A B t s f g)). Qed.
Lemma lem5070935 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term158 A B s f x y) = (term158 A B s f x y).
Proof. exact (eq_refl (term158 A B s f x y)). Qed.
Lemma lem5070936 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term159 A B s f x) = (term159 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5070935 A B s f x y)). Qed.
Lemma lem5070937 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5070938 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term160 A B s f x) = (term160 A B s f x).
Proof. exact (MK_COMB (@lem5070937 A) (@lem5070936 A B s f x)). Qed.
Lemma lem5070939 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term161 A B s f) = (term161 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5070938 A B s f x)). Qed.
Lemma lem5070940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5070941 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term63 A B s f) = (term63 A B s f).
Proof. exact (MK_COMB (@lem5070940 A) (@lem5070939 A B s f)). Qed.
Lemma lem5070950 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term152 A B t s f g y) = (term152 A B t s f g y).
Proof. exact (eq_refl (term152 A B t s f g y)). Qed.
Lemma lem5070951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term153 A B t s f g) = (term153 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5070950 A B t s f g y)). Qed.
Lemma lem5070952 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5070953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term78 A B t s f g).
Proof. exact (MK_COMB (@lem5070952 B) (@lem5070951 A B t s f g)). Qed.
Lemma lem5070954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070955 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term85 A B t s f g) = (term85 A B t s f g).
Proof. exact (MK_COMB (@lem5070954) (@lem5070953 A B t s f g)). Qed.
Lemma lem5070956 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term87 A B t g s f) = (term87 A B t g s f).
Proof. exact (MK_COMB (@lem5070955 A B t s f g) (@lem5070941 A B s f)). Qed.
Lemma lem5070961 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term162 A B s f x t) = (term162 A B s f x t).
Proof. exact (eq_refl (term162 A B s f x t)). Qed.
Lemma lem5070962 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term163 A B s f t) = (term163 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5070961 A B s f x t)). Qed.
Lemma lem5070963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5070964 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term96 A B s f t) = (term96 A B s f t).
Proof. exact (MK_COMB (@lem5070963 A) (@lem5070962 A B s f t)). Qed.
Lemma lem5070965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5070966 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term66 A B s f t).
Proof. exact (MK_COMB (@lem5070965) (@lem5070964 A B s f t)). Qed.
Lemma lem5070967 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term103 A B t g s f) = (term103 A B t g s f).
Proof. exact (MK_COMB (@lem5070966 A B s f t) (@lem5070956 A B t g s f)). Qed.
Lemma lem5070968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5070969 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term114 A B t g s f) = (term114 A B t g s f).
Proof. exact (MK_COMB (@lem5070968) (@lem5070967 A B t g s f)). Qed.
Lemma lem5070970 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term118 A B t s f g).
Proof. exact (MK_COMB (@lem5070969 A B t g s f) (@lem5070922 A B t s f g)). Qed.
Lemma lem5070971 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term120 A B t s f) = (term120 A B t s f).
Proof. exact (fun_ext (fun g : B -> A => @lem5070970 A B t s f g)). Qed.
Lemma lem5070972 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5070973 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term122 A B t s f) = (term122 A B t s f).
Proof. exact (MK_COMB (@lem5070972 A B) (@lem5070971 A B t s f)). Qed.
Lemma lem5070974 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term141 A B s f) = (term141 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5070973 A B t s f)). Qed.
Lemma lem5070975 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5070976 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term143 A B s f) = (term143 A B s f).
Proof. exact (MK_COMB (@lem5070975 B) (@lem5070974 A B s f)). Qed.
Lemma lem5070977 {A B : Type'} (f : A -> B) : (term145 A B f) = (term145 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5070976 A B s f)). Qed.
Lemma lem5070978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5070979 {A B : Type'} (f : A -> B) : (term147 A B f) = (term147 A B f).
Proof. exact (MK_COMB (@lem5070978 A) (@lem5070977 A B f)). Qed.
Lemma lem5070980 {A B : Type'} : (term149 A B) = (term149 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5070979 A B f)). Qed.
Lemma lem5070981 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5070982 {A B : Type'} : (term151 A B) = (term151 A B).
Proof. exact (MK_COMB (@lem5070981 A B) (@lem5070980 A B)). Qed.
Lemma lem5071073 {A B : Type'} : (term150 A B) = (term151 A B).
Proof. exact (TRANS (@lem5070895 A B) (@lem5070982 A B)). Qed.
Lemma lem5071074 {A B : Type'} : (term151 A B) = (term150 A B).
Proof. exact (SYM (@lem5071073 A B)). Qed.
Lemma lem5071075 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term103 A B t g s f.
Proof. exact (h1). Qed.
Lemma lem5071077 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5071078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term116 A B t s f g) = (term164 A B t s f g).
Proof. exact (@lem5071077 (term116 A B t s f g)). Qed.
Lemma lem5071079 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term164 A B t s f g) = (term116 A B t s f g).
Proof. exact (SYM (@lem5071078 A B t s f g)). Qed.
Lemma lem5071080 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term165 A B t s f g) : term165 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5071087 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term162 A B s f x t) = (term166 A B s f x t).
Proof. exact (@lem17265 (@IN A x s) (term167 A B f x t)). Qed.
Lemma lem5071088 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term163 A B s f t) = (term168 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5071087 A B s f x t)). Qed.
Lemma lem5071089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071090 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term96 A B s f t) = (term169 A B s f t).
Proof. exact (MK_COMB (@lem5071089 A) (@lem5071088 A B s f t)). Qed.
Lemma lem5071101 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term152 A B t s f g y) = (term170 A B t s f g y).
Proof. exact (@lem17265 (@IN B y t) (term171 A B s f g y)). Qed.
Lemma lem5071102 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term153 A B t s f g) = (term172 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5071101 A B t s f g y)). Qed.
Lemma lem5071103 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5071104 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term173 A B t s f g).
Proof. exact (MK_COMB (@lem5071103 B) (@lem5071102 A B t s f g)). Qed.
Lemma lem5071112 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term174 A B s x f y) = (term175 A B s x f y).
Proof. exact (@lem17045 (@IN A y s) ((f x) = (f y))). Qed.
Lemma lem5071114 {A : Type'} (x : A) (s : A -> Prop) : (term176 A x s) = (term176 A x s).
Proof. exact (eq_refl (term176 A x s)). Qed.
Lemma lem5071115 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term177 A B s x f y) = (term178 A B s x f y).
Proof. exact (MK_COMB (@lem5071114 A x s) (@lem5071112 A B s x f y)). Qed.
Lemma lem5071116 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term179 A B s x f y) = (term177 A B s x f y).
Proof. exact (@lem17045 (@IN A x s) (term180 A B s x f y)). Qed.
Lemma lem5071117 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term179 A B s x f y) = (term178 A B s x f y).
Proof. exact (TRANS (@lem5071116 A B s x f y) (@lem5071115 A B s x f y)). Qed.
Lemma lem5071118 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5071119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5071120 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term181 A B s x f y) = (term182 A B s x f y).
Proof. exact (MK_COMB (@lem5071119) (@lem5071117 A B s x f y)). Qed.
Lemma lem5071121 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term183 A B s f x y) = (term184 A B s f x y).
Proof. exact (MK_COMB (@lem5071120 A B s x f y) (@lem5071118 A x y)). Qed.
Lemma lem5071122 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term158 A B s f x y) = (term183 A B s f x y).
Proof. exact (@lem17265 (term185 A B s x f y) (x = y)). Qed.
Lemma lem5071123 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term158 A B s f x y) = (term184 A B s f x y).
Proof. exact (TRANS (@lem5071122 A B s f x y) (@lem5071121 A B s f x y)). Qed.
Lemma lem5071124 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term159 A B s f x) = (term186 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5071123 A B s f x y)). Qed.
Lemma lem5071125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071126 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term160 A B s f x) = (term187 A B s f x).
Proof. exact (MK_COMB (@lem5071125 A) (@lem5071124 A B s f x)). Qed.
Lemma lem5071127 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term161 A B s f) = (term188 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5071126 A B s f x)). Qed.
Lemma lem5071128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071129 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term63 A B s f) = (term189 A B s f).
Proof. exact (MK_COMB (@lem5071128 A) (@lem5071127 A B s f)). Qed.
Lemma lem5071130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5071131 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term85 A B t s f g) = (term190 A B t s f g).
Proof. exact (MK_COMB (@lem5071130) (@lem5071104 A B t s f g)). Qed.
Lemma lem5071132 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term87 A B t g s f) = (term191 A B t g s f).
Proof. exact (MK_COMB (@lem5071131 A B t s f g) (@lem5071129 A B s f)). Qed.
Lemma lem5071133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5071134 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term66 A B s f t) = (term192 A B s f t).
Proof. exact (MK_COMB (@lem5071133) (@lem5071090 A B s f t)). Qed.
Lemma lem5071287 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term103 A B t g s f) = (term193 A B t g s f).
Proof. exact (MK_COMB (@lem5071134 A B s f t) (@lem5071132 A B t g s f)). Qed.
Lemma lem5071288 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term193 A B t g s f.
Proof. exact (EQ_MP (@lem5071287 A B t g s f) (@lem5071075 A B t g s f h1)). Qed.
Lemma lem5071296 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term194 A B t g f x) = (term195 A B t g f x).
Proof. exact (@lem17045 (term167 A B f x t) ((term196 A B g f x) = x)). Qed.
Lemma lem5071298 {A : Type'} (x : A) (s : A -> Prop) : (term197 A x s) = (term197 A x s).
Proof. exact (eq_refl (term197 A x s)). Qed.
Lemma lem5071299 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term198 A B s t g f x) = (term199 A B s t g f x).
Proof. exact (MK_COMB (@lem5071298 A x s) (@lem5071296 A B t g f x)). Qed.
Lemma lem5071300 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term200 A B s t g f x) = (term198 A B s t g f x).
Proof. exact (@lem17362 (@IN A x s) (term201 A B t g f x)). Qed.
Lemma lem5071301 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term200 A B s t g f x) = (term199 A B s t g f x).
Proof. exact (TRANS (@lem5071300 A B s t g f x) (@lem5071299 A B s t g f x)). Qed.
Lemma lem5071302 {A : Type'} (P : A -> Prop) : (term202 A P) = (term203 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5071303 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term204 A B s t g f) = (term205 A B s t g f).
Proof. exact (@lem5071302 A (term155 A B s t g f)). Qed.
Lemma lem5071304 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term206 A B s t g f x) = (term154 A B s t g f x).
Proof. exact (eq_refl (term206 A B s t g f x)). Qed.
Lemma lem5071305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5071306 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term207 A B s t g f x) = (term200 A B s t g f x).
Proof. exact (MK_COMB (@lem5071305) (@lem5071304 A B s t g f x)). Qed.
Lemma lem5071307 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term207 A B s t g f x) = (term199 A B s t g f x).
Proof. exact (TRANS (@lem5071306 A B s t g f x) (@lem5071301 A B s t g f x)). Qed.
Lemma lem5071308 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term208 A B s t g f) = (term209 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5071307 A B s t g f x)). Qed.
Lemma lem5071309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5071310 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term205 A B s t g f) = (term210 A B s t g f).
Proof. exact (MK_COMB (@lem5071309 A) (@lem5071308 A B s t g f)). Qed.
Lemma lem5071311 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term204 A B s t g f) = (term210 A B s t g f).
Proof. exact (TRANS (@lem5071303 A B s t g f) (@lem5071310 A B s t g f)). Qed.
Lemma lem5071319 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term211 A B s f g y) = (term212 A B s f g y).
Proof. exact (@lem17045 (term213 A B g y s) ((term214 A B f g y) = y)). Qed.
Lemma lem5071321 {B : Type'} (y : B) (t : B -> Prop) : (term197 B y t) = (term197 B y t).
Proof. exact (eq_refl (term197 B y t)). Qed.
Lemma lem5071322 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term215 A B t s f g y) = (term216 A B t s f g y).
Proof. exact (MK_COMB (@lem5071321 B y t) (@lem5071319 A B s f g y)). Qed.
Lemma lem5071323 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term217 A B t s f g y) = (term215 A B t s f g y).
Proof. exact (@lem17362 (@IN B y t) (term171 A B s f g y)). Qed.
Lemma lem5071324 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term217 A B t s f g y) = (term216 A B t s f g y).
Proof. exact (TRANS (@lem5071323 A B t s f g y) (@lem5071322 A B t s f g y)). Qed.
Lemma lem5071325 {B : Type'} (P : B -> Prop) : (term202 B P) = (term203 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5071326 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term218 A B t s f g) = (term219 A B t s f g).
Proof. exact (@lem5071325 B (term153 A B t s f g)). Qed.
Lemma lem5071327 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term220 A B t s f g y) = (term152 A B t s f g y).
Proof. exact (eq_refl (term220 A B t s f g y)). Qed.
Lemma lem5071328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5071329 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term221 A B t s f g y) = (term217 A B t s f g y).
Proof. exact (MK_COMB (@lem5071328) (@lem5071327 A B t s f g y)). Qed.
Lemma lem5071330 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term221 A B t s f g y) = (term216 A B t s f g y).
Proof. exact (TRANS (@lem5071329 A B t s f g y) (@lem5071324 A B t s f g y)). Qed.
Lemma lem5071331 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term222 A B t s f g) = (term223 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5071330 A B t s f g y)). Qed.
Lemma lem5071332 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5071333 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term219 A B t s f g) = (term224 A B t s f g).
Proof. exact (MK_COMB (@lem5071332 B) (@lem5071331 A B t s f g)). Qed.
Lemma lem5071334 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term218 A B t s f g) = (term224 A B t s f g).
Proof. exact (TRANS (@lem5071326 A B t s f g) (@lem5071333 A B t s f g)). Qed.
Lemma lem5071335 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5071336 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term225 A B s t g f) = (term226 A B s t g f).
Proof. exact (MK_COMB (@lem5071335) (@lem5071311 A B s t g f)). Qed.
Lemma lem5071337 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term227 A B t s f g) = (term228 A B t s f g).
Proof. exact (MK_COMB (@lem5071336 A B s t g f) (@lem5071334 A B t s f g)). Qed.
Lemma lem5071338 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term165 A B t s f g) = (term227 A B t s f g).
Proof. exact (@lem17045 (term156 A B s t g f) (term78 A B t s f g)). Qed.
Lemma lem5071339 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term165 A B t s f g) = (term228 A B t s f g).
Proof. exact (TRANS (@lem5071338 A B t s f g) (@lem5071337 A B t s f g)). Qed.
Lemma lem5071440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5071441 {A : Type'} (P : A -> Prop) (Q : Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (@lem5071440 A P Q). Qed.
Lemma lem5071442 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term231 A B t s f g) = (term232 A B t s f g).
Proof. exact (@lem5071441 A (term209 A B s t g f) (term224 A B t s f g)). Qed.
Lemma lem5071443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term233 A B s t g f x) = (term199 A B s t g f x).
Proof. exact (eq_refl (term233 A B s t g f x)). Qed.
Lemma lem5071444 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term234 A B s t g f) = (term209 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5071443 A B s t g f x)). Qed.
Lemma lem5071445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5071446 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term235 A B s t g f) = (term210 A B s t g f).
Proof. exact (MK_COMB (@lem5071445 A) (@lem5071444 A B s t g f)). Qed.
Lemma lem5071447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5071448 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term236 A B s t g f) = (term226 A B s t g f).
Proof. exact (MK_COMB (@lem5071447) (@lem5071446 A B s t g f)). Qed.
Lemma lem5071449 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term224 A B t s f g) = (term224 A B t s f g).
Proof. exact (eq_refl (term224 A B t s f g)). Qed.
Lemma lem5071450 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term231 A B t s f g) = (term228 A B t s f g).
Proof. exact (MK_COMB (@lem5071448 A B s t g f) (@lem5071449 A B t s f g)). Qed.
Lemma lem5071451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5071452 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term237 A B t s f g) = (term238 A B t s f g).
Proof. exact (MK_COMB (@lem5071451) (@lem5071450 A B t s f g)). Qed.
Lemma lem5071453 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term233 A B s t g f x) = (term199 A B s t g f x).
Proof. exact (eq_refl (term233 A B s t g f x)). Qed.
Lemma lem5071454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5071455 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term239 A B s t g f x) = (term240 A B s t g f x).
Proof. exact (MK_COMB (@lem5071454) (@lem5071453 A B s t g f x)). Qed.
Lemma lem5071456 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term224 A B t s f g) = (term224 A B t s f g).
Proof. exact (eq_refl (term224 A B t s f g)). Qed.
Lemma lem5071457 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term241 A B x t s f g) = (term242 A B x t s f g).
Proof. exact (MK_COMB (@lem5071455 A B s t g f x) (@lem5071456 A B t s f g)). Qed.
Lemma lem5071458 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term243 A B t s f g) = (term244 A B t s f g).
Proof. exact (fun_ext (fun x : A => @lem5071457 A B x t s f g)). Qed.
Lemma lem5071459 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5071460 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term232 A B t s f g) = (term245 A B t s f g).
Proof. exact (MK_COMB (@lem5071459 A) (@lem5071458 A B t s f g)). Qed.
Lemma lem5071461 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term231 A B t s f g) = (term232 A B t s f g)) = ((term228 A B t s f g) = (term245 A B t s f g)).
Proof. exact (MK_COMB (@lem5071452 A B t s f g) (@lem5071460 A B t s f g)). Qed.
Lemma lem5071462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term228 A B t s f g) = (term245 A B t s f g).
Proof. exact (EQ_MP (@lem5071461 A B t s f g) (@lem5071442 A B t s f g)). Qed.
Lemma lem5071464 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5071465 {B : Type'} (P : Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem5071464 B P Q). Qed.
Lemma lem5071466 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term248 A B x t s f g) = (term249 A B x t s f g).
Proof. exact (@lem5071465 B (term199 A B s t g f x) (term223 A B t s f g)). Qed.
Lemma lem5071467 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term250 A B t s f g y) = (term216 A B t s f g y).
Proof. exact (eq_refl (term250 A B t s f g y)). Qed.
Lemma lem5071468 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term251 A B t s f g) = (term223 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5071467 A B t s f g y)). Qed.
Lemma lem5071469 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5071470 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term252 A B t s f g) = (term224 A B t s f g).
Proof. exact (MK_COMB (@lem5071469 B) (@lem5071468 A B t s f g)). Qed.
Lemma lem5071471 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term240 A B s t g f x) = (term240 A B s t g f x).
Proof. exact (eq_refl (term240 A B s t g f x)). Qed.
Lemma lem5071472 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term248 A B x t s f g) = (term242 A B x t s f g).
Proof. exact (MK_COMB (@lem5071471 A B s t g f x) (@lem5071470 A B t s f g)). Qed.
Lemma lem5071473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5071474 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term253 A B x t s f g) = (term254 A B x t s f g).
Proof. exact (MK_COMB (@lem5071473) (@lem5071472 A B x t s f g)). Qed.
Lemma lem5071475 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term250 A B t s f g y) = (term216 A B t s f g y).
Proof. exact (eq_refl (term250 A B t s f g y)). Qed.
Lemma lem5071476 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term240 A B s t g f x) = (term240 A B s t g f x).
Proof. exact (eq_refl (term240 A B s t g f x)). Qed.
Lemma lem5071477 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term255 A B x t s f g y) = (term256 A B x t s f g y).
Proof. exact (MK_COMB (@lem5071476 A B s t g f x) (@lem5071475 A B t s f g y)). Qed.
Lemma lem5071478 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term257 A B x t s f g) = (term258 A B x t s f g).
Proof. exact (fun_ext (fun y : B => @lem5071477 A B x t s f g y)). Qed.
Lemma lem5071479 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5071480 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term249 A B x t s f g) = (term259 A B x t s f g).
Proof. exact (MK_COMB (@lem5071479 B) (@lem5071478 A B x t s f g)). Qed.
Lemma lem5071481 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term248 A B x t s f g) = (term249 A B x t s f g)) = ((term242 A B x t s f g) = (term259 A B x t s f g)).
Proof. exact (MK_COMB (@lem5071474 A B x t s f g) (@lem5071480 A B x t s f g)). Qed.
Lemma lem5071482 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term242 A B x t s f g) = (term259 A B x t s f g).
Proof. exact (EQ_MP (@lem5071481 A B x t s f g) (@lem5071466 A B x t s f g)). Qed.
Lemma lem5071483 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term244 A B t s f g) = (term260 A B t s f g).
Proof. exact (fun_ext (fun x : A => @lem5071482 A B x t s f g)). Qed.
Lemma lem5071484 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5071485 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term245 A B t s f g) = (term261 A B t s f g).
Proof. exact (MK_COMB (@lem5071484 A) (@lem5071483 A B t s f g)). Qed.
Lemma lem5071487 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term228 A B t s f g) = (term261 A B t s f g).
Proof. exact (TRANS (@lem5071462 A B t s f g) (@lem5071485 A B t s f g)). Qed.
Lemma lem5071488 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term165 A B t s f g) = (term261 A B t s f g).
Proof. exact (TRANS (@lem5071339 A B t s f g) (@lem5071487 A B t s f g)). Qed.
Lemma lem5071489 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term165 A B t s f g) : term261 A B t s f g.
Proof. exact (EQ_MP (@lem5071488 A B t s f g) (@lem5071080 A B t s f g h1)). Qed.
Lemma lem5071490 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term259 A B x t s f g) : term259 A B x t s f g.
Proof. exact (h1). Qed.
Lemma lem5071530 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term184 A B s f x y) = (term184 A B s f x y).
Proof. exact (eq_refl (term184 A B s f x y)). Qed.
Lemma lem5071531 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term186 A B s f x) = (term186 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5071530 A B s f x y)). Qed.
Lemma lem5071532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071533 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B s f x) = (term187 A B s f x).
Proof. exact (MK_COMB (@lem5071532 A) (@lem5071531 A B s f x)). Qed.
Lemma lem5071534 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term188 A B s f) = (term188 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5071533 A B s f x)). Qed.
Lemma lem5071535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071536 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term189 A B s f) = (term189 A B s f).
Proof. exact (MK_COMB (@lem5071535 A) (@lem5071534 A B s f)). Qed.
Lemma lem5071565 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term170 A B t s f g y) = (term170 A B t s f g y).
Proof. exact (eq_refl (term170 A B t s f g y)). Qed.
Lemma lem5071566 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term172 A B t s f g) = (term172 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5071565 A B t s f g y)). Qed.
Lemma lem5071567 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5071568 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term173 A B t s f g) = (term173 A B t s f g).
Proof. exact (MK_COMB (@lem5071567 B) (@lem5071566 A B t s f g)). Qed.
Lemma lem5071569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5071570 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term190 A B t s f g) = (term190 A B t s f g).
Proof. exact (MK_COMB (@lem5071569) (@lem5071568 A B t s f g)). Qed.
Lemma lem5071571 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term191 A B t g s f) = (term191 A B t g s f).
Proof. exact (MK_COMB (@lem5071570 A B t s f g) (@lem5071536 A B s f)). Qed.
Lemma lem5071588 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term166 A B s f x t) = (term166 A B s f x t).
Proof. exact (eq_refl (term166 A B s f x t)). Qed.
Lemma lem5071589 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term168 A B s f t) = (term168 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5071588 A B s f x t)). Qed.
Lemma lem5071590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071591 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term169 A B s f t) = (term169 A B s f t).
Proof. exact (MK_COMB (@lem5071590 A) (@lem5071589 A B s f t)). Qed.
Lemma lem5071592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5071593 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term192 A B s f t) = (term192 A B s f t).
Proof. exact (MK_COMB (@lem5071592) (@lem5071591 A B s f t)). Qed.
Lemma lem5071594 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term193 A B t g s f) = (term193 A B t g s f).
Proof. exact (MK_COMB (@lem5071593 A B s f t) (@lem5071571 A B t g s f)). Qed.
Lemma lem5071595 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term193 A B t g s f.
Proof. exact (EQ_MP (@lem5071594 A B t g s f) (@lem5071288 A B t g s f h1)). Qed.
Lemma lem5071661 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term256 A B x t s f g y) : term256 A B x t s f g y.
Proof. exact (h1). Qed.
Lemma lem5071662 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term191 A B t g s f.
Proof. exact (proj2 (@lem5071595 A B t g s f h1)). Qed.
Lemma lem5071663 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term169 A B s f t.
Proof. exact (proj1 (@lem5071595 A B t g s f h1)). Qed.
Lemma lem5071664 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term189 A B s f.
Proof. exact (proj2 (@lem5071662 A B t g s f h1)). Qed.
Lemma lem5071665 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term173 A B t s f g.
Proof. exact (proj1 (@lem5071662 A B t g s f h1)). Qed.
Lemma lem5071666 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term199 A B s t g f x.
Proof. exact (h1). Qed.
Lemma lem5071667 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : term216 A B t s f g y.
Proof. exact (h1). Qed.
Lemma lem5071668 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term195 A B t g f x.
Proof. exact (proj2 (@lem5071666 A B s t g f x h1)). Qed.
Lemma lem5071672 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : term212 A B s f g y.
Proof. exact (proj2 (@lem5071667 A B t s f g y h1)). Qed.
Lemma lem5071683 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term166 A B s f x t) = (term166 A B s f x t).
Proof. exact (eq_refl (term166 A B s f x t)). Qed.
Lemma lem5071684 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term168 A B s f t) = (term168 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5071683 A B s f x t)). Qed.
Lemma lem5071685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071687 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term169 A B s f t) = (term169 A B s f t).
Proof. exact (MK_COMB (@lem5071685 A) (@lem5071684 A B s f t)). Qed.
Lemma lem5071688 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term169 A B s f t.
Proof. exact (EQ_MP (@lem5071687 A B s f t) (@lem5071663 A B t g s f h1)). Qed.
Lemma lem5071747 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term262 A B f x t) : term262 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5071755 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term166 A B s f x t) = (term166 A B s f x t).
Proof. exact (eq_refl (term166 A B s f x t)). Qed.
Lemma lem5071756 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term168 A B s f t) = (term168 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem5071755 A B s f x t)). Qed.
Lemma lem5071757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071759 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term169 A B s f t) = (term169 A B s f t).
Proof. exact (MK_COMB (@lem5071757 A) (@lem5071756 A B s f t)). Qed.
Lemma lem5071760 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term169 A B s f t.
Proof. exact (EQ_MP (@lem5071759 A B s f t) (@lem5071663 A B t g s f h1)). Qed.
Lemma lem5071778 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term170 A B t s f g y) = (term263 A B s t f g y).
Proof. exact (@lem19490 (term213 A B g y s) (term264 B y t) ((term214 A B f g y) = y)). Qed.
Lemma lem5071779 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term172 A B t s f g) = (term265 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5071778 A B s t f g y)). Qed.
Lemma lem5071780 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5071782 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term173 A B t s f g) = (term266 A B s t f g).
Proof. exact (MK_COMB (@lem5071780 B) (@lem5071779 A B s t f g)). Qed.
Lemma lem5071783 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term266 A B s t f g.
Proof. exact (EQ_MP (@lem5071782 A B s t f g) (@lem5071665 A B t g s f h1)). Qed.
Lemma lem5071803 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term184 A B s f x y) = (term184 A B s f x y).
Proof. exact (eq_refl (term184 A B s f x y)). Qed.
Lemma lem5071804 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term186 A B s f x) = (term186 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5071803 A B s f x y)). Qed.
Lemma lem5071805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071806 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B s f x) = (term187 A B s f x).
Proof. exact (MK_COMB (@lem5071805 A) (@lem5071804 A B s f x)). Qed.
Lemma lem5071807 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term188 A B s f) = (term188 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5071806 A B s f x)). Qed.
Lemma lem5071808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5071810 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term189 A B s f) = (term189 A B s f).
Proof. exact (MK_COMB (@lem5071808 A) (@lem5071807 A B s f)). Qed.
Lemma lem5071811 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term189 A B s f.
Proof. exact (EQ_MP (@lem5071810 A B s f) (@lem5071664 A B t g s f h1)). Qed.
Lemma lem5071819 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) : term267 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5071850 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term170 A B t s f g y) = (term263 A B s t f g y).
Proof. exact (@lem19490 (term213 A B g y s) (term264 B y t) ((term214 A B f g y) = y)). Qed.
Lemma lem5071851 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term172 A B t s f g) = (term265 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5071850 A B s t f g y)). Qed.
Lemma lem5071852 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5071854 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term173 A B t s f g) = (term266 A B s t f g).
Proof. exact (MK_COMB (@lem5071852 B) (@lem5071851 A B s t f g)). Qed.
Lemma lem5071855 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term266 A B s t f g.
Proof. exact (EQ_MP (@lem5071854 A B s t f g) (@lem5071665 A B t g s f h1)). Qed.
Lemma lem5071891 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term268 A B g y s) : term268 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5071922 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term170 A B t s f g y) = (term263 A B s t f g y).
Proof. exact (@lem19490 (term213 A B g y s) (term264 B y t) ((term214 A B f g y) = y)). Qed.
Lemma lem5071923 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term172 A B t s f g) = (term265 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5071922 A B s t f g y)). Qed.
Lemma lem5071924 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5071926 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term173 A B t s f g) = (term266 A B s t f g).
Proof. exact (MK_COMB (@lem5071924 B) (@lem5071923 A B s t f g)). Qed.
Lemma lem5071927 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term266 A B s t f g.
Proof. exact (EQ_MP (@lem5071926 A B s t f g) (@lem5071665 A B t g s f h1)). Qed.
Lemma lem5071963 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) : term269 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5071964 {A B : Type'} (_65290 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term270 A B s f t _65290.
Proof. exact (@lem5071688 A B t g s f h1 _65290). Qed.
Lemma lem5071965 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65290 : A) (t : B -> Prop) : (term270 A B s f t _65290) = (term166 A B s f _65290 t).
Proof. exact (eq_refl (term270 A B s f t _65290)). Qed.
Lemma lem5071976 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term270 A B s f t _65294.
Proof. exact (@lem5071760 A B t g s f h1 _65294). Qed.
Lemma lem5071977 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65294 : A) (t : B -> Prop) : (term270 A B s f t _65294) = (term166 A B s f _65294 t).
Proof. exact (eq_refl (term270 A B s f t _65294)). Qed.
Lemma lem5071979 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term271 A B s t f g _65295.
Proof. exact (@lem5071783 A B t g s f h1 _65295). Qed.
Lemma lem5071980 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_65295 : B) : (term271 A B s t f g _65295) = (term263 A B s t f g _65295).
Proof. exact (eq_refl (term271 A B s t f g _65295)). Qed.
Lemma lem5071981 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term263 A B s t f g _65295.
Proof. exact (EQ_MP (@lem5071980 A B s t f g _65295) (@lem5071979 A B _65295 t g s f h1)). Qed.
Lemma lem5071982 {A B : Type'} (_65296 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term272 A B s f _65296.
Proof. exact (@lem5071811 A B t g s f h1 _65296). Qed.
Lemma lem5071983 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) : (term272 A B s f _65296) = (term187 A B s f _65296).
Proof. exact (eq_refl (term272 A B s f _65296)). Qed.
Lemma lem5071984 {A B : Type'} (_65296 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term187 A B s f _65296.
Proof. exact (EQ_MP (@lem5071983 A B s f _65296) (@lem5071982 A B _65296 t g s f h1)). Qed.
Lemma lem5071985 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term273 A B s f _65296 _65297.
Proof. exact (@lem5071984 A B _65296 t g s f h1 _65297). Qed.
Lemma lem5071986 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term273 A B s f _65296 _65297) = (term184 A B s f _65296 _65297).
Proof. exact (eq_refl (term273 A B s f _65296 _65297)). Qed.
Lemma lem5071987 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term184 A B s f _65296 _65297.
Proof. exact (EQ_MP (@lem5071986 A B s f _65296 _65297) (@lem5071985 A B _65296 _65297 t g s f h1)). Qed.
Lemma lem5071991 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term271 A B s t f g _65299.
Proof. exact (@lem5071855 A B t g s f h1 _65299). Qed.
Lemma lem5071992 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_65299 : B) : (term271 A B s t f g _65299) = (term263 A B s t f g _65299).
Proof. exact (eq_refl (term271 A B s t f g _65299)). Qed.
Lemma lem5071993 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term263 A B s t f g _65299.
Proof. exact (EQ_MP (@lem5071992 A B s t f g _65299) (@lem5071991 A B _65299 t g s f h1)). Qed.
Lemma lem5072003 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term271 A B s t f g _65303.
Proof. exact (@lem5071927 A B t g s f h1 _65303). Qed.
Lemma lem5072004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_65303 : B) : (term271 A B s t f g _65303) = (term263 A B s t f g _65303).
Proof. exact (eq_refl (term271 A B s t f g _65303)). Qed.
Lemma lem5072005 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term263 A B s t f g _65303.
Proof. exact (EQ_MP (@lem5072004 A B s t f g _65303) (@lem5072003 A B _65303 t g s f h1)). Qed.
Lemma lem5072025 {A B : Type'} (_65290 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term166 A B s f _65290 t.
Proof. exact (EQ_MP (@lem5071965 A B s f _65290 t) (@lem5071964 A B _65290 t g s f h1)). Qed.
Lemma lem5072047 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term262 A B f x t) : term262 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5072065 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term166 A B s f _65294 t.
Proof. exact (EQ_MP (@lem5071977 A B s f _65294 t) (@lem5071976 A B _65294 t g s f h1)). Qed.
Lemma lem5072069 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term184 A B s f _65296 _65297) = (term274 A B s f _65296 _65297).
Proof. exact (@lem5070406 (term264 A _65296 s) (term175 A B s _65296 f _65297) (_65296 = _65297)). Qed.
Lemma lem5072076 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term275 A B s f _65296 _65297) = (term276 A B s f _65296 _65297).
Proof. exact (@lem5070406 (term264 A _65297 s) (term277 A B _65296 f _65297) (_65296 = _65297)). Qed.
Lemma lem5072077 {A : Type'} (_65296 : A) (s : A -> Prop) : (term176 A _65296 s) = (term176 A _65296 s).
Proof. exact (eq_refl (term176 A _65296 s)). Qed.
Lemma lem5072080 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term274 A B s f _65296 _65297) = (term278 A B s f _65296 _65297).
Proof. exact (MK_COMB (@lem5072077 A _65296 s) (@lem5072076 A B s f _65296 _65297)). Qed.
Lemma lem5072082 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term184 A B s f _65296 _65297) = (term278 A B s f _65296 _65297).
Proof. exact (TRANS (@lem5072069 A B s f _65296 _65297) (@lem5072080 A B s f _65296 _65297)). Qed.
Lemma lem5072083 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term278 A B s f _65296 _65297.
Proof. exact (EQ_MP (@lem5072082 A B s f _65296 _65297) (@lem5071987 A B _65296 _65297 t g s f h1)). Qed.
Lemma lem5072087 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) : term267 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5072093 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term279 A B t g _65295 s.
Proof. exact (proj1 (@lem5071981 A B _65295 t g s f h1)). Qed.
Lemma lem5072099 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term280 A B t f g _65295.
Proof. exact (proj2 (@lem5071981 A B _65295 t g s f h1)). Qed.
Lemma lem5072127 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term268 A B g y s) : term268 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5072133 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term279 A B t g _65299 s.
Proof. exact (proj1 (@lem5071993 A B _65299 t g s f h1)). Qed.
Lemma lem5072167 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) : term269 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5072179 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term280 A B t f g _65303.
Proof. exact (proj2 (@lem5072005 A B _65303 t g s f h1)). Qed.
Lemma lem5072243 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5071666 A B s t g f x h1)). Qed.
Lemma lem5072244 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term281 A x s.
Proof. exact (fun h0 : term264 A x s => @lem5072243 A B s t g f x h1). Qed.
Lemma lem5072246 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072247 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem5072246 (@IN A x s)). Qed.
Lemma lem5072248 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5072247 A x s) (@lem5072244 A B s t g f x h1)). Qed.
Lemma lem5072254 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072255 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : (term166 A B s f _65290 t) = (term283 A B f t _65290 s).
Proof. exact (@lem5072254 (term167 A B f _65290 t) (term264 A _65290 s)). Qed.
Lemma lem5072261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072262 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : (term284 A B s f _65290 t) = (term285 A B f t _65290 s).
Proof. exact (MK_COMB (@lem5072261) (@lem5072255 A B f t _65290 s)). Qed.
Lemma lem5072268 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : (term283 A B f t _65290 s) = (term283 A B f t _65290 s).
Proof. exact (eq_refl (term283 A B f t _65290 s)). Qed.
Lemma lem5072269 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : ((term166 A B s f _65290 t) = (term283 A B f t _65290 s)) = ((term283 A B f t _65290 s) = (term283 A B f t _65290 s)).
Proof. exact (MK_COMB (@lem5072262 A B f t _65290 s) (@lem5072268 A B f t _65290 s)). Qed.
Lemma lem5072271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072272 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072271 Prop x). Qed.
Lemma lem5072273 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : ((term283 A B f t _65290 s) = (term283 A B f t _65290 s)) = True.
Proof. exact (@lem5072272 (term283 A B f t _65290 s)). Qed.
Lemma lem5072274 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : ((term166 A B s f _65290 t) = (term283 A B f t _65290 s)) = True.
Proof. exact (TRANS (@lem5072269 A B f t _65290 s) (@lem5072273 A B f t _65290 s)). Qed.
Lemma lem5072275 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : True = ((term166 A B s f _65290 t) = (term283 A B f t _65290 s)).
Proof. exact (SYM (@lem5072274 A B f t _65290 s)). Qed.
Lemma lem5072276 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65290 : A) (s : A -> Prop) : (term166 A B s f _65290 t) = (term283 A B f t _65290 s).
Proof. exact (EQ_MP (@lem5072275 A B f t _65290 s) (@lem0)). Qed.
Lemma lem5072277 {A B : Type'} (_65290 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term283 A B f t _65290 s.
Proof. exact (EQ_MP (@lem5072276 A B f t _65290 s) (@lem5072025 A B _65290 t g s f h1)). Qed.
Lemma lem5072279 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072280 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65290 : A) (t : B -> Prop) : (term283 A B f t _65290 s) = (term287 A B s f _65290 t).
Proof. exact (@lem5072279 (term264 A _65290 s) (term167 A B f _65290 t)). Qed.
Lemma lem5072282 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072283 {A : Type'} (_65290 : A) (s : A -> Prop) : (term288 A _65290 s) = (@IN A _65290 s).
Proof. exact (@lem5072282 (@IN A _65290 s)). Qed.
Lemma lem5072284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072285 {A : Type'} (_65290 : A) (s : A -> Prop) : (term289 A _65290 s) = (term290 A _65290 s).
Proof. exact (MK_COMB (@lem5072284) (@lem5072283 A _65290 s)). Qed.
Lemma lem5072286 {A B : Type'} (f : A -> B) (_65290 : A) (t : B -> Prop) : (term167 A B f _65290 t) = (term167 A B f _65290 t).
Proof. exact (eq_refl (term167 A B f _65290 t)). Qed.
Lemma lem5072287 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65290 : A) (t : B -> Prop) : (term287 A B s f _65290 t) = (term162 A B s f _65290 t).
Proof. exact (MK_COMB (@lem5072285 A _65290 s) (@lem5072286 A B f _65290 t)). Qed.
Lemma lem5072288 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65290 : A) (t : B -> Prop) : (term283 A B f t _65290 s) = (term162 A B s f _65290 t).
Proof. exact (TRANS (@lem5072280 A B s f _65290 t) (@lem5072287 A B s f _65290 t)). Qed.
Lemma lem5072291 {A B : Type'} (_65290 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65290 t.
Proof. exact (EQ_MP (@lem5072288 A B s f _65290 t) (@lem5072277 A B _65290 t g s f h1)). Qed.
Lemma lem5072292 {A B : Type'} (_65290 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65290 t.
Proof. exact (@lem5072291 A B _65290 t g s f h1). Qed.
Lemma lem5072293 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f x t.
Proof. exact (@lem5072292 A B x t g s f h1). Qed.
Lemma lem5072296 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (@lem5072293 A B x t g s f h1 (@lem5072248 A B s t g f x h2)). Qed.
Lemma lem5072297 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term291 A B f x t.
Proof. exact (fun h0 : term262 A B f x t => @lem5072296 A B s t g f x h1 h2). Qed.
Lemma lem5072299 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072300 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term291 A B f x t) = (term167 A B f x t).
Proof. exact (@lem5072299 (term167 A B f x t)). Qed.
Lemma lem5072301 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (EQ_MP (@lem5072300 A B f x t) (@lem5072297 A B s t g f x h1 h2)). Qed.
Lemma lem5072304 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5072306 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term262 A B f x t) = (term292 A B f x t).
Proof. exact (@lem5072304 (term167 A B f x t)). Qed.
Lemma lem5072309 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term262 A B f x t) : term292 A B f x t.
Proof. exact (EQ_MP (@lem5072306 A B f x t) (@lem5072047 A B f x t h1)). Qed.
Lemma lem5072312 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (@lem5072309 A B f x t h1 (@lem5072301 A B s t g f x h2 h3)). Qed.
Lemma lem5072313 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : term293.
Proof. exact (fun h0 : ~ False => @lem5072312 A B s t g f x h1 h2 h3). Qed.
Lemma lem5072315 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072316 : term293 = False.
Proof. exact (@lem5072315 False). Qed.
Lemma lem5072317 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5072316) (@lem5072313 A B s t g f x h1 h2 h3)). Qed.
Lemma lem5072381 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5071666 A B s t g f x h1)). Qed.
Lemma lem5072382 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term281 A x s.
Proof. exact (fun h0 : term264 A x s => @lem5072381 A B s t g f x h1). Qed.
Lemma lem5072384 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072385 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem5072384 (@IN A x s)). Qed.
Lemma lem5072386 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5072385 A x s) (@lem5072382 A B s t g f x h1)). Qed.
Lemma lem5072392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072393 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : (term166 A B s f _65294 t) = (term283 A B f t _65294 s).
Proof. exact (@lem5072392 (term167 A B f _65294 t) (term264 A _65294 s)). Qed.
Lemma lem5072399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072400 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : (term284 A B s f _65294 t) = (term285 A B f t _65294 s).
Proof. exact (MK_COMB (@lem5072399) (@lem5072393 A B f t _65294 s)). Qed.
Lemma lem5072406 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : (term283 A B f t _65294 s) = (term283 A B f t _65294 s).
Proof. exact (eq_refl (term283 A B f t _65294 s)). Qed.
Lemma lem5072407 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : ((term166 A B s f _65294 t) = (term283 A B f t _65294 s)) = ((term283 A B f t _65294 s) = (term283 A B f t _65294 s)).
Proof. exact (MK_COMB (@lem5072400 A B f t _65294 s) (@lem5072406 A B f t _65294 s)). Qed.
Lemma lem5072409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072410 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072409 Prop x). Qed.
Lemma lem5072411 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : ((term283 A B f t _65294 s) = (term283 A B f t _65294 s)) = True.
Proof. exact (@lem5072410 (term283 A B f t _65294 s)). Qed.
Lemma lem5072412 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : ((term166 A B s f _65294 t) = (term283 A B f t _65294 s)) = True.
Proof. exact (TRANS (@lem5072407 A B f t _65294 s) (@lem5072411 A B f t _65294 s)). Qed.
Lemma lem5072413 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : True = ((term166 A B s f _65294 t) = (term283 A B f t _65294 s)).
Proof. exact (SYM (@lem5072412 A B f t _65294 s)). Qed.
Lemma lem5072414 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65294 : A) (s : A -> Prop) : (term166 A B s f _65294 t) = (term283 A B f t _65294 s).
Proof. exact (EQ_MP (@lem5072413 A B f t _65294 s) (@lem0)). Qed.
Lemma lem5072415 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term283 A B f t _65294 s.
Proof. exact (EQ_MP (@lem5072414 A B f t _65294 s) (@lem5072065 A B _65294 t g s f h1)). Qed.
Lemma lem5072417 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072418 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65294 : A) (t : B -> Prop) : (term283 A B f t _65294 s) = (term287 A B s f _65294 t).
Proof. exact (@lem5072417 (term264 A _65294 s) (term167 A B f _65294 t)). Qed.
Lemma lem5072420 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072421 {A : Type'} (_65294 : A) (s : A -> Prop) : (term288 A _65294 s) = (@IN A _65294 s).
Proof. exact (@lem5072420 (@IN A _65294 s)). Qed.
Lemma lem5072422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072423 {A : Type'} (_65294 : A) (s : A -> Prop) : (term289 A _65294 s) = (term290 A _65294 s).
Proof. exact (MK_COMB (@lem5072422) (@lem5072421 A _65294 s)). Qed.
Lemma lem5072424 {A B : Type'} (f : A -> B) (_65294 : A) (t : B -> Prop) : (term167 A B f _65294 t) = (term167 A B f _65294 t).
Proof. exact (eq_refl (term167 A B f _65294 t)). Qed.
Lemma lem5072425 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65294 : A) (t : B -> Prop) : (term287 A B s f _65294 t) = (term162 A B s f _65294 t).
Proof. exact (MK_COMB (@lem5072423 A _65294 s) (@lem5072424 A B f _65294 t)). Qed.
Lemma lem5072426 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65294 : A) (t : B -> Prop) : (term283 A B f t _65294 s) = (term162 A B s f _65294 t).
Proof. exact (TRANS (@lem5072418 A B s f _65294 t) (@lem5072425 A B s f _65294 t)). Qed.
Lemma lem5072429 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65294 t.
Proof. exact (EQ_MP (@lem5072426 A B s f _65294 t) (@lem5072415 A B _65294 t g s f h1)). Qed.
Lemma lem5072430 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65294 t.
Proof. exact (@lem5072429 A B _65294 t g s f h1). Qed.
Lemma lem5072431 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f x t.
Proof. exact (@lem5072430 A B x t g s f h1). Qed.
Lemma lem5072434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (@lem5072431 A B x t g s f h1 (@lem5072386 A B s t g f x h2)). Qed.
Lemma lem5072435 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term291 A B f x t.
Proof. exact (fun h0 : term262 A B f x t => @lem5072434 A B s t g f x h1 h2). Qed.
Lemma lem5072437 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072438 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term291 A B f x t) = (term167 A B f x t).
Proof. exact (@lem5072437 (term167 A B f x t)). Qed.
Lemma lem5072439 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (EQ_MP (@lem5072438 A B f x t) (@lem5072435 A B s t g f x h1 h2)). Qed.
Lemma lem5072445 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072446 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : (term279 A B t g _65295 s) = (term294 A B g s _65295 t).
Proof. exact (@lem5072445 (term213 A B g _65295 s) (term264 B _65295 t)). Qed.
Lemma lem5072452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072453 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : (term295 A B t g _65295 s) = (term296 A B g s _65295 t).
Proof. exact (MK_COMB (@lem5072452) (@lem5072446 A B g s _65295 t)). Qed.
Lemma lem5072459 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : (term294 A B g s _65295 t) = (term294 A B g s _65295 t).
Proof. exact (eq_refl (term294 A B g s _65295 t)). Qed.
Lemma lem5072460 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : ((term279 A B t g _65295 s) = (term294 A B g s _65295 t)) = ((term294 A B g s _65295 t) = (term294 A B g s _65295 t)).
Proof. exact (MK_COMB (@lem5072453 A B g s _65295 t) (@lem5072459 A B g s _65295 t)). Qed.
Lemma lem5072462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072463 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072462 Prop x). Qed.
Lemma lem5072464 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : ((term294 A B g s _65295 t) = (term294 A B g s _65295 t)) = True.
Proof. exact (@lem5072463 (term294 A B g s _65295 t)). Qed.
Lemma lem5072465 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : ((term279 A B t g _65295 s) = (term294 A B g s _65295 t)) = True.
Proof. exact (TRANS (@lem5072460 A B g s _65295 t) (@lem5072464 A B g s _65295 t)). Qed.
Lemma lem5072466 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : True = ((term279 A B t g _65295 s) = (term294 A B g s _65295 t)).
Proof. exact (SYM (@lem5072465 A B g s _65295 t)). Qed.
Lemma lem5072467 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65295 : B) (t : B -> Prop) : (term279 A B t g _65295 s) = (term294 A B g s _65295 t).
Proof. exact (EQ_MP (@lem5072466 A B g s _65295 t) (@lem0)). Qed.
Lemma lem5072468 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term294 A B g s _65295 t.
Proof. exact (EQ_MP (@lem5072467 A B g s _65295 t) (@lem5072093 A B _65295 t g s f h1)). Qed.
Lemma lem5072470 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072471 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65295 : B) (s : A -> Prop) : (term294 A B g s _65295 t) = (term297 A B t g _65295 s).
Proof. exact (@lem5072470 (term264 B _65295 t) (term213 A B g _65295 s)). Qed.
Lemma lem5072473 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072474 {B : Type'} (_65295 : B) (t : B -> Prop) : (term288 B _65295 t) = (@IN B _65295 t).
Proof. exact (@lem5072473 (@IN B _65295 t)). Qed.
Lemma lem5072475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072476 {B : Type'} (_65295 : B) (t : B -> Prop) : (term289 B _65295 t) = (term290 B _65295 t).
Proof. exact (MK_COMB (@lem5072475) (@lem5072474 B _65295 t)). Qed.
Lemma lem5072477 {A B : Type'} (g : B -> A) (_65295 : B) (s : A -> Prop) : (term213 A B g _65295 s) = (term213 A B g _65295 s).
Proof. exact (eq_refl (term213 A B g _65295 s)). Qed.
Lemma lem5072478 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65295 : B) (s : A -> Prop) : (term297 A B t g _65295 s) = (term298 A B t g _65295 s).
Proof. exact (MK_COMB (@lem5072476 B _65295 t) (@lem5072477 A B g _65295 s)). Qed.
Lemma lem5072479 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65295 : B) (s : A -> Prop) : (term294 A B g s _65295 t) = (term298 A B t g _65295 s).
Proof. exact (TRANS (@lem5072471 A B t g _65295 s) (@lem5072478 A B t g _65295 s)). Qed.
Lemma lem5072482 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term298 A B t g _65295 s.
Proof. exact (EQ_MP (@lem5072479 A B t g _65295 s) (@lem5072468 A B _65295 t g s f h1)). Qed.
Lemma lem5072483 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term298 A B t g _65295 s.
Proof. exact (@lem5072482 A B _65295 t g s f h1). Qed.
Lemma lem5072484 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term299 A B t g f x s.
Proof. exact (@lem5072483 A B (f x) t g s f h1). Qed.
Lemma lem5072487 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term300 A B g f x s.
Proof. exact (@lem5072484 A B x t g s f h1 (@lem5072439 A B s t g f x h1 h2)). Qed.
Lemma lem5072488 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term301 A B g f x s.
Proof. exact (fun h0 : term302 A B g f x s => @lem5072487 A B s t g f x h1 h2). Qed.
Lemma lem5072490 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072491 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (s : A -> Prop) : (term301 A B g f x s) = (term300 A B g f x s).
Proof. exact (@lem5072490 (term300 A B g f x s)). Qed.
Lemma lem5072492 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term300 A B g f x s.
Proof. exact (EQ_MP (@lem5072491 A B g f x s) (@lem5072488 A B s t g f x h1 h2)). Qed.
Lemma lem5072494 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5071666 A B s t g f x h1)). Qed.
Lemma lem5072495 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term281 A x s.
Proof. exact (fun h0 : term264 A x s => @lem5072494 A B s t g f x h1). Qed.
Lemma lem5072497 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072498 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem5072497 (@IN A x s)). Qed.
Lemma lem5072499 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5072498 A x s) (@lem5072495 A B s t g f x h1)). Qed.
Lemma lem5072501 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5071666 A B s t g f x h1)). Qed.
Lemma lem5072502 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : term281 A x s.
Proof. exact (fun h0 : term264 A x s => @lem5072501 A B s t g f x h1). Qed.
Lemma lem5072504 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072505 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem5072504 (@IN A x s)). Qed.
Lemma lem5072506 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term199 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5072505 A x s) (@lem5072502 A B s t g f x h1)). Qed.
Lemma lem5072508 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65294 t.
Proof. exact (EQ_MP (@lem5072426 A B s f _65294 t) (@lem5072415 A B _65294 t g s f h1)). Qed.
Lemma lem5072509 {A B : Type'} (_65294 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f _65294 t.
Proof. exact (@lem5072508 A B _65294 t g s f h1). Qed.
Lemma lem5072510 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term162 A B s f x t.
Proof. exact (@lem5072509 A B x t g s f h1). Qed.
Lemma lem5072513 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (@lem5072510 A B x t g s f h1 (@lem5072506 A B s t g f x h2)). Qed.
Lemma lem5072514 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term291 A B f x t.
Proof. exact (fun h0 : term262 A B f x t => @lem5072513 A B s t g f x h1 h2). Qed.
Lemma lem5072516 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072517 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term291 A B f x t) = (term167 A B f x t).
Proof. exact (@lem5072516 (term167 A B f x t)). Qed.
Lemma lem5072518 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term167 A B f x t.
Proof. exact (EQ_MP (@lem5072517 A B f x t) (@lem5072514 A B s t g f x h1 h2)). Qed.
Lemma lem5072524 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072525 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : (term280 A B t f g _65295) = (term303 A B f g _65295 t).
Proof. exact (@lem5072524 ((term214 A B f g _65295) = _65295) (term264 B _65295 t)). Qed.
Lemma lem5072533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072534 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : (term304 A B t f g _65295) = (term305 A B f g _65295 t).
Proof. exact (MK_COMB (@lem5072533) (@lem5072525 A B f g _65295 t)). Qed.
Lemma lem5072542 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : (term303 A B f g _65295 t) = (term303 A B f g _65295 t).
Proof. exact (eq_refl (term303 A B f g _65295 t)). Qed.
Lemma lem5072543 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : ((term280 A B t f g _65295) = (term303 A B f g _65295 t)) = ((term303 A B f g _65295 t) = (term303 A B f g _65295 t)).
Proof. exact (MK_COMB (@lem5072534 A B f g _65295 t) (@lem5072542 A B f g _65295 t)). Qed.
Lemma lem5072545 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072546 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072545 Prop x). Qed.
Lemma lem5072547 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : ((term303 A B f g _65295 t) = (term303 A B f g _65295 t)) = True.
Proof. exact (@lem5072546 (term303 A B f g _65295 t)). Qed.
Lemma lem5072548 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : ((term280 A B t f g _65295) = (term303 A B f g _65295 t)) = True.
Proof. exact (TRANS (@lem5072543 A B f g _65295 t) (@lem5072547 A B f g _65295 t)). Qed.
Lemma lem5072549 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : True = ((term280 A B t f g _65295) = (term303 A B f g _65295 t)).
Proof. exact (SYM (@lem5072548 A B f g _65295 t)). Qed.
Lemma lem5072550 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) (t : B -> Prop) : (term280 A B t f g _65295) = (term303 A B f g _65295 t).
Proof. exact (EQ_MP (@lem5072549 A B f g _65295 t) (@lem0)). Qed.
Lemma lem5072551 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term303 A B f g _65295 t.
Proof. exact (EQ_MP (@lem5072550 A B f g _65295 t) (@lem5072099 A B _65295 t g s f h1)). Qed.
Lemma lem5072553 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072554 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65295 : B) : (term303 A B f g _65295 t) = (term306 A B t f g _65295).
Proof. exact (@lem5072553 (term264 B _65295 t) ((term214 A B f g _65295) = _65295)). Qed.
Lemma lem5072556 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072557 {B : Type'} (_65295 : B) (t : B -> Prop) : (term288 B _65295 t) = (@IN B _65295 t).
Proof. exact (@lem5072556 (@IN B _65295 t)). Qed.
Lemma lem5072558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072559 {B : Type'} (_65295 : B) (t : B -> Prop) : (term289 B _65295 t) = (term290 B _65295 t).
Proof. exact (MK_COMB (@lem5072558) (@lem5072557 B _65295 t)). Qed.
Lemma lem5072560 {A B : Type'} (f : A -> B) (g : B -> A) (_65295 : B) : ((term214 A B f g _65295) = _65295) = ((term214 A B f g _65295) = _65295).
Proof. exact (eq_refl ((term214 A B f g _65295) = _65295)). Qed.
Lemma lem5072561 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65295 : B) : (term306 A B t f g _65295) = (term307 A B t f g _65295).
Proof. exact (MK_COMB (@lem5072559 B _65295 t) (@lem5072560 A B f g _65295)). Qed.
Lemma lem5072562 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65295 : B) : (term303 A B f g _65295 t) = (term307 A B t f g _65295).
Proof. exact (TRANS (@lem5072554 A B t f g _65295) (@lem5072561 A B t f g _65295)). Qed.
Lemma lem5072565 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term307 A B t f g _65295.
Proof. exact (EQ_MP (@lem5072562 A B t f g _65295) (@lem5072551 A B _65295 t g s f h1)). Qed.
Lemma lem5072566 {A B : Type'} (_65295 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term307 A B t f g _65295.
Proof. exact (@lem5072565 A B _65295 t g s f h1). Qed.
Lemma lem5072567 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term308 A B t g f x.
Proof. exact (@lem5072566 A B (f x) t g s f h1). Qed.
Lemma lem5072570 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : (term309 A B g f x) = (f x).
Proof. exact (@lem5072567 A B x t g s f h1 (@lem5072518 A B s t g f x h1 h2)). Qed.
Lemma lem5072571 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term310 A B g f x.
Proof. exact (fun h0 : term311 A B g f x => @lem5072570 A B s t g f x h1 h2). Qed.
Lemma lem5072573 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072574 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term310 A B g f x) = ((term309 A B g f x) = (f x)).
Proof. exact (@lem5072573 ((term309 A B g f x) = (f x))). Qed.
Lemma lem5072575 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : (term309 A B g f x) = (f x).
Proof. exact (EQ_MP (@lem5072574 A B g f x) (@lem5072571 A B s t g f x h1 h2)). Qed.
Lemma lem5072591 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5072592 {A B : Type'} (f : A -> B) (s : A -> Prop) (_65296 : A) (_65297 : A) : (term276 A B s f _65296 _65297) = (term312 A B f s _65296 _65297).
Proof. exact (@lem5072591 (term277 A B _65296 f _65297) (term264 A _65297 s) (_65296 = _65297)). Qed.
Lemma lem5072608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072609 {A : Type'} (_65296 : A) (_65297 : A) (s : A -> Prop) : (term313 A s _65296 _65297) = (term314 A _65296 _65297 s).
Proof. exact (@lem5072608 (_65296 = _65297) (term264 A _65297 s)). Qed.
Lemma lem5072617 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) : (term315 A B _65296 f _65297) = (term315 A B _65296 f _65297).
Proof. exact (eq_refl (term315 A B _65296 f _65297)). Qed.
Lemma lem5072618 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term312 A B f s _65296 _65297) = (term316 A B f _65296 _65297 s).
Proof. exact (MK_COMB (@lem5072617 A B _65296 f _65297) (@lem5072609 A _65296 _65297 s)). Qed.
Lemma lem5072622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5072623 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term316 A B f _65296 _65297 s) = (term317 A B _65296 f _65297 s).
Proof. exact (@lem5072622 (_65296 = _65297) (term277 A B _65296 f _65297) (term264 A _65297 s)). Qed.
Lemma lem5072643 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term312 A B f s _65296 _65297) = (term317 A B _65296 f _65297 s).
Proof. exact (TRANS (@lem5072618 A B f _65296 _65297 s) (@lem5072623 A B _65296 f _65297 s)). Qed.
Lemma lem5072644 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term276 A B s f _65296 _65297) = (term317 A B _65296 f _65297 s).
Proof. exact (TRANS (@lem5072592 A B f s _65296 _65297) (@lem5072643 A B _65296 f _65297 s)). Qed.
Lemma lem5072645 {A : Type'} (_65296 : A) (s : A -> Prop) : (term176 A _65296 s) = (term176 A _65296 s).
Proof. exact (eq_refl (term176 A _65296 s)). Qed.
Lemma lem5072646 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term278 A B s f _65296 _65297) = (term318 A B _65296 f _65297 s).
Proof. exact (MK_COMB (@lem5072645 A _65296 s) (@lem5072644 A B _65296 f _65297 s)). Qed.
Lemma lem5072650 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5072651 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term318 A B _65296 f _65297 s) = (term319 A B _65296 f _65297 s).
Proof. exact (@lem5072650 (_65296 = _65297) (term264 A _65296 s) (term320 A B _65296 f _65297 s)). Qed.
Lemma lem5072667 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5072668 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term321 A B _65296 f _65297 s) = (term322 A B f _65296 _65297 s).
Proof. exact (@lem5072667 (term277 A B _65296 f _65297) (term264 A _65296 s) (term264 A _65297 s)). Qed.
Lemma lem5072686 {A : Type'} (_65296 : A) (_65297 : A) : (term323 A _65296 _65297) = (term323 A _65296 _65297).
Proof. exact (eq_refl (term323 A _65296 _65297)). Qed.
Lemma lem5072687 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term319 A B _65296 f _65297 s) = (term324 A B f _65296 _65297 s).
Proof. exact (MK_COMB (@lem5072686 A _65296 _65297) (@lem5072668 A B f _65296 _65297 s)). Qed.
Lemma lem5072698 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term318 A B _65296 f _65297 s) = (term324 A B f _65296 _65297 s).
Proof. exact (TRANS (@lem5072651 A B _65296 f _65297 s) (@lem5072687 A B f _65296 _65297 s)). Qed.
Lemma lem5072699 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term278 A B s f _65296 _65297) = (term324 A B f _65296 _65297 s).
Proof. exact (TRANS (@lem5072646 A B _65296 f _65297 s) (@lem5072698 A B f _65296 _65297 s)). Qed.
Lemma lem5072700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072701 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term325 A B s f _65296 _65297) = (term326 A B f _65296 _65297 s).
Proof. exact (MK_COMB (@lem5072700) (@lem5072699 A B f _65296 _65297 s)). Qed.
Lemma lem5072727 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072728 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term175 A B s _65296 f _65297) = (term320 A B _65296 f _65297 s).
Proof. exact (@lem5072727 (term277 A B _65296 f _65297) (term264 A _65297 s)). Qed.
Lemma lem5072736 {A : Type'} (_65296 : A) (s : A -> Prop) : (term176 A _65296 s) = (term176 A _65296 s).
Proof. exact (eq_refl (term176 A _65296 s)). Qed.
Lemma lem5072737 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) (s : A -> Prop) : (term178 A B s _65296 f _65297) = (term321 A B _65296 f _65297 s).
Proof. exact (MK_COMB (@lem5072736 A _65296 s) (@lem5072728 A B _65296 f _65297 s)). Qed.
Lemma lem5072741 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5072742 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term321 A B _65296 f _65297 s) = (term322 A B f _65296 _65297 s).
Proof. exact (@lem5072741 (term277 A B _65296 f _65297) (term264 A _65296 s) (term264 A _65297 s)). Qed.
Lemma lem5072760 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term178 A B s _65296 f _65297) = (term322 A B f _65296 _65297 s).
Proof. exact (TRANS (@lem5072737 A B _65296 f _65297 s) (@lem5072742 A B f _65296 _65297 s)). Qed.
Lemma lem5072761 {A : Type'} (_65296 : A) (_65297 : A) : (term323 A _65296 _65297) = (term323 A _65296 _65297).
Proof. exact (eq_refl (term323 A _65296 _65297)). Qed.
Lemma lem5072762 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : (term327 A B s _65296 f _65297) = (term324 A B f _65296 _65297 s).
Proof. exact (MK_COMB (@lem5072761 A _65296 _65297) (@lem5072760 A B f _65296 _65297 s)). Qed.
Lemma lem5072773 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : ((term278 A B s f _65296 _65297) = (term327 A B s _65296 f _65297)) = ((term324 A B f _65296 _65297 s) = (term324 A B f _65296 _65297 s)).
Proof. exact (MK_COMB (@lem5072701 A B f _65296 _65297 s) (@lem5072762 A B f _65296 _65297 s)). Qed.
Lemma lem5072775 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072776 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072775 Prop x). Qed.
Lemma lem5072777 {A B : Type'} (f : A -> B) (_65296 : A) (_65297 : A) (s : A -> Prop) : ((term324 A B f _65296 _65297 s) = (term324 A B f _65296 _65297 s)) = True.
Proof. exact (@lem5072776 (term324 A B f _65296 _65297 s)). Qed.
Lemma lem5072778 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : ((term278 A B s f _65296 _65297) = (term327 A B s _65296 f _65297)) = True.
Proof. exact (TRANS (@lem5072773 A B f _65296 _65297 s) (@lem5072777 A B f _65296 _65297 s)). Qed.
Lemma lem5072779 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : True = ((term278 A B s f _65296 _65297) = (term327 A B s _65296 f _65297)).
Proof. exact (SYM (@lem5072778 A B s _65296 f _65297)). Qed.
Lemma lem5072780 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term278 A B s f _65296 _65297) = (term327 A B s _65296 f _65297).
Proof. exact (EQ_MP (@lem5072779 A B s _65296 f _65297) (@lem0)). Qed.
Lemma lem5072781 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term327 A B s _65296 f _65297.
Proof. exact (EQ_MP (@lem5072780 A B s _65296 f _65297) (@lem5072083 A B _65296 _65297 t g s f h1)). Qed.
Lemma lem5072783 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072784 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term327 A B s _65296 f _65297) = (term328 A B s f _65296 _65297).
Proof. exact (@lem5072783 (term178 A B s _65296 f _65297) (_65296 = _65297)). Qed.
Lemma lem5072786 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5072787 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term331 A B s _65296 f _65297) = (term332 A B s _65296 f _65297).
Proof. exact (@lem5072786 (term264 A _65296 s) (term175 A B s _65296 f _65297)). Qed.
Lemma lem5072789 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072790 {A : Type'} (_65296 : A) (s : A -> Prop) : (term288 A _65296 s) = (@IN A _65296 s).
Proof. exact (@lem5072789 (@IN A _65296 s)). Qed.
Lemma lem5072791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5072792 {A : Type'} (_65296 : A) (s : A -> Prop) : (term333 A _65296 s) = (term197 A _65296 s).
Proof. exact (MK_COMB (@lem5072791) (@lem5072790 A _65296 s)). Qed.
Lemma lem5072794 (a : Prop) (b : Prop) : (term329 a b) = (term330 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5072795 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term334 A B s _65296 f _65297) = (term335 A B s _65296 f _65297).
Proof. exact (@lem5072794 (term264 A _65297 s) (term277 A B _65296 f _65297)). Qed.
Lemma lem5072797 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072798 {A : Type'} (_65297 : A) (s : A -> Prop) : (term288 A _65297 s) = (@IN A _65297 s).
Proof. exact (@lem5072797 (@IN A _65297 s)). Qed.
Lemma lem5072799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5072800 {A : Type'} (_65297 : A) (s : A -> Prop) : (term333 A _65297 s) = (term197 A _65297 s).
Proof. exact (MK_COMB (@lem5072799) (@lem5072798 A _65297 s)). Qed.
Lemma lem5072802 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072803 {A B : Type'} (_65296 : A) (f : A -> B) (_65297 : A) : (term336 A B _65296 f _65297) = ((f _65296) = (f _65297)).
Proof. exact (@lem5072802 ((f _65296) = (f _65297))). Qed.
Lemma lem5072804 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term335 A B s _65296 f _65297) = (term180 A B s _65296 f _65297).
Proof. exact (MK_COMB (@lem5072800 A _65297 s) (@lem5072803 A B _65296 f _65297)). Qed.
Lemma lem5072805 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term334 A B s _65296 f _65297) = (term180 A B s _65296 f _65297).
Proof. exact (TRANS (@lem5072795 A B s _65296 f _65297) (@lem5072804 A B s _65296 f _65297)). Qed.
Lemma lem5072806 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term332 A B s _65296 f _65297) = (term185 A B s _65296 f _65297).
Proof. exact (MK_COMB (@lem5072792 A _65296 s) (@lem5072805 A B s _65296 f _65297)). Qed.
Lemma lem5072807 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term331 A B s _65296 f _65297) = (term185 A B s _65296 f _65297).
Proof. exact (TRANS (@lem5072787 A B s _65296 f _65297) (@lem5072806 A B s _65296 f _65297)). Qed.
Lemma lem5072808 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072809 {A B : Type'} (s : A -> Prop) (_65296 : A) (f : A -> B) (_65297 : A) : (term337 A B s _65296 f _65297) = (term338 A B s _65296 f _65297).
Proof. exact (MK_COMB (@lem5072808) (@lem5072807 A B s _65296 f _65297)). Qed.
Lemma lem5072810 {A : Type'} (_65296 : A) (_65297 : A) : (_65296 = _65297) = (_65296 = _65297).
Proof. exact (eq_refl (_65296 = _65297)). Qed.
Lemma lem5072811 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term328 A B s f _65296 _65297) = (term158 A B s f _65296 _65297).
Proof. exact (MK_COMB (@lem5072809 A B s _65296 f _65297) (@lem5072810 A _65296 _65297)). Qed.
Lemma lem5072812 {A B : Type'} (s : A -> Prop) (f : A -> B) (_65296 : A) (_65297 : A) : (term327 A B s _65296 f _65297) = (term158 A B s f _65296 _65297).
Proof. exact (TRANS (@lem5072784 A B s f _65296 _65297) (@lem5072811 A B s f _65296 _65297)). Qed.
Lemma lem5072814 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term339 A B s g f x.
Proof. exact (conj (@lem5072499 A B s t g f x h2) (@lem5072575 A B s t g f x h1 h2)). Qed.
Lemma lem5072815 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term340 A B s g f x.
Proof. exact (conj (@lem5072492 A B s t g f x h1 h2) (@lem5072814 A B s t g f x h1 h2)). Qed.
Lemma lem5072817 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term158 A B s f _65296 _65297.
Proof. exact (EQ_MP (@lem5072812 A B s f _65296 _65297) (@lem5072781 A B _65296 _65297 t g s f h1)). Qed.
Lemma lem5072818 {A B : Type'} (_65296 : A) (_65297 : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term158 A B s f _65296 _65297.
Proof. exact (@lem5072817 A B _65296 _65297 t g s f h1). Qed.
Lemma lem5072819 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term341 A B s g f x.
Proof. exact (@lem5072818 A B (term196 A B g f x) x t g s f h1). Qed.
Lemma lem5072822 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : (term196 A B g f x) = x.
Proof. exact (@lem5072819 A B x t g s f h1 (@lem5072815 A B s t g f x h1 h2)). Qed.
Lemma lem5072823 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : term342 A B g f x.
Proof. exact (fun h0 : term267 A B g f x => @lem5072822 A B s t g f x h1 h2). Qed.
Lemma lem5072825 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072826 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term342 A B g f x) = ((term196 A B g f x) = x).
Proof. exact (@lem5072825 ((term196 A B g f x) = x)). Qed.
Lemma lem5072827 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : (term196 A B g f x) = x.
Proof. exact (EQ_MP (@lem5072826 A B g f x) (@lem5072823 A B s t g f x h1 h2)). Qed.
Lemma lem5072830 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5072832 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term267 A B g f x) = (term343 A B g f x).
Proof. exact (@lem5072830 ((term196 A B g f x) = x)). Qed.
Lemma lem5072835 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) : term343 A B g f x.
Proof. exact (EQ_MP (@lem5072832 A B g f x) (@lem5072087 A B g f x h1)). Qed.
Lemma lem5072838 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (@lem5072835 A B g f x h1 (@lem5072827 A B s t g f x h2 h3)). Qed.
Lemma lem5072839 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : term293.
Proof. exact (fun h0 : ~ False => @lem5072838 A B s t g f x h1 h2 h3). Qed.
Lemma lem5072841 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072842 : term293 = False.
Proof. exact (@lem5072841 False). Qed.
Lemma lem5072843 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5072842) (@lem5072839 A B s t g f x h1 h2 h3)). Qed.
Lemma lem5072907 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5071667 A B t s f g y h1)). Qed.
Lemma lem5072908 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : term281 B y t.
Proof. exact (fun h0 : term264 B y t => @lem5072907 A B t s f g y h1). Qed.
Lemma lem5072910 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072911 {B : Type'} (y : B) (t : B -> Prop) : (term281 B y t) = (@IN B y t).
Proof. exact (@lem5072910 (@IN B y t)). Qed.
Lemma lem5072912 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5072911 B y t) (@lem5072908 A B t s f g y h1)). Qed.
Lemma lem5072918 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5072919 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : (term279 A B t g _65299 s) = (term294 A B g s _65299 t).
Proof. exact (@lem5072918 (term213 A B g _65299 s) (term264 B _65299 t)). Qed.
Lemma lem5072925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5072926 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : (term295 A B t g _65299 s) = (term296 A B g s _65299 t).
Proof. exact (MK_COMB (@lem5072925) (@lem5072919 A B g s _65299 t)). Qed.
Lemma lem5072932 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : (term294 A B g s _65299 t) = (term294 A B g s _65299 t).
Proof. exact (eq_refl (term294 A B g s _65299 t)). Qed.
Lemma lem5072933 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : ((term279 A B t g _65299 s) = (term294 A B g s _65299 t)) = ((term294 A B g s _65299 t) = (term294 A B g s _65299 t)).
Proof. exact (MK_COMB (@lem5072926 A B g s _65299 t) (@lem5072932 A B g s _65299 t)). Qed.
Lemma lem5072935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5072936 (x : Prop) : (x = x) = True.
Proof. exact (@lem5072935 Prop x). Qed.
Lemma lem5072937 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : ((term294 A B g s _65299 t) = (term294 A B g s _65299 t)) = True.
Proof. exact (@lem5072936 (term294 A B g s _65299 t)). Qed.
Lemma lem5072938 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : ((term279 A B t g _65299 s) = (term294 A B g s _65299 t)) = True.
Proof. exact (TRANS (@lem5072933 A B g s _65299 t) (@lem5072937 A B g s _65299 t)). Qed.
Lemma lem5072939 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : True = ((term279 A B t g _65299 s) = (term294 A B g s _65299 t)).
Proof. exact (SYM (@lem5072938 A B g s _65299 t)). Qed.
Lemma lem5072940 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65299 : B) (t : B -> Prop) : (term279 A B t g _65299 s) = (term294 A B g s _65299 t).
Proof. exact (EQ_MP (@lem5072939 A B g s _65299 t) (@lem0)). Qed.
Lemma lem5072941 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term294 A B g s _65299 t.
Proof. exact (EQ_MP (@lem5072940 A B g s _65299 t) (@lem5072133 A B _65299 t g s f h1)). Qed.
Lemma lem5072943 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5072944 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65299 : B) (s : A -> Prop) : (term294 A B g s _65299 t) = (term297 A B t g _65299 s).
Proof. exact (@lem5072943 (term264 B _65299 t) (term213 A B g _65299 s)). Qed.
Lemma lem5072946 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5072947 {B : Type'} (_65299 : B) (t : B -> Prop) : (term288 B _65299 t) = (@IN B _65299 t).
Proof. exact (@lem5072946 (@IN B _65299 t)). Qed.
Lemma lem5072948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5072949 {B : Type'} (_65299 : B) (t : B -> Prop) : (term289 B _65299 t) = (term290 B _65299 t).
Proof. exact (MK_COMB (@lem5072948) (@lem5072947 B _65299 t)). Qed.
Lemma lem5072950 {A B : Type'} (g : B -> A) (_65299 : B) (s : A -> Prop) : (term213 A B g _65299 s) = (term213 A B g _65299 s).
Proof. exact (eq_refl (term213 A B g _65299 s)). Qed.
Lemma lem5072951 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65299 : B) (s : A -> Prop) : (term297 A B t g _65299 s) = (term298 A B t g _65299 s).
Proof. exact (MK_COMB (@lem5072949 B _65299 t) (@lem5072950 A B g _65299 s)). Qed.
Lemma lem5072952 {A B : Type'} (t : B -> Prop) (g : B -> A) (_65299 : B) (s : A -> Prop) : (term294 A B g s _65299 t) = (term298 A B t g _65299 s).
Proof. exact (TRANS (@lem5072944 A B t g _65299 s) (@lem5072951 A B t g _65299 s)). Qed.
Lemma lem5072955 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term298 A B t g _65299 s.
Proof. exact (EQ_MP (@lem5072952 A B t g _65299 s) (@lem5072941 A B _65299 t g s f h1)). Qed.
Lemma lem5072956 {A B : Type'} (_65299 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term298 A B t g _65299 s.
Proof. exact (@lem5072955 A B _65299 t g s f h1). Qed.
Lemma lem5072957 {A B : Type'} (y : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term298 A B t g y s.
Proof. exact (@lem5072956 A B y t g s f h1). Qed.
Lemma lem5072960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : term213 A B g y s.
Proof. exact (@lem5072957 A B y t g s f h1 (@lem5072912 A B t s f g y h2)). Qed.
Lemma lem5072961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : term344 A B g y s.
Proof. exact (fun h0 : term268 A B g y s => @lem5072960 A B t s f g y h1 h2). Qed.
Lemma lem5072963 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072964 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term344 A B g y s) = (term213 A B g y s).
Proof. exact (@lem5072963 (term213 A B g y s)). Qed.
Lemma lem5072965 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : term213 A B g y s.
Proof. exact (EQ_MP (@lem5072964 A B g y s) (@lem5072961 A B t s f g y h1 h2)). Qed.
Lemma lem5072968 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5072970 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term268 A B g y s) = (term345 A B g y s).
Proof. exact (@lem5072968 (term213 A B g y s)). Qed.
Lemma lem5072973 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term268 A B g y s) : term345 A B g y s.
Proof. exact (EQ_MP (@lem5072970 A B g y s) (@lem5072127 A B g y s h1)). Qed.
Lemma lem5072976 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (@lem5072973 A B g y s h1 (@lem5072965 A B t s f g y h2 h3)). Qed.
Lemma lem5072977 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : term293.
Proof. exact (fun h0 : ~ False => @lem5072976 A B t s f g y h1 h2 h3). Qed.
Lemma lem5072979 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5072980 : term293 = False.
Proof. exact (@lem5072979 False). Qed.
Lemma lem5072981 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5072980) (@lem5072977 A B t s f g y h1 h2 h3)). Qed.
Lemma lem5073045 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5071667 A B t s f g y h1)). Qed.
Lemma lem5073046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : term281 B y t.
Proof. exact (fun h0 : term264 B y t => @lem5073045 A B t s f g y h1). Qed.
Lemma lem5073048 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5073049 {B : Type'} (y : B) (t : B -> Prop) : (term281 B y t) = (@IN B y t).
Proof. exact (@lem5073048 (@IN B y t)). Qed.
Lemma lem5073050 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term216 A B t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5073049 B y t) (@lem5073046 A B t s f g y h1)). Qed.
Lemma lem5073056 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5073057 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : (term280 A B t f g _65303) = (term303 A B f g _65303 t).
Proof. exact (@lem5073056 ((term214 A B f g _65303) = _65303) (term264 B _65303 t)). Qed.
Lemma lem5073065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5073066 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : (term304 A B t f g _65303) = (term305 A B f g _65303 t).
Proof. exact (MK_COMB (@lem5073065) (@lem5073057 A B f g _65303 t)). Qed.
Lemma lem5073074 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : (term303 A B f g _65303 t) = (term303 A B f g _65303 t).
Proof. exact (eq_refl (term303 A B f g _65303 t)). Qed.
Lemma lem5073075 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : ((term280 A B t f g _65303) = (term303 A B f g _65303 t)) = ((term303 A B f g _65303 t) = (term303 A B f g _65303 t)).
Proof. exact (MK_COMB (@lem5073066 A B f g _65303 t) (@lem5073074 A B f g _65303 t)). Qed.
Lemma lem5073077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5073078 (x : Prop) : (x = x) = True.
Proof. exact (@lem5073077 Prop x). Qed.
Lemma lem5073079 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : ((term303 A B f g _65303 t) = (term303 A B f g _65303 t)) = True.
Proof. exact (@lem5073078 (term303 A B f g _65303 t)). Qed.
Lemma lem5073080 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : ((term280 A B t f g _65303) = (term303 A B f g _65303 t)) = True.
Proof. exact (TRANS (@lem5073075 A B f g _65303 t) (@lem5073079 A B f g _65303 t)). Qed.
Lemma lem5073081 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : True = ((term280 A B t f g _65303) = (term303 A B f g _65303 t)).
Proof. exact (SYM (@lem5073080 A B f g _65303 t)). Qed.
Lemma lem5073082 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) (t : B -> Prop) : (term280 A B t f g _65303) = (term303 A B f g _65303 t).
Proof. exact (EQ_MP (@lem5073081 A B f g _65303 t) (@lem0)). Qed.
Lemma lem5073083 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term303 A B f g _65303 t.
Proof. exact (EQ_MP (@lem5073082 A B f g _65303 t) (@lem5072179 A B _65303 t g s f h1)). Qed.
Lemma lem5073085 (b : Prop) (a : Prop) : (a \/ b) = (term286 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5073086 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65303 : B) : (term303 A B f g _65303 t) = (term306 A B t f g _65303).
Proof. exact (@lem5073085 (term264 B _65303 t) ((term214 A B f g _65303) = _65303)). Qed.
Lemma lem5073088 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5073089 {B : Type'} (_65303 : B) (t : B -> Prop) : (term288 B _65303 t) = (@IN B _65303 t).
Proof. exact (@lem5073088 (@IN B _65303 t)). Qed.
Lemma lem5073090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5073091 {B : Type'} (_65303 : B) (t : B -> Prop) : (term289 B _65303 t) = (term290 B _65303 t).
Proof. exact (MK_COMB (@lem5073090) (@lem5073089 B _65303 t)). Qed.
Lemma lem5073092 {A B : Type'} (f : A -> B) (g : B -> A) (_65303 : B) : ((term214 A B f g _65303) = _65303) = ((term214 A B f g _65303) = _65303).
Proof. exact (eq_refl ((term214 A B f g _65303) = _65303)). Qed.
Lemma lem5073093 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65303 : B) : (term306 A B t f g _65303) = (term307 A B t f g _65303).
Proof. exact (MK_COMB (@lem5073091 B _65303 t) (@lem5073092 A B f g _65303)). Qed.
Lemma lem5073094 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_65303 : B) : (term303 A B f g _65303 t) = (term307 A B t f g _65303).
Proof. exact (TRANS (@lem5073086 A B t f g _65303) (@lem5073093 A B t f g _65303)). Qed.
Lemma lem5073097 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term307 A B t f g _65303.
Proof. exact (EQ_MP (@lem5073094 A B t f g _65303) (@lem5073083 A B _65303 t g s f h1)). Qed.
Lemma lem5073098 {A B : Type'} (_65303 : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term307 A B t f g _65303.
Proof. exact (@lem5073097 A B _65303 t g s f h1). Qed.
Lemma lem5073099 {A B : Type'} (y : B) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term307 A B t f g y.
Proof. exact (@lem5073098 A B y t g s f h1). Qed.
Lemma lem5073102 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : (term214 A B f g y) = y.
Proof. exact (@lem5073099 A B y t g s f h1 (@lem5073050 A B t s f g y h2)). Qed.
Lemma lem5073103 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : term346 A B f g y.
Proof. exact (fun h0 : term269 A B f g y => @lem5073102 A B t s f g y h1 h2). Qed.
Lemma lem5073105 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5073106 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term346 A B f g y) = ((term214 A B f g y) = y).
Proof. exact (@lem5073105 ((term214 A B f g y) = y)). Qed.
Lemma lem5073107 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : (term214 A B f g y) = y.
Proof. exact (EQ_MP (@lem5073106 A B f g y) (@lem5073103 A B t s f g y h1 h2)). Qed.
Lemma lem5073110 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5073112 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term269 A B f g y) = (term347 A B f g y).
Proof. exact (@lem5073110 ((term214 A B f g y) = y)). Qed.
Lemma lem5073115 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) : term347 A B f g y.
Proof. exact (EQ_MP (@lem5073112 A B f g y) (@lem5072167 A B f g y h1)). Qed.
Lemma lem5073118 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (@lem5073115 A B f g y h1 (@lem5073107 A B t s f g y h2 h3)). Qed.
Lemma lem5073119 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : term293.
Proof. exact (fun h0 : ~ False => @lem5073118 A B t s f g y h1 h2 h3). Qed.
Lemma lem5073121 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5073122 : term293 = False.
Proof. exact (@lem5073121 False). Qed.
Lemma lem5073123 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073122) (@lem5073119 A B t s f g y h1 h2 h3)). Qed.
Lemma lem5073124 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term269 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term269 A B f g y => @lem5073123 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5072167 A B f g y h1)). Qed.
Lemma lem5073125 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073124 A B t s f g y h1 h2 h3) (@lem5072167 A B f g y h1)). Qed.
Lemma lem5073126 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term268 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term268 A B g y s => @lem5072981 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5072127 A B g y s h1)). Qed.
Lemma lem5073127 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073126 A B t s f g y h1 h2 h3) (@lem5072127 A B g y s h1)). Qed.
Lemma lem5073128 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term267 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term267 A B g f x => @lem5072843 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5072087 A B g f x h1)). Qed.
Lemma lem5073129 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073128 A B s t g f x h1 h2 h3) (@lem5072087 A B g f x h1)). Qed.
Lemma lem5073130 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term262 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term262 A B f x t => @lem5072317 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5072047 A B f x t h1)). Qed.
Lemma lem5073131 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073130 A B s t g f x h1 h2 h3) (@lem5072047 A B f x t h1)). Qed.
Lemma lem5073132 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term269 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term269 A B f g y => @lem5073125 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5071963 A B f g y h1)). Qed.
Lemma lem5073133 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073132 A B t s f g y h1 h2 h3) (@lem5071963 A B f g y h1)). Qed.
Lemma lem5073134 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term268 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term268 A B g y s => @lem5073127 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5071891 A B g y s h1)). Qed.
Lemma lem5073135 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073134 A B t s f g y h1 h2 h3) (@lem5071891 A B g y s h1)). Qed.
Lemma lem5073136 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term267 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term267 A B g f x => @lem5073129 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5071819 A B g f x h1)). Qed.
Lemma lem5073137 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073136 A B s t g f x h1 h2 h3) (@lem5071819 A B g f x h1)). Qed.
Lemma lem5073138 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term262 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term262 A B f x t => @lem5073131 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5071747 A B f x t h1)). Qed.
Lemma lem5073139 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073138 A B s t g f x h1 h2 h3) (@lem5071747 A B f x t h1)). Qed.
Lemma lem5073140 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term269 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term269 A B f g y => @lem5073133 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5071963 A B f g y h1)). Qed.
Lemma lem5073141 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term269 A B f g y) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073140 A B t s f g y h1 h2 h3) (@lem5071963 A B f g y h1)). Qed.
Lemma lem5073142 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : (term268 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term268 A B g y s => @lem5073135 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5071891 A B g y s h1)). Qed.
Lemma lem5073143 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term268 A B g y s) (h2 : term103 A B t g s f) (h3 : term216 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5073142 A B t s f g y h1 h2 h3) (@lem5071891 A B g y s h1)). Qed.
Lemma lem5073144 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term267 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term267 A B g f x => @lem5073137 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5071819 A B g f x h1)). Qed.
Lemma lem5073145 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term267 A B g f x) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073144 A B s t g f x h1 h2 h3) (@lem5071819 A B g f x h1)). Qed.
Lemma lem5073146 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : (term262 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term262 A B f x t => @lem5073139 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5071747 A B f x t h1)). Qed.
Lemma lem5073147 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term262 A B f x t) (h2 : term103 A B t g s f) (h3 : term199 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5073146 A B s t g f x h1 h2 h3) (@lem5071747 A B f x t h1)). Qed.
Lemma lem5073148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term216 A B t s f g y) : False.
Proof. exact (or_elim (@lem5071672 A B t s f g y h2) (fun h0 : term268 A B g y s => @lem5073143 A B t s f g y h0 h1 h2) (fun h0 : term269 A B f g y => @lem5073141 A B t s f g y h0 h1 h2)). Qed.
Lemma lem5073149 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term103 A B t g s f) (h2 : term199 A B s t g f x) : False.
Proof. exact (or_elim (@lem5071668 A B s t g f x h2) (fun h0 : term262 A B f x t => @lem5073147 A B s t g f x h0 h1 h2) (fun h0 : term267 A B g f x => @lem5073145 A B s t g f x h0 h1 h2)). Qed.
Lemma lem5073150 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term256 A B x t s f g y) : False.
Proof. exact (or_elim (@lem5071661 A B x t s f g y h2) (fun h0 : term199 A B s t g f x => @lem5073149 A B s t g f x h1 h0) (fun h0 : term216 A B t s f g y => @lem5073148 A B t s f g y h1 h0)). Qed.
Lemma lem5073151 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term256 A B x t s f g y) : (term256 A B x t s f g y) = False.
Proof. exact (prop_ext (fun h3 : term256 A B x t s f g y => @lem5073150 A B x t s f g y h1 h2) (fun h3 : False => @lem5071661 A B x t s f g y h2)). Qed.
Lemma lem5073152 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term103 A B t g s f) (h2 : term256 A B x t s f g y) : False.
Proof. exact (EQ_MP (@lem5073151 A B x t s f g y h1 h2) (@lem5071661 A B x t s f g y h2)). Qed.
Lemma lem5073153 {A B : Type'} (x : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term259 A B x t s f g) (h2 : term103 A B t g s f) : False.
Proof. exact (ex_elim (@lem5071490 A B x t s f g h1) (fun y : B => fun h0 : term258 A B x t s f g y => @lem5073152 A B x t s f g y h2 h0)). Qed.
Lemma lem5073154 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term165 A B t s f g) (h2 : term103 A B t g s f) : False.
Proof. exact (ex_elim (@lem5071489 A B t s f g h1) (fun x : A => fun h0 : term260 A B t s f g x => @lem5073153 A B x t g s f h0 h2)). Qed.
Lemma lem5073155 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term165 A B t s f g) (h2 : term103 A B t g s f) : (term165 A B t s f g) = False.
Proof. exact (prop_ext (fun h3 : term165 A B t s f g => @lem5073154 A B t g s f h1 h2) (fun h3 : False => @lem5071080 A B t s f g h1)). Qed.
Lemma lem5073156 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term165 A B t s f g) (h2 : term103 A B t g s f) : False.
Proof. exact (EQ_MP (@lem5073155 A B t g s f h1 h2) (@lem5071080 A B t s f g h1)). Qed.
Lemma lem5073157 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term164 A B t s f g.
Proof. exact (fun h0 : term165 A B t s f g => @lem5073156 A B t g s f h0 h1). Qed.
Lemma lem5073158 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term103 A B t g s f) : term116 A B t s f g.
Proof. exact (EQ_MP (@lem5071079 A B t s f g) (@lem5073157 A B t g s f h1)). Qed.
Lemma lem5073159 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term118 A B t s f g.
Proof. exact (fun h0 : term103 A B t g s f => @lem5073158 A B t g s f h0). Qed.
Lemma lem5073164 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term122 A B t s f.
Proof. exact (fun g : B -> A => @lem5073159 A B t s f g). Qed.
Lemma lem5073169 {A B : Type'} (s : A -> Prop) (f : A -> B) : term143 A B s f.
Proof. exact (fun t : B -> Prop => @lem5073164 A B t s f). Qed.
Lemma lem5073174 {A B : Type'} (f : A -> B) : term147 A B f.
Proof. exact (fun s : A -> Prop => @lem5073169 A B s f). Qed.
Lemma lem5073179 {A B : Type'} : term151 A B.
Proof. exact (fun f : A -> B => @lem5073174 A B f). Qed.
Lemma lem5073180 {A B : Type'} : term150 A B.
Proof. exact (EQ_MP (@lem5071074 A B) (@lem5073179 A B)). Qed.
Lemma lem5073181 {A B : Type'} (f : A -> B) : term348 A B f.
Proof. exact (@lem5073180 A B f). Qed.
Lemma lem5073182 {A B : Type'} (f : A -> B) : (term348 A B f) = (term146 A B f).
Proof. exact (eq_refl (term348 A B f)). Qed.
Lemma lem5073183 {A B : Type'} (f : A -> B) : term146 A B f.
Proof. exact (EQ_MP (@lem5073182 A B f) (@lem5073181 A B f)). Qed.
Lemma lem5073184 {A B : Type'} (f : A -> B) (s : A -> Prop) : term349 A B f s.
Proof. exact (@lem5073183 A B f s). Qed.
Lemma lem5073185 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term349 A B f s) = (term142 A B s f).
Proof. exact (eq_refl (term349 A B f s)). Qed.
Lemma lem5073186 {A B : Type'} (s : A -> Prop) (f : A -> B) : term142 A B s f.
Proof. exact (EQ_MP (@lem5073185 A B s f) (@lem5073184 A B f s)). Qed.
Lemma lem5073187 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term350 A B s f t.
Proof. exact (@lem5073186 A B s f t). Qed.
Lemma lem5073188 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term350 A B s f t) = (term133 A B t s f).
Proof. exact (eq_refl (term350 A B s f t)). Qed.
Lemma lem5073189 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term133 A B t s f.
Proof. exact (EQ_MP (@lem5073188 A B t s f) (@lem5073187 A B s f t)). Qed.
Lemma lem5073191 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term133 A B t s f.
Proof. exact (@lem5070795 A B t s f (@lem5073189 A B t s f)). Qed.
Lemma lem5073192 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term134 A B t s f) : False.
Proof. exact (@lem5073191 A B t s f (@lem5070779 A B t s f h1)). Qed.
Lemma lem5073193 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term134 A B t s f) : (term134 A B t s f) = False.
Proof. exact (prop_ext (fun h2 : term134 A B t s f => @lem5073192 A B t s f h1) (fun h2 : False => @lem5070779 A B t s f h1)). Qed.
Lemma lem5073194 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term134 A B t s f) : False.
Proof. exact (EQ_MP (@lem5073193 A B t s f h1) (@lem5070779 A B t s f h1)). Qed.
Lemma lem5073195 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term133 A B t s f.
Proof. exact (fun h0 : term134 A B t s f => @lem5073194 A B t s f h0). Qed.
Lemma lem5073196 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term122 A B t s f.
Proof. exact (EQ_MP (@lem5070778 A B t s f) (@lem5073195 A B t s f)). Qed.
Lemma lem5073197 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term108 A B t s f.
Proof. exact (@lem5070774 A B t s f (@lem5073196 A B t s f)). Qed.
Lemma lem5073198 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term69 A B t s f.
Proof. exact (EQ_MP (@lem5070747 A B t s f) (@lem5073197 A B t s f)). Qed.
Lemma lem5073203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term71 A B t s.
Proof. exact (fun f : A -> B => @lem5073198 A B t s f). Qed.
Lemma lem5073204 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term48 A B t s.
Proof. exact (EQ_MP (@lem5070581 A B t s) (@lem5073203 A B t s)). Qed.
Lemma lem5073205 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term59 A B t s.
Proof. exact (@lem5070480 A B t s (@lem5073204 A B t s)). Qed.
Lemma lem5073206 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term31 A B s t) : term57 A B t s.
Proof. exact (@lem5073205 A B t s (@lem5070453 A B s t h1)). Qed.
Lemma lem5073207 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term351 A B t s.
Proof. exact (fun h0 : term31 A B s t => @lem5073206 A B s t h0). Qed.
Lemma lem5073212 {A B : Type'} (s : A -> Prop) : term352 A B s.
Proof. exact (fun t : B -> Prop => @lem5073207 A B t s). Qed.
Lemma lem5073217 {A B : Type'} : term353 A B.
Proof. exact (fun s : A -> Prop => @lem5073212 A B s). Qed.
