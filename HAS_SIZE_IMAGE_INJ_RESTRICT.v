Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_RESTRICT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Require Import SURJECTIVE_IFF_INJECTIVE_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
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
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Lemma lem4968424 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4968425 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem4968424 A B h1 f). Qed.
Lemma lem4968426 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4968427 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem4968426 A B f) (@lem4968425 A B f h1)). Qed.
Lemma lem4968428 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem4968427 A B f h1 s). Qed.
Lemma lem4968429 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4968430 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem4968429 A B f s) (@lem4968428 A B f s h1)). Qed.
Lemma lem4968431 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term5 A B f s n.
Proof. exact (@lem4968430 A B f s h1 n). Qed.
Lemma lem4968432 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem4968433 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (EQ_MP (@lem4968432 A B f s n) (@lem4968431 A B f s n h1)). Qed.
Lemma lem4968434 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term7 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4968435 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem4968433 A B f s n h1 (@lem4968434 A B f s n h2)). Qed.
Lemma lem4968436 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term7 A B f s n) : term9 A B f s n.
Proof. exact (fun h0 : term0 A B => @lem4968435 A B f s n h0 h1). Qed.
Lemma lem4968437 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4968438 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) (h2 : term7 A B f s n) : term8 A B f s n.
Proof. exact (@lem4968436 A B f s n h2 (@lem4968437 A B h1)). Qed.
Lemma lem4968439 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term0 A B) : term6 A B f s n.
Proof. exact (fun h0 : term7 A B f s n => @lem4968438 A B f s n h1 h0). Qed.
Lemma lem4968440 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun n : nat => @lem4968439 A B f s n h1). Qed.
Lemma lem4968441 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem4968440 A B f s h1). Qed.
Lemma lem4968442 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem4968441 A B f h1). Qed.
Lemma lem4968443 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term0 A B => @lem4968442 A B h0). Qed.
Lemma lem4968444 {A B : Type'} : term0 A B.
Proof. exact (@lem4968443 A B (@lem4004559 A B)). Qed.
Lemma lem4968445 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem4968444 A B f). Qed.
Lemma lem4968446 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4968447 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem4968446 A B f) (@lem4968445 A B f)). Qed.
Lemma lem4968448 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem4968447 A B f s). Qed.
Lemma lem4968449 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4968450 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem4968449 A B f s) (@lem4968448 A B f s)). Qed.
Lemma lem4968451 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term5 A B f s n.
Proof. exact (@lem4968450 A B f s n). Qed.
Lemma lem4968452 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term5 A B f s n) = (term6 A B f s n).
Proof. exact (eq_refl (term5 A B f s n)). Qed.
Lemma lem4968454 {A B : Type'} : term11 A B.
Proof. exact (@lem4944739 A B). Qed.
Lemma lem4968455 {A B : Type'} (s : A -> Prop) : term12 A B s.
Proof. exact (@lem4968454 A B s). Qed.
Lemma lem4968456 {A B : Type'} (s : A -> Prop) : (term12 A B s) = (term13 A B s).
Proof. exact (eq_refl (term12 A B s)). Qed.
Lemma lem4968457 {A B : Type'} (s : A -> Prop) : term13 A B s.
Proof. exact (EQ_MP (@lem4968456 A B s) (@lem4968455 A B s)). Qed.
Lemma lem4968458 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term14 A B s t.
Proof. exact (@lem4968457 A B s t). Qed.
Lemma lem4968459 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term14 A B s t) = (term15 A B t s).
Proof. exact (eq_refl (term14 A B s t)). Qed.
Lemma lem4968460 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term15 A B t s.
Proof. exact (EQ_MP (@lem4968459 A B t s) (@lem4968458 A B s t)). Qed.
Lemma lem4968461 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term16 A B t s f.
Proof. exact (@lem4968460 A B t s f). Qed.
Lemma lem4968462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term16 A B t s f) = (term17 A B t s f).
Proof. exact (eq_refl (term16 A B t s f)). Qed.
Lemma lem4968463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term17 A B t s f.
Proof. exact (EQ_MP (@lem4968462 A B t s f) (@lem4968461 A B t s f)). Qed.
Lemma lem4968464 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term18 A B t s P f n) : term18 A B t s P f n.
Proof. exact (h1). Qed.
Lemma lem4968465 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term19 A B t s P f n) : term19 A B t s P f n.
Proof. exact (h1). Qed.
Lemma lem4968466 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4968467 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term20 A B t s P f n) : term20 A B t s P f n.
Proof. exact (h1). Qed.
Lemma lem4968468 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4968469 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term21 A B t s P f n) : term21 A B t s P f n.
Proof. exact (h1). Qed.
Lemma lem4968470 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem4968471 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term22 A B s P f n) : term22 A B s P f n.
Proof. exact (h1). Qed.
Lemma lem4968472 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term23 A B f s t) : term23 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4968473 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : term24 A B s P f n.
Proof. exact (h1). Qed.
Lemma lem4968474 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : term25 A B s f.
Proof. exact (h1). Qed.
Lemma lem4968475 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : (term26 B t P) = (term27 A B s P f)) : (term26 B t P) = (term27 A B s P f).
Proof. exact (h1). Qed.
Lemma lem4968476 {B : Type'} (n : nat) : (term28 B n) = (term28 B n).
Proof. exact (eq_refl (term28 B n)). Qed.
Lemma lem4968477 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : (term26 B t P) = (term27 A B s P f)) : (term29 B n t P) = (term30 A B n s P f).
Proof. exact (MK_COMB (@lem4968476 B n) (@lem4968475 A B t s P f h1)). Qed.
Lemma lem4968478 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term30 A B n s P f) = (term31 A B s P f n).
Proof. exact (eq_refl (term30 A B n s P f)). Qed.
Lemma lem4968479 {B : Type'} (n : nat) (t : B -> Prop) (P : B -> Prop) : (term32 B n t P) = (term32 B n t P).
Proof. exact (eq_refl (term32 B n t P)). Qed.
Lemma lem4968480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : ((term29 B n t P) = (term30 A B n s P f)) = ((term29 B n t P) = (term31 A B s P f n)).
Proof. exact (MK_COMB (@lem4968479 B n t P) (@lem4968478 A B s P f n)). Qed.
Lemma lem4968481 {B : Type'} (t : B -> Prop) (P : B -> Prop) (n : nat) : (term29 B n t P) = (term33 B t P n).
Proof. exact (eq_refl (term29 B n t P)). Qed.
Lemma lem4968482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4968483 {B : Type'} (t : B -> Prop) (P : B -> Prop) (n : nat) : (term32 B n t P) = (term34 B t P n).
Proof. exact (MK_COMB (@lem4968482) (@lem4968481 B t P n)). Qed.
Lemma lem4968484 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term31 A B s P f n) = (term31 A B s P f n).
Proof. exact (eq_refl (term31 A B s P f n)). Qed.
Lemma lem4968485 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : ((term29 B n t P) = (term31 A B s P f n)) = ((term33 B t P n) = (term31 A B s P f n)).
Proof. exact (MK_COMB (@lem4968483 B t P n) (@lem4968484 A B s P f n)). Qed.
Lemma lem4968486 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : ((term29 B n t P) = (term30 A B n s P f)) = ((term33 B t P n) = (term31 A B s P f n)).
Proof. exact (TRANS (@lem4968480 A B t s P f n) (@lem4968485 A B t s P f n)). Qed.
Lemma lem4968487 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : (term26 B t P) = (term27 A B s P f)) : (term33 B t P n) = (term31 A B s P f n).
Proof. exact (EQ_MP (@lem4968486 A B t s P f n) (@lem4968477 A B n t s P f h1)). Qed.
Lemma lem4968488 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : (term26 B t P) = (term27 A B s P f)) : (term31 A B s P f n) = (term33 B t P n).
Proof. exact (SYM (@lem4968487 A B n t s P f h1)). Qed.
Lemma lem4968489 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4968491 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem4968493 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term23 A B f s t) = ((term23 A B f s t) = True).
Proof. exact (@lem7 (term23 A B f s t)). Qed.
Lemma lem4968495 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : term35 A B s f x.
Proof. exact (@lem4968474 A B s f h1 x). Qed.
Lemma lem4968496 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term35 A B s f x) = (term36 A B s f x).
Proof. exact (eq_refl (term35 A B s f x)). Qed.
Lemma lem4968497 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : term36 A B s f x.
Proof. exact (EQ_MP (@lem4968496 A B s f x) (@lem4968495 A B x s f h1)). Qed.
Lemma lem4968498 {A B : Type'} (x : A) (y : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : term37 A B s f x y.
Proof. exact (@lem4968497 A B x s f h1 y). Qed.
Lemma lem4968499 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term37 A B s f x y) = (term38 A B s f x y).
Proof. exact (eq_refl (term37 A B s f x y)). Qed.
Lemma lem4968500 {A B : Type'} (x : A) (y : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : term38 A B s f x y.
Proof. exact (EQ_MP (@lem4968499 A B s f x y) (@lem4968498 A B x y s f h1)). Qed.
Lemma lem4968501 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term38 A B s f x y) = ((term38 A B s f x y) = True).
Proof. exact (@lem7 (term38 A B s f x y)). Qed.
Lemma lem4968512 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4968489 A s) (@lem4968466 A s h1)). Qed.
Lemma lem4968513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968514 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term39 A s) = (and True).
Proof. exact (MK_COMB (@lem4968513) (@lem4968512 A s h1)). Qed.
Lemma lem4968518 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4968491 B t) (@lem4968468 B t h1)). Qed.
Lemma lem4968519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968520 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term39 B t) = (and True).
Proof. exact (MK_COMB (@lem4968519) (@lem4968518 B t h1)). Qed.
Lemma lem4968526 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem4968527 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4968528 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term40 A s) = (term40 B t).
Proof. exact (MK_COMB (@lem4968527) (@lem4968526 A B s t h1)). Qed.
Lemma lem4968529 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem4968530 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = ((@CARD B t) = (@CARD B t)).
Proof. exact (MK_COMB (@lem4968528 A B s t h1) (@lem4968529 B t)). Qed.
Lemma lem4968532 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4968533 (x : nat) : (x = x) = True.
Proof. exact (@lem4968532 nat x). Qed.
Lemma lem4968534 {B : Type'} (t : B -> Prop) : ((@CARD B t) = (@CARD B t)) = True.
Proof. exact (@lem4968533 (@CARD B t)). Qed.
Lemma lem4968535 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = True.
Proof. exact (TRANS (@lem4968530 A B s t h1) (@lem4968534 B t)). Qed.
Lemma lem4968536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term41 A B s t) = (and True).
Proof. exact (MK_COMB (@lem4968536) (@lem4968535 A B s t h1)). Qed.
Lemma lem4968539 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term23 A B f s t) : (term23 A B f s t) = True.
Proof. exact (EQ_MP (@lem4968493 A B f s t) (@lem4968472 A B f s t h1)). Qed.
Lemma lem4968540 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : term23 A B f s t) : (term42 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4968537 A B s t h1) (@lem4968539 A B f s t h2)). Qed.
Lemma lem4968542 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4968543 : (True /\ True) = True.
Proof. exact (@lem4968542 True). Qed.
Lemma lem4968544 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : term23 A B f s t) : (term42 A B f s t) = True.
Proof. exact (TRANS (@lem4968540 A B f s t h1 h2) (@lem4968543)). Qed.
Lemma lem4968545 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : (@CARD A s) = (@CARD B t)) (h3 : term23 A B f s t) : (term43 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4968520 B t h1) (@lem4968544 A B f s t h2 h3)). Qed.
Lemma lem4968547 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4968548 : (True /\ True) = True.
Proof. exact (@lem4968547 True). Qed.
Lemma lem4968549 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : (@CARD A s) = (@CARD B t)) (h3 : term23 A B f s t) : (term43 A B f s t) = True.
Proof. exact (TRANS (@lem4968545 A B f s t h1 h2 h3) (@lem4968548)). Qed.
Lemma lem4968550 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term23 A B f s t) : (term44 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4968514 A s h1) (@lem4968549 A B f s t h2 h3 h4)). Qed.
Lemma lem4968552 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4968553 : (True /\ True) = True.
Proof. exact (@lem4968552 True). Qed.
Lemma lem4968554 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term23 A B f s t) : (term44 A B f s t) = True.
Proof. exact (TRANS (@lem4968550 A B f s t h1 h2 h3 h4) (@lem4968553)). Qed.
Lemma lem4968555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968556 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term23 A B f s t) : (term45 A B f s t) = (imp True).
Proof. exact (MK_COMB (@lem4968555) (@lem4968554 A B f s t h1 h2 h3 h4)). Qed.
Lemma lem4968582 {A B : Type'} (x : A) (y : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term38 A B s f x y) = True.
Proof. exact (EQ_MP (@lem4968501 A B s f x y) (@lem4968500 A B x y s f h1)). Qed.
Lemma lem4968583 {A B : Type'} (x : A) (y : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term38 A B s f x y) = True.
Proof. exact (@lem4968582 A B x y s f h1). Qed.
Lemma lem4968584 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term46 A B s f x) = (term47 A).
Proof. exact (fun_ext (fun y : A => @lem4968583 A B x y s f h1)). Qed.
Lemma lem4968585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4968586 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term36 A B s f x) = (term48 A).
Proof. exact (MK_COMB (@lem4968585 A) (@lem4968584 A B x s f h1)). Qed.
Lemma lem4968588 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4968589 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (@lem4968588 A t). Qed.
Lemma lem4968590 {A : Type'} : (term48 A) = True.
Proof. exact (@lem4968589 A True). Qed.
Lemma lem4968591 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term36 A B s f x) = True.
Proof. exact (TRANS (@lem4968586 A B x s f h1) (@lem4968590 A)). Qed.
Lemma lem4968592 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term50 A B s f) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem4968591 A B x s f h1)). Qed.
Lemma lem4968593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4968594 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term25 A B s f) = (term48 A).
Proof. exact (MK_COMB (@lem4968593 A) (@lem4968592 A B s f h1)). Qed.
Lemma lem4968596 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4968597 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (@lem4968596 A t). Qed.
Lemma lem4968598 {A : Type'} : (term48 A) = True.
Proof. exact (@lem4968597 A True). Qed.
Lemma lem4968599 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : (term25 A B s f) = True.
Proof. exact (TRANS (@lem4968594 A B s f h1) (@lem4968598 A)). Qed.
Lemma lem4968600 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term51 A B t s f) = (term51 A B t s f).
Proof. exact (eq_refl (term51 A B t s f)). Qed.
Lemma lem4968601 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : ((term52 A B t s f) = (term25 A B s f)) = ((term52 A B t s f) = True).
Proof. exact (MK_COMB (@lem4968600 A B t s f) (@lem4968599 A B s f h1)). Qed.
Lemma lem4968603 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4968604 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term52 A B t s f) = True) = (term52 A B t s f).
Proof. exact (@lem4968603 (term52 A B t s f)). Qed.
Lemma lem4968619 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term25 A B s f) : ((term52 A B t s f) = (term25 A B s f)) = (term52 A B t s f).
Proof. exact (TRANS (@lem4968601 A B t s f h1) (@lem4968604 A B t s f)). Qed.
Lemma lem4968620 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term17 A B t s f) = (term53 A B t s f).
Proof. exact (MK_COMB (@lem4968556 A B f s t h2 h3 h4 h5) (@lem4968619 A B t s f h1)). Qed.
Lemma lem4968622 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4968623 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term53 A B t s f) = (term52 A B t s f).
Proof. exact (@lem4968622 (term52 A B t s f)). Qed.
Lemma lem4968638 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term17 A B t s f) = (term52 A B t s f).
Proof. exact (TRANS (@lem4968620 A B f s t h1 h2 h3 h4 h5) (@lem4968623 A B t s f)). Qed.
Lemma lem4968639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968640 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term54 A B t s f) = (term55 A B t s f).
Proof. exact (MK_COMB (@lem4968639) (@lem4968638 A B f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem4968655 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term26 B t P) = (term27 A B s P f)) = ((term26 B t P) = (term27 A B s P f)).
Proof. exact (eq_refl ((term26 B t P) = (term27 A B s P f))). Qed.
Lemma lem4968656 {A B : Type'} (P : B -> Prop) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term56 A B t s P f) = (term57 A B t s P f).
Proof. exact (MK_COMB (@lem4968640 A B f s t h1 h2 h3 h4 h5) (@lem4968655 A B t s P f)). Qed.
Lemma lem4968659 {A B : Type'} (P : B -> Prop) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term57 A B t s P f) = (term56 A B t s P f).
Proof. exact (SYM (@lem4968656 A B P f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem4968660 (t1 : Prop) : term58 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4968661 (t1 : Prop) : (term58 t1) = (term59 t1).
Proof. exact (eq_refl (term58 t1)). Qed.
Lemma lem4968662 (t1 : Prop) : term59 t1.
Proof. exact (EQ_MP (@lem4968661 t1) (@lem4968660 t1)). Qed.
Lemma lem4968663 (t1 : Prop) (t2 : Prop) : term60 t1 t2.
Proof. exact (@lem4968662 t1 t2). Qed.
Lemma lem4968664 (t1 : Prop) (t2 : Prop) : (term60 t1 t2) = (term61 t1 t2).
Proof. exact (eq_refl (term60 t1 t2)). Qed.
Lemma lem4968665 (t1 : Prop) (t2 : Prop) : term61 t1 t2.
Proof. exact (EQ_MP (@lem4968664 t1 t2) (@lem4968663 t1 t2)). Qed.
Lemma lem4968666 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term62 t1 t2 t3.
Proof. exact (@lem4968665 t1 t2 t3). Qed.
Lemma lem4968667 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term62 t1 t2 t3) = ((term63 t1 t2 t3) = (term64 t1 t2 t3)).
Proof. exact (eq_refl (term62 t1 t2 t3)). Qed.
Lemma lem4968668 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term63 t1 t2 t3) = (term64 t1 t2 t3).
Proof. exact (EQ_MP (@lem4968667 t1 t2 t3) (@lem4968666 t1 t2 t3)). Qed.
Lemma lem4968669 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term64 t1 t2 t3) = (term63 t1 t2 t3).
Proof. exact (SYM (@lem4968668 t1 t2 t3)). Qed.
Lemma lem4968670 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term65 A B t s.
Proof. exact (conj (@lem4968468 B t h2) (@lem4968466 A s h1)). Qed.
Lemma lem4968671 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term66 A B t s.
Proof. exact (conj (@lem4968470 A B s t h3) (@lem4968670 A B s t h1 h2)). Qed.
Lemma lem4968672 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term23 A B f s t) : term67 A B f t s.
Proof. exact (conj (@lem4968472 A B f s t h4) (@lem4968671 A B s t h1 h2 h3)). Qed.
Lemma lem4968673 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : term68 A B f t s.
Proof. exact (conj (@lem4968474 A B s f h1) (@lem4968672 A B f s t h2 h3 h4 h5)). Qed.
Lemma lem4968674 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term69 A B P n f t s.
Proof. exact (conj (@lem4968473 A B s P f n h5) (@lem4968673 A B f s t h1 h2 h3 h4 h6)). Qed.
Lemma lem4968712 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term70 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4968713 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term70 B s t).
Proof. exact (@lem4968712 B s t). Qed.
Lemma lem4968714 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term23 A B f s t) = (term71 A B f s t).
Proof. exact (@lem4968713 B (@IMAGE A B f s) t). Qed.
Lemma lem4968721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968722 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term72 A B f s t) = (term73 A B f s t).
Proof. exact (MK_COMB (@lem4968721) (@lem4968714 A B f s t)). Qed.
Lemma lem4968731 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4968732 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term67 A B f t s) = (term74 A B f t s).
Proof. exact (MK_COMB (@lem4968722 A B f s t) (@lem4968731 A B t s)). Qed.
Lemma lem4968735 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term75 A B s f) = (term75 A B s f).
Proof. exact (eq_refl (term75 A B s f)). Qed.
Lemma lem4968736 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term68 A B f t s) = (term76 A B f t s).
Proof. exact (MK_COMB (@lem4968735 A B s f) (@lem4968732 A B f t s)). Qed.
Lemma lem4968739 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term77 A B s P f n) = (term77 A B s P f n).
Proof. exact (eq_refl (term77 A B s P f n)). Qed.
Lemma lem4968740 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term69 A B P n f t s) = (term78 A B P n f t s).
Proof. exact (MK_COMB (@lem4968739 A B s P f n) (@lem4968736 A B f t s)). Qed.
Lemma lem4968743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968744 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term79 A B P n f t s) = (term80 A B P n f t s).
Proof. exact (MK_COMB (@lem4968743) (@lem4968740 A B P n f t s)). Qed.
Lemma lem4968766 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term81 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4968767 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term81 B s t).
Proof. exact (@lem4968766 B s t). Qed.
Lemma lem4968768 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term26 B t P) = (term27 A B s P f)) = (term82 A B t s P f).
Proof. exact (@lem4968767 B (term26 B t P) (term27 A B s P f)). Qed.
Lemma lem4968789 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term55 A B t s f) = (term55 A B t s f).
Proof. exact (eq_refl (term55 A B t s f)). Qed.
Lemma lem4968790 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term57 A B t s P f) = (term83 A B t s P f).
Proof. exact (MK_COMB (@lem4968789 A B t s f) (@lem4968768 A B t s P f)). Qed.
Lemma lem4968793 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term84 A B n t s P f) = (term85 A B n t s P f).
Proof. exact (MK_COMB (@lem4968744 A B P n f t s) (@lem4968790 A B t s P f)). Qed.
Lemma lem4968796 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term85 A B n t s P f) = (term84 A B n t s P f).
Proof. exact (SYM (@lem4968793 A B n t s P f)). Qed.
Lemma lem4968808 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968809 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4968808 A P x). Qed.
Lemma lem4968810 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4968809 A s x). Qed.
Lemma lem4968811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968812 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4968811) (@lem4968810 A s x)). Qed.
Lemma lem4968813 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term88 A B P f x).
Proof. exact (eq_refl (term88 A B P f x)). Qed.
Lemma lem4968814 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term89 A B s P f x) = (term90 A B s P f x).
Proof. exact (MK_COMB (@lem4968812 A s x) (@lem4968813 A B P f x)). Qed.
Lemma lem4968817 {A : Type'} (GEN_PVAR_217 : A) : (@SETSPEC A GEN_PVAR_217) = (@SETSPEC A GEN_PVAR_217).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_217)). Qed.
Lemma lem4968818 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term91 A B GEN_PVAR_217 s P f x) = (term92 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4968817 A GEN_PVAR_217) (@lem4968814 A B s P f x)). Qed.
Lemma lem4968819 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4968820 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term93 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4968818 A B GEN_PVAR_217 s P f x) (@lem4968819 A x)). Qed.
Lemma lem4968821 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term95 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4968820 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4968822 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4968823 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term97 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4968822 A) (@lem4968821 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4968828 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term99 A B s P f) = (term100 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4968823 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4968829 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4968830 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term101 A B s P f) = (term102 A B s P f).
Proof. exact (MK_COMB (@lem4968829 A) (@lem4968828 A B s P f)). Qed.
Lemma lem4968831 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4968832 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term103 A B s P f) = (term104 A B s P f).
Proof. exact (MK_COMB (@lem4968831 A) (@lem4968830 A B s P f)). Qed.
Lemma lem4968833 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4968834 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term24 A B s P f n) = (term105 A B s P f n).
Proof. exact (MK_COMB (@lem4968832 A B s P f) (@lem4968833 n)). Qed.
Lemma lem4968835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968836 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term77 A B s P f n) = (term106 A B s P f n).
Proof. exact (MK_COMB (@lem4968835) (@lem4968834 A B s P f n)). Qed.
Lemma lem4968852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968853 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4968852 A P x). Qed.
Lemma lem4968854 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4968853 A s x). Qed.
Lemma lem4968855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968856 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4968855) (@lem4968854 A s x)). Qed.
Lemma lem4968860 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968861 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4968860 A P x). Qed.
Lemma lem4968862 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4968861 A s y). Qed.
Lemma lem4968863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968864 {A : Type'} (s : A -> Prop) (y : A) : (term86 A y s) = (term87 A s y).
Proof. exact (MK_COMB (@lem4968863) (@lem4968862 A s y)). Qed.
Lemma lem4968867 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem4968868 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term107 A B s x f y) = (term108 A B s x f y).
Proof. exact (MK_COMB (@lem4968864 A s y) (@lem4968867 A B x f y)). Qed.
Lemma lem4968871 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term109 A B s x f y) = (term110 A B s x f y).
Proof. exact (MK_COMB (@lem4968856 A s x) (@lem4968868 A B s x f y)). Qed.
Lemma lem4968874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968875 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term111 A B s x f y) = (term112 A B s x f y).
Proof. exact (MK_COMB (@lem4968874) (@lem4968871 A B s x f y)). Qed.
Lemma lem4968878 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4968879 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term38 A B s f x y) = (term113 A B s f x y).
Proof. exact (MK_COMB (@lem4968875 A B s x f y) (@lem4968878 A x y)). Qed.
Lemma lem4968882 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term46 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4968879 A B s f x y)). Qed.
Lemma lem4968883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4968884 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term36 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4968883 A) (@lem4968882 A B s f x)). Qed.
Lemma lem4968889 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4968884 A B s f x)). Qed.
Lemma lem4968890 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4968891 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term25 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4968890 A) (@lem4968889 A B s f)). Qed.
Lemma lem4968896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968897 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term75 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4968896) (@lem4968891 A B s f)). Qed.
Lemma lem4968907 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4968908 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (@lem4968907 A B y f s). Qed.
Lemma lem4968909 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term120 A B x f s).
Proof. exact (@lem4968908 A B x f s). Qed.
Lemma lem4968919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968920 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4968919 A P x). Qed.
Lemma lem4968921 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4968920 A s x). Qed.
Lemma lem4968922 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term121 A B x f x') = (term121 A B x f x').
Proof. exact (eq_refl (term121 A B x f x')). Qed.
Lemma lem4968923 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term122 A B x f x' s) = (term123 A B x f s x').
Proof. exact (MK_COMB (@lem4968922 A B x f x') (@lem4968921 A s x')). Qed.
Lemma lem4968926 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4968923 A B x f s x')). Qed.
Lemma lem4968927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4968928 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4968927 A) (@lem4968926 A B x f s)). Qed.
Lemma lem4968933 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term126 A B x f s).
Proof. exact (TRANS (@lem4968909 A B x f s) (@lem4968928 A B x f s)). Qed.
Lemma lem4968934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968935 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4968934) (@lem4968933 A B x f s)). Qed.
Lemma lem4968937 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968938 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4968937 B P x). Qed.
Lemma lem4968939 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4968938 B t x). Qed.
Lemma lem4968940 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term129 A B f s x t) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4968935 A B x f s) (@lem4968939 B t x)). Qed.
Lemma lem4968943 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term131 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4968940 A B f s t x)). Qed.
Lemma lem4968944 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4968945 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term71 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4968944 B) (@lem4968943 A B f s t)). Qed.
Lemma lem4968950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968951 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term73 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4968950) (@lem4968945 A B f s t)). Qed.
Lemma lem4968958 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4968959 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term74 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4968951 A B f s t) (@lem4968958 A B t s)). Qed.
Lemma lem4968962 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term76 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4968897 A B s f) (@lem4968959 A B f t s)). Qed.
Lemma lem4968965 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term78 A B P n f t s) = (term137 A B P n f t s).
Proof. exact (MK_COMB (@lem4968836 A B s P f n) (@lem4968962 A B f t s)). Qed.
Lemma lem4968968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968969 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term80 A B P n f t s) = (term138 A B P n f t s).
Proof. exact (MK_COMB (@lem4968968) (@lem4968965 A B P n f t s)). Qed.
Lemma lem4968979 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968980 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4968979 B P x). Qed.
Lemma lem4968981 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem4968980 B t y). Qed.
Lemma lem4968982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968983 {B : Type'} (t : B -> Prop) (y : B) : (term139 B y t) = (term140 B t y).
Proof. exact (MK_COMB (@lem4968982) (@lem4968981 B t y)). Qed.
Lemma lem4968991 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4968992 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4968991 A P x). Qed.
Lemma lem4968993 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4968992 A s x). Qed.
Lemma lem4968994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968995 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4968994) (@lem4968993 A s x)). Qed.
Lemma lem4968998 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem4968999 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term141 A B s f x y) = (term142 A B s f x y).
Proof. exact (MK_COMB (@lem4968995 A s x) (@lem4968998 A B f x y)). Qed.
Lemma lem4969002 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term143 A B s f y) = (term144 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4968999 A B s f x y)). Qed.
Lemma lem4969003 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969004 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term145 A B s f y) = (term146 A B s f y).
Proof. exact (MK_COMB (@lem4969003 A) (@lem4969002 A B s f y)). Qed.
Lemma lem4969009 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term147 A B t s f y) = (term148 A B t s f y).
Proof. exact (MK_COMB (@lem4968983 B t y) (@lem4969004 A B s f y)). Qed.
Lemma lem4969012 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term149 A B t s f) = (term150 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4969009 A B t s f y)). Qed.
Lemma lem4969013 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969014 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term52 A B t s f) = (term151 A B t s f).
Proof. exact (MK_COMB (@lem4969013 B) (@lem4969012 A B t s f)). Qed.
Lemma lem4969019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969020 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term55 A B t s f) = (term152 A B t s f).
Proof. exact (MK_COMB (@lem4969019) (@lem4969014 A B t s f)). Qed.
Lemma lem4969028 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term153 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4969029 {B : Type'} (p : B -> Prop) (x : B) : (term153 B x p) = (p x).
Proof. exact (@lem4969028 B p x). Qed.
Lemma lem4969030 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term154 B x t P) = (term155 B t P x).
Proof. exact (@lem4969029 B (term156 B t P) x). Qed.
Lemma lem4969031 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term155 B t P x) = (term157 B t P x).
Proof. exact (eq_refl (term155 B t P x)). Qed.
Lemma lem4969032 {B : Type'} (GEN_PVAR_215 : B) : (@SETSPEC B GEN_PVAR_215) = (@SETSPEC B GEN_PVAR_215).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_215)). Qed.
Lemma lem4969033 {B : Type'} (GEN_PVAR_215 : B) (t : B -> Prop) (P : B -> Prop) (x : B) : (term158 B GEN_PVAR_215 t P x) = (term159 B GEN_PVAR_215 t P x).
Proof. exact (MK_COMB (@lem4969032 B GEN_PVAR_215) (@lem4969031 B t P x)). Qed.
Lemma lem4969034 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4969035 {B : Type'} (GEN_PVAR_215 : B) (t : B -> Prop) (P : B -> Prop) (x : B) : (term160 B GEN_PVAR_215 t P x) = (term161 B GEN_PVAR_215 t P x).
Proof. exact (MK_COMB (@lem4969033 B GEN_PVAR_215 t P x) (@lem4969034 B x)). Qed.
Lemma lem4969036 {B : Type'} (GEN_PVAR_215 : B) (t : B -> Prop) (P : B -> Prop) : (term162 B GEN_PVAR_215 t P) = (term163 B GEN_PVAR_215 t P).
Proof. exact (fun_ext (fun x : B => @lem4969035 B GEN_PVAR_215 t P x)). Qed.
Lemma lem4969037 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4969038 {B : Type'} (GEN_PVAR_215 : B) (t : B -> Prop) (P : B -> Prop) : (term164 B GEN_PVAR_215 t P) = (term165 B GEN_PVAR_215 t P).
Proof. exact (MK_COMB (@lem4969037 B) (@lem4969036 B GEN_PVAR_215 t P)). Qed.
Lemma lem4969039 {B : Type'} (t : B -> Prop) (P : B -> Prop) : (term166 B t P) = (term167 B t P).
Proof. exact (fun_ext (fun GEN_PVAR_215 : B => @lem4969038 B GEN_PVAR_215 t P)). Qed.
Lemma lem4969040 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem4969041 {B : Type'} (t : B -> Prop) (P : B -> Prop) : (term168 B t P) = (term26 B t P).
Proof. exact (MK_COMB (@lem4969040 B) (@lem4969039 B t P)). Qed.
Lemma lem4969042 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem4969043 {B : Type'} (x : B) (t : B -> Prop) (P : B -> Prop) : (term154 B x t P) = (term169 B x t P).
Proof. exact (MK_COMB (@lem4969042 B x) (@lem4969041 B t P)). Qed.
Lemma lem4969044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969045 {B : Type'} (x : B) (t : B -> Prop) (P : B -> Prop) : (term170 B x t P) = (term171 B x t P).
Proof. exact (MK_COMB (@lem4969044) (@lem4969043 B x t P)). Qed.
Lemma lem4969046 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term155 B t P x) = (term157 B t P x).
Proof. exact (eq_refl (term155 B t P x)). Qed.
Lemma lem4969047 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : ((term154 B x t P) = (term155 B t P x)) = ((term169 B x t P) = (term157 B t P x)).
Proof. exact (MK_COMB (@lem4969045 B x t P) (@lem4969046 B t P x)). Qed.
Lemma lem4969048 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term169 B x t P) = (term157 B t P x).
Proof. exact (EQ_MP (@lem4969047 B t P x) (@lem4969030 B t P x)). Qed.
Lemma lem4969052 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4969053 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4969052 B P x). Qed.
Lemma lem4969054 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4969053 B t x). Qed.
Lemma lem4969055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969056 {B : Type'} (t : B -> Prop) (x : B) : (term86 B x t) = (term87 B t x).
Proof. exact (MK_COMB (@lem4969055) (@lem4969054 B t x)). Qed.
Lemma lem4969057 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem4969058 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term157 B t P x) = (term172 B t P x).
Proof. exact (MK_COMB (@lem4969056 B t x) (@lem4969057 B P x)). Qed.
Lemma lem4969061 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term169 B x t P) = (term172 B t P x).
Proof. exact (TRANS (@lem4969048 B t P x) (@lem4969058 B t P x)). Qed.
Lemma lem4969062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969063 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term171 B x t P) = (term173 B t P x).
Proof. exact (MK_COMB (@lem4969062) (@lem4969061 B t P x)). Qed.
Lemma lem4969065 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4969066 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (@lem4969065 A B y f s). Qed.
Lemma lem4969067 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term174 A B x s P f) = (term175 A B x s P f).
Proof. exact (@lem4969066 A B x f (term101 A B s P f)). Qed.
Lemma lem4969077 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term153 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4969078 {A : Type'} (p : A -> Prop) (x : A) : (term153 A x p) = (p x).
Proof. exact (@lem4969077 A p x). Qed.
Lemma lem4969079 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term176 A B x s P f) = (term177 A B s P f x).
Proof. exact (@lem4969078 A (term178 A B s P f) x). Qed.
Lemma lem4969080 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term177 A B s P f x) = (term89 A B s P f x).
Proof. exact (eq_refl (term177 A B s P f x)). Qed.
Lemma lem4969081 {A : Type'} (GEN_PVAR_216 : A) : (@SETSPEC A GEN_PVAR_216) = (@SETSPEC A GEN_PVAR_216).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_216)). Qed.
Lemma lem4969082 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term179 A B GEN_PVAR_216 s P f x) = (term91 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4969081 A GEN_PVAR_216) (@lem4969080 A B s P f x)). Qed.
Lemma lem4969083 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4969084 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term180 A B GEN_PVAR_216 s P f x) = (term93 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4969082 A B GEN_PVAR_216 s P f x) (@lem4969083 A x)). Qed.
Lemma lem4969085 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term181 A B GEN_PVAR_216 s P f) = (term95 A B GEN_PVAR_216 s P f).
Proof. exact (fun_ext (fun x : A => @lem4969084 A B GEN_PVAR_216 s P f x)). Qed.
Lemma lem4969086 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969087 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term182 A B GEN_PVAR_216 s P f) = (term97 A B GEN_PVAR_216 s P f).
Proof. exact (MK_COMB (@lem4969086 A) (@lem4969085 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4969088 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term183 A B s P f) = (term99 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_216 : A => @lem4969087 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4969089 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4969090 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term184 A B s P f) = (term101 A B s P f).
Proof. exact (MK_COMB (@lem4969089 A) (@lem4969088 A B s P f)). Qed.
Lemma lem4969091 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4969092 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term176 A B x s P f) = (term185 A B x s P f).
Proof. exact (MK_COMB (@lem4969091 A x) (@lem4969090 A B s P f)). Qed.
Lemma lem4969093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969094 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term186 A B x s P f) = (term187 A B x s P f).
Proof. exact (MK_COMB (@lem4969093) (@lem4969092 A B x s P f)). Qed.
Lemma lem4969095 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term177 A B s P f x) = (term89 A B s P f x).
Proof. exact (eq_refl (term177 A B s P f x)). Qed.
Lemma lem4969096 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : ((term176 A B x s P f) = (term177 A B s P f x)) = ((term185 A B x s P f) = (term89 A B s P f x)).
Proof. exact (MK_COMB (@lem4969094 A B x s P f) (@lem4969095 A B s P f x)). Qed.
Lemma lem4969097 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term185 A B x s P f) = (term89 A B s P f x).
Proof. exact (EQ_MP (@lem4969096 A B s P f x) (@lem4969079 A B s P f x)). Qed.
Lemma lem4969101 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4969102 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4969101 A P x). Qed.
Lemma lem4969103 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4969102 A s x). Qed.
Lemma lem4969104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969105 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4969104) (@lem4969103 A s x)). Qed.
Lemma lem4969106 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term88 A B P f x).
Proof. exact (eq_refl (term88 A B P f x)). Qed.
Lemma lem4969107 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term89 A B s P f x) = (term90 A B s P f x).
Proof. exact (MK_COMB (@lem4969105 A s x) (@lem4969106 A B P f x)). Qed.
Lemma lem4969110 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term185 A B x s P f) = (term90 A B s P f x).
Proof. exact (TRANS (@lem4969097 A B s P f x) (@lem4969107 A B s P f x)). Qed.
Lemma lem4969111 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term121 A B x f x') = (term121 A B x f x').
Proof. exact (eq_refl (term121 A B x f x')). Qed.
Lemma lem4969112 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term188 A B x x' s P f) = (term189 A B x s P f x').
Proof. exact (MK_COMB (@lem4969111 A B x f x') (@lem4969110 A B s P f x')). Qed.
Lemma lem4969115 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term190 A B x s P f) = (term191 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4969112 A B x s P f x')). Qed.
Lemma lem4969116 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969117 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term175 A B x s P f) = (term192 A B x s P f).
Proof. exact (MK_COMB (@lem4969116 A) (@lem4969115 A B x s P f)). Qed.
Lemma lem4969122 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term174 A B x s P f) = (term192 A B x s P f).
Proof. exact (TRANS (@lem4969067 A B x s P f) (@lem4969117 A B x s P f)). Qed.
Lemma lem4969123 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term169 B x t P) = (term174 A B x s P f)) = ((term172 B t P x) = (term192 A B x s P f)).
Proof. exact (MK_COMB (@lem4969063 B t P x) (@lem4969122 A B x s P f)). Qed.
Lemma lem4969126 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term193 A B t s P f) = (term194 A B t s P f).
Proof. exact (fun_ext (fun x : B => @lem4969123 A B t x s P f)). Qed.
Lemma lem4969127 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969128 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term82 A B t s P f) = (term195 A B t s P f).
Proof. exact (MK_COMB (@lem4969127 B) (@lem4969126 A B t s P f)). Qed.
Lemma lem4969133 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term83 A B t s P f) = (term196 A B t s P f).
Proof. exact (MK_COMB (@lem4969020 A B t s f) (@lem4969128 A B t s P f)). Qed.
Lemma lem4969136 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term85 A B n t s P f) = (term197 A B n t s P f).
Proof. exact (MK_COMB (@lem4968969 A B P n f t s) (@lem4969133 A B t s P f)). Qed.
Lemma lem4969139 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term197 A B n t s P f) = (term85 A B n t s P f).
Proof. exact (SYM (@lem4969136 A B n t s P f)). Qed.
Lemma lem4969141 (p : Prop) : p = (term198 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4969142 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term197 A B n t s P f) = (term199 A B n t s P f).
Proof. exact (@lem4969141 (term197 A B n t s P f)). Qed.
Lemma lem4969143 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term199 A B n t s P f) = (term197 A B n t s P f).
Proof. exact (SYM (@lem4969142 A B n t s P f)). Qed.
Lemma lem4969144 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term200 A B n t s P f) : term200 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4969147 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term199 A B n t s P f) : term199 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4969148 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term201 A B n t s P f.
Proof. exact (fun h0 : term199 A B n t s P f => @lem4969147 A B n t s P f h0). Qed.
Lemma lem4969149 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term201 A B n t s P f) : term201 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4969150 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term199 A B n t s P f) : term199 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4969151 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term199 A B n t s P f) (h2 : term201 A B n t s P f) : term199 A B n t s P f.
Proof. exact (@lem4969149 A B n t s P f h2 (@lem4969150 A B n t s P f h1)). Qed.
Lemma lem4969152 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term199 A B n t s P f) : term202 A B n t s P f.
Proof. exact (fun h0 : term201 A B n t s P f => @lem4969151 A B n t s P f h1 h0). Qed.
Lemma lem4969153 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term201 A B n t s P f) : term201 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4969154 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term199 A B n t s P f) (h2 : term201 A B n t s P f) : term199 A B n t s P f.
Proof. exact (@lem4969152 A B n t s P f h1 (@lem4969153 A B n t s P f h2)). Qed.
Lemma lem4969155 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term201 A B n t s P f) : term201 A B n t s P f.
Proof. exact (fun h0 : term199 A B n t s P f => @lem4969154 A B n t s P f h0 h1). Qed.
Lemma lem4969156 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term203 A B n t s P f.
Proof. exact (fun h0 : term201 A B n t s P f => @lem4969155 A B n t s P f h0). Qed.
Lemma lem4969159 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term201 A B n t s P f.
Proof. exact (@lem4969156 A B n t s P f (@lem4969148 A B n t s P f)). Qed.
Lemma lem4969160 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term201 A B n t s P f.
Proof. exact (@lem4969159 A B n t s P f). Qed.
Lemma lem4969182 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4969183 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term199 A B n t s P f) = (term204 A B n t s P f).
Proof. exact (@lem4969182 (term200 A B n t s P f)). Qed.
Lemma lem4969185 (t : Prop) : (term205 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4969186 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term204 A B n t s P f) = (term197 A B n t s P f).
Proof. exact (@lem4969185 (term197 A B n t s P f)). Qed.
Lemma lem4969189 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term199 A B n t s P f) = (term197 A B n t s P f).
Proof. exact (TRANS (@lem4969183 A B n t s P f) (@lem4969186 A B n t s P f)). Qed.
Lemma lem4969356 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term206 A B t s P f) = (term207 A B t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4969189 A B n t s P f)). Qed.
Lemma lem4969357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4969358 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term208 A B t s P f) = (term209 A B t s P f).
Proof. exact (MK_COMB (@lem4969357) (@lem4969356 A B t s P f)). Qed.
Lemma lem4969363 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term210 A B s P f) = (term211 A B s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4969358 A B t s P f)). Qed.
Lemma lem4969364 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969365 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term212 A B s P f) = (term213 A B s P f).
Proof. exact (MK_COMB (@lem4969364 B) (@lem4969363 A B s P f)). Qed.
Lemma lem4969370 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term214 A B P f) = (term215 A B P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969365 A B s P f)). Qed.
Lemma lem4969371 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969372 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term216 A B P f) = (term217 A B P f).
Proof. exact (MK_COMB (@lem4969371 A) (@lem4969370 A B P f)). Qed.
Lemma lem4969377 {A B : Type'} (f : A -> B) : (term218 A B f) = (term219 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969372 A B P f)). Qed.
Lemma lem4969378 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969379 {A B : Type'} (f : A -> B) : (term220 A B f) = (term221 A B f).
Proof. exact (MK_COMB (@lem4969378 B) (@lem4969377 A B f)). Qed.
Lemma lem4969384 {A B : Type'} : (term222 A B) = (term223 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4969379 A B f)). Qed.
Lemma lem4969385 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969392 {A B : Type'} : (term224 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem4969385 A B) (@lem4969384 A B)). Qed.
Lemma lem4969393 {A B : Type'} (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : _62510 = (term226 A B).
Proof. exact (h1). Qed.
Lemma lem4969394 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4969395 {A B : Type'} (s : A -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s) = (term227 A B s).
Proof. exact (MK_COMB (@lem4969393 A B _62510 h1) (@lem4969394 A s)). Qed.
Lemma lem4969396 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4969397 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term229 A B _62510 s) = (term229 A B _62510 s).
Proof. exact (eq_refl (term229 A B _62510 s)). Qed.
Lemma lem4969398 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term227 A B s)) = ((_62510 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4969397 A B _62510 s) (@lem4969396 A B s)). Qed.
Lemma lem4969399 {A B : Type'} (s : A -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s) = (term228 A B s).
Proof. exact (EQ_MP (@lem4969398 A B _62510 s) (@lem4969395 A B s _62510 h1)). Qed.
Lemma lem4969400 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4969401 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s P) = (term230 A B s P).
Proof. exact (MK_COMB (@lem4969399 A B s _62510 h1) (@lem4969400 B P)). Qed.
Lemma lem4969402 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4969403 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62510 s P) = (term232 A B _62510 s P).
Proof. exact (eq_refl (term232 A B _62510 s P)). Qed.
Lemma lem4969404 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term230 A B s P)) = ((_62510 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4969403 A B _62510 s P) (@lem4969402 A B s P)). Qed.
Lemma lem4969405 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s P) = (term231 A B s P).
Proof. exact (EQ_MP (@lem4969404 A B _62510 s P) (@lem4969401 A B s P _62510 h1)). Qed.
Lemma lem4969406 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4969407 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s P f) = (term233 A B s P f).
Proof. exact (MK_COMB (@lem4969405 A B s P _62510 h1) (@lem4969406 A B f)). Qed.
Lemma lem4969408 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4969409 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62510 s P f) = (term234 A B _62510 s P f).
Proof. exact (eq_refl (term234 A B _62510 s P f)). Qed.
Lemma lem4969410 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term233 A B s P f)) = ((_62510 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4969409 A B _62510 s P f) (@lem4969408 A B s P f)). Qed.
Lemma lem4969411 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (_62510 s P f) = (term100 A B s P f).
Proof. exact (EQ_MP (@lem4969410 A B _62510 s P f) (@lem4969407 A B s P f _62510 h1)). Qed.
Lemma lem4969433 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term189 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term189 A B x s P f x')). Qed.
Lemma lem4969434 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term191 A B x s P f) = (term191 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4969433 A B x s P f x')). Qed.
Lemma lem4969435 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969436 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term192 A B x s P f) = (term192 A B x s P f).
Proof. exact (MK_COMB (@lem4969435 A) (@lem4969434 A B x s P f)). Qed.
Lemma lem4969447 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term173 B t P x) = (term173 B t P x).
Proof. exact (eq_refl (term173 B t P x)). Qed.
Lemma lem4969448 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term172 B t P x) = (term192 A B x s P f)) = ((term172 B t P x) = (term192 A B x s P f)).
Proof. exact (MK_COMB (@lem4969447 B t P x) (@lem4969436 A B x s P f)). Qed.
Lemma lem4969449 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term194 A B t s P f) = (term194 A B t s P f).
Proof. exact (fun_ext (fun x : B => @lem4969448 A B t x s P f)). Qed.
Lemma lem4969450 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term195 A B t s P f) = (term195 A B t s P f).
Proof. exact (MK_COMB (@lem4969450 B) (@lem4969449 A B t s P f)). Qed.
Lemma lem4969464 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term142 A B s f x y) = (term142 A B s f x y).
Proof. exact (eq_refl (term142 A B s f x y)). Qed.
Lemma lem4969465 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term144 A B s f y) = (term144 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4969464 A B s f x y)). Qed.
Lemma lem4969466 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969467 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term146 A B s f y) = (term146 A B s f y).
Proof. exact (MK_COMB (@lem4969466 A) (@lem4969465 A B s f y)). Qed.
Lemma lem4969472 {B : Type'} (t : B -> Prop) (y : B) : (term140 B t y) = (term140 B t y).
Proof. exact (eq_refl (term140 B t y)). Qed.
Lemma lem4969473 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term148 A B t s f y) = (term148 A B t s f y).
Proof. exact (MK_COMB (@lem4969472 B t y) (@lem4969467 A B s f y)). Qed.
Lemma lem4969474 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term150 A B t s f) = (term150 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4969473 A B t s f y)). Qed.
Lemma lem4969475 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969476 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term151 A B t s f) = (term151 A B t s f).
Proof. exact (MK_COMB (@lem4969475 B) (@lem4969474 A B t s f)). Qed.
Lemma lem4969477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term152 A B t s f) = (term152 A B t s f).
Proof. exact (MK_COMB (@lem4969477) (@lem4969476 A B t s f)). Qed.
Lemma lem4969479 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term196 A B t s P f) = (term196 A B t s P f).
Proof. exact (MK_COMB (@lem4969478 A B t s f) (@lem4969451 A B t s P f)). Qed.
Lemma lem4969500 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4969503 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4969516 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term123 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term123 A B x f s x')). Qed.
Lemma lem4969517 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4969516 A B x f s x')). Qed.
Lemma lem4969518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969519 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4969518 A) (@lem4969517 A B x f s)). Qed.
Lemma lem4969520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969521 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4969520) (@lem4969519 A B x f s)). Qed.
Lemma lem4969522 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4969521 A B x f s) (@lem4969503 B t x)). Qed.
Lemma lem4969523 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4969522 A B f s t x)). Qed.
Lemma lem4969524 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969525 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4969524 B) (@lem4969523 A B f s t)). Qed.
Lemma lem4969526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969527 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4969526) (@lem4969525 A B f s t)). Qed.
Lemma lem4969528 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4969527 A B f s t) (@lem4969500 A B t s)). Qed.
Lemma lem4969557 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term113 A B s f x y).
Proof. exact (eq_refl (term113 A B s f x y)). Qed.
Lemma lem4969558 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4969557 A B s f x y)). Qed.
Lemma lem4969559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969560 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4969559 A) (@lem4969558 A B s f x)). Qed.
Lemma lem4969561 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4969560 A B s f x)). Qed.
Lemma lem4969562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969563 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4969562 A) (@lem4969561 A B s f)). Qed.
Lemma lem4969564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969565 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4969564) (@lem4969563 A B s f)). Qed.
Lemma lem4969566 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4969565 A B s f) (@lem4969528 A B f t s)). Qed.
Lemma lem4969567 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4969569 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term100 A B s P f) = (_62510 s P f).
Proof. exact (SYM (@lem4969411 A B s P f _62510 h1)). Qed.
Lemma lem4969570 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term100 A B s P f) = (_62510 s P f).
Proof. exact (@lem4969569 A B s P f _62510 h1). Qed.
Lemma lem4969571 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4969572 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term102 A B s P f) = (term235 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969571 A) (@lem4969570 A B s P f _62510 h1)). Qed.
Lemma lem4969573 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4969574 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term104 A B s P f) = (term236 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969573 A) (@lem4969572 A B s P f _62510 h1)). Qed.
Lemma lem4969575 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term105 A B s P f n) = (term237 A B _62510 s P f n).
Proof. exact (MK_COMB (@lem4969574 A B s P f _62510 h1) (@lem4969567 n)). Qed.
Lemma lem4969576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969577 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term106 A B s P f n) = (term238 A B _62510 s P f n).
Proof. exact (MK_COMB (@lem4969576) (@lem4969575 A B s P f n _62510 h1)). Qed.
Lemma lem4969578 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term137 A B P n f t s) = (term239 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4969577 A B s P f n _62510 h1) (@lem4969566 A B f t s)). Qed.
Lemma lem4969579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969580 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term138 A B P n f t s) = (term240 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4969579) (@lem4969578 A B P n f t s _62510 h1)). Qed.
Lemma lem4969581 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term197 A B n t s P f) = (term241 A B _62510 n t s P f).
Proof. exact (MK_COMB (@lem4969580 A B P n f t s _62510 h1) (@lem4969479 A B t s P f)). Qed.
Lemma lem4969582 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term207 A B t s P f) = (term242 A B _62510 t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4969581 A B n t s P f _62510 h1)). Qed.
Lemma lem4969583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4969584 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term209 A B t s P f) = (term243 A B _62510 t s P f).
Proof. exact (MK_COMB (@lem4969583) (@lem4969582 A B t s P f _62510 h1)). Qed.
Lemma lem4969585 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term211 A B s P f) = (term244 A B _62510 s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4969584 A B t s P f _62510 h1)). Qed.
Lemma lem4969586 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969587 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term213 A B s P f) = (term245 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969586 B) (@lem4969585 A B s P f _62510 h1)). Qed.
Lemma lem4969588 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term215 A B P f) = (term246 A B _62510 P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969587 A B s P f _62510 h1)). Qed.
Lemma lem4969589 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969590 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term217 A B P f) = (term247 A B _62510 P f).
Proof. exact (MK_COMB (@lem4969589 A) (@lem4969588 A B P f _62510 h1)). Qed.
Lemma lem4969591 {A B : Type'} (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term219 A B f) = (term248 A B _62510 f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969590 A B P f _62510 h1)). Qed.
Lemma lem4969592 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969593 {A B : Type'} (f : A -> B) (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term221 A B f) = (term249 A B _62510 f).
Proof. exact (MK_COMB (@lem4969592 B) (@lem4969591 A B f _62510 h1)). Qed.
Lemma lem4969594 {A B : Type'} (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term223 A B) = (term250 A B _62510).
Proof. exact (fun_ext (fun f : A -> B => @lem4969593 A B f _62510 h1)). Qed.
Lemma lem4969595 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969596 {A B : Type'} (_62510 : type653 A B) (h1 : _62510 = (term226 A B)) : (term225 A B) = (term251 A B _62510).
Proof. exact (MK_COMB (@lem4969595 A B) (@lem4969594 A B _62510 h1)). Qed.
Lemma lem4969597 {A B : Type'} (_62510 : type653 A B) : term252 A B _62510.
Proof. exact (fun h0 : _62510 = (term226 A B) => @lem4969596 A B _62510 h0). Qed.
Lemma lem4969598 {A B : Type'} : term253 A B.
Proof. exact (fun _62510 : type653 A B => @lem4969597 A B _62510). Qed.
Lemma lem4969600 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term254 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4969601 {A B : Type'} (P : Prop) (c : type653 A B) (Q : type145 A B) : term255 A B P c Q.
Proof. exact (@lem4969600 (type653 A B) P c Q). Qed.
Lemma lem4969602 {A B : Type'} : term256 A B.
Proof. exact (@lem4969601 A B (term225 A B) (term226 A B) (term257 A B)). Qed.
Lemma lem4969603 {A B : Type'} (_62510 : type653 A B) : (term258 A B _62510) = (term251 A B _62510).
Proof. exact (eq_refl (term258 A B _62510)). Qed.
Lemma lem4969604 {A B : Type'} : (term259 A B) = (term259 A B).
Proof. exact (eq_refl (term259 A B)). Qed.
Lemma lem4969605 {A B : Type'} (_62510 : type653 A B) : ((term225 A B) = (term258 A B _62510)) = ((term225 A B) = (term251 A B _62510)).
Proof. exact (MK_COMB (@lem4969604 A B) (@lem4969603 A B _62510)). Qed.
Lemma lem4969606 {A B : Type'} (_62510 : type653 A B) : (term260 A B _62510) = (term260 A B _62510).
Proof. exact (eq_refl (term260 A B _62510)). Qed.
Lemma lem4969607 {A B : Type'} (_62510 : type653 A B) : (term261 A B _62510) = (term252 A B _62510).
Proof. exact (MK_COMB (@lem4969606 A B _62510) (@lem4969605 A B _62510)). Qed.
Lemma lem4969608 {A B : Type'} : (term262 A B) = (term263 A B).
Proof. exact (fun_ext (fun _62510 : type653 A B => @lem4969607 A B _62510)). Qed.
Lemma lem4969609 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4969610 {A B : Type'} : (term264 A B) = (term253 A B).
Proof. exact (MK_COMB (@lem4969609 A B) (@lem4969608 A B)). Qed.
Lemma lem4969611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969612 {A B : Type'} : (term265 A B) = (term266 A B).
Proof. exact (MK_COMB (@lem4969611) (@lem4969610 A B)). Qed.
Lemma lem4969613 {A B : Type'} (_62510 : type653 A B) : (term258 A B _62510) = (term251 A B _62510).
Proof. exact (eq_refl (term258 A B _62510)). Qed.
Lemma lem4969614 {A B : Type'} (_62510 : type653 A B) : (term260 A B _62510) = (term260 A B _62510).
Proof. exact (eq_refl (term260 A B _62510)). Qed.
Lemma lem4969615 {A B : Type'} (_62510 : type653 A B) : (term267 A B _62510) = (term268 A B _62510).
Proof. exact (MK_COMB (@lem4969614 A B _62510) (@lem4969613 A B _62510)). Qed.
Lemma lem4969616 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (fun_ext (fun _62510 : type653 A B => @lem4969615 A B _62510)). Qed.
Lemma lem4969617 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4969618 {A B : Type'} : (term271 A B) = (term272 A B).
Proof. exact (MK_COMB (@lem4969617 A B) (@lem4969616 A B)). Qed.
Lemma lem4969619 {A B : Type'} : (term259 A B) = (term259 A B).
Proof. exact (eq_refl (term259 A B)). Qed.
Lemma lem4969620 {A B : Type'} : ((term225 A B) = (term271 A B)) = ((term225 A B) = (term272 A B)).
Proof. exact (MK_COMB (@lem4969619 A B) (@lem4969618 A B)). Qed.
Lemma lem4969621 {A B : Type'} : (term256 A B) = (term273 A B).
Proof. exact (MK_COMB (@lem4969612 A B) (@lem4969620 A B)). Qed.
Lemma lem4969622 {A B : Type'} : term273 A B.
Proof. exact (EQ_MP (@lem4969621 A B) (@lem4969602 A B)). Qed.
Lemma lem4969623 {A B : Type'} : (term225 A B) = (term272 A B).
Proof. exact (@lem4969622 A B (@lem4969598 A B)). Qed.
Lemma lem4969625 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4969626 {A B : Type'} (s : type653 A B) (t : type653 A B) : (s = (term276 A B t)) = (term277 A B s t).
Proof. exact (@lem4969625 (type832 A B) (A -> Prop) s t). Qed.
Lemma lem4969627 {A B : Type'} (_62510 : type653 A B) : (_62510 = (term278 A B)) = (term279 A B _62510).
Proof. exact (@lem4969626 A B _62510 (term226 A B)). Qed.
Lemma lem4969628 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4969629 {A B : Type'} : (term278 A B) = (term226 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969628 A B s)). Qed.
Lemma lem4969630 {A B : Type'} (_62510 : type653 A B) : (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510) = (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510)). Qed.
Lemma lem4969631 {A B : Type'} (_62510 : type653 A B) : (_62510 = (term278 A B)) = (_62510 = (term226 A B)).
Proof. exact (MK_COMB (@lem4969630 A B _62510) (@lem4969629 A B)). Qed.
Lemma lem4969632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969633 {A B : Type'} (_62510 : type653 A B) : (term280 A B _62510) = (term281 A B _62510).
Proof. exact (MK_COMB (@lem4969632) (@lem4969631 A B _62510)). Qed.
Lemma lem4969634 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4969635 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term229 A B _62510 s) = (term229 A B _62510 s).
Proof. exact (eq_refl (term229 A B _62510 s)). Qed.
Lemma lem4969636 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term227 A B s)) = ((_62510 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4969635 A B _62510 s) (@lem4969634 A B s)). Qed.
Lemma lem4969637 {A B : Type'} (_62510 : type653 A B) : (term282 A B _62510) = (term283 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969636 A B _62510 s)). Qed.
Lemma lem4969638 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969639 {A B : Type'} (_62510 : type653 A B) : (term279 A B _62510) = (term284 A B _62510).
Proof. exact (MK_COMB (@lem4969638 A) (@lem4969637 A B _62510)). Qed.
Lemma lem4969640 {A B : Type'} (_62510 : type653 A B) : ((_62510 = (term278 A B)) = (term279 A B _62510)) = ((_62510 = (term226 A B)) = (term284 A B _62510)).
Proof. exact (MK_COMB (@lem4969633 A B _62510) (@lem4969639 A B _62510)). Qed.
Lemma lem4969641 {A B : Type'} (_62510 : type653 A B) : (_62510 = (term226 A B)) = (term284 A B _62510).
Proof. exact (EQ_MP (@lem4969640 A B _62510) (@lem4969627 A B _62510)). Qed.
Lemma lem4969643 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4969644 {A B : Type'} (s : type832 A B) (t : type832 A B) : (s = (term285 A B t)) = (term286 A B s t).
Proof. exact (@lem4969643 (type551 A B) (B -> Prop) s t). Qed.
Lemma lem4969645 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term287 A B s)) = (term288 A B _62510 s).
Proof. exact (@lem4969644 A B (_62510 s) (term228 A B s)). Qed.
Lemma lem4969646 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4969647 {A B : Type'} (s : A -> Prop) : (term287 A B s) = (term228 A B s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969646 A B s P)). Qed.
Lemma lem4969648 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term229 A B _62510 s) = (term229 A B _62510 s).
Proof. exact (eq_refl (term229 A B _62510 s)). Qed.
Lemma lem4969649 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term287 A B s)) = ((_62510 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4969648 A B _62510 s) (@lem4969647 A B s)). Qed.
Lemma lem4969650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969651 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term289 A B _62510 s) = (term290 A B _62510 s).
Proof. exact (MK_COMB (@lem4969650) (@lem4969649 A B _62510 s)). Qed.
Lemma lem4969652 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4969653 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62510 s P) = (term232 A B _62510 s P).
Proof. exact (eq_refl (term232 A B _62510 s P)). Qed.
Lemma lem4969654 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term230 A B s P)) = ((_62510 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4969653 A B _62510 s P) (@lem4969652 A B s P)). Qed.
Lemma lem4969655 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term291 A B _62510 s) = (term292 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969654 A B _62510 s P)). Qed.
Lemma lem4969656 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969657 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term288 A B _62510 s) = (term293 A B _62510 s).
Proof. exact (MK_COMB (@lem4969656 B) (@lem4969655 A B _62510 s)). Qed.
Lemma lem4969658 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (((_62510 s) = (term287 A B s)) = (term288 A B _62510 s)) = (((_62510 s) = (term228 A B s)) = (term293 A B _62510 s)).
Proof. exact (MK_COMB (@lem4969651 A B _62510 s) (@lem4969657 A B _62510 s)). Qed.
Lemma lem4969659 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term228 A B s)) = (term293 A B _62510 s).
Proof. exact (EQ_MP (@lem4969658 A B _62510 s) (@lem4969645 A B _62510 s)). Qed.
Lemma lem4969661 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4969662 {A B : Type'} (s : type551 A B) (t : type551 A B) : (s = (term294 A B t)) = (term295 A B s t).
Proof. exact (@lem4969661 (A -> Prop) (A -> B) s t). Qed.
Lemma lem4969663 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term296 A B s P)) = (term297 A B _62510 s P).
Proof. exact (@lem4969662 A B (_62510 s P) (term231 A B s P)). Qed.
Lemma lem4969664 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4969665 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term296 A B s P) = (term231 A B s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4969664 A B s P f)). Qed.
Lemma lem4969666 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62510 s P) = (term232 A B _62510 s P).
Proof. exact (eq_refl (term232 A B _62510 s P)). Qed.
Lemma lem4969667 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term296 A B s P)) = ((_62510 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4969666 A B _62510 s P) (@lem4969665 A B s P)). Qed.
Lemma lem4969668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969669 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term298 A B _62510 s P) = (term299 A B _62510 s P).
Proof. exact (MK_COMB (@lem4969668) (@lem4969667 A B _62510 s P)). Qed.
Lemma lem4969670 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4969671 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62510 s P f) = (term234 A B _62510 s P f).
Proof. exact (eq_refl (term234 A B _62510 s P f)). Qed.
Lemma lem4969672 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term233 A B s P f)) = ((_62510 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4969671 A B _62510 s P f) (@lem4969670 A B s P f)). Qed.
Lemma lem4969673 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term300 A B _62510 s P) = (term301 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4969672 A B _62510 s P f)). Qed.
Lemma lem4969674 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969675 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term297 A B _62510 s P) = (term302 A B _62510 s P).
Proof. exact (MK_COMB (@lem4969674 A B) (@lem4969673 A B _62510 s P)). Qed.
Lemma lem4969676 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (((_62510 s P) = (term296 A B s P)) = (term297 A B _62510 s P)) = (((_62510 s P) = (term231 A B s P)) = (term302 A B _62510 s P)).
Proof. exact (MK_COMB (@lem4969669 A B _62510 s P) (@lem4969675 A B _62510 s P)). Qed.
Lemma lem4969677 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term231 A B s P)) = (term302 A B _62510 s P).
Proof. exact (EQ_MP (@lem4969676 A B _62510 s P) (@lem4969663 A B _62510 s P)). Qed.
Lemma lem4969679 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4969680 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term303 A t)) = (term304 A s t).
Proof. exact (@lem4969679 Prop A s t). Qed.
Lemma lem4969681 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term305 A B s P f)) = (term306 A B _62510 s P f).
Proof. exact (@lem4969680 A (_62510 s P f) (term100 A B s P f)). Qed.
Lemma lem4969682 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term307 A B s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term307 A B s P f GEN_PVAR_217)). Qed.
Lemma lem4969683 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term305 A B s P f) = (term100 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4969682 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4969684 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62510 s P f) = (term234 A B _62510 s P f).
Proof. exact (eq_refl (term234 A B _62510 s P f)). Qed.
Lemma lem4969685 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term305 A B s P f)) = ((_62510 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4969684 A B _62510 s P f) (@lem4969683 A B s P f)). Qed.
Lemma lem4969686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4969687 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term308 A B _62510 s P f) = (term309 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969686) (@lem4969685 A B _62510 s P f)). Qed.
Lemma lem4969688 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term307 A B s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term307 A B s P f GEN_PVAR_217)). Qed.
Lemma lem4969689 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term310 A B _62510 s P f GEN_PVAR_217) = (term310 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term310 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4969690 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f GEN_PVAR_217) = (term307 A B s P f GEN_PVAR_217)) = ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4969689 A B _62510 s P f GEN_PVAR_217) (@lem4969688 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4969691 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term311 A B _62510 s P f) = (term312 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4969690 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4969692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969693 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term306 A B _62510 s P f) = (term313 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969692 A) (@lem4969691 A B _62510 s P f)). Qed.
Lemma lem4969694 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (((_62510 s P f) = (term305 A B s P f)) = (term306 A B _62510 s P f)) = (((_62510 s P f) = (term100 A B s P f)) = (term313 A B _62510 s P f)).
Proof. exact (MK_COMB (@lem4969687 A B _62510 s P f) (@lem4969693 A B _62510 s P f)). Qed.
Lemma lem4969695 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term100 A B s P f)) = (term313 A B _62510 s P f).
Proof. exact (EQ_MP (@lem4969694 A B _62510 s P f) (@lem4969681 A B _62510 s P f)). Qed.
Lemma lem4969696 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (eq_refl ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f))). Qed.
Lemma lem4969697 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62510 s P f) = (term312 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4969696 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4969698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969699 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62510 s P f) = (term313 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969698 A) (@lem4969697 A B _62510 s P f)). Qed.
Lemma lem4969700 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f) = (term100 A B s P f)) = (term313 A B _62510 s P f).
Proof. exact (TRANS (@lem4969695 A B _62510 s P f) (@lem4969699 A B _62510 s P f)). Qed.
Lemma lem4969701 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term301 A B _62510 s P) = (term314 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4969700 A B _62510 s P f)). Qed.
Lemma lem4969702 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969703 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term302 A B _62510 s P) = (term315 A B _62510 s P).
Proof. exact (MK_COMB (@lem4969702 A B) (@lem4969701 A B _62510 s P)). Qed.
Lemma lem4969704 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62510 s P) = (term231 A B s P)) = (term315 A B _62510 s P).
Proof. exact (TRANS (@lem4969677 A B _62510 s P) (@lem4969703 A B _62510 s P)). Qed.
Lemma lem4969705 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term292 A B _62510 s) = (term316 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969704 A B _62510 s P)). Qed.
Lemma lem4969706 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969707 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term293 A B _62510 s) = (term317 A B _62510 s).
Proof. exact (MK_COMB (@lem4969706 B) (@lem4969705 A B _62510 s)). Qed.
Lemma lem4969708 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((_62510 s) = (term228 A B s)) = (term317 A B _62510 s).
Proof. exact (TRANS (@lem4969659 A B _62510 s) (@lem4969707 A B _62510 s)). Qed.
Lemma lem4969709 {A B : Type'} (_62510 : type653 A B) : (term283 A B _62510) = (term318 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969708 A B _62510 s)). Qed.
Lemma lem4969710 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969711 {A B : Type'} (_62510 : type653 A B) : (term284 A B _62510) = (term319 A B _62510).
Proof. exact (MK_COMB (@lem4969710 A) (@lem4969709 A B _62510)). Qed.
Lemma lem4969712 {A B : Type'} (_62510 : type653 A B) : (_62510 = (term226 A B)) = (term319 A B _62510).
Proof. exact (TRANS (@lem4969641 A B _62510) (@lem4969711 A B _62510)). Qed.
Lemma lem4969713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969714 {A B : Type'} (_62510 : type653 A B) : (term260 A B _62510) = (term320 A B _62510).
Proof. exact (MK_COMB (@lem4969713) (@lem4969712 A B _62510)). Qed.
Lemma lem4969715 {A B : Type'} (_62510 : type653 A B) : (term251 A B _62510) = (term251 A B _62510).
Proof. exact (eq_refl (term251 A B _62510)). Qed.
Lemma lem4969716 {A B : Type'} (_62510 : type653 A B) : (term268 A B _62510) = (term321 A B _62510).
Proof. exact (MK_COMB (@lem4969714 A B _62510) (@lem4969715 A B _62510)). Qed.
Lemma lem4969717 {A B : Type'} : (term270 A B) = (term322 A B).
Proof. exact (fun_ext (fun _62510 : type653 A B => @lem4969716 A B _62510)). Qed.
Lemma lem4969718 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4969719 {A B : Type'} : (term272 A B) = (term323 A B).
Proof. exact (MK_COMB (@lem4969718 A B) (@lem4969717 A B)). Qed.
Lemma lem4969720 {A B : Type'} : (term259 A B) = (term259 A B).
Proof. exact (eq_refl (term259 A B)). Qed.
Lemma lem4969721 {A B : Type'} : ((term225 A B) = (term272 A B)) = ((term225 A B) = (term323 A B)).
Proof. exact (MK_COMB (@lem4969720 A B) (@lem4969719 A B)). Qed.
Lemma lem4969724 {A B : Type'} : (term225 A B) = (term323 A B).
Proof. exact (EQ_MP (@lem4969721 A B) (@lem4969623 A B)). Qed.
Lemma lem4969725 {A B : Type'} : (term224 A B) = (term323 A B).
Proof. exact (TRANS (@lem4969392 A B) (@lem4969724 A B)). Qed.
Lemma lem4969734 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term189 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term189 A B x s P f x')). Qed.
Lemma lem4969735 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term191 A B x s P f) = (term191 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4969734 A B x s P f x')). Qed.
Lemma lem4969736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969737 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term192 A B x s P f) = (term192 A B x s P f).
Proof. exact (MK_COMB (@lem4969736 A) (@lem4969735 A B x s P f)). Qed.
Lemma lem4969744 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term173 B t P x) = (term173 B t P x).
Proof. exact (eq_refl (term173 B t P x)). Qed.
Lemma lem4969745 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term172 B t P x) = (term192 A B x s P f)) = ((term172 B t P x) = (term192 A B x s P f)).
Proof. exact (MK_COMB (@lem4969744 B t P x) (@lem4969737 A B x s P f)). Qed.
Lemma lem4969746 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term194 A B t s P f) = (term194 A B t s P f).
Proof. exact (fun_ext (fun x : B => @lem4969745 A B t x s P f)). Qed.
Lemma lem4969747 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969748 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term195 A B t s P f) = (term195 A B t s P f).
Proof. exact (MK_COMB (@lem4969747 B) (@lem4969746 A B t s P f)). Qed.
Lemma lem4969753 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term142 A B s f x y) = (term142 A B s f x y).
Proof. exact (eq_refl (term142 A B s f x y)). Qed.
Lemma lem4969754 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term144 A B s f y) = (term144 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4969753 A B s f x y)). Qed.
Lemma lem4969755 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969756 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term146 A B s f y) = (term146 A B s f y).
Proof. exact (MK_COMB (@lem4969755 A) (@lem4969754 A B s f y)). Qed.
Lemma lem4969759 {B : Type'} (t : B -> Prop) (y : B) : (term140 B t y) = (term140 B t y).
Proof. exact (eq_refl (term140 B t y)). Qed.
Lemma lem4969760 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term148 A B t s f y) = (term148 A B t s f y).
Proof. exact (MK_COMB (@lem4969759 B t y) (@lem4969756 A B s f y)). Qed.
Lemma lem4969761 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term150 A B t s f) = (term150 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4969760 A B t s f y)). Qed.
Lemma lem4969762 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969763 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term151 A B t s f) = (term151 A B t s f).
Proof. exact (MK_COMB (@lem4969762 B) (@lem4969761 A B t s f)). Qed.
Lemma lem4969764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969765 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term152 A B t s f) = (term152 A B t s f).
Proof. exact (MK_COMB (@lem4969764) (@lem4969763 A B t s f)). Qed.
Lemma lem4969766 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term196 A B t s P f) = (term196 A B t s P f).
Proof. exact (MK_COMB (@lem4969765 A B t s f) (@lem4969748 A B t s P f)). Qed.
Lemma lem4969775 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4969776 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4969781 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term123 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term123 A B x f s x')). Qed.
Lemma lem4969782 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4969781 A B x f s x')). Qed.
Lemma lem4969783 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969784 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4969783 A) (@lem4969782 A B x f s)). Qed.
Lemma lem4969785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969786 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4969785) (@lem4969784 A B x f s)). Qed.
Lemma lem4969787 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4969786 A B x f s) (@lem4969776 B t x)). Qed.
Lemma lem4969788 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4969787 A B f s t x)). Qed.
Lemma lem4969789 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4969790 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4969789 B) (@lem4969788 A B f s t)). Qed.
Lemma lem4969791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969792 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4969791) (@lem4969790 A B f s t)). Qed.
Lemma lem4969793 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4969792 A B f s t) (@lem4969775 A B t s)). Qed.
Lemma lem4969806 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term113 A B s f x y).
Proof. exact (eq_refl (term113 A B s f x y)). Qed.
Lemma lem4969807 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4969806 A B s f x y)). Qed.
Lemma lem4969808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969809 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4969808 A) (@lem4969807 A B s f x)). Qed.
Lemma lem4969810 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4969809 A B s f x)). Qed.
Lemma lem4969811 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969812 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4969811 A) (@lem4969810 A B s f)). Qed.
Lemma lem4969813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4969814 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4969813) (@lem4969812 A B s f)). Qed.
Lemma lem4969815 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4969814 A B s f) (@lem4969793 A B f t s)). Qed.
Lemma lem4969818 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62510 s P f n) = (term238 A B _62510 s P f n).
Proof. exact (eq_refl (term238 A B _62510 s P f n)). Qed.
Lemma lem4969819 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term239 A B _62510 P n f t s) = (term239 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4969818 A B _62510 s P f n) (@lem4969815 A B f t s)). Qed.
Lemma lem4969820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969821 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term240 A B _62510 P n f t s) = (term240 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4969820) (@lem4969819 A B _62510 P n f t s)). Qed.
Lemma lem4969822 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term241 A B _62510 n t s P f) = (term241 A B _62510 n t s P f).
Proof. exact (MK_COMB (@lem4969821 A B _62510 P n f t s) (@lem4969766 A B t s P f)). Qed.
Lemma lem4969823 {A B : Type'} (_62510 : type653 A B) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term242 A B _62510 t s P f) = (term242 A B _62510 t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4969822 A B _62510 n t s P f)). Qed.
Lemma lem4969824 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4969825 {A B : Type'} (_62510 : type653 A B) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term243 A B _62510 t s P f) = (term243 A B _62510 t s P f).
Proof. exact (MK_COMB (@lem4969824) (@lem4969823 A B _62510 t s P f)). Qed.
Lemma lem4969826 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term244 A B _62510 s P f) = (term244 A B _62510 s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4969825 A B _62510 t s P f)). Qed.
Lemma lem4969827 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969828 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term245 A B _62510 s P f) = (term245 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969827 B) (@lem4969826 A B _62510 s P f)). Qed.
Lemma lem4969829 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (f : A -> B) : (term246 A B _62510 P f) = (term246 A B _62510 P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969828 A B _62510 s P f)). Qed.
Lemma lem4969830 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969831 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (f : A -> B) : (term247 A B _62510 P f) = (term247 A B _62510 P f).
Proof. exact (MK_COMB (@lem4969830 A) (@lem4969829 A B _62510 P f)). Qed.
Lemma lem4969832 {A B : Type'} (_62510 : type653 A B) (f : A -> B) : (term248 A B _62510 f) = (term248 A B _62510 f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969831 A B _62510 P f)). Qed.
Lemma lem4969833 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969834 {A B : Type'} (_62510 : type653 A B) (f : A -> B) : (term249 A B _62510 f) = (term249 A B _62510 f).
Proof. exact (MK_COMB (@lem4969833 B) (@lem4969832 A B _62510 f)). Qed.
Lemma lem4969835 {A B : Type'} (_62510 : type653 A B) : (term250 A B _62510) = (term250 A B _62510).
Proof. exact (fun_ext (fun f : A -> B => @lem4969834 A B _62510 f)). Qed.
Lemma lem4969836 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969837 {A B : Type'} (_62510 : type653 A B) : (term251 A B _62510) = (term251 A B _62510).
Proof. exact (MK_COMB (@lem4969836 A B) (@lem4969835 A B _62510)). Qed.
Lemma lem4969838 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term94 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term94 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4969839 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term96 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4969838 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4969840 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4969841 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term98 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4969840 A) (@lem4969839 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4969844 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term310 A B _62510 s P f GEN_PVAR_217) = (term310 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term310 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4969845 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4969844 A B _62510 s P f GEN_PVAR_217) (@lem4969841 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4969846 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62510 s P f) = (term312 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4969845 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4969847 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4969848 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62510 s P f) = (term313 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4969847 A) (@lem4969846 A B _62510 s P f)). Qed.
Lemma lem4969849 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term314 A B _62510 s P) = (term314 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4969848 A B _62510 s P f)). Qed.
Lemma lem4969850 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4969851 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term315 A B _62510 s P) = (term315 A B _62510 s P).
Proof. exact (MK_COMB (@lem4969850 A B) (@lem4969849 A B _62510 s P)). Qed.
Lemma lem4969852 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term316 A B _62510 s) = (term316 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4969851 A B _62510 s P)). Qed.
Lemma lem4969853 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4969854 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term317 A B _62510 s) = (term317 A B _62510 s).
Proof. exact (MK_COMB (@lem4969853 B) (@lem4969852 A B _62510 s)). Qed.
Lemma lem4969855 {A B : Type'} (_62510 : type653 A B) : (term318 A B _62510) = (term318 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4969854 A B _62510 s)). Qed.
Lemma lem4969856 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4969857 {A B : Type'} (_62510 : type653 A B) : (term319 A B _62510) = (term319 A B _62510).
Proof. exact (MK_COMB (@lem4969856 A) (@lem4969855 A B _62510)). Qed.
Lemma lem4969858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4969859 {A B : Type'} (_62510 : type653 A B) : (term320 A B _62510) = (term320 A B _62510).
Proof. exact (MK_COMB (@lem4969858) (@lem4969857 A B _62510)). Qed.
Lemma lem4969860 {A B : Type'} (_62510 : type653 A B) : (term321 A B _62510) = (term321 A B _62510).
Proof. exact (MK_COMB (@lem4969859 A B _62510) (@lem4969837 A B _62510)). Qed.
Lemma lem4969861 {A B : Type'} : (term322 A B) = (term322 A B).
Proof. exact (fun_ext (fun _62510 : type653 A B => @lem4969860 A B _62510)). Qed.
Lemma lem4969862 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4969863 {A B : Type'} : (term323 A B) = (term323 A B).
Proof. exact (MK_COMB (@lem4969862 A B) (@lem4969861 A B)). Qed.
Lemma lem4970018 {A B : Type'} : (term224 A B) = (term323 A B).
Proof. exact (TRANS (@lem4969725 A B) (@lem4969863 A B)). Qed.
Lemma lem4970019 {A B : Type'} : (term323 A B) = (term224 A B).
Proof. exact (SYM (@lem4970018 A B)). Qed.
Lemma lem4970020 {A B : Type'} (_62510 : type653 A B) (h1 : term319 A B _62510) : term319 A B _62510.
Proof. exact (h1). Qed.
Lemma lem4970021 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term239 A B _62510 P n f t s.
Proof. exact (h1). Qed.
Lemma lem4970022 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term151 A B t s f) : term151 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4970024 (p : Prop) : p = (term198 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4970025 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term172 B t P x) = (term192 A B x s P f)) = (term324 A B t x s P f).
Proof. exact (@lem4970024 ((term172 B t P x) = (term192 A B x s P f))). Qed.
Lemma lem4970026 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term324 A B t x s P f) = ((term172 B t P x) = (term192 A B x s P f)).
Proof. exact (SYM (@lem4970025 A B t x s P f)). Qed.
Lemma lem4970027 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term325 A B t x s P f) : term325 A B t x s P f.
Proof. exact (h1). Qed.
Lemma lem4970031 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term94 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term94 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970032 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4970033 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term328 A B GEN_PVAR_217 s P f) = (term329 A B GEN_PVAR_217 s P f).
Proof. exact (@lem4970032 A (term96 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970034 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4970037 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term331 A B GEN_PVAR_217 s P f x) = (term332 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4970035) (@lem4970034 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970038 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term333 A B GEN_PVAR_217 s P f) = (term334 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4970037 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970039 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970040 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term329 A B GEN_PVAR_217 s P f) = (term335 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970039 A) (@lem4970038 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970041 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term328 A B GEN_PVAR_217 s P f) = (term335 A B GEN_PVAR_217 s P f).
Proof. exact (TRANS (@lem4970033 A B GEN_PVAR_217 s P f) (@lem4970040 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970042 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term96 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4970031 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4970044 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term98 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970043 A) (@lem4970042 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970046 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62510 s P f GEN_PVAR_217) = (term336 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970047 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term337 A B _62510 GEN_PVAR_217 s P f) = (term337 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970046 A B _62510 s P f GEN_PVAR_217) (@lem4970044 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970049 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term338 A B _62510 s P f GEN_PVAR_217) = (term338 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term338 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970050 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term339 A B _62510 GEN_PVAR_217 s P f) = (term340 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970049 A B _62510 s P f GEN_PVAR_217) (@lem4970041 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970052 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term341 A B _62510 GEN_PVAR_217 s P f) = (term342 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970051) (@lem4970050 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970053 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term343 A B _62510 GEN_PVAR_217 s P f) = (term344 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970052 A B _62510 GEN_PVAR_217 s P f) (@lem4970047 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970054 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = (term343 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (@lem17784 (_62510 s P f GEN_PVAR_217) (term98 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970055 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62510 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = (term344 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (TRANS (@lem4970054 A B _62510 GEN_PVAR_217 s P f) (@lem4970053 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970056 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62510 s P f) = (term345 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970055 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970058 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62510 s P f) = (term346 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970057 A) (@lem4970056 A B _62510 s P f)). Qed.
Lemma lem4970059 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term314 A B _62510 s P) = (term347 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970058 A B _62510 s P f)). Qed.
Lemma lem4970060 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970061 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term315 A B _62510 s P) = (term348 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970060 A B) (@lem4970059 A B _62510 s P)). Qed.
Lemma lem4970062 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term316 A B _62510 s) = (term349 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970061 A B _62510 s P)). Qed.
Lemma lem4970063 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970064 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term317 A B _62510 s) = (term350 A B _62510 s).
Proof. exact (MK_COMB (@lem4970063 B) (@lem4970062 A B _62510 s)). Qed.
Lemma lem4970065 {A B : Type'} (_62510 : type653 A B) : (term318 A B _62510) = (term351 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970064 A B _62510 s)). Qed.
Lemma lem4970066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970067 {A B : Type'} (_62510 : type653 A B) : (term319 A B _62510) = (term352 A B _62510).
Proof. exact (MK_COMB (@lem4970066 A) (@lem4970065 A B _62510)). Qed.
Lemma lem4970081 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4970082 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (@lem4970081 A P Q). Qed.
Lemma lem4970083 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term355 A B _62510 s P f) = (term356 A B _62510 s P f).
Proof. exact (@lem4970082 A (term357 A B _62510 s P f) (term358 A B _62510 s P f)). Qed.
Lemma lem4970084 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term359 A B _62510 s P f GEN_PVAR_217) = (term340 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term359 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970086 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term360 A B _62510 s P f GEN_PVAR_217) = (term342 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970085) (@lem4970084 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970087 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term361 A B _62510 s P f GEN_PVAR_217) = (term337 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term361 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970088 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term362 A B _62510 s P f GEN_PVAR_217) = (term344 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970086 A B _62510 GEN_PVAR_217 s P f) (@lem4970087 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970089 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term363 A B _62510 s P f) = (term345 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970088 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970090 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970091 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term355 A B _62510 s P f) = (term346 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970090 A) (@lem4970089 A B _62510 s P f)). Qed.
Lemma lem4970092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970093 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term364 A B _62510 s P f) = (term365 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970092) (@lem4970091 A B _62510 s P f)). Qed.
Lemma lem4970094 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term359 A B _62510 s P f GEN_PVAR_217) = (term340 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term359 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970095 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term366 A B _62510 s P f) = (term357 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970094 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970097 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term367 A B _62510 s P f) = (term368 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970096 A) (@lem4970095 A B _62510 s P f)). Qed.
Lemma lem4970098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970099 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term369 A B _62510 s P f) = (term370 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970098) (@lem4970097 A B _62510 s P f)). Qed.
Lemma lem4970100 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term361 A B _62510 s P f GEN_PVAR_217) = (term337 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term361 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970101 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term371 A B _62510 s P f) = (term358 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970100 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970103 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term372 A B _62510 s P f) = (term373 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970102 A) (@lem4970101 A B _62510 s P f)). Qed.
Lemma lem4970104 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term356 A B _62510 s P f) = (term374 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970099 A B _62510 s P f) (@lem4970103 A B _62510 s P f)). Qed.
Lemma lem4970105 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term355 A B _62510 s P f) = (term356 A B _62510 s P f)) = ((term346 A B _62510 s P f) = (term374 A B _62510 s P f)).
Proof. exact (MK_COMB (@lem4970093 A B _62510 s P f) (@lem4970104 A B _62510 s P f)). Qed.
Lemma lem4970106 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term346 A B _62510 s P f) = (term374 A B _62510 s P f).
Proof. exact (EQ_MP (@lem4970105 A B _62510 s P f) (@lem4970083 A B _62510 s P f)). Qed.
Lemma lem4970211 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term347 A B _62510 s P) = (term375 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970106 A B _62510 s P f)). Qed.
Lemma lem4970212 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970213 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term348 A B _62510 s P) = (term376 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970212 A B) (@lem4970211 A B _62510 s P)). Qed.
Lemma lem4970215 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4970216 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term377 A B P Q) = (term378 A B P Q).
Proof. exact (@lem4970215 (A -> B) P Q). Qed.
Lemma lem4970217 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term379 A B _62510 s P) = (term380 A B _62510 s P).
Proof. exact (@lem4970216 A B (term381 A B _62510 s P) (term382 A B _62510 s P)). Qed.
Lemma lem4970218 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term383 A B _62510 s P f) = (term368 A B _62510 s P f).
Proof. exact (eq_refl (term383 A B _62510 s P f)). Qed.
Lemma lem4970219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970220 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term384 A B _62510 s P f) = (term370 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970219) (@lem4970218 A B _62510 s P f)). Qed.
Lemma lem4970221 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term385 A B _62510 s P f) = (term373 A B _62510 s P f).
Proof. exact (eq_refl (term385 A B _62510 s P f)). Qed.
Lemma lem4970222 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term386 A B _62510 s P f) = (term374 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970220 A B _62510 s P f) (@lem4970221 A B _62510 s P f)). Qed.
Lemma lem4970223 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term387 A B _62510 s P) = (term375 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970222 A B _62510 s P f)). Qed.
Lemma lem4970224 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970225 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term379 A B _62510 s P) = (term376 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970224 A B) (@lem4970223 A B _62510 s P)). Qed.
Lemma lem4970226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970227 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term388 A B _62510 s P) = (term389 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970226) (@lem4970225 A B _62510 s P)). Qed.
Lemma lem4970228 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term383 A B _62510 s P f) = (term368 A B _62510 s P f).
Proof. exact (eq_refl (term383 A B _62510 s P f)). Qed.
Lemma lem4970229 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term390 A B _62510 s P) = (term381 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970228 A B _62510 s P f)). Qed.
Lemma lem4970230 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970231 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term391 A B _62510 s P) = (term392 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970230 A B) (@lem4970229 A B _62510 s P)). Qed.
Lemma lem4970232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970233 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term393 A B _62510 s P) = (term394 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970232) (@lem4970231 A B _62510 s P)). Qed.
Lemma lem4970234 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term385 A B _62510 s P f) = (term373 A B _62510 s P f).
Proof. exact (eq_refl (term385 A B _62510 s P f)). Qed.
Lemma lem4970235 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term395 A B _62510 s P) = (term382 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970234 A B _62510 s P f)). Qed.
Lemma lem4970236 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970237 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term396 A B _62510 s P) = (term397 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970236 A B) (@lem4970235 A B _62510 s P)). Qed.
Lemma lem4970238 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term380 A B _62510 s P) = (term398 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970233 A B _62510 s P) (@lem4970237 A B _62510 s P)). Qed.
Lemma lem4970239 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((term379 A B _62510 s P) = (term380 A B _62510 s P)) = ((term376 A B _62510 s P) = (term398 A B _62510 s P)).
Proof. exact (MK_COMB (@lem4970227 A B _62510 s P) (@lem4970238 A B _62510 s P)). Qed.
Lemma lem4970240 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term376 A B _62510 s P) = (term398 A B _62510 s P).
Proof. exact (EQ_MP (@lem4970239 A B _62510 s P) (@lem4970217 A B _62510 s P)). Qed.
Lemma lem4970353 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term348 A B _62510 s P) = (term398 A B _62510 s P).
Proof. exact (TRANS (@lem4970213 A B _62510 s P) (@lem4970240 A B _62510 s P)). Qed.
Lemma lem4970354 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term349 A B _62510 s) = (term399 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970353 A B _62510 s P)). Qed.
Lemma lem4970355 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970356 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term350 A B _62510 s) = (term400 A B _62510 s).
Proof. exact (MK_COMB (@lem4970355 B) (@lem4970354 A B _62510 s)). Qed.
Lemma lem4970358 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4970359 {B : Type'} (P : type686 B) (Q : type686 B) : (term401 B P Q) = (term402 B P Q).
Proof. exact (@lem4970358 (B -> Prop) P Q). Qed.
Lemma lem4970360 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term403 A B _62510 s) = (term404 A B _62510 s).
Proof. exact (@lem4970359 B (term405 A B _62510 s) (term406 A B _62510 s)). Qed.
Lemma lem4970361 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term407 A B _62510 s P) = (term392 A B _62510 s P).
Proof. exact (eq_refl (term407 A B _62510 s P)). Qed.
Lemma lem4970362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970363 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term408 A B _62510 s P) = (term394 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970362) (@lem4970361 A B _62510 s P)). Qed.
Lemma lem4970364 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term409 A B _62510 s P) = (term397 A B _62510 s P).
Proof. exact (eq_refl (term409 A B _62510 s P)). Qed.
Lemma lem4970365 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term410 A B _62510 s P) = (term398 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970363 A B _62510 s P) (@lem4970364 A B _62510 s P)). Qed.
Lemma lem4970366 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term411 A B _62510 s) = (term399 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970365 A B _62510 s P)). Qed.
Lemma lem4970367 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970368 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term403 A B _62510 s) = (term400 A B _62510 s).
Proof. exact (MK_COMB (@lem4970367 B) (@lem4970366 A B _62510 s)). Qed.
Lemma lem4970369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970370 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term412 A B _62510 s) = (term413 A B _62510 s).
Proof. exact (MK_COMB (@lem4970369) (@lem4970368 A B _62510 s)). Qed.
Lemma lem4970371 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term407 A B _62510 s P) = (term392 A B _62510 s P).
Proof. exact (eq_refl (term407 A B _62510 s P)). Qed.
Lemma lem4970372 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term414 A B _62510 s) = (term405 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970371 A B _62510 s P)). Qed.
Lemma lem4970373 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970374 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term415 A B _62510 s) = (term416 A B _62510 s).
Proof. exact (MK_COMB (@lem4970373 B) (@lem4970372 A B _62510 s)). Qed.
Lemma lem4970375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970376 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term417 A B _62510 s) = (term418 A B _62510 s).
Proof. exact (MK_COMB (@lem4970375) (@lem4970374 A B _62510 s)). Qed.
Lemma lem4970377 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term409 A B _62510 s P) = (term397 A B _62510 s P).
Proof. exact (eq_refl (term409 A B _62510 s P)). Qed.
Lemma lem4970378 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term419 A B _62510 s) = (term406 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970377 A B _62510 s P)). Qed.
Lemma lem4970379 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970380 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term420 A B _62510 s) = (term421 A B _62510 s).
Proof. exact (MK_COMB (@lem4970379 B) (@lem4970378 A B _62510 s)). Qed.
Lemma lem4970381 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term404 A B _62510 s) = (term422 A B _62510 s).
Proof. exact (MK_COMB (@lem4970376 A B _62510 s) (@lem4970380 A B _62510 s)). Qed.
Lemma lem4970382 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((term403 A B _62510 s) = (term404 A B _62510 s)) = ((term400 A B _62510 s) = (term422 A B _62510 s)).
Proof. exact (MK_COMB (@lem4970370 A B _62510 s) (@lem4970381 A B _62510 s)). Qed.
Lemma lem4970383 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term400 A B _62510 s) = (term422 A B _62510 s).
Proof. exact (EQ_MP (@lem4970382 A B _62510 s) (@lem4970360 A B _62510 s)). Qed.
Lemma lem4970504 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term350 A B _62510 s) = (term422 A B _62510 s).
Proof. exact (TRANS (@lem4970356 A B _62510 s) (@lem4970383 A B _62510 s)). Qed.
Lemma lem4970505 {A B : Type'} (_62510 : type653 A B) : (term351 A B _62510) = (term423 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970504 A B _62510 s)). Qed.
Lemma lem4970506 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970507 {A B : Type'} (_62510 : type653 A B) : (term352 A B _62510) = (term424 A B _62510).
Proof. exact (MK_COMB (@lem4970506 A) (@lem4970505 A B _62510)). Qed.
Lemma lem4970509 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4970510 {A : Type'} (P : type686 A) (Q : type686 A) : (term401 A P Q) = (term402 A P Q).
Proof. exact (@lem4970509 (A -> Prop) P Q). Qed.
Lemma lem4970511 {A B : Type'} (_62510 : type653 A B) : (term425 A B _62510) = (term426 A B _62510).
Proof. exact (@lem4970510 A (term427 A B _62510) (term428 A B _62510)). Qed.
Lemma lem4970512 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term429 A B _62510 s) = (term416 A B _62510 s).
Proof. exact (eq_refl (term429 A B _62510 s)). Qed.
Lemma lem4970513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970514 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term430 A B _62510 s) = (term418 A B _62510 s).
Proof. exact (MK_COMB (@lem4970513) (@lem4970512 A B _62510 s)). Qed.
Lemma lem4970515 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term431 A B _62510 s) = (term421 A B _62510 s).
Proof. exact (eq_refl (term431 A B _62510 s)). Qed.
Lemma lem4970516 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term432 A B _62510 s) = (term422 A B _62510 s).
Proof. exact (MK_COMB (@lem4970514 A B _62510 s) (@lem4970515 A B _62510 s)). Qed.
Lemma lem4970517 {A B : Type'} (_62510 : type653 A B) : (term433 A B _62510) = (term423 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970516 A B _62510 s)). Qed.
Lemma lem4970518 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970519 {A B : Type'} (_62510 : type653 A B) : (term425 A B _62510) = (term424 A B _62510).
Proof. exact (MK_COMB (@lem4970518 A) (@lem4970517 A B _62510)). Qed.
Lemma lem4970520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970521 {A B : Type'} (_62510 : type653 A B) : (term434 A B _62510) = (term435 A B _62510).
Proof. exact (MK_COMB (@lem4970520) (@lem4970519 A B _62510)). Qed.
Lemma lem4970522 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term429 A B _62510 s) = (term416 A B _62510 s).
Proof. exact (eq_refl (term429 A B _62510 s)). Qed.
Lemma lem4970523 {A B : Type'} (_62510 : type653 A B) : (term436 A B _62510) = (term427 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970522 A B _62510 s)). Qed.
Lemma lem4970524 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970525 {A B : Type'} (_62510 : type653 A B) : (term437 A B _62510) = (term438 A B _62510).
Proof. exact (MK_COMB (@lem4970524 A) (@lem4970523 A B _62510)). Qed.
Lemma lem4970526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970527 {A B : Type'} (_62510 : type653 A B) : (term439 A B _62510) = (term440 A B _62510).
Proof. exact (MK_COMB (@lem4970526) (@lem4970525 A B _62510)). Qed.
Lemma lem4970528 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term431 A B _62510 s) = (term421 A B _62510 s).
Proof. exact (eq_refl (term431 A B _62510 s)). Qed.
Lemma lem4970529 {A B : Type'} (_62510 : type653 A B) : (term441 A B _62510) = (term428 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970528 A B _62510 s)). Qed.
Lemma lem4970530 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970531 {A B : Type'} (_62510 : type653 A B) : (term442 A B _62510) = (term443 A B _62510).
Proof. exact (MK_COMB (@lem4970530 A) (@lem4970529 A B _62510)). Qed.
Lemma lem4970532 {A B : Type'} (_62510 : type653 A B) : (term426 A B _62510) = (term444 A B _62510).
Proof. exact (MK_COMB (@lem4970527 A B _62510) (@lem4970531 A B _62510)). Qed.
Lemma lem4970533 {A B : Type'} (_62510 : type653 A B) : ((term425 A B _62510) = (term426 A B _62510)) = ((term424 A B _62510) = (term444 A B _62510)).
Proof. exact (MK_COMB (@lem4970521 A B _62510) (@lem4970532 A B _62510)). Qed.
Lemma lem4970534 {A B : Type'} (_62510 : type653 A B) : (term424 A B _62510) = (term444 A B _62510).
Proof. exact (EQ_MP (@lem4970533 A B _62510) (@lem4970511 A B _62510)). Qed.
Lemma lem4970663 {A B : Type'} (_62510 : type653 A B) : (term352 A B _62510) = (term444 A B _62510).
Proof. exact (TRANS (@lem4970507 A B _62510) (@lem4970534 A B _62510)). Qed.
Lemma lem4970665 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4970666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (@lem4970665 A P Q). Qed.
Lemma lem4970667 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term447 A B _62510 GEN_PVAR_217 s P f) = (term448 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (@lem4970666 A (term449 A B _62510 s P f GEN_PVAR_217) (term96 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970668 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970669 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term450 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4970668 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970670 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4970671 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term451 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970670 A) (@lem4970669 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970672 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62510 s P f GEN_PVAR_217) = (term336 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970673 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term447 A B _62510 GEN_PVAR_217 s P f) = (term337 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970672 A B _62510 s P f GEN_PVAR_217) (@lem4970671 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4970674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970675 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term452 A B _62510 GEN_PVAR_217 s P f) = (term453 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970674) (@lem4970673 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970676 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970677 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62510 s P f GEN_PVAR_217) = (term336 A B _62510 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970678 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term454 A B _62510 GEN_PVAR_217 s P f x) = (term455 A B _62510 GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4970677 A B _62510 s P f GEN_PVAR_217) (@lem4970676 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970679 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term456 A B _62510 GEN_PVAR_217 s P f) = (term457 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4970678 A B _62510 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970680 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4970681 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term448 A B _62510 GEN_PVAR_217 s P f) = (term458 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970680 A) (@lem4970679 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970682 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term447 A B _62510 GEN_PVAR_217 s P f) = (term448 A B _62510 GEN_PVAR_217 s P f)) = ((term337 A B _62510 GEN_PVAR_217 s P f) = (term458 A B _62510 GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4970675 A B _62510 GEN_PVAR_217 s P f) (@lem4970681 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970683 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term337 A B _62510 GEN_PVAR_217 s P f) = (term458 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (EQ_MP (@lem4970682 A B _62510 GEN_PVAR_217 s P f) (@lem4970667 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970684 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term358 A B _62510 s P f) = (term459 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970683 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970686 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term373 A B _62510 s P f) = (term460 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970685 A) (@lem4970684 A B _62510 s P f)). Qed.
Lemma lem4970688 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4970689 {A : Type'} (P : type1402 A) : (term463 A P) = (term464 A P).
Proof. exact (@lem4970688 A A P). Qed.
Lemma lem4970690 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term465 A B _62510 s P f) = (term466 A B _62510 s P f).
Proof. exact (@lem4970689 A (term467 A B _62510 s P f)). Qed.
Lemma lem4970691 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term468 A B _62510 s P f GEN_PVAR_217) = (term457 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term468 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970692 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4970693 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term469 A B _62510 s P f GEN_PVAR_217 x) = (term470 A B _62510 GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4970691 A B _62510 GEN_PVAR_217 s P f) (@lem4970692 A x)). Qed.
Lemma lem4970694 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term470 A B _62510 GEN_PVAR_217 s P f x) = (term455 A B _62510 GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term470 A B _62510 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970695 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term469 A B _62510 s P f GEN_PVAR_217 x) = (term455 A B _62510 GEN_PVAR_217 s P f x).
Proof. exact (TRANS (@lem4970693 A B _62510 GEN_PVAR_217 s P f x) (@lem4970694 A B _62510 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970696 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term471 A B _62510 s P f GEN_PVAR_217) = (term457 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4970695 A B _62510 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4970697 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4970698 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term472 A B _62510 s P f GEN_PVAR_217) = (term458 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4970697 A) (@lem4970696 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970699 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term473 A B _62510 s P f) = (term459 A B _62510 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970698 A B _62510 GEN_PVAR_217 s P f)). Qed.
Lemma lem4970700 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970701 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term465 A B _62510 s P f) = (term460 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970700 A) (@lem4970699 A B _62510 s P f)). Qed.
Lemma lem4970702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970703 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term474 A B _62510 s P f) = (term475 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970702) (@lem4970701 A B _62510 s P f)). Qed.
Lemma lem4970704 {A B : Type'} (_62510 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term468 A B _62510 s P f GEN_PVAR_217) = (term457 A B _62510 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term468 A B _62510 s P f GEN_PVAR_217)). Qed.
Lemma lem4970705 {A : Type'} (x : A -> A) (GEN_PVAR_217 : A) : (x GEN_PVAR_217) = (x GEN_PVAR_217).
Proof. exact (eq_refl (x GEN_PVAR_217)). Qed.
Lemma lem4970706 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term476 A B _62510 s P f x GEN_PVAR_217) = (term477 A B _62510 s P f x GEN_PVAR_217).
Proof. exact (MK_COMB (@lem4970704 A B _62510 GEN_PVAR_217 s P f) (@lem4970705 A x GEN_PVAR_217)). Qed.
Lemma lem4970707 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term477 A B _62510 s P f x GEN_PVAR_217) = (term478 A B _62510 s P f x GEN_PVAR_217).
Proof. exact (eq_refl (term477 A B _62510 s P f x GEN_PVAR_217)). Qed.
Lemma lem4970708 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term476 A B _62510 s P f x GEN_PVAR_217) = (term478 A B _62510 s P f x GEN_PVAR_217).
Proof. exact (TRANS (@lem4970706 A B _62510 s P f x GEN_PVAR_217) (@lem4970707 A B _62510 s P f x GEN_PVAR_217)). Qed.
Lemma lem4970709 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term479 A B _62510 s P f x) = (term480 A B _62510 s P f x).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4970708 A B _62510 s P f x GEN_PVAR_217)). Qed.
Lemma lem4970710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970711 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term481 A B _62510 s P f x) = (term482 A B _62510 s P f x).
Proof. exact (MK_COMB (@lem4970710 A) (@lem4970709 A B _62510 s P f x)). Qed.
Lemma lem4970712 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term483 A B _62510 s P f) = (term484 A B _62510 s P f).
Proof. exact (fun_ext (fun x : A -> A => @lem4970711 A B _62510 s P f x)). Qed.
Lemma lem4970713 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4970714 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term466 A B _62510 s P f) = (term485 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970713 A) (@lem4970712 A B _62510 s P f)). Qed.
Lemma lem4970715 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term465 A B _62510 s P f) = (term466 A B _62510 s P f)) = ((term460 A B _62510 s P f) = (term485 A B _62510 s P f)).
Proof. exact (MK_COMB (@lem4970703 A B _62510 s P f) (@lem4970714 A B _62510 s P f)). Qed.
Lemma lem4970716 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term460 A B _62510 s P f) = (term485 A B _62510 s P f).
Proof. exact (EQ_MP (@lem4970715 A B _62510 s P f) (@lem4970690 A B _62510 s P f)). Qed.
Lemma lem4970717 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term373 A B _62510 s P f) = (term485 A B _62510 s P f).
Proof. exact (TRANS (@lem4970686 A B _62510 s P f) (@lem4970716 A B _62510 s P f)). Qed.
Lemma lem4970718 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term382 A B _62510 s P) = (term486 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970717 A B _62510 s P f)). Qed.
Lemma lem4970719 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970720 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term397 A B _62510 s P) = (term487 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970719 A B) (@lem4970718 A B _62510 s P)). Qed.
Lemma lem4970722 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4970723 {A B : Type'} (P : type513 A B) : (term488 A B P) = (term489 A B P).
Proof. exact (@lem4970722 (A -> B) (A -> A) P). Qed.
Lemma lem4970724 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term490 A B _62510 s P) = (term491 A B _62510 s P).
Proof. exact (@lem4970723 A B (term492 A B _62510 s P)). Qed.
Lemma lem4970725 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term493 A B _62510 s P f) = (term484 A B _62510 s P f).
Proof. exact (eq_refl (term493 A B _62510 s P f)). Qed.
Lemma lem4970726 {A : Type'} (x : A -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4970727 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term494 A B _62510 s P f x) = (term495 A B _62510 s P f x).
Proof. exact (MK_COMB (@lem4970725 A B _62510 s P f) (@lem4970726 A x)). Qed.
Lemma lem4970728 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term495 A B _62510 s P f x) = (term482 A B _62510 s P f x).
Proof. exact (eq_refl (term495 A B _62510 s P f x)). Qed.
Lemma lem4970729 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term494 A B _62510 s P f x) = (term482 A B _62510 s P f x).
Proof. exact (TRANS (@lem4970727 A B _62510 s P f x) (@lem4970728 A B _62510 s P f x)). Qed.
Lemma lem4970730 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term496 A B _62510 s P f) = (term484 A B _62510 s P f).
Proof. exact (fun_ext (fun x : A -> A => @lem4970729 A B _62510 s P f x)). Qed.
Lemma lem4970731 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4970732 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term497 A B _62510 s P f) = (term485 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4970731 A) (@lem4970730 A B _62510 s P f)). Qed.
Lemma lem4970733 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term498 A B _62510 s P) = (term486 A B _62510 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4970732 A B _62510 s P f)). Qed.
Lemma lem4970734 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970735 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term490 A B _62510 s P) = (term487 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970734 A B) (@lem4970733 A B _62510 s P)). Qed.
Lemma lem4970736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970737 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term499 A B _62510 s P) = (term500 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970736) (@lem4970735 A B _62510 s P)). Qed.
Lemma lem4970738 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term493 A B _62510 s P f) = (term484 A B _62510 s P f).
Proof. exact (eq_refl (term493 A B _62510 s P f)). Qed.
Lemma lem4970739 {A B : Type'} (x : type548 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4970740 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term501 A B _62510 s P x f) = (term502 A B _62510 s P x f).
Proof. exact (MK_COMB (@lem4970738 A B _62510 s P f) (@lem4970739 A B x f)). Qed.
Lemma lem4970741 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term502 A B _62510 s P x f) = (term503 A B _62510 s P x f).
Proof. exact (eq_refl (term502 A B _62510 s P x f)). Qed.
Lemma lem4970742 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term501 A B _62510 s P x f) = (term503 A B _62510 s P x f).
Proof. exact (TRANS (@lem4970740 A B _62510 s P x f) (@lem4970741 A B _62510 s P x f)). Qed.
Lemma lem4970743 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term504 A B _62510 s P x) = (term505 A B _62510 s P x).
Proof. exact (fun_ext (fun f : A -> B => @lem4970742 A B _62510 s P x f)). Qed.
Lemma lem4970744 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4970745 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term506 A B _62510 s P x) = (term507 A B _62510 s P x).
Proof. exact (MK_COMB (@lem4970744 A B) (@lem4970743 A B _62510 s P x)). Qed.
Lemma lem4970746 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term508 A B _62510 s P) = (term509 A B _62510 s P).
Proof. exact (fun_ext (fun x : type548 A B => @lem4970745 A B _62510 s P x)). Qed.
Lemma lem4970747 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem4970748 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term491 A B _62510 s P) = (term510 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970747 A B) (@lem4970746 A B _62510 s P)). Qed.
Lemma lem4970749 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((term490 A B _62510 s P) = (term491 A B _62510 s P)) = ((term487 A B _62510 s P) = (term510 A B _62510 s P)).
Proof. exact (MK_COMB (@lem4970737 A B _62510 s P) (@lem4970748 A B _62510 s P)). Qed.
Lemma lem4970750 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term487 A B _62510 s P) = (term510 A B _62510 s P).
Proof. exact (EQ_MP (@lem4970749 A B _62510 s P) (@lem4970724 A B _62510 s P)). Qed.
Lemma lem4970751 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term397 A B _62510 s P) = (term510 A B _62510 s P).
Proof. exact (TRANS (@lem4970720 A B _62510 s P) (@lem4970750 A B _62510 s P)). Qed.
Lemma lem4970752 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term406 A B _62510 s) = (term511 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970751 A B _62510 s P)). Qed.
Lemma lem4970753 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970754 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term421 A B _62510 s) = (term512 A B _62510 s).
Proof. exact (MK_COMB (@lem4970753 B) (@lem4970752 A B _62510 s)). Qed.
Lemma lem4970756 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4970757 {A B : Type'} (P : type817 A B) : (term513 A B P) = (term514 A B P).
Proof. exact (@lem4970756 (B -> Prop) (type548 A B) P). Qed.
Lemma lem4970758 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term515 A B _62510 s) = (term516 A B _62510 s).
Proof. exact (@lem4970757 A B (term517 A B _62510 s)). Qed.
Lemma lem4970759 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term518 A B _62510 s P) = (term509 A B _62510 s P).
Proof. exact (eq_refl (term518 A B _62510 s P)). Qed.
Lemma lem4970760 {A B : Type'} (x : type548 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4970761 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term519 A B _62510 s P x) = (term520 A B _62510 s P x).
Proof. exact (MK_COMB (@lem4970759 A B _62510 s P) (@lem4970760 A B x)). Qed.
Lemma lem4970762 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term520 A B _62510 s P x) = (term507 A B _62510 s P x).
Proof. exact (eq_refl (term520 A B _62510 s P x)). Qed.
Lemma lem4970763 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term519 A B _62510 s P x) = (term507 A B _62510 s P x).
Proof. exact (TRANS (@lem4970761 A B _62510 s P x) (@lem4970762 A B _62510 s P x)). Qed.
Lemma lem4970764 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term521 A B _62510 s P) = (term509 A B _62510 s P).
Proof. exact (fun_ext (fun x : type548 A B => @lem4970763 A B _62510 s P x)). Qed.
Lemma lem4970765 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem4970766 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term522 A B _62510 s P) = (term510 A B _62510 s P).
Proof. exact (MK_COMB (@lem4970765 A B) (@lem4970764 A B _62510 s P)). Qed.
Lemma lem4970767 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term523 A B _62510 s) = (term511 A B _62510 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970766 A B _62510 s P)). Qed.
Lemma lem4970768 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970769 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term515 A B _62510 s) = (term512 A B _62510 s).
Proof. exact (MK_COMB (@lem4970768 B) (@lem4970767 A B _62510 s)). Qed.
Lemma lem4970770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970771 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term524 A B _62510 s) = (term525 A B _62510 s).
Proof. exact (MK_COMB (@lem4970770) (@lem4970769 A B _62510 s)). Qed.
Lemma lem4970772 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term518 A B _62510 s P) = (term509 A B _62510 s P).
Proof. exact (eq_refl (term518 A B _62510 s P)). Qed.
Lemma lem4970773 {A B : Type'} (x : type831 A B) (P : B -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem4970774 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term526 A B _62510 s x P) = (term527 A B _62510 s x P).
Proof. exact (MK_COMB (@lem4970772 A B _62510 s P) (@lem4970773 A B x P)). Qed.
Lemma lem4970775 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term527 A B _62510 s x P) = (term528 A B _62510 s x P).
Proof. exact (eq_refl (term527 A B _62510 s x P)). Qed.
Lemma lem4970776 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term526 A B _62510 s x P) = (term528 A B _62510 s x P).
Proof. exact (TRANS (@lem4970774 A B _62510 s x P) (@lem4970775 A B _62510 s x P)). Qed.
Lemma lem4970777 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term529 A B _62510 s x) = (term530 A B _62510 s x).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4970776 A B _62510 s x P)). Qed.
Lemma lem4970778 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4970779 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term531 A B _62510 s x) = (term532 A B _62510 s x).
Proof. exact (MK_COMB (@lem4970778 B) (@lem4970777 A B _62510 s x)). Qed.
Lemma lem4970780 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term533 A B _62510 s) = (term534 A B _62510 s).
Proof. exact (fun_ext (fun x : type831 A B => @lem4970779 A B _62510 s x)). Qed.
Lemma lem4970781 {A B : Type'} : (@ex ((B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4970782 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term516 A B _62510 s) = (term535 A B _62510 s).
Proof. exact (MK_COMB (@lem4970781 A B) (@lem4970780 A B _62510 s)). Qed.
Lemma lem4970783 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : ((term515 A B _62510 s) = (term516 A B _62510 s)) = ((term512 A B _62510 s) = (term535 A B _62510 s)).
Proof. exact (MK_COMB (@lem4970771 A B _62510 s) (@lem4970782 A B _62510 s)). Qed.
Lemma lem4970784 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term512 A B _62510 s) = (term535 A B _62510 s).
Proof. exact (EQ_MP (@lem4970783 A B _62510 s) (@lem4970758 A B _62510 s)). Qed.
Lemma lem4970785 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term421 A B _62510 s) = (term535 A B _62510 s).
Proof. exact (TRANS (@lem4970754 A B _62510 s) (@lem4970784 A B _62510 s)). Qed.
Lemma lem4970786 {A B : Type'} (_62510 : type653 A B) : (term428 A B _62510) = (term536 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970785 A B _62510 s)). Qed.
Lemma lem4970787 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970788 {A B : Type'} (_62510 : type653 A B) : (term443 A B _62510) = (term537 A B _62510).
Proof. exact (MK_COMB (@lem4970787 A) (@lem4970786 A B _62510)). Qed.
Lemma lem4970790 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4970791 {A B : Type'} (P : type605 A B) : (term538 A B P) = (term539 A B P).
Proof. exact (@lem4970790 (A -> Prop) (type831 A B) P). Qed.
Lemma lem4970792 {A B : Type'} (_62510 : type653 A B) : (term540 A B _62510) = (term541 A B _62510).
Proof. exact (@lem4970791 A B (term542 A B _62510)). Qed.
Lemma lem4970793 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term543 A B _62510 s) = (term534 A B _62510 s).
Proof. exact (eq_refl (term543 A B _62510 s)). Qed.
Lemma lem4970794 {A B : Type'} (x : type831 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4970795 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term544 A B _62510 s x) = (term545 A B _62510 s x).
Proof. exact (MK_COMB (@lem4970793 A B _62510 s) (@lem4970794 A B x)). Qed.
Lemma lem4970796 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term545 A B _62510 s x) = (term532 A B _62510 s x).
Proof. exact (eq_refl (term545 A B _62510 s x)). Qed.
Lemma lem4970797 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term544 A B _62510 s x) = (term532 A B _62510 s x).
Proof. exact (TRANS (@lem4970795 A B _62510 s x) (@lem4970796 A B _62510 s x)). Qed.
Lemma lem4970798 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term546 A B _62510 s) = (term534 A B _62510 s).
Proof. exact (fun_ext (fun x : type831 A B => @lem4970797 A B _62510 s x)). Qed.
Lemma lem4970799 {A B : Type'} : (@ex ((B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4970800 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term547 A B _62510 s) = (term535 A B _62510 s).
Proof. exact (MK_COMB (@lem4970799 A B) (@lem4970798 A B _62510 s)). Qed.
Lemma lem4970801 {A B : Type'} (_62510 : type653 A B) : (term548 A B _62510) = (term536 A B _62510).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970800 A B _62510 s)). Qed.
Lemma lem4970802 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970803 {A B : Type'} (_62510 : type653 A B) : (term540 A B _62510) = (term537 A B _62510).
Proof. exact (MK_COMB (@lem4970802 A) (@lem4970801 A B _62510)). Qed.
Lemma lem4970804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970805 {A B : Type'} (_62510 : type653 A B) : (term549 A B _62510) = (term550 A B _62510).
Proof. exact (MK_COMB (@lem4970804) (@lem4970803 A B _62510)). Qed.
Lemma lem4970806 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (term543 A B _62510 s) = (term534 A B _62510 s).
Proof. exact (eq_refl (term543 A B _62510 s)). Qed.
Lemma lem4970807 {A B : Type'} (x : type652 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4970808 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term551 A B _62510 x s) = (term552 A B _62510 x s).
Proof. exact (MK_COMB (@lem4970806 A B _62510 s) (@lem4970807 A B x s)). Qed.
Lemma lem4970809 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term552 A B _62510 x s) = (term553 A B _62510 x s).
Proof. exact (eq_refl (term552 A B _62510 x s)). Qed.
Lemma lem4970810 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term551 A B _62510 x s) = (term553 A B _62510 x s).
Proof. exact (TRANS (@lem4970808 A B _62510 x s) (@lem4970809 A B _62510 x s)). Qed.
Lemma lem4970811 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) : (term554 A B _62510 x) = (term555 A B _62510 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4970810 A B _62510 x s)). Qed.
Lemma lem4970812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4970813 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) : (term556 A B _62510 x) = (term557 A B _62510 x).
Proof. exact (MK_COMB (@lem4970812 A) (@lem4970811 A B _62510 x)). Qed.
Lemma lem4970814 {A B : Type'} (_62510 : type653 A B) : (term558 A B _62510) = (term559 A B _62510).
Proof. exact (fun_ext (fun x : type652 A B => @lem4970813 A B _62510 x)). Qed.
Lemma lem4970815 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4970816 {A B : Type'} (_62510 : type653 A B) : (term541 A B _62510) = (term560 A B _62510).
Proof. exact (MK_COMB (@lem4970815 A B) (@lem4970814 A B _62510)). Qed.
Lemma lem4970817 {A B : Type'} (_62510 : type653 A B) : ((term540 A B _62510) = (term541 A B _62510)) = ((term537 A B _62510) = (term560 A B _62510)).
Proof. exact (MK_COMB (@lem4970805 A B _62510) (@lem4970816 A B _62510)). Qed.
Lemma lem4970818 {A B : Type'} (_62510 : type653 A B) : (term537 A B _62510) = (term560 A B _62510).
Proof. exact (EQ_MP (@lem4970817 A B _62510) (@lem4970792 A B _62510)). Qed.
Lemma lem4970819 {A B : Type'} (_62510 : type653 A B) : (term443 A B _62510) = (term560 A B _62510).
Proof. exact (TRANS (@lem4970788 A B _62510) (@lem4970818 A B _62510)). Qed.
Lemma lem4970820 {A B : Type'} (_62510 : type653 A B) : (term440 A B _62510) = (term440 A B _62510).
Proof. exact (eq_refl (term440 A B _62510)). Qed.
Lemma lem4970821 {A B : Type'} (_62510 : type653 A B) : (term444 A B _62510) = (term561 A B _62510).
Proof. exact (MK_COMB (@lem4970820 A B _62510) (@lem4970819 A B _62510)). Qed.
Lemma lem4970823 {A : Type'} (P : Prop) (Q : A -> Prop) : (term562 A P Q) = (term563 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4970824 {A B : Type'} (P : Prop) (Q : type144 A B) : (term564 A B P Q) = (term565 A B P Q).
Proof. exact (@lem4970823 (type652 A B) P Q). Qed.
Lemma lem4970825 {A B : Type'} (_62510 : type653 A B) : (term566 A B _62510) = (term567 A B _62510).
Proof. exact (@lem4970824 A B (term438 A B _62510) (term559 A B _62510)). Qed.
Lemma lem4970826 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) : (term568 A B _62510 x) = (term557 A B _62510 x).
Proof. exact (eq_refl (term568 A B _62510 x)). Qed.
Lemma lem4970827 {A B : Type'} (_62510 : type653 A B) : (term569 A B _62510) = (term559 A B _62510).
Proof. exact (fun_ext (fun x : type652 A B => @lem4970826 A B _62510 x)). Qed.
Lemma lem4970828 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4970829 {A B : Type'} (_62510 : type653 A B) : (term570 A B _62510) = (term560 A B _62510).
Proof. exact (MK_COMB (@lem4970828 A B) (@lem4970827 A B _62510)). Qed.
Lemma lem4970830 {A B : Type'} (_62510 : type653 A B) : (term440 A B _62510) = (term440 A B _62510).
Proof. exact (eq_refl (term440 A B _62510)). Qed.
Lemma lem4970831 {A B : Type'} (_62510 : type653 A B) : (term566 A B _62510) = (term561 A B _62510).
Proof. exact (MK_COMB (@lem4970830 A B _62510) (@lem4970829 A B _62510)). Qed.
Lemma lem4970832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4970833 {A B : Type'} (_62510 : type653 A B) : (term571 A B _62510) = (term572 A B _62510).
Proof. exact (MK_COMB (@lem4970832) (@lem4970831 A B _62510)). Qed.
Lemma lem4970834 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) : (term568 A B _62510 x) = (term557 A B _62510 x).
Proof. exact (eq_refl (term568 A B _62510 x)). Qed.
Lemma lem4970835 {A B : Type'} (_62510 : type653 A B) : (term440 A B _62510) = (term440 A B _62510).
Proof. exact (eq_refl (term440 A B _62510)). Qed.
Lemma lem4970836 {A B : Type'} (_62510 : type653 A B) (x : type652 A B) : (term573 A B _62510 x) = (term574 A B _62510 x).
Proof. exact (MK_COMB (@lem4970835 A B _62510) (@lem4970834 A B _62510 x)). Qed.
Lemma lem4970837 {A B : Type'} (_62510 : type653 A B) : (term575 A B _62510) = (term576 A B _62510).
Proof. exact (fun_ext (fun x : type652 A B => @lem4970836 A B _62510 x)). Qed.
Lemma lem4970838 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4970839 {A B : Type'} (_62510 : type653 A B) : (term567 A B _62510) = (term577 A B _62510).
Proof. exact (MK_COMB (@lem4970838 A B) (@lem4970837 A B _62510)). Qed.
Lemma lem4970840 {A B : Type'} (_62510 : type653 A B) : ((term566 A B _62510) = (term567 A B _62510)) = ((term561 A B _62510) = (term577 A B _62510)).
Proof. exact (MK_COMB (@lem4970833 A B _62510) (@lem4970839 A B _62510)). Qed.
Lemma lem4970841 {A B : Type'} (_62510 : type653 A B) : (term561 A B _62510) = (term577 A B _62510).
Proof. exact (EQ_MP (@lem4970840 A B _62510) (@lem4970825 A B _62510)). Qed.
Lemma lem4970842 {A B : Type'} (_62510 : type653 A B) : (term444 A B _62510) = (term577 A B _62510).
Proof. exact (TRANS (@lem4970821 A B _62510) (@lem4970841 A B _62510)). Qed.
Lemma lem4970843 {A B : Type'} (_62510 : type653 A B) : (term352 A B _62510) = (term577 A B _62510).
Proof. exact (TRANS (@lem4970663 A B _62510) (@lem4970842 A B _62510)). Qed.
Lemma lem4970844 {A B : Type'} (_62510 : type653 A B) : (term319 A B _62510) = (term577 A B _62510).
Proof. exact (TRANS (@lem4970067 A B _62510) (@lem4970843 A B _62510)). Qed.
Lemma lem4970845 {A B : Type'} (_62510 : type653 A B) (h1 : term319 A B _62510) : term577 A B _62510.
Proof. exact (EQ_MP (@lem4970844 A B _62510) (@lem4970020 A B _62510 h1)). Qed.
Lemma lem4970854 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term578 A B s x f y) = (term579 A B s x f y).
Proof. exact (@lem17045 (s y) ((f x) = (f y))). Qed.
Lemma lem4970856 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term580 A s x).
Proof. exact (eq_refl (term580 A s x)). Qed.
Lemma lem4970857 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term581 A B s x f y) = (term582 A B s x f y).
Proof. exact (MK_COMB (@lem4970856 A s x) (@lem4970854 A B s x f y)). Qed.
Lemma lem4970858 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term583 A B s x f y) = (term581 A B s x f y).
Proof. exact (@lem17045 (s x) (term108 A B s x f y)). Qed.
Lemma lem4970859 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term583 A B s x f y) = (term582 A B s x f y).
Proof. exact (TRANS (@lem4970858 A B s x f y) (@lem4970857 A B s x f y)). Qed.
Lemma lem4970860 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4970861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4970862 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term584 A B s x f y) = (term585 A B s x f y).
Proof. exact (MK_COMB (@lem4970861) (@lem4970859 A B s x f y)). Qed.
Lemma lem4970863 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term586 A B s f x y) = (term587 A B s f x y).
Proof. exact (MK_COMB (@lem4970862 A B s x f y) (@lem4970860 A x y)). Qed.
Lemma lem4970864 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term586 A B s f x y).
Proof. exact (@lem17265 (term110 A B s x f y) (x = y)). Qed.
Lemma lem4970865 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term587 A B s f x y).
Proof. exact (TRANS (@lem4970864 A B s f x y) (@lem4970863 A B s f x y)). Qed.
Lemma lem4970866 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term588 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4970865 A B s f x y)). Qed.
Lemma lem4970867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970868 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term589 A B s f x).
Proof. exact (MK_COMB (@lem4970867 A) (@lem4970866 A B s f x)). Qed.
Lemma lem4970869 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term590 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4970868 A B s f x)). Qed.
Lemma lem4970870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970871 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term591 A B s f).
Proof. exact (MK_COMB (@lem4970870 A) (@lem4970869 A B s f)). Qed.
Lemma lem4970878 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term592 A B x f s x') = (term593 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem4970879 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4970880 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term594 A B x f s) = (term595 A B x f s).
Proof. exact (@lem4970879 A (term125 A B x f s)). Qed.
Lemma lem4970881 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term596 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term596 A B x f s x')). Qed.
Lemma lem4970882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4970883 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term597 A B x f s x') = (term592 A B x f s x').
Proof. exact (MK_COMB (@lem4970882) (@lem4970881 A B x f s x')). Qed.
Lemma lem4970884 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term597 A B x f s x') = (term593 A B x f s x').
Proof. exact (TRANS (@lem4970883 A B x f s x') (@lem4970878 A B x f s x')). Qed.
Lemma lem4970885 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term598 A B x f s) = (term599 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4970884 A B x f s x')). Qed.
Lemma lem4970886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4970887 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term595 A B x f s) = (term600 A B x f s).
Proof. exact (MK_COMB (@lem4970886 A) (@lem4970885 A B x f s)). Qed.
Lemma lem4970888 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term594 A B x f s) = (term600 A B x f s).
Proof. exact (TRANS (@lem4970880 A B x f s) (@lem4970887 A B x f s)). Qed.
Lemma lem4970889 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4970890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4970891 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term601 A B x f s) = (term602 A B x f s).
Proof. exact (MK_COMB (@lem4970890) (@lem4970888 A B x f s)). Qed.
Lemma lem4970892 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term603 A B f s t x) = (term604 A B f s t x).
Proof. exact (MK_COMB (@lem4970891 A B x f s) (@lem4970889 B t x)). Qed.
Lemma lem4970893 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term603 A B f s t x).
Proof. exact (@lem17265 (term126 A B x f s) (t x)). Qed.
Lemma lem4970894 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term604 A B f s t x).
Proof. exact (TRANS (@lem4970893 A B f s t x) (@lem4970892 A B f s t x)). Qed.
Lemma lem4970895 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term605 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4970894 A B f s t x)). Qed.
Lemma lem4970896 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4970897 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term606 A B f s t).
Proof. exact (MK_COMB (@lem4970896 B) (@lem4970895 A B f s t)). Qed.
Lemma lem4970906 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4970907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970908 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term607 A B f s t).
Proof. exact (MK_COMB (@lem4970907) (@lem4970897 A B f s t)). Qed.
Lemma lem4970909 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term608 A B f t s).
Proof. exact (MK_COMB (@lem4970908 A B f s t) (@lem4970906 A B t s)). Qed.
Lemma lem4970910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4970911 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term609 A B s f).
Proof. exact (MK_COMB (@lem4970910) (@lem4970871 A B s f)). Qed.
Lemma lem4970912 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term610 A B f t s).
Proof. exact (MK_COMB (@lem4970911 A B s f) (@lem4970909 A B f t s)). Qed.
Lemma lem4970914 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62510 s P f n) = (term238 A B _62510 s P f n).
Proof. exact (eq_refl (term238 A B _62510 s P f n)). Qed.
Lemma lem4971051 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term239 A B _62510 P n f t s) = (term611 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4970914 A B _62510 s P f n) (@lem4970912 A B f t s)). Qed.
Lemma lem4971052 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term611 A B _62510 P n f t s.
Proof. exact (EQ_MP (@lem4971051 A B _62510 P n f t s) (@lem4970021 A B _62510 P n f t s h1)). Qed.
Lemma lem4971058 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term142 A B s f x y) = (term142 A B s f x y).
Proof. exact (eq_refl (term142 A B s f x y)). Qed.
Lemma lem4971059 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term144 A B s f y) = (term144 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4971058 A B s f x y)). Qed.
Lemma lem4971060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971061 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term146 A B s f y) = (term146 A B s f y).
Proof. exact (MK_COMB (@lem4971060 A) (@lem4971059 A B s f y)). Qed.
Lemma lem4971063 {B : Type'} (t : B -> Prop) (y : B) : (term580 B t y) = (term580 B t y).
Proof. exact (eq_refl (term580 B t y)). Qed.
Lemma lem4971064 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term612 A B t s f y) = (term612 A B t s f y).
Proof. exact (MK_COMB (@lem4971063 B t y) (@lem4971061 A B s f y)). Qed.
Lemma lem4971065 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term148 A B t s f y) = (term612 A B t s f y).
Proof. exact (@lem17265 (t y) (term146 A B s f y)). Qed.
Lemma lem4971066 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term148 A B t s f y) = (term612 A B t s f y).
Proof. exact (TRANS (@lem4971065 A B t s f y) (@lem4971064 A B t s f y)). Qed.
Lemma lem4971067 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term150 A B t s f) = (term613 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4971066 A B t s f y)). Qed.
Lemma lem4971068 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971069 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term151 A B t s f) = (term614 A B t s f).
Proof. exact (MK_COMB (@lem4971068 B) (@lem4971067 A B t s f)). Qed.
Lemma lem4971148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4971149 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (@lem4971148 A P Q). Qed.
Lemma lem4971150 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term615 A B t s f y) = (term616 A B t s f y).
Proof. exact (@lem4971149 A (term617 B t y) (term144 A B s f y)). Qed.
Lemma lem4971151 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term618 A B s f y x) = (term142 A B s f x y).
Proof. exact (eq_refl (term618 A B s f y x)). Qed.
Lemma lem4971152 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term619 A B s f y) = (term144 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4971151 A B s f x y)). Qed.
Lemma lem4971153 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971154 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term620 A B s f y) = (term146 A B s f y).
Proof. exact (MK_COMB (@lem4971153 A) (@lem4971152 A B s f y)). Qed.
Lemma lem4971155 {B : Type'} (t : B -> Prop) (y : B) : (term580 B t y) = (term580 B t y).
Proof. exact (eq_refl (term580 B t y)). Qed.
Lemma lem4971156 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term615 A B t s f y) = (term612 A B t s f y).
Proof. exact (MK_COMB (@lem4971155 B t y) (@lem4971154 A B s f y)). Qed.
Lemma lem4971157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4971158 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term621 A B t s f y) = (term622 A B t s f y).
Proof. exact (MK_COMB (@lem4971157) (@lem4971156 A B t s f y)). Qed.
Lemma lem4971159 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term618 A B s f y x) = (term142 A B s f x y).
Proof. exact (eq_refl (term618 A B s f y x)). Qed.
Lemma lem4971160 {B : Type'} (t : B -> Prop) (y : B) : (term580 B t y) = (term580 B t y).
Proof. exact (eq_refl (term580 B t y)). Qed.
Lemma lem4971161 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term623 A B t s f y x) = (term624 A B t s f x y).
Proof. exact (MK_COMB (@lem4971160 B t y) (@lem4971159 A B s f x y)). Qed.
Lemma lem4971162 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term625 A B t s f y) = (term626 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4971161 A B t s f x y)). Qed.
Lemma lem4971163 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971164 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term616 A B t s f y) = (term627 A B t s f y).
Proof. exact (MK_COMB (@lem4971163 A) (@lem4971162 A B t s f y)). Qed.
Lemma lem4971165 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : ((term615 A B t s f y) = (term616 A B t s f y)) = ((term612 A B t s f y) = (term627 A B t s f y)).
Proof. exact (MK_COMB (@lem4971158 A B t s f y) (@lem4971164 A B t s f y)). Qed.
Lemma lem4971166 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term612 A B t s f y) = (term627 A B t s f y).
Proof. exact (EQ_MP (@lem4971165 A B t s f y) (@lem4971150 A B t s f y)). Qed.
Lemma lem4971167 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term613 A B t s f) = (term628 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4971166 A B t s f y)). Qed.
Lemma lem4971168 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971169 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term614 A B t s f) = (term629 A B t s f).
Proof. exact (MK_COMB (@lem4971168 B) (@lem4971167 A B t s f)). Qed.
Lemma lem4971171 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4971172 {A B : Type'} (P : type1470 A B) : (term630 A B P) = (term631 A B P).
Proof. exact (@lem4971171 B A P). Qed.
Lemma lem4971173 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term632 A B t s f) = (term633 A B t s f).
Proof. exact (@lem4971172 A B (term634 A B t s f)). Qed.
Lemma lem4971174 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term635 A B t s f y) = (term626 A B t s f y).
Proof. exact (eq_refl (term635 A B t s f y)). Qed.
Lemma lem4971175 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4971176 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term636 A B t s f y x) = (term637 A B t s f y x).
Proof. exact (MK_COMB (@lem4971174 A B t s f y) (@lem4971175 A x)). Qed.
Lemma lem4971177 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term637 A B t s f y x) = (term624 A B t s f x y).
Proof. exact (eq_refl (term637 A B t s f y x)). Qed.
Lemma lem4971178 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term636 A B t s f y x) = (term624 A B t s f x y).
Proof. exact (TRANS (@lem4971176 A B t s f y x) (@lem4971177 A B t s f x y)). Qed.
Lemma lem4971179 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term638 A B t s f y) = (term626 A B t s f y).
Proof. exact (fun_ext (fun x : A => @lem4971178 A B t s f x y)). Qed.
Lemma lem4971180 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971181 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term639 A B t s f y) = (term627 A B t s f y).
Proof. exact (MK_COMB (@lem4971180 A) (@lem4971179 A B t s f y)). Qed.
Lemma lem4971182 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term640 A B t s f) = (term628 A B t s f).
Proof. exact (fun_ext (fun y : B => @lem4971181 A B t s f y)). Qed.
Lemma lem4971183 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term632 A B t s f) = (term629 A B t s f).
Proof. exact (MK_COMB (@lem4971183 B) (@lem4971182 A B t s f)). Qed.
Lemma lem4971185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4971186 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term641 A B t s f) = (term642 A B t s f).
Proof. exact (MK_COMB (@lem4971185) (@lem4971184 A B t s f)). Qed.
Lemma lem4971187 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term635 A B t s f y) = (term626 A B t s f y).
Proof. exact (eq_refl (term635 A B t s f y)). Qed.
Lemma lem4971188 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4971189 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term643 A B t s f x y) = (term644 A B t s f x y).
Proof. exact (MK_COMB (@lem4971187 A B t s f y) (@lem4971188 A B x y)). Qed.
Lemma lem4971190 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term644 A B t s f x y) = (term645 A B t s f x y).
Proof. exact (eq_refl (term644 A B t s f x y)). Qed.
Lemma lem4971191 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term643 A B t s f x y) = (term645 A B t s f x y).
Proof. exact (TRANS (@lem4971189 A B t s f x y) (@lem4971190 A B t s f x y)). Qed.
Lemma lem4971192 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) : (term646 A B t s f x) = (term647 A B t s f x).
Proof. exact (fun_ext (fun y : B => @lem4971191 A B t s f x y)). Qed.
Lemma lem4971193 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971194 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B -> A) : (term648 A B t s f x) = (term649 A B t s f x).
Proof. exact (MK_COMB (@lem4971193 B) (@lem4971192 A B t s f x)). Qed.
Lemma lem4971195 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term650 A B t s f) = (term651 A B t s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4971194 A B t s f x)). Qed.
Lemma lem4971196 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4971197 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term633 A B t s f) = (term652 A B t s f).
Proof. exact (MK_COMB (@lem4971196 A B) (@lem4971195 A B t s f)). Qed.
Lemma lem4971198 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : ((term632 A B t s f) = (term633 A B t s f)) = ((term629 A B t s f) = (term652 A B t s f)).
Proof. exact (MK_COMB (@lem4971186 A B t s f) (@lem4971197 A B t s f)). Qed.
Lemma lem4971199 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term629 A B t s f) = (term652 A B t s f).
Proof. exact (EQ_MP (@lem4971198 A B t s f) (@lem4971173 A B t s f)). Qed.
Lemma lem4971201 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term614 A B t s f) = (term652 A B t s f).
Proof. exact (TRANS (@lem4971169 A B t s f) (@lem4971199 A B t s f)). Qed.
Lemma lem4971202 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term151 A B t s f) = (term652 A B t s f).
Proof. exact (TRANS (@lem4971069 A B t s f) (@lem4971201 A B t s f)). Qed.
Lemma lem4971203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term151 A B t s f) : term652 A B t s f.
Proof. exact (EQ_MP (@lem4971202 A B t s f) (@lem4970022 A B t s f h1)). Qed.
Lemma lem4971212 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term653 B t P x) = (term654 B t P x).
Proof. exact (@lem17045 (t x) (P x)). Qed.
Lemma lem4971226 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term655 A B s P f x) = (term656 A B s P f x).
Proof. exact (@lem17045 (s x) (term88 A B P f x)). Qed.
Lemma lem4971231 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term657 A B x f x') = (term657 A B x f x').
Proof. exact (eq_refl (term657 A B x f x')). Qed.
Lemma lem4971232 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term658 A B x s P f x') = (term659 A B x s P f x').
Proof. exact (MK_COMB (@lem4971231 A B x f x') (@lem4971226 A B s P f x')). Qed.
Lemma lem4971233 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term660 A B x s P f x') = (term658 A B x s P f x').
Proof. exact (@lem17045 (x = (f x')) (term90 A B s P f x')). Qed.
Lemma lem4971234 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term660 A B x s P f x') = (term659 A B x s P f x').
Proof. exact (TRANS (@lem4971233 A B x s P f x') (@lem4971232 A B x s P f x')). Qed.
Lemma lem4971237 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term189 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term189 A B x s P f x')). Qed.
Lemma lem4971238 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4971239 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term661 A B x s P f) = (term662 A B x s P f).
Proof. exact (@lem4971238 A (term191 A B x s P f)). Qed.
Lemma lem4971240 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term663 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term663 A B x s P f x')). Qed.
Lemma lem4971241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971242 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term664 A B x s P f x') = (term660 A B x s P f x').
Proof. exact (MK_COMB (@lem4971241) (@lem4971240 A B x s P f x')). Qed.
Lemma lem4971243 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term664 A B x s P f x') = (term659 A B x s P f x').
Proof. exact (TRANS (@lem4971242 A B x s P f x') (@lem4971234 A B x s P f x')). Qed.
Lemma lem4971244 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term665 A B x s P f) = (term666 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971243 A B x s P f x')). Qed.
Lemma lem4971245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4971246 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term662 A B x s P f) = (term667 A B x s P f).
Proof. exact (MK_COMB (@lem4971245 A) (@lem4971244 A B x s P f)). Qed.
Lemma lem4971247 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term661 A B x s P f) = (term667 A B x s P f).
Proof. exact (TRANS (@lem4971239 A B x s P f) (@lem4971246 A B x s P f)). Qed.
Lemma lem4971248 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term191 A B x s P f) = (term191 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971237 A B x s P f x')). Qed.
Lemma lem4971249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971250 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term192 A B x s P f) = (term192 A B x s P f).
Proof. exact (MK_COMB (@lem4971249 A) (@lem4971248 A B x s P f)). Qed.
Lemma lem4971251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971252 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term668 B t P x) = (term669 B t P x).
Proof. exact (MK_COMB (@lem4971251) (@lem4971212 B t P x)). Qed.
Lemma lem4971253 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term670 A B t x s P f) = (term671 A B t x s P f).
Proof. exact (MK_COMB (@lem4971252 B t P x) (@lem4971250 A B x s P f)). Qed.
Lemma lem4971255 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term672 B t P x) = (term672 B t P x).
Proof. exact (eq_refl (term672 B t P x)). Qed.
Lemma lem4971256 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term673 A B t x s P f) = (term674 A B t x s P f).
Proof. exact (MK_COMB (@lem4971255 B t P x) (@lem4971247 A B x s P f)). Qed.
Lemma lem4971257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971258 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term675 A B t x s P f) = (term676 A B t x s P f).
Proof. exact (MK_COMB (@lem4971257) (@lem4971256 A B t x s P f)). Qed.
Lemma lem4971259 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term677 A B t x s P f) = (term678 A B t x s P f).
Proof. exact (MK_COMB (@lem4971258 A B t x s P f) (@lem4971253 A B t x s P f)). Qed.
Lemma lem4971260 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term325 A B t x s P f) = (term677 A B t x s P f).
Proof. exact (@lem17646 (term172 B t P x) (term192 A B x s P f)). Qed.
Lemma lem4971261 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term325 A B t x s P f) = (term678 A B t x s P f).
Proof. exact (TRANS (@lem4971260 A B t x s P f) (@lem4971259 A B t x s P f)). Qed.
Lemma lem4971360 {A : Type'} (P : Prop) (Q : A -> Prop) : (term562 A P Q) = (term563 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4971361 {A : Type'} (P : Prop) (Q : A -> Prop) : (term562 A P Q) = (term563 A P Q).
Proof. exact (@lem4971360 A P Q). Qed.
Lemma lem4971362 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term679 A B t x s P f) = (term680 A B t x s P f).
Proof. exact (@lem4971361 A (term654 B t P x) (term191 A B x s P f)). Qed.
Lemma lem4971363 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term663 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term663 A B x s P f x')). Qed.
Lemma lem4971364 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term681 A B x s P f) = (term191 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971363 A B x s P f x')). Qed.
Lemma lem4971365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971366 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term682 A B x s P f) = (term192 A B x s P f).
Proof. exact (MK_COMB (@lem4971365 A) (@lem4971364 A B x s P f)). Qed.
Lemma lem4971367 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term669 B t P x) = (term669 B t P x).
Proof. exact (eq_refl (term669 B t P x)). Qed.
Lemma lem4971368 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term679 A B t x s P f) = (term671 A B t x s P f).
Proof. exact (MK_COMB (@lem4971367 B t P x) (@lem4971366 A B x s P f)). Qed.
Lemma lem4971369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4971370 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term683 A B t x s P f) = (term684 A B t x s P f).
Proof. exact (MK_COMB (@lem4971369) (@lem4971368 A B t x s P f)). Qed.
Lemma lem4971371 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term663 A B x s P f x') = (term189 A B x s P f x').
Proof. exact (eq_refl (term663 A B x s P f x')). Qed.
Lemma lem4971372 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term669 B t P x) = (term669 B t P x).
Proof. exact (eq_refl (term669 B t P x)). Qed.
Lemma lem4971373 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term685 A B t x s P f x') = (term686 A B t x s P f x').
Proof. exact (MK_COMB (@lem4971372 B t P x) (@lem4971371 A B x s P f x')). Qed.
Lemma lem4971374 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term687 A B t x s P f) = (term688 A B t x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971373 A B t x s P f x')). Qed.
Lemma lem4971375 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971376 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term680 A B t x s P f) = (term689 A B t x s P f).
Proof. exact (MK_COMB (@lem4971375 A) (@lem4971374 A B t x s P f)). Qed.
Lemma lem4971377 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term679 A B t x s P f) = (term680 A B t x s P f)) = ((term671 A B t x s P f) = (term689 A B t x s P f)).
Proof. exact (MK_COMB (@lem4971370 A B t x s P f) (@lem4971376 A B t x s P f)). Qed.
Lemma lem4971378 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term671 A B t x s P f) = (term689 A B t x s P f).
Proof. exact (EQ_MP (@lem4971377 A B t x s P f) (@lem4971362 A B t x s P f)). Qed.
Lemma lem4971379 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term676 A B t x s P f) = (term676 A B t x s P f).
Proof. exact (eq_refl (term676 A B t x s P f)). Qed.
Lemma lem4971380 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term678 A B t x s P f) = (term690 A B t x s P f).
Proof. exact (MK_COMB (@lem4971379 A B t x s P f) (@lem4971378 A B t x s P f)). Qed.
Lemma lem4971382 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4971383 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (@lem4971382 A P Q). Qed.
Lemma lem4971384 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term691 A B t x s P f) = (term692 A B t x s P f).
Proof. exact (@lem4971383 A (term674 A B t x s P f) (term688 A B t x s P f)). Qed.
Lemma lem4971385 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term693 A B t x s P f x') = (term686 A B t x s P f x').
Proof. exact (eq_refl (term693 A B t x s P f x')). Qed.
Lemma lem4971386 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term694 A B t x s P f) = (term688 A B t x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971385 A B t x s P f x')). Qed.
Lemma lem4971387 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971388 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term695 A B t x s P f) = (term689 A B t x s P f).
Proof. exact (MK_COMB (@lem4971387 A) (@lem4971386 A B t x s P f)). Qed.
Lemma lem4971389 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term676 A B t x s P f) = (term676 A B t x s P f).
Proof. exact (eq_refl (term676 A B t x s P f)). Qed.
Lemma lem4971390 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term691 A B t x s P f) = (term690 A B t x s P f).
Proof. exact (MK_COMB (@lem4971389 A B t x s P f) (@lem4971388 A B t x s P f)). Qed.
Lemma lem4971391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4971392 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term696 A B t x s P f) = (term697 A B t x s P f).
Proof. exact (MK_COMB (@lem4971391) (@lem4971390 A B t x s P f)). Qed.
Lemma lem4971393 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term693 A B t x s P f x') = (term686 A B t x s P f x').
Proof. exact (eq_refl (term693 A B t x s P f x')). Qed.
Lemma lem4971394 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term676 A B t x s P f) = (term676 A B t x s P f).
Proof. exact (eq_refl (term676 A B t x s P f)). Qed.
Lemma lem4971395 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term698 A B t x s P f x') = (term699 A B t x s P f x').
Proof. exact (MK_COMB (@lem4971394 A B t x s P f) (@lem4971393 A B t x s P f x')). Qed.
Lemma lem4971396 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term700 A B t x s P f) = (term701 A B t x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971395 A B t x s P f x')). Qed.
Lemma lem4971397 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4971398 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term692 A B t x s P f) = (term702 A B t x s P f).
Proof. exact (MK_COMB (@lem4971397 A) (@lem4971396 A B t x s P f)). Qed.
Lemma lem4971399 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term691 A B t x s P f) = (term692 A B t x s P f)) = ((term690 A B t x s P f) = (term702 A B t x s P f)).
Proof. exact (MK_COMB (@lem4971392 A B t x s P f) (@lem4971398 A B t x s P f)). Qed.
Lemma lem4971400 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term690 A B t x s P f) = (term702 A B t x s P f).
Proof. exact (EQ_MP (@lem4971399 A B t x s P f) (@lem4971384 A B t x s P f)). Qed.
Lemma lem4971402 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term678 A B t x s P f) = (term702 A B t x s P f).
Proof. exact (TRANS (@lem4971380 A B t x s P f) (@lem4971400 A B t x s P f)). Qed.
Lemma lem4971403 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term325 A B t x s P f) = (term702 A B t x s P f).
Proof. exact (TRANS (@lem4971261 A B t x s P f) (@lem4971402 A B t x s P f)). Qed.
Lemma lem4971404 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term325 A B t x s P f) : term702 A B t x s P f.
Proof. exact (EQ_MP (@lem4971403 A B t x s P f) (@lem4970027 A B t x s P f h1)). Qed.
Lemma lem4971405 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term699 A B t x s P f x') : term699 A B t x s P f x'.
Proof. exact (h1). Qed.
Lemma lem4971406 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term649 A B t s f x''.
Proof. exact (h1). Qed.
Lemma lem4971412 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971413 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4971412 (A -> Prop) Prop f x). Qed.
Lemma lem4971415 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4971413 A (@FINITE A) s). Qed.
Lemma lem4971420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971421 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4971420 (B -> Prop) Prop f x). Qed.
Lemma lem4971423 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@I ((B -> Prop) -> Prop) (@FINITE B) t).
Proof. exact (@lem4971421 B (@FINITE B) t). Qed.
Lemma lem4971424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971425 {B : Type'} (t : B -> Prop) : (term39 B t) = (term703 B t).
Proof. exact (MK_COMB (@lem4971424) (@lem4971423 B t)). Qed.
Lemma lem4971426 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term65 A B t s) = (term704 A B t s).
Proof. exact (MK_COMB (@lem4971425 B t) (@lem4971415 A s)). Qed.
Lemma lem4971427 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4971432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971433 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem4971432 (A -> Prop) nat f x). Qed.
Lemma lem4971435 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem4971433 A (@CARD A) s). Qed.
Lemma lem4971440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971441 {B : Type'} (f : type687 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> nat) f x).
Proof. exact (@lem4971440 (B -> Prop) nat f x). Qed.
Lemma lem4971443 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@I ((B -> Prop) -> nat) (@CARD B) t).
Proof. exact (@lem4971441 B (@CARD B) t). Qed.
Lemma lem4971444 {A : Type'} (s : A -> Prop) : (term40 A s) = (term705 A s).
Proof. exact (MK_COMB (@lem4971427) (@lem4971435 A s)). Qed.
Lemma lem4971445 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((@CARD A s) = (@CARD B t)) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((B -> Prop) -> nat) (@CARD B) t)).
Proof. exact (MK_COMB (@lem4971444 A s) (@lem4971443 B t)). Qed.
Lemma lem4971446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971447 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term41 A B s t) = (term706 A B s t).
Proof. exact (MK_COMB (@lem4971446) (@lem4971445 A B s t)). Qed.
Lemma lem4971448 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term707 A B t s).
Proof. exact (MK_COMB (@lem4971447 A B s t) (@lem4971426 A B t s)). Qed.
Lemma lem4971453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971454 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971453 B Prop f x). Qed.
Lemma lem4971456 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4971454 B t x). Qed.
Lemma lem4971457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971463 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971462 A Prop f x). Qed.
Lemma lem4971465 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4971463 A s x). Qed.
Lemma lem4971466 {A : Type'} (s : A -> Prop) (x : A) : (term617 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem4971457) (@lem4971465 A s x)). Qed.
Lemma lem4971467 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971474 A B f x). Qed.
Lemma lem4971477 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4971478 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem4971477 B x) (@lem4971476 A B f x')). Qed.
Lemma lem4971479 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term709 A B x f x') = (term710 A B x f x').
Proof. exact (MK_COMB (@lem4971467) (@lem4971478 A B x f x')). Qed.
Lemma lem4971480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971481 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term657 A B x f x') = (term711 A B x f x').
Proof. exact (MK_COMB (@lem4971480) (@lem4971479 A B x f x')). Qed.
Lemma lem4971482 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term593 A B x f s x') = (term712 A B x f s x').
Proof. exact (MK_COMB (@lem4971481 A B x f x') (@lem4971466 A s x')). Qed.
Lemma lem4971483 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term599 A B x f s) = (term713 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4971482 A B x f s x')). Qed.
Lemma lem4971484 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4971485 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term600 A B x f s) = (term714 A B x f s).
Proof. exact (MK_COMB (@lem4971484 A) (@lem4971483 A B x f s)). Qed.
Lemma lem4971486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971487 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term602 A B x f s) = (term715 A B x f s).
Proof. exact (MK_COMB (@lem4971486) (@lem4971485 A B x f s)). Qed.
Lemma lem4971488 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term604 A B f s t x) = (term716 A B f s t x).
Proof. exact (MK_COMB (@lem4971487 A B x f s) (@lem4971456 B t x)). Qed.
Lemma lem4971489 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term605 A B f s t) = (term717 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4971488 A B f s t x)). Qed.
Lemma lem4971490 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971491 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term606 A B f s t) = (term718 A B f s t).
Proof. exact (MK_COMB (@lem4971490 B) (@lem4971489 A B f s t)). Qed.
Lemma lem4971492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971493 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term607 A B f s t) = (term719 A B f s t).
Proof. exact (MK_COMB (@lem4971492) (@lem4971491 A B f s t)). Qed.
Lemma lem4971494 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term608 A B f t s) = (term720 A B f t s).
Proof. exact (MK_COMB (@lem4971493 A B f s t) (@lem4971448 A B t s)). Qed.
Lemma lem4971499 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4971500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971501 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4971506 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971506 A B f x). Qed.
Lemma lem4971513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971513 A B f x). Qed.
Lemma lem4971516 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4971514 A B f y). Qed.
Lemma lem4971517 {A B : Type'} (f : A -> B) (x : A) : (term721 A B f x) = (term722 A B f x).
Proof. exact (MK_COMB (@lem4971501 B) (@lem4971508 A B f x)). Qed.
Lemma lem4971518 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem4971517 A B f x) (@lem4971516 A B f y)). Qed.
Lemma lem4971519 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term723 A B x f y) = (term724 A B x f y).
Proof. exact (MK_COMB (@lem4971500) (@lem4971518 A B x f y)). Qed.
Lemma lem4971520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971525 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971526 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971525 A Prop f x). Qed.
Lemma lem4971528 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem4971526 A s y). Qed.
Lemma lem4971529 {A : Type'} (s : A -> Prop) (y : A) : (term617 A s y) = (term708 A s y).
Proof. exact (MK_COMB (@lem4971520) (@lem4971528 A s y)). Qed.
Lemma lem4971530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971531 {A : Type'} (s : A -> Prop) (y : A) : (term580 A s y) = (term725 A s y).
Proof. exact (MK_COMB (@lem4971530) (@lem4971529 A s y)). Qed.
Lemma lem4971532 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term579 A B s x f y) = (term726 A B s x f y).
Proof. exact (MK_COMB (@lem4971531 A s y) (@lem4971519 A B x f y)). Qed.
Lemma lem4971533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971539 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971538 A Prop f x). Qed.
Lemma lem4971541 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4971539 A s x). Qed.
Lemma lem4971542 {A : Type'} (s : A -> Prop) (x : A) : (term617 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem4971533) (@lem4971541 A s x)). Qed.
Lemma lem4971543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971544 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term725 A s x).
Proof. exact (MK_COMB (@lem4971543) (@lem4971542 A s x)). Qed.
Lemma lem4971545 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term582 A B s x f y) = (term727 A B s x f y).
Proof. exact (MK_COMB (@lem4971544 A s x) (@lem4971532 A B s x f y)). Qed.
Lemma lem4971546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971547 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term585 A B s x f y) = (term728 A B s x f y).
Proof. exact (MK_COMB (@lem4971546) (@lem4971545 A B s x f y)). Qed.
Lemma lem4971548 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term587 A B s f x y) = (term729 A B s f x y).
Proof. exact (MK_COMB (@lem4971547 A B s x f y) (@lem4971499 A x y)). Qed.
Lemma lem4971549 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term588 A B s f x) = (term730 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4971548 A B s f x y)). Qed.
Lemma lem4971550 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4971551 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term589 A B s f x) = (term731 A B s f x).
Proof. exact (MK_COMB (@lem4971550 A) (@lem4971549 A B s f x)). Qed.
Lemma lem4971552 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term590 A B s f) = (term732 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4971551 A B s f x)). Qed.
Lemma lem4971553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4971554 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term591 A B s f) = (term733 A B s f).
Proof. exact (MK_COMB (@lem4971553 A) (@lem4971552 A B s f)). Qed.
Lemma lem4971555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971556 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term609 A B s f) = (term734 A B s f).
Proof. exact (MK_COMB (@lem4971555) (@lem4971554 A B s f)). Qed.
Lemma lem4971557 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term610 A B f t s) = (term735 A B f t s).
Proof. exact (MK_COMB (@lem4971556 A B s f) (@lem4971494 A B f t s)). Qed.
Lemma lem4971558 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4971559 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4971568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971569 {A B : Type'} (f : type653 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) f x).
Proof. exact (@lem4971568 (A -> Prop) (type832 A B) f x). Qed.
Lemma lem4971570 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) : (_62510 s) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510 s).
Proof. exact (@lem4971569 A B _62510 s). Qed.
Lemma lem4971571 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4971572 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (_62510 s P) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510 s P).
Proof. exact (MK_COMB (@lem4971570 A B _62510 s) (@lem4971571 B P)). Qed.
Lemma lem4971574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971575 {A B : Type'} (f : type832 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B) -> A -> Prop) f x).
Proof. exact (@lem4971574 (B -> Prop) (type551 A B) f x). Qed.
Lemma lem4971576 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510 s P) = (term736 A B _62510 s P).
Proof. exact (@lem4971575 A B (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62510 s) P). Qed.
Lemma lem4971577 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (_62510 s P) = (term736 A B _62510 s P).
Proof. exact (TRANS (@lem4971572 A B _62510 s P) (@lem4971576 A B _62510 s P)). Qed.
Lemma lem4971578 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4971579 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (_62510 s P f) = (term737 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4971577 A B _62510 s P) (@lem4971578 A B f)). Qed.
Lemma lem4971581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971582 {A B : Type'} (f : type551 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> Prop) f x).
Proof. exact (@lem4971581 (A -> B) (A -> Prop) f x). Qed.
Lemma lem4971583 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term737 A B _62510 s P f) = (term738 A B _62510 s P f).
Proof. exact (@lem4971582 A B (term736 A B _62510 s P) f). Qed.
Lemma lem4971585 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (_62510 s P f) = (term738 A B _62510 s P f).
Proof. exact (TRANS (@lem4971579 A B _62510 s P f) (@lem4971583 A B _62510 s P f)). Qed.
Lemma lem4971586 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term235 A B _62510 s P f) = (term739 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4971559 A) (@lem4971585 A B _62510 s P f)). Qed.
Lemma lem4971588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971589 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4971588 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4971590 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term739 A B _62510 s P f) = (term740 A B _62510 s P f).
Proof. exact (@lem4971589 A (@GSPEC A) (term738 A B _62510 s P f)). Qed.
Lemma lem4971591 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term235 A B _62510 s P f) = (term740 A B _62510 s P f).
Proof. exact (TRANS (@lem4971586 A B _62510 s P f) (@lem4971590 A B _62510 s P f)). Qed.
Lemma lem4971592 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4971593 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term236 A B _62510 s P f) = (term741 A B _62510 s P f).
Proof. exact (MK_COMB (@lem4971558 A) (@lem4971591 A B _62510 s P f)). Qed.
Lemma lem4971594 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term237 A B _62510 s P f n) = (term742 A B _62510 s P f n).
Proof. exact (MK_COMB (@lem4971593 A B _62510 s P f) (@lem4971592 n)). Qed.
Lemma lem4971596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971597 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem4971596 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem4971598 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term741 A B _62510 s P f) = (term743 A B _62510 s P f).
Proof. exact (@lem4971597 A (@HAS_SIZE A) (term740 A B _62510 s P f)). Qed.
Lemma lem4971599 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4971600 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term742 A B _62510 s P f n) = (term744 A B _62510 s P f n).
Proof. exact (MK_COMB (@lem4971598 A B _62510 s P f) (@lem4971599 n)). Qed.
Lemma lem4971602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971603 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem4971602 nat Prop f x). Qed.
Lemma lem4971604 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term744 A B _62510 s P f n) = (term745 A B _62510 s P f n).
Proof. exact (@lem4971603 (term743 A B _62510 s P f) n). Qed.
Lemma lem4971605 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term742 A B _62510 s P f n) = (term745 A B _62510 s P f n).
Proof. exact (TRANS (@lem4971600 A B _62510 s P f n) (@lem4971604 A B _62510 s P f n)). Qed.
Lemma lem4971606 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term237 A B _62510 s P f n) = (term745 A B _62510 s P f n).
Proof. exact (TRANS (@lem4971594 A B _62510 s P f n) (@lem4971605 A B _62510 s P f n)). Qed.
Lemma lem4971607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971608 {A B : Type'} (_62510 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62510 s P f n) = (term746 A B _62510 s P f n).
Proof. exact (MK_COMB (@lem4971607) (@lem4971606 A B _62510 s P f n)). Qed.
Lemma lem4971609 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term611 A B _62510 P n f t s) = (term747 A B _62510 P n f t s).
Proof. exact (MK_COMB (@lem4971608 A B _62510 s P f n) (@lem4971557 A B f t s)). Qed.
Lemma lem4971610 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term747 A B _62510 P n f t s.
Proof. exact (EQ_MP (@lem4971609 A B _62510 P n f t s) (@lem4971052 A B _62510 P n f t s h1)). Qed.
Lemma lem4971611 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4971616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971616 A B f x). Qed.
Lemma lem4971619 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem4971617 A B f x'). Qed.
Lemma lem4971620 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term88 A B P f x') = (term748 A B P f x').
Proof. exact (MK_COMB (@lem4971611 B P) (@lem4971619 A B f x')). Qed.
Lemma lem4971622 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971623 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971622 B Prop f x). Qed.
Lemma lem4971624 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term748 A B P f x') = (term749 A B P f x').
Proof. exact (@lem4971623 B P (@I (A -> B) f x')). Qed.
Lemma lem4971625 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term88 A B P f x') = (term749 A B P f x').
Proof. exact (TRANS (@lem4971620 A B P f x') (@lem4971624 A B P f x')). Qed.
Lemma lem4971630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971631 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971630 A Prop f x). Qed.
Lemma lem4971633 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem4971631 A s x'). Qed.
Lemma lem4971634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971635 {A : Type'} (s : A -> Prop) (x' : A) : (term87 A s x') = (term750 A s x').
Proof. exact (MK_COMB (@lem4971634) (@lem4971633 A s x')). Qed.
Lemma lem4971636 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term90 A B s P f x') = (term751 A B s P f x').
Proof. exact (MK_COMB (@lem4971635 A s x') (@lem4971625 A B P f x')). Qed.
Lemma lem4971643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971643 A B f x). Qed.
Lemma lem4971646 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem4971644 A B f x'). Qed.
Lemma lem4971647 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4971648 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem4971647 B x) (@lem4971646 A B f x')). Qed.
Lemma lem4971649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971650 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term121 A B x f x') = (term752 A B x f x').
Proof. exact (MK_COMB (@lem4971649) (@lem4971648 A B x f x')). Qed.
Lemma lem4971651 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term189 A B x s P f x') = (term753 A B x s P f x').
Proof. exact (MK_COMB (@lem4971650 A B x f x') (@lem4971636 A B s P f x')). Qed.
Lemma lem4971652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971657 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971658 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971657 B Prop f x). Qed.
Lemma lem4971660 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (@I (B -> Prop) P x).
Proof. exact (@lem4971658 B P x). Qed.
Lemma lem4971661 {B : Type'} (P : B -> Prop) (x : B) : (term617 B P x) = (term708 B P x).
Proof. exact (MK_COMB (@lem4971652) (@lem4971660 B P x)). Qed.
Lemma lem4971662 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971667 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971668 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971667 B Prop f x). Qed.
Lemma lem4971670 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4971668 B t x). Qed.
Lemma lem4971671 {B : Type'} (t : B -> Prop) (x : B) : (term617 B t x) = (term708 B t x).
Proof. exact (MK_COMB (@lem4971662) (@lem4971670 B t x)). Qed.
Lemma lem4971672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971673 {B : Type'} (t : B -> Prop) (x : B) : (term580 B t x) = (term725 B t x).
Proof. exact (MK_COMB (@lem4971672) (@lem4971671 B t x)). Qed.
Lemma lem4971674 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term654 B t P x) = (term754 B t P x).
Proof. exact (MK_COMB (@lem4971673 B t x) (@lem4971661 B P x)). Qed.
Lemma lem4971675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971676 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term669 B t P x) = (term755 B t P x).
Proof. exact (MK_COMB (@lem4971675) (@lem4971674 B t P x)). Qed.
Lemma lem4971677 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term686 A B t x s P f x') = (term756 A B t x s P f x').
Proof. exact (MK_COMB (@lem4971676 B t P x) (@lem4971651 A B x s P f x')). Qed.
Lemma lem4971678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971679 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4971684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971684 A B f x). Qed.
Lemma lem4971687 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term748 A B P f x).
Proof. exact (MK_COMB (@lem4971679 B P) (@lem4971686 A B f x)). Qed.
Lemma lem4971689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971690 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971689 B Prop f x). Qed.
Lemma lem4971691 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term748 A B P f x) = (term749 A B P f x).
Proof. exact (@lem4971690 B P (@I (A -> B) f x)). Qed.
Lemma lem4971692 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term749 A B P f x).
Proof. exact (TRANS (@lem4971687 A B P f x) (@lem4971691 A B P f x)). Qed.
Lemma lem4971693 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term757 A B P f x) = (term758 A B P f x).
Proof. exact (MK_COMB (@lem4971678) (@lem4971692 A B P f x)). Qed.
Lemma lem4971694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971700 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971699 A Prop f x). Qed.
Lemma lem4971702 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4971700 A s x). Qed.
Lemma lem4971703 {A : Type'} (s : A -> Prop) (x : A) : (term617 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem4971694) (@lem4971702 A s x)). Qed.
Lemma lem4971704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971705 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term725 A s x).
Proof. exact (MK_COMB (@lem4971704) (@lem4971703 A s x)). Qed.
Lemma lem4971706 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term656 A B s P f x) = (term759 A B s P f x).
Proof. exact (MK_COMB (@lem4971705 A s x) (@lem4971693 A B P f x)). Qed.
Lemma lem4971707 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971714 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971714 A B f x). Qed.
Lemma lem4971717 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4971718 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem4971717 B x) (@lem4971716 A B f x')). Qed.
Lemma lem4971719 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term709 A B x f x') = (term710 A B x f x').
Proof. exact (MK_COMB (@lem4971707) (@lem4971718 A B x f x')). Qed.
Lemma lem4971720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971721 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term657 A B x f x') = (term711 A B x f x').
Proof. exact (MK_COMB (@lem4971720) (@lem4971719 A B x f x')). Qed.
Lemma lem4971722 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term659 A B x s P f x') = (term760 A B x s P f x').
Proof. exact (MK_COMB (@lem4971721 A B x f x') (@lem4971706 A B s P f x')). Qed.
Lemma lem4971723 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term666 A B x s P f) = (term761 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4971722 A B x s P f x')). Qed.
Lemma lem4971724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4971725 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term667 A B x s P f) = (term762 A B x s P f).
Proof. exact (MK_COMB (@lem4971724 A) (@lem4971723 A B x s P f)). Qed.
Lemma lem4971730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971731 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971730 B Prop f x). Qed.
Lemma lem4971733 {B : Type'} (P : B -> Prop) (x : B) : (P x) = (@I (B -> Prop) P x).
Proof. exact (@lem4971731 B P x). Qed.
Lemma lem4971738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971739 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971738 B Prop f x). Qed.
Lemma lem4971741 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4971739 B t x). Qed.
Lemma lem4971742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971743 {B : Type'} (t : B -> Prop) (x : B) : (term87 B t x) = (term750 B t x).
Proof. exact (MK_COMB (@lem4971742) (@lem4971741 B t x)). Qed.
Lemma lem4971744 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term172 B t P x) = (term763 B t P x).
Proof. exact (MK_COMB (@lem4971743 B t x) (@lem4971733 B P x)). Qed.
Lemma lem4971745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971746 {B : Type'} (t : B -> Prop) (P : B -> Prop) (x : B) : (term672 B t P x) = (term764 B t P x).
Proof. exact (MK_COMB (@lem4971745) (@lem4971744 B t P x)). Qed.
Lemma lem4971747 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term674 A B t x s P f) = (term765 A B t x s P f).
Proof. exact (MK_COMB (@lem4971746 B t P x) (@lem4971725 A B x s P f)). Qed.
Lemma lem4971748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971749 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term676 A B t x s P f) = (term766 A B t x s P f).
Proof. exact (MK_COMB (@lem4971748) (@lem4971747 A B t x s P f)). Qed.
Lemma lem4971750 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term699 A B t x s P f x') = (term767 A B t x s P f x').
Proof. exact (MK_COMB (@lem4971749 A B t x s P f) (@lem4971677 A B t x s P f x')). Qed.
Lemma lem4971751 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term699 A B t x s P f x') : term767 A B t x s P f x'.
Proof. exact (EQ_MP (@lem4971750 A B t x s P f x') (@lem4971405 A B t x s P f x' h1)). Qed.
Lemma lem4971752 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4971753 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4971758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971759 {A B : Type'} (f : B -> A) (x : B) : (f x) = (@I (B -> A) f x).
Proof. exact (@lem4971758 B A f x). Qed.
Lemma lem4971761 {A B : Type'} (x'' : B -> A) (y : B) : (x'' y) = (@I (B -> A) x'' y).
Proof. exact (@lem4971759 A B x'' y). Qed.
Lemma lem4971762 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : (term768 A B f x'' y) = (term769 A B f x'' y).
Proof. exact (MK_COMB (@lem4971753 A B f) (@lem4971761 A B x'' y)). Qed.
Lemma lem4971764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4971764 A B f x). Qed.
Lemma lem4971766 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : (term769 A B f x'' y) = (term770 A B f x'' y).
Proof. exact (@lem4971765 A B f (@I (B -> A) x'' y)). Qed.
Lemma lem4971767 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : (term768 A B f x'' y) = (term770 A B f x'' y).
Proof. exact (TRANS (@lem4971762 A B f x'' y) (@lem4971766 A B f x'' y)). Qed.
Lemma lem4971768 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4971769 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : (term771 A B f x'' y) = (term772 A B f x'' y).
Proof. exact (MK_COMB (@lem4971752 B) (@lem4971767 A B f x'' y)). Qed.
Lemma lem4971770 {A B : Type'} (f : A -> B) (x'' : B -> A) (y : B) : ((term768 A B f x'' y) = y) = ((term770 A B f x'' y) = y).
Proof. exact (MK_COMB (@lem4971769 A B f x'' y) (@lem4971768 B y)). Qed.
Lemma lem4971771 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4971776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971777 {A B : Type'} (f : B -> A) (x : B) : (f x) = (@I (B -> A) f x).
Proof. exact (@lem4971776 B A f x). Qed.
Lemma lem4971779 {A B : Type'} (x'' : B -> A) (y : B) : (x'' y) = (@I (B -> A) x'' y).
Proof. exact (@lem4971777 A B x'' y). Qed.
Lemma lem4971780 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (y : B) : (term773 A B s x'' y) = (term774 A B s x'' y).
Proof. exact (MK_COMB (@lem4971771 A s) (@lem4971779 A B x'' y)). Qed.
Lemma lem4971782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971783 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4971782 A Prop f x). Qed.
Lemma lem4971784 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (y : B) : (term774 A B s x'' y) = (term775 A B s x'' y).
Proof. exact (@lem4971783 A s (@I (B -> A) x'' y)). Qed.
Lemma lem4971785 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (y : B) : (term773 A B s x'' y) = (term775 A B s x'' y).
Proof. exact (TRANS (@lem4971780 A B s x'' y) (@lem4971784 A B s x'' y)). Qed.
Lemma lem4971786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4971787 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (y : B) : (term776 A B s x'' y) = (term777 A B s x'' y).
Proof. exact (MK_COMB (@lem4971786) (@lem4971785 A B s x'' y)). Qed.
Lemma lem4971788 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term778 A B s f x'' y) = (term779 A B s f x'' y).
Proof. exact (MK_COMB (@lem4971787 A B s x'' y) (@lem4971770 A B f x'' y)). Qed.
Lemma lem4971789 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4971794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4971795 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4971794 B Prop f x). Qed.
Lemma lem4971797 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem4971795 B t y). Qed.
Lemma lem4971798 {B : Type'} (t : B -> Prop) (y : B) : (term617 B t y) = (term708 B t y).
Proof. exact (MK_COMB (@lem4971789) (@lem4971797 B t y)). Qed.
Lemma lem4971799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4971800 {B : Type'} (t : B -> Prop) (y : B) : (term580 B t y) = (term725 B t y).
Proof. exact (MK_COMB (@lem4971799) (@lem4971798 B t y)). Qed.
Lemma lem4971801 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term645 A B t s f x'' y) = (term780 A B t s f x'' y).
Proof. exact (MK_COMB (@lem4971800 B t y) (@lem4971788 A B s f x'' y)). Qed.
Lemma lem4971802 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) : (term647 A B t s f x'') = (term781 A B t s f x'').
Proof. exact (fun_ext (fun y : B => @lem4971801 A B t s f x'' y)). Qed.
Lemma lem4971803 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4971804 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) : (term649 A B t s f x'') = (term782 A B t s f x'').
Proof. exact (MK_COMB (@lem4971803 B) (@lem4971802 A B t s f x'')). Qed.
Lemma lem4971805 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term782 A B t s f x''.
Proof. exact (EQ_MP (@lem4971804 A B t s f x'') (@lem4971406 A B t s f x'' h1)). Qed.
Lemma lem4972122 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term735 A B f t s.
Proof. exact (proj2 (@lem4971610 A B _62510 P n f t s h1)). Qed.
Lemma lem4972124 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term720 A B f t s.
Proof. exact (proj2 (@lem4972122 A B _62510 P n f t s h1)). Qed.
Lemma lem4972127 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term718 A B f s t.
Proof. exact (proj1 (@lem4972124 A B _62510 P n f t s h1)). Qed.
Lemma lem4972132 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term765 A B t x s P f.
Proof. exact (h1). Qed.
Lemma lem4972133 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term756 A B t x s P f x'.
Proof. exact (h1). Qed.
Lemma lem4972134 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term762 A B x s P f.
Proof. exact (proj2 (@lem4972132 A B t x s P f h1)). Qed.
Lemma lem4972135 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term763 B t P x.
Proof. exact (proj1 (@lem4972132 A B t x s P f h1)). Qed.
Lemma lem4972138 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term753 A B x s P f x'.
Proof. exact (proj2 (@lem4972133 A B t x s P f x' h1)). Qed.
Lemma lem4972139 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term754 B t P x.
Proof. exact (proj1 (@lem4972133 A B t x s P f x' h1)). Qed.
Lemma lem4972140 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term751 A B s P f x'.
Proof. exact (proj2 (@lem4972138 A B t x s P f x' h1)). Qed.
Lemma lem4972163 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) (y : B) : (term780 A B t s f x'' y) = (term783 A B s t f x'' y).
Proof. exact (@lem19490 (term775 A B s x'' y) (term708 B t y) ((term770 A B f x'' y) = y)). Qed.
Lemma lem4972164 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) : (term781 A B t s f x'') = (term784 A B s t f x'').
Proof. exact (fun_ext (fun y : B => @lem4972163 A B s t f x'' y)). Qed.
Lemma lem4972165 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4972167 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) : (term782 A B t s f x'') = (term785 A B s t f x'').
Proof. exact (MK_COMB (@lem4972165 B) (@lem4972164 A B s t f x'')). Qed.
Lemma lem4972168 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term785 A B s t f x''.
Proof. exact (EQ_MP (@lem4972167 A B s t f x'') (@lem4971805 A B t s f x'' h1)). Qed.
Lemma lem4972352 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term760 A B x s P f x') = (term760 A B x s P f x').
Proof. exact (eq_refl (term760 A B x s P f x')). Qed.
Lemma lem4972353 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term761 A B x s P f) = (term761 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem4972352 A B x s P f x')). Qed.
Lemma lem4972354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4972356 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term762 A B x s P f) = (term762 A B x s P f).
Proof. exact (MK_COMB (@lem4972354 A) (@lem4972353 A B x s P f)). Qed.
Lemma lem4972357 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term762 A B x s P f.
Proof. exact (EQ_MP (@lem4972356 A B x s P f) (@lem4972134 A B t x s P f h1)). Qed.
Lemma lem4972500 {A : Type'} (P : A -> Prop) (Q : Prop) : (term786 A P Q) = (term787 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4972501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term786 A P Q) = (term787 A P Q).
Proof. exact (@lem4972500 A P Q). Qed.
Lemma lem4972502 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term788 A B f s t x) = (term789 A B f s t x).
Proof. exact (@lem4972501 A (term713 A B x f s) (@I (B -> Prop) t x)). Qed.
Lemma lem4972503 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term790 A B x f s x') = (term712 A B x f s x').
Proof. exact (eq_refl (term790 A B x f s x')). Qed.
Lemma lem4972504 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term791 A B x f s) = (term713 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4972503 A B x f s x')). Qed.
Lemma lem4972505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4972506 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term792 A B x f s) = (term714 A B x f s).
Proof. exact (MK_COMB (@lem4972505 A) (@lem4972504 A B x f s)). Qed.
Lemma lem4972507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4972508 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term793 A B x f s) = (term715 A B x f s).
Proof. exact (MK_COMB (@lem4972507) (@lem4972506 A B x f s)). Qed.
Lemma lem4972509 {B : Type'} (t : B -> Prop) (x : B) : (@I (B -> Prop) t x) = (@I (B -> Prop) t x).
Proof. exact (eq_refl (@I (B -> Prop) t x)). Qed.
Lemma lem4972510 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term788 A B f s t x) = (term716 A B f s t x).
Proof. exact (MK_COMB (@lem4972508 A B x f s) (@lem4972509 B t x)). Qed.
Lemma lem4972511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4972512 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term794 A B f s t x) = (term795 A B f s t x).
Proof. exact (MK_COMB (@lem4972511) (@lem4972510 A B f s t x)). Qed.
Lemma lem4972513 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term790 A B x f s x') = (term712 A B x f s x').
Proof. exact (eq_refl (term790 A B x f s x')). Qed.
Lemma lem4972514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4972515 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term796 A B x f s x') = (term797 A B x f s x').
Proof. exact (MK_COMB (@lem4972514) (@lem4972513 A B x f s x')). Qed.
Lemma lem4972516 {B : Type'} (t : B -> Prop) (x : B) : (@I (B -> Prop) t x) = (@I (B -> Prop) t x).
Proof. exact (eq_refl (@I (B -> Prop) t x)). Qed.
Lemma lem4972517 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term798 A B f s x t x') = (term799 A B f s x t x').
Proof. exact (MK_COMB (@lem4972515 A B x' f s x) (@lem4972516 B t x')). Qed.
Lemma lem4972518 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term800 A B f s t x) = (term801 A B f s t x).
Proof. exact (fun_ext (fun x' : A => @lem4972517 A B f s x' t x)). Qed.
Lemma lem4972519 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4972520 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term789 A B f s t x) = (term802 A B f s t x).
Proof. exact (MK_COMB (@lem4972519 A) (@lem4972518 A B f s t x)). Qed.
Lemma lem4972521 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : ((term788 A B f s t x) = (term789 A B f s t x)) = ((term716 A B f s t x) = (term802 A B f s t x)).
Proof. exact (MK_COMB (@lem4972512 A B f s t x) (@lem4972520 A B f s t x)). Qed.
Lemma lem4972522 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term716 A B f s t x) = (term802 A B f s t x).
Proof. exact (EQ_MP (@lem4972521 A B f s t x) (@lem4972502 A B f s t x)). Qed.
Lemma lem4972523 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term717 A B f s t) = (term803 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4972522 A B f s t x)). Qed.
Lemma lem4972524 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4972525 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term718 A B f s t) = (term804 A B f s t).
Proof. exact (MK_COMB (@lem4972524 B) (@lem4972523 A B f s t)). Qed.
Lemma lem4972538 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term799 A B f s x t x') = (term799 A B f s x t x').
Proof. exact (eq_refl (term799 A B f s x t x')). Qed.
Lemma lem4972539 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term801 A B f s t x) = (term801 A B f s t x).
Proof. exact (fun_ext (fun x' : A => @lem4972538 A B f s x' t x)). Qed.
Lemma lem4972540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4972541 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term802 A B f s t x) = (term802 A B f s t x).
Proof. exact (MK_COMB (@lem4972540 A) (@lem4972539 A B f s t x)). Qed.
Lemma lem4972542 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term803 A B f s t) = (term803 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4972541 A B f s t x)). Qed.
Lemma lem4972543 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4972544 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term804 A B f s t) = (term804 A B f s t).
Proof. exact (MK_COMB (@lem4972543 B) (@lem4972542 A B f s t)). Qed.
Lemma lem4972545 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term718 A B f s t) = (term804 A B f s t).
Proof. exact (TRANS (@lem4972525 A B f s t) (@lem4972544 A B f s t)). Qed.
Lemma lem4972546 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term804 A B f s t.
Proof. exact (EQ_MP (@lem4972545 A B f s t) (@lem4972127 A B _62510 P n f t s h1)). Qed.
Lemma lem4972574 {B : Type'} (t : B -> Prop) (x : B) (h1 : term708 B t x) : term708 B t x.
Proof. exact (h1). Qed.
Lemma lem4972783 {B : Type'} (P : B -> Prop) (x : B) (h1 : term708 B P x) : term708 B P x.
Proof. exact (h1). Qed.
Lemma lem4972784 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term805 A B s t f x'' _62511.
Proof. exact (@lem4972168 A B t s f x'' h1 _62511). Qed.
Lemma lem4972785 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_62511 : B) : (term805 A B s t f x'' _62511) = (term783 A B s t f x'' _62511).
Proof. exact (eq_refl (term805 A B s t f x'' _62511)). Qed.
Lemma lem4972786 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term783 A B s t f x'' _62511.
Proof. exact (EQ_MP (@lem4972785 A B s t f x'' _62511) (@lem4972784 A B _62511 t s f x'' h1)). Qed.
Lemma lem4972826 {A B : Type'} (_62525 : A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term806 A B x s P f _62525.
Proof. exact (@lem4972357 A B t x s P f h1 _62525). Qed.
Lemma lem4972827 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term806 A B x s P f _62525) = (term760 A B x s P f _62525).
Proof. exact (eq_refl (term806 A B x s P f _62525)). Qed.
Lemma lem4972865 {A B : Type'} (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term807 A B f s t _62538.
Proof. exact (@lem4972546 A B _62510 P n f t s h1 _62538). Qed.
Lemma lem4972866 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (_62538 : B) : (term807 A B f s t _62538) = (term802 A B f s t _62538).
Proof. exact (eq_refl (term807 A B f s t _62538)). Qed.
Lemma lem4972867 {A B : Type'} (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term802 A B f s t _62538.
Proof. exact (EQ_MP (@lem4972866 A B f s t _62538) (@lem4972865 A B _62538 _62510 P n f t s h1)). Qed.
Lemma lem4972868 {A B : Type'} (_62538 : B) (_62539 : A) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term808 A B f s t _62538 _62539.
Proof. exact (@lem4972867 A B _62538 _62510 P n f t s h1 _62539). Qed.
Lemma lem4972869 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62539 : A) (t : B -> Prop) (_62538 : B) : (term808 A B f s t _62538 _62539) = (term799 A B f s _62539 t _62538).
Proof. exact (eq_refl (term808 A B f s t _62538 _62539)). Qed.
Lemma lem4972870 {A B : Type'} (_62539 : A) (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term799 A B f s _62539 t _62538.
Proof. exact (EQ_MP (@lem4972869 A B f s _62539 t _62538) (@lem4972868 A B _62538 _62539 _62510 P n f t s h1)). Qed.
Lemma lem4972978 {A B : Type'} (_62525 : A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term760 A B x s P f _62525.
Proof. exact (EQ_MP (@lem4972827 A B x s P f _62525) (@lem4972826 A B _62525 t x s P f h1)). Qed.
Lemma lem4972988 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term809 A B t s x'' _62511.
Proof. exact (proj1 (@lem4972786 A B _62511 t s f x'' h1)). Qed.
Lemma lem4972994 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term810 A B t f x'' _62511.
Proof. exact (proj2 (@lem4972786 A B _62511 t s f x'' h1)). Qed.
Lemma lem4973037 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62539 : A) (t : B -> Prop) (_62538 : B) : (term799 A B f s _62539 t _62538) = (term811 A B f s _62539 t _62538).
Proof. exact (@lem4968669 (term710 A B _62538 f _62539) (term708 A s _62539) (@I (B -> Prop) t _62538)). Qed.
Lemma lem4973046 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : x = (@I (A -> B) f x').
Proof. exact (proj1 (@lem4972138 A B t x s P f x' h1)). Qed.
Lemma lem4973052 {B : Type'} (t : B -> Prop) (x : B) (h1 : term708 B t x) : term708 B t x.
Proof. exact (h1). Qed.
Lemma lem4973116 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : x = (@I (A -> B) f x').
Proof. exact (proj1 (@lem4972138 A B t x s P f x' h1)). Qed.
Lemma lem4973122 {B : Type'} (P : B -> Prop) (x : B) (h1 : term708 B P x) : term708 B P x.
Proof. exact (h1). Qed.
Lemma lem4973218 {A B : Type'} (_62539 : A) (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term811 A B f s _62539 t _62538.
Proof. exact (EQ_MP (@lem4973037 A B f s _62539 t _62538) (@lem4972870 A B _62539 _62538 _62510 P n f t s h1)). Qed.
Lemma lem4973289 {B : Type'} (t : B -> Prop) : (term812 B t) = (term812 B t).
Proof. exact (eq_refl (term812 B t)). Qed.
Lemma lem4973290 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : (term813 B t x) = (term814 A B t f x').
Proof. exact (MK_COMB (@lem4973289 B t) (@lem4973046 A B t x s P f x' h1)). Qed.
Lemma lem4973291 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term814 A B t f x') = (term758 A B t f x').
Proof. exact (eq_refl (term814 A B t f x')). Qed.
Lemma lem4973292 {B : Type'} (t : B -> Prop) (x : B) : (term815 B t x) = (term815 B t x).
Proof. exact (eq_refl (term815 B t x)). Qed.
Lemma lem4973293 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term813 B t x) = (term814 A B t f x')) = ((term813 B t x) = (term758 A B t f x')).
Proof. exact (MK_COMB (@lem4973292 B t x) (@lem4973291 A B t f x')). Qed.
Lemma lem4973294 {B : Type'} (t : B -> Prop) (x : B) : (term813 B t x) = (term708 B t x).
Proof. exact (eq_refl (term813 B t x)). Qed.
Lemma lem4973295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4973296 {B : Type'} (t : B -> Prop) (x : B) : (term815 B t x) = (term816 B t x).
Proof. exact (MK_COMB (@lem4973295) (@lem4973294 B t x)). Qed.
Lemma lem4973297 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term758 A B t f x') = (term758 A B t f x').
Proof. exact (eq_refl (term758 A B t f x')). Qed.
Lemma lem4973298 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term813 B t x) = (term758 A B t f x')) = ((term708 B t x) = (term758 A B t f x')).
Proof. exact (MK_COMB (@lem4973296 B t x) (@lem4973297 A B t f x')). Qed.
Lemma lem4973299 {A B : Type'} (x : B) (t : B -> Prop) (f : A -> B) (x' : A) : ((term813 B t x) = (term814 A B t f x')) = ((term708 B t x) = (term758 A B t f x')).
Proof. exact (TRANS (@lem4973293 A B x t f x') (@lem4973298 A B x t f x')). Qed.
Lemma lem4973300 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : (term708 B t x) = (term758 A B t f x').
Proof. exact (EQ_MP (@lem4973299 A B x t f x') (@lem4973290 A B t x s P f x' h1)). Qed.
Lemma lem4973301 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term756 A B t x s P f x') : term758 A B t f x'.
Proof. exact (EQ_MP (@lem4973300 A B t x s P f x' h2) (@lem4973052 B t x h1)). Qed.
Lemma lem4973484 {B : Type'} (P : B -> Prop) : (term812 B P) = (term812 B P).
Proof. exact (eq_refl (term812 B P)). Qed.
Lemma lem4973485 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : (term813 B P x) = (term814 A B P f x').
Proof. exact (MK_COMB (@lem4973484 B P) (@lem4973116 A B t x s P f x' h1)). Qed.
Lemma lem4973486 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term814 A B P f x') = (term758 A B P f x').
Proof. exact (eq_refl (term814 A B P f x')). Qed.
Lemma lem4973487 {B : Type'} (P : B -> Prop) (x : B) : (term815 B P x) = (term815 B P x).
Proof. exact (eq_refl (term815 B P x)). Qed.
Lemma lem4973488 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term813 B P x) = (term814 A B P f x')) = ((term813 B P x) = (term758 A B P f x')).
Proof. exact (MK_COMB (@lem4973487 B P x) (@lem4973486 A B P f x')). Qed.
Lemma lem4973489 {B : Type'} (P : B -> Prop) (x : B) : (term813 B P x) = (term708 B P x).
Proof. exact (eq_refl (term813 B P x)). Qed.
Lemma lem4973490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4973491 {B : Type'} (P : B -> Prop) (x : B) : (term815 B P x) = (term816 B P x).
Proof. exact (MK_COMB (@lem4973490) (@lem4973489 B P x)). Qed.
Lemma lem4973492 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term758 A B P f x') = (term758 A B P f x').
Proof. exact (eq_refl (term758 A B P f x')). Qed.
Lemma lem4973493 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term813 B P x) = (term758 A B P f x')) = ((term708 B P x) = (term758 A B P f x')).
Proof. exact (MK_COMB (@lem4973491 B P x) (@lem4973492 A B P f x')). Qed.
Lemma lem4973494 {A B : Type'} (x : B) (P : B -> Prop) (f : A -> B) (x' : A) : ((term813 B P x) = (term814 A B P f x')) = ((term708 B P x) = (term758 A B P f x')).
Proof. exact (TRANS (@lem4973488 A B x P f x') (@lem4973493 A B x P f x')). Qed.
Lemma lem4973495 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : (term708 B P x) = (term758 A B P f x').
Proof. exact (EQ_MP (@lem4973494 A B x P f x') (@lem4973485 A B t x s P f x' h1)). Qed.
Lemma lem4973496 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : term758 A B P f x'.
Proof. exact (EQ_MP (@lem4973495 A B t x s P f x' h2) (@lem4973122 B P x h1)). Qed.
Lemma lem4973563 {B : Type'} : (@I (B -> Prop)) = (@I (B -> Prop)).
Proof. exact (eq_refl (@I (B -> Prop))). Qed.
Lemma lem4973564 {B : Type'} (_62618 : B -> Prop) (_62620 : B -> Prop) (h1 : _62618 = _62620) : _62618 = _62620.
Proof. exact (h1). Qed.
Lemma lem4973565 {B : Type'} (_62619 : B) (_62621 : B) (h1 : _62619 = _62621) : _62619 = _62621.
Proof. exact (h1). Qed.
Lemma lem4973566 {B : Type'} (_62618 : B -> Prop) (_62620 : B -> Prop) (h1 : _62618 = _62620) : (@I (B -> Prop) _62618) = (@I (B -> Prop) _62620).
Proof. exact (MK_COMB (@lem4973563 B) (@lem4973564 B _62618 _62620 h1)). Qed.
Lemma lem4973567 {B : Type'} (_62619 : B) (_62621 : B) (_62618 : B -> Prop) (_62620 : B -> Prop) (h1 : _62619 = _62621) (h2 : _62618 = _62620) : (@I (B -> Prop) _62618 _62619) = (@I (B -> Prop) _62620 _62621).
Proof. exact (MK_COMB (@lem4973566 B _62618 _62620 h2) (@lem4973565 B _62619 _62621 h1)). Qed.
Lemma lem4973569 (b : Prop) (a : Prop) : term817 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4973570 {B : Type'} (_62620 : B -> Prop) (_62621 : B) (_62618 : B -> Prop) (_62619 : B) : term818 B _62620 _62621 _62618 _62619.
Proof. exact (@lem4973569 (@I (B -> Prop) _62620 _62621) (@I (B -> Prop) _62618 _62619)). Qed.
Lemma lem4973571 {B : Type'} (_62619 : B) (_62621 : B) (_62618 : B -> Prop) (_62620 : B -> Prop) (h1 : _62619 = _62621) (h2 : _62618 = _62620) : term819 B _62620 _62621 _62618 _62619.
Proof. exact (@lem4973570 B _62620 _62621 _62618 _62619 (@lem4973567 B _62619 _62621 _62618 _62620 h1 h2)). Qed.
Lemma lem4973572 {B : Type'} (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) (_62621 : B) (h1 : _62619 = _62621) : term820 B _62620 _62621 _62618 _62619.
Proof. exact (fun h0 : _62618 = _62620 => @lem4973571 B _62619 _62621 _62618 _62620 h1 h0). Qed.
Lemma lem4973574 (a : Prop) (b : Prop) : (a -> b) = (term821 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4973575 {B : Type'} (_62620 : B -> Prop) (_62621 : B) (_62618 : B -> Prop) (_62619 : B) : (term820 B _62620 _62621 _62618 _62619) = (term822 B _62620 _62621 _62618 _62619).
Proof. exact (@lem4973574 (_62618 = _62620) (term819 B _62620 _62621 _62618 _62619)). Qed.
Lemma lem4973576 {B : Type'} (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) (_62621 : B) (h1 : _62619 = _62621) : term822 B _62620 _62621 _62618 _62619.
Proof. exact (EQ_MP (@lem4973575 B _62620 _62621 _62618 _62619) (@lem4973572 B _62620 _62618 _62619 _62621 h1)). Qed.
Lemma lem4973577 {B : Type'} (_62620 : B -> Prop) (_62621 : B) (_62618 : B -> Prop) (_62619 : B) : term823 B _62620 _62621 _62618 _62619.
Proof. exact (fun h0 : _62619 = _62621 => @lem4973576 B _62620 _62618 _62619 _62621 h0). Qed.
Lemma lem4973579 (a : Prop) (b : Prop) : (a -> b) = (term821 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4973580 {B : Type'} (_62620 : B -> Prop) (_62621 : B) (_62618 : B -> Prop) (_62619 : B) : (term823 B _62620 _62621 _62618 _62619) = (term824 B _62620 _62621 _62618 _62619).
Proof. exact (@lem4973579 (_62619 = _62621) (term822 B _62620 _62621 _62618 _62619)). Qed.
Lemma lem4973581 {B : Type'} (_62620 : B -> Prop) (_62621 : B) (_62618 : B -> Prop) (_62619 : B) : term824 B _62620 _62621 _62618 _62619.
Proof. exact (EQ_MP (@lem4973580 B _62620 _62621 _62618 _62619) (@lem4973577 B _62620 _62621 _62618 _62619)). Qed.
Lemma lem4973897 {B : Type'} (x : B) (y : B) (z : B) : term825 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4973937 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem4972135 A B t x s P f h1)). Qed.
Lemma lem4973938 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term826 B t x.
Proof. exact (fun h0 : term708 B t x => @lem4973937 A B t x s P f h1). Qed.
Lemma lem4973940 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4973941 {B : Type'} (t : B -> Prop) (x : B) : (term826 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4973940 (@I (B -> Prop) t x)). Qed.
Lemma lem4973942 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem4973941 B t x) (@lem4973938 A B t x s P f h1)). Qed.
Lemma lem4973948 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4973949 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term810 A B t f x'' _62511) = (term828 A B f x'' t _62511).
Proof. exact (@lem4973948 ((term770 A B f x'' _62511) = _62511) (term708 B t _62511)). Qed.
Lemma lem4973957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4973958 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term829 A B t f x'' _62511) = (term830 A B f x'' t _62511).
Proof. exact (MK_COMB (@lem4973957) (@lem4973949 A B f x'' t _62511)). Qed.
Lemma lem4973966 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term828 A B f x'' t _62511) = (term828 A B f x'' t _62511).
Proof. exact (eq_refl (term828 A B f x'' t _62511)). Qed.
Lemma lem4973967 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term810 A B t f x'' _62511) = (term828 A B f x'' t _62511)) = ((term828 A B f x'' t _62511) = (term828 A B f x'' t _62511)).
Proof. exact (MK_COMB (@lem4973958 A B f x'' t _62511) (@lem4973966 A B f x'' t _62511)). Qed.
Lemma lem4973969 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4973970 (x : Prop) : (x = x) = True.
Proof. exact (@lem4973969 Prop x). Qed.
Lemma lem4973971 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term828 A B f x'' t _62511) = (term828 A B f x'' t _62511)) = True.
Proof. exact (@lem4973970 (term828 A B f x'' t _62511)). Qed.
Lemma lem4973972 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term810 A B t f x'' _62511) = (term828 A B f x'' t _62511)) = True.
Proof. exact (TRANS (@lem4973967 A B f x'' t _62511) (@lem4973971 A B f x'' t _62511)). Qed.
Lemma lem4973973 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : True = ((term810 A B t f x'' _62511) = (term828 A B f x'' t _62511)).
Proof. exact (SYM (@lem4973972 A B f x'' t _62511)). Qed.
Lemma lem4973974 {A B : Type'} (f : A -> B) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term810 A B t f x'' _62511) = (term828 A B f x'' t _62511).
Proof. exact (EQ_MP (@lem4973973 A B f x'' t _62511) (@lem0)). Qed.
Lemma lem4973975 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term828 A B f x'' t _62511.
Proof. exact (EQ_MP (@lem4973974 A B f x'' t _62511) (@lem4972994 A B _62511 t s f x'' h1)). Qed.
Lemma lem4973977 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4973978 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_62511 : B) : (term828 A B f x'' t _62511) = (term832 A B t f x'' _62511).
Proof. exact (@lem4973977 (term708 B t _62511) ((term770 A B f x'' _62511) = _62511)). Qed.
Lemma lem4973980 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4973981 {B : Type'} (t : B -> Prop) (_62511 : B) : (term833 B t _62511) = (@I (B -> Prop) t _62511).
Proof. exact (@lem4973980 (@I (B -> Prop) t _62511)). Qed.
Lemma lem4973982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4973983 {B : Type'} (t : B -> Prop) (_62511 : B) : (term834 B t _62511) = (term835 B t _62511).
Proof. exact (MK_COMB (@lem4973982) (@lem4973981 B t _62511)). Qed.
Lemma lem4973984 {A B : Type'} (f : A -> B) (x'' : B -> A) (_62511 : B) : ((term770 A B f x'' _62511) = _62511) = ((term770 A B f x'' _62511) = _62511).
Proof. exact (eq_refl ((term770 A B f x'' _62511) = _62511)). Qed.
Lemma lem4973985 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_62511 : B) : (term832 A B t f x'' _62511) = (term836 A B t f x'' _62511).
Proof. exact (MK_COMB (@lem4973983 B t _62511) (@lem4973984 A B f x'' _62511)). Qed.
Lemma lem4973986 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : B -> A) (_62511 : B) : (term828 A B f x'' t _62511) = (term836 A B t f x'' _62511).
Proof. exact (TRANS (@lem4973978 A B t f x'' _62511) (@lem4973985 A B t f x'' _62511)). Qed.
Lemma lem4973989 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' _62511.
Proof. exact (EQ_MP (@lem4973986 A B t f x'' _62511) (@lem4973975 A B _62511 t s f x'' h1)). Qed.
Lemma lem4973990 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' _62511.
Proof. exact (@lem4973989 A B _62511 t s f x'' h1). Qed.
Lemma lem4973991 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' x.
Proof. exact (@lem4973990 A B x t s f x'' h1). Qed.
Lemma lem4973994 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : (term770 A B f x'' x) = x.
Proof. exact (@lem4973991 A B x t s f x'' h1 (@lem4973942 A B t x s P f h2)). Qed.
Lemma lem4973995 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term837 A B f x'' x.
Proof. exact (fun h0 : term838 A B f x'' x => @lem4973994 A B x'' t x s P f h1 h2). Qed.
Lemma lem4973997 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4973998 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term837 A B f x'' x) = ((term770 A B f x'' x) = x).
Proof. exact (@lem4973997 ((term770 A B f x'' x) = x)). Qed.
Lemma lem4973999 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : (term770 A B f x'' x) = x.
Proof. exact (EQ_MP (@lem4973998 A B f x'' x) (@lem4973995 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974001 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4974002 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4974001 B x). Qed.
Lemma lem4974003 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term770 A B f x'' x) = (term770 A B f x'' x).
Proof. exact (@lem4974002 B (term770 A B f x'' x)). Qed.
Lemma lem4974004 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term839 A B f x'' x.
Proof. exact (fun h0 : term840 A B f x'' x => @lem4974003 A B f x'' x). Qed.
Lemma lem4974006 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974007 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term839 A B f x'' x) = ((term770 A B f x'' x) = (term770 A B f x'' x)).
Proof. exact (@lem4974006 ((term770 A B f x'' x) = (term770 A B f x'' x))). Qed.
Lemma lem4974008 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term770 A B f x'' x) = (term770 A B f x'' x).
Proof. exact (EQ_MP (@lem4974007 A B f x'' x) (@lem4974004 A B f x'' x)). Qed.
Lemma lem4974026 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4974027 {B : Type'} (y : B) (x : B) (z : B) : (term841 B x y z) = (term842 B y x z).
Proof. exact (@lem4974026 (y = z) (term843 B x z)). Qed.
Lemma lem4974037 {B : Type'} (x : B) (y : B) : (term844 B x y) = (term844 B x y).
Proof. exact (eq_refl (term844 B x y)). Qed.
Lemma lem4974038 {B : Type'} (y : B) (x : B) (z : B) : (term825 B x y z) = (term845 B y x z).
Proof. exact (MK_COMB (@lem4974037 B x y) (@lem4974027 B y x z)). Qed.
Lemma lem4974042 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4974043 {B : Type'} (y : B) (x : B) (z : B) : (term845 B y x z) = (term846 B y x z).
Proof. exact (@lem4974042 (y = z) (term843 B x y) (term843 B x z)). Qed.
Lemma lem4974065 {B : Type'} (y : B) (x : B) (z : B) : (term825 B x y z) = (term846 B y x z).
Proof. exact (TRANS (@lem4974038 B y x z) (@lem4974043 B y x z)). Qed.
Lemma lem4974066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4974067 {B : Type'} (y : B) (x : B) (z : B) : (term847 B x y z) = (term848 B y x z).
Proof. exact (MK_COMB (@lem4974066) (@lem4974065 B y x z)). Qed.
Lemma lem4974089 {B : Type'} (y : B) (x : B) (z : B) : (term846 B y x z) = (term846 B y x z).
Proof. exact (eq_refl (term846 B y x z)). Qed.
Lemma lem4974090 {B : Type'} (y : B) (x : B) (z : B) : ((term825 B x y z) = (term846 B y x z)) = ((term846 B y x z) = (term846 B y x z)).
Proof. exact (MK_COMB (@lem4974067 B y x z) (@lem4974089 B y x z)). Qed.
Lemma lem4974092 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4974093 (x : Prop) : (x = x) = True.
Proof. exact (@lem4974092 Prop x). Qed.
Lemma lem4974094 {B : Type'} (y : B) (x : B) (z : B) : ((term846 B y x z) = (term846 B y x z)) = True.
Proof. exact (@lem4974093 (term846 B y x z)). Qed.
Lemma lem4974095 {B : Type'} (y : B) (x : B) (z : B) : ((term825 B x y z) = (term846 B y x z)) = True.
Proof. exact (TRANS (@lem4974090 B y x z) (@lem4974094 B y x z)). Qed.
Lemma lem4974096 {B : Type'} (y : B) (x : B) (z : B) : True = ((term825 B x y z) = (term846 B y x z)).
Proof. exact (SYM (@lem4974095 B y x z)). Qed.
Lemma lem4974097 {B : Type'} (y : B) (x : B) (z : B) : (term825 B x y z) = (term846 B y x z).
Proof. exact (EQ_MP (@lem4974096 B y x z) (@lem0)). Qed.
Lemma lem4974098 {B : Type'} (y : B) (x : B) (z : B) : term846 B y x z.
Proof. exact (EQ_MP (@lem4974097 B y x z) (@lem4973897 B x y z)). Qed.
Lemma lem4974100 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4974101 {B : Type'} (x : B) (y : B) (z : B) : (term846 B y x z) = (term849 B x y z).
Proof. exact (@lem4974100 (term850 B y x z) (y = z)). Qed.
Lemma lem4974103 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4974104 {B : Type'} (y : B) (x : B) (z : B) : (term853 B y x z) = (term854 B y x z).
Proof. exact (@lem4974103 (term843 B x y) (term843 B x z)). Qed.
Lemma lem4974106 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974107 {B : Type'} (x : B) (y : B) : (term855 B x y) = (x = y).
Proof. exact (@lem4974106 (x = y)). Qed.
Lemma lem4974108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4974109 {B : Type'} (x : B) (y : B) : (term856 B x y) = (term857 B x y).
Proof. exact (MK_COMB (@lem4974108) (@lem4974107 B x y)). Qed.
Lemma lem4974111 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974112 {B : Type'} (x : B) (z : B) : (term855 B x z) = (x = z).
Proof. exact (@lem4974111 (x = z)). Qed.
Lemma lem4974113 {B : Type'} (y : B) (x : B) (z : B) : (term854 B y x z) = (term858 B y x z).
Proof. exact (MK_COMB (@lem4974109 B x y) (@lem4974112 B x z)). Qed.
Lemma lem4974114 {B : Type'} (y : B) (x : B) (z : B) : (term853 B y x z) = (term858 B y x z).
Proof. exact (TRANS (@lem4974104 B y x z) (@lem4974113 B y x z)). Qed.
Lemma lem4974115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4974116 {B : Type'} (y : B) (x : B) (z : B) : (term859 B y x z) = (term860 B y x z).
Proof. exact (MK_COMB (@lem4974115) (@lem4974114 B y x z)). Qed.
Lemma lem4974117 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4974118 {B : Type'} (x : B) (y : B) (z : B) : (term849 B x y z) = (term861 B x y z).
Proof. exact (MK_COMB (@lem4974116 B y x z) (@lem4974117 B y z)). Qed.
Lemma lem4974119 {B : Type'} (x : B) (y : B) (z : B) : (term846 B y x z) = (term861 B x y z).
Proof. exact (TRANS (@lem4974101 B x y z) (@lem4974118 B x y z)). Qed.
Lemma lem4974121 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term862 A B f x'' x.
Proof. exact (conj (@lem4973999 A B x'' t x s P f h1 h2) (@lem4974008 A B f x'' x)). Qed.
Lemma lem4974123 {B : Type'} (x : B) (y : B) (z : B) : term861 B x y z.
Proof. exact (EQ_MP (@lem4974119 B x y z) (@lem4974098 B y x z)). Qed.
Lemma lem4974124 {B : Type'} (x : B) (y : B) (z : B) : term861 B x y z.
Proof. exact (@lem4974123 B x y z). Qed.
Lemma lem4974125 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term863 A B f x'' x.
Proof. exact (@lem4974124 B (term770 A B f x'' x) x (term770 A B f x'' x)). Qed.
Lemma lem4974128 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : x = (term770 A B f x'' x).
Proof. exact (@lem4974125 A B f x'' x (@lem4974121 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974129 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term864 A B f x'' x.
Proof. exact (fun h0 : term865 A B f x'' x => @lem4974128 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974131 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974132 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term864 A B f x'' x) = (x = (term770 A B f x'' x)).
Proof. exact (@lem4974131 (x = (term770 A B f x'' x))). Qed.
Lemma lem4974133 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : x = (term770 A B f x'' x).
Proof. exact (EQ_MP (@lem4974132 A B f x'' x) (@lem4974129 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974135 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem4972135 A B t x s P f h1)). Qed.
Lemma lem4974136 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term826 B t x.
Proof. exact (fun h0 : term708 B t x => @lem4974135 A B t x s P f h1). Qed.
Lemma lem4974138 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974139 {B : Type'} (t : B -> Prop) (x : B) : (term826 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4974138 (@I (B -> Prop) t x)). Qed.
Lemma lem4974140 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem4974139 B t x) (@lem4974136 A B t x s P f h1)). Qed.
Lemma lem4974146 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4974147 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term809 A B t s x'' _62511) = (term866 A B s x'' t _62511).
Proof. exact (@lem4974146 (term775 A B s x'' _62511) (term708 B t _62511)). Qed.
Lemma lem4974153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4974154 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term867 A B t s x'' _62511) = (term868 A B s x'' t _62511).
Proof. exact (MK_COMB (@lem4974153) (@lem4974147 A B s x'' t _62511)). Qed.
Lemma lem4974160 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term866 A B s x'' t _62511) = (term866 A B s x'' t _62511).
Proof. exact (eq_refl (term866 A B s x'' t _62511)). Qed.
Lemma lem4974161 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term809 A B t s x'' _62511) = (term866 A B s x'' t _62511)) = ((term866 A B s x'' t _62511) = (term866 A B s x'' t _62511)).
Proof. exact (MK_COMB (@lem4974154 A B s x'' t _62511) (@lem4974160 A B s x'' t _62511)). Qed.
Lemma lem4974163 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4974164 (x : Prop) : (x = x) = True.
Proof. exact (@lem4974163 Prop x). Qed.
Lemma lem4974165 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term866 A B s x'' t _62511) = (term866 A B s x'' t _62511)) = True.
Proof. exact (@lem4974164 (term866 A B s x'' t _62511)). Qed.
Lemma lem4974166 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : ((term809 A B t s x'' _62511) = (term866 A B s x'' t _62511)) = True.
Proof. exact (TRANS (@lem4974161 A B s x'' t _62511) (@lem4974165 A B s x'' t _62511)). Qed.
Lemma lem4974167 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : True = ((term809 A B t s x'' _62511) = (term866 A B s x'' t _62511)).
Proof. exact (SYM (@lem4974166 A B s x'' t _62511)). Qed.
Lemma lem4974168 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (t : B -> Prop) (_62511 : B) : (term809 A B t s x'' _62511) = (term866 A B s x'' t _62511).
Proof. exact (EQ_MP (@lem4974167 A B s x'' t _62511) (@lem0)). Qed.
Lemma lem4974169 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term866 A B s x'' t _62511.
Proof. exact (EQ_MP (@lem4974168 A B s x'' t _62511) (@lem4972988 A B _62511 t s f x'' h1)). Qed.
Lemma lem4974171 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4974172 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x'' : B -> A) (_62511 : B) : (term866 A B s x'' t _62511) = (term869 A B t s x'' _62511).
Proof. exact (@lem4974171 (term708 B t _62511) (term775 A B s x'' _62511)). Qed.
Lemma lem4974174 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974175 {B : Type'} (t : B -> Prop) (_62511 : B) : (term833 B t _62511) = (@I (B -> Prop) t _62511).
Proof. exact (@lem4974174 (@I (B -> Prop) t _62511)). Qed.
Lemma lem4974176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4974177 {B : Type'} (t : B -> Prop) (_62511 : B) : (term834 B t _62511) = (term835 B t _62511).
Proof. exact (MK_COMB (@lem4974176) (@lem4974175 B t _62511)). Qed.
Lemma lem4974178 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (_62511 : B) : (term775 A B s x'' _62511) = (term775 A B s x'' _62511).
Proof. exact (eq_refl (term775 A B s x'' _62511)). Qed.
Lemma lem4974179 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x'' : B -> A) (_62511 : B) : (term869 A B t s x'' _62511) = (term870 A B t s x'' _62511).
Proof. exact (MK_COMB (@lem4974177 B t _62511) (@lem4974178 A B s x'' _62511)). Qed.
Lemma lem4974180 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x'' : B -> A) (_62511 : B) : (term866 A B s x'' t _62511) = (term870 A B t s x'' _62511).
Proof. exact (TRANS (@lem4974172 A B t s x'' _62511) (@lem4974179 A B t s x'' _62511)). Qed.
Lemma lem4974183 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term870 A B t s x'' _62511.
Proof. exact (EQ_MP (@lem4974180 A B t s x'' _62511) (@lem4974169 A B _62511 t s f x'' h1)). Qed.
Lemma lem4974184 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term870 A B t s x'' _62511.
Proof. exact (@lem4974183 A B _62511 t s f x'' h1). Qed.
Lemma lem4974185 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term870 A B t s x'' x.
Proof. exact (@lem4974184 A B x t s f x'' h1). Qed.
Lemma lem4974188 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term775 A B s x'' x.
Proof. exact (@lem4974185 A B x t s f x'' h1 (@lem4974140 A B t x s P f h2)). Qed.
Lemma lem4974189 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term871 A B s x'' x.
Proof. exact (fun h0 : term872 A B s x'' x => @lem4974188 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974191 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974192 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (x : B) : (term871 A B s x'' x) = (term775 A B s x'' x).
Proof. exact (@lem4974191 (term775 A B s x'' x)). Qed.
Lemma lem4974193 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term775 A B s x'' x.
Proof. exact (EQ_MP (@lem4974192 A B s x'' x) (@lem4974189 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974195 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (proj1 (@lem4972135 A B t x s P f h1)). Qed.
Lemma lem4974196 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term826 B t x.
Proof. exact (fun h0 : term708 B t x => @lem4974195 A B t x s P f h1). Qed.
Lemma lem4974198 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974199 {B : Type'} (t : B -> Prop) (x : B) : (term826 B t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4974198 (@I (B -> Prop) t x)). Qed.
Lemma lem4974200 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) t x.
Proof. exact (EQ_MP (@lem4974199 B t x) (@lem4974196 A B t x s P f h1)). Qed.
Lemma lem4974202 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' _62511.
Proof. exact (EQ_MP (@lem4973986 A B t f x'' _62511) (@lem4973975 A B _62511 t s f x'' h1)). Qed.
Lemma lem4974203 {A B : Type'} (_62511 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' _62511.
Proof. exact (@lem4974202 A B _62511 t s f x'' h1). Qed.
Lemma lem4974204 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x'' : B -> A) (h1 : term649 A B t s f x'') : term836 A B t f x'' x.
Proof. exact (@lem4974203 A B x t s f x'' h1). Qed.
Lemma lem4974207 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : (term770 A B f x'' x) = x.
Proof. exact (@lem4974204 A B x t s f x'' h1 (@lem4974200 A B t x s P f h2)). Qed.
Lemma lem4974208 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term837 A B f x'' x.
Proof. exact (fun h0 : term838 A B f x'' x => @lem4974207 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974210 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974211 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term837 A B f x'' x) = ((term770 A B f x'' x) = x).
Proof. exact (@lem4974210 ((term770 A B f x'' x) = x)). Qed.
Lemma lem4974212 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : (term770 A B f x'' x) = x.
Proof. exact (EQ_MP (@lem4974211 A B f x'' x) (@lem4974208 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974214 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4974215 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4974214 B x). Qed.
Lemma lem4974216 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term770 A B f x'' x) = (term770 A B f x'' x).
Proof. exact (@lem4974215 B (term770 A B f x'' x)). Qed.
Lemma lem4974217 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term839 A B f x'' x.
Proof. exact (fun h0 : term840 A B f x'' x => @lem4974216 A B f x'' x). Qed.
Lemma lem4974219 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974220 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term839 A B f x'' x) = ((term770 A B f x'' x) = (term770 A B f x'' x)).
Proof. exact (@lem4974219 ((term770 A B f x'' x) = (term770 A B f x'' x))). Qed.
Lemma lem4974221 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term770 A B f x'' x) = (term770 A B f x'' x).
Proof. exact (EQ_MP (@lem4974220 A B f x'' x) (@lem4974217 A B f x'' x)). Qed.
Lemma lem4974222 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term862 A B f x'' x.
Proof. exact (conj (@lem4974212 A B x'' t x s P f h1 h2) (@lem4974221 A B f x'' x)). Qed.
Lemma lem4974224 {B : Type'} (x : B) (y : B) (z : B) : term861 B x y z.
Proof. exact (EQ_MP (@lem4974119 B x y z) (@lem4974098 B y x z)). Qed.
Lemma lem4974225 {B : Type'} (x : B) (y : B) (z : B) : term861 B x y z.
Proof. exact (@lem4974224 B x y z). Qed.
Lemma lem4974226 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : term863 A B f x'' x.
Proof. exact (@lem4974225 B (term770 A B f x'' x) x (term770 A B f x'' x)). Qed.
Lemma lem4974229 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : x = (term770 A B f x'' x).
Proof. exact (@lem4974226 A B f x'' x (@lem4974222 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974230 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term864 A B f x'' x.
Proof. exact (fun h0 : term865 A B f x'' x => @lem4974229 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974232 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974233 {A B : Type'} (f : A -> B) (x'' : B -> A) (x : B) : (term864 A B f x'' x) = (x = (term770 A B f x'' x)).
Proof. exact (@lem4974232 (x = (term770 A B f x'' x))). Qed.
Lemma lem4974234 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : x = (term770 A B f x'' x).
Proof. exact (EQ_MP (@lem4974233 A B f x'' x) (@lem4974230 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974236 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem4974237 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem4974236 B x). Qed.
Lemma lem4974238 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (@lem4974237 B P). Qed.
Lemma lem4974239 {B : Type'} (P : B -> Prop) : term873 B P.
Proof. exact (fun h0 : term874 B P => @lem4974238 B P). Qed.
Lemma lem4974241 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974242 {B : Type'} (P : B -> Prop) : (term873 B P) = (P = P).
Proof. exact (@lem4974241 (P = P)). Qed.
Lemma lem4974243 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (EQ_MP (@lem4974242 B P) (@lem4974239 B P)). Qed.
Lemma lem4974245 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) P x.
Proof. exact (proj2 (@lem4972135 A B t x s P f h1)). Qed.
Lemma lem4974246 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term826 B P x.
Proof. exact (fun h0 : term708 B P x => @lem4974245 A B t x s P f h1). Qed.
Lemma lem4974248 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974249 {B : Type'} (P : B -> Prop) (x : B) : (term826 B P x) = (@I (B -> Prop) P x).
Proof. exact (@lem4974248 (@I (B -> Prop) P x)). Qed.
Lemma lem4974250 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : @I (B -> Prop) P x.
Proof. exact (EQ_MP (@lem4974249 B P x) (@lem4974246 A B t x s P f h1)). Qed.
Lemma lem4974268 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4974269 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term822 B _62620 _62621 _62618 _62619) = (term875 B _62621 _62620 _62618 _62619).
Proof. exact (@lem4974268 (@I (B -> Prop) _62620 _62621) (term876 B _62618 _62620) (term708 B _62618 _62619)). Qed.
Lemma lem4974287 {B : Type'} (_62619 : B) (_62621 : B) : (term844 B _62619 _62621) = (term844 B _62619 _62621).
Proof. exact (eq_refl (term844 B _62619 _62621)). Qed.
Lemma lem4974288 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term824 B _62620 _62621 _62618 _62619) = (term877 B _62621 _62620 _62618 _62619).
Proof. exact (MK_COMB (@lem4974287 B _62619 _62621) (@lem4974269 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974292 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4974293 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term877 B _62621 _62620 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619).
Proof. exact (@lem4974292 (@I (B -> Prop) _62620 _62621) (term843 B _62619 _62621) (term879 B _62620 _62618 _62619)). Qed.
Lemma lem4974323 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term824 B _62620 _62621 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619).
Proof. exact (TRANS (@lem4974288 B _62621 _62620 _62618 _62619) (@lem4974293 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4974325 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term880 B _62620 _62621 _62618 _62619) = (term881 B _62621 _62620 _62618 _62619).
Proof. exact (MK_COMB (@lem4974324) (@lem4974323 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974355 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term878 B _62621 _62620 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619).
Proof. exact (eq_refl (term878 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974356 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : ((term824 B _62620 _62621 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619)) = ((term878 B _62621 _62620 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619)).
Proof. exact (MK_COMB (@lem4974325 B _62621 _62620 _62618 _62619) (@lem4974355 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974358 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4974359 (x : Prop) : (x = x) = True.
Proof. exact (@lem4974358 Prop x). Qed.
Lemma lem4974360 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : ((term878 B _62621 _62620 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619)) = True.
Proof. exact (@lem4974359 (term878 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974361 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : ((term824 B _62620 _62621 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619)) = True.
Proof. exact (TRANS (@lem4974356 B _62621 _62620 _62618 _62619) (@lem4974360 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974362 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : True = ((term824 B _62620 _62621 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619)).
Proof. exact (SYM (@lem4974361 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974363 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term824 B _62620 _62621 _62618 _62619) = (term878 B _62621 _62620 _62618 _62619).
Proof. exact (EQ_MP (@lem4974362 B _62621 _62620 _62618 _62619) (@lem0)). Qed.
Lemma lem4974364 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : term878 B _62621 _62620 _62618 _62619.
Proof. exact (EQ_MP (@lem4974363 B _62621 _62620 _62618 _62619) (@lem4973581 B _62620 _62621 _62618 _62619)). Qed.
Lemma lem4974366 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4974367 {B : Type'} (_62618 : B -> Prop) (_62619 : B) (_62620 : B -> Prop) (_62621 : B) : (term878 B _62621 _62620 _62618 _62619) = (term882 B _62618 _62619 _62620 _62621).
Proof. exact (@lem4974366 (term883 B _62621 _62620 _62618 _62619) (@I (B -> Prop) _62620 _62621)). Qed.
Lemma lem4974369 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4974370 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term884 B _62621 _62620 _62618 _62619) = (term885 B _62621 _62620 _62618 _62619).
Proof. exact (@lem4974369 (term843 B _62619 _62621) (term879 B _62620 _62618 _62619)). Qed.
Lemma lem4974372 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974373 {B : Type'} (_62619 : B) (_62621 : B) : (term855 B _62619 _62621) = (_62619 = _62621).
Proof. exact (@lem4974372 (_62619 = _62621)). Qed.
Lemma lem4974374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4974375 {B : Type'} (_62619 : B) (_62621 : B) : (term856 B _62619 _62621) = (term857 B _62619 _62621).
Proof. exact (MK_COMB (@lem4974374) (@lem4974373 B _62619 _62621)). Qed.
Lemma lem4974377 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4974378 {B : Type'} (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term886 B _62620 _62618 _62619) = (term887 B _62620 _62618 _62619).
Proof. exact (@lem4974377 (term876 B _62618 _62620) (term708 B _62618 _62619)). Qed.
Lemma lem4974380 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974381 {B : Type'} (_62618 : B -> Prop) (_62620 : B -> Prop) : (term888 B _62618 _62620) = (_62618 = _62620).
Proof. exact (@lem4974380 (_62618 = _62620)). Qed.
Lemma lem4974382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4974383 {B : Type'} (_62618 : B -> Prop) (_62620 : B -> Prop) : (term889 B _62618 _62620) = (term890 B _62618 _62620).
Proof. exact (MK_COMB (@lem4974382) (@lem4974381 B _62618 _62620)). Qed.
Lemma lem4974385 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974386 {B : Type'} (_62618 : B -> Prop) (_62619 : B) : (term833 B _62618 _62619) = (@I (B -> Prop) _62618 _62619).
Proof. exact (@lem4974385 (@I (B -> Prop) _62618 _62619)). Qed.
Lemma lem4974387 {B : Type'} (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term887 B _62620 _62618 _62619) = (term891 B _62620 _62618 _62619).
Proof. exact (MK_COMB (@lem4974383 B _62618 _62620) (@lem4974386 B _62618 _62619)). Qed.
Lemma lem4974388 {B : Type'} (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term886 B _62620 _62618 _62619) = (term891 B _62620 _62618 _62619).
Proof. exact (TRANS (@lem4974378 B _62620 _62618 _62619) (@lem4974387 B _62620 _62618 _62619)). Qed.
Lemma lem4974389 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term885 B _62621 _62620 _62618 _62619) = (term892 B _62621 _62620 _62618 _62619).
Proof. exact (MK_COMB (@lem4974375 B _62619 _62621) (@lem4974388 B _62620 _62618 _62619)). Qed.
Lemma lem4974390 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term884 B _62621 _62620 _62618 _62619) = (term892 B _62621 _62620 _62618 _62619).
Proof. exact (TRANS (@lem4974370 B _62621 _62620 _62618 _62619) (@lem4974389 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4974392 {B : Type'} (_62621 : B) (_62620 : B -> Prop) (_62618 : B -> Prop) (_62619 : B) : (term893 B _62621 _62620 _62618 _62619) = (term894 B _62621 _62620 _62618 _62619).
Proof. exact (MK_COMB (@lem4974391) (@lem4974390 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974393 {B : Type'} (_62620 : B -> Prop) (_62621 : B) : (@I (B -> Prop) _62620 _62621) = (@I (B -> Prop) _62620 _62621).
Proof. exact (eq_refl (@I (B -> Prop) _62620 _62621)). Qed.
Lemma lem4974394 {B : Type'} (_62618 : B -> Prop) (_62619 : B) (_62620 : B -> Prop) (_62621 : B) : (term882 B _62618 _62619 _62620 _62621) = (term895 B _62618 _62619 _62620 _62621).
Proof. exact (MK_COMB (@lem4974392 B _62621 _62620 _62618 _62619) (@lem4974393 B _62620 _62621)). Qed.
Lemma lem4974395 {B : Type'} (_62618 : B -> Prop) (_62619 : B) (_62620 : B -> Prop) (_62621 : B) : (term878 B _62621 _62620 _62618 _62619) = (term895 B _62618 _62619 _62620 _62621).
Proof. exact (TRANS (@lem4974367 B _62618 _62619 _62620 _62621) (@lem4974394 B _62618 _62619 _62620 _62621)). Qed.
Lemma lem4974397 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term896 B P x.
Proof. exact (conj (@lem4974243 B P) (@lem4974250 A B t x s P f h1)). Qed.
Lemma lem4974398 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term897 A B f x'' P x.
Proof. exact (conj (@lem4974234 A B x'' t x s P f h1 h2) (@lem4974397 A B t x s P f h2)). Qed.
Lemma lem4974400 {B : Type'} (_62618 : B -> Prop) (_62619 : B) (_62620 : B -> Prop) (_62621 : B) : term895 B _62618 _62619 _62620 _62621.
Proof. exact (EQ_MP (@lem4974395 B _62618 _62619 _62620 _62621) (@lem4974364 B _62621 _62620 _62618 _62619)). Qed.
Lemma lem4974401 {B : Type'} (_62618 : B -> Prop) (_62619 : B) (_62620 : B -> Prop) (_62621 : B) : term895 B _62618 _62619 _62620 _62621.
Proof. exact (@lem4974400 B _62618 _62619 _62620 _62621). Qed.
Lemma lem4974402 {A B : Type'} (P : B -> Prop) (f : A -> B) (x'' : B -> A) (x : B) : term898 A B P f x'' x.
Proof. exact (@lem4974401 B P x P (term770 A B f x'' x)). Qed.
Lemma lem4974405 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term899 A B P f x'' x.
Proof. exact (@lem4974402 A B P f x'' x (@lem4974398 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974406 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term900 A B P f x'' x.
Proof. exact (fun h0 : term901 A B P f x'' x => @lem4974405 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974408 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974409 {A B : Type'} (P : B -> Prop) (f : A -> B) (x'' : B -> A) (x : B) : (term900 A B P f x'' x) = (term899 A B P f x'' x).
Proof. exact (@lem4974408 (term899 A B P f x'' x)). Qed.
Lemma lem4974410 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term899 A B P f x'' x.
Proof. exact (EQ_MP (@lem4974409 A B P f x'' x) (@lem4974406 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974412 (a : Prop) (b : Prop) : (term902 a b) = (term903 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4974413 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term759 A B s P f _62525) = (term904 A B s P f _62525).
Proof. exact (@lem4974412 (@I (A -> Prop) s _62525) (term749 A B P f _62525)). Qed.
Lemma lem4974414 {A B : Type'} (x : B) (f : A -> B) (_62525 : A) : (term711 A B x f _62525) = (term711 A B x f _62525).
Proof. exact (eq_refl (term711 A B x f _62525)). Qed.
Lemma lem4974415 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term760 A B x s P f _62525) = (term905 A B x s P f _62525).
Proof. exact (MK_COMB (@lem4974414 A B x f _62525) (@lem4974413 A B s P f _62525)). Qed.
Lemma lem4974417 (a : Prop) (b : Prop) : (term902 a b) = (term903 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4974418 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term905 A B x s P f _62525) = (term906 A B x s P f _62525).
Proof. exact (@lem4974417 (x = (@I (A -> B) f _62525)) (term751 A B s P f _62525)). Qed.
Lemma lem4974419 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term760 A B x s P f _62525) = (term906 A B x s P f _62525).
Proof. exact (TRANS (@lem4974415 A B x s P f _62525) (@lem4974418 A B x s P f _62525)). Qed.
Lemma lem4974421 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4974422 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term906 A B x s P f _62525) = (term907 A B x s P f _62525).
Proof. exact (@lem4974421 (term753 A B x s P f _62525)). Qed.
Lemma lem4974423 {A B : Type'} (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62525 : A) : (term760 A B x s P f _62525) = (term907 A B x s P f _62525).
Proof. exact (TRANS (@lem4974419 A B x s P f _62525) (@lem4974422 A B x s P f _62525)). Qed.
Lemma lem4974425 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term908 A B s P f x'' x.
Proof. exact (conj (@lem4974193 A B x'' t x s P f h1 h2) (@lem4974410 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974426 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term909 A B s P f x'' x.
Proof. exact (conj (@lem4974133 A B x'' t x s P f h1 h2) (@lem4974425 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974428 {A B : Type'} (_62525 : A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term907 A B x s P f _62525.
Proof. exact (EQ_MP (@lem4974423 A B x s P f _62525) (@lem4972978 A B _62525 t x s P f h1)). Qed.
Lemma lem4974429 {A B : Type'} (_62525 : A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term907 A B x s P f _62525.
Proof. exact (@lem4974428 A B _62525 t x s P f h1). Qed.
Lemma lem4974430 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term765 A B t x s P f) : term910 A B s P f x'' x.
Proof. exact (@lem4974429 A B (@I (B -> A) x'' x) t x s P f h1). Qed.
Lemma lem4974433 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : False.
Proof. exact (@lem4974430 A B x'' t x s P f h2 (@lem4974426 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974434 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : term911.
Proof. exact (fun h0 : ~ False => @lem4974433 A B x'' t x s P f h1 h2). Qed.
Lemma lem4974436 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974437 : term911 = False.
Proof. exact (@lem4974436 False). Qed.
Lemma lem4974438 {A B : Type'} (x'' : B -> A) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term649 A B t s f x'') (h2 : term765 A B t x s P f) : False.
Proof. exact (EQ_MP (@lem4974437) (@lem4974434 A B x'' t x s P f h1 h2)). Qed.
Lemma lem4974851 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4974852 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4974851 B x). Qed.
Lemma lem4974853 {A B : Type'} (f : A -> B) (x' : A) : (@I (A -> B) f x') = (@I (A -> B) f x').
Proof. exact (@lem4974852 B (@I (A -> B) f x')). Qed.
Lemma lem4974854 {A B : Type'} (f : A -> B) (x' : A) : term912 A B f x'.
Proof. exact (fun h0 : term913 A B f x' => @lem4974853 A B f x'). Qed.
Lemma lem4974856 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974857 {A B : Type'} (f : A -> B) (x' : A) : (term912 A B f x') = ((@I (A -> B) f x') = (@I (A -> B) f x')).
Proof. exact (@lem4974856 ((@I (A -> B) f x') = (@I (A -> B) f x'))). Qed.
Lemma lem4974858 {A B : Type'} (f : A -> B) (x' : A) : (@I (A -> B) f x') = (@I (A -> B) f x').
Proof. exact (EQ_MP (@lem4974857 A B f x') (@lem4974854 A B f x')). Qed.
Lemma lem4974860 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem4972140 A B t x s P f x' h1)). Qed.
Lemma lem4974861 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term826 A s x'.
Proof. exact (fun h0 : term708 A s x' => @lem4974860 A B t x s P f x' h1). Qed.
Lemma lem4974863 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974864 {A : Type'} (s : A -> Prop) (x' : A) : (term826 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem4974863 (@I (A -> Prop) s x')). Qed.
Lemma lem4974865 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem4974864 A s x') (@lem4974861 A B t x s P f x' h1)). Qed.
Lemma lem4974883 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4974884 {A B : Type'} (t : B -> Prop) (_62538 : B) (s : A -> Prop) (_62539 : A) : (term914 A B s _62539 t _62538) = (term915 A B t _62538 s _62539).
Proof. exact (@lem4974883 (@I (B -> Prop) t _62538) (term708 A s _62539)). Qed.
Lemma lem4974890 {A B : Type'} (_62538 : B) (f : A -> B) (_62539 : A) : (term711 A B _62538 f _62539) = (term711 A B _62538 f _62539).
Proof. exact (eq_refl (term711 A B _62538 f _62539)). Qed.
Lemma lem4974891 {A B : Type'} (f : A -> B) (t : B -> Prop) (_62538 : B) (s : A -> Prop) (_62539 : A) : (term811 A B f s _62539 t _62538) = (term916 A B f t _62538 s _62539).
Proof. exact (MK_COMB (@lem4974890 A B _62538 f _62539) (@lem4974884 A B t _62538 s _62539)). Qed.
Lemma lem4974895 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4974896 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term916 A B f t _62538 s _62539) = (term917 A B t _62538 f s _62539).
Proof. exact (@lem4974895 (@I (B -> Prop) t _62538) (term710 A B _62538 f _62539) (term708 A s _62539)). Qed.
Lemma lem4974914 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term811 A B f s _62539 t _62538) = (term917 A B t _62538 f s _62539).
Proof. exact (TRANS (@lem4974891 A B f t _62538 s _62539) (@lem4974896 A B t _62538 f s _62539)). Qed.
Lemma lem4974915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4974916 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term918 A B f s _62539 t _62538) = (term919 A B t _62538 f s _62539).
Proof. exact (MK_COMB (@lem4974915) (@lem4974914 A B t _62538 f s _62539)). Qed.
Lemma lem4974934 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term917 A B t _62538 f s _62539) = (term917 A B t _62538 f s _62539).
Proof. exact (eq_refl (term917 A B t _62538 f s _62539)). Qed.
Lemma lem4974935 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : ((term811 A B f s _62539 t _62538) = (term917 A B t _62538 f s _62539)) = ((term917 A B t _62538 f s _62539) = (term917 A B t _62538 f s _62539)).
Proof. exact (MK_COMB (@lem4974916 A B t _62538 f s _62539) (@lem4974934 A B t _62538 f s _62539)). Qed.
Lemma lem4974937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4974938 (x : Prop) : (x = x) = True.
Proof. exact (@lem4974937 Prop x). Qed.
Lemma lem4974939 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : ((term917 A B t _62538 f s _62539) = (term917 A B t _62538 f s _62539)) = True.
Proof. exact (@lem4974938 (term917 A B t _62538 f s _62539)). Qed.
Lemma lem4974940 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : ((term811 A B f s _62539 t _62538) = (term917 A B t _62538 f s _62539)) = True.
Proof. exact (TRANS (@lem4974935 A B t _62538 f s _62539) (@lem4974939 A B t _62538 f s _62539)). Qed.
Lemma lem4974941 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : True = ((term811 A B f s _62539 t _62538) = (term917 A B t _62538 f s _62539)).
Proof. exact (SYM (@lem4974940 A B t _62538 f s _62539)). Qed.
Lemma lem4974942 {A B : Type'} (t : B -> Prop) (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term811 A B f s _62539 t _62538) = (term917 A B t _62538 f s _62539).
Proof. exact (EQ_MP (@lem4974941 A B t _62538 f s _62539) (@lem0)). Qed.
Lemma lem4974943 {A B : Type'} (_62538 : B) (_62539 : A) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term917 A B t _62538 f s _62539.
Proof. exact (EQ_MP (@lem4974942 A B t _62538 f s _62539) (@lem4973218 A B _62539 _62538 _62510 P n f t s h1)). Qed.
Lemma lem4974945 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4974946 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62539 : A) (t : B -> Prop) (_62538 : B) : (term917 A B t _62538 f s _62539) = (term920 A B f s _62539 t _62538).
Proof. exact (@lem4974945 (term712 A B _62538 f s _62539) (@I (B -> Prop) t _62538)). Qed.
Lemma lem4974948 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4974949 {A B : Type'} (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term921 A B _62538 f s _62539) = (term922 A B _62538 f s _62539).
Proof. exact (@lem4974948 (term710 A B _62538 f _62539) (term708 A s _62539)). Qed.
Lemma lem4974951 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974952 {A B : Type'} (_62538 : B) (f : A -> B) (_62539 : A) : (term923 A B _62538 f _62539) = (_62538 = (@I (A -> B) f _62539)).
Proof. exact (@lem4974951 (_62538 = (@I (A -> B) f _62539))). Qed.
Lemma lem4974953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4974954 {A B : Type'} (_62538 : B) (f : A -> B) (_62539 : A) : (term924 A B _62538 f _62539) = (term752 A B _62538 f _62539).
Proof. exact (MK_COMB (@lem4974953) (@lem4974952 A B _62538 f _62539)). Qed.
Lemma lem4974956 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4974957 {A : Type'} (s : A -> Prop) (_62539 : A) : (term833 A s _62539) = (@I (A -> Prop) s _62539).
Proof. exact (@lem4974956 (@I (A -> Prop) s _62539)). Qed.
Lemma lem4974958 {A B : Type'} (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term922 A B _62538 f s _62539) = (term925 A B _62538 f s _62539).
Proof. exact (MK_COMB (@lem4974954 A B _62538 f _62539) (@lem4974957 A s _62539)). Qed.
Lemma lem4974959 {A B : Type'} (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term921 A B _62538 f s _62539) = (term925 A B _62538 f s _62539).
Proof. exact (TRANS (@lem4974949 A B _62538 f s _62539) (@lem4974958 A B _62538 f s _62539)). Qed.
Lemma lem4974960 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4974961 {A B : Type'} (_62538 : B) (f : A -> B) (s : A -> Prop) (_62539 : A) : (term926 A B _62538 f s _62539) = (term927 A B _62538 f s _62539).
Proof. exact (MK_COMB (@lem4974960) (@lem4974959 A B _62538 f s _62539)). Qed.
Lemma lem4974962 {B : Type'} (t : B -> Prop) (_62538 : B) : (@I (B -> Prop) t _62538) = (@I (B -> Prop) t _62538).
Proof. exact (eq_refl (@I (B -> Prop) t _62538)). Qed.
Lemma lem4974963 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62539 : A) (t : B -> Prop) (_62538 : B) : (term920 A B f s _62539 t _62538) = (term928 A B f s _62539 t _62538).
Proof. exact (MK_COMB (@lem4974961 A B _62538 f s _62539) (@lem4974962 B t _62538)). Qed.
Lemma lem4974964 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62539 : A) (t : B -> Prop) (_62538 : B) : (term917 A B t _62538 f s _62539) = (term928 A B f s _62539 t _62538).
Proof. exact (TRANS (@lem4974946 A B f s _62539 t _62538) (@lem4974963 A B f s _62539 t _62538)). Qed.
Lemma lem4974966 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term929 A B f s x'.
Proof. exact (conj (@lem4974858 A B f x') (@lem4974865 A B t x s P f x' h1)). Qed.
Lemma lem4974968 {A B : Type'} (_62539 : A) (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term928 A B f s _62539 t _62538.
Proof. exact (EQ_MP (@lem4974964 A B f s _62539 t _62538) (@lem4974943 A B _62538 _62539 _62510 P n f t s h1)). Qed.
Lemma lem4974969 {A B : Type'} (_62539 : A) (_62538 : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term928 A B f s _62539 t _62538.
Proof. exact (@lem4974968 A B _62539 _62538 _62510 P n f t s h1). Qed.
Lemma lem4974970 {A B : Type'} (x' : A) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62510 P n f t s) : term930 A B s t f x'.
Proof. exact (@lem4974969 A B x' (@I (A -> B) f x') _62510 P n f t s h1). Qed.
Lemma lem4974973 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term239 A B _62510 P n f t s) (h2 : term756 A B t x s P f x') : term749 A B t f x'.
Proof. exact (@lem4974970 A B x' _62510 P n f t s h1 (@lem4974966 A B t x s P f x' h2)). Qed.
Lemma lem4974974 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term239 A B _62510 P n f t s) (h2 : term756 A B t x s P f x') : term931 A B t f x'.
Proof. exact (fun h0 : term758 A B t f x' => @lem4974973 A B _62510 n t x s P f x' h1 h2). Qed.
Lemma lem4974976 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974977 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term931 A B t f x') = (term749 A B t f x').
Proof. exact (@lem4974976 (term749 A B t f x')). Qed.
Lemma lem4974978 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term239 A B _62510 P n f t s) (h2 : term756 A B t x s P f x') : term749 A B t f x'.
Proof. exact (EQ_MP (@lem4974977 A B t f x') (@lem4974974 A B _62510 n t x s P f x' h1 h2)). Qed.
Lemma lem4974981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4974983 {A B : Type'} (t : B -> Prop) (f : A -> B) (x' : A) : (term758 A B t f x') = (term932 A B t f x').
Proof. exact (@lem4974981 (term749 A B t f x')). Qed.
Lemma lem4974986 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term756 A B t x s P f x') : term932 A B t f x'.
Proof. exact (EQ_MP (@lem4974983 A B t f x') (@lem4973301 A B t x s P f x' h1 h2)). Qed.
Lemma lem4974989 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : False.
Proof. exact (@lem4974986 A B t x s P f x' h1 h3 (@lem4974978 A B _62510 n t x s P f x' h2 h3)). Qed.
Lemma lem4974990 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : term911.
Proof. exact (fun h0 : ~ False => @lem4974989 A B _62510 n t x s P f x' h1 h2 h3). Qed.
Lemma lem4974992 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4974993 : term911 = False.
Proof. exact (@lem4974992 False). Qed.
Lemma lem4975407 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term749 A B P f x'.
Proof. exact (proj2 (@lem4972140 A B t x s P f x' h1)). Qed.
Lemma lem4975408 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term931 A B P f x'.
Proof. exact (fun h0 : term758 A B P f x' => @lem4975407 A B t x s P f x' h1). Qed.
Lemma lem4975410 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4975411 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term931 A B P f x') = (term749 A B P f x').
Proof. exact (@lem4975410 (term749 A B P f x')). Qed.
Lemma lem4975412 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term756 A B t x s P f x') : term749 A B P f x'.
Proof. exact (EQ_MP (@lem4975411 A B P f x') (@lem4975408 A B t x s P f x' h1)). Qed.
Lemma lem4975415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4975417 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term758 A B P f x') = (term932 A B P f x').
Proof. exact (@lem4975415 (term749 A B P f x')). Qed.
Lemma lem4975420 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : term932 A B P f x'.
Proof. exact (EQ_MP (@lem4975417 A B P f x') (@lem4973496 A B t x s P f x' h1 h2)). Qed.
Lemma lem4975423 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : False.
Proof. exact (@lem4975420 A B t x s P f x' h1 h2 (@lem4975412 A B t x s P f x' h2)). Qed.
Lemma lem4975424 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : term911.
Proof. exact (fun h0 : ~ False => @lem4975423 A B t x s P f x' h1 h2). Qed.
Lemma lem4975426 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4975427 : term911 = False.
Proof. exact (@lem4975426 False). Qed.
Lemma lem4975429 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975427) (@lem4975424 A B t x s P f x' h1 h2)). Qed.
Lemma lem4975430 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4974993) (@lem4974990 A B _62510 n t x s P f x' h1 h2 h3)). Qed.
Lemma lem4975431 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : (term708 B P x) = False.
Proof. exact (prop_ext (fun h3 : term708 B P x => @lem4975429 A B t x s P f x' h1 h2) (fun h3 : False => @lem4973122 B P x h1)). Qed.
Lemma lem4975432 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975431 A B t x s P f x' h1 h2) (@lem4973122 B P x h1)). Qed.
Lemma lem4975433 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : (term708 B t x) = False.
Proof. exact (prop_ext (fun h4 : term708 B t x => @lem4975430 A B _62510 n t x s P f x' h1 h2 h3) (fun h4 : False => @lem4973052 B t x h1)). Qed.
Lemma lem4975434 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975433 A B _62510 n t x s P f x' h1 h2 h3) (@lem4973052 B t x h1)). Qed.
Lemma lem4975435 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : (term708 B P x) = False.
Proof. exact (prop_ext (fun h3 : term708 B P x => @lem4975432 A B t x s P f x' h1 h2) (fun h3 : False => @lem4972783 B P x h1)). Qed.
Lemma lem4975436 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975435 A B t x s P f x' h1 h2) (@lem4972783 B P x h1)). Qed.
Lemma lem4975437 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : (term708 B t x) = False.
Proof. exact (prop_ext (fun h4 : term708 B t x => @lem4975434 A B _62510 n t x s P f x' h1 h2 h3) (fun h4 : False => @lem4972574 B t x h1)). Qed.
Lemma lem4975438 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975437 A B _62510 n t x s P f x' h1 h2 h3) (@lem4972574 B t x h1)). Qed.
Lemma lem4975439 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : (term708 B P x) = False.
Proof. exact (prop_ext (fun h3 : term708 B P x => @lem4975436 A B t x s P f x' h1 h2) (fun h3 : False => @lem4972783 B P x h1)). Qed.
Lemma lem4975440 {A B : Type'} (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B P x) (h2 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975439 A B t x s P f x' h1 h2) (@lem4972783 B P x h1)). Qed.
Lemma lem4975441 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : (term708 B t x) = False.
Proof. exact (prop_ext (fun h4 : term708 B t x => @lem4975438 A B _62510 n t x s P f x' h1 h2 h3) (fun h4 : False => @lem4972574 B t x h1)). Qed.
Lemma lem4975442 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term708 B t x) (h2 : term239 A B _62510 P n f t s) (h3 : term756 A B t x s P f x') : False.
Proof. exact (EQ_MP (@lem4975441 A B _62510 n t x s P f x' h1 h2 h3) (@lem4972574 B t x h1)). Qed.
Lemma lem4975443 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term239 A B _62510 P n f t s) (h2 : term756 A B t x s P f x') : False.
Proof. exact (or_elim (@lem4972139 A B t x s P f x' h2) (fun h0 : term708 B t x => @lem4975442 A B _62510 n t x s P f x' h0 h1 h2) (fun h0 : term708 B P x => @lem4975440 A B t x s P f x' h0 h2)). Qed.
Lemma lem4975444 {A B : Type'} (x'' : B -> A) (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term649 A B t s f x'') (h2 : term239 A B _62510 P n f t s) (h3 : term699 A B t x s P f x') : False.
Proof. exact (or_elim (@lem4971751 A B t x s P f x' h3) (fun h0 : term765 A B t x s P f => @lem4974438 A B x'' t x s P f h1 h0) (fun h0 : term756 A B t x s P f x' => @lem4975443 A B _62510 n t x s P f x' h2 h0)). Qed.
Lemma lem4975445 {A B : Type'} (x'' : B -> A) (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term649 A B t s f x'') (h2 : term319 A B _62510) (h3 : term239 A B _62510 P n f t s) (h4 : term699 A B t x s P f x') : False.
Proof. exact (ex_elim (@lem4970845 A B _62510 h2) (fun x''' : type652 A B => fun h0 : term576 A B _62510 x''' => @lem4975444 A B x'' _62510 n t x s P f x' h1 h3 h4)). Qed.
Lemma lem4975446 {A B : Type'} (_62510 : type653 A B) (n : nat) (t : B -> Prop) (x : B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term239 A B _62510 P n f t s) (h4 : term699 A B t x s P f x') : False.
Proof. exact (ex_elim (@lem4971203 A B t s f h1) (fun x'' : B -> A => fun h0 : term651 A B t s f x'' => @lem4975445 A B x'' _62510 n t x s P f x' h0 h2 h3 h4)). Qed.
Lemma lem4975447 {A B : Type'} (x : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term325 A B t x s P f) (h4 : term239 A B _62510 P n f t s) : False.
Proof. exact (ex_elim (@lem4971404 A B t x s P f h3) (fun x' : A => fun h0 : term701 A B t x s P f x' => @lem4975446 A B _62510 n t x s P f x' h1 h2 h4 h0)). Qed.
Lemma lem4975448 {A B : Type'} (x : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term325 A B t x s P f) (h4 : term239 A B _62510 P n f t s) : (term325 A B t x s P f) = False.
Proof. exact (prop_ext (fun h5 : term325 A B t x s P f => @lem4975447 A B x _62510 P n f t s h1 h2 h3 h4) (fun h5 : False => @lem4970027 A B t x s P f h3)). Qed.
Lemma lem4975449 {A B : Type'} (x : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term325 A B t x s P f) (h4 : term239 A B _62510 P n f t s) : False.
Proof. exact (EQ_MP (@lem4975448 A B x _62510 P n f t s h1 h2 h3 h4) (@lem4970027 A B t x s P f h3)). Qed.
Lemma lem4975450 {A B : Type'} (x : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term239 A B _62510 P n f t s) : term324 A B t x s P f.
Proof. exact (fun h0 : term325 A B t x s P f => @lem4975449 A B x _62510 P n f t s h1 h2 h0 h3). Qed.
Lemma lem4975451 {A B : Type'} (x : B) (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term239 A B _62510 P n f t s) : (term172 B t P x) = (term192 A B x s P f).
Proof. exact (EQ_MP (@lem4970026 A B t x s P f) (@lem4975450 A B x _62510 P n f t s h1 h2 h3)). Qed.
Lemma lem4975456 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term151 A B t s f) (h2 : term319 A B _62510) (h3 : term239 A B _62510 P n f t s) : term195 A B t s P f.
Proof. exact (fun x : B => @lem4975451 A B x _62510 P n f t s h1 h2 h3). Qed.
Lemma lem4975457 {A B : Type'} (_62510 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62510) (h2 : term239 A B _62510 P n f t s) : term196 A B t s P f.
Proof. exact (fun h0 : term151 A B t s f => @lem4975456 A B _62510 P n f t s h0 h1 h2). Qed.
Lemma lem4975458 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : term319 A B _62510) : term241 A B _62510 n t s P f.
Proof. exact (fun h0 : term239 A B _62510 P n f t s => @lem4975457 A B _62510 P n f t s h1 h0). Qed.
Lemma lem4975463 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : term319 A B _62510) : term243 A B _62510 t s P f.
Proof. exact (fun n : nat => @lem4975458 A B n t s P f _62510 h1). Qed.
Lemma lem4975468 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : term319 A B _62510) : term245 A B _62510 s P f.
Proof. exact (fun t : B -> Prop => @lem4975463 A B t s P f _62510 h1). Qed.
Lemma lem4975473 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62510 : type653 A B) (h1 : term319 A B _62510) : term247 A B _62510 P f.
Proof. exact (fun s : A -> Prop => @lem4975468 A B s P f _62510 h1). Qed.
Lemma lem4975478 {A B : Type'} (f : A -> B) (_62510 : type653 A B) (h1 : term319 A B _62510) : term249 A B _62510 f.
Proof. exact (fun P : B -> Prop => @lem4975473 A B P f _62510 h1). Qed.
Lemma lem4975483 {A B : Type'} (_62510 : type653 A B) (h1 : term319 A B _62510) : term251 A B _62510.
Proof. exact (fun f : A -> B => @lem4975478 A B f _62510 h1). Qed.
Lemma lem4975484 {A B : Type'} (_62510 : type653 A B) : term321 A B _62510.
Proof. exact (fun h0 : term319 A B _62510 => @lem4975483 A B _62510 h0). Qed.
Lemma lem4975489 {A B : Type'} : term323 A B.
Proof. exact (fun _62510 : type653 A B => @lem4975484 A B _62510). Qed.
Lemma lem4975490 {A B : Type'} : term224 A B.
Proof. exact (EQ_MP (@lem4970019 A B) (@lem4975489 A B)). Qed.
Lemma lem4975491 {A B : Type'} (f : A -> B) : term933 A B f.
Proof. exact (@lem4975490 A B f). Qed.
Lemma lem4975492 {A B : Type'} (f : A -> B) : (term933 A B f) = (term220 A B f).
Proof. exact (eq_refl (term933 A B f)). Qed.
Lemma lem4975493 {A B : Type'} (f : A -> B) : term220 A B f.
Proof. exact (EQ_MP (@lem4975492 A B f) (@lem4975491 A B f)). Qed.
Lemma lem4975494 {A B : Type'} (f : A -> B) (P : B -> Prop) : term934 A B f P.
Proof. exact (@lem4975493 A B f P). Qed.
Lemma lem4975495 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term934 A B f P) = (term216 A B P f).
Proof. exact (eq_refl (term934 A B f P)). Qed.
Lemma lem4975496 {A B : Type'} (P : B -> Prop) (f : A -> B) : term216 A B P f.
Proof. exact (EQ_MP (@lem4975495 A B P f) (@lem4975494 A B f P)). Qed.
Lemma lem4975497 {A B : Type'} (P : B -> Prop) (f : A -> B) (s : A -> Prop) : term935 A B P f s.
Proof. exact (@lem4975496 A B P f s). Qed.
Lemma lem4975498 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term935 A B P f s) = (term212 A B s P f).
Proof. exact (eq_refl (term935 A B P f s)). Qed.
Lemma lem4975499 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term212 A B s P f.
Proof. exact (EQ_MP (@lem4975498 A B s P f) (@lem4975497 A B P f s)). Qed.
Lemma lem4975500 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (t : B -> Prop) : term936 A B s P f t.
Proof. exact (@lem4975499 A B s P f t). Qed.
Lemma lem4975501 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term936 A B s P f t) = (term208 A B t s P f).
Proof. exact (eq_refl (term936 A B s P f t)). Qed.
Lemma lem4975502 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term208 A B t s P f.
Proof. exact (EQ_MP (@lem4975501 A B t s P f) (@lem4975500 A B s P f t)). Qed.
Lemma lem4975503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : term937 A B t s P f n.
Proof. exact (@lem4975502 A B t s P f n). Qed.
Lemma lem4975504 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term937 A B t s P f n) = (term199 A B n t s P f).
Proof. exact (eq_refl (term937 A B t s P f n)). Qed.
Lemma lem4975505 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term199 A B n t s P f.
Proof. exact (EQ_MP (@lem4975504 A B n t s P f) (@lem4975503 A B t s P f n)). Qed.
Lemma lem4975507 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term199 A B n t s P f.
Proof. exact (@lem4969160 A B n t s P f (@lem4975505 A B n t s P f)). Qed.
Lemma lem4975508 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term200 A B n t s P f) : False.
Proof. exact (@lem4975507 A B n t s P f (@lem4969144 A B n t s P f h1)). Qed.
Lemma lem4975509 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term200 A B n t s P f) : (term200 A B n t s P f) = False.
Proof. exact (prop_ext (fun h2 : term200 A B n t s P f => @lem4975508 A B n t s P f h1) (fun h2 : False => @lem4969144 A B n t s P f h1)). Qed.
Lemma lem4975510 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term200 A B n t s P f) : False.
Proof. exact (EQ_MP (@lem4975509 A B n t s P f h1) (@lem4969144 A B n t s P f h1)). Qed.
Lemma lem4975511 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term199 A B n t s P f.
Proof. exact (fun h0 : term200 A B n t s P f => @lem4975510 A B n t s P f h0). Qed.
Lemma lem4975512 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term197 A B n t s P f.
Proof. exact (EQ_MP (@lem4969143 A B n t s P f) (@lem4975511 A B n t s P f)). Qed.
Lemma lem4975513 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term85 A B n t s P f.
Proof. exact (EQ_MP (@lem4969139 A B n t s P f) (@lem4975512 A B n t s P f)). Qed.
Lemma lem4975514 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term84 A B n t s P f.
Proof. exact (EQ_MP (@lem4968796 A B n t s P f) (@lem4975513 A B n t s P f)). Qed.
Lemma lem4975515 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term57 A B t s P f.
Proof. exact (@lem4975514 A B n t s P f (@lem4968674 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4975516 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term56 A B t s P f.
Proof. exact (EQ_MP (@lem4968659 A B P f s t h1 h2 h3 h4 h6) (@lem4975515 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4975517 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : (term26 B t P) = (term27 A B s P f).
Proof. exact (@lem4975516 A B P n f s t h1 h2 h3 h4 h5 h6 (@lem4968463 A B t s f)). Qed.
Lemma lem4975519 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term6 A B f s n.
Proof. exact (EQ_MP (@lem4968452 A B f s n) (@lem4968451 A B f s n)). Qed.
Lemma lem4975520 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term6 A B f s n.
Proof. exact (@lem4975519 A B f s n). Qed.
Lemma lem4975521 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : term938 A B s P f n.
Proof. exact (@lem4975520 A B f (term101 A B s P f) n). Qed.
Lemma lem4975536 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term24 A B s P f n) = ((term24 A B s P f n) = True).
Proof. exact (@lem7 (term24 A B s P f n)). Qed.
Lemma lem4975571 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : (term24 A B s P f n) = True.
Proof. exact (EQ_MP (@lem4975536 A B s P f n) (@lem4968473 A B s P f n h1)). Qed.
Lemma lem4975572 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : (term24 A B s P f n) = True.
Proof. exact (@lem4975571 A B s P f n h1). Qed.
Lemma lem4975573 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term939 A B s P f) = (term939 A B s P f).
Proof. exact (eq_refl (term939 A B s P f)). Qed.
Lemma lem4975574 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : (term940 A B s P f n) = (term941 A B s P f).
Proof. exact (MK_COMB (@lem4975573 A B s P f) (@lem4975572 A B s P f n h1)). Qed.
Lemma lem4975576 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4975577 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term941 A B s P f) = (term942 A B s P f).
Proof. exact (@lem4975576 (term942 A B s P f)). Qed.
Lemma lem4975608 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : (term940 A B s P f n) = (term942 A B s P f).
Proof. exact (TRANS (@lem4975574 A B s P f n h1) (@lem4975577 A B s P f)). Qed.
Lemma lem4975609 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term24 A B s P f n) : (term942 A B s P f) = (term940 A B s P f n).
Proof. exact (SYM (@lem4975608 A B s P f n h1)). Qed.
Lemma lem4975610 (t1 : Prop) : term58 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4975611 (t1 : Prop) : (term58 t1) = (term59 t1).
Proof. exact (eq_refl (term58 t1)). Qed.
Lemma lem4975612 (t1 : Prop) : term59 t1.
Proof. exact (EQ_MP (@lem4975611 t1) (@lem4975610 t1)). Qed.
Lemma lem4975613 (t1 : Prop) (t2 : Prop) : term60 t1 t2.
Proof. exact (@lem4975612 t1 t2). Qed.
Lemma lem4975614 (t1 : Prop) (t2 : Prop) : (term60 t1 t2) = (term61 t1 t2).
Proof. exact (eq_refl (term60 t1 t2)). Qed.
Lemma lem4975615 (t1 : Prop) (t2 : Prop) : term61 t1 t2.
Proof. exact (EQ_MP (@lem4975614 t1 t2) (@lem4975613 t1 t2)). Qed.
Lemma lem4975616 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term62 t1 t2 t3.
Proof. exact (@lem4975615 t1 t2 t3). Qed.
Lemma lem4975617 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term62 t1 t2 t3) = ((term63 t1 t2 t3) = (term64 t1 t2 t3)).
Proof. exact (eq_refl (term62 t1 t2 t3)). Qed.
Lemma lem4975618 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term63 t1 t2 t3) = (term64 t1 t2 t3).
Proof. exact (EQ_MP (@lem4975617 t1 t2 t3) (@lem4975616 t1 t2 t3)). Qed.
Lemma lem4975619 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term64 t1 t2 t3) = (term63 t1 t2 t3).
Proof. exact (SYM (@lem4975618 t1 t2 t3)). Qed.
Lemma lem4975620 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term65 A B t s.
Proof. exact (conj (@lem4968468 B t h2) (@lem4968466 A s h1)). Qed.
Lemma lem4975621 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term66 A B t s.
Proof. exact (conj (@lem4968470 A B s t h3) (@lem4975620 A B s t h1 h2)). Qed.
Lemma lem4975622 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : term23 A B f s t) : term67 A B f t s.
Proof. exact (conj (@lem4968472 A B f s t h4) (@lem4975621 A B s t h1 h2 h3)). Qed.
Lemma lem4975623 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : term68 A B f t s.
Proof. exact (conj (@lem4968474 A B s f h1) (@lem4975622 A B f s t h2 h3 h4 h5)). Qed.
Lemma lem4975624 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term69 A B P n f t s.
Proof. exact (conj (@lem4968473 A B s P f n h5) (@lem4975623 A B f s t h1 h2 h3 h4 h6)). Qed.
Lemma lem4975662 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term70 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4975663 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term70 B s t).
Proof. exact (@lem4975662 B s t). Qed.
Lemma lem4975664 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term23 A B f s t) = (term71 A B f s t).
Proof. exact (@lem4975663 B (@IMAGE A B f s) t). Qed.
Lemma lem4975671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975672 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term72 A B f s t) = (term73 A B f s t).
Proof. exact (MK_COMB (@lem4975671) (@lem4975664 A B f s t)). Qed.
Lemma lem4975681 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4975682 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term67 A B f t s) = (term74 A B f t s).
Proof. exact (MK_COMB (@lem4975672 A B f s t) (@lem4975681 A B t s)). Qed.
Lemma lem4975685 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term75 A B s f) = (term75 A B s f).
Proof. exact (eq_refl (term75 A B s f)). Qed.
Lemma lem4975686 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term68 A B f t s) = (term76 A B f t s).
Proof. exact (MK_COMB (@lem4975685 A B s f) (@lem4975682 A B f t s)). Qed.
Lemma lem4975689 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term77 A B s P f n) = (term77 A B s P f n).
Proof. exact (eq_refl (term77 A B s P f n)). Qed.
Lemma lem4975690 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term69 A B P n f t s) = (term78 A B P n f t s).
Proof. exact (MK_COMB (@lem4975689 A B s P f n) (@lem4975686 A B f t s)). Qed.
Lemma lem4975693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4975694 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term79 A B P n f t s) = (term80 A B P n f t s).
Proof. exact (MK_COMB (@lem4975693) (@lem4975690 A B P n f t s)). Qed.
Lemma lem4975729 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term942 A B s P f) = (term942 A B s P f).
Proof. exact (eq_refl (term942 A B s P f)). Qed.
Lemma lem4975730 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term943 A B n t s P f) = (term944 A B n t s P f).
Proof. exact (MK_COMB (@lem4975694 A B P n f t s) (@lem4975729 A B s P f)). Qed.
Lemma lem4975733 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term944 A B n t s P f) = (term943 A B n t s P f).
Proof. exact (SYM (@lem4975730 A B n t s P f)). Qed.
Lemma lem4975745 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975746 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975745 A P x). Qed.
Lemma lem4975747 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4975746 A s x). Qed.
Lemma lem4975748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975749 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4975748) (@lem4975747 A s x)). Qed.
Lemma lem4975750 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term88 A B P f x).
Proof. exact (eq_refl (term88 A B P f x)). Qed.
Lemma lem4975751 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term89 A B s P f x) = (term90 A B s P f x).
Proof. exact (MK_COMB (@lem4975749 A s x) (@lem4975750 A B P f x)). Qed.
Lemma lem4975754 {A : Type'} (GEN_PVAR_217 : A) : (@SETSPEC A GEN_PVAR_217) = (@SETSPEC A GEN_PVAR_217).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_217)). Qed.
Lemma lem4975755 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term91 A B GEN_PVAR_217 s P f x) = (term92 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4975754 A GEN_PVAR_217) (@lem4975751 A B s P f x)). Qed.
Lemma lem4975756 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4975757 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term93 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4975755 A B GEN_PVAR_217 s P f x) (@lem4975756 A x)). Qed.
Lemma lem4975758 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term95 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4975757 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4975759 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4975760 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term97 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4975759 A) (@lem4975758 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4975765 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term99 A B s P f) = (term100 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4975760 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4975766 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4975767 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term101 A B s P f) = (term102 A B s P f).
Proof. exact (MK_COMB (@lem4975766 A) (@lem4975765 A B s P f)). Qed.
Lemma lem4975768 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4975769 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term103 A B s P f) = (term104 A B s P f).
Proof. exact (MK_COMB (@lem4975768 A) (@lem4975767 A B s P f)). Qed.
Lemma lem4975770 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4975771 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term24 A B s P f n) = (term105 A B s P f n).
Proof. exact (MK_COMB (@lem4975769 A B s P f) (@lem4975770 n)). Qed.
Lemma lem4975772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975773 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term77 A B s P f n) = (term106 A B s P f n).
Proof. exact (MK_COMB (@lem4975772) (@lem4975771 A B s P f n)). Qed.
Lemma lem4975789 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975790 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975789 A P x). Qed.
Lemma lem4975791 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4975790 A s x). Qed.
Lemma lem4975792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975793 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4975792) (@lem4975791 A s x)). Qed.
Lemma lem4975797 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975798 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975797 A P x). Qed.
Lemma lem4975799 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4975798 A s y). Qed.
Lemma lem4975800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975801 {A : Type'} (s : A -> Prop) (y : A) : (term86 A y s) = (term87 A s y).
Proof. exact (MK_COMB (@lem4975800) (@lem4975799 A s y)). Qed.
Lemma lem4975804 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem4975805 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term107 A B s x f y) = (term108 A B s x f y).
Proof. exact (MK_COMB (@lem4975801 A s y) (@lem4975804 A B x f y)). Qed.
Lemma lem4975808 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term109 A B s x f y) = (term110 A B s x f y).
Proof. exact (MK_COMB (@lem4975793 A s x) (@lem4975805 A B s x f y)). Qed.
Lemma lem4975811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4975812 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term111 A B s x f y) = (term112 A B s x f y).
Proof. exact (MK_COMB (@lem4975811) (@lem4975808 A B s x f y)). Qed.
Lemma lem4975815 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4975816 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term38 A B s f x y) = (term113 A B s f x y).
Proof. exact (MK_COMB (@lem4975812 A B s x f y) (@lem4975815 A x y)). Qed.
Lemma lem4975819 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term46 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4975816 A B s f x y)). Qed.
Lemma lem4975820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4975821 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term36 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4975820 A) (@lem4975819 A B s f x)). Qed.
Lemma lem4975826 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4975821 A B s f x)). Qed.
Lemma lem4975827 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4975828 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term25 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4975827 A) (@lem4975826 A B s f)). Qed.
Lemma lem4975833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975834 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term75 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4975833) (@lem4975828 A B s f)). Qed.
Lemma lem4975844 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4975845 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term119 A B y f s) = (term120 A B y f s).
Proof. exact (@lem4975844 A B y f s). Qed.
Lemma lem4975846 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term120 A B x f s).
Proof. exact (@lem4975845 A B x f s). Qed.
Lemma lem4975856 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975856 A P x). Qed.
Lemma lem4975858 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4975857 A s x). Qed.
Lemma lem4975859 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term121 A B x f x') = (term121 A B x f x').
Proof. exact (eq_refl (term121 A B x f x')). Qed.
Lemma lem4975860 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term122 A B x f x' s) = (term123 A B x f s x').
Proof. exact (MK_COMB (@lem4975859 A B x f x') (@lem4975858 A s x')). Qed.
Lemma lem4975863 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4975860 A B x f s x')). Qed.
Lemma lem4975864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4975865 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4975864 A) (@lem4975863 A B x f s)). Qed.
Lemma lem4975870 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term126 A B x f s).
Proof. exact (TRANS (@lem4975846 A B x f s) (@lem4975865 A B x f s)). Qed.
Lemma lem4975871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4975872 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4975871) (@lem4975870 A B x f s)). Qed.
Lemma lem4975874 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975875 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4975874 B P x). Qed.
Lemma lem4975876 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4975875 B t x). Qed.
Lemma lem4975877 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term129 A B f s x t) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4975872 A B x f s) (@lem4975876 B t x)). Qed.
Lemma lem4975880 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term131 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4975877 A B f s t x)). Qed.
Lemma lem4975881 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4975882 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term71 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4975881 B) (@lem4975880 A B f s t)). Qed.
Lemma lem4975887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975888 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term73 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4975887) (@lem4975882 A B f s t)). Qed.
Lemma lem4975895 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4975896 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term74 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4975888 A B f s t) (@lem4975895 A B t s)). Qed.
Lemma lem4975899 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term76 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4975834 A B s f) (@lem4975896 A B f t s)). Qed.
Lemma lem4975902 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term78 A B P n f t s) = (term137 A B P n f t s).
Proof. exact (MK_COMB (@lem4975773 A B s P f n) (@lem4975899 A B f t s)). Qed.
Lemma lem4975905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4975906 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term80 A B P n f t s) = (term138 A B P n f t s).
Proof. exact (MK_COMB (@lem4975905) (@lem4975902 A B P n f t s)). Qed.
Lemma lem4975920 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term153 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4975921 {A : Type'} (p : A -> Prop) (x : A) : (term153 A x p) = (p x).
Proof. exact (@lem4975920 A p x). Qed.
Lemma lem4975922 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term176 A B x s P f) = (term177 A B s P f x).
Proof. exact (@lem4975921 A (term178 A B s P f) x). Qed.
Lemma lem4975923 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term177 A B s P f x) = (term89 A B s P f x).
Proof. exact (eq_refl (term177 A B s P f x)). Qed.
Lemma lem4975924 {A : Type'} (GEN_PVAR_216 : A) : (@SETSPEC A GEN_PVAR_216) = (@SETSPEC A GEN_PVAR_216).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_216)). Qed.
Lemma lem4975925 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term179 A B GEN_PVAR_216 s P f x) = (term91 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4975924 A GEN_PVAR_216) (@lem4975923 A B s P f x)). Qed.
Lemma lem4975926 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4975927 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term180 A B GEN_PVAR_216 s P f x) = (term93 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4975925 A B GEN_PVAR_216 s P f x) (@lem4975926 A x)). Qed.
Lemma lem4975928 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term181 A B GEN_PVAR_216 s P f) = (term95 A B GEN_PVAR_216 s P f).
Proof. exact (fun_ext (fun x : A => @lem4975927 A B GEN_PVAR_216 s P f x)). Qed.
Lemma lem4975929 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4975930 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term182 A B GEN_PVAR_216 s P f) = (term97 A B GEN_PVAR_216 s P f).
Proof. exact (MK_COMB (@lem4975929 A) (@lem4975928 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4975931 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term183 A B s P f) = (term99 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_216 : A => @lem4975930 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4975932 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4975933 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term184 A B s P f) = (term101 A B s P f).
Proof. exact (MK_COMB (@lem4975932 A) (@lem4975931 A B s P f)). Qed.
Lemma lem4975934 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4975935 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term176 A B x s P f) = (term185 A B x s P f).
Proof. exact (MK_COMB (@lem4975934 A x) (@lem4975933 A B s P f)). Qed.
Lemma lem4975936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4975937 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term186 A B x s P f) = (term187 A B x s P f).
Proof. exact (MK_COMB (@lem4975936) (@lem4975935 A B x s P f)). Qed.
Lemma lem4975938 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term177 A B s P f x) = (term89 A B s P f x).
Proof. exact (eq_refl (term177 A B s P f x)). Qed.
Lemma lem4975939 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : ((term176 A B x s P f) = (term177 A B s P f x)) = ((term185 A B x s P f) = (term89 A B s P f x)).
Proof. exact (MK_COMB (@lem4975937 A B x s P f) (@lem4975938 A B s P f x)). Qed.
Lemma lem4975940 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term185 A B x s P f) = (term89 A B s P f x).
Proof. exact (EQ_MP (@lem4975939 A B s P f x) (@lem4975922 A B s P f x)). Qed.
Lemma lem4975944 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975945 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975944 A P x). Qed.
Lemma lem4975946 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4975945 A s x). Qed.
Lemma lem4975947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975948 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term87 A s x).
Proof. exact (MK_COMB (@lem4975947) (@lem4975946 A s x)). Qed.
Lemma lem4975949 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term88 A B P f x).
Proof. exact (eq_refl (term88 A B P f x)). Qed.
Lemma lem4975950 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term89 A B s P f x) = (term90 A B s P f x).
Proof. exact (MK_COMB (@lem4975948 A s x) (@lem4975949 A B P f x)). Qed.
Lemma lem4975953 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term185 A B x s P f) = (term90 A B s P f x).
Proof. exact (TRANS (@lem4975940 A B s P f x) (@lem4975950 A B s P f x)). Qed.
Lemma lem4975954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975955 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term945 A B x s P f) = (term946 A B s P f x).
Proof. exact (MK_COMB (@lem4975954) (@lem4975953 A B s P f x)). Qed.
Lemma lem4975959 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term153 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4975960 {A : Type'} (p : A -> Prop) (x : A) : (term153 A x p) = (p x).
Proof. exact (@lem4975959 A p x). Qed.
Lemma lem4975961 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term176 A B y s P f) = (term177 A B s P f y).
Proof. exact (@lem4975960 A (term178 A B s P f) y). Qed.
Lemma lem4975962 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term177 A B s P f x) = (term89 A B s P f x).
Proof. exact (eq_refl (term177 A B s P f x)). Qed.
Lemma lem4975963 {A : Type'} (GEN_PVAR_216 : A) : (@SETSPEC A GEN_PVAR_216) = (@SETSPEC A GEN_PVAR_216).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_216)). Qed.
Lemma lem4975964 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term179 A B GEN_PVAR_216 s P f x) = (term91 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4975963 A GEN_PVAR_216) (@lem4975962 A B s P f x)). Qed.
Lemma lem4975965 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4975966 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term180 A B GEN_PVAR_216 s P f x) = (term93 A B GEN_PVAR_216 s P f x).
Proof. exact (MK_COMB (@lem4975964 A B GEN_PVAR_216 s P f x) (@lem4975965 A x)). Qed.
Lemma lem4975967 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term181 A B GEN_PVAR_216 s P f) = (term95 A B GEN_PVAR_216 s P f).
Proof. exact (fun_ext (fun x : A => @lem4975966 A B GEN_PVAR_216 s P f x)). Qed.
Lemma lem4975968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4975969 {A B : Type'} (GEN_PVAR_216 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term182 A B GEN_PVAR_216 s P f) = (term97 A B GEN_PVAR_216 s P f).
Proof. exact (MK_COMB (@lem4975968 A) (@lem4975967 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4975970 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term183 A B s P f) = (term99 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_216 : A => @lem4975969 A B GEN_PVAR_216 s P f)). Qed.
Lemma lem4975971 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4975972 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term184 A B s P f) = (term101 A B s P f).
Proof. exact (MK_COMB (@lem4975971 A) (@lem4975970 A B s P f)). Qed.
Lemma lem4975973 {A : Type'} (y : A) : (@IN A y) = (@IN A y).
Proof. exact (eq_refl (@IN A y)). Qed.
Lemma lem4975974 {A B : Type'} (y : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term176 A B y s P f) = (term185 A B y s P f).
Proof. exact (MK_COMB (@lem4975973 A y) (@lem4975972 A B s P f)). Qed.
Lemma lem4975975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4975976 {A B : Type'} (y : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term186 A B y s P f) = (term187 A B y s P f).
Proof. exact (MK_COMB (@lem4975975) (@lem4975974 A B y s P f)). Qed.
Lemma lem4975977 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term177 A B s P f y) = (term89 A B s P f y).
Proof. exact (eq_refl (term177 A B s P f y)). Qed.
Lemma lem4975978 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : ((term176 A B y s P f) = (term177 A B s P f y)) = ((term185 A B y s P f) = (term89 A B s P f y)).
Proof. exact (MK_COMB (@lem4975976 A B y s P f) (@lem4975977 A B s P f y)). Qed.
Lemma lem4975979 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term185 A B y s P f) = (term89 A B s P f y).
Proof. exact (EQ_MP (@lem4975978 A B s P f y) (@lem4975961 A B s P f y)). Qed.
Lemma lem4975983 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4975984 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4975983 A P x). Qed.
Lemma lem4975985 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4975984 A s y). Qed.
Lemma lem4975986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975987 {A : Type'} (s : A -> Prop) (y : A) : (term86 A y s) = (term87 A s y).
Proof. exact (MK_COMB (@lem4975986) (@lem4975985 A s y)). Qed.
Lemma lem4975988 {A B : Type'} (P : B -> Prop) (f : A -> B) (y : A) : (term88 A B P f y) = (term88 A B P f y).
Proof. exact (eq_refl (term88 A B P f y)). Qed.
Lemma lem4975989 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term89 A B s P f y) = (term90 A B s P f y).
Proof. exact (MK_COMB (@lem4975987 A s y) (@lem4975988 A B P f y)). Qed.
Lemma lem4975992 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term185 A B y s P f) = (term90 A B s P f y).
Proof. exact (TRANS (@lem4975979 A B s P f y) (@lem4975989 A B s P f y)). Qed.
Lemma lem4975993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4975994 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term945 A B y s P f) = (term946 A B s P f y).
Proof. exact (MK_COMB (@lem4975993) (@lem4975992 A B s P f y)). Qed.
Lemma lem4975997 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem4975998 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) : (term947 A B s P x f y) = (term948 A B s P x f y).
Proof. exact (MK_COMB (@lem4975994 A B s P f y) (@lem4975997 A B x f y)). Qed.
Lemma lem4976001 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) : (term949 A B s P x f y) = (term950 A B s P x f y).
Proof. exact (MK_COMB (@lem4975955 A B s P f x) (@lem4975998 A B s P x f y)). Qed.
Lemma lem4976004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976005 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) : (term951 A B s P x f y) = (term952 A B s P x f y).
Proof. exact (MK_COMB (@lem4976004) (@lem4976001 A B s P x f y)). Qed.
Lemma lem4976008 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4976009 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (y : A) : (term953 A B s P f x y) = (term954 A B s P f x y).
Proof. exact (MK_COMB (@lem4976005 A B s P x f y) (@lem4976008 A x y)). Qed.
Lemma lem4976012 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term955 A B s P f x) = (term956 A B s P f x).
Proof. exact (fun_ext (fun y : A => @lem4976009 A B s P f x y)). Qed.
Lemma lem4976013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976014 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term957 A B s P f x) = (term958 A B s P f x).
Proof. exact (MK_COMB (@lem4976013 A) (@lem4976012 A B s P f x)). Qed.
Lemma lem4976019 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term959 A B s P f) = (term960 A B s P f).
Proof. exact (fun_ext (fun x : A => @lem4976014 A B s P f x)). Qed.
Lemma lem4976020 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976021 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term942 A B s P f) = (term961 A B s P f).
Proof. exact (MK_COMB (@lem4976020 A) (@lem4976019 A B s P f)). Qed.
Lemma lem4976026 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term944 A B n t s P f) = (term962 A B n t s P f).
Proof. exact (MK_COMB (@lem4975906 A B P n f t s) (@lem4976021 A B s P f)). Qed.
Lemma lem4976029 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term962 A B n t s P f) = (term944 A B n t s P f).
Proof. exact (SYM (@lem4976026 A B n t s P f)). Qed.
Lemma lem4976031 (p : Prop) : p = (term198 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4976032 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term962 A B n t s P f) = (term963 A B n t s P f).
Proof. exact (@lem4976031 (term962 A B n t s P f)). Qed.
Lemma lem4976033 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term963 A B n t s P f) = (term962 A B n t s P f).
Proof. exact (SYM (@lem4976032 A B n t s P f)). Qed.
Lemma lem4976034 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term964 A B n t s P f) : term964 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4976037 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term963 A B n t s P f) : term963 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4976038 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term965 A B n t s P f.
Proof. exact (fun h0 : term963 A B n t s P f => @lem4976037 A B n t s P f h0). Qed.
Lemma lem4976039 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term965 A B n t s P f) : term965 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4976040 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term963 A B n t s P f) : term963 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4976041 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term963 A B n t s P f) (h2 : term965 A B n t s P f) : term963 A B n t s P f.
Proof. exact (@lem4976039 A B n t s P f h2 (@lem4976040 A B n t s P f h1)). Qed.
Lemma lem4976042 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term963 A B n t s P f) : term966 A B n t s P f.
Proof. exact (fun h0 : term965 A B n t s P f => @lem4976041 A B n t s P f h1 h0). Qed.
Lemma lem4976043 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term965 A B n t s P f) : term965 A B n t s P f.
Proof. exact (h1). Qed.
Lemma lem4976044 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term963 A B n t s P f) (h2 : term965 A B n t s P f) : term963 A B n t s P f.
Proof. exact (@lem4976042 A B n t s P f h1 (@lem4976043 A B n t s P f h2)). Qed.
Lemma lem4976045 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term965 A B n t s P f) : term965 A B n t s P f.
Proof. exact (fun h0 : term963 A B n t s P f => @lem4976044 A B n t s P f h0 h1). Qed.
Lemma lem4976046 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term967 A B n t s P f.
Proof. exact (fun h0 : term965 A B n t s P f => @lem4976045 A B n t s P f h0). Qed.
Lemma lem4976049 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term965 A B n t s P f.
Proof. exact (@lem4976046 A B n t s P f (@lem4976038 A B n t s P f)). Qed.
Lemma lem4976050 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term965 A B n t s P f.
Proof. exact (@lem4976049 A B n t s P f). Qed.
Lemma lem4976072 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4976073 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term963 A B n t s P f) = (term968 A B n t s P f).
Proof. exact (@lem4976072 (term964 A B n t s P f)). Qed.
Lemma lem4976075 (t : Prop) : (term205 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4976076 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term968 A B n t s P f) = (term962 A B n t s P f).
Proof. exact (@lem4976075 (term962 A B n t s P f)). Qed.
Lemma lem4976079 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term963 A B n t s P f) = (term962 A B n t s P f).
Proof. exact (TRANS (@lem4976073 A B n t s P f) (@lem4976076 A B n t s P f)). Qed.
Lemma lem4976168 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term969 A B t s P f) = (term970 A B t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4976079 A B n t s P f)). Qed.
Lemma lem4976169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4976170 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term971 A B t s P f) = (term972 A B t s P f).
Proof. exact (MK_COMB (@lem4976169) (@lem4976168 A B t s P f)). Qed.
Lemma lem4976175 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term973 A B s P f) = (term974 A B s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4976170 A B t s P f)). Qed.
Lemma lem4976176 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976177 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term975 A B s P f) = (term976 A B s P f).
Proof. exact (MK_COMB (@lem4976176 B) (@lem4976175 A B s P f)). Qed.
Lemma lem4976182 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term977 A B P f) = (term978 A B P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976177 A B s P f)). Qed.
Lemma lem4976183 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976184 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term979 A B P f) = (term980 A B P f).
Proof. exact (MK_COMB (@lem4976183 A) (@lem4976182 A B P f)). Qed.
Lemma lem4976189 {A B : Type'} (f : A -> B) : (term981 A B f) = (term982 A B f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976184 A B P f)). Qed.
Lemma lem4976190 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976191 {A B : Type'} (f : A -> B) : (term983 A B f) = (term984 A B f).
Proof. exact (MK_COMB (@lem4976190 B) (@lem4976189 A B f)). Qed.
Lemma lem4976196 {A B : Type'} : (term985 A B) = (term986 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4976191 A B f)). Qed.
Lemma lem4976197 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976204 {A B : Type'} : (term987 A B) = (term988 A B).
Proof. exact (MK_COMB (@lem4976197 A B) (@lem4976196 A B)). Qed.
Lemma lem4976205 {A B : Type'} (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : _62886 = (term226 A B).
Proof. exact (h1). Qed.
Lemma lem4976206 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4976207 {A B : Type'} (s : A -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s) = (term227 A B s).
Proof. exact (MK_COMB (@lem4976205 A B _62886 h1) (@lem4976206 A s)). Qed.
Lemma lem4976208 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4976209 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term229 A B _62886 s) = (term229 A B _62886 s).
Proof. exact (eq_refl (term229 A B _62886 s)). Qed.
Lemma lem4976210 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term227 A B s)) = ((_62886 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4976209 A B _62886 s) (@lem4976208 A B s)). Qed.
Lemma lem4976211 {A B : Type'} (s : A -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s) = (term228 A B s).
Proof. exact (EQ_MP (@lem4976210 A B _62886 s) (@lem4976207 A B s _62886 h1)). Qed.
Lemma lem4976212 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4976213 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s P) = (term230 A B s P).
Proof. exact (MK_COMB (@lem4976211 A B s _62886 h1) (@lem4976212 B P)). Qed.
Lemma lem4976214 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4976215 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62886 s P) = (term232 A B _62886 s P).
Proof. exact (eq_refl (term232 A B _62886 s P)). Qed.
Lemma lem4976216 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term230 A B s P)) = ((_62886 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4976215 A B _62886 s P) (@lem4976214 A B s P)). Qed.
Lemma lem4976217 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s P) = (term231 A B s P).
Proof. exact (EQ_MP (@lem4976216 A B _62886 s P) (@lem4976213 A B s P _62886 h1)). Qed.
Lemma lem4976218 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4976219 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s P f) = (term233 A B s P f).
Proof. exact (MK_COMB (@lem4976217 A B s P _62886 h1) (@lem4976218 A B f)). Qed.
Lemma lem4976220 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4976221 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62886 s P f) = (term234 A B _62886 s P f).
Proof. exact (eq_refl (term234 A B _62886 s P f)). Qed.
Lemma lem4976222 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term233 A B s P f)) = ((_62886 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4976221 A B _62886 s P f) (@lem4976220 A B s P f)). Qed.
Lemma lem4976223 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (_62886 s P f) = (term100 A B s P f).
Proof. exact (EQ_MP (@lem4976222 A B _62886 s P f) (@lem4976219 A B s P f _62886 h1)). Qed.
Lemma lem4976269 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (y : A) : (term954 A B s P f x y) = (term954 A B s P f x y).
Proof. exact (eq_refl (term954 A B s P f x y)). Qed.
Lemma lem4976270 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term956 A B s P f x) = (term956 A B s P f x).
Proof. exact (fun_ext (fun y : A => @lem4976269 A B s P f x y)). Qed.
Lemma lem4976271 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976272 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term958 A B s P f x) = (term958 A B s P f x).
Proof. exact (MK_COMB (@lem4976271 A) (@lem4976270 A B s P f x)). Qed.
Lemma lem4976273 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term960 A B s P f) = (term960 A B s P f).
Proof. exact (fun_ext (fun x : A => @lem4976272 A B s P f x)). Qed.
Lemma lem4976274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976275 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term961 A B s P f) = (term961 A B s P f).
Proof. exact (MK_COMB (@lem4976274 A) (@lem4976273 A B s P f)). Qed.
Lemma lem4976296 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4976299 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4976312 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term123 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term123 A B x f s x')). Qed.
Lemma lem4976313 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4976312 A B x f s x')). Qed.
Lemma lem4976314 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4976315 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4976314 A) (@lem4976313 A B x f s)). Qed.
Lemma lem4976316 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976317 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4976316) (@lem4976315 A B x f s)). Qed.
Lemma lem4976318 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4976317 A B x f s) (@lem4976299 B t x)). Qed.
Lemma lem4976319 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4976318 A B f s t x)). Qed.
Lemma lem4976320 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4976321 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4976320 B) (@lem4976319 A B f s t)). Qed.
Lemma lem4976322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976323 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4976322) (@lem4976321 A B f s t)). Qed.
Lemma lem4976324 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4976323 A B f s t) (@lem4976296 A B t s)). Qed.
Lemma lem4976353 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term113 A B s f x y).
Proof. exact (eq_refl (term113 A B s f x y)). Qed.
Lemma lem4976354 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4976353 A B s f x y)). Qed.
Lemma lem4976355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976356 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4976355 A) (@lem4976354 A B s f x)). Qed.
Lemma lem4976357 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4976356 A B s f x)). Qed.
Lemma lem4976358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976359 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4976358 A) (@lem4976357 A B s f)). Qed.
Lemma lem4976360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976361 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4976360) (@lem4976359 A B s f)). Qed.
Lemma lem4976362 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4976361 A B s f) (@lem4976324 A B f t s)). Qed.
Lemma lem4976363 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4976365 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term100 A B s P f) = (_62886 s P f).
Proof. exact (SYM (@lem4976223 A B s P f _62886 h1)). Qed.
Lemma lem4976366 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term100 A B s P f) = (_62886 s P f).
Proof. exact (@lem4976365 A B s P f _62886 h1). Qed.
Lemma lem4976367 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4976368 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term102 A B s P f) = (term235 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976367 A) (@lem4976366 A B s P f _62886 h1)). Qed.
Lemma lem4976369 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4976370 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term104 A B s P f) = (term236 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976369 A) (@lem4976368 A B s P f _62886 h1)). Qed.
Lemma lem4976371 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term105 A B s P f n) = (term237 A B _62886 s P f n).
Proof. exact (MK_COMB (@lem4976370 A B s P f _62886 h1) (@lem4976363 n)). Qed.
Lemma lem4976372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976373 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term106 A B s P f n) = (term238 A B _62886 s P f n).
Proof. exact (MK_COMB (@lem4976372) (@lem4976371 A B s P f n _62886 h1)). Qed.
Lemma lem4976374 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term137 A B P n f t s) = (term239 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4976373 A B s P f n _62886 h1) (@lem4976362 A B f t s)). Qed.
Lemma lem4976375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976376 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term138 A B P n f t s) = (term240 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4976375) (@lem4976374 A B P n f t s _62886 h1)). Qed.
Lemma lem4976377 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term962 A B n t s P f) = (term989 A B _62886 n t s P f).
Proof. exact (MK_COMB (@lem4976376 A B P n f t s _62886 h1) (@lem4976275 A B s P f)). Qed.
Lemma lem4976378 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term970 A B t s P f) = (term990 A B _62886 t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4976377 A B n t s P f _62886 h1)). Qed.
Lemma lem4976379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4976380 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term972 A B t s P f) = (term991 A B _62886 t s P f).
Proof. exact (MK_COMB (@lem4976379) (@lem4976378 A B t s P f _62886 h1)). Qed.
Lemma lem4976381 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term974 A B s P f) = (term992 A B _62886 s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4976380 A B t s P f _62886 h1)). Qed.
Lemma lem4976382 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976383 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term976 A B s P f) = (term993 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976382 B) (@lem4976381 A B s P f _62886 h1)). Qed.
Lemma lem4976384 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term978 A B P f) = (term994 A B _62886 P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976383 A B s P f _62886 h1)). Qed.
Lemma lem4976385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976386 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term980 A B P f) = (term995 A B _62886 P f).
Proof. exact (MK_COMB (@lem4976385 A) (@lem4976384 A B P f _62886 h1)). Qed.
Lemma lem4976387 {A B : Type'} (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term982 A B f) = (term996 A B _62886 f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976386 A B P f _62886 h1)). Qed.
Lemma lem4976388 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976389 {A B : Type'} (f : A -> B) (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term984 A B f) = (term997 A B _62886 f).
Proof. exact (MK_COMB (@lem4976388 B) (@lem4976387 A B f _62886 h1)). Qed.
Lemma lem4976390 {A B : Type'} (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term986 A B) = (term998 A B _62886).
Proof. exact (fun_ext (fun f : A -> B => @lem4976389 A B f _62886 h1)). Qed.
Lemma lem4976391 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976392 {A B : Type'} (_62886 : type653 A B) (h1 : _62886 = (term226 A B)) : (term988 A B) = (term999 A B _62886).
Proof. exact (MK_COMB (@lem4976391 A B) (@lem4976390 A B _62886 h1)). Qed.
Lemma lem4976393 {A B : Type'} (_62886 : type653 A B) : term1000 A B _62886.
Proof. exact (fun h0 : _62886 = (term226 A B) => @lem4976392 A B _62886 h0). Qed.
Lemma lem4976394 {A B : Type'} : term1001 A B.
Proof. exact (fun _62886 : type653 A B => @lem4976393 A B _62886). Qed.
Lemma lem4976396 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term254 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4976397 {A B : Type'} (P : Prop) (c : type653 A B) (Q : type145 A B) : term255 A B P c Q.
Proof. exact (@lem4976396 (type653 A B) P c Q). Qed.
Lemma lem4976398 {A B : Type'} : term1002 A B.
Proof. exact (@lem4976397 A B (term988 A B) (term226 A B) (term1003 A B)). Qed.
Lemma lem4976399 {A B : Type'} (_62886 : type653 A B) : (term1004 A B _62886) = (term999 A B _62886).
Proof. exact (eq_refl (term1004 A B _62886)). Qed.
Lemma lem4976400 {A B : Type'} : (term1005 A B) = (term1005 A B).
Proof. exact (eq_refl (term1005 A B)). Qed.
Lemma lem4976401 {A B : Type'} (_62886 : type653 A B) : ((term988 A B) = (term1004 A B _62886)) = ((term988 A B) = (term999 A B _62886)).
Proof. exact (MK_COMB (@lem4976400 A B) (@lem4976399 A B _62886)). Qed.
Lemma lem4976402 {A B : Type'} (_62886 : type653 A B) : (term260 A B _62886) = (term260 A B _62886).
Proof. exact (eq_refl (term260 A B _62886)). Qed.
Lemma lem4976403 {A B : Type'} (_62886 : type653 A B) : (term1006 A B _62886) = (term1000 A B _62886).
Proof. exact (MK_COMB (@lem4976402 A B _62886) (@lem4976401 A B _62886)). Qed.
Lemma lem4976404 {A B : Type'} : (term1007 A B) = (term1008 A B).
Proof. exact (fun_ext (fun _62886 : type653 A B => @lem4976403 A B _62886)). Qed.
Lemma lem4976405 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4976406 {A B : Type'} : (term1009 A B) = (term1001 A B).
Proof. exact (MK_COMB (@lem4976405 A B) (@lem4976404 A B)). Qed.
Lemma lem4976407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976408 {A B : Type'} : (term1010 A B) = (term1011 A B).
Proof. exact (MK_COMB (@lem4976407) (@lem4976406 A B)). Qed.
Lemma lem4976409 {A B : Type'} (_62886 : type653 A B) : (term1004 A B _62886) = (term999 A B _62886).
Proof. exact (eq_refl (term1004 A B _62886)). Qed.
Lemma lem4976410 {A B : Type'} (_62886 : type653 A B) : (term260 A B _62886) = (term260 A B _62886).
Proof. exact (eq_refl (term260 A B _62886)). Qed.
Lemma lem4976411 {A B : Type'} (_62886 : type653 A B) : (term1012 A B _62886) = (term1013 A B _62886).
Proof. exact (MK_COMB (@lem4976410 A B _62886) (@lem4976409 A B _62886)). Qed.
Lemma lem4976412 {A B : Type'} : (term1014 A B) = (term1015 A B).
Proof. exact (fun_ext (fun _62886 : type653 A B => @lem4976411 A B _62886)). Qed.
Lemma lem4976413 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4976414 {A B : Type'} : (term1016 A B) = (term1017 A B).
Proof. exact (MK_COMB (@lem4976413 A B) (@lem4976412 A B)). Qed.
Lemma lem4976415 {A B : Type'} : (term1005 A B) = (term1005 A B).
Proof. exact (eq_refl (term1005 A B)). Qed.
Lemma lem4976416 {A B : Type'} : ((term988 A B) = (term1016 A B)) = ((term988 A B) = (term1017 A B)).
Proof. exact (MK_COMB (@lem4976415 A B) (@lem4976414 A B)). Qed.
Lemma lem4976417 {A B : Type'} : (term1002 A B) = (term1018 A B).
Proof. exact (MK_COMB (@lem4976408 A B) (@lem4976416 A B)). Qed.
Lemma lem4976418 {A B : Type'} : term1018 A B.
Proof. exact (EQ_MP (@lem4976417 A B) (@lem4976398 A B)). Qed.
Lemma lem4976419 {A B : Type'} : (term988 A B) = (term1017 A B).
Proof. exact (@lem4976418 A B (@lem4976394 A B)). Qed.
Lemma lem4976421 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4976422 {A B : Type'} (s : type653 A B) (t : type653 A B) : (s = (term276 A B t)) = (term277 A B s t).
Proof. exact (@lem4976421 (type832 A B) (A -> Prop) s t). Qed.
Lemma lem4976423 {A B : Type'} (_62886 : type653 A B) : (_62886 = (term278 A B)) = (term279 A B _62886).
Proof. exact (@lem4976422 A B _62886 (term226 A B)). Qed.
Lemma lem4976424 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4976425 {A B : Type'} : (term278 A B) = (term226 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976424 A B s)). Qed.
Lemma lem4976426 {A B : Type'} (_62886 : type653 A B) : (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886) = (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886)). Qed.
Lemma lem4976427 {A B : Type'} (_62886 : type653 A B) : (_62886 = (term278 A B)) = (_62886 = (term226 A B)).
Proof. exact (MK_COMB (@lem4976426 A B _62886) (@lem4976425 A B)). Qed.
Lemma lem4976428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976429 {A B : Type'} (_62886 : type653 A B) : (term280 A B _62886) = (term281 A B _62886).
Proof. exact (MK_COMB (@lem4976428) (@lem4976427 A B _62886)). Qed.
Lemma lem4976430 {A B : Type'} (s : A -> Prop) : (term227 A B s) = (term228 A B s).
Proof. exact (eq_refl (term227 A B s)). Qed.
Lemma lem4976431 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term229 A B _62886 s) = (term229 A B _62886 s).
Proof. exact (eq_refl (term229 A B _62886 s)). Qed.
Lemma lem4976432 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term227 A B s)) = ((_62886 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4976431 A B _62886 s) (@lem4976430 A B s)). Qed.
Lemma lem4976433 {A B : Type'} (_62886 : type653 A B) : (term282 A B _62886) = (term283 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976432 A B _62886 s)). Qed.
Lemma lem4976434 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976435 {A B : Type'} (_62886 : type653 A B) : (term279 A B _62886) = (term284 A B _62886).
Proof. exact (MK_COMB (@lem4976434 A) (@lem4976433 A B _62886)). Qed.
Lemma lem4976436 {A B : Type'} (_62886 : type653 A B) : ((_62886 = (term278 A B)) = (term279 A B _62886)) = ((_62886 = (term226 A B)) = (term284 A B _62886)).
Proof. exact (MK_COMB (@lem4976429 A B _62886) (@lem4976435 A B _62886)). Qed.
Lemma lem4976437 {A B : Type'} (_62886 : type653 A B) : (_62886 = (term226 A B)) = (term284 A B _62886).
Proof. exact (EQ_MP (@lem4976436 A B _62886) (@lem4976423 A B _62886)). Qed.
Lemma lem4976439 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4976440 {A B : Type'} (s : type832 A B) (t : type832 A B) : (s = (term285 A B t)) = (term286 A B s t).
Proof. exact (@lem4976439 (type551 A B) (B -> Prop) s t). Qed.
Lemma lem4976441 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term287 A B s)) = (term288 A B _62886 s).
Proof. exact (@lem4976440 A B (_62886 s) (term228 A B s)). Qed.
Lemma lem4976442 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4976443 {A B : Type'} (s : A -> Prop) : (term287 A B s) = (term228 A B s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976442 A B s P)). Qed.
Lemma lem4976444 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term229 A B _62886 s) = (term229 A B _62886 s).
Proof. exact (eq_refl (term229 A B _62886 s)). Qed.
Lemma lem4976445 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term287 A B s)) = ((_62886 s) = (term228 A B s)).
Proof. exact (MK_COMB (@lem4976444 A B _62886 s) (@lem4976443 A B s)). Qed.
Lemma lem4976446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976447 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term289 A B _62886 s) = (term290 A B _62886 s).
Proof. exact (MK_COMB (@lem4976446) (@lem4976445 A B _62886 s)). Qed.
Lemma lem4976448 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term230 A B s P) = (term231 A B s P).
Proof. exact (eq_refl (term230 A B s P)). Qed.
Lemma lem4976449 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62886 s P) = (term232 A B _62886 s P).
Proof. exact (eq_refl (term232 A B _62886 s P)). Qed.
Lemma lem4976450 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term230 A B s P)) = ((_62886 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4976449 A B _62886 s P) (@lem4976448 A B s P)). Qed.
Lemma lem4976451 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term291 A B _62886 s) = (term292 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976450 A B _62886 s P)). Qed.
Lemma lem4976452 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976453 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term288 A B _62886 s) = (term293 A B _62886 s).
Proof. exact (MK_COMB (@lem4976452 B) (@lem4976451 A B _62886 s)). Qed.
Lemma lem4976454 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (((_62886 s) = (term287 A B s)) = (term288 A B _62886 s)) = (((_62886 s) = (term228 A B s)) = (term293 A B _62886 s)).
Proof. exact (MK_COMB (@lem4976447 A B _62886 s) (@lem4976453 A B _62886 s)). Qed.
Lemma lem4976455 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term228 A B s)) = (term293 A B _62886 s).
Proof. exact (EQ_MP (@lem4976454 A B _62886 s) (@lem4976441 A B _62886 s)). Qed.
Lemma lem4976457 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4976458 {A B : Type'} (s : type551 A B) (t : type551 A B) : (s = (term294 A B t)) = (term295 A B s t).
Proof. exact (@lem4976457 (A -> Prop) (A -> B) s t). Qed.
Lemma lem4976459 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term296 A B s P)) = (term297 A B _62886 s P).
Proof. exact (@lem4976458 A B (_62886 s P) (term231 A B s P)). Qed.
Lemma lem4976460 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4976461 {A B : Type'} (s : A -> Prop) (P : B -> Prop) : (term296 A B s P) = (term231 A B s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976460 A B s P f)). Qed.
Lemma lem4976462 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term232 A B _62886 s P) = (term232 A B _62886 s P).
Proof. exact (eq_refl (term232 A B _62886 s P)). Qed.
Lemma lem4976463 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term296 A B s P)) = ((_62886 s P) = (term231 A B s P)).
Proof. exact (MK_COMB (@lem4976462 A B _62886 s P) (@lem4976461 A B s P)). Qed.
Lemma lem4976464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976465 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term298 A B _62886 s P) = (term299 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976464) (@lem4976463 A B _62886 s P)). Qed.
Lemma lem4976466 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term233 A B s P f) = (term100 A B s P f).
Proof. exact (eq_refl (term233 A B s P f)). Qed.
Lemma lem4976467 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62886 s P f) = (term234 A B _62886 s P f).
Proof. exact (eq_refl (term234 A B _62886 s P f)). Qed.
Lemma lem4976468 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term233 A B s P f)) = ((_62886 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4976467 A B _62886 s P f) (@lem4976466 A B s P f)). Qed.
Lemma lem4976469 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term300 A B _62886 s P) = (term301 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976468 A B _62886 s P f)). Qed.
Lemma lem4976470 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976471 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term297 A B _62886 s P) = (term302 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976470 A B) (@lem4976469 A B _62886 s P)). Qed.
Lemma lem4976472 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (((_62886 s P) = (term296 A B s P)) = (term297 A B _62886 s P)) = (((_62886 s P) = (term231 A B s P)) = (term302 A B _62886 s P)).
Proof. exact (MK_COMB (@lem4976465 A B _62886 s P) (@lem4976471 A B _62886 s P)). Qed.
Lemma lem4976473 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term231 A B s P)) = (term302 A B _62886 s P).
Proof. exact (EQ_MP (@lem4976472 A B _62886 s P) (@lem4976459 A B _62886 s P)). Qed.
Lemma lem4976475 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term274 _3571 _3575 t)) = (term275 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4976476 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term303 A t)) = (term304 A s t).
Proof. exact (@lem4976475 Prop A s t). Qed.
Lemma lem4976477 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term305 A B s P f)) = (term306 A B _62886 s P f).
Proof. exact (@lem4976476 A (_62886 s P f) (term100 A B s P f)). Qed.
Lemma lem4976478 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term307 A B s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term307 A B s P f GEN_PVAR_217)). Qed.
Lemma lem4976479 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term305 A B s P f) = (term100 A B s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976478 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976480 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term234 A B _62886 s P f) = (term234 A B _62886 s P f).
Proof. exact (eq_refl (term234 A B _62886 s P f)). Qed.
Lemma lem4976481 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term305 A B s P f)) = ((_62886 s P f) = (term100 A B s P f)).
Proof. exact (MK_COMB (@lem4976480 A B _62886 s P f) (@lem4976479 A B s P f)). Qed.
Lemma lem4976482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976483 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term308 A B _62886 s P f) = (term309 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976482) (@lem4976481 A B _62886 s P f)). Qed.
Lemma lem4976484 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term307 A B s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term307 A B s P f GEN_PVAR_217)). Qed.
Lemma lem4976485 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term310 A B _62886 s P f GEN_PVAR_217) = (term310 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term310 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976486 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f GEN_PVAR_217) = (term307 A B s P f GEN_PVAR_217)) = ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4976485 A B _62886 s P f GEN_PVAR_217) (@lem4976484 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976487 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term311 A B _62886 s P f) = (term312 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976486 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976489 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term306 A B _62886 s P f) = (term313 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976488 A) (@lem4976487 A B _62886 s P f)). Qed.
Lemma lem4976490 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (((_62886 s P f) = (term305 A B s P f)) = (term306 A B _62886 s P f)) = (((_62886 s P f) = (term100 A B s P f)) = (term313 A B _62886 s P f)).
Proof. exact (MK_COMB (@lem4976483 A B _62886 s P f) (@lem4976489 A B _62886 s P f)). Qed.
Lemma lem4976491 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term100 A B s P f)) = (term313 A B _62886 s P f).
Proof. exact (EQ_MP (@lem4976490 A B _62886 s P f) (@lem4976477 A B _62886 s P f)). Qed.
Lemma lem4976492 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (eq_refl ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f))). Qed.
Lemma lem4976493 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62886 s P f) = (term312 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976492 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976495 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62886 s P f) = (term313 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976494 A) (@lem4976493 A B _62886 s P f)). Qed.
Lemma lem4976496 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f) = (term100 A B s P f)) = (term313 A B _62886 s P f).
Proof. exact (TRANS (@lem4976491 A B _62886 s P f) (@lem4976495 A B _62886 s P f)). Qed.
Lemma lem4976497 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term301 A B _62886 s P) = (term314 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976496 A B _62886 s P f)). Qed.
Lemma lem4976498 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976499 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term302 A B _62886 s P) = (term315 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976498 A B) (@lem4976497 A B _62886 s P)). Qed.
Lemma lem4976500 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((_62886 s P) = (term231 A B s P)) = (term315 A B _62886 s P).
Proof. exact (TRANS (@lem4976473 A B _62886 s P) (@lem4976499 A B _62886 s P)). Qed.
Lemma lem4976501 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term292 A B _62886 s) = (term316 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976500 A B _62886 s P)). Qed.
Lemma lem4976502 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976503 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term293 A B _62886 s) = (term317 A B _62886 s).
Proof. exact (MK_COMB (@lem4976502 B) (@lem4976501 A B _62886 s)). Qed.
Lemma lem4976504 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((_62886 s) = (term228 A B s)) = (term317 A B _62886 s).
Proof. exact (TRANS (@lem4976455 A B _62886 s) (@lem4976503 A B _62886 s)). Qed.
Lemma lem4976505 {A B : Type'} (_62886 : type653 A B) : (term283 A B _62886) = (term318 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976504 A B _62886 s)). Qed.
Lemma lem4976506 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976507 {A B : Type'} (_62886 : type653 A B) : (term284 A B _62886) = (term319 A B _62886).
Proof. exact (MK_COMB (@lem4976506 A) (@lem4976505 A B _62886)). Qed.
Lemma lem4976508 {A B : Type'} (_62886 : type653 A B) : (_62886 = (term226 A B)) = (term319 A B _62886).
Proof. exact (TRANS (@lem4976437 A B _62886) (@lem4976507 A B _62886)). Qed.
Lemma lem4976509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976510 {A B : Type'} (_62886 : type653 A B) : (term260 A B _62886) = (term320 A B _62886).
Proof. exact (MK_COMB (@lem4976509) (@lem4976508 A B _62886)). Qed.
Lemma lem4976511 {A B : Type'} (_62886 : type653 A B) : (term999 A B _62886) = (term999 A B _62886).
Proof. exact (eq_refl (term999 A B _62886)). Qed.
Lemma lem4976512 {A B : Type'} (_62886 : type653 A B) : (term1013 A B _62886) = (term1019 A B _62886).
Proof. exact (MK_COMB (@lem4976510 A B _62886) (@lem4976511 A B _62886)). Qed.
Lemma lem4976513 {A B : Type'} : (term1015 A B) = (term1020 A B).
Proof. exact (fun_ext (fun _62886 : type653 A B => @lem4976512 A B _62886)). Qed.
Lemma lem4976514 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4976515 {A B : Type'} : (term1017 A B) = (term1021 A B).
Proof. exact (MK_COMB (@lem4976514 A B) (@lem4976513 A B)). Qed.
Lemma lem4976516 {A B : Type'} : (term1005 A B) = (term1005 A B).
Proof. exact (eq_refl (term1005 A B)). Qed.
Lemma lem4976517 {A B : Type'} : ((term988 A B) = (term1017 A B)) = ((term988 A B) = (term1021 A B)).
Proof. exact (MK_COMB (@lem4976516 A B) (@lem4976515 A B)). Qed.
Lemma lem4976520 {A B : Type'} : (term988 A B) = (term1021 A B).
Proof. exact (EQ_MP (@lem4976517 A B) (@lem4976419 A B)). Qed.
Lemma lem4976521 {A B : Type'} : (term987 A B) = (term1021 A B).
Proof. exact (TRANS (@lem4976204 A B) (@lem4976520 A B)). Qed.
Lemma lem4976542 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) (y : A) : (term954 A B s P f x y) = (term954 A B s P f x y).
Proof. exact (eq_refl (term954 A B s P f x y)). Qed.
Lemma lem4976543 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term956 A B s P f x) = (term956 A B s P f x).
Proof. exact (fun_ext (fun y : A => @lem4976542 A B s P f x y)). Qed.
Lemma lem4976544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976545 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term958 A B s P f x) = (term958 A B s P f x).
Proof. exact (MK_COMB (@lem4976544 A) (@lem4976543 A B s P f x)). Qed.
Lemma lem4976546 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term960 A B s P f) = (term960 A B s P f).
Proof. exact (fun_ext (fun x : A => @lem4976545 A B s P f x)). Qed.
Lemma lem4976547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976548 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term961 A B s P f) = (term961 A B s P f).
Proof. exact (MK_COMB (@lem4976547 A) (@lem4976546 A B s P f)). Qed.
Lemma lem4976557 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4976558 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4976563 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term123 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term123 A B x f s x')). Qed.
Lemma lem4976564 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B x f s) = (term125 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4976563 A B x f s x')). Qed.
Lemma lem4976565 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4976566 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term126 A B x f s).
Proof. exact (MK_COMB (@lem4976565 A) (@lem4976564 A B x f s)). Qed.
Lemma lem4976567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976568 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4976567) (@lem4976566 A B x f s)). Qed.
Lemma lem4976569 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term130 A B f s t x).
Proof. exact (MK_COMB (@lem4976568 A B x f s) (@lem4976558 B t x)). Qed.
Lemma lem4976570 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term132 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4976569 A B f s t x)). Qed.
Lemma lem4976571 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4976572 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term133 A B f s t).
Proof. exact (MK_COMB (@lem4976571 B) (@lem4976570 A B f s t)). Qed.
Lemma lem4976573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976574 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term134 A B f s t).
Proof. exact (MK_COMB (@lem4976573) (@lem4976572 A B f s t)). Qed.
Lemma lem4976575 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term135 A B f t s).
Proof. exact (MK_COMB (@lem4976574 A B f s t) (@lem4976557 A B t s)). Qed.
Lemma lem4976588 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term113 A B s f x y).
Proof. exact (eq_refl (term113 A B s f x y)). Qed.
Lemma lem4976589 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term114 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4976588 A B s f x y)). Qed.
Lemma lem4976590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term115 A B s f x).
Proof. exact (MK_COMB (@lem4976590 A) (@lem4976589 A B s f x)). Qed.
Lemma lem4976592 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term116 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4976591 A B s f x)). Qed.
Lemma lem4976593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976594 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (MK_COMB (@lem4976593 A) (@lem4976592 A B s f)). Qed.
Lemma lem4976595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976596 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem4976595) (@lem4976594 A B s f)). Qed.
Lemma lem4976597 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term136 A B f t s).
Proof. exact (MK_COMB (@lem4976596 A B s f) (@lem4976575 A B f t s)). Qed.
Lemma lem4976600 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62886 s P f n) = (term238 A B _62886 s P f n).
Proof. exact (eq_refl (term238 A B _62886 s P f n)). Qed.
Lemma lem4976601 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term239 A B _62886 P n f t s) = (term239 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4976600 A B _62886 s P f n) (@lem4976597 A B f t s)). Qed.
Lemma lem4976602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976603 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term240 A B _62886 P n f t s) = (term240 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4976602) (@lem4976601 A B _62886 P n f t s)). Qed.
Lemma lem4976604 {A B : Type'} (_62886 : type653 A B) (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term989 A B _62886 n t s P f) = (term989 A B _62886 n t s P f).
Proof. exact (MK_COMB (@lem4976603 A B _62886 P n f t s) (@lem4976548 A B s P f)). Qed.
Lemma lem4976605 {A B : Type'} (_62886 : type653 A B) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term990 A B _62886 t s P f) = (term990 A B _62886 t s P f).
Proof. exact (fun_ext (fun n : nat => @lem4976604 A B _62886 n t s P f)). Qed.
Lemma lem4976606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4976607 {A B : Type'} (_62886 : type653 A B) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term991 A B _62886 t s P f) = (term991 A B _62886 t s P f).
Proof. exact (MK_COMB (@lem4976606) (@lem4976605 A B _62886 t s P f)). Qed.
Lemma lem4976608 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term992 A B _62886 s P f) = (term992 A B _62886 s P f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4976607 A B _62886 t s P f)). Qed.
Lemma lem4976609 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976610 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term993 A B _62886 s P f) = (term993 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976609 B) (@lem4976608 A B _62886 s P f)). Qed.
Lemma lem4976611 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (f : A -> B) : (term994 A B _62886 P f) = (term994 A B _62886 P f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976610 A B _62886 s P f)). Qed.
Lemma lem4976612 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976613 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (f : A -> B) : (term995 A B _62886 P f) = (term995 A B _62886 P f).
Proof. exact (MK_COMB (@lem4976612 A) (@lem4976611 A B _62886 P f)). Qed.
Lemma lem4976614 {A B : Type'} (_62886 : type653 A B) (f : A -> B) : (term996 A B _62886 f) = (term996 A B _62886 f).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976613 A B _62886 P f)). Qed.
Lemma lem4976615 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976616 {A B : Type'} (_62886 : type653 A B) (f : A -> B) : (term997 A B _62886 f) = (term997 A B _62886 f).
Proof. exact (MK_COMB (@lem4976615 B) (@lem4976614 A B _62886 f)). Qed.
Lemma lem4976617 {A B : Type'} (_62886 : type653 A B) : (term998 A B _62886) = (term998 A B _62886).
Proof. exact (fun_ext (fun f : A -> B => @lem4976616 A B _62886 f)). Qed.
Lemma lem4976618 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976619 {A B : Type'} (_62886 : type653 A B) : (term999 A B _62886) = (term999 A B _62886).
Proof. exact (MK_COMB (@lem4976618 A B) (@lem4976617 A B _62886)). Qed.
Lemma lem4976620 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term94 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term94 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976621 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term96 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4976620 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976622 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4976623 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term98 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976622 A) (@lem4976621 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976626 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term310 A B _62886 s P f GEN_PVAR_217) = (term310 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term310 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976627 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4976626 A B _62886 s P f GEN_PVAR_217) (@lem4976623 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976628 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62886 s P f) = (term312 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976627 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976630 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62886 s P f) = (term313 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976629 A) (@lem4976628 A B _62886 s P f)). Qed.
Lemma lem4976631 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term314 A B _62886 s P) = (term314 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976630 A B _62886 s P f)). Qed.
Lemma lem4976632 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976633 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term315 A B _62886 s P) = (term315 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976632 A B) (@lem4976631 A B _62886 s P)). Qed.
Lemma lem4976634 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term316 A B _62886 s) = (term316 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976633 A B _62886 s P)). Qed.
Lemma lem4976635 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976636 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term317 A B _62886 s) = (term317 A B _62886 s).
Proof. exact (MK_COMB (@lem4976635 B) (@lem4976634 A B _62886 s)). Qed.
Lemma lem4976637 {A B : Type'} (_62886 : type653 A B) : (term318 A B _62886) = (term318 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976636 A B _62886 s)). Qed.
Lemma lem4976638 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976639 {A B : Type'} (_62886 : type653 A B) : (term319 A B _62886) = (term319 A B _62886).
Proof. exact (MK_COMB (@lem4976638 A) (@lem4976637 A B _62886)). Qed.
Lemma lem4976640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4976641 {A B : Type'} (_62886 : type653 A B) : (term320 A B _62886) = (term320 A B _62886).
Proof. exact (MK_COMB (@lem4976640) (@lem4976639 A B _62886)). Qed.
Lemma lem4976642 {A B : Type'} (_62886 : type653 A B) : (term1019 A B _62886) = (term1019 A B _62886).
Proof. exact (MK_COMB (@lem4976641 A B _62886) (@lem4976619 A B _62886)). Qed.
Lemma lem4976643 {A B : Type'} : (term1020 A B) = (term1020 A B).
Proof. exact (fun_ext (fun _62886 : type653 A B => @lem4976642 A B _62886)). Qed.
Lemma lem4976644 {A B : Type'} : (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)) = (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop))). Qed.
Lemma lem4976645 {A B : Type'} : (term1021 A B) = (term1021 A B).
Proof. exact (MK_COMB (@lem4976644 A B) (@lem4976643 A B)). Qed.
Lemma lem4976786 {A B : Type'} : (term987 A B) = (term1021 A B).
Proof. exact (TRANS (@lem4976521 A B) (@lem4976645 A B)). Qed.
Lemma lem4976787 {A B : Type'} : (term1021 A B) = (term987 A B).
Proof. exact (SYM (@lem4976786 A B)). Qed.
Lemma lem4976788 {A B : Type'} (_62886 : type653 A B) (h1 : term319 A B _62886) : term319 A B _62886.
Proof. exact (h1). Qed.
Lemma lem4976789 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term239 A B _62886 P n f t s.
Proof. exact (h1). Qed.
Lemma lem4976792 (p : Prop) : p = (term198 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4976793 {A : Type'} (x : A) (y : A) : (x = y) = (term1022 A x y).
Proof. exact (@lem4976792 (x = y)). Qed.
Lemma lem4976794 {A : Type'} (x : A) (y : A) : (term1022 A x y) = (x = y).
Proof. exact (SYM (@lem4976793 A x y)). Qed.
Lemma lem4976795 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term843 A x y.
Proof. exact (h1). Qed.
Lemma lem4976799 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term94 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term94 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976800 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4976801 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term328 A B GEN_PVAR_217 s P f) = (term329 A B GEN_PVAR_217 s P f).
Proof. exact (@lem4976800 A (term96 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976802 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4976805 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term331 A B GEN_PVAR_217 s P f x) = (term332 A B GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4976803) (@lem4976802 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976806 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term333 A B GEN_PVAR_217 s P f) = (term334 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4976805 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976807 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976808 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term329 A B GEN_PVAR_217 s P f) = (term335 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976807 A) (@lem4976806 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976809 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term328 A B GEN_PVAR_217 s P f) = (term335 A B GEN_PVAR_217 s P f).
Proof. exact (TRANS (@lem4976801 A B GEN_PVAR_217 s P f) (@lem4976808 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976810 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term96 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4976799 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4976811 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4976812 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term98 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976811 A) (@lem4976810 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976814 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62886 s P f GEN_PVAR_217) = (term336 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976815 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term337 A B _62886 GEN_PVAR_217 s P f) = (term337 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976814 A B _62886 s P f GEN_PVAR_217) (@lem4976812 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976817 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term338 A B _62886 s P f GEN_PVAR_217) = (term338 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term338 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976818 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term339 A B _62886 GEN_PVAR_217 s P f) = (term340 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976817 A B _62886 s P f GEN_PVAR_217) (@lem4976809 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976820 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term341 A B _62886 GEN_PVAR_217 s P f) = (term342 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976819) (@lem4976818 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976821 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term343 A B _62886 GEN_PVAR_217 s P f) = (term344 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976820 A B _62886 GEN_PVAR_217 s P f) (@lem4976815 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976822 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = (term343 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (@lem17784 (_62886 s P f GEN_PVAR_217) (term98 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4976823 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((_62886 s P f GEN_PVAR_217) = (term98 A B GEN_PVAR_217 s P f)) = (term344 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (TRANS (@lem4976822 A B _62886 GEN_PVAR_217 s P f) (@lem4976821 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976824 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term312 A B _62886 s P f) = (term345 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976823 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976826 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B _62886 s P f) = (term346 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976825 A) (@lem4976824 A B _62886 s P f)). Qed.
Lemma lem4976827 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term314 A B _62886 s P) = (term347 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976826 A B _62886 s P f)). Qed.
Lemma lem4976828 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976829 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term315 A B _62886 s P) = (term348 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976828 A B) (@lem4976827 A B _62886 s P)). Qed.
Lemma lem4976830 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term316 A B _62886 s) = (term349 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4976829 A B _62886 s P)). Qed.
Lemma lem4976831 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4976832 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term317 A B _62886 s) = (term350 A B _62886 s).
Proof. exact (MK_COMB (@lem4976831 B) (@lem4976830 A B _62886 s)). Qed.
Lemma lem4976833 {A B : Type'} (_62886 : type653 A B) : (term318 A B _62886) = (term351 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4976832 A B _62886 s)). Qed.
Lemma lem4976834 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4976835 {A B : Type'} (_62886 : type653 A B) : (term319 A B _62886) = (term352 A B _62886).
Proof. exact (MK_COMB (@lem4976834 A) (@lem4976833 A B _62886)). Qed.
Lemma lem4976849 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4976850 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (@lem4976849 A P Q). Qed.
Lemma lem4976851 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term355 A B _62886 s P f) = (term356 A B _62886 s P f).
Proof. exact (@lem4976850 A (term357 A B _62886 s P f) (term358 A B _62886 s P f)). Qed.
Lemma lem4976852 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term359 A B _62886 s P f GEN_PVAR_217) = (term340 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term359 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976854 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term360 A B _62886 s P f GEN_PVAR_217) = (term342 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976853) (@lem4976852 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976855 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term361 A B _62886 s P f GEN_PVAR_217) = (term337 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term361 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976856 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term362 A B _62886 s P f GEN_PVAR_217) = (term344 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4976854 A B _62886 GEN_PVAR_217 s P f) (@lem4976855 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976857 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term363 A B _62886 s P f) = (term345 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976856 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976859 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term355 A B _62886 s P f) = (term346 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976858 A) (@lem4976857 A B _62886 s P f)). Qed.
Lemma lem4976860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976861 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term364 A B _62886 s P f) = (term365 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976860) (@lem4976859 A B _62886 s P f)). Qed.
Lemma lem4976862 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term359 A B _62886 s P f GEN_PVAR_217) = (term340 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term359 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976863 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term366 A B _62886 s P f) = (term357 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976862 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976865 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term367 A B _62886 s P f) = (term368 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976864 A) (@lem4976863 A B _62886 s P f)). Qed.
Lemma lem4976866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976867 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term369 A B _62886 s P f) = (term370 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976866) (@lem4976865 A B _62886 s P f)). Qed.
Lemma lem4976868 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term361 A B _62886 s P f GEN_PVAR_217) = (term337 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term361 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4976869 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term371 A B _62886 s P f) = (term358 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4976868 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4976870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4976871 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term372 A B _62886 s P f) = (term373 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976870 A) (@lem4976869 A B _62886 s P f)). Qed.
Lemma lem4976872 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term356 A B _62886 s P f) = (term374 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976867 A B _62886 s P f) (@lem4976871 A B _62886 s P f)). Qed.
Lemma lem4976873 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term355 A B _62886 s P f) = (term356 A B _62886 s P f)) = ((term346 A B _62886 s P f) = (term374 A B _62886 s P f)).
Proof. exact (MK_COMB (@lem4976861 A B _62886 s P f) (@lem4976872 A B _62886 s P f)). Qed.
Lemma lem4976874 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term346 A B _62886 s P f) = (term374 A B _62886 s P f).
Proof. exact (EQ_MP (@lem4976873 A B _62886 s P f) (@lem4976851 A B _62886 s P f)). Qed.
Lemma lem4976979 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term347 A B _62886 s P) = (term375 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976874 A B _62886 s P f)). Qed.
Lemma lem4976980 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976981 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term348 A B _62886 s P) = (term376 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976980 A B) (@lem4976979 A B _62886 s P)). Qed.
Lemma lem4976983 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4976984 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term377 A B P Q) = (term378 A B P Q).
Proof. exact (@lem4976983 (A -> B) P Q). Qed.
Lemma lem4976985 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term379 A B _62886 s P) = (term380 A B _62886 s P).
Proof. exact (@lem4976984 A B (term381 A B _62886 s P) (term382 A B _62886 s P)). Qed.
Lemma lem4976986 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term383 A B _62886 s P f) = (term368 A B _62886 s P f).
Proof. exact (eq_refl (term383 A B _62886 s P f)). Qed.
Lemma lem4976987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4976988 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term384 A B _62886 s P f) = (term370 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976987) (@lem4976986 A B _62886 s P f)). Qed.
Lemma lem4976989 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term385 A B _62886 s P f) = (term373 A B _62886 s P f).
Proof. exact (eq_refl (term385 A B _62886 s P f)). Qed.
Lemma lem4976990 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term386 A B _62886 s P f) = (term374 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4976988 A B _62886 s P f) (@lem4976989 A B _62886 s P f)). Qed.
Lemma lem4976991 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term387 A B _62886 s P) = (term375 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976990 A B _62886 s P f)). Qed.
Lemma lem4976992 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976993 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term379 A B _62886 s P) = (term376 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976992 A B) (@lem4976991 A B _62886 s P)). Qed.
Lemma lem4976994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4976995 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term388 A B _62886 s P) = (term389 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976994) (@lem4976993 A B _62886 s P)). Qed.
Lemma lem4976996 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term383 A B _62886 s P f) = (term368 A B _62886 s P f).
Proof. exact (eq_refl (term383 A B _62886 s P f)). Qed.
Lemma lem4976997 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term390 A B _62886 s P) = (term381 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4976996 A B _62886 s P f)). Qed.
Lemma lem4976998 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4976999 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term391 A B _62886 s P) = (term392 A B _62886 s P).
Proof. exact (MK_COMB (@lem4976998 A B) (@lem4976997 A B _62886 s P)). Qed.
Lemma lem4977000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977001 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term393 A B _62886 s P) = (term394 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977000) (@lem4976999 A B _62886 s P)). Qed.
Lemma lem4977002 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term385 A B _62886 s P f) = (term373 A B _62886 s P f).
Proof. exact (eq_refl (term385 A B _62886 s P f)). Qed.
Lemma lem4977003 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term395 A B _62886 s P) = (term382 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4977002 A B _62886 s P f)). Qed.
Lemma lem4977004 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4977005 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term396 A B _62886 s P) = (term397 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977004 A B) (@lem4977003 A B _62886 s P)). Qed.
Lemma lem4977006 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term380 A B _62886 s P) = (term398 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977001 A B _62886 s P) (@lem4977005 A B _62886 s P)). Qed.
Lemma lem4977007 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((term379 A B _62886 s P) = (term380 A B _62886 s P)) = ((term376 A B _62886 s P) = (term398 A B _62886 s P)).
Proof. exact (MK_COMB (@lem4976995 A B _62886 s P) (@lem4977006 A B _62886 s P)). Qed.
Lemma lem4977008 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term376 A B _62886 s P) = (term398 A B _62886 s P).
Proof. exact (EQ_MP (@lem4977007 A B _62886 s P) (@lem4976985 A B _62886 s P)). Qed.
Lemma lem4977121 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term348 A B _62886 s P) = (term398 A B _62886 s P).
Proof. exact (TRANS (@lem4976981 A B _62886 s P) (@lem4977008 A B _62886 s P)). Qed.
Lemma lem4977122 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term349 A B _62886 s) = (term399 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977121 A B _62886 s P)). Qed.
Lemma lem4977123 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977124 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term350 A B _62886 s) = (term400 A B _62886 s).
Proof. exact (MK_COMB (@lem4977123 B) (@lem4977122 A B _62886 s)). Qed.
Lemma lem4977126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4977127 {B : Type'} (P : type686 B) (Q : type686 B) : (term401 B P Q) = (term402 B P Q).
Proof. exact (@lem4977126 (B -> Prop) P Q). Qed.
Lemma lem4977128 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term403 A B _62886 s) = (term404 A B _62886 s).
Proof. exact (@lem4977127 B (term405 A B _62886 s) (term406 A B _62886 s)). Qed.
Lemma lem4977129 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term407 A B _62886 s P) = (term392 A B _62886 s P).
Proof. exact (eq_refl (term407 A B _62886 s P)). Qed.
Lemma lem4977130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977131 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term408 A B _62886 s P) = (term394 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977130) (@lem4977129 A B _62886 s P)). Qed.
Lemma lem4977132 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term409 A B _62886 s P) = (term397 A B _62886 s P).
Proof. exact (eq_refl (term409 A B _62886 s P)). Qed.
Lemma lem4977133 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term410 A B _62886 s P) = (term398 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977131 A B _62886 s P) (@lem4977132 A B _62886 s P)). Qed.
Lemma lem4977134 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term411 A B _62886 s) = (term399 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977133 A B _62886 s P)). Qed.
Lemma lem4977135 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977136 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term403 A B _62886 s) = (term400 A B _62886 s).
Proof. exact (MK_COMB (@lem4977135 B) (@lem4977134 A B _62886 s)). Qed.
Lemma lem4977137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977138 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term412 A B _62886 s) = (term413 A B _62886 s).
Proof. exact (MK_COMB (@lem4977137) (@lem4977136 A B _62886 s)). Qed.
Lemma lem4977139 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term407 A B _62886 s P) = (term392 A B _62886 s P).
Proof. exact (eq_refl (term407 A B _62886 s P)). Qed.
Lemma lem4977140 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term414 A B _62886 s) = (term405 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977139 A B _62886 s P)). Qed.
Lemma lem4977141 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977142 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term415 A B _62886 s) = (term416 A B _62886 s).
Proof. exact (MK_COMB (@lem4977141 B) (@lem4977140 A B _62886 s)). Qed.
Lemma lem4977143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977144 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term417 A B _62886 s) = (term418 A B _62886 s).
Proof. exact (MK_COMB (@lem4977143) (@lem4977142 A B _62886 s)). Qed.
Lemma lem4977145 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term409 A B _62886 s P) = (term397 A B _62886 s P).
Proof. exact (eq_refl (term409 A B _62886 s P)). Qed.
Lemma lem4977146 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term419 A B _62886 s) = (term406 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977145 A B _62886 s P)). Qed.
Lemma lem4977147 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977148 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term420 A B _62886 s) = (term421 A B _62886 s).
Proof. exact (MK_COMB (@lem4977147 B) (@lem4977146 A B _62886 s)). Qed.
Lemma lem4977149 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term404 A B _62886 s) = (term422 A B _62886 s).
Proof. exact (MK_COMB (@lem4977144 A B _62886 s) (@lem4977148 A B _62886 s)). Qed.
Lemma lem4977150 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((term403 A B _62886 s) = (term404 A B _62886 s)) = ((term400 A B _62886 s) = (term422 A B _62886 s)).
Proof. exact (MK_COMB (@lem4977138 A B _62886 s) (@lem4977149 A B _62886 s)). Qed.
Lemma lem4977151 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term400 A B _62886 s) = (term422 A B _62886 s).
Proof. exact (EQ_MP (@lem4977150 A B _62886 s) (@lem4977128 A B _62886 s)). Qed.
Lemma lem4977272 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term350 A B _62886 s) = (term422 A B _62886 s).
Proof. exact (TRANS (@lem4977124 A B _62886 s) (@lem4977151 A B _62886 s)). Qed.
Lemma lem4977273 {A B : Type'} (_62886 : type653 A B) : (term351 A B _62886) = (term423 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977272 A B _62886 s)). Qed.
Lemma lem4977274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977275 {A B : Type'} (_62886 : type653 A B) : (term352 A B _62886) = (term424 A B _62886).
Proof. exact (MK_COMB (@lem4977274 A) (@lem4977273 A B _62886)). Qed.
Lemma lem4977277 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4977278 {A : Type'} (P : type686 A) (Q : type686 A) : (term401 A P Q) = (term402 A P Q).
Proof. exact (@lem4977277 (A -> Prop) P Q). Qed.
Lemma lem4977279 {A B : Type'} (_62886 : type653 A B) : (term425 A B _62886) = (term426 A B _62886).
Proof. exact (@lem4977278 A (term427 A B _62886) (term428 A B _62886)). Qed.
Lemma lem4977280 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term429 A B _62886 s) = (term416 A B _62886 s).
Proof. exact (eq_refl (term429 A B _62886 s)). Qed.
Lemma lem4977281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977282 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term430 A B _62886 s) = (term418 A B _62886 s).
Proof. exact (MK_COMB (@lem4977281) (@lem4977280 A B _62886 s)). Qed.
Lemma lem4977283 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term431 A B _62886 s) = (term421 A B _62886 s).
Proof. exact (eq_refl (term431 A B _62886 s)). Qed.
Lemma lem4977284 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term432 A B _62886 s) = (term422 A B _62886 s).
Proof. exact (MK_COMB (@lem4977282 A B _62886 s) (@lem4977283 A B _62886 s)). Qed.
Lemma lem4977285 {A B : Type'} (_62886 : type653 A B) : (term433 A B _62886) = (term423 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977284 A B _62886 s)). Qed.
Lemma lem4977286 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977287 {A B : Type'} (_62886 : type653 A B) : (term425 A B _62886) = (term424 A B _62886).
Proof. exact (MK_COMB (@lem4977286 A) (@lem4977285 A B _62886)). Qed.
Lemma lem4977288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977289 {A B : Type'} (_62886 : type653 A B) : (term434 A B _62886) = (term435 A B _62886).
Proof. exact (MK_COMB (@lem4977288) (@lem4977287 A B _62886)). Qed.
Lemma lem4977290 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term429 A B _62886 s) = (term416 A B _62886 s).
Proof. exact (eq_refl (term429 A B _62886 s)). Qed.
Lemma lem4977291 {A B : Type'} (_62886 : type653 A B) : (term436 A B _62886) = (term427 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977290 A B _62886 s)). Qed.
Lemma lem4977292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977293 {A B : Type'} (_62886 : type653 A B) : (term437 A B _62886) = (term438 A B _62886).
Proof. exact (MK_COMB (@lem4977292 A) (@lem4977291 A B _62886)). Qed.
Lemma lem4977294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977295 {A B : Type'} (_62886 : type653 A B) : (term439 A B _62886) = (term440 A B _62886).
Proof. exact (MK_COMB (@lem4977294) (@lem4977293 A B _62886)). Qed.
Lemma lem4977296 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term431 A B _62886 s) = (term421 A B _62886 s).
Proof. exact (eq_refl (term431 A B _62886 s)). Qed.
Lemma lem4977297 {A B : Type'} (_62886 : type653 A B) : (term441 A B _62886) = (term428 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977296 A B _62886 s)). Qed.
Lemma lem4977298 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977299 {A B : Type'} (_62886 : type653 A B) : (term442 A B _62886) = (term443 A B _62886).
Proof. exact (MK_COMB (@lem4977298 A) (@lem4977297 A B _62886)). Qed.
Lemma lem4977300 {A B : Type'} (_62886 : type653 A B) : (term426 A B _62886) = (term444 A B _62886).
Proof. exact (MK_COMB (@lem4977295 A B _62886) (@lem4977299 A B _62886)). Qed.
Lemma lem4977301 {A B : Type'} (_62886 : type653 A B) : ((term425 A B _62886) = (term426 A B _62886)) = ((term424 A B _62886) = (term444 A B _62886)).
Proof. exact (MK_COMB (@lem4977289 A B _62886) (@lem4977300 A B _62886)). Qed.
Lemma lem4977302 {A B : Type'} (_62886 : type653 A B) : (term424 A B _62886) = (term444 A B _62886).
Proof. exact (EQ_MP (@lem4977301 A B _62886) (@lem4977279 A B _62886)). Qed.
Lemma lem4977431 {A B : Type'} (_62886 : type653 A B) : (term352 A B _62886) = (term444 A B _62886).
Proof. exact (TRANS (@lem4977275 A B _62886) (@lem4977302 A B _62886)). Qed.
Lemma lem4977433 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4977434 {A : Type'} (P : Prop) (Q : A -> Prop) : (term445 A P Q) = (term446 A P Q).
Proof. exact (@lem4977433 A P Q). Qed.
Lemma lem4977435 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term447 A B _62886 GEN_PVAR_217 s P f) = (term448 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (@lem4977434 A (term449 A B _62886 s P f GEN_PVAR_217) (term96 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4977436 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977437 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term450 A B GEN_PVAR_217 s P f) = (term96 A B GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4977436 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977438 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4977439 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term451 A B GEN_PVAR_217 s P f) = (term98 A B GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4977438 A) (@lem4977437 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4977440 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62886 s P f GEN_PVAR_217) = (term336 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4977441 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term447 A B _62886 GEN_PVAR_217 s P f) = (term337 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4977440 A B _62886 s P f GEN_PVAR_217) (@lem4977439 A B GEN_PVAR_217 s P f)). Qed.
Lemma lem4977442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977443 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term452 A B _62886 GEN_PVAR_217 s P f) = (term453 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4977442) (@lem4977441 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977444 {A B : Type'} (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term330 A B GEN_PVAR_217 s P f x) = (term94 A B GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term330 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977445 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (GEN_PVAR_217 : A) : (term336 A B _62886 s P f GEN_PVAR_217) = (term336 A B _62886 s P f GEN_PVAR_217).
Proof. exact (eq_refl (term336 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4977446 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term454 A B _62886 GEN_PVAR_217 s P f x) = (term455 A B _62886 GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4977445 A B _62886 s P f GEN_PVAR_217) (@lem4977444 A B GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977447 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term456 A B _62886 GEN_PVAR_217 s P f) = (term457 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4977446 A B _62886 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977448 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4977449 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term448 A B _62886 GEN_PVAR_217 s P f) = (term458 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4977448 A) (@lem4977447 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977450 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term447 A B _62886 GEN_PVAR_217 s P f) = (term448 A B _62886 GEN_PVAR_217 s P f)) = ((term337 A B _62886 GEN_PVAR_217 s P f) = (term458 A B _62886 GEN_PVAR_217 s P f)).
Proof. exact (MK_COMB (@lem4977443 A B _62886 GEN_PVAR_217 s P f) (@lem4977449 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977451 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term337 A B _62886 GEN_PVAR_217 s P f) = (term458 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (EQ_MP (@lem4977450 A B _62886 GEN_PVAR_217 s P f) (@lem4977435 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977452 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term358 A B _62886 s P f) = (term459 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4977451 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977454 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term373 A B _62886 s P f) = (term460 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4977453 A) (@lem4977452 A B _62886 s P f)). Qed.
Lemma lem4977456 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4977457 {A : Type'} (P : type1402 A) : (term463 A P) = (term464 A P).
Proof. exact (@lem4977456 A A P). Qed.
Lemma lem4977458 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term465 A B _62886 s P f) = (term466 A B _62886 s P f).
Proof. exact (@lem4977457 A (term467 A B _62886 s P f)). Qed.
Lemma lem4977459 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term468 A B _62886 s P f GEN_PVAR_217) = (term457 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term468 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4977460 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4977461 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term469 A B _62886 s P f GEN_PVAR_217 x) = (term470 A B _62886 GEN_PVAR_217 s P f x).
Proof. exact (MK_COMB (@lem4977459 A B _62886 GEN_PVAR_217 s P f) (@lem4977460 A x)). Qed.
Lemma lem4977462 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term470 A B _62886 GEN_PVAR_217 s P f x) = (term455 A B _62886 GEN_PVAR_217 s P f x).
Proof. exact (eq_refl (term470 A B _62886 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977463 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term469 A B _62886 s P f GEN_PVAR_217 x) = (term455 A B _62886 GEN_PVAR_217 s P f x).
Proof. exact (TRANS (@lem4977461 A B _62886 GEN_PVAR_217 s P f x) (@lem4977462 A B _62886 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977464 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term471 A B _62886 s P f GEN_PVAR_217) = (term457 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (fun_ext (fun x : A => @lem4977463 A B _62886 GEN_PVAR_217 s P f x)). Qed.
Lemma lem4977465 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4977466 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term472 A B _62886 s P f GEN_PVAR_217) = (term458 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (MK_COMB (@lem4977465 A) (@lem4977464 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977467 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term473 A B _62886 s P f) = (term459 A B _62886 s P f).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4977466 A B _62886 GEN_PVAR_217 s P f)). Qed.
Lemma lem4977468 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977469 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term465 A B _62886 s P f) = (term460 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4977468 A) (@lem4977467 A B _62886 s P f)). Qed.
Lemma lem4977470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977471 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term474 A B _62886 s P f) = (term475 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4977470) (@lem4977469 A B _62886 s P f)). Qed.
Lemma lem4977472 {A B : Type'} (_62886 : type653 A B) (GEN_PVAR_217 : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term468 A B _62886 s P f GEN_PVAR_217) = (term457 A B _62886 GEN_PVAR_217 s P f).
Proof. exact (eq_refl (term468 A B _62886 s P f GEN_PVAR_217)). Qed.
Lemma lem4977473 {A : Type'} (x : A -> A) (GEN_PVAR_217 : A) : (x GEN_PVAR_217) = (x GEN_PVAR_217).
Proof. exact (eq_refl (x GEN_PVAR_217)). Qed.
Lemma lem4977474 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term476 A B _62886 s P f x GEN_PVAR_217) = (term477 A B _62886 s P f x GEN_PVAR_217).
Proof. exact (MK_COMB (@lem4977472 A B _62886 GEN_PVAR_217 s P f) (@lem4977473 A x GEN_PVAR_217)). Qed.
Lemma lem4977475 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term477 A B _62886 s P f x GEN_PVAR_217) = (term478 A B _62886 s P f x GEN_PVAR_217).
Proof. exact (eq_refl (term477 A B _62886 s P f x GEN_PVAR_217)). Qed.
Lemma lem4977476 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) (GEN_PVAR_217 : A) : (term476 A B _62886 s P f x GEN_PVAR_217) = (term478 A B _62886 s P f x GEN_PVAR_217).
Proof. exact (TRANS (@lem4977474 A B _62886 s P f x GEN_PVAR_217) (@lem4977475 A B _62886 s P f x GEN_PVAR_217)). Qed.
Lemma lem4977477 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term479 A B _62886 s P f x) = (term480 A B _62886 s P f x).
Proof. exact (fun_ext (fun GEN_PVAR_217 : A => @lem4977476 A B _62886 s P f x GEN_PVAR_217)). Qed.
Lemma lem4977478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977479 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term481 A B _62886 s P f x) = (term482 A B _62886 s P f x).
Proof. exact (MK_COMB (@lem4977478 A) (@lem4977477 A B _62886 s P f x)). Qed.
Lemma lem4977480 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term483 A B _62886 s P f) = (term484 A B _62886 s P f).
Proof. exact (fun_ext (fun x : A -> A => @lem4977479 A B _62886 s P f x)). Qed.
Lemma lem4977481 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4977482 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term466 A B _62886 s P f) = (term485 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4977481 A) (@lem4977480 A B _62886 s P f)). Qed.
Lemma lem4977483 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : ((term465 A B _62886 s P f) = (term466 A B _62886 s P f)) = ((term460 A B _62886 s P f) = (term485 A B _62886 s P f)).
Proof. exact (MK_COMB (@lem4977471 A B _62886 s P f) (@lem4977482 A B _62886 s P f)). Qed.
Lemma lem4977484 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term460 A B _62886 s P f) = (term485 A B _62886 s P f).
Proof. exact (EQ_MP (@lem4977483 A B _62886 s P f) (@lem4977458 A B _62886 s P f)). Qed.
Lemma lem4977485 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term373 A B _62886 s P f) = (term485 A B _62886 s P f).
Proof. exact (TRANS (@lem4977454 A B _62886 s P f) (@lem4977484 A B _62886 s P f)). Qed.
Lemma lem4977486 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term382 A B _62886 s P) = (term486 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4977485 A B _62886 s P f)). Qed.
Lemma lem4977487 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4977488 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term397 A B _62886 s P) = (term487 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977487 A B) (@lem4977486 A B _62886 s P)). Qed.
Lemma lem4977490 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4977491 {A B : Type'} (P : type513 A B) : (term488 A B P) = (term489 A B P).
Proof. exact (@lem4977490 (A -> B) (A -> A) P). Qed.
Lemma lem4977492 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term490 A B _62886 s P) = (term491 A B _62886 s P).
Proof. exact (@lem4977491 A B (term492 A B _62886 s P)). Qed.
Lemma lem4977493 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term493 A B _62886 s P f) = (term484 A B _62886 s P f).
Proof. exact (eq_refl (term493 A B _62886 s P f)). Qed.
Lemma lem4977494 {A : Type'} (x : A -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4977495 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term494 A B _62886 s P f x) = (term495 A B _62886 s P f x).
Proof. exact (MK_COMB (@lem4977493 A B _62886 s P f) (@lem4977494 A x)). Qed.
Lemma lem4977496 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term495 A B _62886 s P f x) = (term482 A B _62886 s P f x).
Proof. exact (eq_refl (term495 A B _62886 s P f x)). Qed.
Lemma lem4977497 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A -> A) : (term494 A B _62886 s P f x) = (term482 A B _62886 s P f x).
Proof. exact (TRANS (@lem4977495 A B _62886 s P f x) (@lem4977496 A B _62886 s P f x)). Qed.
Lemma lem4977498 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term496 A B _62886 s P f) = (term484 A B _62886 s P f).
Proof. exact (fun_ext (fun x : A -> A => @lem4977497 A B _62886 s P f x)). Qed.
Lemma lem4977499 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4977500 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term497 A B _62886 s P f) = (term485 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4977499 A) (@lem4977498 A B _62886 s P f)). Qed.
Lemma lem4977501 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term498 A B _62886 s P) = (term486 A B _62886 s P).
Proof. exact (fun_ext (fun f : A -> B => @lem4977500 A B _62886 s P f)). Qed.
Lemma lem4977502 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4977503 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term490 A B _62886 s P) = (term487 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977502 A B) (@lem4977501 A B _62886 s P)). Qed.
Lemma lem4977504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977505 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term499 A B _62886 s P) = (term500 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977504) (@lem4977503 A B _62886 s P)). Qed.
Lemma lem4977506 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term493 A B _62886 s P f) = (term484 A B _62886 s P f).
Proof. exact (eq_refl (term493 A B _62886 s P f)). Qed.
Lemma lem4977507 {A B : Type'} (x : type548 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4977508 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term501 A B _62886 s P x f) = (term502 A B _62886 s P x f).
Proof. exact (MK_COMB (@lem4977506 A B _62886 s P f) (@lem4977507 A B x f)). Qed.
Lemma lem4977509 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term502 A B _62886 s P x f) = (term503 A B _62886 s P x f).
Proof. exact (eq_refl (term502 A B _62886 s P x f)). Qed.
Lemma lem4977510 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) (f : A -> B) : (term501 A B _62886 s P x f) = (term503 A B _62886 s P x f).
Proof. exact (TRANS (@lem4977508 A B _62886 s P x f) (@lem4977509 A B _62886 s P x f)). Qed.
Lemma lem4977511 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term504 A B _62886 s P x) = (term505 A B _62886 s P x).
Proof. exact (fun_ext (fun f : A -> B => @lem4977510 A B _62886 s P x f)). Qed.
Lemma lem4977512 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4977513 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term506 A B _62886 s P x) = (term507 A B _62886 s P x).
Proof. exact (MK_COMB (@lem4977512 A B) (@lem4977511 A B _62886 s P x)). Qed.
Lemma lem4977514 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term508 A B _62886 s P) = (term509 A B _62886 s P).
Proof. exact (fun_ext (fun x : type548 A B => @lem4977513 A B _62886 s P x)). Qed.
Lemma lem4977515 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem4977516 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term491 A B _62886 s P) = (term510 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977515 A B) (@lem4977514 A B _62886 s P)). Qed.
Lemma lem4977517 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : ((term490 A B _62886 s P) = (term491 A B _62886 s P)) = ((term487 A B _62886 s P) = (term510 A B _62886 s P)).
Proof. exact (MK_COMB (@lem4977505 A B _62886 s P) (@lem4977516 A B _62886 s P)). Qed.
Lemma lem4977518 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term487 A B _62886 s P) = (term510 A B _62886 s P).
Proof. exact (EQ_MP (@lem4977517 A B _62886 s P) (@lem4977492 A B _62886 s P)). Qed.
Lemma lem4977519 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term397 A B _62886 s P) = (term510 A B _62886 s P).
Proof. exact (TRANS (@lem4977488 A B _62886 s P) (@lem4977518 A B _62886 s P)). Qed.
Lemma lem4977520 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term406 A B _62886 s) = (term511 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977519 A B _62886 s P)). Qed.
Lemma lem4977521 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977522 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term421 A B _62886 s) = (term512 A B _62886 s).
Proof. exact (MK_COMB (@lem4977521 B) (@lem4977520 A B _62886 s)). Qed.
Lemma lem4977524 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4977525 {A B : Type'} (P : type817 A B) : (term513 A B P) = (term514 A B P).
Proof. exact (@lem4977524 (B -> Prop) (type548 A B) P). Qed.
Lemma lem4977526 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term515 A B _62886 s) = (term516 A B _62886 s).
Proof. exact (@lem4977525 A B (term517 A B _62886 s)). Qed.
Lemma lem4977527 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term518 A B _62886 s P) = (term509 A B _62886 s P).
Proof. exact (eq_refl (term518 A B _62886 s P)). Qed.
Lemma lem4977528 {A B : Type'} (x : type548 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4977529 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term519 A B _62886 s P x) = (term520 A B _62886 s P x).
Proof. exact (MK_COMB (@lem4977527 A B _62886 s P) (@lem4977528 A B x)). Qed.
Lemma lem4977530 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term520 A B _62886 s P x) = (term507 A B _62886 s P x).
Proof. exact (eq_refl (term520 A B _62886 s P x)). Qed.
Lemma lem4977531 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (x : type548 A B) : (term519 A B _62886 s P x) = (term507 A B _62886 s P x).
Proof. exact (TRANS (@lem4977529 A B _62886 s P x) (@lem4977530 A B _62886 s P x)). Qed.
Lemma lem4977532 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term521 A B _62886 s P) = (term509 A B _62886 s P).
Proof. exact (fun_ext (fun x : type548 A B => @lem4977531 A B _62886 s P x)). Qed.
Lemma lem4977533 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem4977534 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term522 A B _62886 s P) = (term510 A B _62886 s P).
Proof. exact (MK_COMB (@lem4977533 A B) (@lem4977532 A B _62886 s P)). Qed.
Lemma lem4977535 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term523 A B _62886 s) = (term511 A B _62886 s).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977534 A B _62886 s P)). Qed.
Lemma lem4977536 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977537 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term515 A B _62886 s) = (term512 A B _62886 s).
Proof. exact (MK_COMB (@lem4977536 B) (@lem4977535 A B _62886 s)). Qed.
Lemma lem4977538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977539 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term524 A B _62886 s) = (term525 A B _62886 s).
Proof. exact (MK_COMB (@lem4977538) (@lem4977537 A B _62886 s)). Qed.
Lemma lem4977540 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (term518 A B _62886 s P) = (term509 A B _62886 s P).
Proof. exact (eq_refl (term518 A B _62886 s P)). Qed.
Lemma lem4977541 {A B : Type'} (x : type831 A B) (P : B -> Prop) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem4977542 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term526 A B _62886 s x P) = (term527 A B _62886 s x P).
Proof. exact (MK_COMB (@lem4977540 A B _62886 s P) (@lem4977541 A B x P)). Qed.
Lemma lem4977543 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term527 A B _62886 s x P) = (term528 A B _62886 s x P).
Proof. exact (eq_refl (term527 A B _62886 s x P)). Qed.
Lemma lem4977544 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) (P : B -> Prop) : (term526 A B _62886 s x P) = (term528 A B _62886 s x P).
Proof. exact (TRANS (@lem4977542 A B _62886 s x P) (@lem4977543 A B _62886 s x P)). Qed.
Lemma lem4977545 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term529 A B _62886 s x) = (term530 A B _62886 s x).
Proof. exact (fun_ext (fun P : B -> Prop => @lem4977544 A B _62886 s x P)). Qed.
Lemma lem4977546 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4977547 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term531 A B _62886 s x) = (term532 A B _62886 s x).
Proof. exact (MK_COMB (@lem4977546 B) (@lem4977545 A B _62886 s x)). Qed.
Lemma lem4977548 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term533 A B _62886 s) = (term534 A B _62886 s).
Proof. exact (fun_ext (fun x : type831 A B => @lem4977547 A B _62886 s x)). Qed.
Lemma lem4977549 {A B : Type'} : (@ex ((B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4977550 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term516 A B _62886 s) = (term535 A B _62886 s).
Proof. exact (MK_COMB (@lem4977549 A B) (@lem4977548 A B _62886 s)). Qed.
Lemma lem4977551 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : ((term515 A B _62886 s) = (term516 A B _62886 s)) = ((term512 A B _62886 s) = (term535 A B _62886 s)).
Proof. exact (MK_COMB (@lem4977539 A B _62886 s) (@lem4977550 A B _62886 s)). Qed.
Lemma lem4977552 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term512 A B _62886 s) = (term535 A B _62886 s).
Proof. exact (EQ_MP (@lem4977551 A B _62886 s) (@lem4977526 A B _62886 s)). Qed.
Lemma lem4977553 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term421 A B _62886 s) = (term535 A B _62886 s).
Proof. exact (TRANS (@lem4977522 A B _62886 s) (@lem4977552 A B _62886 s)). Qed.
Lemma lem4977554 {A B : Type'} (_62886 : type653 A B) : (term428 A B _62886) = (term536 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977553 A B _62886 s)). Qed.
Lemma lem4977555 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977556 {A B : Type'} (_62886 : type653 A B) : (term443 A B _62886) = (term537 A B _62886).
Proof. exact (MK_COMB (@lem4977555 A) (@lem4977554 A B _62886)). Qed.
Lemma lem4977558 {A B : Type'} (P : type1413 A B) : (term461 A B P) = (term462 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4977559 {A B : Type'} (P : type605 A B) : (term538 A B P) = (term539 A B P).
Proof. exact (@lem4977558 (A -> Prop) (type831 A B) P). Qed.
Lemma lem4977560 {A B : Type'} (_62886 : type653 A B) : (term540 A B _62886) = (term541 A B _62886).
Proof. exact (@lem4977559 A B (term542 A B _62886)). Qed.
Lemma lem4977561 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term543 A B _62886 s) = (term534 A B _62886 s).
Proof. exact (eq_refl (term543 A B _62886 s)). Qed.
Lemma lem4977562 {A B : Type'} (x : type831 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4977563 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term544 A B _62886 s x) = (term545 A B _62886 s x).
Proof. exact (MK_COMB (@lem4977561 A B _62886 s) (@lem4977562 A B x)). Qed.
Lemma lem4977564 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term545 A B _62886 s x) = (term532 A B _62886 s x).
Proof. exact (eq_refl (term545 A B _62886 s x)). Qed.
Lemma lem4977565 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (x : type831 A B) : (term544 A B _62886 s x) = (term532 A B _62886 s x).
Proof. exact (TRANS (@lem4977563 A B _62886 s x) (@lem4977564 A B _62886 s x)). Qed.
Lemma lem4977566 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term546 A B _62886 s) = (term534 A B _62886 s).
Proof. exact (fun_ext (fun x : type831 A B => @lem4977565 A B _62886 s x)). Qed.
Lemma lem4977567 {A B : Type'} : (@ex ((B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4977568 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term547 A B _62886 s) = (term535 A B _62886 s).
Proof. exact (MK_COMB (@lem4977567 A B) (@lem4977566 A B _62886 s)). Qed.
Lemma lem4977569 {A B : Type'} (_62886 : type653 A B) : (term548 A B _62886) = (term536 A B _62886).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977568 A B _62886 s)). Qed.
Lemma lem4977570 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977571 {A B : Type'} (_62886 : type653 A B) : (term540 A B _62886) = (term537 A B _62886).
Proof. exact (MK_COMB (@lem4977570 A) (@lem4977569 A B _62886)). Qed.
Lemma lem4977572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977573 {A B : Type'} (_62886 : type653 A B) : (term549 A B _62886) = (term550 A B _62886).
Proof. exact (MK_COMB (@lem4977572) (@lem4977571 A B _62886)). Qed.
Lemma lem4977574 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (term543 A B _62886 s) = (term534 A B _62886 s).
Proof. exact (eq_refl (term543 A B _62886 s)). Qed.
Lemma lem4977575 {A B : Type'} (x : type652 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4977576 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term551 A B _62886 x s) = (term552 A B _62886 x s).
Proof. exact (MK_COMB (@lem4977574 A B _62886 s) (@lem4977575 A B x s)). Qed.
Lemma lem4977577 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term552 A B _62886 x s) = (term553 A B _62886 x s).
Proof. exact (eq_refl (term552 A B _62886 x s)). Qed.
Lemma lem4977578 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) (s : A -> Prop) : (term551 A B _62886 x s) = (term553 A B _62886 x s).
Proof. exact (TRANS (@lem4977576 A B _62886 x s) (@lem4977577 A B _62886 x s)). Qed.
Lemma lem4977579 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) : (term554 A B _62886 x) = (term555 A B _62886 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4977578 A B _62886 x s)). Qed.
Lemma lem4977580 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4977581 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) : (term556 A B _62886 x) = (term557 A B _62886 x).
Proof. exact (MK_COMB (@lem4977580 A) (@lem4977579 A B _62886 x)). Qed.
Lemma lem4977582 {A B : Type'} (_62886 : type653 A B) : (term558 A B _62886) = (term559 A B _62886).
Proof. exact (fun_ext (fun x : type652 A B => @lem4977581 A B _62886 x)). Qed.
Lemma lem4977583 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4977584 {A B : Type'} (_62886 : type653 A B) : (term541 A B _62886) = (term560 A B _62886).
Proof. exact (MK_COMB (@lem4977583 A B) (@lem4977582 A B _62886)). Qed.
Lemma lem4977585 {A B : Type'} (_62886 : type653 A B) : ((term540 A B _62886) = (term541 A B _62886)) = ((term537 A B _62886) = (term560 A B _62886)).
Proof. exact (MK_COMB (@lem4977573 A B _62886) (@lem4977584 A B _62886)). Qed.
Lemma lem4977586 {A B : Type'} (_62886 : type653 A B) : (term537 A B _62886) = (term560 A B _62886).
Proof. exact (EQ_MP (@lem4977585 A B _62886) (@lem4977560 A B _62886)). Qed.
Lemma lem4977587 {A B : Type'} (_62886 : type653 A B) : (term443 A B _62886) = (term560 A B _62886).
Proof. exact (TRANS (@lem4977556 A B _62886) (@lem4977586 A B _62886)). Qed.
Lemma lem4977588 {A B : Type'} (_62886 : type653 A B) : (term440 A B _62886) = (term440 A B _62886).
Proof. exact (eq_refl (term440 A B _62886)). Qed.
Lemma lem4977589 {A B : Type'} (_62886 : type653 A B) : (term444 A B _62886) = (term561 A B _62886).
Proof. exact (MK_COMB (@lem4977588 A B _62886) (@lem4977587 A B _62886)). Qed.
Lemma lem4977591 {A : Type'} (P : Prop) (Q : A -> Prop) : (term562 A P Q) = (term563 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4977592 {A B : Type'} (P : Prop) (Q : type144 A B) : (term564 A B P Q) = (term565 A B P Q).
Proof. exact (@lem4977591 (type652 A B) P Q). Qed.
Lemma lem4977593 {A B : Type'} (_62886 : type653 A B) : (term566 A B _62886) = (term567 A B _62886).
Proof. exact (@lem4977592 A B (term438 A B _62886) (term559 A B _62886)). Qed.
Lemma lem4977594 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) : (term568 A B _62886 x) = (term557 A B _62886 x).
Proof. exact (eq_refl (term568 A B _62886 x)). Qed.
Lemma lem4977595 {A B : Type'} (_62886 : type653 A B) : (term569 A B _62886) = (term559 A B _62886).
Proof. exact (fun_ext (fun x : type652 A B => @lem4977594 A B _62886 x)). Qed.
Lemma lem4977596 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4977597 {A B : Type'} (_62886 : type653 A B) : (term570 A B _62886) = (term560 A B _62886).
Proof. exact (MK_COMB (@lem4977596 A B) (@lem4977595 A B _62886)). Qed.
Lemma lem4977598 {A B : Type'} (_62886 : type653 A B) : (term440 A B _62886) = (term440 A B _62886).
Proof. exact (eq_refl (term440 A B _62886)). Qed.
Lemma lem4977599 {A B : Type'} (_62886 : type653 A B) : (term566 A B _62886) = (term561 A B _62886).
Proof. exact (MK_COMB (@lem4977598 A B _62886) (@lem4977597 A B _62886)). Qed.
Lemma lem4977600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4977601 {A B : Type'} (_62886 : type653 A B) : (term571 A B _62886) = (term572 A B _62886).
Proof. exact (MK_COMB (@lem4977600) (@lem4977599 A B _62886)). Qed.
Lemma lem4977602 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) : (term568 A B _62886 x) = (term557 A B _62886 x).
Proof. exact (eq_refl (term568 A B _62886 x)). Qed.
Lemma lem4977603 {A B : Type'} (_62886 : type653 A B) : (term440 A B _62886) = (term440 A B _62886).
Proof. exact (eq_refl (term440 A B _62886)). Qed.
Lemma lem4977604 {A B : Type'} (_62886 : type653 A B) (x : type652 A B) : (term573 A B _62886 x) = (term574 A B _62886 x).
Proof. exact (MK_COMB (@lem4977603 A B _62886) (@lem4977602 A B _62886 x)). Qed.
Lemma lem4977605 {A B : Type'} (_62886 : type653 A B) : (term575 A B _62886) = (term576 A B _62886).
Proof. exact (fun_ext (fun x : type652 A B => @lem4977604 A B _62886 x)). Qed.
Lemma lem4977606 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)) = (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> A))). Qed.
Lemma lem4977607 {A B : Type'} (_62886 : type653 A B) : (term567 A B _62886) = (term577 A B _62886).
Proof. exact (MK_COMB (@lem4977606 A B) (@lem4977605 A B _62886)). Qed.
Lemma lem4977608 {A B : Type'} (_62886 : type653 A B) : ((term566 A B _62886) = (term567 A B _62886)) = ((term561 A B _62886) = (term577 A B _62886)).
Proof. exact (MK_COMB (@lem4977601 A B _62886) (@lem4977607 A B _62886)). Qed.
Lemma lem4977609 {A B : Type'} (_62886 : type653 A B) : (term561 A B _62886) = (term577 A B _62886).
Proof. exact (EQ_MP (@lem4977608 A B _62886) (@lem4977593 A B _62886)). Qed.
Lemma lem4977610 {A B : Type'} (_62886 : type653 A B) : (term444 A B _62886) = (term577 A B _62886).
Proof. exact (TRANS (@lem4977589 A B _62886) (@lem4977609 A B _62886)). Qed.
Lemma lem4977611 {A B : Type'} (_62886 : type653 A B) : (term352 A B _62886) = (term577 A B _62886).
Proof. exact (TRANS (@lem4977431 A B _62886) (@lem4977610 A B _62886)). Qed.
Lemma lem4977612 {A B : Type'} (_62886 : type653 A B) : (term319 A B _62886) = (term577 A B _62886).
Proof. exact (TRANS (@lem4976835 A B _62886) (@lem4977611 A B _62886)). Qed.
Lemma lem4977613 {A B : Type'} (_62886 : type653 A B) (h1 : term319 A B _62886) : term577 A B _62886.
Proof. exact (EQ_MP (@lem4977612 A B _62886) (@lem4976788 A B _62886 h1)). Qed.
Lemma lem4977622 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term578 A B s x f y) = (term579 A B s x f y).
Proof. exact (@lem17045 (s y) ((f x) = (f y))). Qed.
Lemma lem4977624 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term580 A s x).
Proof. exact (eq_refl (term580 A s x)). Qed.
Lemma lem4977625 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term581 A B s x f y) = (term582 A B s x f y).
Proof. exact (MK_COMB (@lem4977624 A s x) (@lem4977622 A B s x f y)). Qed.
Lemma lem4977626 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term583 A B s x f y) = (term581 A B s x f y).
Proof. exact (@lem17045 (s x) (term108 A B s x f y)). Qed.
Lemma lem4977627 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term583 A B s x f y) = (term582 A B s x f y).
Proof. exact (TRANS (@lem4977626 A B s x f y) (@lem4977625 A B s x f y)). Qed.
Lemma lem4977628 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4977629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977630 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term584 A B s x f y) = (term585 A B s x f y).
Proof. exact (MK_COMB (@lem4977629) (@lem4977627 A B s x f y)). Qed.
Lemma lem4977631 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term586 A B s f x y) = (term587 A B s f x y).
Proof. exact (MK_COMB (@lem4977630 A B s x f y) (@lem4977628 A x y)). Qed.
Lemma lem4977632 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term586 A B s f x y).
Proof. exact (@lem17265 (term110 A B s x f y) (x = y)). Qed.
Lemma lem4977633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term587 A B s f x y).
Proof. exact (TRANS (@lem4977632 A B s f x y) (@lem4977631 A B s f x y)). Qed.
Lemma lem4977634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term588 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4977633 A B s f x y)). Qed.
Lemma lem4977635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977636 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term589 A B s f x).
Proof. exact (MK_COMB (@lem4977635 A) (@lem4977634 A B s f x)). Qed.
Lemma lem4977637 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term590 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4977636 A B s f x)). Qed.
Lemma lem4977638 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977639 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term591 A B s f).
Proof. exact (MK_COMB (@lem4977638 A) (@lem4977637 A B s f)). Qed.
Lemma lem4977646 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term592 A B x f s x') = (term593 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem4977647 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4977648 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term594 A B x f s) = (term595 A B x f s).
Proof. exact (@lem4977647 A (term125 A B x f s)). Qed.
Lemma lem4977649 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term596 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term596 A B x f s x')). Qed.
Lemma lem4977650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977651 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term597 A B x f s x') = (term592 A B x f s x').
Proof. exact (MK_COMB (@lem4977650) (@lem4977649 A B x f s x')). Qed.
Lemma lem4977652 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term597 A B x f s x') = (term593 A B x f s x').
Proof. exact (TRANS (@lem4977651 A B x f s x') (@lem4977646 A B x f s x')). Qed.
Lemma lem4977653 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term598 A B x f s) = (term599 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4977652 A B x f s x')). Qed.
Lemma lem4977654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977655 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term595 A B x f s) = (term600 A B x f s).
Proof. exact (MK_COMB (@lem4977654 A) (@lem4977653 A B x f s)). Qed.
Lemma lem4977656 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term594 A B x f s) = (term600 A B x f s).
Proof. exact (TRANS (@lem4977648 A B x f s) (@lem4977655 A B x f s)). Qed.
Lemma lem4977657 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4977658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977659 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term601 A B x f s) = (term602 A B x f s).
Proof. exact (MK_COMB (@lem4977658) (@lem4977656 A B x f s)). Qed.
Lemma lem4977660 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term603 A B f s t x) = (term604 A B f s t x).
Proof. exact (MK_COMB (@lem4977659 A B x f s) (@lem4977657 B t x)). Qed.
Lemma lem4977661 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term603 A B f s t x).
Proof. exact (@lem17265 (term126 A B x f s) (t x)). Qed.
Lemma lem4977662 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term130 A B f s t x) = (term604 A B f s t x).
Proof. exact (TRANS (@lem4977661 A B f s t x) (@lem4977660 A B f s t x)). Qed.
Lemma lem4977663 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term132 A B f s t) = (term605 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4977662 A B f s t x)). Qed.
Lemma lem4977664 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4977665 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term133 A B f s t) = (term606 A B f s t).
Proof. exact (MK_COMB (@lem4977664 B) (@lem4977663 A B f s t)). Qed.
Lemma lem4977674 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term66 A B t s).
Proof. exact (eq_refl (term66 A B t s)). Qed.
Lemma lem4977675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977676 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term134 A B f s t) = (term607 A B f s t).
Proof. exact (MK_COMB (@lem4977675) (@lem4977665 A B f s t)). Qed.
Lemma lem4977677 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term135 A B f t s) = (term608 A B f t s).
Proof. exact (MK_COMB (@lem4977676 A B f s t) (@lem4977674 A B t s)). Qed.
Lemma lem4977678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977679 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term609 A B s f).
Proof. exact (MK_COMB (@lem4977678) (@lem4977639 A B s f)). Qed.
Lemma lem4977680 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term136 A B f t s) = (term610 A B f t s).
Proof. exact (MK_COMB (@lem4977679 A B s f) (@lem4977677 A B f t s)). Qed.
Lemma lem4977682 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62886 s P f n) = (term238 A B _62886 s P f n).
Proof. exact (eq_refl (term238 A B _62886 s P f n)). Qed.
Lemma lem4977819 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term239 A B _62886 P n f t s) = (term611 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4977682 A B _62886 s P f n) (@lem4977680 A B f t s)). Qed.
Lemma lem4977820 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term611 A B _62886 P n f t s.
Proof. exact (EQ_MP (@lem4977819 A B _62886 P n f t s) (@lem4976789 A B _62886 P n f t s h1)). Qed.
Lemma lem4977842 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term950 A B s P x f y.
Proof. exact (h1). Qed.
Lemma lem4977848 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term843 A x y.
Proof. exact (h1). Qed.
Lemma lem4977854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977855 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4977854 (A -> Prop) Prop f x). Qed.
Lemma lem4977857 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem4977855 A (@FINITE A) s). Qed.
Lemma lem4977862 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977863 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4977862 (B -> Prop) Prop f x). Qed.
Lemma lem4977865 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@I ((B -> Prop) -> Prop) (@FINITE B) t).
Proof. exact (@lem4977863 B (@FINITE B) t). Qed.
Lemma lem4977866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977867 {B : Type'} (t : B -> Prop) : (term39 B t) = (term703 B t).
Proof. exact (MK_COMB (@lem4977866) (@lem4977865 B t)). Qed.
Lemma lem4977868 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term65 A B t s) = (term704 A B t s).
Proof. exact (MK_COMB (@lem4977867 B t) (@lem4977857 A s)). Qed.
Lemma lem4977869 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4977874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977875 {A : Type'} (f : type687 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat) f x).
Proof. exact (@lem4977874 (A -> Prop) nat f x). Qed.
Lemma lem4977877 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@I ((A -> Prop) -> nat) (@CARD A) s).
Proof. exact (@lem4977875 A (@CARD A) s). Qed.
Lemma lem4977882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977883 {B : Type'} (f : type687 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> nat) f x).
Proof. exact (@lem4977882 (B -> Prop) nat f x). Qed.
Lemma lem4977885 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@I ((B -> Prop) -> nat) (@CARD B) t).
Proof. exact (@lem4977883 B (@CARD B) t). Qed.
Lemma lem4977886 {A : Type'} (s : A -> Prop) : (term40 A s) = (term705 A s).
Proof. exact (MK_COMB (@lem4977869) (@lem4977877 A s)). Qed.
Lemma lem4977887 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((@CARD A s) = (@CARD B t)) = ((@I ((A -> Prop) -> nat) (@CARD A) s) = (@I ((B -> Prop) -> nat) (@CARD B) t)).
Proof. exact (MK_COMB (@lem4977886 A s) (@lem4977885 B t)). Qed.
Lemma lem4977888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977889 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term41 A B s t) = (term706 A B s t).
Proof. exact (MK_COMB (@lem4977888) (@lem4977887 A B s t)). Qed.
Lemma lem4977890 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term66 A B t s) = (term707 A B t s).
Proof. exact (MK_COMB (@lem4977889 A B s t) (@lem4977868 A B t s)). Qed.
Lemma lem4977895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977896 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4977895 B Prop f x). Qed.
Lemma lem4977898 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem4977896 B t x). Qed.
Lemma lem4977899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977904 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977905 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4977904 A Prop f x). Qed.
Lemma lem4977907 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4977905 A s x). Qed.
Lemma lem4977908 {A : Type'} (s : A -> Prop) (x : A) : (term617 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem4977899) (@lem4977907 A s x)). Qed.
Lemma lem4977909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977916 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4977916 A B f x). Qed.
Lemma lem4977919 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4977920 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem4977919 B x) (@lem4977918 A B f x')). Qed.
Lemma lem4977921 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term709 A B x f x') = (term710 A B x f x').
Proof. exact (MK_COMB (@lem4977909) (@lem4977920 A B x f x')). Qed.
Lemma lem4977922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977923 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term657 A B x f x') = (term711 A B x f x').
Proof. exact (MK_COMB (@lem4977922) (@lem4977921 A B x f x')). Qed.
Lemma lem4977924 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term593 A B x f s x') = (term712 A B x f s x').
Proof. exact (MK_COMB (@lem4977923 A B x f x') (@lem4977908 A s x')). Qed.
Lemma lem4977925 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term599 A B x f s) = (term713 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4977924 A B x f s x')). Qed.
Lemma lem4977926 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977927 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term600 A B x f s) = (term714 A B x f s).
Proof. exact (MK_COMB (@lem4977926 A) (@lem4977925 A B x f s)). Qed.
Lemma lem4977928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977929 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term602 A B x f s) = (term715 A B x f s).
Proof. exact (MK_COMB (@lem4977928) (@lem4977927 A B x f s)). Qed.
Lemma lem4977930 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term604 A B f s t x) = (term716 A B f s t x).
Proof. exact (MK_COMB (@lem4977929 A B x f s) (@lem4977898 B t x)). Qed.
Lemma lem4977931 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term605 A B f s t) = (term717 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4977930 A B f s t x)). Qed.
Lemma lem4977932 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4977933 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term606 A B f s t) = (term718 A B f s t).
Proof. exact (MK_COMB (@lem4977932 B) (@lem4977931 A B f s t)). Qed.
Lemma lem4977934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977935 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term607 A B f s t) = (term719 A B f s t).
Proof. exact (MK_COMB (@lem4977934) (@lem4977933 A B f s t)). Qed.
Lemma lem4977936 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term608 A B f t s) = (term720 A B f t s).
Proof. exact (MK_COMB (@lem4977935 A B f s t) (@lem4977890 A B t s)). Qed.
Lemma lem4977941 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4977942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977943 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4977948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4977948 A B f x). Qed.
Lemma lem4977955 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4977955 A B f x). Qed.
Lemma lem4977958 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4977956 A B f y). Qed.
Lemma lem4977959 {A B : Type'} (f : A -> B) (x : A) : (term721 A B f x) = (term722 A B f x).
Proof. exact (MK_COMB (@lem4977943 B) (@lem4977950 A B f x)). Qed.
Lemma lem4977960 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem4977959 A B f x) (@lem4977958 A B f y)). Qed.
Lemma lem4977961 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term723 A B x f y) = (term724 A B x f y).
Proof. exact (MK_COMB (@lem4977942) (@lem4977960 A B x f y)). Qed.
Lemma lem4977962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977968 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4977967 A Prop f x). Qed.
Lemma lem4977970 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem4977968 A s y). Qed.
Lemma lem4977971 {A : Type'} (s : A -> Prop) (y : A) : (term617 A s y) = (term708 A s y).
Proof. exact (MK_COMB (@lem4977962) (@lem4977970 A s y)). Qed.
Lemma lem4977972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977973 {A : Type'} (s : A -> Prop) (y : A) : (term580 A s y) = (term725 A s y).
Proof. exact (MK_COMB (@lem4977972) (@lem4977971 A s y)). Qed.
Lemma lem4977974 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term579 A B s x f y) = (term726 A B s x f y).
Proof. exact (MK_COMB (@lem4977973 A s y) (@lem4977961 A B x f y)). Qed.
Lemma lem4977975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4977980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4977981 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4977980 A Prop f x). Qed.
Lemma lem4977983 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4977981 A s x). Qed.
Lemma lem4977984 {A : Type'} (s : A -> Prop) (x : A) : (term617 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem4977975) (@lem4977983 A s x)). Qed.
Lemma lem4977985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977986 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term725 A s x).
Proof. exact (MK_COMB (@lem4977985) (@lem4977984 A s x)). Qed.
Lemma lem4977987 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term582 A B s x f y) = (term727 A B s x f y).
Proof. exact (MK_COMB (@lem4977986 A s x) (@lem4977974 A B s x f y)). Qed.
Lemma lem4977988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4977989 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term585 A B s x f y) = (term728 A B s x f y).
Proof. exact (MK_COMB (@lem4977988) (@lem4977987 A B s x f y)). Qed.
Lemma lem4977990 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term587 A B s f x y) = (term729 A B s f x y).
Proof. exact (MK_COMB (@lem4977989 A B s x f y) (@lem4977941 A x y)). Qed.
Lemma lem4977991 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term588 A B s f x) = (term730 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4977990 A B s f x y)). Qed.
Lemma lem4977992 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977993 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term589 A B s f x) = (term731 A B s f x).
Proof. exact (MK_COMB (@lem4977992 A) (@lem4977991 A B s f x)). Qed.
Lemma lem4977994 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term590 A B s f) = (term732 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4977993 A B s f x)). Qed.
Lemma lem4977995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4977996 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term591 A B s f) = (term733 A B s f).
Proof. exact (MK_COMB (@lem4977995 A) (@lem4977994 A B s f)). Qed.
Lemma lem4977997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4977998 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term609 A B s f) = (term734 A B s f).
Proof. exact (MK_COMB (@lem4977997) (@lem4977996 A B s f)). Qed.
Lemma lem4977999 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term610 A B f t s) = (term735 A B f t s).
Proof. exact (MK_COMB (@lem4977998 A B s f) (@lem4977936 A B f t s)). Qed.
Lemma lem4978000 {A : Type'} : (@HAS_SIZE A) = (@HAS_SIZE A).
Proof. exact (eq_refl (@HAS_SIZE A)). Qed.
Lemma lem4978001 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4978010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978011 {A B : Type'} (f : type653 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) f x).
Proof. exact (@lem4978010 (A -> Prop) (type832 A B) f x). Qed.
Lemma lem4978012 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) : (_62886 s) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886 s).
Proof. exact (@lem4978011 A B _62886 s). Qed.
Lemma lem4978013 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4978014 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (_62886 s P) = (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886 s P).
Proof. exact (MK_COMB (@lem4978012 A B _62886 s) (@lem4978013 B P)). Qed.
Lemma lem4978016 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978017 {A B : Type'} (f : type832 A B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (A -> B) -> A -> Prop) f x).
Proof. exact (@lem4978016 (B -> Prop) (type551 A B) f x). Qed.
Lemma lem4978018 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886 s P) = (term736 A B _62886 s P).
Proof. exact (@lem4978017 A B (@I ((A -> Prop) -> (B -> Prop) -> (A -> B) -> A -> Prop) _62886 s) P). Qed.
Lemma lem4978019 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) : (_62886 s P) = (term736 A B _62886 s P).
Proof. exact (TRANS (@lem4978014 A B _62886 s P) (@lem4978018 A B _62886 s P)). Qed.
Lemma lem4978020 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4978021 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (_62886 s P f) = (term737 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4978019 A B _62886 s P) (@lem4978020 A B f)). Qed.
Lemma lem4978023 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978024 {A B : Type'} (f : type551 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> Prop) f x).
Proof. exact (@lem4978023 (A -> B) (A -> Prop) f x). Qed.
Lemma lem4978025 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term737 A B _62886 s P f) = (term738 A B _62886 s P f).
Proof. exact (@lem4978024 A B (term736 A B _62886 s P) f). Qed.
Lemma lem4978027 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (_62886 s P f) = (term738 A B _62886 s P f).
Proof. exact (TRANS (@lem4978021 A B _62886 s P f) (@lem4978025 A B _62886 s P f)). Qed.
Lemma lem4978028 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term235 A B _62886 s P f) = (term739 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4978001 A) (@lem4978027 A B _62886 s P f)). Qed.
Lemma lem4978030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978031 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4978030 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4978032 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term739 A B _62886 s P f) = (term740 A B _62886 s P f).
Proof. exact (@lem4978031 A (@GSPEC A) (term738 A B _62886 s P f)). Qed.
Lemma lem4978033 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term235 A B _62886 s P f) = (term740 A B _62886 s P f).
Proof. exact (TRANS (@lem4978028 A B _62886 s P f) (@lem4978032 A B _62886 s P f)). Qed.
Lemma lem4978034 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4978035 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term236 A B _62886 s P f) = (term741 A B _62886 s P f).
Proof. exact (MK_COMB (@lem4978000 A) (@lem4978033 A B _62886 s P f)). Qed.
Lemma lem4978036 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term237 A B _62886 s P f n) = (term742 A B _62886 s P f n).
Proof. exact (MK_COMB (@lem4978035 A B _62886 s P f) (@lem4978034 n)). Qed.
Lemma lem4978038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978039 {A : Type'} (f : type682 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> nat -> Prop) f x).
Proof. exact (@lem4978038 (A -> Prop) (nat -> Prop) f x). Qed.
Lemma lem4978040 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term741 A B _62886 s P f) = (term743 A B _62886 s P f).
Proof. exact (@lem4978039 A (@HAS_SIZE A) (term740 A B _62886 s P f)). Qed.
Lemma lem4978041 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4978042 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term742 A B _62886 s P f n) = (term744 A B _62886 s P f n).
Proof. exact (MK_COMB (@lem4978040 A B _62886 s P f) (@lem4978041 n)). Qed.
Lemma lem4978044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978045 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem4978044 nat Prop f x). Qed.
Lemma lem4978046 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term744 A B _62886 s P f n) = (term745 A B _62886 s P f n).
Proof. exact (@lem4978045 (term743 A B _62886 s P f) n). Qed.
Lemma lem4978047 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term742 A B _62886 s P f n) = (term745 A B _62886 s P f n).
Proof. exact (TRANS (@lem4978042 A B _62886 s P f n) (@lem4978046 A B _62886 s P f n)). Qed.
Lemma lem4978048 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term237 A B _62886 s P f n) = (term745 A B _62886 s P f n).
Proof. exact (TRANS (@lem4978036 A B _62886 s P f n) (@lem4978047 A B _62886 s P f n)). Qed.
Lemma lem4978049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4978050 {A B : Type'} (_62886 : type653 A B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : (term238 A B _62886 s P f n) = (term746 A B _62886 s P f n).
Proof. exact (MK_COMB (@lem4978049) (@lem4978048 A B _62886 s P f n)). Qed.
Lemma lem4978051 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term611 A B _62886 P n f t s) = (term747 A B _62886 P n f t s).
Proof. exact (MK_COMB (@lem4978050 A B _62886 s P f n) (@lem4977999 A B f t s)). Qed.
Lemma lem4978052 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term747 A B _62886 P n f t s.
Proof. exact (EQ_MP (@lem4978051 A B _62886 P n f t s) (@lem4977820 A B _62886 P n f t s h1)). Qed.
Lemma lem4978053 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4978058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4978058 A B f x). Qed.
Lemma lem4978065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4978065 A B f x). Qed.
Lemma lem4978068 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4978066 A B f y). Qed.
Lemma lem4978069 {A B : Type'} (f : A -> B) (x : A) : (term721 A B f x) = (term722 A B f x).
Proof. exact (MK_COMB (@lem4978053 B) (@lem4978060 A B f x)). Qed.
Lemma lem4978070 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem4978069 A B f x) (@lem4978068 A B f y)). Qed.
Lemma lem4978071 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4978076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4978076 A B f x). Qed.
Lemma lem4978079 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4978077 A B f y). Qed.
Lemma lem4978080 {A B : Type'} (P : B -> Prop) (f : A -> B) (y : A) : (term88 A B P f y) = (term748 A B P f y).
Proof. exact (MK_COMB (@lem4978071 B P) (@lem4978079 A B f y)). Qed.
Lemma lem4978082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978083 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4978082 B Prop f x). Qed.
Lemma lem4978084 {A B : Type'} (P : B -> Prop) (f : A -> B) (y : A) : (term748 A B P f y) = (term749 A B P f y).
Proof. exact (@lem4978083 B P (@I (A -> B) f y)). Qed.
Lemma lem4978085 {A B : Type'} (P : B -> Prop) (f : A -> B) (y : A) : (term88 A B P f y) = (term749 A B P f y).
Proof. exact (TRANS (@lem4978080 A B P f y) (@lem4978084 A B P f y)). Qed.
Lemma lem4978090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978091 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4978090 A Prop f x). Qed.
Lemma lem4978093 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem4978091 A s y). Qed.
Lemma lem4978094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4978095 {A : Type'} (s : A -> Prop) (y : A) : (term87 A s y) = (term750 A s y).
Proof. exact (MK_COMB (@lem4978094) (@lem4978093 A s y)). Qed.
Lemma lem4978096 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term90 A B s P f y) = (term751 A B s P f y).
Proof. exact (MK_COMB (@lem4978095 A s y) (@lem4978085 A B P f y)). Qed.
Lemma lem4978097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4978098 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (y : A) : (term946 A B s P f y) = (term1023 A B s P f y).
Proof. exact (MK_COMB (@lem4978097) (@lem4978096 A B s P f y)). Qed.
Lemma lem4978099 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) : (term948 A B s P x f y) = (term1024 A B s P x f y).
Proof. exact (MK_COMB (@lem4978098 A B s P f y) (@lem4978070 A B x f y)). Qed.
Lemma lem4978100 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4978105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4978105 A B f x). Qed.
Lemma lem4978108 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term748 A B P f x).
Proof. exact (MK_COMB (@lem4978100 B P) (@lem4978107 A B f x)). Qed.
Lemma lem4978110 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978111 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem4978110 B Prop f x). Qed.
Lemma lem4978112 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term748 A B P f x) = (term749 A B P f x).
Proof. exact (@lem4978111 B P (@I (A -> B) f x)). Qed.
Lemma lem4978113 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term88 A B P f x) = (term749 A B P f x).
Proof. exact (TRANS (@lem4978108 A B P f x) (@lem4978112 A B P f x)). Qed.
Lemma lem4978118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4978119 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4978118 A Prop f x). Qed.
Lemma lem4978121 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4978119 A s x). Qed.
Lemma lem4978122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4978123 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (term750 A s x).
Proof. exact (MK_COMB (@lem4978122) (@lem4978121 A s x)). Qed.
Lemma lem4978124 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term90 A B s P f x) = (term751 A B s P f x).
Proof. exact (MK_COMB (@lem4978123 A s x) (@lem4978113 A B P f x)). Qed.
Lemma lem4978125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4978126 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term946 A B s P f x) = (term1023 A B s P f x).
Proof. exact (MK_COMB (@lem4978125) (@lem4978124 A B s P f x)). Qed.
Lemma lem4978127 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) : (term950 A B s P x f y) = (term1025 A B s P x f y).
Proof. exact (MK_COMB (@lem4978126 A B s P f x) (@lem4978099 A B s P x f y)). Qed.
Lemma lem4978128 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term1025 A B s P x f y.
Proof. exact (EQ_MP (@lem4978127 A B s P x f y) (@lem4977842 A B s P x f y h1)). Qed.
Lemma lem4978136 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term843 A x y.
Proof. exact (h1). Qed.
Lemma lem4978453 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term1024 A B s P x f y.
Proof. exact (proj2 (@lem4978128 A B s P x f y h1)). Qed.
Lemma lem4978454 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term751 A B s P f x.
Proof. exact (proj1 (@lem4978128 A B s P x f y h1)). Qed.
Lemma lem4978456 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term751 A B s P f y.
Proof. exact (proj1 (@lem4978453 A B s P x f y h1)). Qed.
Lemma lem4978461 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term735 A B f t s.
Proof. exact (proj2 (@lem4978052 A B _62886 P n f t s h1)). Qed.
Lemma lem4978464 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term733 A B s f.
Proof. exact (proj1 (@lem4978461 A B _62886 P n f t s h1)). Qed.
Lemma lem4978474 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term843 A x y.
Proof. exact (h1). Qed.
Lemma lem4978596 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term729 A B s f x y) = (term729 A B s f x y).
Proof. exact (eq_refl (term729 A B s f x y)). Qed.
Lemma lem4978597 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term730 A B s f x) = (term730 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4978596 A B s f x y)). Qed.
Lemma lem4978598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4978599 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term731 A B s f x) = (term731 A B s f x).
Proof. exact (MK_COMB (@lem4978598 A) (@lem4978597 A B s f x)). Qed.
Lemma lem4978600 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term732 A B s f) = (term732 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4978599 A B s f x)). Qed.
Lemma lem4978601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4978603 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term733 A B s f) = (term733 A B s f).
Proof. exact (MK_COMB (@lem4978601 A) (@lem4978600 A B s f)). Qed.
Lemma lem4978604 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term733 A B s f.
Proof. exact (EQ_MP (@lem4978603 A B s f) (@lem4978464 A B _62886 P n f t s h1)). Qed.
Lemma lem4978692 {A B : Type'} (_62896 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1026 A B s f _62896.
Proof. exact (@lem4978604 A B _62886 P n f t s h1 _62896). Qed.
Lemma lem4978693 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) : (term1026 A B s f _62896) = (term731 A B s f _62896).
Proof. exact (eq_refl (term1026 A B s f _62896)). Qed.
Lemma lem4978694 {A B : Type'} (_62896 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term731 A B s f _62896.
Proof. exact (EQ_MP (@lem4978693 A B s f _62896) (@lem4978692 A B _62896 _62886 P n f t s h1)). Qed.
Lemma lem4978695 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1027 A B s f _62896 _62897.
Proof. exact (@lem4978694 A B _62896 _62886 P n f t s h1 _62897). Qed.
Lemma lem4978696 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1027 A B s f _62896 _62897) = (term729 A B s f _62896 _62897).
Proof. exact (eq_refl (term1027 A B s f _62896 _62897)). Qed.
Lemma lem4978697 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term729 A B s f _62896 _62897.
Proof. exact (EQ_MP (@lem4978696 A B s f _62896 _62897) (@lem4978695 A B _62896 _62897 _62886 P n f t s h1)). Qed.
Lemma lem4978705 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term843 A x y.
Proof. exact (h1). Qed.
Lemma lem4978733 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term729 A B s f _62896 _62897) = (term1028 A B s f _62896 _62897).
Proof. exact (@lem4975619 (term708 A s _62896) (term726 A B s _62896 f _62897) (_62896 = _62897)). Qed.
Lemma lem4978740 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1029 A B s f _62896 _62897) = (term1030 A B s f _62896 _62897).
Proof. exact (@lem4975619 (term708 A s _62897) (term724 A B _62896 f _62897) (_62896 = _62897)). Qed.
Lemma lem4978741 {A : Type'} (s : A -> Prop) (_62896 : A) : (term725 A s _62896) = (term725 A s _62896).
Proof. exact (eq_refl (term725 A s _62896)). Qed.
Lemma lem4978744 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1028 A B s f _62896 _62897) = (term1031 A B s f _62896 _62897).
Proof. exact (MK_COMB (@lem4978741 A s _62896) (@lem4978740 A B s f _62896 _62897)). Qed.
Lemma lem4978746 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term729 A B s f _62896 _62897) = (term1031 A B s f _62896 _62897).
Proof. exact (TRANS (@lem4978733 A B s f _62896 _62897) (@lem4978744 A B s f _62896 _62897)). Qed.
Lemma lem4978747 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1031 A B s f _62896 _62897.
Proof. exact (EQ_MP (@lem4978746 A B s f _62896 _62897) (@lem4978697 A B _62896 _62897 _62886 P n f t s h1)). Qed.
Lemma lem4979161 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4978454 A B s P x f y h1)). Qed.
Lemma lem4979162 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term826 A s x.
Proof. exact (fun h0 : term708 A s x => @lem4979161 A B s P x f y h1). Qed.
Lemma lem4979164 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4979165 {A : Type'} (s : A -> Prop) (x : A) : (term826 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4979164 (@I (A -> Prop) s x)). Qed.
Lemma lem4979166 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4979165 A s x) (@lem4979162 A B s P x f y h1)). Qed.
Lemma lem4979168 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : @I (A -> Prop) s y.
Proof. exact (proj1 (@lem4978456 A B s P x f y h1)). Qed.
Lemma lem4979169 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term826 A s y.
Proof. exact (fun h0 : term708 A s y => @lem4979168 A B s P x f y h1). Qed.
Lemma lem4979171 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4979172 {A : Type'} (s : A -> Prop) (y : A) : (term826 A s y) = (@I (A -> Prop) s y).
Proof. exact (@lem4979171 (@I (A -> Prop) s y)). Qed.
Lemma lem4979173 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : @I (A -> Prop) s y.
Proof. exact (EQ_MP (@lem4979172 A s y) (@lem4979169 A B s P x f y h1)). Qed.
Lemma lem4979175 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (proj2 (@lem4978453 A B s P x f y h1)). Qed.
Lemma lem4979176 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term1032 A B x f y.
Proof. exact (fun h0 : term724 A B x f y => @lem4979175 A B s P x f y h1). Qed.
Lemma lem4979178 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4979179 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1032 A B x f y) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (@lem4979178 ((@I (A -> B) f x) = (@I (A -> B) f y))). Qed.
Lemma lem4979180 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem4979179 A B x f y) (@lem4979176 A B s P x f y h1)). Qed.
Lemma lem4979196 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4979197 {A B : Type'} (f : A -> B) (s : A -> Prop) (_62896 : A) (_62897 : A) : (term1030 A B s f _62896 _62897) = (term1033 A B f s _62896 _62897).
Proof. exact (@lem4979196 (term724 A B _62896 f _62897) (term708 A s _62897) (_62896 = _62897)). Qed.
Lemma lem4979213 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4979214 {A : Type'} (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1034 A s _62896 _62897) = (term1035 A _62896 s _62897).
Proof. exact (@lem4979213 (_62896 = _62897) (term708 A s _62897)). Qed.
Lemma lem4979222 {A B : Type'} (_62896 : A) (f : A -> B) (_62897 : A) : (term1036 A B _62896 f _62897) = (term1036 A B _62896 f _62897).
Proof. exact (eq_refl (term1036 A B _62896 f _62897)). Qed.
Lemma lem4979223 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1033 A B f s _62896 _62897) = (term1037 A B f _62896 s _62897).
Proof. exact (MK_COMB (@lem4979222 A B _62896 f _62897) (@lem4979214 A _62896 s _62897)). Qed.
Lemma lem4979227 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4979228 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term1037 A B f _62896 s _62897) = (term1038 A B _62896 f s _62897).
Proof. exact (@lem4979227 (_62896 = _62897) (term724 A B _62896 f _62897) (term708 A s _62897)). Qed.
Lemma lem4979248 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term1033 A B f s _62896 _62897) = (term1038 A B _62896 f s _62897).
Proof. exact (TRANS (@lem4979223 A B f _62896 s _62897) (@lem4979228 A B _62896 f s _62897)). Qed.
Lemma lem4979249 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term1030 A B s f _62896 _62897) = (term1038 A B _62896 f s _62897).
Proof. exact (TRANS (@lem4979197 A B f s _62896 _62897) (@lem4979248 A B _62896 f s _62897)). Qed.
Lemma lem4979250 {A : Type'} (s : A -> Prop) (_62896 : A) : (term725 A s _62896) = (term725 A s _62896).
Proof. exact (eq_refl (term725 A s _62896)). Qed.
Lemma lem4979251 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term1031 A B s f _62896 _62897) = (term1039 A B _62896 f s _62897).
Proof. exact (MK_COMB (@lem4979250 A s _62896) (@lem4979249 A B _62896 f s _62897)). Qed.
Lemma lem4979255 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4979256 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term1039 A B _62896 f s _62897) = (term1040 A B _62896 f s _62897).
Proof. exact (@lem4979255 (_62896 = _62897) (term708 A s _62896) (term1041 A B _62896 f s _62897)). Qed.
Lemma lem4979272 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4979273 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1042 A B _62896 f s _62897) = (term1043 A B f _62896 s _62897).
Proof. exact (@lem4979272 (term724 A B _62896 f _62897) (term708 A s _62896) (term708 A s _62897)). Qed.
Lemma lem4979291 {A : Type'} (_62896 : A) (_62897 : A) : (term1044 A _62896 _62897) = (term1044 A _62896 _62897).
Proof. exact (eq_refl (term1044 A _62896 _62897)). Qed.
Lemma lem4979292 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1040 A B _62896 f s _62897) = (term1045 A B f _62896 s _62897).
Proof. exact (MK_COMB (@lem4979291 A _62896 _62897) (@lem4979273 A B f _62896 s _62897)). Qed.
Lemma lem4979303 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1039 A B _62896 f s _62897) = (term1045 A B f _62896 s _62897).
Proof. exact (TRANS (@lem4979256 A B _62896 f s _62897) (@lem4979292 A B f _62896 s _62897)). Qed.
Lemma lem4979304 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1031 A B s f _62896 _62897) = (term1045 A B f _62896 s _62897).
Proof. exact (TRANS (@lem4979251 A B _62896 f s _62897) (@lem4979303 A B f _62896 s _62897)). Qed.
Lemma lem4979305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4979306 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1046 A B s f _62896 _62897) = (term1047 A B f _62896 s _62897).
Proof. exact (MK_COMB (@lem4979305) (@lem4979304 A B f _62896 s _62897)). Qed.
Lemma lem4979332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4979333 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term726 A B s _62896 f _62897) = (term1041 A B _62896 f s _62897).
Proof. exact (@lem4979332 (term724 A B _62896 f _62897) (term708 A s _62897)). Qed.
Lemma lem4979341 {A : Type'} (s : A -> Prop) (_62896 : A) : (term725 A s _62896) = (term725 A s _62896).
Proof. exact (eq_refl (term725 A s _62896)). Qed.
Lemma lem4979342 {A B : Type'} (_62896 : A) (f : A -> B) (s : A -> Prop) (_62897 : A) : (term727 A B s _62896 f _62897) = (term1042 A B _62896 f s _62897).
Proof. exact (MK_COMB (@lem4979341 A s _62896) (@lem4979333 A B _62896 f s _62897)). Qed.
Lemma lem4979346 (q : Prop) (p : Prop) (r : Prop) : (term63 p q r) = (term63 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4979347 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1042 A B _62896 f s _62897) = (term1043 A B f _62896 s _62897).
Proof. exact (@lem4979346 (term724 A B _62896 f _62897) (term708 A s _62896) (term708 A s _62897)). Qed.
Lemma lem4979365 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term727 A B s _62896 f _62897) = (term1043 A B f _62896 s _62897).
Proof. exact (TRANS (@lem4979342 A B _62896 f s _62897) (@lem4979347 A B f _62896 s _62897)). Qed.
Lemma lem4979366 {A : Type'} (_62896 : A) (_62897 : A) : (term1044 A _62896 _62897) = (term1044 A _62896 _62897).
Proof. exact (eq_refl (term1044 A _62896 _62897)). Qed.
Lemma lem4979367 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : (term1048 A B s _62896 f _62897) = (term1045 A B f _62896 s _62897).
Proof. exact (MK_COMB (@lem4979366 A _62896 _62897) (@lem4979365 A B f _62896 s _62897)). Qed.
Lemma lem4979378 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : ((term1031 A B s f _62896 _62897) = (term1048 A B s _62896 f _62897)) = ((term1045 A B f _62896 s _62897) = (term1045 A B f _62896 s _62897)).
Proof. exact (MK_COMB (@lem4979306 A B f _62896 s _62897) (@lem4979367 A B f _62896 s _62897)). Qed.
Lemma lem4979380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4979381 (x : Prop) : (x = x) = True.
Proof. exact (@lem4979380 Prop x). Qed.
Lemma lem4979382 {A B : Type'} (f : A -> B) (_62896 : A) (s : A -> Prop) (_62897 : A) : ((term1045 A B f _62896 s _62897) = (term1045 A B f _62896 s _62897)) = True.
Proof. exact (@lem4979381 (term1045 A B f _62896 s _62897)). Qed.
Lemma lem4979383 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : ((term1031 A B s f _62896 _62897) = (term1048 A B s _62896 f _62897)) = True.
Proof. exact (TRANS (@lem4979378 A B f _62896 s _62897) (@lem4979382 A B f _62896 s _62897)). Qed.
Lemma lem4979384 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : True = ((term1031 A B s f _62896 _62897) = (term1048 A B s _62896 f _62897)).
Proof. exact (SYM (@lem4979383 A B s _62896 f _62897)). Qed.
Lemma lem4979385 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1031 A B s f _62896 _62897) = (term1048 A B s _62896 f _62897).
Proof. exact (EQ_MP (@lem4979384 A B s _62896 f _62897) (@lem0)). Qed.
Lemma lem4979386 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1048 A B s _62896 f _62897.
Proof. exact (EQ_MP (@lem4979385 A B s _62896 f _62897) (@lem4978747 A B _62896 _62897 _62886 P n f t s h1)). Qed.
Lemma lem4979388 (b : Prop) (a : Prop) : (a \/ b) = (term831 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4979389 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1048 A B s _62896 f _62897) = (term1049 A B s f _62896 _62897).
Proof. exact (@lem4979388 (term727 A B s _62896 f _62897) (_62896 = _62897)). Qed.
Lemma lem4979391 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4979392 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1050 A B s _62896 f _62897) = (term1051 A B s _62896 f _62897).
Proof. exact (@lem4979391 (term708 A s _62896) (term726 A B s _62896 f _62897)). Qed.
Lemma lem4979394 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4979395 {A : Type'} (s : A -> Prop) (_62896 : A) : (term833 A s _62896) = (@I (A -> Prop) s _62896).
Proof. exact (@lem4979394 (@I (A -> Prop) s _62896)). Qed.
Lemma lem4979396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4979397 {A : Type'} (s : A -> Prop) (_62896 : A) : (term1052 A s _62896) = (term750 A s _62896).
Proof. exact (MK_COMB (@lem4979396) (@lem4979395 A s _62896)). Qed.
Lemma lem4979399 (a : Prop) (b : Prop) : (term851 a b) = (term852 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4979400 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1053 A B s _62896 f _62897) = (term1054 A B s _62896 f _62897).
Proof. exact (@lem4979399 (term708 A s _62897) (term724 A B _62896 f _62897)). Qed.
Lemma lem4979402 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4979403 {A : Type'} (s : A -> Prop) (_62897 : A) : (term833 A s _62897) = (@I (A -> Prop) s _62897).
Proof. exact (@lem4979402 (@I (A -> Prop) s _62897)). Qed.
Lemma lem4979404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4979405 {A : Type'} (s : A -> Prop) (_62897 : A) : (term1052 A s _62897) = (term750 A s _62897).
Proof. exact (MK_COMB (@lem4979404) (@lem4979403 A s _62897)). Qed.
Lemma lem4979407 (a : Prop) : (term205 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4979408 {A B : Type'} (_62896 : A) (f : A -> B) (_62897 : A) : (term1055 A B _62896 f _62897) = ((@I (A -> B) f _62896) = (@I (A -> B) f _62897)).
Proof. exact (@lem4979407 ((@I (A -> B) f _62896) = (@I (A -> B) f _62897))). Qed.
Lemma lem4979409 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1054 A B s _62896 f _62897) = (term1056 A B s _62896 f _62897).
Proof. exact (MK_COMB (@lem4979405 A s _62897) (@lem4979408 A B _62896 f _62897)). Qed.
Lemma lem4979410 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1053 A B s _62896 f _62897) = (term1056 A B s _62896 f _62897).
Proof. exact (TRANS (@lem4979400 A B s _62896 f _62897) (@lem4979409 A B s _62896 f _62897)). Qed.
Lemma lem4979411 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1051 A B s _62896 f _62897) = (term1057 A B s _62896 f _62897).
Proof. exact (MK_COMB (@lem4979397 A s _62896) (@lem4979410 A B s _62896 f _62897)). Qed.
Lemma lem4979412 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1050 A B s _62896 f _62897) = (term1057 A B s _62896 f _62897).
Proof. exact (TRANS (@lem4979392 A B s _62896 f _62897) (@lem4979411 A B s _62896 f _62897)). Qed.
Lemma lem4979413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4979414 {A B : Type'} (s : A -> Prop) (_62896 : A) (f : A -> B) (_62897 : A) : (term1058 A B s _62896 f _62897) = (term1059 A B s _62896 f _62897).
Proof. exact (MK_COMB (@lem4979413) (@lem4979412 A B s _62896 f _62897)). Qed.
Lemma lem4979415 {A : Type'} (_62896 : A) (_62897 : A) : (_62896 = _62897) = (_62896 = _62897).
Proof. exact (eq_refl (_62896 = _62897)). Qed.
Lemma lem4979416 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1049 A B s f _62896 _62897) = (term1060 A B s f _62896 _62897).
Proof. exact (MK_COMB (@lem4979414 A B s _62896 f _62897) (@lem4979415 A _62896 _62897)). Qed.
Lemma lem4979417 {A B : Type'} (s : A -> Prop) (f : A -> B) (_62896 : A) (_62897 : A) : (term1048 A B s _62896 f _62897) = (term1060 A B s f _62896 _62897).
Proof. exact (TRANS (@lem4979389 A B s f _62896 _62897) (@lem4979416 A B s f _62896 _62897)). Qed.
Lemma lem4979419 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term1056 A B s x f y.
Proof. exact (conj (@lem4979173 A B s P x f y h1) (@lem4979180 A B s P x f y h1)). Qed.
Lemma lem4979420 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term950 A B s P x f y) : term1057 A B s x f y.
Proof. exact (conj (@lem4979166 A B s P x f y h1) (@lem4979419 A B s P x f y h1)). Qed.
Lemma lem4979422 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1060 A B s f _62896 _62897.
Proof. exact (EQ_MP (@lem4979417 A B s f _62896 _62897) (@lem4979386 A B _62896 _62897 _62886 P n f t s h1)). Qed.
Lemma lem4979423 {A B : Type'} (_62896 : A) (_62897 : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1060 A B s f _62896 _62897.
Proof. exact (@lem4979422 A B _62896 _62897 _62886 P n f t s h1). Qed.
Lemma lem4979424 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term239 A B _62886 P n f t s) : term1060 A B s f x y.
Proof. exact (@lem4979423 A B x y _62886 P n f t s h1). Qed.
Lemma lem4979427 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term950 A B s P x f y) (h2 : term239 A B _62886 P n f t s) : x = y.
Proof. exact (@lem4979424 A B x y _62886 P n f t s h2 (@lem4979420 A B s P x f y h1)). Qed.
Lemma lem4979428 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term950 A B s P x f y) (h2 : term239 A B _62886 P n f t s) : term1061 A x y.
Proof. exact (fun h0 : term843 A x y => @lem4979427 A B x y _62886 P n f t s h1 h2). Qed.
Lemma lem4979430 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4979431 {A : Type'} (x : A) (y : A) : (term1061 A x y) = (x = y).
Proof. exact (@lem4979430 (x = y)). Qed.
Lemma lem4979432 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term950 A B s P x f y) (h2 : term239 A B _62886 P n f t s) : x = y.
Proof. exact (EQ_MP (@lem4979431 A x y) (@lem4979428 A B x y _62886 P n f t s h1 h2)). Qed.
Lemma lem4979435 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4979437 {A : Type'} (x : A) (y : A) : (term843 A x y) = (term1062 A x y).
Proof. exact (@lem4979435 (x = y)). Qed.
Lemma lem4979440 {A : Type'} (x : A) (y : A) (h1 : term843 A x y) : term1062 A x y.
Proof. exact (EQ_MP (@lem4979437 A x y) (@lem4978705 A x y h1)). Qed.
Lemma lem4979443 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (@lem4979440 A x y h1 (@lem4979432 A B x y _62886 P n f t s h2 h3)). Qed.
Lemma lem4979444 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : term911.
Proof. exact (fun h0 : ~ False => @lem4979443 A B x y _62886 P n f t s h1 h2 h3). Qed.
Lemma lem4979446 (p : Prop) : (term827 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4979447 : term911 = False.
Proof. exact (@lem4979446 False). Qed.
Lemma lem4979448 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979447) (@lem4979444 A B x y _62886 P n f t s h1 h2 h3)). Qed.
Lemma lem4979449 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h4 : term843 A x y => @lem4979448 A B x y _62886 P n f t s h1 h2 h3) (fun h4 : False => @lem4978705 A x y h1)). Qed.
Lemma lem4979450 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979449 A B x y _62886 P n f t s h1 h2 h3) (@lem4978705 A x y h1)). Qed.
Lemma lem4979451 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h4 : term843 A x y => @lem4979450 A B x y _62886 P n f t s h1 h2 h3) (fun h4 : False => @lem4978474 A x y h1)). Qed.
Lemma lem4979452 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979451 A B x y _62886 P n f t s h1 h2 h3) (@lem4978474 A x y h1)). Qed.
Lemma lem4979453 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h4 : term843 A x y => @lem4979452 A B x y _62886 P n f t s h1 h2 h3) (fun h4 : False => @lem4978474 A x y h1)). Qed.
Lemma lem4979454 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979453 A B x y _62886 P n f t s h1 h2 h3) (@lem4978474 A x y h1)). Qed.
Lemma lem4979455 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h4 : term843 A x y => @lem4979454 A B x y _62886 P n f t s h1 h2 h3) (fun h4 : False => @lem4978136 A x y h1)). Qed.
Lemma lem4979456 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term843 A x y) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979455 A B x y _62886 P n f t s h1 h2 h3) (@lem4978136 A x y h1)). Qed.
Lemma lem4979457 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : False.
Proof. exact (ex_elim (@lem4977613 A B _62886 h1) (fun x' : type652 A B => fun h0 : term576 A B _62886 x' => @lem4979456 A B x y _62886 P n f t s h2 h3 h4)). Qed.
Lemma lem4979458 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h5 : term843 A x y => @lem4979457 A B x y _62886 P n f t s h1 h2 h3 h4) (fun h5 : False => @lem4977848 A x y h2)). Qed.
Lemma lem4979459 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979458 A B x y _62886 P n f t s h1 h2 h3 h4) (@lem4977848 A x y h2)). Qed.
Lemma lem4979460 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : (term950 A B s P x f y) = False.
Proof. exact (prop_ext (fun h5 : term950 A B s P x f y => @lem4979459 A B x y _62886 P n f t s h1 h2 h3 h4) (fun h5 : False => @lem4977842 A B s P x f y h3)). Qed.
Lemma lem4979461 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979460 A B x y _62886 P n f t s h1 h2 h3 h4) (@lem4977842 A B s P x f y h3)). Qed.
Lemma lem4979462 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : (term843 A x y) = False.
Proof. exact (prop_ext (fun h5 : term843 A x y => @lem4979461 A B x y _62886 P n f t s h1 h2 h3 h4) (fun h5 : False => @lem4976795 A x y h2)). Qed.
Lemma lem4979463 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term843 A x y) (h3 : term950 A B s P x f y) (h4 : term239 A B _62886 P n f t s) : False.
Proof. exact (EQ_MP (@lem4979462 A B x y _62886 P n f t s h1 h2 h3 h4) (@lem4976795 A x y h2)). Qed.
Lemma lem4979464 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : term1022 A x y.
Proof. exact (fun h0 : term843 A x y => @lem4979463 A B x y _62886 P n f t s h1 h0 h2 h3). Qed.
Lemma lem4979465 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term950 A B s P x f y) (h3 : term239 A B _62886 P n f t s) : x = y.
Proof. exact (EQ_MP (@lem4976794 A x y) (@lem4979464 A B x y _62886 P n f t s h1 h2 h3)). Qed.
Lemma lem4979466 {A B : Type'} (x : A) (y : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term239 A B _62886 P n f t s) : term954 A B s P f x y.
Proof. exact (fun h0 : term950 A B s P x f y => @lem4979465 A B x y _62886 P n f t s h1 h0 h2). Qed.
Lemma lem4979471 {A B : Type'} (x : A) (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term239 A B _62886 P n f t s) : term958 A B s P f x.
Proof. exact (fun y : A => @lem4979466 A B x y _62886 P n f t s h1 h2). Qed.
Lemma lem4979476 {A B : Type'} (_62886 : type653 A B) (P : B -> Prop) (n : nat) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term319 A B _62886) (h2 : term239 A B _62886 P n f t s) : term961 A B s P f.
Proof. exact (fun x : A => @lem4979471 A B x _62886 P n f t s h1 h2). Qed.
Lemma lem4979477 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : term319 A B _62886) : term989 A B _62886 n t s P f.
Proof. exact (fun h0 : term239 A B _62886 P n f t s => @lem4979476 A B _62886 P n f t s h1 h0). Qed.
Lemma lem4979482 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : term319 A B _62886) : term991 A B _62886 t s P f.
Proof. exact (fun n : nat => @lem4979477 A B n t s P f _62886 h1). Qed.
Lemma lem4979487 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : term319 A B _62886) : term993 A B _62886 s P f.
Proof. exact (fun t : B -> Prop => @lem4979482 A B t s P f _62886 h1). Qed.
Lemma lem4979492 {A B : Type'} (P : B -> Prop) (f : A -> B) (_62886 : type653 A B) (h1 : term319 A B _62886) : term995 A B _62886 P f.
Proof. exact (fun s : A -> Prop => @lem4979487 A B s P f _62886 h1). Qed.
Lemma lem4979497 {A B : Type'} (f : A -> B) (_62886 : type653 A B) (h1 : term319 A B _62886) : term997 A B _62886 f.
Proof. exact (fun P : B -> Prop => @lem4979492 A B P f _62886 h1). Qed.
Lemma lem4979502 {A B : Type'} (_62886 : type653 A B) (h1 : term319 A B _62886) : term999 A B _62886.
Proof. exact (fun f : A -> B => @lem4979497 A B f _62886 h1). Qed.
Lemma lem4979503 {A B : Type'} (_62886 : type653 A B) : term1019 A B _62886.
Proof. exact (fun h0 : term319 A B _62886 => @lem4979502 A B _62886 h0). Qed.
Lemma lem4979508 {A B : Type'} : term1021 A B.
Proof. exact (fun _62886 : type653 A B => @lem4979503 A B _62886). Qed.
Lemma lem4979509 {A B : Type'} : term987 A B.
Proof. exact (EQ_MP (@lem4976787 A B) (@lem4979508 A B)). Qed.
Lemma lem4979510 {A B : Type'} (f : A -> B) : term1063 A B f.
Proof. exact (@lem4979509 A B f). Qed.
Lemma lem4979511 {A B : Type'} (f : A -> B) : (term1063 A B f) = (term983 A B f).
Proof. exact (eq_refl (term1063 A B f)). Qed.
Lemma lem4979512 {A B : Type'} (f : A -> B) : term983 A B f.
Proof. exact (EQ_MP (@lem4979511 A B f) (@lem4979510 A B f)). Qed.
Lemma lem4979513 {A B : Type'} (f : A -> B) (P : B -> Prop) : term1064 A B f P.
Proof. exact (@lem4979512 A B f P). Qed.
Lemma lem4979514 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term1064 A B f P) = (term979 A B P f).
Proof. exact (eq_refl (term1064 A B f P)). Qed.
Lemma lem4979515 {A B : Type'} (P : B -> Prop) (f : A -> B) : term979 A B P f.
Proof. exact (EQ_MP (@lem4979514 A B P f) (@lem4979513 A B f P)). Qed.
Lemma lem4979516 {A B : Type'} (P : B -> Prop) (f : A -> B) (s : A -> Prop) : term1065 A B P f s.
Proof. exact (@lem4979515 A B P f s). Qed.
Lemma lem4979517 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term1065 A B P f s) = (term975 A B s P f).
Proof. exact (eq_refl (term1065 A B P f s)). Qed.
Lemma lem4979518 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term975 A B s P f.
Proof. exact (EQ_MP (@lem4979517 A B s P f) (@lem4979516 A B P f s)). Qed.
Lemma lem4979519 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (t : B -> Prop) : term1066 A B s P f t.
Proof. exact (@lem4979518 A B s P f t). Qed.
Lemma lem4979520 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term1066 A B s P f t) = (term971 A B t s P f).
Proof. exact (eq_refl (term1066 A B s P f t)). Qed.
Lemma lem4979521 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term971 A B t s P f.
Proof. exact (EQ_MP (@lem4979520 A B t s P f) (@lem4979519 A B s P f t)). Qed.
Lemma lem4979522 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) : term1067 A B t s P f n.
Proof. exact (@lem4979521 A B t s P f n). Qed.
Lemma lem4979523 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term1067 A B t s P f n) = (term963 A B n t s P f).
Proof. exact (eq_refl (term1067 A B t s P f n)). Qed.
Lemma lem4979524 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term963 A B n t s P f.
Proof. exact (EQ_MP (@lem4979523 A B n t s P f) (@lem4979522 A B t s P f n)). Qed.
Lemma lem4979526 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term963 A B n t s P f.
Proof. exact (@lem4976050 A B n t s P f (@lem4979524 A B n t s P f)). Qed.
Lemma lem4979527 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term964 A B n t s P f) : False.
Proof. exact (@lem4979526 A B n t s P f (@lem4976034 A B n t s P f h1)). Qed.
Lemma lem4979528 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term964 A B n t s P f) : (term964 A B n t s P f) = False.
Proof. exact (prop_ext (fun h2 : term964 A B n t s P f => @lem4979527 A B n t s P f h1) (fun h2 : False => @lem4976034 A B n t s P f h1)). Qed.
Lemma lem4979529 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term964 A B n t s P f) : False.
Proof. exact (EQ_MP (@lem4979528 A B n t s P f h1) (@lem4976034 A B n t s P f h1)). Qed.
Lemma lem4979530 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term963 A B n t s P f.
Proof. exact (fun h0 : term964 A B n t s P f => @lem4979529 A B n t s P f h0). Qed.
Lemma lem4979531 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term962 A B n t s P f.
Proof. exact (EQ_MP (@lem4976033 A B n t s P f) (@lem4979530 A B n t s P f)). Qed.
Lemma lem4979532 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term944 A B n t s P f.
Proof. exact (EQ_MP (@lem4976029 A B n t s P f) (@lem4979531 A B n t s P f)). Qed.
Lemma lem4979533 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term943 A B n t s P f.
Proof. exact (EQ_MP (@lem4975733 A B n t s P f) (@lem4979532 A B n t s P f)). Qed.
Lemma lem4979534 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term942 A B s P f.
Proof. exact (@lem4979533 A B n t s P f (@lem4975624 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4979535 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term940 A B s P f n.
Proof. exact (EQ_MP (@lem4975609 A B s P f n h5) (@lem4979534 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4979536 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term31 A B s P f n.
Proof. exact (@lem4975521 A B s P f n (@lem4979535 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4979537 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (term26 B t P) = (term27 A B s P f)) (h5 : (@CARD A s) = (@CARD B t)) (h6 : term24 A B s P f n) (h7 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4968488 A B n t s P f h4) (@lem4979536 A B P n f s t h1 h2 h3 h5 h6 h7)). Qed.
Lemma lem4979538 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : ((term26 B t P) = (term27 A B s P f)) = (term33 B t P n).
Proof. exact (prop_ext (fun h7 : (term26 B t P) = (term27 A B s P f) => @lem4979537 A B P n f s t h1 h2 h3 h7 h4 h5 h6) (fun h7 : term33 B t P n => @lem4975517 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4979539 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979538 A B P n f s t h1 h2 h3 h4 h5 h6) (@lem4975517 A B P n f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4979540 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term18 A B t s P f n) : term19 A B t s P f n.
Proof. exact (proj2 (@lem4968464 A B t s P f n h1)). Qed.
Lemma lem4979541 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term18 A B t s P f n) : @FINITE A s.
Proof. exact (proj1 (@lem4968464 A B t s P f n h1)). Qed.
Lemma lem4979542 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term19 A B t s P f n) : term20 A B t s P f n.
Proof. exact (proj2 (@lem4968465 A B t s P f n h1)). Qed.
Lemma lem4979543 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term19 A B t s P f n) : @FINITE B t.
Proof. exact (proj1 (@lem4968465 A B t s P f n h1)). Qed.
Lemma lem4979544 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term20 A B t s P f n) : term21 A B t s P f n.
Proof. exact (proj2 (@lem4968467 A B t s P f n h1)). Qed.
Lemma lem4979545 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term20 A B t s P f n) : (@CARD A s) = (@CARD B t).
Proof. exact (proj1 (@lem4968467 A B t s P f n h1)). Qed.
Lemma lem4979546 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term21 A B t s P f n) : term22 A B s P f n.
Proof. exact (proj2 (@lem4968469 A B t s P f n h1)). Qed.
Lemma lem4979547 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term21 A B t s P f n) : term23 A B f s t.
Proof. exact (proj1 (@lem4968469 A B t s P f n h1)). Qed.
Lemma lem4979548 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term22 A B s P f n) : term24 A B s P f n.
Proof. exact (proj2 (@lem4968471 A B s P f n h1)). Qed.
Lemma lem4979549 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term22 A B s P f n) : term25 A B s f.
Proof. exact (proj1 (@lem4968471 A B s P f n h1)). Qed.
Lemma lem4979550 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : (term24 A B s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h7 : term24 A B s P f n => @lem4979539 A B P n f s t h1 h2 h3 h4 h5 h6) (fun h7 : term33 B t P n => @lem4968473 A B s P f n h5)). Qed.
Lemma lem4979551 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979550 A B P n f s t h1 h2 h3 h4 h5 h6) (@lem4968473 A B s P f n h5)). Qed.
Lemma lem4979552 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : (term25 A B s f) = (term33 B t P n).
Proof. exact (prop_ext (fun h7 : term25 A B s f => @lem4979551 A B P n f s t h1 h2 h3 h4 h5 h6) (fun h7 : term33 B t P n => @lem4968474 A B s f h1)). Qed.
Lemma lem4979553 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term24 A B s P f n) (h6 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979552 A B P n f s t h1 h2 h3 h4 h5 h6) (@lem4968474 A B s f h1)). Qed.
Lemma lem4979554 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term22 A B s P f n) (h5 : (@CARD A s) = (@CARD B t)) (h6 : term23 A B f s t) : (term24 A B s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h7 : term24 A B s P f n => @lem4979553 A B P n f s t h1 h2 h3 h5 h7 h6) (fun h7 : term33 B t P n => @lem4979548 A B s P f n h4)). Qed.
Lemma lem4979555 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term25 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term22 A B s P f n) (h5 : (@CARD A s) = (@CARD B t)) (h6 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979554 A B P n f s t h1 h2 h3 h4 h5 h6) (@lem4979548 A B s P f n h4)). Qed.
Lemma lem4979556 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term22 A B s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term25 A B s f) = (term33 B t P n).
Proof. exact (prop_ext (fun h6 : term25 A B s f => @lem4979555 A B P n f s t h6 h1 h2 h3 h4 h5) (fun h6 : term33 B t P n => @lem4979549 A B s P f n h3)). Qed.
Lemma lem4979557 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term22 A B s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979556 A B P n f s t h1 h2 h3 h4 h5) (@lem4979549 A B s P f n h3)). Qed.
Lemma lem4979558 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term22 A B s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term23 A B f s t) = (term33 B t P n).
Proof. exact (prop_ext (fun h6 : term23 A B f s t => @lem4979557 A B P n f s t h1 h2 h3 h4 h5) (fun h6 : term33 B t P n => @lem4968472 A B f s t h5)). Qed.
Lemma lem4979559 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term22 A B s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979558 A B P n f s t h1 h2 h3 h4 h5) (@lem4968472 A B f s t h5)). Qed.
Lemma lem4979560 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : (term22 A B s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h6 : term22 A B s P f n => @lem4979559 A B P n f s t h1 h2 h6 h4 h5) (fun h6 : term33 B t P n => @lem4979546 A B t s P f n h3)). Qed.
Lemma lem4979561 {A B : Type'} (P : B -> Prop) (n : nat) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) (h5 : term23 A B f s t) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979560 A B P n f s t h1 h2 h3 h4 h5) (@lem4979546 A B t s P f n h3)). Qed.
Lemma lem4979562 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : (term23 A B f s t) = (term33 B t P n).
Proof. exact (prop_ext (fun h5 : term23 A B f s t => @lem4979561 A B P n f s t h1 h2 h3 h4 h5) (fun h5 : term33 B t P n => @lem4979547 A B t s P f n h3)). Qed.
Lemma lem4979563 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979562 A B P f n s t h1 h2 h3 h4) (@lem4979547 A B t s P f n h3)). Qed.
Lemma lem4979564 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = (term33 B t P n).
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (@CARD B t) => @lem4979563 A B P f n s t h1 h2 h3 h4) (fun h5 : term33 B t P n => @lem4968470 A B s t h4)). Qed.
Lemma lem4979565 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term21 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979564 A B P f n s t h1 h2 h3 h4) (@lem4968470 A B s t h4)). Qed.
Lemma lem4979566 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : (term21 A B t s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h5 : term21 A B t s P f n => @lem4979565 A B P f n s t h1 h2 h5 h4) (fun h5 : term33 B t P n => @lem4979544 A B t s P f n h3)). Qed.
Lemma lem4979567 {A B : Type'} (P : B -> Prop) (f : A -> B) (n : nat) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) (h4 : (@CARD A s) = (@CARD B t)) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979566 A B P f n s t h1 h2 h3 h4) (@lem4979544 A B t s P f n h3)). Qed.
Lemma lem4979568 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) : ((@CARD A s) = (@CARD B t)) = (term33 B t P n).
Proof. exact (prop_ext (fun h4 : (@CARD A s) = (@CARD B t) => @lem4979567 A B P f n s t h1 h2 h3 h4) (fun h4 : term33 B t P n => @lem4979545 A B t s P f n h3)). Qed.
Lemma lem4979569 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979568 A B t s P f n h1 h2 h3) (@lem4979545 A B t s P f n h3)). Qed.
Lemma lem4979570 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) : (@FINITE B t) = (term33 B t P n).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem4979569 A B t s P f n h1 h2 h3) (fun h4 : term33 B t P n => @lem4968468 B t h2)). Qed.
Lemma lem4979571 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term20 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979570 A B t s P f n h1 h2 h3) (@lem4968468 B t h2)). Qed.
Lemma lem4979572 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term19 A B t s P f n) : (term20 A B t s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h4 : term20 A B t s P f n => @lem4979571 A B t s P f n h1 h2 h4) (fun h4 : term33 B t P n => @lem4979542 A B t s P f n h3)). Qed.
Lemma lem4979573 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term19 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979572 A B t s P f n h1 h2 h3) (@lem4979542 A B t s P f n h3)). Qed.
Lemma lem4979574 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term19 A B t s P f n) : (@FINITE B t) = (term33 B t P n).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4979573 A B t s P f n h1 h3 h2) (fun h3 : term33 B t P n => @lem4979543 A B t s P f n h2)). Qed.
Lemma lem4979575 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term19 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979574 A B t s P f n h1 h2) (@lem4979543 A B t s P f n h2)). Qed.
Lemma lem4979576 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term19 A B t s P f n) : (@FINITE A s) = (term33 B t P n).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4979575 A B t s P f n h1 h2) (fun h3 : term33 B t P n => @lem4968466 A s h1)). Qed.
Lemma lem4979577 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term19 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979576 A B t s P f n h1 h2) (@lem4968466 A s h1)). Qed.
Lemma lem4979578 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term18 A B t s P f n) : (term19 A B t s P f n) = (term33 B t P n).
Proof. exact (prop_ext (fun h3 : term19 A B t s P f n => @lem4979577 A B t s P f n h1 h3) (fun h3 : term33 B t P n => @lem4979540 A B t s P f n h2)). Qed.
Lemma lem4979579 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : @FINITE A s) (h2 : term18 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979578 A B t s P f n h1 h2) (@lem4979540 A B t s P f n h2)). Qed.
Lemma lem4979580 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term18 A B t s P f n) : (@FINITE A s) = (term33 B t P n).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4979579 A B t s P f n h2 h1) (fun h2 : term33 B t P n => @lem4979541 A B t s P f n h1)). Qed.
Lemma lem4979581 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (n : nat) (h1 : term18 A B t s P f n) : term33 B t P n.
Proof. exact (EQ_MP (@lem4979580 A B t s P f n h1) (@lem4979541 A B t s P f n h1)). Qed.
Lemma lem4979582 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (P : B -> Prop) (n : nat) : term1068 A B s f t P n.
Proof. exact (fun h0 : term18 A B t s P f n => @lem4979581 A B t s P f n h0). Qed.
Lemma lem4979587 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (P : B -> Prop) : term1069 A B s f t P.
Proof. exact (fun n : nat => @lem4979582 A B s f t P n). Qed.
Lemma lem4979592 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term1070 A B s f t.
Proof. exact (fun P : B -> Prop => @lem4979587 A B s f t P). Qed.
Lemma lem4979597 {A B : Type'} (s : A -> Prop) (f : A -> B) : term1071 A B s f.
Proof. exact (fun t : B -> Prop => @lem4979592 A B s f t). Qed.
Lemma lem4979602 {A B : Type'} (f : A -> B) : term1072 A B f.
Proof. exact (fun s : A -> Prop => @lem4979597 A B s f). Qed.
Lemma lem4979609 {A B : Type'} : term1073 A B.
Proof. exact (fun f : A -> B => @lem4979602 A B f). Qed.
