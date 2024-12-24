Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNCURRY_DEF_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem48489 {A B C : Type'} : (@UNCURRY A B C) = (term0 A B C).
Proof. exact (@UNCURRY_def A B C). Qed.
Lemma lem48490 {A B C : Type'} (_1304 : type1412 A B C) : _1304 = _1304.
Proof. exact (eq_refl _1304). Qed.
Lemma lem48491 {A B C : Type'} (_1304 : type1412 A B C) : (@UNCURRY A B C _1304) = (term1 A B C _1304).
Proof. exact (MK_COMB (@lem48489 A B C) (@lem48490 A B C _1304)). Qed.
Lemma lem48492 {A B C : Type'} (_1304 : type1412 A B C) : (term1 A B C _1304) = (term2 A B C _1304).
Proof. exact (eq_refl (term1 A B C _1304)). Qed.
Lemma lem48493 {A B C : Type'} (_1304 : type1412 A B C) : (@UNCURRY A B C _1304) = (term2 A B C _1304).
Proof. exact (TRANS (@lem48491 A B C _1304) (@lem48492 A B C _1304)). Qed.
Lemma lem48494 {A B : Type'} (_1305 : prod A B) : _1305 = _1305.
Proof. exact (eq_refl _1305). Qed.
Lemma lem48495 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : (@UNCURRY A B C _1304 _1305) = (term3 A B C _1304 _1305).
Proof. exact (MK_COMB (@lem48493 A B C _1304) (@lem48494 A B _1305)). Qed.
Lemma lem48496 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : (term3 A B C _1304 _1305) = (term4 A B C _1304 _1305).
Proof. exact (eq_refl (term3 A B C _1304 _1305)). Qed.
Lemma lem48497 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : (@UNCURRY A B C _1304 _1305) = (term4 A B C _1304 _1305).
Proof. exact (TRANS (@lem48495 A B C _1304 _1305) (@lem48496 A B C _1304 _1305)). Qed.
Lemma lem48498 {A B C : Type'} (_1304 : type1412 A B C) : term5 A B C _1304.
Proof. exact (fun _1305 : prod A B => @lem48497 A B C _1304 _1305). Qed.
Lemma lem48499 {A B C : Type'} : term6 A B C.
Proof. exact (fun _1304 : type1412 A B C => @lem48498 A B C _1304). Qed.
Lemma lem48500 {A B C : Type'} (_1304 : type1412 A B C) : term7 A B C _1304.
Proof. exact (@lem48499 A B C _1304). Qed.
Lemma lem48501 {A B C : Type'} (_1304 : type1412 A B C) : (term7 A B C _1304) = (term5 A B C _1304).
Proof. exact (eq_refl (term7 A B C _1304)). Qed.
Lemma lem48502 {A B C : Type'} (_1304 : type1412 A B C) : term5 A B C _1304.
Proof. exact (EQ_MP (@lem48501 A B C _1304) (@lem48500 A B C _1304)). Qed.
Lemma lem48503 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : term8 A B C _1304 _1305.
Proof. exact (@lem48502 A B C _1304 _1305). Qed.
Lemma lem48504 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : (term8 A B C _1304 _1305) = ((@UNCURRY A B C _1304 _1305) = (term4 A B C _1304 _1305)).
Proof. exact (eq_refl (term8 A B C _1304 _1305)). Qed.
Lemma lem48505 {A B C : Type'} (_1304 : type1412 A B C) (_1305 : prod A B) : (@UNCURRY A B C _1304 _1305) = (term4 A B C _1304 _1305).
Proof. exact (EQ_MP (@lem48504 A B C _1304 _1305) (@lem48503 A B C _1304 _1305)). Qed.
Lemma lem48506 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term9 A B C f x y) = (term10 A B C f x y).
Proof. exact (@lem48505 A B C f (@pair A B x y)). Qed.
Lemma lem48507 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem48508 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem48509 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem48508 A B x) (@lem48507 A B x)). Qed.
Lemma lem48510 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem48509 A B x y). Qed.
Lemma lem48511 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((term14 A B x y) = y).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem48513 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem48514 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem48515 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem48514 A B x) (@lem48513 A B x)). Qed.
Lemma lem48516 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem48515 A B x y). Qed.
Lemma lem48517 {A B : Type'} (y : B) (x : A) : (term17 A B x y) = ((term18 A B x y) = x).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem48522 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem48517 A B y x) (@lem48516 A B x y)). Qed.
Lemma lem48523 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (@lem48522 A B y x). Qed.
Lemma lem48524 {A B : Type'} (x : A) (y : B) : x = (term18 A B x y).
Proof. exact (SYM (@lem48523 A B y x)). Qed.
Lemma lem48526 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem48511 A B x y) (@lem48510 A B x y)). Qed.
Lemma lem48527 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (@lem48526 A B x y). Qed.
Lemma lem48528 {A B : Type'} (x : A) (y : B) : y = (term14 A B x y).
Proof. exact (SYM (@lem48527 A B x y)). Qed.
Lemma lem48530 {A B C : Type'} (f : type1412 A B C) : (term19 A B C f) = (term19 A B C f).
Proof. exact (eq_refl (term19 A B C f)). Qed.
Lemma lem48531 {A B C : Type'} (f : type1412 A B C) : (term19 A B C f) = (term20 A B C f).
Proof. exact (eq_refl (term19 A B C f)). Qed.
Lemma lem48532 {A B C : Type'} (f : type1412 A B C) : (term21 A B C f) = (term21 A B C f).
Proof. exact (eq_refl (term21 A B C f)). Qed.
Lemma lem48533 {A B C : Type'} (f : type1412 A B C) : ((term19 A B C f) = (term19 A B C f)) = ((term19 A B C f) = (term20 A B C f)).
Proof. exact (MK_COMB (@lem48532 A B C f) (@lem48531 A B C f)). Qed.
Lemma lem48534 {A B C : Type'} (f : type1412 A B C) : (term19 A B C f) = (term20 A B C f).
Proof. exact (eq_refl (term19 A B C f)). Qed.
Lemma lem48535 {A B C : Type'} : (@eq (A -> B -> C)) = (@eq (A -> B -> C)).
Proof. exact (eq_refl (@eq (A -> B -> C))). Qed.
Lemma lem48536 {A B C : Type'} (f : type1412 A B C) : (term21 A B C f) = (term22 A B C f).
Proof. exact (MK_COMB (@lem48535 A B C) (@lem48534 A B C f)). Qed.
Lemma lem48537 {A B C : Type'} (f : type1412 A B C) : (term20 A B C f) = (term20 A B C f).
Proof. exact (eq_refl (term20 A B C f)). Qed.
Lemma lem48538 {A B C : Type'} (f : type1412 A B C) : ((term19 A B C f) = (term20 A B C f)) = ((term20 A B C f) = (term20 A B C f)).
Proof. exact (MK_COMB (@lem48536 A B C f) (@lem48537 A B C f)). Qed.
Lemma lem48539 {A B C : Type'} (f : type1412 A B C) : ((term19 A B C f) = (term19 A B C f)) = ((term20 A B C f) = (term20 A B C f)).
Proof. exact (TRANS (@lem48533 A B C f) (@lem48538 A B C f)). Qed.
Lemma lem48540 {A B C : Type'} (f : type1412 A B C) : (term20 A B C f) = (term20 A B C f).
Proof. exact (EQ_MP (@lem48539 A B C f) (@lem48530 A B C f)). Qed.
Lemma lem48541 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term23 A B C f x) = (term24 A B C f x y).
Proof. exact (MK_COMB (@lem48540 A B C f) (@lem48524 A B x y)). Qed.
Lemma lem48542 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term24 A B C f x y) = (term25 A B C f x y).
Proof. exact (eq_refl (term24 A B C f x y)). Qed.
Lemma lem48543 {A B C : Type'} (f : type1412 A B C) (x : A) : (term26 A B C f x) = (term26 A B C f x).
Proof. exact (eq_refl (term26 A B C f x)). Qed.
Lemma lem48544 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term23 A B C f x) = (term24 A B C f x y)) = ((term23 A B C f x) = (term25 A B C f x y)).
Proof. exact (MK_COMB (@lem48543 A B C f x) (@lem48542 A B C f x y)). Qed.
Lemma lem48545 {A B C : Type'} (f : type1412 A B C) (x : A) : (term23 A B C f x) = (term27 A B C f x).
Proof. exact (eq_refl (term23 A B C f x)). Qed.
Lemma lem48546 {B C : Type'} : (@eq (B -> C)) = (@eq (B -> C)).
Proof. exact (eq_refl (@eq (B -> C))). Qed.
Lemma lem48547 {A B C : Type'} (f : type1412 A B C) (x : A) : (term26 A B C f x) = (term28 A B C f x).
Proof. exact (MK_COMB (@lem48546 B C) (@lem48545 A B C f x)). Qed.
Lemma lem48548 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term25 A B C f x y) = (term25 A B C f x y).
Proof. exact (eq_refl (term25 A B C f x y)). Qed.
Lemma lem48549 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term23 A B C f x) = (term25 A B C f x y)) = ((term27 A B C f x) = (term25 A B C f x y)).
Proof. exact (MK_COMB (@lem48547 A B C f x) (@lem48548 A B C f x y)). Qed.
Lemma lem48550 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term23 A B C f x) = (term24 A B C f x y)) = ((term27 A B C f x) = (term25 A B C f x y)).
Proof. exact (TRANS (@lem48544 A B C f x y) (@lem48549 A B C f x y)). Qed.
Lemma lem48551 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term27 A B C f x) = (term25 A B C f x y).
Proof. exact (EQ_MP (@lem48550 A B C f x y) (@lem48541 A B C f x y)). Qed.
Lemma lem48552 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term29 A B C f x y) = (term30 A B C f x y).
Proof. exact (MK_COMB (@lem48551 A B C f x y) (@lem48528 A B x y)). Qed.
Lemma lem48553 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term30 A B C f x y) = (term10 A B C f x y).
Proof. exact (eq_refl (term30 A B C f x y)). Qed.
Lemma lem48554 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term31 A B C f x y) = (term31 A B C f x y).
Proof. exact (eq_refl (term31 A B C f x y)). Qed.
Lemma lem48555 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term29 A B C f x y) = (term30 A B C f x y)) = ((term29 A B C f x y) = (term10 A B C f x y)).
Proof. exact (MK_COMB (@lem48554 A B C f x y) (@lem48553 A B C f x y)). Qed.
Lemma lem48556 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term29 A B C f x y) = (f x y).
Proof. exact (eq_refl (term29 A B C f x y)). Qed.
Lemma lem48557 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem48558 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term31 A B C f x y) = (term32 A B C f x y).
Proof. exact (MK_COMB (@lem48557 C) (@lem48556 A B C f x y)). Qed.
Lemma lem48559 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term10 A B C f x y) = (term10 A B C f x y).
Proof. exact (eq_refl (term10 A B C f x y)). Qed.
Lemma lem48560 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term29 A B C f x y) = (term10 A B C f x y)) = ((f x y) = (term10 A B C f x y)).
Proof. exact (MK_COMB (@lem48558 A B C f x y) (@lem48559 A B C f x y)). Qed.
Lemma lem48561 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term29 A B C f x y) = (term30 A B C f x y)) = ((f x y) = (term10 A B C f x y)).
Proof. exact (TRANS (@lem48555 A B C f x y) (@lem48560 A B C f x y)). Qed.
Lemma lem48562 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (f x y) = (term10 A B C f x y).
Proof. exact (EQ_MP (@lem48561 A B C f x y) (@lem48552 A B C f x y)). Qed.
Lemma lem48563 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term10 A B C f x y) = (f x y).
Proof. exact (SYM (@lem48562 A B C f x y)). Qed.
Lemma lem48564 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term9 A B C f x y) = (f x y).
Proof. exact (TRANS (@lem48506 A B C f x y) (@lem48563 A B C f x y)). Qed.
Lemma lem48565 {A B C : Type'} (f : type1412 A B C) (x : A) : term33 A B C f x.
Proof. exact (fun y : B => @lem48564 A B C f x y). Qed.
Lemma lem48566 {A B C : Type'} (f : type1412 A B C) : term34 A B C f.
Proof. exact (fun x : A => @lem48565 A B C f x). Qed.
Lemma lem48567 {A B C : Type'} : term35 A B C.
Proof. exact (fun f : type1412 A B C => @lem48566 A B C f). Qed.
