Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_IDEMPOT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_IN_GSPEC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_PRODUCT_DEPENDENT_spec.
Require Import FINITE_UNION_OF_INC_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import FUN_EQ_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import UNIONS_IMAGE_spec.
Require Import UNION_OF_spec.
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
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm7_spec.
Lemma lem4879381 {_89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 : Type'} (Q : _89357 -> Prop) : term0 _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q.
Proof. exact (proj2 (@lem3449335 Prop _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q)). Qed.
Lemma lem4879397 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) : term1 _89212 _89213 _89357 Q.
Proof. exact (proj1 (@lem4879381 _89212 _89213 Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem4879398 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) (P : type1470 _89212 _89213) : term2 _89212 _89213 _89357 Q P.
Proof. exact (@lem4879397 _89212 _89213 _89357 Q P). Qed.
Lemma lem4879399 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : (term2 _89212 _89213 _89357 Q P) = (term3 _89212 _89213 _89357 P Q).
Proof. exact (eq_refl (term2 _89212 _89213 _89357 Q P)). Qed.
Lemma lem4879400 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : term3 _89212 _89213 _89357 P Q.
Proof. exact (EQ_MP (@lem4879399 _89212 _89213 _89357 P Q) (@lem4879398 _89212 _89213 _89357 Q P)). Qed.
Lemma lem4879401 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : term4 _89212 _89213 _89357 P Q f.
Proof. exact (@lem4879400 _89212 _89213 _89357 P Q f). Qed.
Lemma lem4879402 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term4 _89212 _89213 _89357 P Q f) = ((term5 _89212 _89213 _89357 P f Q) = (term6 _89212 _89213 _89357 P Q f)).
Proof. exact (eq_refl (term4 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem4879411 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term7 _89422 _89438 f.
Proof. exact (@lem3452302 _89422 _89438 f). Qed.
Lemma lem4879412 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term7 _89422 _89438 f) = (term8 _89422 _89438 f).
Proof. exact (eq_refl (term7 _89422 _89438 f)). Qed.
Lemma lem4879413 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term8 _89422 _89438 f.
Proof. exact (EQ_MP (@lem4879412 _89422 _89438 f) (@lem4879411 _89422 _89438 f)). Qed.
Lemma lem4879414 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term9 _89422 _89438 f s.
Proof. exact (@lem4879413 _89422 _89438 f s). Qed.
Lemma lem4879415 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term9 _89422 _89438 f s) = ((term10 _89422 _89438 f s) = (term11 _89422 _89438 s f)).
Proof. exact (eq_refl (term9 _89422 _89438 f s)). Qed.
Lemma lem4879417 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term12 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem4879433 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term13 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem4879417 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4879434 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term14 _88961 _88962 _89106 Q P.
Proof. exact (@lem4879433 _88961 _88962 _89106 Q P). Qed.
Lemma lem4879435 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term14 _88961 _88962 _89106 Q P) = (term15 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term14 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4879436 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term15 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem4879435 _88961 _88962 _89106 P Q) (@lem4879434 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4879437 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term16 _88961 _88962 _89106 P Q f.
Proof. exact (@lem4879436 _88961 _88962 _89106 P Q f). Qed.
Lemma lem4879438 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term16 _88961 _88962 _89106 P Q f) = ((term17 _88961 _88962 _89106 P f Q) = (term18 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term16 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4879447 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term19 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4879448 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term19 _87967 _87968 P f) = (term20 _87967 _87968 P f).
Proof. exact (eq_refl (term19 _87967 _87968 P f)). Qed.
Lemma lem4879449 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term20 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4879448 _87967 _87968 P f) (@lem4879447 _87967 _87968 P f)). Qed.
Lemma lem4879450 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term21 _87967 _87968 P f s.
Proof. exact (@lem4879449 _87967 _87968 P f s). Qed.
Lemma lem4879451 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term21 _87967 _87968 P f s) = ((term22 _87967 _87968 f s P) = (term23 _87967 _87968 s P f)).
Proof. exact (eq_refl (term21 _87967 _87968 P f s)). Qed.
Lemma lem4879453 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4879454 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem4879455 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem4879454 A P) (@lem4879453 A P)). Qed.
Lemma lem4879456 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem4879455 A P Q). Qed.
Lemma lem4879457 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem4879459 {A B : Type'} (P : type1413 A B) : term29 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4879460 {A B : Type'} (P : type1413 A B) : (term29 A B P) = ((term30 A B P) = (term31 A B P)).
Proof. exact (eq_refl (term29 A B P)). Qed.
Lemma lem4879462 {A : Type'} (P : Prop) : term32 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem4879463 {A : Type'} (P : Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem4879464 {A : Type'} (P : Prop) : term33 A P.
Proof. exact (EQ_MP (@lem4879463 A P) (@lem4879462 A P)). Qed.
Lemma lem4879465 {A : Type'} (P : Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem4879464 A P Q). Qed.
Lemma lem4879466 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem4879468 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4879469 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem4879470 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem4879469 A P) (@lem4879468 A P)). Qed.
Lemma lem4879471 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem4879470 A P Q). Qed.
Lemma lem4879472 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem4879474 {A : Type'} (P : type180 A) : term37 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4879475 {A : Type'} (P : type180 A) : (term37 A P) = (term38 A P).
Proof. exact (eq_refl (term37 A P)). Qed.
Lemma lem4879476 {A : Type'} (P : type180 A) : term38 A P.
Proof. exact (EQ_MP (@lem4879475 A P) (@lem4879474 A P)). Qed.
Lemma lem4879477 {A : Type'} (P : type180 A) (Q : type686 A) : term39 A P Q.
Proof. exact (@lem4879476 A P Q). Qed.
Lemma lem4879478 {A : Type'} (P : type180 A) (Q : type686 A) : (term39 A P Q) = ((@UNION_OF A P Q) = (term40 A P Q)).
Proof. exact (eq_refl (term39 A P Q)). Qed.
Lemma lem4879480 {A : Type'} (P : type686 A) : term41 A P.
Proof. exact (@lem4876798 A P). Qed.
Lemma lem4879481 {A : Type'} (P : type686 A) : (term41 A P) = (term42 A P).
Proof. exact (eq_refl (term41 A P)). Qed.
Lemma lem4879482 {A : Type'} (P : type686 A) : term42 A P.
Proof. exact (EQ_MP (@lem4879481 A P) (@lem4879480 A P)). Qed.
Lemma lem4879483 {A : Type'} (P : type686 A) (s : A -> Prop) : term43 A P s.
Proof. exact (@lem4879482 A P s). Qed.
Lemma lem4879484 {A : Type'} (P : type686 A) (s : A -> Prop) : (term43 A P s) = (term44 A P s).
Proof. exact (eq_refl (term43 A P s)). Qed.
Lemma lem4879485 {A : Type'} (P : type686 A) (s : A -> Prop) : term44 A P s.
Proof. exact (EQ_MP (@lem4879484 A P s) (@lem4879483 A P s)). Qed.
Lemma lem4879486 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = ((term44 A P s) = True).
Proof. exact (@lem7 (term44 A P s)). Qed.
Lemma lem4879488 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4879489 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (eq_refl (term45 A B f)). Qed.
Lemma lem4879490 {A B : Type'} (f : A -> B) : term46 A B f.
Proof. exact (EQ_MP (@lem4879489 A B f) (@lem4879488 A B f)). Qed.
Lemma lem4879491 {A B : Type'} (f : A -> B) (g : A -> B) : term47 A B f g.
Proof. exact (@lem4879490 A B f g). Qed.
Lemma lem4879492 {A B : Type'} (f : A -> B) (g : A -> B) : (term47 A B f g) = ((f = g) = (term48 A B f g)).
Proof. exact (eq_refl (term47 A B f g)). Qed.
Lemma lem4879497 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term48 A B f g).
Proof. exact (EQ_MP (@lem4879492 A B f g) (@lem4879491 A B f g)). Qed.
Lemma lem4879498 {A : Type'} (f : type686 A) (g : type686 A) : (f = g) = (term49 A f g).
Proof. exact (@lem4879497 (A -> Prop) Prop f g). Qed.
Lemma lem4879499 {A : Type'} (P : type686 A) : ((term50 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)) = (term51 A P).
Proof. exact (@lem4879498 A (term50 A P) (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4879508 {A : Type'} (P : type686 A) : (term51 A P) = ((term50 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P)).
Proof. exact (SYM (@lem4879499 A P)). Qed.
Lemma lem4879518 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = True.
Proof. exact (EQ_MP (@lem4879486 A P s) (@lem4879485 A P s)). Qed.
Lemma lem4879519 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = True.
Proof. exact (@lem4879518 A P s). Qed.
Lemma lem4879520 {A : Type'} (P : type686 A) (s : A -> Prop) : (term52 A P s) = True.
Proof. exact (@lem4879519 A (@UNION_OF A (@FINITE (A -> Prop)) P) s). Qed.
Lemma lem4879521 {A : Type'} (P : type686 A) (s : A -> Prop) : True = (term52 A P s).
Proof. exact (SYM (@lem4879520 A P s)). Qed.
Lemma lem4879522 {A : Type'} (P : type686 A) (s : A -> Prop) : term52 A P s.
Proof. exact (EQ_MP (@lem4879521 A P s) (@lem0)). Qed.
Lemma lem4879526 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4879478 A P Q) (@lem4879477 A P Q)). Qed.
Lemma lem4879527 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4879526 A P Q). Qed.
Lemma lem4879528 {A : Type'} (P : type686 A) : (term50 A P) = (term53 A P).
Proof. exact (@lem4879527 A (@FINITE (A -> Prop)) (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4879544 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4879478 A P Q) (@lem4879477 A P Q)). Qed.
Lemma lem4879545 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4879544 A P Q). Qed.
Lemma lem4879546 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term54 A P).
Proof. exact (@lem4879545 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4879563 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4879564 {A : Type'} (P : type686 A) (c : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P c) = (term55 A P c).
Proof. exact (MK_COMB (@lem4879546 A P) (@lem4879563 A c)). Qed.
Lemma lem4879566 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879567 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4879566 (A -> Prop) Prop f y). Qed.
Lemma lem4879568 {A : Type'} (P : type686 A) (c : A -> Prop) : (term58 A P c) = (term55 A P c).
Proof. exact (@lem4879567 A (term54 A P) c). Qed.
Lemma lem4879569 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4879570 {A : Type'} (P : type686 A) : (term60 A P) = (term54 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879569 A P s)). Qed.
Lemma lem4879571 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4879572 {A : Type'} (P : type686 A) (c : A -> Prop) : (term58 A P c) = (term55 A P c).
Proof. exact (MK_COMB (@lem4879570 A P) (@lem4879571 A c)). Qed.
Lemma lem4879573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879574 {A : Type'} (P : type686 A) (c : A -> Prop) : (term61 A P c) = (term62 A P c).
Proof. exact (MK_COMB (@lem4879573) (@lem4879572 A P c)). Qed.
Lemma lem4879575 {A : Type'} (P : type686 A) (c : A -> Prop) : (term55 A P c) = (term59 A P c).
Proof. exact (eq_refl (term55 A P c)). Qed.
Lemma lem4879576 {A : Type'} (P : type686 A) (c : A -> Prop) : ((term58 A P c) = (term55 A P c)) = ((term55 A P c) = (term59 A P c)).
Proof. exact (MK_COMB (@lem4879574 A P c) (@lem4879575 A P c)). Qed.
Lemma lem4879577 {A : Type'} (P : type686 A) (c : A -> Prop) : (term55 A P c) = (term59 A P c).
Proof. exact (EQ_MP (@lem4879576 A P c) (@lem4879568 A P c)). Qed.
Lemma lem4879594 {A : Type'} (P : type686 A) (c : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P c) = (term59 A P c).
Proof. exact (TRANS (@lem4879564 A P c) (@lem4879577 A P c)). Qed.
Lemma lem4879595 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4879596 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term64 A u P c) = (term65 A u P c).
Proof. exact (MK_COMB (@lem4879595 A c u) (@lem4879594 A P c)). Qed.
Lemma lem4879599 {A : Type'} (u : type686 A) (P : type686 A) : (term66 A u P) = (term67 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879596 A u P c)). Qed.
Lemma lem4879600 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879601 {A : Type'} (u : type686 A) (P : type686 A) : (term68 A u P) = (term69 A u P).
Proof. exact (MK_COMB (@lem4879600 A) (@lem4879599 A u P)). Qed.
Lemma lem4879606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4879607 {A : Type'} (u : type686 A) (P : type686 A) : (term70 A u P) = (term71 A u P).
Proof. exact (MK_COMB (@lem4879606) (@lem4879601 A u P)). Qed.
Lemma lem4879610 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4879611 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term72 A P u s) = (term73 A P u s).
Proof. exact (MK_COMB (@lem4879607 A u P) (@lem4879610 A u s)). Qed.
Lemma lem4879614 {A : Type'} (u : type686 A) : (term74 A u) = (term74 A u).
Proof. exact (eq_refl (term74 A u)). Qed.
Lemma lem4879615 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term75 A P u s) = (term76 A P u s).
Proof. exact (MK_COMB (@lem4879614 A u) (@lem4879611 A P u s)). Qed.
Lemma lem4879618 {A : Type'} (P : type686 A) (s : A -> Prop) : (term77 A P s) = (term78 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4879615 A P u s)). Qed.
Lemma lem4879619 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4879620 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term80 A P s).
Proof. exact (MK_COMB (@lem4879619 A) (@lem4879618 A P s)). Qed.
Lemma lem4879625 {A : Type'} (P : type686 A) : (term53 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879620 A P s)). Qed.
Lemma lem4879626 {A : Type'} (P : type686 A) : (term50 A P) = (term81 A P).
Proof. exact (TRANS (@lem4879528 A P) (@lem4879625 A P)). Qed.
Lemma lem4879627 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879628 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (term83 A P s).
Proof. exact (MK_COMB (@lem4879626 A P) (@lem4879627 A s)). Qed.
Lemma lem4879630 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879631 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4879630 (A -> Prop) Prop f y). Qed.
Lemma lem4879632 {A : Type'} (P : type686 A) (s : A -> Prop) : (term84 A P s) = (term83 A P s).
Proof. exact (@lem4879631 A (term81 A P) s). Qed.
Lemma lem4879633 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (eq_refl (term83 A P s)). Qed.
Lemma lem4879634 {A : Type'} (P : type686 A) : (term85 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879633 A P s)). Qed.
Lemma lem4879635 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879636 {A : Type'} (P : type686 A) (s : A -> Prop) : (term84 A P s) = (term83 A P s).
Proof. exact (MK_COMB (@lem4879634 A P) (@lem4879635 A s)). Qed.
Lemma lem4879637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879638 {A : Type'} (P : type686 A) (s : A -> Prop) : (term86 A P s) = (term87 A P s).
Proof. exact (MK_COMB (@lem4879637) (@lem4879636 A P s)). Qed.
Lemma lem4879639 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (eq_refl (term83 A P s)). Qed.
Lemma lem4879640 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term84 A P s) = (term83 A P s)) = ((term83 A P s) = (term80 A P s)).
Proof. exact (MK_COMB (@lem4879638 A P s) (@lem4879639 A P s)). Qed.
Lemma lem4879641 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (EQ_MP (@lem4879640 A P s) (@lem4879632 A P s)). Qed.
Lemma lem4879674 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (term80 A P s).
Proof. exact (TRANS (@lem4879628 A P s) (@lem4879641 A P s)). Qed.
Lemma lem4879675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879676 {A : Type'} (P : type686 A) (s : A -> Prop) : (term88 A P s) = (term89 A P s).
Proof. exact (MK_COMB (@lem4879675) (@lem4879674 A P s)). Qed.
Lemma lem4879678 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4879478 A P Q) (@lem4879477 A P Q)). Qed.
Lemma lem4879679 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4879678 A P Q). Qed.
Lemma lem4879680 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term54 A P).
Proof. exact (@lem4879679 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4879697 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879698 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term55 A P s).
Proof. exact (MK_COMB (@lem4879680 A P) (@lem4879697 A s)). Qed.
Lemma lem4879700 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4879701 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4879700 (A -> Prop) Prop f y). Qed.
Lemma lem4879702 {A : Type'} (P : type686 A) (s : A -> Prop) : (term58 A P s) = (term55 A P s).
Proof. exact (@lem4879701 A (term54 A P) s). Qed.
Lemma lem4879703 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4879704 {A : Type'} (P : type686 A) : (term60 A P) = (term54 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4879703 A P s)). Qed.
Lemma lem4879705 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4879706 {A : Type'} (P : type686 A) (s : A -> Prop) : (term58 A P s) = (term55 A P s).
Proof. exact (MK_COMB (@lem4879704 A P) (@lem4879705 A s)). Qed.
Lemma lem4879707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879708 {A : Type'} (P : type686 A) (s : A -> Prop) : (term61 A P s) = (term62 A P s).
Proof. exact (MK_COMB (@lem4879707) (@lem4879706 A P s)). Qed.
Lemma lem4879709 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4879710 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term58 A P s) = (term55 A P s)) = ((term55 A P s) = (term59 A P s)).
Proof. exact (MK_COMB (@lem4879708 A P s) (@lem4879709 A P s)). Qed.
Lemma lem4879711 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (EQ_MP (@lem4879710 A P s) (@lem4879702 A P s)). Qed.
Lemma lem4879728 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term59 A P s).
Proof. exact (TRANS (@lem4879698 A P s) (@lem4879711 A P s)). Qed.
Lemma lem4879729 {A : Type'} (P : type686 A) (s : A -> Prop) : (term90 A P s) = (term91 A P s).
Proof. exact (MK_COMB (@lem4879676 A P s) (@lem4879728 A P s)). Qed.
Lemma lem4879731 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem4879472 A P Q) (@lem4879471 A P Q)). Qed.
Lemma lem4879732 {A : Type'} (P : type180 A) (Q : Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (@lem4879731 (type686 A) P Q). Qed.
Lemma lem4879733 {A : Type'} (P : type686 A) (s : A -> Prop) : (term94 A P s) = (term95 A P s).
Proof. exact (@lem4879732 A (term78 A P s) (term59 A P s)). Qed.
Lemma lem4879734 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term96 A P s u) = (term76 A P u s).
Proof. exact (eq_refl (term96 A P s u)). Qed.
Lemma lem4879735 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term78 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4879734 A P u s)). Qed.
Lemma lem4879736 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4879737 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term80 A P s).
Proof. exact (MK_COMB (@lem4879736 A) (@lem4879735 A P s)). Qed.
Lemma lem4879738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879739 {A : Type'} (P : type686 A) (s : A -> Prop) : (term99 A P s) = (term89 A P s).
Proof. exact (MK_COMB (@lem4879738) (@lem4879737 A P s)). Qed.
Lemma lem4879740 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term59 A P s).
Proof. exact (eq_refl (term59 A P s)). Qed.
Lemma lem4879741 {A : Type'} (P : type686 A) (s : A -> Prop) : (term94 A P s) = (term91 A P s).
Proof. exact (MK_COMB (@lem4879739 A P s) (@lem4879740 A P s)). Qed.
Lemma lem4879742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879743 {A : Type'} (P : type686 A) (s : A -> Prop) : (term100 A P s) = (term101 A P s).
Proof. exact (MK_COMB (@lem4879742) (@lem4879741 A P s)). Qed.
Lemma lem4879744 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term96 A P s u) = (term76 A P u s).
Proof. exact (eq_refl (term96 A P s u)). Qed.
Lemma lem4879745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879746 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term102 A P s u) = (term103 A P u s).
Proof. exact (MK_COMB (@lem4879745) (@lem4879744 A P u s)). Qed.
Lemma lem4879747 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term59 A P s).
Proof. exact (eq_refl (term59 A P s)). Qed.
Lemma lem4879748 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term104 A u P s) = (term105 A u P s).
Proof. exact (MK_COMB (@lem4879746 A P u s) (@lem4879747 A P s)). Qed.
Lemma lem4879749 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term107 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4879748 A u P s)). Qed.
Lemma lem4879750 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4879751 {A : Type'} (P : type686 A) (s : A -> Prop) : (term95 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4879750 A) (@lem4879749 A P s)). Qed.
Lemma lem4879752 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term94 A P s) = (term95 A P s)) = ((term91 A P s) = (term108 A P s)).
Proof. exact (MK_COMB (@lem4879743 A P s) (@lem4879751 A P s)). Qed.
Lemma lem4879753 {A : Type'} (P : type686 A) (s : A -> Prop) : (term91 A P s) = (term108 A P s).
Proof. exact (EQ_MP (@lem4879752 A P s) (@lem4879733 A P s)). Qed.
Lemma lem4879804 {A : Type'} (P : type686 A) (s : A -> Prop) : (term90 A P s) = (term108 A P s).
Proof. exact (TRANS (@lem4879729 A P s) (@lem4879753 A P s)). Qed.
Lemma lem4879805 {A : Type'} (P : type686 A) (s : A -> Prop) : (term108 A P s) = (term90 A P s).
Proof. exact (SYM (@lem4879804 A P s)). Qed.
Lemma lem4879806 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term76 A P u s.
Proof. exact (h1). Qed.
Lemma lem4879807 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term73 A P u s.
Proof. exact (h1). Qed.
Lemma lem4879808 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4879809 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term73 A P u s.
Proof. exact (h1). Qed.
Lemma lem4879810 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4879811 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : s = (@UNIONS A u).
Proof. exact (SYM (@lem4879810 A u s h1)). Qed.
Lemma lem4879812 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term69 A u P) : term69 A u P.
Proof. exact (h1). Qed.
Lemma lem4879813 {A : Type'} (u : type686 A) (P : type686 A) : (term109 A u P) = (term109 A u P).
Proof. exact (eq_refl (term109 A u P)). Qed.
Lemma lem4879814 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term110 A u P s) = (term111 A P u).
Proof. exact (MK_COMB (@lem4879813 A u P) (@lem4879811 A u s h1)). Qed.
Lemma lem4879815 {A : Type'} (P : type686 A) (u : type686 A) : (term111 A P u) = (term112 A P u).
Proof. exact (eq_refl (term111 A P u)). Qed.
Lemma lem4879816 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term113 A u P s) = (term113 A u P s).
Proof. exact (eq_refl (term113 A u P s)). Qed.
Lemma lem4879817 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term111 A P u)) = ((term110 A u P s) = (term112 A P u)).
Proof. exact (MK_COMB (@lem4879816 A u P s) (@lem4879815 A P u)). Qed.
Lemma lem4879818 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term110 A u P s) = (term114 A u P s).
Proof. exact (eq_refl (term110 A u P s)). Qed.
Lemma lem4879819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879820 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term113 A u P s) = (term115 A u P s).
Proof. exact (MK_COMB (@lem4879819) (@lem4879818 A u P s)). Qed.
Lemma lem4879821 {A : Type'} (P : type686 A) (u : type686 A) : (term112 A P u) = (term112 A P u).
Proof. exact (eq_refl (term112 A P u)). Qed.
Lemma lem4879822 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term112 A P u)) = ((term114 A u P s) = (term112 A P u)).
Proof. exact (MK_COMB (@lem4879820 A u P s) (@lem4879821 A P u)). Qed.
Lemma lem4879823 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term111 A P u)) = ((term114 A u P s) = (term112 A P u)).
Proof. exact (TRANS (@lem4879817 A s P u) (@lem4879822 A s P u)). Qed.
Lemma lem4879824 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term114 A u P s) = (term112 A P u).
Proof. exact (EQ_MP (@lem4879823 A s P u) (@lem4879814 A P u s h1)). Qed.
Lemma lem4879825 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term112 A P u) = (term114 A u P s).
Proof. exact (SYM (@lem4879824 A P u s h1)). Qed.
Lemma lem4879827 {A : Type'} (P : Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem4879466 A P Q) (@lem4879465 A P Q)). Qed.
Lemma lem4879828 {A : Type'} (P : Prop) (Q : type180 A) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem4879827 (type686 A) P Q). Qed.
Lemma lem4879829 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term118 A u P c) = (term119 A u P c).
Proof. exact (@lem4879828 A (@IN (A -> Prop) c u) (term120 A P c)). Qed.
Lemma lem4879830 {A : Type'} (P : type686 A) (u : type686 A) (c : A -> Prop) : (term121 A P c u) = (term122 A P u c).
Proof. exact (eq_refl (term121 A P c u)). Qed.
Lemma lem4879831 {A : Type'} (P : type686 A) (c : A -> Prop) : (term123 A P c) = (term120 A P c).
Proof. exact (fun_ext (fun u : type686 A => @lem4879830 A P u c)). Qed.
Lemma lem4879832 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4879833 {A : Type'} (P : type686 A) (c : A -> Prop) : (term124 A P c) = (term59 A P c).
Proof. exact (MK_COMB (@lem4879832 A) (@lem4879831 A P c)). Qed.
Lemma lem4879834 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4879835 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term118 A u P c) = (term65 A u P c).
Proof. exact (MK_COMB (@lem4879834 A c u) (@lem4879833 A P c)). Qed.
Lemma lem4879836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879837 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term125 A u P c) = (term126 A u P c).
Proof. exact (MK_COMB (@lem4879836) (@lem4879835 A u P c)). Qed.
Lemma lem4879838 {A : Type'} (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term121 A P c u') = (term122 A P u' c).
Proof. exact (eq_refl (term121 A P c u')). Qed.
Lemma lem4879839 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4879840 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term127 A u P c u') = (term128 A u P u' c).
Proof. exact (MK_COMB (@lem4879839 A c u) (@lem4879838 A P u' c)). Qed.
Lemma lem4879841 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term129 A u P c) = (term130 A u P c).
Proof. exact (fun_ext (fun u' : type686 A => @lem4879840 A u P u' c)). Qed.
Lemma lem4879842 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4879843 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term119 A u P c) = (term131 A u P c).
Proof. exact (MK_COMB (@lem4879842 A) (@lem4879841 A u P c)). Qed.
Lemma lem4879844 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : ((term118 A u P c) = (term119 A u P c)) = ((term65 A u P c) = (term131 A u P c)).
Proof. exact (MK_COMB (@lem4879837 A u P c) (@lem4879843 A u P c)). Qed.
Lemma lem4879845 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term65 A u P c) = (term131 A u P c).
Proof. exact (EQ_MP (@lem4879844 A u P c) (@lem4879829 A u P c)). Qed.
Lemma lem4879846 {A : Type'} (u : type686 A) (P : type686 A) : (term67 A u P) = (term132 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879845 A u P c)). Qed.
Lemma lem4879847 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879848 {A : Type'} (u : type686 A) (P : type686 A) : (term69 A u P) = (term133 A u P).
Proof. exact (MK_COMB (@lem4879847 A) (@lem4879846 A u P)). Qed.
Lemma lem4879849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879850 {A : Type'} (u : type686 A) (P : type686 A) : (term134 A u P) = (term135 A u P).
Proof. exact (MK_COMB (@lem4879849) (@lem4879848 A u P)). Qed.
Lemma lem4879851 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4879852 {A : Type'} (P : type686 A) (u : type686 A) : (term112 A P u) = (term137 A P u).
Proof. exact (MK_COMB (@lem4879850 A u P) (@lem4879851 A P u)). Qed.
Lemma lem4879853 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term112 A P u).
Proof. exact (SYM (@lem4879852 A P u)). Qed.
Lemma lem4879857 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem4879460 A B P) (@lem4879459 A B P)). Qed.
Lemma lem4879858 {A : Type'} (P : type599 A) : (term138 A P) = (term139 A P).
Proof. exact (@lem4879857 (A -> Prop) (type686 A) P). Qed.
Lemma lem4879859 {A : Type'} (u : type686 A) (P : type686 A) : (term140 A u P) = (term141 A u P).
Proof. exact (@lem4879858 A (term142 A u P)). Qed.
Lemma lem4879860 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term143 A u P c) = (term130 A u P c).
Proof. exact (eq_refl (term143 A u P c)). Qed.
Lemma lem4879861 {A : Type'} (u' : type686 A) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem4879862 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) (u' : type686 A) : (term144 A u P c u') = (term145 A u P c u').
Proof. exact (MK_COMB (@lem4879860 A u P c) (@lem4879861 A u')). Qed.
Lemma lem4879863 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term145 A u P c u') = (term128 A u P u' c).
Proof. exact (eq_refl (term145 A u P c u')). Qed.
Lemma lem4879864 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term144 A u P c u') = (term128 A u P u' c).
Proof. exact (TRANS (@lem4879862 A u P c u') (@lem4879863 A u P u' c)). Qed.
Lemma lem4879865 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term146 A u P c) = (term130 A u P c).
Proof. exact (fun_ext (fun u' : type686 A => @lem4879864 A u P u' c)). Qed.
Lemma lem4879866 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4879867 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term147 A u P c) = (term131 A u P c).
Proof. exact (MK_COMB (@lem4879866 A) (@lem4879865 A u P c)). Qed.
Lemma lem4879868 {A : Type'} (u : type686 A) (P : type686 A) : (term148 A u P) = (term132 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879867 A u P c)). Qed.
Lemma lem4879869 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879870 {A : Type'} (u : type686 A) (P : type686 A) : (term140 A u P) = (term133 A u P).
Proof. exact (MK_COMB (@lem4879869 A) (@lem4879868 A u P)). Qed.
Lemma lem4879871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879872 {A : Type'} (u : type686 A) (P : type686 A) : (term149 A u P) = (term150 A u P).
Proof. exact (MK_COMB (@lem4879871) (@lem4879870 A u P)). Qed.
Lemma lem4879873 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term143 A u P c) = (term130 A u P c).
Proof. exact (eq_refl (term143 A u P c)). Qed.
Lemma lem4879874 {A : Type'} (u' : type639 A) (c : A -> Prop) : (u' c) = (u' c).
Proof. exact (eq_refl (u' c)). Qed.
Lemma lem4879875 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term151 A u P u' c) = (term152 A u P u' c).
Proof. exact (MK_COMB (@lem4879873 A u P c) (@lem4879874 A u' c)). Qed.
Lemma lem4879876 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term152 A u P u' c) = (term153 A u P u' c).
Proof. exact (eq_refl (term152 A u P u' c)). Qed.
Lemma lem4879877 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term151 A u P u' c) = (term153 A u P u' c).
Proof. exact (TRANS (@lem4879875 A u P u' c) (@lem4879876 A u P u' c)). Qed.
Lemma lem4879878 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term154 A u P u') = (term155 A u P u').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4879877 A u P u' c)). Qed.
Lemma lem4879879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4879880 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term156 A u P u') = (term157 A u P u').
Proof. exact (MK_COMB (@lem4879879 A) (@lem4879878 A u P u')). Qed.
Lemma lem4879881 {A : Type'} (u : type686 A) (P : type686 A) : (term158 A u P) = (term159 A u P).
Proof. exact (fun_ext (fun u' : type639 A => @lem4879880 A u P u')). Qed.
Lemma lem4879882 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4879883 {A : Type'} (u : type686 A) (P : type686 A) : (term141 A u P) = (term160 A u P).
Proof. exact (MK_COMB (@lem4879882 A) (@lem4879881 A u P)). Qed.
Lemma lem4879884 {A : Type'} (u : type686 A) (P : type686 A) : ((term140 A u P) = (term141 A u P)) = ((term133 A u P) = (term160 A u P)).
Proof. exact (MK_COMB (@lem4879872 A u P) (@lem4879883 A u P)). Qed.
Lemma lem4879885 {A : Type'} (u : type686 A) (P : type686 A) : (term133 A u P) = (term160 A u P).
Proof. exact (EQ_MP (@lem4879884 A u P) (@lem4879859 A u P)). Qed.
Lemma lem4879908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879909 {A : Type'} (u : type686 A) (P : type686 A) : (term135 A u P) = (term161 A u P).
Proof. exact (MK_COMB (@lem4879908) (@lem4879885 A u P)). Qed.
Lemma lem4879926 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4879927 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term162 A P u).
Proof. exact (MK_COMB (@lem4879909 A u P) (@lem4879926 A P u)). Qed.
Lemma lem4879929 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem4879457 A P Q) (@lem4879456 A P Q)). Qed.
Lemma lem4879930 {A : Type'} (P : type141 A) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem4879929 (type639 A) P Q). Qed.
Lemma lem4879931 {A : Type'} (P : type686 A) (u : type686 A) : (term165 A P u) = (term166 A P u).
Proof. exact (@lem4879930 A (term159 A u P) (term136 A P u)). Qed.
Lemma lem4879932 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term167 A u P u') = (term157 A u P u').
Proof. exact (eq_refl (term167 A u P u')). Qed.
Lemma lem4879933 {A : Type'} (u : type686 A) (P : type686 A) : (term168 A u P) = (term159 A u P).
Proof. exact (fun_ext (fun u' : type639 A => @lem4879932 A u P u')). Qed.
Lemma lem4879934 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4879935 {A : Type'} (u : type686 A) (P : type686 A) : (term169 A u P) = (term160 A u P).
Proof. exact (MK_COMB (@lem4879934 A) (@lem4879933 A u P)). Qed.
Lemma lem4879936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879937 {A : Type'} (u : type686 A) (P : type686 A) : (term170 A u P) = (term161 A u P).
Proof. exact (MK_COMB (@lem4879936) (@lem4879935 A u P)). Qed.
Lemma lem4879938 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4879939 {A : Type'} (P : type686 A) (u : type686 A) : (term165 A P u) = (term162 A P u).
Proof. exact (MK_COMB (@lem4879937 A u P) (@lem4879938 A P u)). Qed.
Lemma lem4879940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4879941 {A : Type'} (P : type686 A) (u : type686 A) : (term171 A P u) = (term172 A P u).
Proof. exact (MK_COMB (@lem4879940) (@lem4879939 A P u)). Qed.
Lemma lem4879942 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term167 A u P u') = (term157 A u P u').
Proof. exact (eq_refl (term167 A u P u')). Qed.
Lemma lem4879943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4879944 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term173 A u P u') = (term174 A u P u').
Proof. exact (MK_COMB (@lem4879943) (@lem4879942 A u P u')). Qed.
Lemma lem4879945 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4879946 {A : Type'} (u' : type639 A) (P : type686 A) (u : type686 A) : (term175 A u' P u) = (term176 A u' P u).
Proof. exact (MK_COMB (@lem4879944 A u P u') (@lem4879945 A P u)). Qed.
Lemma lem4879947 {A : Type'} (P : type686 A) (u : type686 A) : (term177 A P u) = (term178 A P u).
Proof. exact (fun_ext (fun u' : type639 A => @lem4879946 A u' P u)). Qed.
Lemma lem4879948 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4879949 {A : Type'} (P : type686 A) (u : type686 A) : (term166 A P u) = (term179 A P u).
Proof. exact (MK_COMB (@lem4879948 A) (@lem4879947 A P u)). Qed.
Lemma lem4879950 {A : Type'} (P : type686 A) (u : type686 A) : ((term165 A P u) = (term166 A P u)) = ((term162 A P u) = (term179 A P u)).
Proof. exact (MK_COMB (@lem4879941 A P u) (@lem4879949 A P u)). Qed.
Lemma lem4879951 {A : Type'} (P : type686 A) (u : type686 A) : (term162 A P u) = (term179 A P u).
Proof. exact (EQ_MP (@lem4879950 A P u) (@lem4879931 A P u)). Qed.
Lemma lem4879992 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term179 A P u).
Proof. exact (TRANS (@lem4879927 A P u) (@lem4879951 A P u)). Qed.
Lemma lem4879993 {A : Type'} (P : type686 A) (u : type686 A) : (term179 A P u) = (term137 A P u).
Proof. exact (SYM (@lem4879992 A P u)). Qed.
Lemma lem4879994 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term157 A u P f.
Proof. exact (h1). Qed.
Lemma lem4879995 {A B C : Type'} (f : type1412 A B C) : term180 A B C f.
Proof. exact (@lem4323219 A B C f). Qed.
Lemma lem4879996 {A B C : Type'} (f : type1412 A B C) : (term180 A B C f) = (term181 A B C f).
Proof. exact (eq_refl (term180 A B C f)). Qed.
Lemma lem4879997 {A B C : Type'} (f : type1412 A B C) : term181 A B C f.
Proof. exact (EQ_MP (@lem4879996 A B C f) (@lem4879995 A B C f)). Qed.
Lemma lem4879998 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) : term182 A B C f s.
Proof. exact (@lem4879997 A B C f s). Qed.
Lemma lem4879999 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : (term182 A B C f s) = (term183 A B C s f).
Proof. exact (eq_refl (term182 A B C f s)). Qed.
Lemma lem4880000 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : term183 A B C s f.
Proof. exact (EQ_MP (@lem4879999 A B C s f) (@lem4879998 A B C f s)). Qed.
Lemma lem4880001 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) (t : type1413 A B) : term184 A B C s f t.
Proof. exact (@lem4880000 A B C s f t). Qed.
Lemma lem4880002 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term184 A B C s f t) = (term185 A B C s t f).
Proof. exact (eq_refl (term184 A B C s f t)). Qed.
Lemma lem4880003 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term185 A B C s t f.
Proof. exact (EQ_MP (@lem4880002 A B C s t f) (@lem4880001 A B C s f t)). Qed.
Lemma lem4880004 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term186 A B s t) : term186 A B s t.
Proof. exact (h1). Qed.
Lemma lem4880005 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term186 A B s t) : term187 A B C s t f.
Proof. exact (@lem4880003 A B C s t f (@lem4880004 A B s t h1)). Qed.
Lemma lem4880006 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term187 A B C s t f) = ((term187 A B C s t f) = True).
Proof. exact (@lem7 (term187 A B C s t f)). Qed.
Lemma lem4880007 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term186 A B s t) : (term187 A B C s t f) = True.
Proof. exact (EQ_MP (@lem4880006 A B C s t f) (@lem4880005 A B C f s t h1)). Qed.
Lemma lem4880013 {A B : Type'} (f : A -> B) : term188 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4880014 {A B : Type'} (f : A -> B) : (term188 A B f) = (term189 A B f).
Proof. exact (eq_refl (term188 A B f)). Qed.
Lemma lem4880015 {A B : Type'} (f : A -> B) : term189 A B f.
Proof. exact (EQ_MP (@lem4880014 A B f) (@lem4880013 A B f)). Qed.
Lemma lem4880016 {A B : Type'} (f : A -> B) (s : A -> Prop) : term190 A B f s.
Proof. exact (@lem4880015 A B f s). Qed.
Lemma lem4880017 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term190 A B f s) = (term191 A B f s).
Proof. exact (eq_refl (term190 A B f s)). Qed.
Lemma lem4880018 {A B : Type'} (f : A -> B) (s : A -> Prop) : term191 A B f s.
Proof. exact (EQ_MP (@lem4880017 A B f s) (@lem4880016 A B f s)). Qed.
Lemma lem4880019 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4880020 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term192 A B f s.
Proof. exact (@lem4880018 A B f s (@lem4880019 A s h1)). Qed.
Lemma lem4880021 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term192 A B f s) = ((term192 A B f s) = True).
Proof. exact (@lem7 (term192 A B f s)). Qed.
Lemma lem4880022 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term192 A B f s) = True.
Proof. exact (EQ_MP (@lem4880021 A B f s) (@lem4880020 A B f s h1)). Qed.
Lemma lem4880028 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4880030 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term193 A u P f c.
Proof. exact (@lem4879994 A u P f h1 c). Qed.
Lemma lem4880031 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term193 A u P f c) = (term153 A u P f c).
Proof. exact (eq_refl (term193 A u P f c)). Qed.
Lemma lem4880032 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term153 A u P f c.
Proof. exact (EQ_MP (@lem4880031 A u P f c) (@lem4880030 A c u P f h1)). Qed.
Lemma lem4880033 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4880034 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) (u : type686 A) (h1 : term157 A u P f) (h2 : @IN (A -> Prop) c u) : term194 A P f c.
Proof. exact (@lem4880032 A c u P f h1 (@lem4880033 A c u h2)). Qed.
Lemma lem4880086 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) (u : type686 A) (h1 : term157 A u P f) (h2 : @IN (A -> Prop) c u) : term195 A f c.
Proof. exact (proj1 (@lem4880034 A P f c u h1 h2)). Qed.
Lemma lem4880087 {A : Type'} (f : type639 A) (c : A -> Prop) : (term195 A f c) = ((term195 A f c) = True).
Proof. exact (@lem7 (term195 A f c)). Qed.
Lemma lem4880088 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) (u : type686 A) (h1 : term157 A u P f) (h2 : @IN (A -> Prop) c u) : (term195 A f c) = True.
Proof. exact (EQ_MP (@lem4880087 A f c) (@lem4880086 A P f c u h1 h2)). Qed.
Lemma lem4880097 {A B : Type'} (f : A -> B) (s : A -> Prop) : term196 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4880022 A B f s h0). Qed.
Lemma lem4880098 {A : Type'} (f : type1170 A) (s : type1171 A) : term197 A f s.
Proof. exact (@lem4880097 (type1643 A) (A -> Prop) f s). Qed.
Lemma lem4880099 {A : Type'} (u : type686 A) (f : type639 A) : term198 A u f.
Proof. exact (@lem4880098 A (@snd (A -> Prop) (A -> Prop)) (term199 A u f)). Qed.
Lemma lem4880101 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term200 A B C s t f.
Proof. exact (fun h0 : term186 A B s t => @lem4880007 A B C f s t h0). Qed.
Lemma lem4880102 {A : Type'} (s : type686 A) (t : type639 A) (f : type637 A) : term201 A s t f.
Proof. exact (@lem4880101 (A -> Prop) (A -> Prop) (type1643 A) s t f). Qed.
Lemma lem4880103 {A : Type'} (u : type686 A) (f : type639 A) : term202 A u f.
Proof. exact (@lem4880102 A u f (@pair (A -> Prop) (A -> Prop))). Qed.
Lemma lem4880107 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4880028 A u) (@lem4879808 A u h1)). Qed.
Lemma lem4880108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880109 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term74 A u) = (and True).
Proof. exact (MK_COMB (@lem4880108) (@lem4880107 A u h1)). Qed.
Lemma lem4880117 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term203 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4880118 (p : Prop) (q : Prop) (p' : Prop) : term204 p q p'.
Proof. exact (fun q' : Prop => @lem4880117 p q p' q'). Qed.
Lemma lem4880119 (p : Prop) (q : Prop) : term205 p q.
Proof. exact (fun p' : Prop => @lem4880118 p q p'). Qed.
Lemma lem4880120 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : term206 A u f s.
Proof. exact (@lem4880119 (@IN (A -> Prop) s u) (term195 A f s)). Qed.
Lemma lem4880121 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) : term207 A u f s p'.
Proof. exact (@lem4880120 A u f s p'). Qed.
Lemma lem4880122 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) : (term207 A u f s p') = (term208 A u f s p').
Proof. exact (eq_refl (term207 A u f s p')). Qed.
Lemma lem4880123 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) : term208 A u f s p'.
Proof. exact (EQ_MP (@lem4880122 A u f s p') (@lem4880121 A u f s p')). Qed.
Lemma lem4880124 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term209 A u f s p' q'.
Proof. exact (@lem4880123 A u f s p' q'). Qed.
Lemma lem4880125 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term209 A u f s p' q') = (term210 A u f s p' q').
Proof. exact (eq_refl (term209 A u f s p' q')). Qed.
Lemma lem4880126 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term210 A u f s p' q'.
Proof. exact (EQ_MP (@lem4880125 A u f s p' q') (@lem4880124 A u f s p' q')). Qed.
Lemma lem4880127 {A : Type'} (s : A -> Prop) (u : type686 A) : (@IN (A -> Prop) s u) = (@IN (A -> Prop) s u).
Proof. exact (eq_refl (@IN (A -> Prop) s u)). Qed.
Lemma lem4880128 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (q' : Prop) : term211 A f s u q'.
Proof. exact (@lem4880126 A u f s (@IN (A -> Prop) s u) q'). Qed.
Lemma lem4880129 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (q' : Prop) : term212 A f s u q'.
Proof. exact (@lem4880128 A f s u q' (@lem4880127 A s u)). Qed.
Lemma lem4880130 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) s u) : @IN (A -> Prop) s u.
Proof. exact (h1). Qed.
Lemma lem4880131 {A : Type'} (s : A -> Prop) (u : type686 A) : (@IN (A -> Prop) s u) = ((@IN (A -> Prop) s u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) s u)). Qed.
Lemma lem4880134 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term213 A u f c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4880088 A P f c u h1 h0). Qed.
Lemma lem4880135 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term213 A u f c.
Proof. exact (@lem4880134 A c u P f h1). Qed.
Lemma lem4880136 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term213 A u f s.
Proof. exact (@lem4880135 A s u P f h1). Qed.
Lemma lem4880138 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) s u) : (@IN (A -> Prop) s u) = True.
Proof. exact (EQ_MP (@lem4880131 A s u) (@lem4880130 A s u h1)). Qed.
Lemma lem4880139 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) s u) : True = (@IN (A -> Prop) s u).
Proof. exact (SYM (@lem4880138 A s u h1)). Qed.
Lemma lem4880140 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) s u) : @IN (A -> Prop) s u.
Proof. exact (EQ_MP (@lem4880139 A s u h1) (@lem0)). Qed.
Lemma lem4880141 {A : Type'} (P : type686 A) (f : type639 A) (s : A -> Prop) (u : type686 A) (h1 : term157 A u P f) (h2 : @IN (A -> Prop) s u) : (term195 A f s) = True.
Proof. exact (@lem4880136 A s u P f h1 (@lem4880140 A s u h2)). Qed.
Lemma lem4880142 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term213 A u f s.
Proof. exact (fun h0 : @IN (A -> Prop) s u => @lem4880141 A P f s u h1 h0). Qed.
Lemma lem4880143 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) : term214 A f s u.
Proof. exact (@lem4880129 A f s u True). Qed.
Lemma lem4880144 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : (term215 A u f s) = (term216 A s u).
Proof. exact (@lem4880143 A f s u (@lem4880142 A s u P f h1)). Qed.
Lemma lem4880146 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4880147 {A : Type'} (s : A -> Prop) (u : type686 A) : (term216 A s u) = True.
Proof. exact (@lem4880146 (@IN (A -> Prop) s u)). Qed.
Lemma lem4880148 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : (term215 A u f s) = True.
Proof. exact (TRANS (@lem4880144 A s u P f h1) (@lem4880147 A s u)). Qed.
Lemma lem4880149 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : (term217 A u f) = (term218 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880148 A s u P f h1)). Qed.
Lemma lem4880150 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880151 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : (term219 A u f) = (term220 A).
Proof. exact (MK_COMB (@lem4880150 A) (@lem4880149 A u P f h1)). Qed.
Lemma lem4880153 {A : Type'} (t : Prop) : (term221 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4880154 {A : Type'} (t : Prop) : (term222 A t) = t.
Proof. exact (@lem4880153 (A -> Prop) t). Qed.
Lemma lem4880155 {A : Type'} : (term220 A) = True.
Proof. exact (@lem4880154 A True). Qed.
Lemma lem4880156 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : (term219 A u f) = True.
Proof. exact (TRANS (@lem4880151 A u P f h1) (@lem4880155 A)). Qed.
Lemma lem4880157 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term223 A u f) = (True /\ True).
Proof. exact (MK_COMB (@lem4880109 A u h2) (@lem4880156 A u P f h1)). Qed.
Lemma lem4880159 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4880160 : (True /\ True) = True.
Proof. exact (@lem4880159 True). Qed.
Lemma lem4880161 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term223 A u f) = True.
Proof. exact (TRANS (@lem4880157 A P f u h1 h2) (@lem4880160)). Qed.
Lemma lem4880162 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : True = (term223 A u f).
Proof. exact (SYM (@lem4880161 A P f u h1 h2)). Qed.
Lemma lem4880163 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term223 A u f.
Proof. exact (EQ_MP (@lem4880162 A P f u h1 h2) (@lem0)). Qed.
Lemma lem4880164 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term224 A u f) = True.
Proof. exact (@lem4880103 A u f (@lem4880163 A P f u h1 h2)). Qed.
Lemma lem4880165 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : True = (term224 A u f).
Proof. exact (SYM (@lem4880164 A P f u h1 h2)). Qed.
Lemma lem4880166 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term224 A u f.
Proof. exact (EQ_MP (@lem4880165 A P f u h1 h2) (@lem0)). Qed.
Lemma lem4880167 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term225 A u f) = True.
Proof. exact (@lem4880099 A u f (@lem4880166 A P f u h1 h2)). Qed.
Lemma lem4880168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880169 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term226 A u f) = (and True).
Proof. exact (MK_COMB (@lem4880168) (@lem4880167 A P f u h1 h2)). Qed.
Lemma lem4880255 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term227 A P f u) = (term227 A P f u).
Proof. exact (eq_refl (term227 A P f u)). Qed.
Lemma lem4880256 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term228 A P f u) = (term229 A P f u).
Proof. exact (MK_COMB (@lem4880169 A P f u h1 h2) (@lem4880255 A P f u)). Qed.
Lemma lem4880258 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4880259 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term229 A P f u) = (term227 A P f u).
Proof. exact (@lem4880258 (term227 A P f u)). Qed.
Lemma lem4880345 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term228 A P f u) = (term227 A P f u).
Proof. exact (TRANS (@lem4880256 A P f u h1 h2) (@lem4880259 A P f u)). Qed.
Lemma lem4880346 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term227 A P f u) = (term228 A P f u).
Proof. exact (SYM (@lem4880345 A P f u h1 h2)). Qed.
Lemma lem4880350 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term22 _87967 _87968 f s P) = (term23 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4879451 _87967 _87968 s P f) (@lem4879450 _87967 _87968 P f s)). Qed.
Lemma lem4880351 {A : Type'} (s : type1171 A) (P : type686 A) (f : type1170 A) : (term230 A f s P) = (term231 A s P f).
Proof. exact (@lem4880350 (A -> Prop) (type1643 A) s P f). Qed.
Lemma lem4880352 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term232 A u f P) = (term233 A u f P).
Proof. exact (@lem4880351 A (term199 A u f) P (@snd (A -> Prop) (A -> Prop))). Qed.
Lemma lem4880354 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term17 _88961 _88962 _89106 P f Q) = (term18 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem4879438 _88961 _88962 _89106 P Q f) (@lem4879437 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4880355 {A : Type'} (P : type639 A) (Q : type1171 A) (f : type637 A) : (term234 A P f Q) = (term235 A P Q f).
Proof. exact (@lem4880354 (A -> Prop) (A -> Prop) (type1643 A) P Q f). Qed.
Lemma lem4880356 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term236 A u f P) = (term237 A u f P).
Proof. exact (@lem4880355 A (term238 A u f) (term239 A P) (@pair (A -> Prop) (A -> Prop))). Qed.
Lemma lem4880357 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term240 A u f s) = (term241 A u f s).
Proof. exact (eq_refl (term240 A u f s)). Qed.
Lemma lem4880358 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4880359 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term242 A u f s t) = (term243 A u f s t).
Proof. exact (MK_COMB (@lem4880357 A u f s) (@lem4880358 A t)). Qed.
Lemma lem4880360 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term243 A u f s t) = (term244 A u t f s).
Proof. exact (eq_refl (term243 A u f s t)). Qed.
Lemma lem4880361 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term242 A u f s t) = (term244 A u t f s).
Proof. exact (TRANS (@lem4880359 A u f s t) (@lem4880360 A u t f s)). Qed.
Lemma lem4880362 {A : Type'} (GEN_PVAR_214 : type1643 A) : (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214) = (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214).
Proof. exact (eq_refl (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214)). Qed.
Lemma lem4880363 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term245 A GEN_PVAR_214 u f s t) = (term246 A GEN_PVAR_214 u t f s).
Proof. exact (MK_COMB (@lem4880362 A GEN_PVAR_214) (@lem4880361 A u t f s)). Qed.
Lemma lem4880364 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@pair (A -> Prop) (A -> Prop) s t) = (@pair (A -> Prop) (A -> Prop) s t).
Proof. exact (eq_refl (@pair (A -> Prop) (A -> Prop) s t)). Qed.
Lemma lem4880365 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term247 A GEN_PVAR_214 u f s t) = (term248 A GEN_PVAR_214 u f s t).
Proof. exact (MK_COMB (@lem4880363 A GEN_PVAR_214 u t f s) (@lem4880364 A s t)). Qed.
Lemma lem4880366 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term249 A GEN_PVAR_214 u f s) = (term250 A GEN_PVAR_214 u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880365 A GEN_PVAR_214 u f s t)). Qed.
Lemma lem4880367 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4880368 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term251 A GEN_PVAR_214 u f s) = (term252 A GEN_PVAR_214 u f s).
Proof. exact (MK_COMB (@lem4880367 A) (@lem4880366 A GEN_PVAR_214 u f s)). Qed.
Lemma lem4880369 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) : (term253 A GEN_PVAR_214 u f) = (term254 A GEN_PVAR_214 u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880368 A GEN_PVAR_214 u f s)). Qed.
Lemma lem4880370 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4880371 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) : (term255 A GEN_PVAR_214 u f) = (term256 A GEN_PVAR_214 u f).
Proof. exact (MK_COMB (@lem4880370 A) (@lem4880369 A GEN_PVAR_214 u f)). Qed.
Lemma lem4880372 {A : Type'} (u : type686 A) (f : type639 A) : (term257 A u f) = (term258 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_214 : type1643 A => @lem4880371 A GEN_PVAR_214 u f)). Qed.
Lemma lem4880373 {A : Type'} : (@GSPEC (prod (A -> Prop) (A -> Prop))) = (@GSPEC (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@GSPEC (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4880374 {A : Type'} (u : type686 A) (f : type639 A) : (term259 A u f) = (term199 A u f).
Proof. exact (MK_COMB (@lem4880373 A) (@lem4880372 A u f)). Qed.
Lemma lem4880375 {A : Type'} (x : type1643 A) : (@IN (prod (A -> Prop) (A -> Prop)) x) = (@IN (prod (A -> Prop) (A -> Prop)) x).
Proof. exact (eq_refl (@IN (prod (A -> Prop) (A -> Prop)) x)). Qed.
Lemma lem4880376 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term260 A x u f) = (term261 A x u f).
Proof. exact (MK_COMB (@lem4880375 A x) (@lem4880374 A u f)). Qed.
Lemma lem4880377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880378 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term262 A x u f) = (term263 A x u f).
Proof. exact (MK_COMB (@lem4880377) (@lem4880376 A x u f)). Qed.
Lemma lem4880379 {A : Type'} (P : type686 A) (x : type1643 A) : (term264 A P x) = (term265 A P x).
Proof. exact (eq_refl (term264 A P x)). Qed.
Lemma lem4880380 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (x : type1643 A) : (term266 A u f P x) = (term267 A u f P x).
Proof. exact (MK_COMB (@lem4880378 A x u f) (@lem4880379 A P x)). Qed.
Lemma lem4880381 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term268 A u f P) = (term269 A u f P).
Proof. exact (fun_ext (fun x : type1643 A => @lem4880380 A u f P x)). Qed.
Lemma lem4880382 {A : Type'} : (@all (prod (A -> Prop) (A -> Prop))) = (@all (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@all (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4880383 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term236 A u f P) = (term233 A u f P).
Proof. exact (MK_COMB (@lem4880382 A) (@lem4880381 A u f P)). Qed.
Lemma lem4880384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4880385 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term270 A u f P) = (term271 A u f P).
Proof. exact (MK_COMB (@lem4880384) (@lem4880383 A u f P)). Qed.
Lemma lem4880386 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term240 A u f s) = (term241 A u f s).
Proof. exact (eq_refl (term240 A u f s)). Qed.
Lemma lem4880387 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4880388 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term242 A u f s t) = (term243 A u f s t).
Proof. exact (MK_COMB (@lem4880386 A u f s) (@lem4880387 A t)). Qed.
Lemma lem4880389 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term243 A u f s t) = (term244 A u t f s).
Proof. exact (eq_refl (term243 A u f s t)). Qed.
Lemma lem4880390 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term242 A u f s t) = (term244 A u t f s).
Proof. exact (TRANS (@lem4880388 A u f s t) (@lem4880389 A u t f s)). Qed.
Lemma lem4880391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880392 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term272 A u f s t) = (term273 A u t f s).
Proof. exact (MK_COMB (@lem4880391) (@lem4880390 A u t f s)). Qed.
Lemma lem4880393 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term274 A P s t) = (term275 A P s t).
Proof. exact (eq_refl (term274 A P s t)). Qed.
Lemma lem4880394 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term276 A u f P s t) = (term277 A u f P s t).
Proof. exact (MK_COMB (@lem4880392 A u t f s) (@lem4880393 A P s t)). Qed.
Lemma lem4880395 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) : (term278 A u f P s) = (term279 A u f P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880394 A u f P s t)). Qed.
Lemma lem4880396 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880397 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) : (term280 A u f P s) = (term281 A u f P s).
Proof. exact (MK_COMB (@lem4880396 A) (@lem4880395 A u f P s)). Qed.
Lemma lem4880398 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term282 A u f P) = (term283 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880397 A u f P s)). Qed.
Lemma lem4880399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880400 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term237 A u f P) = (term284 A u f P).
Proof. exact (MK_COMB (@lem4880399 A) (@lem4880398 A u f P)). Qed.
Lemma lem4880401 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : ((term236 A u f P) = (term237 A u f P)) = ((term233 A u f P) = (term284 A u f P)).
Proof. exact (MK_COMB (@lem4880385 A u f P) (@lem4880400 A u f P)). Qed.
Lemma lem4880402 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term233 A u f P) = (term284 A u f P).
Proof. exact (EQ_MP (@lem4880401 A u f P) (@lem4880356 A u f P)). Qed.
Lemma lem4880407 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term232 A u f P) = (term284 A u f P).
Proof. exact (TRANS (@lem4880352 A u f P) (@lem4880402 A u f P)). Qed.
Lemma lem4880417 {A B : Type'} (x : A) (y : B) : (term285 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4880418 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term286 A x y) = y.
Proof. exact (@lem4880417 (A -> Prop) (A -> Prop) x y). Qed.
Lemma lem4880419 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term286 A s t) = t.
Proof. exact (@lem4880418 A s t). Qed.
Lemma lem4880420 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4880421 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term275 A P s t) = (P t).
Proof. exact (MK_COMB (@lem4880420 A P) (@lem4880419 A s t)). Qed.
Lemma lem4880422 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term273 A u t f s) = (term273 A u t f s).
Proof. exact (eq_refl (term273 A u t f s)). Qed.
Lemma lem4880423 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term277 A u f P s t) = (term287 A u f s P t).
Proof. exact (MK_COMB (@lem4880422 A u t f s) (@lem4880421 A s P t)). Qed.
Lemma lem4880426 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term279 A u f P s) = (term288 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880423 A u f s P t)). Qed.
Lemma lem4880427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880428 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term281 A u f P s) = (term289 A u f s P).
Proof. exact (MK_COMB (@lem4880427 A) (@lem4880426 A u f s P)). Qed.
Lemma lem4880433 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term283 A u f P) = (term290 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880428 A u f s P)). Qed.
Lemma lem4880434 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880435 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term284 A u f P) = (term291 A u f P).
Proof. exact (MK_COMB (@lem4880434 A) (@lem4880433 A u f P)). Qed.
Lemma lem4880440 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term232 A u f P) = (term291 A u f P).
Proof. exact (TRANS (@lem4880407 A u f P) (@lem4880435 A u f P)). Qed.
Lemma lem4880441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880442 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term292 A u f P) = (term293 A u f P).
Proof. exact (MK_COMB (@lem4880441) (@lem4880440 A u f P)). Qed.
Lemma lem4880455 {A : Type'} (f : type639 A) (u : type686 A) : ((term294 A u f) = (@UNIONS A u)) = ((term294 A u f) = (@UNIONS A u)).
Proof. exact (eq_refl ((term294 A u f) = (@UNIONS A u))). Qed.
Lemma lem4880456 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term227 A P f u) = (term295 A P f u).
Proof. exact (MK_COMB (@lem4880442 A u f P) (@lem4880455 A f u)). Qed.
Lemma lem4880459 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term295 A P f u) = (term227 A P f u).
Proof. exact (SYM (@lem4880456 A P f u)). Qed.
Lemma lem4880470 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term296 A P f u.
Proof. exact (conj (@lem4879994 A u P f h1) (@lem4879808 A u h2)). Qed.
Lemma lem4880494 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4880495 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (@lem4880494 A s t). Qed.
Lemma lem4880496 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term298 A f c) = c) = (term299 A f c).
Proof. exact (@lem4880495 A (term298 A f c) c). Qed.
Lemma lem4880505 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term300 A f c P) = (term300 A f c P).
Proof. exact (eq_refl (term300 A f c P)). Qed.
Lemma lem4880506 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4880505 A f c P) (@lem4880496 A f c)). Qed.
Lemma lem4880509 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4880510 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term194 A P f c) = (term304 A P f c).
Proof. exact (MK_COMB (@lem4880509 A f c) (@lem4880506 A P f c)). Qed.
Lemma lem4880513 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4880514 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term153 A u P f c) = (term305 A u P f c).
Proof. exact (MK_COMB (@lem4880513 A c u) (@lem4880510 A P f c)). Qed.
Lemma lem4880517 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term155 A u P f) = (term306 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4880514 A u P f c)). Qed.
Lemma lem4880518 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880519 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term157 A u P f) = (term307 A u P f).
Proof. exact (MK_COMB (@lem4880518 A) (@lem4880517 A u P f)). Qed.
Lemma lem4880524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880525 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term308 A u P f) = (term309 A u P f).
Proof. exact (MK_COMB (@lem4880524) (@lem4880519 A u P f)). Qed.
Lemma lem4880526 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4880527 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term296 A P f u) = (term310 A P f u).
Proof. exact (MK_COMB (@lem4880525 A u P f) (@lem4880526 A u)). Qed.
Lemma lem4880530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880531 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term311 A P f u) = (term312 A P f u).
Proof. exact (MK_COMB (@lem4880530) (@lem4880527 A P f u)). Qed.
Lemma lem4880544 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term291 A u f P) = (term291 A u f P).
Proof. exact (eq_refl (term291 A u f P)). Qed.
Lemma lem4880545 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term313 A u f P) = (term314 A u f P).
Proof. exact (MK_COMB (@lem4880531 A P f u) (@lem4880544 A u f P)). Qed.
Lemma lem4880548 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term314 A u f P) = (term313 A u f P).
Proof. exact (SYM (@lem4880545 A u f P)). Qed.
Lemma lem4880560 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880561 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4880560 (A -> Prop) P x). Qed.
Lemma lem4880562 {A : Type'} (u : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c u) = (u c).
Proof. exact (@lem4880561 A u c). Qed.
Lemma lem4880563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880564 {A : Type'} (u : type686 A) (c : A -> Prop) : (term63 A c u) = (term315 A u c).
Proof. exact (MK_COMB (@lem4880563) (@lem4880562 A u c)). Qed.
Lemma lem4880576 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880577 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4880576 (A -> Prop) P x). Qed.
Lemma lem4880578 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term316 A c' f c) = (f c c').
Proof. exact (@lem4880577 A (f c) c'). Qed.
Lemma lem4880579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880580 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term317 A c' f c) = (term318 A f c c').
Proof. exact (MK_COMB (@lem4880579) (@lem4880578 A f c c')). Qed.
Lemma lem4880581 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (P c').
Proof. exact (eq_refl (P c')). Qed.
Lemma lem4880582 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term319 A f c P c') = (term320 A f c P c').
Proof. exact (MK_COMB (@lem4880580 A f c c') (@lem4880581 A P c')). Qed.
Lemma lem4880585 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term321 A f c P) = (term322 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4880582 A f c P c')). Qed.
Lemma lem4880586 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880587 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term323 A f c P) = (term324 A f c P).
Proof. exact (MK_COMB (@lem4880586 A) (@lem4880585 A f c P)). Qed.
Lemma lem4880592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880593 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term300 A f c P) = (term325 A f c P).
Proof. exact (MK_COMB (@lem4880592) (@lem4880587 A f c P)). Qed.
Lemma lem4880601 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4880602 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (@lem4880601 A s x). Qed.
Lemma lem4880603 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term328 A x f c) = (term329 A f c x).
Proof. exact (@lem4880602 A (f c) x). Qed.
Lemma lem4880611 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880612 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4880611 (A -> Prop) P x). Qed.
Lemma lem4880613 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term316 A t f c) = (f c t).
Proof. exact (@lem4880612 A (f c) t). Qed.
Lemma lem4880614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880615 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term330 A t f c) = (term331 A f c t).
Proof. exact (MK_COMB (@lem4880614) (@lem4880613 A f c t)). Qed.
Lemma lem4880617 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880618 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4880617 A P x). Qed.
Lemma lem4880619 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4880618 A t x). Qed.
Lemma lem4880620 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term332 A f c x t) = (term333 A f c t x).
Proof. exact (MK_COMB (@lem4880615 A f c t) (@lem4880619 A t x)). Qed.
Lemma lem4880623 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term334 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880620 A f c t x)). Qed.
Lemma lem4880624 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4880625 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term329 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4880624 A) (@lem4880623 A f c x)). Qed.
Lemma lem4880630 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term328 A x f c) = (term336 A f c x).
Proof. exact (TRANS (@lem4880603 A f c x) (@lem4880625 A f c x)). Qed.
Lemma lem4880631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4880632 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term337 A x f c) = (term338 A f c x).
Proof. exact (MK_COMB (@lem4880631) (@lem4880630 A f c x)). Qed.
Lemma lem4880634 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880635 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4880634 A P x). Qed.
Lemma lem4880636 {A : Type'} (c : A -> Prop) (x : A) : (@IN A x c) = (c x).
Proof. exact (@lem4880635 A c x). Qed.
Lemma lem4880637 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term328 A x f c) = (@IN A x c)) = ((term336 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4880632 A f c x) (@lem4880636 A c x)). Qed.
Lemma lem4880640 {A : Type'} (f : type639 A) (c : A -> Prop) : (term339 A f c) = (term340 A f c).
Proof. exact (fun_ext (fun x : A => @lem4880637 A f c x)). Qed.
Lemma lem4880641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4880642 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term341 A f c).
Proof. exact (MK_COMB (@lem4880641 A) (@lem4880640 A f c)). Qed.
Lemma lem4880647 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term342 A P f c).
Proof. exact (MK_COMB (@lem4880593 A f c P) (@lem4880642 A f c)). Qed.
Lemma lem4880650 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4880651 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term304 A P f c) = (term343 A P f c).
Proof. exact (MK_COMB (@lem4880650 A f c) (@lem4880647 A P f c)). Qed.
Lemma lem4880654 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term305 A u P f c) = (term344 A u P f c).
Proof. exact (MK_COMB (@lem4880564 A u c) (@lem4880651 A P f c)). Qed.
Lemma lem4880657 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term345 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4880654 A u P f c)). Qed.
Lemma lem4880658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880659 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term307 A u P f) = (term346 A u P f).
Proof. exact (MK_COMB (@lem4880658 A) (@lem4880657 A u P f)). Qed.
Lemma lem4880664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880665 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term309 A u P f) = (term347 A u P f).
Proof. exact (MK_COMB (@lem4880664) (@lem4880659 A u P f)). Qed.
Lemma lem4880666 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4880667 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term310 A P f u) = (term348 A P f u).
Proof. exact (MK_COMB (@lem4880665 A u P f) (@lem4880666 A u)). Qed.
Lemma lem4880670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880671 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term312 A P f u) = (term349 A P f u).
Proof. exact (MK_COMB (@lem4880670) (@lem4880667 A P f u)). Qed.
Lemma lem4880685 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880686 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4880685 (A -> Prop) P x). Qed.
Lemma lem4880687 {A : Type'} (u : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s u) = (u s).
Proof. exact (@lem4880686 A u s). Qed.
Lemma lem4880688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880689 {A : Type'} (u : type686 A) (s : A -> Prop) : (term350 A s u) = (term351 A u s).
Proof. exact (MK_COMB (@lem4880688) (@lem4880687 A u s)). Qed.
Lemma lem4880691 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4880692 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4880691 (A -> Prop) P x). Qed.
Lemma lem4880693 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term316 A t f s) = (f s t).
Proof. exact (@lem4880692 A (f s) t). Qed.
Lemma lem4880694 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term244 A u t f s) = (term352 A u f s t).
Proof. exact (MK_COMB (@lem4880689 A u s) (@lem4880693 A f s t)). Qed.
Lemma lem4880697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880698 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term273 A u t f s) = (term353 A u f s t).
Proof. exact (MK_COMB (@lem4880697) (@lem4880694 A u f s t)). Qed.
Lemma lem4880699 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem4880700 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term287 A u f s P t) = (term354 A u f s P t).
Proof. exact (MK_COMB (@lem4880698 A u f s t) (@lem4880699 A P t)). Qed.
Lemma lem4880703 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term288 A u f s P) = (term355 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880700 A u f s P t)). Qed.
Lemma lem4880704 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880705 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term289 A u f s P) = (term356 A u f s P).
Proof. exact (MK_COMB (@lem4880704 A) (@lem4880703 A u f s P)). Qed.
Lemma lem4880710 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term290 A u f P) = (term357 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880705 A u f s P)). Qed.
Lemma lem4880711 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880712 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term291 A u f P) = (term358 A u f P).
Proof. exact (MK_COMB (@lem4880711 A) (@lem4880710 A u f P)). Qed.
Lemma lem4880717 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term314 A u f P) = (term359 A u f P).
Proof. exact (MK_COMB (@lem4880671 A P f u) (@lem4880712 A u f P)). Qed.
Lemma lem4880720 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term359 A u f P) = (term314 A u f P).
Proof. exact (SYM (@lem4880717 A u f P)). Qed.
Lemma lem4880722 (p : Prop) : p = (term360 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4880723 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term359 A u f P) = (term361 A u f P).
Proof. exact (@lem4880722 (term359 A u f P)). Qed.
Lemma lem4880724 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term361 A u f P) = (term359 A u f P).
Proof. exact (SYM (@lem4880723 A u f P)). Qed.
Lemma lem4880725 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term362 A u f P) : term362 A u f P.
Proof. exact (h1). Qed.
Lemma lem4880728 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term361 A u f P) : term361 A u f P.
Proof. exact (h1). Qed.
Lemma lem4880729 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term363 A u f P.
Proof. exact (fun h0 : term361 A u f P => @lem4880728 A u f P h0). Qed.
Lemma lem4880730 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term363 A u f P) : term363 A u f P.
Proof. exact (h1). Qed.
Lemma lem4880731 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term361 A u f P) : term361 A u f P.
Proof. exact (h1). Qed.
Lemma lem4880732 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term361 A u f P) (h2 : term363 A u f P) : term361 A u f P.
Proof. exact (@lem4880730 A u f P h2 (@lem4880731 A u f P h1)). Qed.
Lemma lem4880733 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term361 A u f P) : term364 A u f P.
Proof. exact (fun h0 : term363 A u f P => @lem4880732 A u f P h1 h0). Qed.
Lemma lem4880734 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term363 A u f P) : term363 A u f P.
Proof. exact (h1). Qed.
Lemma lem4880735 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term361 A u f P) (h2 : term363 A u f P) : term361 A u f P.
Proof. exact (@lem4880733 A u f P h1 (@lem4880734 A u f P h2)). Qed.
Lemma lem4880736 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term363 A u f P) : term363 A u f P.
Proof. exact (fun h0 : term361 A u f P => @lem4880735 A u f P h0 h1). Qed.
Lemma lem4880737 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term365 A u f P.
Proof. exact (fun h0 : term363 A u f P => @lem4880736 A u f P h0). Qed.
Lemma lem4880740 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term363 A u f P.
Proof. exact (@lem4880737 A u f P (@lem4880729 A u f P)). Qed.
Lemma lem4880741 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term363 A u f P.
Proof. exact (@lem4880740 A u f P). Qed.
Lemma lem4880755 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4880756 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term361 A u f P) = (term366 A u f P).
Proof. exact (@lem4880755 (term362 A u f P)). Qed.
Lemma lem4880758 (t : Prop) : (term367 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4880759 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term366 A u f P) = (term359 A u f P).
Proof. exact (@lem4880758 (term359 A u f P)). Qed.
Lemma lem4880762 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term361 A u f P) = (term359 A u f P).
Proof. exact (TRANS (@lem4880756 A u f P) (@lem4880759 A u f P)). Qed.
Lemma lem4880847 {A : Type'} (f : type639 A) (P : type686 A) : (term368 A f P) = (term369 A f P).
Proof. exact (fun_ext (fun u : type686 A => @lem4880762 A u f P)). Qed.
Lemma lem4880848 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4880849 {A : Type'} (f : type639 A) (P : type686 A) : (term370 A f P) = (term371 A f P).
Proof. exact (MK_COMB (@lem4880848 A) (@lem4880847 A f P)). Qed.
Lemma lem4880854 {A : Type'} (P : type686 A) : (term372 A P) = (term373 A P).
Proof. exact (fun_ext (fun f : type639 A => @lem4880849 A f P)). Qed.
Lemma lem4880855 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4880856 {A : Type'} (P : type686 A) : (term374 A P) = (term375 A P).
Proof. exact (MK_COMB (@lem4880855 A) (@lem4880854 A P)). Qed.
Lemma lem4880861 {A : Type'} : (term376 A) = (term377 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4880856 A P)). Qed.
Lemma lem4880862 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4880871 {A : Type'} : (term378 A) = (term379 A).
Proof. exact (MK_COMB (@lem4880862 A) (@lem4880861 A)). Qed.
Lemma lem4880880 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term354 A u f s P t) = (term354 A u f s P t).
Proof. exact (eq_refl (term354 A u f s P t)). Qed.
Lemma lem4880881 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term355 A u f s P) = (term355 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880880 A u f s P t)). Qed.
Lemma lem4880882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880883 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term356 A u f s P) = (term356 A u f s P).
Proof. exact (MK_COMB (@lem4880882 A) (@lem4880881 A u f s P)). Qed.
Lemma lem4880884 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term357 A u f P) = (term357 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4880883 A u f s P)). Qed.
Lemma lem4880885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880886 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term358 A u f P) = (term358 A u f P).
Proof. exact (MK_COMB (@lem4880885 A) (@lem4880884 A u f P)). Qed.
Lemma lem4880887 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4880888 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4880893 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term333 A f c t x) = (term333 A f c t x).
Proof. exact (eq_refl (term333 A f c t x)). Qed.
Lemma lem4880894 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term335 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4880893 A f c t x)). Qed.
Lemma lem4880895 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4880896 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term336 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4880895 A) (@lem4880894 A f c x)). Qed.
Lemma lem4880897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4880898 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term338 A f c x) = (term338 A f c x).
Proof. exact (MK_COMB (@lem4880897) (@lem4880896 A f c x)). Qed.
Lemma lem4880899 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = ((term336 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4880898 A f c x) (@lem4880888 A c x)). Qed.
Lemma lem4880900 {A : Type'} (f : type639 A) (c : A -> Prop) : (term340 A f c) = (term340 A f c).
Proof. exact (fun_ext (fun x : A => @lem4880899 A f c x)). Qed.
Lemma lem4880901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4880902 {A : Type'} (f : type639 A) (c : A -> Prop) : (term341 A f c) = (term341 A f c).
Proof. exact (MK_COMB (@lem4880901 A) (@lem4880900 A f c)). Qed.
Lemma lem4880907 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term320 A f c P c') = (term320 A f c P c').
Proof. exact (eq_refl (term320 A f c P c')). Qed.
Lemma lem4880908 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term322 A f c P) = (term322 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4880907 A f c P c')). Qed.
Lemma lem4880909 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880910 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term324 A f c P) = (term324 A f c P).
Proof. exact (MK_COMB (@lem4880909 A) (@lem4880908 A f c P)). Qed.
Lemma lem4880911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880912 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term325 A f c P) = (term325 A f c P).
Proof. exact (MK_COMB (@lem4880911) (@lem4880910 A f c P)). Qed.
Lemma lem4880913 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term342 A P f c) = (term342 A P f c).
Proof. exact (MK_COMB (@lem4880912 A f c P) (@lem4880902 A f c)). Qed.
Lemma lem4880916 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4880917 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term343 A P f c) = (term343 A P f c).
Proof. exact (MK_COMB (@lem4880916 A f c) (@lem4880913 A P f c)). Qed.
Lemma lem4880920 {A : Type'} (u : type686 A) (c : A -> Prop) : (term315 A u c) = (term315 A u c).
Proof. exact (eq_refl (term315 A u c)). Qed.
Lemma lem4880921 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term344 A u P f c).
Proof. exact (MK_COMB (@lem4880920 A u c) (@lem4880917 A P f c)). Qed.
Lemma lem4880922 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term345 A u P f) = (term345 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4880921 A u P f c)). Qed.
Lemma lem4880923 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4880924 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term346 A u P f) = (term346 A u P f).
Proof. exact (MK_COMB (@lem4880923 A) (@lem4880922 A u P f)). Qed.
Lemma lem4880925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4880926 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term347 A u P f) = (term347 A u P f).
Proof. exact (MK_COMB (@lem4880925) (@lem4880924 A u P f)). Qed.
Lemma lem4880927 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term348 A P f u).
Proof. exact (MK_COMB (@lem4880926 A u P f) (@lem4880887 A u)). Qed.
Lemma lem4880928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4880929 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term349 A P f u) = (term349 A P f u).
Proof. exact (MK_COMB (@lem4880928) (@lem4880927 A P f u)). Qed.
Lemma lem4880930 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term359 A u f P) = (term359 A u f P).
Proof. exact (MK_COMB (@lem4880929 A P f u) (@lem4880886 A u f P)). Qed.
Lemma lem4880931 {A : Type'} (f : type639 A) (P : type686 A) : (term369 A f P) = (term369 A f P).
Proof. exact (fun_ext (fun u : type686 A => @lem4880930 A u f P)). Qed.
Lemma lem4880932 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4880933 {A : Type'} (f : type639 A) (P : type686 A) : (term371 A f P) = (term371 A f P).
Proof. exact (MK_COMB (@lem4880932 A) (@lem4880931 A f P)). Qed.
Lemma lem4880934 {A : Type'} (P : type686 A) : (term373 A P) = (term373 A P).
Proof. exact (fun_ext (fun f : type639 A => @lem4880933 A f P)). Qed.
Lemma lem4880935 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4880936 {A : Type'} (P : type686 A) : (term375 A P) = (term375 A P).
Proof. exact (MK_COMB (@lem4880935 A) (@lem4880934 A P)). Qed.
Lemma lem4880937 {A : Type'} : (term377 A) = (term377 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4880936 A P)). Qed.
Lemma lem4880938 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4880939 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (MK_COMB (@lem4880938 A) (@lem4880937 A)). Qed.
Lemma lem4881014 {A : Type'} : (term378 A) = (term379 A).
Proof. exact (TRANS (@lem4880871 A) (@lem4880939 A)). Qed.
Lemma lem4881015 {A : Type'} : (term379 A) = (term378 A).
Proof. exact (SYM (@lem4881014 A)). Qed.
Lemma lem4881016 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term348 A P f u.
Proof. exact (h1). Qed.
Lemma lem4881019 (p : Prop) : p = (term360 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4881020 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (term380 A P t).
Proof. exact (@lem4881019 (P t)). Qed.
Lemma lem4881021 {A : Type'} (P : type686 A) (t : A -> Prop) : (term380 A P t) = (P t).
Proof. exact (SYM (@lem4881020 A P t)). Qed.
Lemma lem4881022 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term381 A P t) : term381 A P t.
Proof. exact (h1). Qed.
Lemma lem4881031 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term320 A f c P c') = (term382 A f c P c').
Proof. exact (@lem17265 (f c c') (P c')). Qed.
Lemma lem4881032 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term322 A f c P) = (term383 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4881031 A f c P c')). Qed.
Lemma lem4881033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881034 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term324 A f c P) = (term384 A f c P).
Proof. exact (MK_COMB (@lem4881033 A) (@lem4881032 A f c P)). Qed.
Lemma lem4881043 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term385 A f c t x) = (term386 A f c t x).
Proof. exact (@lem17045 (f c t) (t x)). Qed.
Lemma lem4881046 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term333 A f c t x) = (term333 A f c t x).
Proof. exact (eq_refl (term333 A f c t x)). Qed.
Lemma lem4881047 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4881048 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term389 A f c x) = (term390 A f c x).
Proof. exact (@lem4881047 A (term335 A f c x)). Qed.
Lemma lem4881049 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4881050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881051 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term392 A f c x t) = (term385 A f c t x).
Proof. exact (MK_COMB (@lem4881050) (@lem4881049 A f c t x)). Qed.
Lemma lem4881052 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term392 A f c x t) = (term386 A f c t x).
Proof. exact (TRANS (@lem4881051 A f c t x) (@lem4881043 A f c t x)). Qed.
Lemma lem4881053 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term393 A f c x) = (term394 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881052 A f c t x)). Qed.
Lemma lem4881054 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881055 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term390 A f c x) = (term395 A f c x).
Proof. exact (MK_COMB (@lem4881054 A) (@lem4881053 A f c x)). Qed.
Lemma lem4881056 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term389 A f c x) = (term395 A f c x).
Proof. exact (TRANS (@lem4881048 A f c x) (@lem4881055 A f c x)). Qed.
Lemma lem4881057 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term335 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881046 A f c t x)). Qed.
Lemma lem4881058 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4881059 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term336 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4881058 A) (@lem4881057 A f c x)). Qed.
Lemma lem4881060 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4881061 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4881062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881063 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term397 A f c x) = (term398 A f c x).
Proof. exact (MK_COMB (@lem4881062) (@lem4881056 A f c x)). Qed.
Lemma lem4881064 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term399 A f c x) = (term400 A f c x).
Proof. exact (MK_COMB (@lem4881063 A f c x) (@lem4881061 A c x)). Qed.
Lemma lem4881065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881066 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term401 A f c x) = (term401 A f c x).
Proof. exact (MK_COMB (@lem4881065) (@lem4881059 A f c x)). Qed.
Lemma lem4881067 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term402 A f c x) = (term402 A f c x).
Proof. exact (MK_COMB (@lem4881066 A f c x) (@lem4881060 A c x)). Qed.
Lemma lem4881068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881069 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term403 A f c x) = (term403 A f c x).
Proof. exact (MK_COMB (@lem4881068) (@lem4881067 A f c x)). Qed.
Lemma lem4881070 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term404 A f c x) = (term405 A f c x).
Proof. exact (MK_COMB (@lem4881069 A f c x) (@lem4881064 A f c x)). Qed.
Lemma lem4881071 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = (term404 A f c x).
Proof. exact (@lem17784 (term336 A f c x) (c x)). Qed.
Lemma lem4881072 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = (term405 A f c x).
Proof. exact (TRANS (@lem4881071 A f c x) (@lem4881070 A f c x)). Qed.
Lemma lem4881073 {A : Type'} (f : type639 A) (c : A -> Prop) : (term340 A f c) = (term406 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881072 A f c x)). Qed.
Lemma lem4881074 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881075 {A : Type'} (f : type639 A) (c : A -> Prop) : (term341 A f c) = (term407 A f c).
Proof. exact (MK_COMB (@lem4881074 A) (@lem4881073 A f c)). Qed.
Lemma lem4881076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881077 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term325 A f c P) = (term408 A f c P).
Proof. exact (MK_COMB (@lem4881076) (@lem4881034 A f c P)). Qed.
Lemma lem4881078 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term342 A P f c) = (term409 A P f c).
Proof. exact (MK_COMB (@lem4881077 A f c P) (@lem4881075 A f c)). Qed.
Lemma lem4881080 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4881081 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term343 A P f c) = (term410 A P f c).
Proof. exact (MK_COMB (@lem4881080 A f c) (@lem4881078 A P f c)). Qed.
Lemma lem4881083 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4881084 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term412 A u P f c) = (term413 A u P f c).
Proof. exact (MK_COMB (@lem4881083 A u c) (@lem4881081 A P f c)). Qed.
Lemma lem4881085 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term412 A u P f c).
Proof. exact (@lem17265 (u c) (term343 A P f c)). Qed.
Lemma lem4881086 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term413 A u P f c).
Proof. exact (TRANS (@lem4881085 A u P f c) (@lem4881084 A u P f c)). Qed.
Lemma lem4881087 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term345 A u P f) = (term414 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881086 A u P f c)). Qed.
Lemma lem4881088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881089 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term346 A u P f) = (term415 A u P f).
Proof. exact (MK_COMB (@lem4881088 A) (@lem4881087 A u P f)). Qed.
Lemma lem4881090 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881092 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term347 A u P f) = (term416 A u P f).
Proof. exact (MK_COMB (@lem4881091) (@lem4881089 A u P f)). Qed.
Lemma lem4881093 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term417 A P f u).
Proof. exact (MK_COMB (@lem4881092 A u P f) (@lem4881090 A u)). Qed.
Lemma lem4881175 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term418 A P Q) = (term419 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4881176 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term418 A P Q) = (term419 A P Q).
Proof. exact (@lem4881175 A P Q). Qed.
Lemma lem4881177 {A : Type'} (f : type639 A) (c : A -> Prop) : (term420 A f c) = (term421 A f c).
Proof. exact (@lem4881176 A (term422 A f c) (term423 A f c)). Qed.
Lemma lem4881178 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term424 A f c x) = (term402 A f c x).
Proof. exact (eq_refl (term424 A f c x)). Qed.
Lemma lem4881179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881180 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term425 A f c x) = (term403 A f c x).
Proof. exact (MK_COMB (@lem4881179) (@lem4881178 A f c x)). Qed.
Lemma lem4881181 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term426 A f c x) = (term400 A f c x).
Proof. exact (eq_refl (term426 A f c x)). Qed.
Lemma lem4881182 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term427 A f c x) = (term405 A f c x).
Proof. exact (MK_COMB (@lem4881180 A f c x) (@lem4881181 A f c x)). Qed.
Lemma lem4881183 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term406 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881182 A f c x)). Qed.
Lemma lem4881184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881185 {A : Type'} (f : type639 A) (c : A -> Prop) : (term420 A f c) = (term407 A f c).
Proof. exact (MK_COMB (@lem4881184 A) (@lem4881183 A f c)). Qed.
Lemma lem4881186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881187 {A : Type'} (f : type639 A) (c : A -> Prop) : (term429 A f c) = (term430 A f c).
Proof. exact (MK_COMB (@lem4881186) (@lem4881185 A f c)). Qed.
Lemma lem4881188 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term424 A f c x) = (term402 A f c x).
Proof. exact (eq_refl (term424 A f c x)). Qed.
Lemma lem4881189 {A : Type'} (f : type639 A) (c : A -> Prop) : (term431 A f c) = (term422 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881188 A f c x)). Qed.
Lemma lem4881190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881191 {A : Type'} (f : type639 A) (c : A -> Prop) : (term432 A f c) = (term433 A f c).
Proof. exact (MK_COMB (@lem4881190 A) (@lem4881189 A f c)). Qed.
Lemma lem4881192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881193 {A : Type'} (f : type639 A) (c : A -> Prop) : (term434 A f c) = (term435 A f c).
Proof. exact (MK_COMB (@lem4881192) (@lem4881191 A f c)). Qed.
Lemma lem4881194 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term426 A f c x) = (term400 A f c x).
Proof. exact (eq_refl (term426 A f c x)). Qed.
Lemma lem4881195 {A : Type'} (f : type639 A) (c : A -> Prop) : (term436 A f c) = (term423 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881194 A f c x)). Qed.
Lemma lem4881196 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881197 {A : Type'} (f : type639 A) (c : A -> Prop) : (term437 A f c) = (term438 A f c).
Proof. exact (MK_COMB (@lem4881196 A) (@lem4881195 A f c)). Qed.
Lemma lem4881198 {A : Type'} (f : type639 A) (c : A -> Prop) : (term421 A f c) = (term439 A f c).
Proof. exact (MK_COMB (@lem4881193 A f c) (@lem4881197 A f c)). Qed.
Lemma lem4881199 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term420 A f c) = (term421 A f c)) = ((term407 A f c) = (term439 A f c)).
Proof. exact (MK_COMB (@lem4881187 A f c) (@lem4881198 A f c)). Qed.
Lemma lem4881200 {A : Type'} (f : type639 A) (c : A -> Prop) : (term407 A f c) = (term439 A f c).
Proof. exact (EQ_MP (@lem4881199 A f c) (@lem4881177 A f c)). Qed.
Lemma lem4881377 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4881378 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term409 A P f c) = (term440 A P f c).
Proof. exact (MK_COMB (@lem4881377 A f c P) (@lem4881200 A f c)). Qed.
Lemma lem4881379 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4881380 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term410 A P f c) = (term441 A P f c).
Proof. exact (MK_COMB (@lem4881379 A f c) (@lem4881378 A P f c)). Qed.
Lemma lem4881381 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4881382 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term413 A u P f c) = (term442 A u P f c).
Proof. exact (MK_COMB (@lem4881381 A u c) (@lem4881380 A P f c)). Qed.
Lemma lem4881383 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term414 A u P f) = (term443 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881382 A u P f c)). Qed.
Lemma lem4881384 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881385 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term415 A u P f) = (term444 A u P f).
Proof. exact (MK_COMB (@lem4881384 A) (@lem4881383 A u P f)). Qed.
Lemma lem4881434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881435 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term416 A u P f) = (term445 A u P f).
Proof. exact (MK_COMB (@lem4881434) (@lem4881385 A u P f)). Qed.
Lemma lem4881436 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881437 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term417 A P f u) = (term446 A P f u).
Proof. exact (MK_COMB (@lem4881435 A u P f) (@lem4881436 A u)). Qed.
Lemma lem4881439 {A : Type'} (P : A -> Prop) (Q : Prop) : (term447 A P Q) = (term448 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4881440 {A : Type'} (P : type686 A) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (@lem4881439 (A -> Prop) P Q). Qed.
Lemma lem4881441 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term451 A f c x) = (term452 A f c x).
Proof. exact (@lem4881440 A (term335 A f c x) (term396 A c x)). Qed.
Lemma lem4881442 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4881443 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term453 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881442 A f c t x)). Qed.
Lemma lem4881444 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4881445 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term454 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4881444 A) (@lem4881443 A f c x)). Qed.
Lemma lem4881446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881447 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term455 A f c x) = (term401 A f c x).
Proof. exact (MK_COMB (@lem4881446) (@lem4881445 A f c x)). Qed.
Lemma lem4881448 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4881449 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term451 A f c x) = (term402 A f c x).
Proof. exact (MK_COMB (@lem4881447 A f c x) (@lem4881448 A c x)). Qed.
Lemma lem4881450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881451 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term456 A f c x) = (term457 A f c x).
Proof. exact (MK_COMB (@lem4881450) (@lem4881449 A f c x)). Qed.
Lemma lem4881452 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4881453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881454 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term458 A f c x t) = (term459 A f c t x).
Proof. exact (MK_COMB (@lem4881453) (@lem4881452 A f c t x)). Qed.
Lemma lem4881455 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4881456 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term460 A f t c x) = (term461 A f t c x).
Proof. exact (MK_COMB (@lem4881454 A f c t x) (@lem4881455 A c x)). Qed.
Lemma lem4881457 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term462 A f c x) = (term463 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881456 A f t c x)). Qed.
Lemma lem4881458 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4881459 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term452 A f c x) = (term464 A f c x).
Proof. exact (MK_COMB (@lem4881458 A) (@lem4881457 A f c x)). Qed.
Lemma lem4881460 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term451 A f c x) = (term452 A f c x)) = ((term402 A f c x) = (term464 A f c x)).
Proof. exact (MK_COMB (@lem4881451 A f c x) (@lem4881459 A f c x)). Qed.
Lemma lem4881461 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term402 A f c x) = (term464 A f c x).
Proof. exact (EQ_MP (@lem4881460 A f c x) (@lem4881441 A f c x)). Qed.
Lemma lem4881462 {A : Type'} (f : type639 A) (c : A -> Prop) : (term422 A f c) = (term465 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881461 A f c x)). Qed.
Lemma lem4881463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881464 {A : Type'} (f : type639 A) (c : A -> Prop) : (term433 A f c) = (term466 A f c).
Proof. exact (MK_COMB (@lem4881463 A) (@lem4881462 A f c)). Qed.
Lemma lem4881466 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4881467 {A : Type'} (P : type1364 A) : (term467 A P) = (term468 A P).
Proof. exact (@lem4881466 A (A -> Prop) P). Qed.
Lemma lem4881468 {A : Type'} (f : type639 A) (c : A -> Prop) : (term469 A f c) = (term470 A f c).
Proof. exact (@lem4881467 A (term471 A f c)). Qed.
Lemma lem4881469 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term472 A f c x) = (term463 A f c x).
Proof. exact (eq_refl (term472 A f c x)). Qed.
Lemma lem4881470 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4881471 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) (t : A -> Prop) : (term473 A f c x t) = (term474 A f c x t).
Proof. exact (MK_COMB (@lem4881469 A f c x) (@lem4881470 A t)). Qed.
Lemma lem4881472 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term474 A f c x t) = (term461 A f t c x).
Proof. exact (eq_refl (term474 A f c x t)). Qed.
Lemma lem4881473 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term473 A f c x t) = (term461 A f t c x).
Proof. exact (TRANS (@lem4881471 A f c x t) (@lem4881472 A f t c x)). Qed.
Lemma lem4881474 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term475 A f c x) = (term463 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881473 A f t c x)). Qed.
Lemma lem4881475 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4881476 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term476 A f c x) = (term464 A f c x).
Proof. exact (MK_COMB (@lem4881475 A) (@lem4881474 A f c x)). Qed.
Lemma lem4881477 {A : Type'} (f : type639 A) (c : A -> Prop) : (term477 A f c) = (term465 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881476 A f c x)). Qed.
Lemma lem4881478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881479 {A : Type'} (f : type639 A) (c : A -> Prop) : (term469 A f c) = (term466 A f c).
Proof. exact (MK_COMB (@lem4881478 A) (@lem4881477 A f c)). Qed.
Lemma lem4881480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881481 {A : Type'} (f : type639 A) (c : A -> Prop) : (term478 A f c) = (term479 A f c).
Proof. exact (MK_COMB (@lem4881480) (@lem4881479 A f c)). Qed.
Lemma lem4881482 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term472 A f c x) = (term463 A f c x).
Proof. exact (eq_refl (term472 A f c x)). Qed.
Lemma lem4881483 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4881484 {A : Type'} (f : type639 A) (c : A -> Prop) (t : type1402 A) (x : A) : (term480 A f c t x) = (term481 A f c t x).
Proof. exact (MK_COMB (@lem4881482 A f c x) (@lem4881483 A t x)). Qed.
Lemma lem4881485 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term481 A f c t x) = (term482 A f t c x).
Proof. exact (eq_refl (term481 A f c t x)). Qed.
Lemma lem4881486 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term480 A f c t x) = (term482 A f t c x).
Proof. exact (TRANS (@lem4881484 A f c t x) (@lem4881485 A f t c x)). Qed.
Lemma lem4881487 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term483 A f c t) = (term484 A f t c).
Proof. exact (fun_ext (fun x : A => @lem4881486 A f t c x)). Qed.
Lemma lem4881488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881489 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term485 A f c t) = (term486 A f t c).
Proof. exact (MK_COMB (@lem4881488 A) (@lem4881487 A f t c)). Qed.
Lemma lem4881490 {A : Type'} (f : type639 A) (c : A -> Prop) : (term487 A f c) = (term488 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881489 A f t c)). Qed.
Lemma lem4881491 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881492 {A : Type'} (f : type639 A) (c : A -> Prop) : (term470 A f c) = (term489 A f c).
Proof. exact (MK_COMB (@lem4881491 A) (@lem4881490 A f c)). Qed.
Lemma lem4881493 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term469 A f c) = (term470 A f c)) = ((term466 A f c) = (term489 A f c)).
Proof. exact (MK_COMB (@lem4881481 A f c) (@lem4881492 A f c)). Qed.
Lemma lem4881494 {A : Type'} (f : type639 A) (c : A -> Prop) : (term466 A f c) = (term489 A f c).
Proof. exact (EQ_MP (@lem4881493 A f c) (@lem4881468 A f c)). Qed.
Lemma lem4881495 {A : Type'} (f : type639 A) (c : A -> Prop) : (term433 A f c) = (term489 A f c).
Proof. exact (TRANS (@lem4881464 A f c) (@lem4881494 A f c)). Qed.
Lemma lem4881496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881497 {A : Type'} (f : type639 A) (c : A -> Prop) : (term435 A f c) = (term490 A f c).
Proof. exact (MK_COMB (@lem4881496) (@lem4881495 A f c)). Qed.
Lemma lem4881498 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4881499 {A : Type'} (f : type639 A) (c : A -> Prop) : (term439 A f c) = (term491 A f c).
Proof. exact (MK_COMB (@lem4881497 A f c) (@lem4881498 A f c)). Qed.
Lemma lem4881501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4881502 {A : Type'} (P : type421 A) (Q : Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (@lem4881501 (type1402 A) P Q). Qed.
Lemma lem4881503 {A : Type'} (f : type639 A) (c : A -> Prop) : (term496 A f c) = (term497 A f c).
Proof. exact (@lem4881502 A (term488 A f c) (term438 A f c)). Qed.
Lemma lem4881504 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term498 A f c t) = (term486 A f t c).
Proof. exact (eq_refl (term498 A f c t)). Qed.
Lemma lem4881505 {A : Type'} (f : type639 A) (c : A -> Prop) : (term499 A f c) = (term488 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881504 A f t c)). Qed.
Lemma lem4881506 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881507 {A : Type'} (f : type639 A) (c : A -> Prop) : (term500 A f c) = (term489 A f c).
Proof. exact (MK_COMB (@lem4881506 A) (@lem4881505 A f c)). Qed.
Lemma lem4881508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881509 {A : Type'} (f : type639 A) (c : A -> Prop) : (term501 A f c) = (term490 A f c).
Proof. exact (MK_COMB (@lem4881508) (@lem4881507 A f c)). Qed.
Lemma lem4881510 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4881511 {A : Type'} (f : type639 A) (c : A -> Prop) : (term496 A f c) = (term491 A f c).
Proof. exact (MK_COMB (@lem4881509 A f c) (@lem4881510 A f c)). Qed.
Lemma lem4881512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881513 {A : Type'} (f : type639 A) (c : A -> Prop) : (term502 A f c) = (term503 A f c).
Proof. exact (MK_COMB (@lem4881512) (@lem4881511 A f c)). Qed.
Lemma lem4881514 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term498 A f c t) = (term486 A f t c).
Proof. exact (eq_refl (term498 A f c t)). Qed.
Lemma lem4881515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881516 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term504 A f c t) = (term505 A f t c).
Proof. exact (MK_COMB (@lem4881515) (@lem4881514 A f t c)). Qed.
Lemma lem4881517 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4881518 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term506 A t f c) = (term507 A t f c).
Proof. exact (MK_COMB (@lem4881516 A f t c) (@lem4881517 A f c)). Qed.
Lemma lem4881519 {A : Type'} (f : type639 A) (c : A -> Prop) : (term508 A f c) = (term509 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881518 A t f c)). Qed.
Lemma lem4881520 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881521 {A : Type'} (f : type639 A) (c : A -> Prop) : (term497 A f c) = (term510 A f c).
Proof. exact (MK_COMB (@lem4881520 A) (@lem4881519 A f c)). Qed.
Lemma lem4881522 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term496 A f c) = (term497 A f c)) = ((term491 A f c) = (term510 A f c)).
Proof. exact (MK_COMB (@lem4881513 A f c) (@lem4881521 A f c)). Qed.
Lemma lem4881523 {A : Type'} (f : type639 A) (c : A -> Prop) : (term491 A f c) = (term510 A f c).
Proof. exact (EQ_MP (@lem4881522 A f c) (@lem4881503 A f c)). Qed.
Lemma lem4881524 {A : Type'} (f : type639 A) (c : A -> Prop) : (term439 A f c) = (term510 A f c).
Proof. exact (TRANS (@lem4881499 A f c) (@lem4881523 A f c)). Qed.
Lemma lem4881525 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4881526 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term440 A P f c) = (term511 A P f c).
Proof. exact (MK_COMB (@lem4881525 A f c P) (@lem4881524 A f c)). Qed.
Lemma lem4881528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4881529 {A : Type'} (P : Prop) (Q : type421 A) : (term514 A P Q) = (term515 A P Q).
Proof. exact (@lem4881528 (type1402 A) P Q). Qed.
Lemma lem4881530 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term516 A P f c) = (term517 A P f c).
Proof. exact (@lem4881529 A (term384 A f c P) (term509 A f c)). Qed.
Lemma lem4881531 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term518 A f c t) = (term507 A t f c).
Proof. exact (eq_refl (term518 A f c t)). Qed.
Lemma lem4881532 {A : Type'} (f : type639 A) (c : A -> Prop) : (term519 A f c) = (term509 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881531 A t f c)). Qed.
Lemma lem4881533 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881534 {A : Type'} (f : type639 A) (c : A -> Prop) : (term520 A f c) = (term510 A f c).
Proof. exact (MK_COMB (@lem4881533 A) (@lem4881532 A f c)). Qed.
Lemma lem4881535 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4881536 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term516 A P f c) = (term511 A P f c).
Proof. exact (MK_COMB (@lem4881535 A f c P) (@lem4881534 A f c)). Qed.
Lemma lem4881537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881538 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term521 A P f c) = (term522 A P f c).
Proof. exact (MK_COMB (@lem4881537) (@lem4881536 A P f c)). Qed.
Lemma lem4881539 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term518 A f c t) = (term507 A t f c).
Proof. exact (eq_refl (term518 A f c t)). Qed.
Lemma lem4881540 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4881541 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term523 A P f c t) = (term524 A P t f c).
Proof. exact (MK_COMB (@lem4881540 A f c P) (@lem4881539 A t f c)). Qed.
Lemma lem4881542 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A P f c) = (term526 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881541 A P t f c)). Qed.
Lemma lem4881543 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881544 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term517 A P f c) = (term527 A P f c).
Proof. exact (MK_COMB (@lem4881543 A) (@lem4881542 A P f c)). Qed.
Lemma lem4881545 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term516 A P f c) = (term517 A P f c)) = ((term511 A P f c) = (term527 A P f c)).
Proof. exact (MK_COMB (@lem4881538 A P f c) (@lem4881544 A P f c)). Qed.
Lemma lem4881546 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term511 A P f c) = (term527 A P f c).
Proof. exact (EQ_MP (@lem4881545 A P f c) (@lem4881530 A P f c)). Qed.
Lemma lem4881547 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term440 A P f c) = (term527 A P f c).
Proof. exact (TRANS (@lem4881526 A P f c) (@lem4881546 A P f c)). Qed.
Lemma lem4881548 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4881549 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term441 A P f c) = (term528 A P f c).
Proof. exact (MK_COMB (@lem4881548 A f c) (@lem4881547 A P f c)). Qed.
Lemma lem4881551 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4881552 {A : Type'} (P : Prop) (Q : type421 A) : (term514 A P Q) = (term515 A P Q).
Proof. exact (@lem4881551 (type1402 A) P Q). Qed.
Lemma lem4881553 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A P f c) = (term530 A P f c).
Proof. exact (@lem4881552 A (term195 A f c) (term526 A P f c)). Qed.
Lemma lem4881554 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term531 A P f c t) = (term524 A P t f c).
Proof. exact (eq_refl (term531 A P f c t)). Qed.
Lemma lem4881555 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term532 A P f c) = (term526 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881554 A P t f c)). Qed.
Lemma lem4881556 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881557 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term533 A P f c) = (term527 A P f c).
Proof. exact (MK_COMB (@lem4881556 A) (@lem4881555 A P f c)). Qed.
Lemma lem4881558 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4881559 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A P f c) = (term528 A P f c).
Proof. exact (MK_COMB (@lem4881558 A f c) (@lem4881557 A P f c)). Qed.
Lemma lem4881560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881561 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term534 A P f c) = (term535 A P f c).
Proof. exact (MK_COMB (@lem4881560) (@lem4881559 A P f c)). Qed.
Lemma lem4881562 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term531 A P f c t) = (term524 A P t f c).
Proof. exact (eq_refl (term531 A P f c t)). Qed.
Lemma lem4881563 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4881564 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term536 A P f c t) = (term537 A P t f c).
Proof. exact (MK_COMB (@lem4881563 A f c) (@lem4881562 A P t f c)). Qed.
Lemma lem4881565 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term538 A P f c) = (term539 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881564 A P t f c)). Qed.
Lemma lem4881566 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881567 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term530 A P f c) = (term540 A P f c).
Proof. exact (MK_COMB (@lem4881566 A) (@lem4881565 A P f c)). Qed.
Lemma lem4881568 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term529 A P f c) = (term530 A P f c)) = ((term528 A P f c) = (term540 A P f c)).
Proof. exact (MK_COMB (@lem4881561 A P f c) (@lem4881567 A P f c)). Qed.
Lemma lem4881569 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term528 A P f c) = (term540 A P f c).
Proof. exact (EQ_MP (@lem4881568 A P f c) (@lem4881553 A P f c)). Qed.
Lemma lem4881570 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term441 A P f c) = (term540 A P f c).
Proof. exact (TRANS (@lem4881549 A P f c) (@lem4881569 A P f c)). Qed.
Lemma lem4881571 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4881572 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term442 A u P f c) = (term541 A u P f c).
Proof. exact (MK_COMB (@lem4881571 A u c) (@lem4881570 A P f c)). Qed.
Lemma lem4881574 {A : Type'} (P : Prop) (Q : A -> Prop) : (term542 A P Q) = (term543 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4881575 {A : Type'} (P : Prop) (Q : type421 A) : (term544 A P Q) = (term545 A P Q).
Proof. exact (@lem4881574 (type1402 A) P Q). Qed.
Lemma lem4881576 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term546 A u P f c) = (term547 A u P f c).
Proof. exact (@lem4881575 A (term381 A u c) (term539 A P f c)). Qed.
Lemma lem4881577 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term548 A P f c t) = (term537 A P t f c).
Proof. exact (eq_refl (term548 A P f c t)). Qed.
Lemma lem4881578 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term549 A P f c) = (term539 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881577 A P t f c)). Qed.
Lemma lem4881579 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881580 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term550 A P f c) = (term540 A P f c).
Proof. exact (MK_COMB (@lem4881579 A) (@lem4881578 A P f c)). Qed.
Lemma lem4881581 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4881582 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term546 A u P f c) = (term541 A u P f c).
Proof. exact (MK_COMB (@lem4881581 A u c) (@lem4881580 A P f c)). Qed.
Lemma lem4881583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881584 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term551 A u P f c) = (term552 A u P f c).
Proof. exact (MK_COMB (@lem4881583) (@lem4881582 A u P f c)). Qed.
Lemma lem4881585 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term548 A P f c t) = (term537 A P t f c).
Proof. exact (eq_refl (term548 A P f c t)). Qed.
Lemma lem4881586 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4881587 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term553 A u P f c t) = (term554 A u P t f c).
Proof. exact (MK_COMB (@lem4881586 A u c) (@lem4881585 A P t f c)). Qed.
Lemma lem4881588 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term555 A u P f c) = (term556 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881587 A u P t f c)). Qed.
Lemma lem4881589 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881590 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term547 A u P f c) = (term557 A u P f c).
Proof. exact (MK_COMB (@lem4881589 A) (@lem4881588 A u P f c)). Qed.
Lemma lem4881591 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term546 A u P f c) = (term547 A u P f c)) = ((term541 A u P f c) = (term557 A u P f c)).
Proof. exact (MK_COMB (@lem4881584 A u P f c) (@lem4881590 A u P f c)). Qed.
Lemma lem4881592 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term541 A u P f c) = (term557 A u P f c).
Proof. exact (EQ_MP (@lem4881591 A u P f c) (@lem4881576 A u P f c)). Qed.
Lemma lem4881593 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term442 A u P f c) = (term557 A u P f c).
Proof. exact (TRANS (@lem4881572 A u P f c) (@lem4881592 A u P f c)). Qed.
Lemma lem4881594 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term443 A u P f) = (term558 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881593 A u P f c)). Qed.
Lemma lem4881595 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881596 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term444 A u P f) = (term559 A u P f).
Proof. exact (MK_COMB (@lem4881595 A) (@lem4881594 A u P f)). Qed.
Lemma lem4881598 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4881599 {A : Type'} (P : type611 A) : (term560 A P) = (term561 A P).
Proof. exact (@lem4881598 (A -> Prop) (type1402 A) P). Qed.
Lemma lem4881600 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term562 A u P f) = (term563 A u P f).
Proof. exact (@lem4881599 A (term564 A u P f)). Qed.
Lemma lem4881601 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term565 A u P f c) = (term556 A u P f c).
Proof. exact (eq_refl (term565 A u P f c)). Qed.
Lemma lem4881602 {A : Type'} (t : type1402 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4881603 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) (t : type1402 A) : (term566 A u P f c t) = (term567 A u P f c t).
Proof. exact (MK_COMB (@lem4881601 A u P f c) (@lem4881602 A t)). Qed.
Lemma lem4881604 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term567 A u P f c t) = (term554 A u P t f c).
Proof. exact (eq_refl (term567 A u P f c t)). Qed.
Lemma lem4881605 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term566 A u P f c t) = (term554 A u P t f c).
Proof. exact (TRANS (@lem4881603 A u P f c t) (@lem4881604 A u P t f c)). Qed.
Lemma lem4881606 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term568 A u P f c) = (term556 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4881605 A u P t f c)). Qed.
Lemma lem4881607 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4881608 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term569 A u P f c) = (term557 A u P f c).
Proof. exact (MK_COMB (@lem4881607 A) (@lem4881606 A u P f c)). Qed.
Lemma lem4881609 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term570 A u P f) = (term558 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881608 A u P f c)). Qed.
Lemma lem4881610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881611 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term562 A u P f) = (term559 A u P f).
Proof. exact (MK_COMB (@lem4881610 A) (@lem4881609 A u P f)). Qed.
Lemma lem4881612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881613 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term571 A u P f) = (term572 A u P f).
Proof. exact (MK_COMB (@lem4881612) (@lem4881611 A u P f)). Qed.
Lemma lem4881614 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term565 A u P f c) = (term556 A u P f c).
Proof. exact (eq_refl (term565 A u P f c)). Qed.
Lemma lem4881615 {A : Type'} (t : type667 A) (c : A -> Prop) : (t c) = (t c).
Proof. exact (eq_refl (t c)). Qed.
Lemma lem4881616 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (t : type667 A) (c : A -> Prop) : (term573 A u P f t c) = (term574 A u P f t c).
Proof. exact (MK_COMB (@lem4881614 A u P f c) (@lem4881615 A t c)). Qed.
Lemma lem4881617 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term574 A u P f t c) = (term575 A u P t f c).
Proof. exact (eq_refl (term574 A u P f t c)). Qed.
Lemma lem4881618 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term573 A u P f t c) = (term575 A u P t f c).
Proof. exact (TRANS (@lem4881616 A u P f t c) (@lem4881617 A u P t f c)). Qed.
Lemma lem4881619 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term576 A u P f t) = (term577 A u P t f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881618 A u P t f c)). Qed.
Lemma lem4881620 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881621 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term578 A u P f t) = (term579 A u P t f).
Proof. exact (MK_COMB (@lem4881620 A) (@lem4881619 A u P t f)). Qed.
Lemma lem4881622 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term580 A u P f) = (term581 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4881621 A u P t f)). Qed.
Lemma lem4881623 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4881624 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term563 A u P f) = (term582 A u P f).
Proof. exact (MK_COMB (@lem4881623 A) (@lem4881622 A u P f)). Qed.
Lemma lem4881625 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : ((term562 A u P f) = (term563 A u P f)) = ((term559 A u P f) = (term582 A u P f)).
Proof. exact (MK_COMB (@lem4881613 A u P f) (@lem4881624 A u P f)). Qed.
Lemma lem4881626 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term559 A u P f) = (term582 A u P f).
Proof. exact (EQ_MP (@lem4881625 A u P f) (@lem4881600 A u P f)). Qed.
Lemma lem4881627 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term444 A u P f) = (term582 A u P f).
Proof. exact (TRANS (@lem4881596 A u P f) (@lem4881626 A u P f)). Qed.
Lemma lem4881628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881629 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term445 A u P f) = (term583 A u P f).
Proof. exact (MK_COMB (@lem4881628) (@lem4881627 A u P f)). Qed.
Lemma lem4881630 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881631 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term446 A P f u) = (term584 A P f u).
Proof. exact (MK_COMB (@lem4881629 A u P f) (@lem4881630 A u)). Qed.
Lemma lem4881633 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4881634 {A : Type'} (P : type149 A) (Q : Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (@lem4881633 (type667 A) P Q). Qed.
Lemma lem4881635 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term587 A P f u) = (term588 A P f u).
Proof. exact (@lem4881634 A (term581 A u P f) (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881636 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term589 A u P f t) = (term579 A u P t f).
Proof. exact (eq_refl (term589 A u P f t)). Qed.
Lemma lem4881637 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term590 A u P f) = (term581 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4881636 A u P t f)). Qed.
Lemma lem4881638 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4881639 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term591 A u P f) = (term582 A u P f).
Proof. exact (MK_COMB (@lem4881638 A) (@lem4881637 A u P f)). Qed.
Lemma lem4881640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881641 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term592 A u P f) = (term583 A u P f).
Proof. exact (MK_COMB (@lem4881640) (@lem4881639 A u P f)). Qed.
Lemma lem4881642 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881643 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term587 A P f u) = (term584 A P f u).
Proof. exact (MK_COMB (@lem4881641 A u P f) (@lem4881642 A u)). Qed.
Lemma lem4881644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881645 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term593 A P f u) = (term594 A P f u).
Proof. exact (MK_COMB (@lem4881644) (@lem4881643 A P f u)). Qed.
Lemma lem4881646 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term589 A u P f t) = (term579 A u P t f).
Proof. exact (eq_refl (term589 A u P f t)). Qed.
Lemma lem4881647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881648 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term595 A u P f t) = (term596 A u P t f).
Proof. exact (MK_COMB (@lem4881647) (@lem4881646 A u P t f)). Qed.
Lemma lem4881649 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4881650 {A : Type'} (P : type686 A) (t : type667 A) (f : type639 A) (u : type686 A) : (term597 A P f t u) = (term598 A P t f u).
Proof. exact (MK_COMB (@lem4881648 A u P t f) (@lem4881649 A u)). Qed.
Lemma lem4881651 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term599 A P f u) = (term600 A P f u).
Proof. exact (fun_ext (fun t : type667 A => @lem4881650 A P t f u)). Qed.
Lemma lem4881652 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4881653 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term588 A P f u) = (term601 A P f u).
Proof. exact (MK_COMB (@lem4881652 A) (@lem4881651 A P f u)). Qed.
Lemma lem4881654 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : ((term587 A P f u) = (term588 A P f u)) = ((term584 A P f u) = (term601 A P f u)).
Proof. exact (MK_COMB (@lem4881645 A P f u) (@lem4881653 A P f u)). Qed.
Lemma lem4881655 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term584 A P f u) = (term601 A P f u).
Proof. exact (EQ_MP (@lem4881654 A P f u) (@lem4881635 A P f u)). Qed.
Lemma lem4881656 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term446 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4881631 A P f u) (@lem4881655 A P f u)). Qed.
Lemma lem4881657 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term417 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4881437 A P f u) (@lem4881656 A P f u)). Qed.
Lemma lem4881658 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4881093 A P f u) (@lem4881657 A P f u)). Qed.
Lemma lem4881659 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term601 A P f u.
Proof. exact (EQ_MP (@lem4881658 A P f u) (@lem4881016 A P f u h1)). Qed.
Lemma lem4881669 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term352 A u f s t.
Proof. exact (h1). Qed.
Lemma lem4881675 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term381 A P t) : term381 A P t.
Proof. exact (h1). Qed.
Lemma lem4881676 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term598 A P t' f u.
Proof. exact (h1). Qed.
Lemma lem4881683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881684 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4881683 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4881685 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4881684 A f s). Qed.
Lemma lem4881686 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4881687 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4881685 A f s) (@lem4881686 A t)). Qed.
Lemma lem4881689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881690 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881689 (A -> Prop) Prop f x). Qed.
Lemma lem4881691 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term602 A f s t).
Proof. exact (@lem4881690 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4881693 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term602 A f s t).
Proof. exact (TRANS (@lem4881687 A f s t) (@lem4881691 A f s t)). Qed.
Lemma lem4881698 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881699 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881698 (A -> Prop) Prop f x). Qed.
Lemma lem4881701 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4881699 A u s). Qed.
Lemma lem4881702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881703 {A : Type'} (u : type686 A) (s : A -> Prop) : (term351 A u s) = (term603 A u s).
Proof. exact (MK_COMB (@lem4881702) (@lem4881701 A u s)). Qed.
Lemma lem4881704 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term352 A u f s t) = (term604 A u f s t).
Proof. exact (MK_COMB (@lem4881703 A u s) (@lem4881693 A f s t)). Qed.
Lemma lem4881705 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term604 A u f s t.
Proof. exact (EQ_MP (@lem4881704 A u f s t) (@lem4881669 A u f s t h1)). Qed.
Lemma lem4881706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881711 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881712 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881711 (A -> Prop) Prop f x). Qed.
Lemma lem4881714 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4881712 A P t). Qed.
Lemma lem4881715 {A : Type'} (P : type686 A) (t : A -> Prop) : (term381 A P t) = (term605 A P t).
Proof. exact (MK_COMB (@lem4881706) (@lem4881714 A P t)). Qed.
Lemma lem4881721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881722 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4881721 (type686 A) Prop f x). Qed.
Lemma lem4881724 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) u).
Proof. exact (@lem4881722 A (@FINITE (A -> Prop)) u). Qed.
Lemma lem4881729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881730 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4881729 A Prop f x). Qed.
Lemma lem4881732 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4881730 A c x). Qed.
Lemma lem4881733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881739 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4881738 A Prop f x). Qed.
Lemma lem4881741 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4881739 A t x). Qed.
Lemma lem4881742 {A : Type'} (t : A -> Prop) (x : A) : (term396 A t x) = (term606 A t x).
Proof. exact (MK_COMB (@lem4881733) (@lem4881741 A t x)). Qed.
Lemma lem4881743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881750 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881751 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4881750 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4881752 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4881751 A f c). Qed.
Lemma lem4881753 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4881754 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t).
Proof. exact (MK_COMB (@lem4881752 A f c) (@lem4881753 A t)). Qed.
Lemma lem4881756 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881757 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881756 (A -> Prop) Prop f x). Qed.
Lemma lem4881758 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t) = (term602 A f c t).
Proof. exact (@lem4881757 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) t). Qed.
Lemma lem4881760 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (term602 A f c t).
Proof. exact (TRANS (@lem4881754 A f c t) (@lem4881758 A f c t)). Qed.
Lemma lem4881761 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term607 A f c t) = (term608 A f c t).
Proof. exact (MK_COMB (@lem4881743) (@lem4881760 A f c t)). Qed.
Lemma lem4881762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881763 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term609 A f c t) = (term610 A f c t).
Proof. exact (MK_COMB (@lem4881762) (@lem4881761 A f c t)). Qed.
Lemma lem4881764 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term386 A f c t x) = (term611 A f c t x).
Proof. exact (MK_COMB (@lem4881763 A f c t) (@lem4881742 A t x)). Qed.
Lemma lem4881765 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term394 A f c x) = (term612 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881764 A f c t x)). Qed.
Lemma lem4881766 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881767 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term395 A f c x) = (term613 A f c x).
Proof. exact (MK_COMB (@lem4881766 A) (@lem4881765 A f c x)). Qed.
Lemma lem4881768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881769 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term398 A f c x) = (term614 A f c x).
Proof. exact (MK_COMB (@lem4881768) (@lem4881767 A f c x)). Qed.
Lemma lem4881770 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term400 A f c x) = (term615 A f c x).
Proof. exact (MK_COMB (@lem4881769 A f c x) (@lem4881732 A c x)). Qed.
Lemma lem4881771 {A : Type'} (f : type639 A) (c : A -> Prop) : (term423 A f c) = (term616 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881770 A f c x)). Qed.
Lemma lem4881772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881773 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term617 A f c).
Proof. exact (MK_COMB (@lem4881772 A) (@lem4881771 A f c)). Qed.
Lemma lem4881774 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881780 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4881779 A Prop f x). Qed.
Lemma lem4881782 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4881780 A c x). Qed.
Lemma lem4881783 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term606 A c x).
Proof. exact (MK_COMB (@lem4881774) (@lem4881782 A c x)). Qed.
Lemma lem4881792 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881793 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4881792 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4881794 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4881793 A t' c). Qed.
Lemma lem4881795 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4881796 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4881794 A t' c) (@lem4881795 A x)). Qed.
Lemma lem4881798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881799 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4881798 A (A -> Prop) f x). Qed.
Lemma lem4881800 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term618 A t' c x).
Proof. exact (@lem4881799 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4881801 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term618 A t' c x).
Proof. exact (TRANS (@lem4881796 A t' c x) (@lem4881800 A t' c x)). Qed.
Lemma lem4881802 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4881803 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term619 A t' c x).
Proof. exact (MK_COMB (@lem4881801 A t' c x) (@lem4881802 A x)). Qed.
Lemma lem4881805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881806 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4881805 A Prop f x). Qed.
Lemma lem4881807 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term619 A t' c x) = (term620 A t' c x).
Proof. exact (@lem4881806 A (term618 A t' c x) x). Qed.
Lemma lem4881809 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term620 A t' c x).
Proof. exact (TRANS (@lem4881803 A t' c x) (@lem4881807 A t' c x)). Qed.
Lemma lem4881818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881819 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4881818 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4881820 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4881819 A t' c). Qed.
Lemma lem4881821 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4881822 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4881820 A t' c) (@lem4881821 A x)). Qed.
Lemma lem4881824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881825 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4881824 A (A -> Prop) f x). Qed.
Lemma lem4881826 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term618 A t' c x).
Proof. exact (@lem4881825 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4881828 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term618 A t' c x).
Proof. exact (TRANS (@lem4881822 A t' c x) (@lem4881826 A t' c x)). Qed.
Lemma lem4881829 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (f c).
Proof. exact (eq_refl (f c)). Qed.
Lemma lem4881830 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term621 A f t' c x) = (term622 A f t' c x).
Proof. exact (MK_COMB (@lem4881829 A f c) (@lem4881828 A t' c x)). Qed.
Lemma lem4881832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881833 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4881832 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4881834 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4881833 A f c). Qed.
Lemma lem4881835 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term618 A t' c x) = (term618 A t' c x).
Proof. exact (eq_refl (term618 A t' c x)). Qed.
Lemma lem4881836 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term622 A f t' c x) = (term623 A f t' c x).
Proof. exact (MK_COMB (@lem4881834 A f c) (@lem4881835 A t' c x)). Qed.
Lemma lem4881838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881839 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881838 (A -> Prop) Prop f x). Qed.
Lemma lem4881840 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term623 A f t' c x) = (term624 A f t' c x).
Proof. exact (@lem4881839 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) (term618 A t' c x)). Qed.
Lemma lem4881841 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term622 A f t' c x) = (term624 A f t' c x).
Proof. exact (TRANS (@lem4881836 A f t' c x) (@lem4881840 A f t' c x)). Qed.
Lemma lem4881842 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term621 A f t' c x) = (term624 A f t' c x).
Proof. exact (TRANS (@lem4881830 A f t' c x) (@lem4881841 A f t' c x)). Qed.
Lemma lem4881843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881844 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term625 A f t' c x) = (term626 A f t' c x).
Proof. exact (MK_COMB (@lem4881843) (@lem4881842 A f t' c x)). Qed.
Lemma lem4881845 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term627 A f t' c x) = (term628 A f t' c x).
Proof. exact (MK_COMB (@lem4881844 A f t' c x) (@lem4881809 A t' c x)). Qed.
Lemma lem4881846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881847 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term629 A f t' c x) = (term630 A f t' c x).
Proof. exact (MK_COMB (@lem4881846) (@lem4881845 A f t' c x)). Qed.
Lemma lem4881848 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term631 A f t' c x) = (term632 A f t' c x).
Proof. exact (MK_COMB (@lem4881847 A f t' c x) (@lem4881783 A c x)). Qed.
Lemma lem4881849 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term633 A f t' c) = (term634 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4881848 A f t' c x)). Qed.
Lemma lem4881850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881851 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term635 A f t' c) = (term636 A f t' c).
Proof. exact (MK_COMB (@lem4881850 A) (@lem4881849 A f t' c)). Qed.
Lemma lem4881852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881853 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term637 A f t' c) = (term638 A f t' c).
Proof. exact (MK_COMB (@lem4881852) (@lem4881851 A f t' c)). Qed.
Lemma lem4881854 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term640 A t' f c).
Proof. exact (MK_COMB (@lem4881853 A f t' c) (@lem4881773 A f c)). Qed.
Lemma lem4881859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881860 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881859 (A -> Prop) Prop f x). Qed.
Lemma lem4881862 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (@I ((A -> Prop) -> Prop) P c').
Proof. exact (@lem4881860 A P c'). Qed.
Lemma lem4881863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881870 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881871 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4881870 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4881872 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4881871 A f c). Qed.
Lemma lem4881873 {A : Type'} (c' : A -> Prop) : c' = c'.
Proof. exact (eq_refl c'). Qed.
Lemma lem4881874 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c').
Proof. exact (MK_COMB (@lem4881872 A f c) (@lem4881873 A c')). Qed.
Lemma lem4881876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881877 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881876 (A -> Prop) Prop f x). Qed.
Lemma lem4881878 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c') = (term602 A f c c').
Proof. exact (@lem4881877 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) c'). Qed.
Lemma lem4881880 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (term602 A f c c').
Proof. exact (TRANS (@lem4881874 A f c c') (@lem4881878 A f c c')). Qed.
Lemma lem4881881 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term607 A f c c') = (term608 A f c c').
Proof. exact (MK_COMB (@lem4881863) (@lem4881880 A f c c')). Qed.
Lemma lem4881882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881883 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term609 A f c c') = (term610 A f c c').
Proof. exact (MK_COMB (@lem4881882) (@lem4881881 A f c c')). Qed.
Lemma lem4881884 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term382 A f c P c') = (term641 A f c P c').
Proof. exact (MK_COMB (@lem4881883 A f c c') (@lem4881862 A P c')). Qed.
Lemma lem4881885 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term383 A f c P) = (term642 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4881884 A f c P c')). Qed.
Lemma lem4881886 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881887 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term384 A f c P) = (term643 A f c P).
Proof. exact (MK_COMB (@lem4881886 A) (@lem4881885 A f c P)). Qed.
Lemma lem4881888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881889 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term644 A f c P).
Proof. exact (MK_COMB (@lem4881888) (@lem4881887 A f c P)). Qed.
Lemma lem4881890 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term645 A P t' f c) = (term646 A P t' f c).
Proof. exact (MK_COMB (@lem4881889 A f c P) (@lem4881854 A t' f c)). Qed.
Lemma lem4881891 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4881896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881897 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4881896 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4881899 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4881897 A f c). Qed.
Lemma lem4881900 {A : Type'} (f : type639 A) (c : A -> Prop) : (term195 A f c) = (term647 A f c).
Proof. exact (MK_COMB (@lem4881891 A) (@lem4881899 A f c)). Qed.
Lemma lem4881902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881903 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4881902 (type686 A) Prop f x). Qed.
Lemma lem4881904 {A : Type'} (f : type639 A) (c : A -> Prop) : (term647 A f c) = (term648 A f c).
Proof. exact (@lem4881903 A (@FINITE (A -> Prop)) (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c)). Qed.
Lemma lem4881905 {A : Type'} (f : type639 A) (c : A -> Prop) : (term195 A f c) = (term648 A f c).
Proof. exact (TRANS (@lem4881900 A f c) (@lem4881904 A f c)). Qed.
Lemma lem4881906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881907 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term649 A f c).
Proof. exact (MK_COMB (@lem4881906) (@lem4881905 A f c)). Qed.
Lemma lem4881908 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term650 A P t' f c) = (term651 A P t' f c).
Proof. exact (MK_COMB (@lem4881907 A f c) (@lem4881890 A P t' f c)). Qed.
Lemma lem4881909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4881914 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4881915 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4881914 (A -> Prop) Prop f x). Qed.
Lemma lem4881917 {A : Type'} (u : type686 A) (c : A -> Prop) : (u c) = (@I ((A -> Prop) -> Prop) u c).
Proof. exact (@lem4881915 A u c). Qed.
Lemma lem4881918 {A : Type'} (u : type686 A) (c : A -> Prop) : (term381 A u c) = (term605 A u c).
Proof. exact (MK_COMB (@lem4881909) (@lem4881917 A u c)). Qed.
Lemma lem4881919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881920 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term652 A u c).
Proof. exact (MK_COMB (@lem4881919) (@lem4881918 A u c)). Qed.
Lemma lem4881921 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term575 A u P t' f c) = (term653 A u P t' f c).
Proof. exact (MK_COMB (@lem4881920 A u c) (@lem4881908 A P t' f c)). Qed.
Lemma lem4881922 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term577 A u P t' f) = (term654 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4881921 A u P t' f c)). Qed.
Lemma lem4881923 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881924 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term579 A u P t' f) = (term655 A u P t' f).
Proof. exact (MK_COMB (@lem4881923 A) (@lem4881922 A u P t' f)). Qed.
Lemma lem4881925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881926 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term596 A u P t' f) = (term656 A u P t' f).
Proof. exact (MK_COMB (@lem4881925) (@lem4881924 A u P t' f)). Qed.
Lemma lem4881927 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) : (term598 A P t' f u) = (term657 A P t' f u).
Proof. exact (MK_COMB (@lem4881926 A u P t' f) (@lem4881724 A u)). Qed.
Lemma lem4881928 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term657 A P t' f u.
Proof. exact (EQ_MP (@lem4881927 A P t' f u) (@lem4881676 A P t' f u h1)). Qed.
Lemma lem4881930 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term655 A u P t' f.
Proof. exact (proj1 (@lem4881928 A P t' f u h1)). Qed.
Lemma lem4881938 {A : Type'} (P : A -> Prop) (Q : Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4881939 {A : Type'} (P : type686 A) (Q : Prop) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4881938 (A -> Prop) P Q). Qed.
Lemma lem4881940 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term663 A f c x).
Proof. exact (@lem4881939 A (term612 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4881941 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4881942 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term612 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881941 A f c t x)). Qed.
Lemma lem4881943 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881944 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term613 A f c x).
Proof. exact (MK_COMB (@lem4881943 A) (@lem4881942 A f c x)). Qed.
Lemma lem4881945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881946 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term667 A f c x) = (term614 A f c x).
Proof. exact (MK_COMB (@lem4881945) (@lem4881944 A f c x)). Qed.
Lemma lem4881947 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4881948 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term615 A f c x).
Proof. exact (MK_COMB (@lem4881946 A f c x) (@lem4881947 A c x)). Qed.
Lemma lem4881949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881950 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term668 A f c x) = (term669 A f c x).
Proof. exact (MK_COMB (@lem4881949) (@lem4881948 A f c x)). Qed.
Lemma lem4881951 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4881952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4881953 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term670 A f c x t) = (term671 A f c t x).
Proof. exact (MK_COMB (@lem4881952) (@lem4881951 A f c t x)). Qed.
Lemma lem4881954 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4881955 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term672 A f t c x) = (term673 A f t c x).
Proof. exact (MK_COMB (@lem4881953 A f c t x) (@lem4881954 A c x)). Qed.
Lemma lem4881956 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term674 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881955 A f t c x)). Qed.
Lemma lem4881957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4881958 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term663 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4881957 A) (@lem4881956 A f c x)). Qed.
Lemma lem4881959 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A f c x) = (term663 A f c x)) = ((term615 A f c x) = (term676 A f c x)).
Proof. exact (MK_COMB (@lem4881950 A f c x) (@lem4881958 A f c x)). Qed.
Lemma lem4881960 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term615 A f c x) = (term676 A f c x).
Proof. exact (EQ_MP (@lem4881959 A f c x) (@lem4881940 A f c x)). Qed.
Lemma lem4881961 {A : Type'} (f : type639 A) (c : A -> Prop) : (term616 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881960 A f c x)). Qed.
Lemma lem4881962 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881963 {A : Type'} (f : type639 A) (c : A -> Prop) : (term617 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4881962 A) (@lem4881961 A f c)). Qed.
Lemma lem4881964 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term638 A f t' c) = (term638 A f t' c).
Proof. exact (eq_refl (term638 A f t' c)). Qed.
Lemma lem4881965 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4881964 A f t' c) (@lem4881963 A f c)). Qed.
Lemma lem4881967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4881968 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (@lem4881967 A P Q). Qed.
Lemma lem4881969 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term681 A t' f c).
Proof. exact (@lem4881968 A (term634 A f t' c) (term677 A f c)). Qed.
Lemma lem4881970 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4881971 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term683 A f t' c) = (term634 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4881970 A f t' c x)). Qed.
Lemma lem4881972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881973 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term684 A f t' c) = (term636 A f t' c).
Proof. exact (MK_COMB (@lem4881972 A) (@lem4881971 A f t' c)). Qed.
Lemma lem4881974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881975 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term685 A f t' c) = (term638 A f t' c).
Proof. exact (MK_COMB (@lem4881974) (@lem4881973 A f t' c)). Qed.
Lemma lem4881976 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4881977 {A : Type'} (f : type639 A) (c : A -> Prop) : (term687 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4881976 A f c x)). Qed.
Lemma lem4881978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881979 {A : Type'} (f : type639 A) (c : A -> Prop) : (term688 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4881978 A) (@lem4881977 A f c)). Qed.
Lemma lem4881980 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4881975 A f t' c) (@lem4881979 A f c)). Qed.
Lemma lem4881981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4881982 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term689 A t' f c) = (term690 A t' f c).
Proof. exact (MK_COMB (@lem4881981) (@lem4881980 A t' f c)). Qed.
Lemma lem4881983 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4881984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4881985 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term691 A f t' c x) = (term692 A f t' c x).
Proof. exact (MK_COMB (@lem4881984) (@lem4881983 A f t' c x)). Qed.
Lemma lem4881986 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4881987 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term693 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4881985 A f t' c x) (@lem4881986 A f c x)). Qed.
Lemma lem4881988 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A t' f c) = (term696 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4881987 A t' f c x)). Qed.
Lemma lem4881989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4881990 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A t' f c) = (term697 A t' f c).
Proof. exact (MK_COMB (@lem4881989 A) (@lem4881988 A t' f c)). Qed.
Lemma lem4881991 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term680 A t' f c) = (term681 A t' f c)) = ((term679 A t' f c) = (term697 A t' f c)).
Proof. exact (MK_COMB (@lem4881982 A t' f c) (@lem4881990 A t' f c)). Qed.
Lemma lem4881992 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term697 A t' f c).
Proof. exact (EQ_MP (@lem4881991 A t' f c) (@lem4881969 A t' f c)). Qed.
Lemma lem4881994 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4881995 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4881994 (A -> Prop) P Q). Qed.
Lemma lem4881996 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term703 A t' f c x).
Proof. exact (@lem4881995 A (term632 A f t' c x) (term675 A f c x)). Qed.
Lemma lem4881997 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4881998 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term705 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4881997 A f t c x)). Qed.
Lemma lem4881999 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882000 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term706 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4881999 A) (@lem4881998 A f c x)). Qed.
Lemma lem4882001 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4882002 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4882001 A f t' c x) (@lem4882000 A f c x)). Qed.
Lemma lem4882003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882004 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term707 A t' f c x) = (term708 A t' f c x).
Proof. exact (MK_COMB (@lem4882003) (@lem4882002 A t' f c x)). Qed.
Lemma lem4882005 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4882006 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4882007 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term709 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (MK_COMB (@lem4882006 A f t' c x) (@lem4882005 A f t c x)). Qed.
Lemma lem4882008 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882007 A t' f t c x)). Qed.
Lemma lem4882009 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882010 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4882009 A) (@lem4882008 A t' f c x)). Qed.
Lemma lem4882011 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term702 A t' f c x) = (term703 A t' f c x)) = ((term694 A t' f c x) = (term713 A t' f c x)).
Proof. exact (MK_COMB (@lem4882004 A t' f c x) (@lem4882010 A t' f c x)). Qed.
Lemma lem4882012 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term694 A t' f c x) = (term713 A t' f c x).
Proof. exact (EQ_MP (@lem4882011 A t' f c x) (@lem4881996 A t' f c x)). Qed.
Lemma lem4882013 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882012 A t' f c x)). Qed.
Lemma lem4882014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882015 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4882014 A) (@lem4882013 A t' f c)). Qed.
Lemma lem4882016 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4881992 A t' f c) (@lem4882015 A t' f c)). Qed.
Lemma lem4882017 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4881965 A t' f c) (@lem4882016 A t' f c)). Qed.
Lemma lem4882018 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term644 A f c P) = (term644 A f c P).
Proof. exact (eq_refl (term644 A f c P)). Qed.
Lemma lem4882019 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4882018 A f c P) (@lem4882017 A t' f c)). Qed.
Lemma lem4882023 {A : Type'} (P : A -> Prop) (Q : Prop) : (term717 A P Q) = (term718 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4882024 {A : Type'} (P : type686 A) (Q : Prop) : (term719 A P Q) = (term720 A P Q).
Proof. exact (@lem4882023 (A -> Prop) P Q). Qed.
Lemma lem4882025 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term722 A P t' f c).
Proof. exact (@lem4882024 A (term642 A f c P) (term715 A t' f c)). Qed.
Lemma lem4882026 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4882027 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term724 A f c P) = (term642 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882026 A f c P c')). Qed.
Lemma lem4882028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882029 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term725 A f c P) = (term643 A f c P).
Proof. exact (MK_COMB (@lem4882028 A) (@lem4882027 A f c P)). Qed.
Lemma lem4882030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882031 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term726 A f c P) = (term644 A f c P).
Proof. exact (MK_COMB (@lem4882030) (@lem4882029 A f c P)). Qed.
Lemma lem4882032 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4882033 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4882031 A f c P) (@lem4882032 A t' f c)). Qed.
Lemma lem4882034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882035 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c) = (term728 A P t' f c).
Proof. exact (MK_COMB (@lem4882034) (@lem4882033 A P t' f c)). Qed.
Lemma lem4882036 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4882037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882038 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term729 A f c P c') = (term730 A f c P c').
Proof. exact (MK_COMB (@lem4882037) (@lem4882036 A f c P c')). Qed.
Lemma lem4882039 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4882040 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term731 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882038 A f c P c') (@lem4882039 A t' f c)). Qed.
Lemma lem4882041 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P t' f c) = (term734 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882040 A P c' t' f c)). Qed.
Lemma lem4882042 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882043 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term722 A P t' f c) = (term735 A P t' f c).
Proof. exact (MK_COMB (@lem4882042 A) (@lem4882041 A P t' f c)). Qed.
Lemma lem4882044 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term721 A P t' f c) = (term722 A P t' f c)) = ((term716 A P t' f c) = (term735 A P t' f c)).
Proof. exact (MK_COMB (@lem4882035 A P t' f c) (@lem4882043 A P t' f c)). Qed.
Lemma lem4882045 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term735 A P t' f c).
Proof. exact (EQ_MP (@lem4882044 A P t' f c) (@lem4882025 A P t' f c)). Qed.
Lemma lem4882047 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4882048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4882047 A P Q). Qed.
Lemma lem4882049 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term737 A P c' t' f c).
Proof. exact (@lem4882048 A (term641 A f c P c') (term714 A t' f c)). Qed.
Lemma lem4882050 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4882051 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term739 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882050 A t' f c x)). Qed.
Lemma lem4882052 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882053 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4882052 A) (@lem4882051 A t' f c)). Qed.
Lemma lem4882054 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4882055 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882054 A f c P c') (@lem4882053 A t' f c)). Qed.
Lemma lem4882056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882057 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term742 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882056) (@lem4882055 A P c' t' f c)). Qed.
Lemma lem4882058 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4882059 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4882060 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term743 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882059 A f c P c') (@lem4882058 A t' f c x)). Qed.
Lemma lem4882061 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term745 A P c' t' f c) = (term746 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882060 A P c' t' f c x)). Qed.
Lemma lem4882062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882063 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882062 A) (@lem4882061 A P c' t' f c)). Qed.
Lemma lem4882064 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term736 A P c' t' f c) = (term737 A P c' t' f c)) = ((term732 A P c' t' f c) = (term747 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4882057 A P c' t' f c) (@lem4882063 A P c' t' f c)). Qed.
Lemma lem4882065 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (EQ_MP (@lem4882064 A P c' t' f c) (@lem4882049 A P c' t' f c)). Qed.
Lemma lem4882067 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4882068 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4882067 (A -> Prop) P Q). Qed.
Lemma lem4882069 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term749 A P c' t' f c x).
Proof. exact (@lem4882068 A (term641 A f c P c') (term712 A t' f c x)). Qed.
Lemma lem4882070 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4882071 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term751 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882070 A t' f t c x)). Qed.
Lemma lem4882072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882073 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4882072 A) (@lem4882071 A t' f c x)). Qed.
Lemma lem4882074 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4882075 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882074 A f c P c') (@lem4882073 A t' f c x)). Qed.
Lemma lem4882076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882077 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term754 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882076) (@lem4882075 A P c' t' f c x)). Qed.
Lemma lem4882078 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4882079 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4882080 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term755 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882079 A f c P c') (@lem4882078 A t' f t c x)). Qed.
Lemma lem4882081 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term757 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882080 A P c' t' f t c x)). Qed.
Lemma lem4882082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882083 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882082 A) (@lem4882081 A P c' t' f c x)). Qed.
Lemma lem4882084 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term748 A P c' t' f c x) = (term749 A P c' t' f c x)) = ((term744 A P c' t' f c x) = (term759 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4882077 A P c' t' f c x) (@lem4882083 A P c' t' f c x)). Qed.
Lemma lem4882085 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4882084 A P c' t' f c x) (@lem4882069 A P c' t' f c x)). Qed.
Lemma lem4882086 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882085 A P c' t' f c x)). Qed.
Lemma lem4882087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882088 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882087 A) (@lem4882086 A P c' t' f c)). Qed.
Lemma lem4882089 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (TRANS (@lem4882065 A P c' t' f c) (@lem4882088 A P c' t' f c)). Qed.
Lemma lem4882090 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882089 A P c' t' f c)). Qed.
Lemma lem4882091 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882092 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4882091 A) (@lem4882090 A P t' f c)). Qed.
Lemma lem4882093 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4882045 A P t' f c) (@lem4882092 A P t' f c)). Qed.
Lemma lem4882094 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4882019 A P t' f c) (@lem4882093 A P t' f c)). Qed.
Lemma lem4882095 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882096 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4882095 A f c) (@lem4882094 A P t' f c)). Qed.
Lemma lem4882098 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4882099 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4882098 (A -> Prop) P Q). Qed.
Lemma lem4882100 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term766 A P t' f c).
Proof. exact (@lem4882099 A (term648 A f c) (term762 A P t' f c)). Qed.
Lemma lem4882101 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4882102 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term768 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882101 A P c' t' f c)). Qed.
Lemma lem4882103 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882104 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term769 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4882103 A) (@lem4882102 A P t' f c)). Qed.
Lemma lem4882105 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882106 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4882105 A f c) (@lem4882104 A P t' f c)). Qed.
Lemma lem4882107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882108 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A P t' f c) = (term771 A P t' f c).
Proof. exact (MK_COMB (@lem4882107) (@lem4882106 A P t' f c)). Qed.
Lemma lem4882109 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4882110 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882111 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882110 A f c) (@lem4882109 A P c' t' f c)). Qed.
Lemma lem4882112 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term775 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882111 A P c' t' f c)). Qed.
Lemma lem4882113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882114 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term766 A P t' f c) = (term776 A P t' f c).
Proof. exact (MK_COMB (@lem4882113 A) (@lem4882112 A P t' f c)). Qed.
Lemma lem4882115 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term765 A P t' f c) = (term766 A P t' f c)) = ((term764 A P t' f c) = (term776 A P t' f c)).
Proof. exact (MK_COMB (@lem4882108 A P t' f c) (@lem4882114 A P t' f c)). Qed.
Lemma lem4882116 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term776 A P t' f c).
Proof. exact (EQ_MP (@lem4882115 A P t' f c) (@lem4882100 A P t' f c)). Qed.
Lemma lem4882118 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4882119 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4882118 A P Q). Qed.
Lemma lem4882120 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term778 A P c' t' f c).
Proof. exact (@lem4882119 A (term648 A f c) (term760 A P c' t' f c)). Qed.
Lemma lem4882121 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4882122 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882121 A P c' t' f c x)). Qed.
Lemma lem4882123 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882124 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882123 A) (@lem4882122 A P c' t' f c)). Qed.
Lemma lem4882125 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882126 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882125 A f c) (@lem4882124 A P c' t' f c)). Qed.
Lemma lem4882127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882128 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A P c' t' f c) = (term783 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882127) (@lem4882126 A P c' t' f c)). Qed.
Lemma lem4882129 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4882130 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882131 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882130 A f c) (@lem4882129 A P c' t' f c x)). Qed.
Lemma lem4882132 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term787 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882131 A P c' t' f c x)). Qed.
Lemma lem4882133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882134 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882133 A) (@lem4882132 A P c' t' f c)). Qed.
Lemma lem4882135 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term777 A P c' t' f c) = (term778 A P c' t' f c)) = ((term773 A P c' t' f c) = (term788 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4882128 A P c' t' f c) (@lem4882134 A P c' t' f c)). Qed.
Lemma lem4882136 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (EQ_MP (@lem4882135 A P c' t' f c) (@lem4882120 A P c' t' f c)). Qed.
Lemma lem4882138 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4882139 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4882138 (A -> Prop) P Q). Qed.
Lemma lem4882140 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term790 A P c' t' f c x).
Proof. exact (@lem4882139 A (term648 A f c) (term758 A P c' t' f c x)). Qed.
Lemma lem4882141 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4882142 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term792 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882141 A P c' t' f t c x)). Qed.
Lemma lem4882143 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882144 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term793 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882143 A) (@lem4882142 A P c' t' f c x)). Qed.
Lemma lem4882145 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882146 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882145 A f c) (@lem4882144 A P c' t' f c x)). Qed.
Lemma lem4882147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882148 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A P c' t' f c x) = (term795 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882147) (@lem4882146 A P c' t' f c x)). Qed.
Lemma lem4882149 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4882150 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882151 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882150 A f c) (@lem4882149 A P c' t' f t c x)). Qed.
Lemma lem4882152 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882151 A P c' t' f t c x)). Qed.
Lemma lem4882153 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882154 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882153 A) (@lem4882152 A P c' t' f c x)). Qed.
Lemma lem4882155 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term789 A P c' t' f c x) = (term790 A P c' t' f c x)) = ((term785 A P c' t' f c x) = (term800 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4882148 A P c' t' f c x) (@lem4882154 A P c' t' f c x)). Qed.
Lemma lem4882156 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term785 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4882155 A P c' t' f c x) (@lem4882140 A P c' t' f c x)). Qed.
Lemma lem4882157 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882156 A P c' t' f c x)). Qed.
Lemma lem4882158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882159 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term788 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882158 A) (@lem4882157 A P c' t' f c)). Qed.
Lemma lem4882160 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (TRANS (@lem4882136 A P c' t' f c) (@lem4882159 A P c' t' f c)). Qed.
Lemma lem4882161 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882160 A P c' t' f c)). Qed.
Lemma lem4882162 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882163 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term776 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4882162 A) (@lem4882161 A P t' f c)). Qed.
Lemma lem4882164 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4882116 A P t' f c) (@lem4882163 A P t' f c)). Qed.
Lemma lem4882165 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4882096 A P t' f c) (@lem4882164 A P t' f c)). Qed.
Lemma lem4882166 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882167 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4882166 A u c) (@lem4882165 A P t' f c)). Qed.
Lemma lem4882169 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4882170 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4882169 (A -> Prop) P Q). Qed.
Lemma lem4882171 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term811 A u P t' f c).
Proof. exact (@lem4882170 A (term605 A u c) (term803 A P t' f c)). Qed.
Lemma lem4882172 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4882173 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term813 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882172 A P c' t' f c)). Qed.
Lemma lem4882174 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882175 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term814 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4882174 A) (@lem4882173 A P t' f c)). Qed.
Lemma lem4882176 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882177 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4882176 A u c) (@lem4882175 A P t' f c)). Qed.
Lemma lem4882178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882179 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term815 A u P t' f c) = (term816 A u P t' f c).
Proof. exact (MK_COMB (@lem4882178) (@lem4882177 A u P t' f c)). Qed.
Lemma lem4882180 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4882181 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882182 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term817 A u P t' f c c') = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4882181 A u c) (@lem4882180 A P c' t' f c)). Qed.
Lemma lem4882183 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term819 A u P t' f c) = (term820 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882182 A u P c' t' f c)). Qed.
Lemma lem4882184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882185 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term811 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (MK_COMB (@lem4882184 A) (@lem4882183 A u P t' f c)). Qed.
Lemma lem4882186 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term810 A u P t' f c) = (term811 A u P t' f c)) = ((term805 A u P t' f c) = (term821 A u P t' f c)).
Proof. exact (MK_COMB (@lem4882179 A u P t' f c) (@lem4882185 A u P t' f c)). Qed.
Lemma lem4882187 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (EQ_MP (@lem4882186 A u P t' f c) (@lem4882171 A u P t' f c)). Qed.
Lemma lem4882189 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4882190 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (@lem4882189 A P Q). Qed.
Lemma lem4882191 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term823 A u P c' t' f c).
Proof. exact (@lem4882190 A (term605 A u c) (term801 A P c' t' f c)). Qed.
Lemma lem4882192 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4882193 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term825 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882192 A P c' t' f c x)). Qed.
Lemma lem4882194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882195 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term826 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4882194 A) (@lem4882193 A P c' t' f c)). Qed.
Lemma lem4882196 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882197 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4882196 A u c) (@lem4882195 A P c' t' f c)). Qed.
Lemma lem4882198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882199 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term827 A u P c' t' f c) = (term828 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4882198) (@lem4882197 A u P c' t' f c)). Qed.
Lemma lem4882200 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4882201 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882202 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term829 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4882201 A u c) (@lem4882200 A P c' t' f c x)). Qed.
Lemma lem4882203 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term831 A u P c' t' f c) = (term832 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882202 A u P c' t' f c x)). Qed.
Lemma lem4882204 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882205 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term823 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4882204 A) (@lem4882203 A u P c' t' f c)). Qed.
Lemma lem4882206 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term822 A u P c' t' f c) = (term823 A u P c' t' f c)) = ((term818 A u P c' t' f c) = (term833 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4882199 A u P c' t' f c) (@lem4882205 A u P c' t' f c)). Qed.
Lemma lem4882207 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4882206 A u P c' t' f c) (@lem4882191 A u P c' t' f c)). Qed.
Lemma lem4882209 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4882210 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4882209 (A -> Prop) P Q). Qed.
Lemma lem4882211 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term835 A u P c' t' f c x).
Proof. exact (@lem4882210 A (term605 A u c) (term799 A P c' t' f c x)). Qed.
Lemma lem4882212 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4882213 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term837 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882212 A P c' t' f t c x)). Qed.
Lemma lem4882214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882215 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term838 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4882214 A) (@lem4882213 A P c' t' f c x)). Qed.
Lemma lem4882216 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882217 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4882216 A u c) (@lem4882215 A P c' t' f c x)). Qed.
Lemma lem4882218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882219 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term839 A u P c' t' f c x) = (term840 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4882218) (@lem4882217 A u P c' t' f c x)). Qed.
Lemma lem4882220 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4882221 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882222 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term841 A u P c' t' f c x t) = (term842 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882221 A u c) (@lem4882220 A P c' t' f t c x)). Qed.
Lemma lem4882223 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term843 A u P c' t' f c x) = (term844 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882222 A u P c' t' f t c x)). Qed.
Lemma lem4882224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882225 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term835 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4882224 A) (@lem4882223 A u P c' t' f c x)). Qed.
Lemma lem4882226 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term834 A u P c' t' f c x) = (term835 A u P c' t' f c x)) = ((term830 A u P c' t' f c x) = (term845 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4882219 A u P c' t' f c x) (@lem4882225 A u P c' t' f c x)). Qed.
Lemma lem4882227 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term830 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4882226 A u P c' t' f c x) (@lem4882211 A u P c' t' f c x)). Qed.
Lemma lem4882228 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term832 A u P c' t' f c) = (term846 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4882227 A u P c' t' f c x)). Qed.
Lemma lem4882229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882230 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term833 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4882229 A) (@lem4882228 A u P c' t' f c)). Qed.
Lemma lem4882231 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (TRANS (@lem4882207 A u P c' t' f c) (@lem4882230 A u P c' t' f c)). Qed.
Lemma lem4882232 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term820 A u P t' f c) = (term848 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882231 A u P c' t' f c)). Qed.
Lemma lem4882233 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882234 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term821 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (MK_COMB (@lem4882233 A) (@lem4882232 A u P t' f c)). Qed.
Lemma lem4882235 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4882187 A u P t' f c) (@lem4882234 A u P t' f c)). Qed.
Lemma lem4882236 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4882167 A u P t' f c) (@lem4882235 A u P t' f c)). Qed.
Lemma lem4882237 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term654 A u P t' f) = (term850 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4882236 A u P t' f c)). Qed.
Lemma lem4882238 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882239 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term655 A u P t' f) = (term851 A u P t' f).
Proof. exact (MK_COMB (@lem4882238 A) (@lem4882237 A u P t' f)). Qed.
Lemma lem4882252 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term673 A f t c x) = (term673 A f t c x).
Proof. exact (eq_refl (term673 A f t c x)). Qed.
Lemma lem4882269 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term632 A f t' c x) = (term852 A f t' c x).
Proof. exact (@lem19699 (term624 A f t' c x) (term620 A t' c x) (term606 A c x)). Qed.
Lemma lem4882270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882271 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term853 A f t' c x).
Proof. exact (MK_COMB (@lem4882270) (@lem4882269 A f t' c x)). Qed.
Lemma lem4882272 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f t c x) = (term854 A t' f t c x).
Proof. exact (MK_COMB (@lem4882271 A f t' c x) (@lem4882252 A f t c x)). Qed.
Lemma lem4882281 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4882282 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f t c x) = (term855 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882281 A f c P c') (@lem4882272 A t' f t c x)). Qed.
Lemma lem4882285 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4882286 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term797 A P c' t' f t c x) = (term856 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882285 A f c) (@lem4882282 A P c' t' f t c x)). Qed.
Lemma lem4882289 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4882290 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term857 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4882289 A u c) (@lem4882286 A P c' t' f t c x)). Qed.
Lemma lem4882291 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term858 A u P c' t' f t c x).
Proof. exact (@lem19490 (term648 A f c) (term605 A u c) (term855 A P c' t' f t c x)). Qed.
Lemma lem4882292 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term860 A P c' u t' f t c x).
Proof. exact (@lem19490 (term641 A f c P c') (term605 A u c) (term854 A t' f t c x)). Qed.
Lemma lem4882293 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term862 A t' u f t c x).
Proof. exact (@lem19490 (term852 A f t' c x) (term605 A u c) (term673 A f t c x)). Qed.
Lemma lem4882294 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term863 A u f t c x) = (term863 A u f t c x).
Proof. exact (eq_refl (term863 A u f t c x)). Qed.
Lemma lem4882301 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term864 A u f t' c x) = (term865 A f u t' c x).
Proof. exact (@lem19490 (term866 A f t' c x) (term605 A u c) (term867 A t' c x)). Qed.
Lemma lem4882302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882303 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term868 A u f t' c x) = (term869 A f u t' c x).
Proof. exact (MK_COMB (@lem4882302) (@lem4882301 A f u t' c x)). Qed.
Lemma lem4882304 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term862 A t' u f t c x) = (term870 A t' u f t c x).
Proof. exact (MK_COMB (@lem4882303 A f u t' c x) (@lem4882294 A u f t c x)). Qed.
Lemma lem4882305 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term870 A t' u f t c x).
Proof. exact (TRANS (@lem4882293 A t' u f t c x) (@lem4882304 A t' u f t c x)). Qed.
Lemma lem4882308 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term871 A u f c P c') = (term871 A u f c P c').
Proof. exact (eq_refl (term871 A u f c P c')). Qed.
Lemma lem4882309 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term860 A P c' u t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4882308 A u f c P c') (@lem4882305 A t' u f t c x)). Qed.
Lemma lem4882310 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4882292 A P c' u t' f t c x) (@lem4882309 A P c' t' u f t c x)). Qed.
Lemma lem4882313 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term873 A u f c) = (term873 A u f c).
Proof. exact (eq_refl (term873 A u f c)). Qed.
Lemma lem4882314 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term858 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4882313 A u f c) (@lem4882310 A P c' t' u f t c x)). Qed.
Lemma lem4882315 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4882291 A u P c' t' f t c x) (@lem4882314 A P c' t' u f t c x)). Qed.
Lemma lem4882316 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4882290 A u P c' t' f t c x) (@lem4882315 A P c' t' u f t c x)). Qed.
Lemma lem4882317 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term844 A u P c' t' f c x) = (term875 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882316 A P c' t' u f t c x)). Qed.
Lemma lem4882318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882319 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term845 A u P c' t' f c x) = (term876 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4882318 A) (@lem4882317 A P c' t' u f c x)). Qed.
Lemma lem4882320 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term846 A u P c' t' f c) = (term877 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4882319 A P c' t' u f c x)). Qed.
Lemma lem4882321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882322 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term847 A u P c' t' f c) = (term878 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4882321 A) (@lem4882320 A P c' t' u f c)). Qed.
Lemma lem4882323 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term848 A u P t' f c) = (term879 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882322 A P c' t' u f c)). Qed.
Lemma lem4882324 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882325 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term849 A u P t' f c) = (term880 A P t' u f c).
Proof. exact (MK_COMB (@lem4882324 A) (@lem4882323 A P t' u f c)). Qed.
Lemma lem4882326 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term850 A u P t' f) = (term881 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4882325 A P t' u f c)). Qed.
Lemma lem4882327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882328 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term851 A u P t' f) = (term882 A P t' u f).
Proof. exact (MK_COMB (@lem4882327 A) (@lem4882326 A P t' u f)). Qed.
Lemma lem4882329 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term655 A u P t' f) = (term882 A P t' u f).
Proof. exact (TRANS (@lem4882239 A u P t' f) (@lem4882328 A P t' u f)). Qed.
Lemma lem4882330 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term882 A P t' u f.
Proof. exact (EQ_MP (@lem4882329 A P t' u f) (@lem4881930 A P t' f u h1)). Qed.
Lemma lem4882343 {A : Type'} (_60382 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term883 A P t' u f _60382.
Proof. exact (@lem4882330 A P t' f u h1 _60382). Qed.
Lemma lem4882344 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) : (term883 A P t' u f _60382) = (term880 A P t' u f _60382).
Proof. exact (eq_refl (term883 A P t' u f _60382)). Qed.
Lemma lem4882345 {A : Type'} (_60382 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term880 A P t' u f _60382.
Proof. exact (EQ_MP (@lem4882344 A P t' u f _60382) (@lem4882343 A _60382 P t' f u h1)). Qed.
Lemma lem4882346 {A : Type'} (_60382 : A -> Prop) (_60383 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term884 A P t' u f _60382 _60383.
Proof. exact (@lem4882345 A _60382 P t' f u h1 _60383). Qed.
Lemma lem4882347 {A : Type'} (P : type686 A) (_60383 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) : (term884 A P t' u f _60382 _60383) = (term878 A P _60383 t' u f _60382).
Proof. exact (eq_refl (term884 A P t' u f _60382 _60383)). Qed.
Lemma lem4882348 {A : Type'} (_60383 : A -> Prop) (_60382 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term878 A P _60383 t' u f _60382.
Proof. exact (EQ_MP (@lem4882347 A P _60383 t' u f _60382) (@lem4882346 A _60382 _60383 P t' f u h1)). Qed.
Lemma lem4882349 {A : Type'} (_60383 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term885 A P _60383 t' u f _60382 _60384.
Proof. exact (@lem4882348 A _60383 _60382 P t' f u h1 _60384). Qed.
Lemma lem4882350 {A : Type'} (P : type686 A) (_60383 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60384 : A) : (term885 A P _60383 t' u f _60382 _60384) = (term876 A P _60383 t' u f _60382 _60384).
Proof. exact (eq_refl (term885 A P _60383 t' u f _60382 _60384)). Qed.
Lemma lem4882351 {A : Type'} (_60383 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term876 A P _60383 t' u f _60382 _60384.
Proof. exact (EQ_MP (@lem4882350 A P _60383 t' u f _60382 _60384) (@lem4882349 A _60383 _60382 _60384 P t' f u h1)). Qed.
Lemma lem4882352 {A : Type'} (_60383 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) (_60385 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term886 A P _60383 t' u f _60382 _60384 _60385.
Proof. exact (@lem4882351 A _60383 _60382 _60384 P t' f u h1 _60385). Qed.
Lemma lem4882353 {A : Type'} (P : type686 A) (_60383 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60385 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) : (term886 A P _60383 t' u f _60382 _60384 _60385) = (term874 A P _60383 t' u f _60385 _60382 _60384).
Proof. exact (eq_refl (term886 A P _60383 t' u f _60382 _60384 _60385)). Qed.
Lemma lem4882354 {A : Type'} (_60383 : A -> Prop) (_60385 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term874 A P _60383 t' u f _60385 _60382 _60384.
Proof. exact (EQ_MP (@lem4882353 A P _60383 t' u f _60385 _60382 _60384) (@lem4882352 A _60383 _60382 _60384 _60385 P t' f u h1)). Qed.
Lemma lem4882355 {A : Type'} (_60383 : A -> Prop) (_60385 : A -> Prop) (_60382 : A -> Prop) (_60384 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term872 A P _60383 t' u f _60385 _60382 _60384.
Proof. exact (proj2 (@lem4882354 A _60383 _60385 _60382 _60384 P t' f u h1)). Qed.
Lemma lem4882364 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term381 A P t) : term605 A P t.
Proof. exact (EQ_MP (@lem4881715 A P t) (@lem4881675 A P t h1)). Qed.
Lemma lem4882386 {A : Type'} (_60382 : A -> Prop) (_60383 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term887 A u f _60382 P _60383.
Proof. exact (proj1 (@lem4882355 A _60383 (@el (A -> Prop)) _60382 (@el A) P t' f u h1)). Qed.
Lemma lem4882424 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4881705 A u f s t h1)). Qed.
Lemma lem4882425 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4882424 A u f s t h1). Qed.
Lemma lem4882427 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4882428 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4882427 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4882429 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4882428 A u s) (@lem4882425 A u f s t h1)). Qed.
Lemma lem4882431 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term602 A f s t.
Proof. exact (proj2 (@lem4881705 A u f s t h1)). Qed.
Lemma lem4882432 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term890 A f s t.
Proof. exact (fun h0 : term608 A f s t => @lem4882431 A u f s t h1). Qed.
Lemma lem4882434 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4882435 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term890 A f s t) = (term602 A f s t).
Proof. exact (@lem4882434 (term602 A f s t)). Qed.
Lemma lem4882436 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term602 A f s t.
Proof. exact (EQ_MP (@lem4882435 A f s t) (@lem4882432 A u f s t h1)). Qed.
Lemma lem4882452 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4882453 {A : Type'} (P : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term641 A f _60382 P _60383) = (term891 A P f _60382 _60383).
Proof. exact (@lem4882452 (@I ((A -> Prop) -> Prop) P _60383) (term608 A f _60382 _60383)). Qed.
Lemma lem4882459 {A : Type'} (u : type686 A) (_60382 : A -> Prop) : (term652 A u _60382) = (term652 A u _60382).
Proof. exact (eq_refl (term652 A u _60382)). Qed.
Lemma lem4882460 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term887 A u f _60382 P _60383) = (term892 A u P f _60382 _60383).
Proof. exact (MK_COMB (@lem4882459 A u _60382) (@lem4882453 A P f _60382 _60383)). Qed.
Lemma lem4882464 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4882465 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term892 A u P f _60382 _60383) = (term894 A P u f _60382 _60383).
Proof. exact (@lem4882464 (@I ((A -> Prop) -> Prop) P _60383) (term605 A u _60382) (term608 A f _60382 _60383)). Qed.
Lemma lem4882481 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term887 A u f _60382 P _60383) = (term894 A P u f _60382 _60383).
Proof. exact (TRANS (@lem4882460 A u P f _60382 _60383) (@lem4882465 A P u f _60382 _60383)). Qed.
Lemma lem4882482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882483 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term895 A u f _60382 P _60383) = (term896 A P u f _60382 _60383).
Proof. exact (MK_COMB (@lem4882482) (@lem4882481 A P u f _60382 _60383)). Qed.
Lemma lem4882499 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term894 A P u f _60382 _60383) = (term894 A P u f _60382 _60383).
Proof. exact (eq_refl (term894 A P u f _60382 _60383)). Qed.
Lemma lem4882500 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : ((term887 A u f _60382 P _60383) = (term894 A P u f _60382 _60383)) = ((term894 A P u f _60382 _60383) = (term894 A P u f _60382 _60383)).
Proof. exact (MK_COMB (@lem4882483 A P u f _60382 _60383) (@lem4882499 A P u f _60382 _60383)). Qed.
Lemma lem4882502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4882503 (x : Prop) : (x = x) = True.
Proof. exact (@lem4882502 Prop x). Qed.
Lemma lem4882504 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : ((term894 A P u f _60382 _60383) = (term894 A P u f _60382 _60383)) = True.
Proof. exact (@lem4882503 (term894 A P u f _60382 _60383)). Qed.
Lemma lem4882505 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : ((term887 A u f _60382 P _60383) = (term894 A P u f _60382 _60383)) = True.
Proof. exact (TRANS (@lem4882500 A P u f _60382 _60383) (@lem4882504 A P u f _60382 _60383)). Qed.
Lemma lem4882506 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : True = ((term887 A u f _60382 P _60383) = (term894 A P u f _60382 _60383)).
Proof. exact (SYM (@lem4882505 A P u f _60382 _60383)). Qed.
Lemma lem4882507 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term887 A u f _60382 P _60383) = (term894 A P u f _60382 _60383).
Proof. exact (EQ_MP (@lem4882506 A P u f _60382 _60383) (@lem0)). Qed.
Lemma lem4882508 {A : Type'} (_60382 : A -> Prop) (_60383 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term894 A P u f _60382 _60383.
Proof. exact (EQ_MP (@lem4882507 A P u f _60382 _60383) (@lem4882386 A _60382 _60383 P t' f u h1)). Qed.
Lemma lem4882510 (b : Prop) (a : Prop) : (a \/ b) = (term897 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4882511 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (P : type686 A) (_60383 : A -> Prop) : (term894 A P u f _60382 _60383) = (term898 A u f _60382 P _60383).
Proof. exact (@lem4882510 (term899 A u f _60382 _60383) (@I ((A -> Prop) -> Prop) P _60383)). Qed.
Lemma lem4882513 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4882514 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term902 A u f _60382 _60383) = (term903 A u f _60382 _60383).
Proof. exact (@lem4882513 (term605 A u _60382) (term608 A f _60382 _60383)). Qed.
Lemma lem4882516 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4882517 {A : Type'} (u : type686 A) (_60382 : A -> Prop) : (term904 A u _60382) = (@I ((A -> Prop) -> Prop) u _60382).
Proof. exact (@lem4882516 (@I ((A -> Prop) -> Prop) u _60382)). Qed.
Lemma lem4882518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882519 {A : Type'} (u : type686 A) (_60382 : A -> Prop) : (term905 A u _60382) = (term603 A u _60382).
Proof. exact (MK_COMB (@lem4882518) (@lem4882517 A u _60382)). Qed.
Lemma lem4882521 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4882522 {A : Type'} (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term906 A f _60382 _60383) = (term602 A f _60382 _60383).
Proof. exact (@lem4882521 (term602 A f _60382 _60383)). Qed.
Lemma lem4882523 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term903 A u f _60382 _60383) = (term604 A u f _60382 _60383).
Proof. exact (MK_COMB (@lem4882519 A u _60382) (@lem4882522 A f _60382 _60383)). Qed.
Lemma lem4882524 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term902 A u f _60382 _60383) = (term604 A u f _60382 _60383).
Proof. exact (TRANS (@lem4882514 A u f _60382 _60383) (@lem4882523 A u f _60382 _60383)). Qed.
Lemma lem4882525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4882526 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (_60383 : A -> Prop) : (term907 A u f _60382 _60383) = (term908 A u f _60382 _60383).
Proof. exact (MK_COMB (@lem4882525) (@lem4882524 A u f _60382 _60383)). Qed.
Lemma lem4882527 {A : Type'} (P : type686 A) (_60383 : A -> Prop) : (@I ((A -> Prop) -> Prop) P _60383) = (@I ((A -> Prop) -> Prop) P _60383).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) P _60383)). Qed.
Lemma lem4882528 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (P : type686 A) (_60383 : A -> Prop) : (term898 A u f _60382 P _60383) = (term909 A u f _60382 P _60383).
Proof. exact (MK_COMB (@lem4882526 A u f _60382 _60383) (@lem4882527 A P _60383)). Qed.
Lemma lem4882529 {A : Type'} (u : type686 A) (f : type639 A) (_60382 : A -> Prop) (P : type686 A) (_60383 : A -> Prop) : (term894 A P u f _60382 _60383) = (term909 A u f _60382 P _60383).
Proof. exact (TRANS (@lem4882511 A u f _60382 P _60383) (@lem4882528 A u f _60382 P _60383)). Qed.
Lemma lem4882531 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term352 A u f s t) : term604 A u f s t.
Proof. exact (conj (@lem4882429 A u f s t h1) (@lem4882436 A u f s t h1)). Qed.
Lemma lem4882533 {A : Type'} (_60382 : A -> Prop) (_60383 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term909 A u f _60382 P _60383.
Proof. exact (EQ_MP (@lem4882529 A u f _60382 P _60383) (@lem4882508 A _60382 _60383 P t' f u h1)). Qed.
Lemma lem4882534 {A : Type'} (_60382 : A -> Prop) (_60383 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term909 A u f _60382 P _60383.
Proof. exact (@lem4882533 A _60382 _60383 P t' f u h1). Qed.
Lemma lem4882535 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term909 A u f s P t.
Proof. exact (@lem4882534 A s t P t' f u h1). Qed.
Lemma lem4882538 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term598 A P t' f u) (h2 : term352 A u f s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (@lem4882535 A s t P t' f u h1 (@lem4882531 A u f s t h2)). Qed.
Lemma lem4882539 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term598 A P t' f u) (h2 : term352 A u f s t) : term888 A P t.
Proof. exact (fun h0 : term605 A P t => @lem4882538 A P t' u f s t h1 h2). Qed.
Lemma lem4882541 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4882542 {A : Type'} (P : type686 A) (t : A -> Prop) : (term888 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4882541 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4882543 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term598 A P t' f u) (h2 : term352 A u f s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4882542 A P t) (@lem4882539 A P t' u f s t h1 h2)). Qed.
Lemma lem4882546 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4882548 {A : Type'} (P : type686 A) (t : A -> Prop) : (term605 A P t) = (term910 A P t).
Proof. exact (@lem4882546 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4882551 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term381 A P t) : term910 A P t.
Proof. exact (EQ_MP (@lem4882548 A P t) (@lem4882364 A P t h1)). Qed.
Lemma lem4882554 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term598 A P t' f u) (h3 : term352 A u f s t) : False.
Proof. exact (@lem4882551 A P t h1 (@lem4882543 A P t' u f s t h2 h3)). Qed.
Lemma lem4882555 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term598 A P t' f u) (h3 : term352 A u f s t) : term911.
Proof. exact (fun h0 : ~ False => @lem4882554 A P t' u f s t h1 h2 h3). Qed.
Lemma lem4882557 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4882558 : term911 = False.
Proof. exact (@lem4882557 False). Qed.
Lemma lem4882559 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term598 A P t' f u) (h3 : term352 A u f s t) : False.
Proof. exact (EQ_MP (@lem4882558) (@lem4882555 A P t' u f s t h1 h2 h3)). Qed.
Lemma lem4882560 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : False.
Proof. exact (ex_elim (@lem4881659 A P f u h2) (fun t' : type667 A => fun h0 : term600 A P f u t' => @lem4882559 A P t' u f s t h1 h0 h3)). Qed.
Lemma lem4882561 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : (term381 A P t) = False.
Proof. exact (prop_ext (fun h4 : term381 A P t => @lem4882560 A P u f s t h1 h2 h3) (fun h4 : False => @lem4881675 A P t h1)). Qed.
Lemma lem4882562 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : False.
Proof. exact (EQ_MP (@lem4882561 A P u f s t h1 h2 h3) (@lem4881675 A P t h1)). Qed.
Lemma lem4882563 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : (term352 A u f s t) = False.
Proof. exact (prop_ext (fun h4 : term352 A u f s t => @lem4882562 A P u f s t h1 h2 h3) (fun h4 : False => @lem4881669 A u f s t h3)). Qed.
Lemma lem4882564 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : False.
Proof. exact (EQ_MP (@lem4882563 A P u f s t h1 h2 h3) (@lem4881669 A u f s t h3)). Qed.
Lemma lem4882565 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : (term381 A P t) = False.
Proof. exact (prop_ext (fun h4 : term381 A P t => @lem4882564 A P u f s t h1 h2 h3) (fun h4 : False => @lem4881022 A P t h1)). Qed.
Lemma lem4882566 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term381 A P t) (h2 : term348 A P f u) (h3 : term352 A u f s t) : False.
Proof. exact (EQ_MP (@lem4882565 A P u f s t h1 h2 h3) (@lem4881022 A P t h1)). Qed.
Lemma lem4882567 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term348 A P f u) (h2 : term352 A u f s t) : term380 A P t.
Proof. exact (fun h0 : term381 A P t => @lem4882566 A P u f s t h0 h1 h2). Qed.
Lemma lem4882568 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term348 A P f u) (h2 : term352 A u f s t) : P t.
Proof. exact (EQ_MP (@lem4881021 A P t) (@lem4882567 A P u f s t h1 h2)). Qed.
Lemma lem4882569 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term354 A u f s P t.
Proof. exact (fun h0 : term352 A u f s t => @lem4882568 A P u f s t h1 h0). Qed.
Lemma lem4882574 {A : Type'} (s : A -> Prop) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term356 A u f s P.
Proof. exact (fun t : A -> Prop => @lem4882569 A s t P f u h1). Qed.
Lemma lem4882579 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term358 A u f P.
Proof. exact (fun s : A -> Prop => @lem4882574 A s P f u h1). Qed.
Lemma lem4882580 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term359 A u f P.
Proof. exact (fun h0 : term348 A P f u => @lem4882579 A P f u h0). Qed.
Lemma lem4882585 {A : Type'} (f : type639 A) (P : type686 A) : term371 A f P.
Proof. exact (fun u : type686 A => @lem4882580 A u f P). Qed.
Lemma lem4882590 {A : Type'} (P : type686 A) : term375 A P.
Proof. exact (fun f : type639 A => @lem4882585 A f P). Qed.
Lemma lem4882595 {A : Type'} : term379 A.
Proof. exact (fun P : type686 A => @lem4882590 A P). Qed.
Lemma lem4882596 {A : Type'} : term378 A.
Proof. exact (EQ_MP (@lem4881015 A) (@lem4882595 A)). Qed.
Lemma lem4882597 {A : Type'} (P : type686 A) : term912 A P.
Proof. exact (@lem4882596 A P). Qed.
Lemma lem4882598 {A : Type'} (P : type686 A) : (term912 A P) = (term374 A P).
Proof. exact (eq_refl (term912 A P)). Qed.
Lemma lem4882599 {A : Type'} (P : type686 A) : term374 A P.
Proof. exact (EQ_MP (@lem4882598 A P) (@lem4882597 A P)). Qed.
Lemma lem4882600 {A : Type'} (P : type686 A) (f : type639 A) : term913 A P f.
Proof. exact (@lem4882599 A P f). Qed.
Lemma lem4882601 {A : Type'} (f : type639 A) (P : type686 A) : (term913 A P f) = (term370 A f P).
Proof. exact (eq_refl (term913 A P f)). Qed.
Lemma lem4882602 {A : Type'} (f : type639 A) (P : type686 A) : term370 A f P.
Proof. exact (EQ_MP (@lem4882601 A f P) (@lem4882600 A P f)). Qed.
Lemma lem4882603 {A : Type'} (f : type639 A) (P : type686 A) (u : type686 A) : term914 A f P u.
Proof. exact (@lem4882602 A f P u). Qed.
Lemma lem4882604 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term914 A f P u) = (term361 A u f P).
Proof. exact (eq_refl (term914 A f P u)). Qed.
Lemma lem4882605 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term361 A u f P.
Proof. exact (EQ_MP (@lem4882604 A u f P) (@lem4882603 A f P u)). Qed.
Lemma lem4882607 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term361 A u f P.
Proof. exact (@lem4880741 A u f P (@lem4882605 A u f P)). Qed.
Lemma lem4882608 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term362 A u f P) : False.
Proof. exact (@lem4882607 A u f P (@lem4880725 A u f P h1)). Qed.
Lemma lem4882609 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term362 A u f P) : (term362 A u f P) = False.
Proof. exact (prop_ext (fun h2 : term362 A u f P => @lem4882608 A u f P h1) (fun h2 : False => @lem4880725 A u f P h1)). Qed.
Lemma lem4882610 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term362 A u f P) : False.
Proof. exact (EQ_MP (@lem4882609 A u f P h1) (@lem4880725 A u f P h1)). Qed.
Lemma lem4882611 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term361 A u f P.
Proof. exact (fun h0 : term362 A u f P => @lem4882610 A u f P h0). Qed.
Lemma lem4882612 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term359 A u f P.
Proof. exact (EQ_MP (@lem4880724 A u f P) (@lem4882611 A u f P)). Qed.
Lemma lem4882613 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term314 A u f P.
Proof. exact (EQ_MP (@lem4880720 A u f P) (@lem4882612 A u f P)). Qed.
Lemma lem4882614 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term313 A u f P.
Proof. exact (EQ_MP (@lem4880548 A u f P) (@lem4882613 A u f P)). Qed.
Lemma lem4882615 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term291 A u f P.
Proof. exact (@lem4882614 A u f P (@lem4880470 A P f u h1 h2)). Qed.
Lemma lem4882619 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term10 _89422 _89438 f s) = (term11 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem4879415 _89422 _89438 s f) (@lem4879414 _89422 _89438 f s)). Qed.
Lemma lem4882620 {A : Type'} (s : type1171 A) (f : type1170 A) : (term915 A f s) = (term916 A s f).
Proof. exact (@lem4882619 A (type1643 A) s f). Qed.
Lemma lem4882621 {A : Type'} (u : type686 A) (f : type639 A) : (term294 A u f) = (term917 A u f).
Proof. exact (@lem4882620 A (term199 A u f) (@snd (A -> Prop) (A -> Prop))). Qed.
Lemma lem4882642 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4882643 {A : Type'} (u : type686 A) (f : type639 A) : (term918 A u f) = (term919 A u f).
Proof. exact (MK_COMB (@lem4882642 A) (@lem4882621 A u f)). Qed.
Lemma lem4882644 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4882645 {A : Type'} (f : type639 A) (u : type686 A) : ((term294 A u f) = (@UNIONS A u)) = ((term917 A u f) = (@UNIONS A u)).
Proof. exact (MK_COMB (@lem4882643 A u f) (@lem4882644 A u)). Qed.
Lemma lem4882648 {A : Type'} (f : type639 A) (u : type686 A) : ((term917 A u f) = (@UNIONS A u)) = ((term294 A u f) = (@UNIONS A u)).
Proof. exact (SYM (@lem4882645 A f u)). Qed.
Lemma lem4882656 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term5 _89212 _89213 _89357 P f Q) = (term6 _89212 _89213 _89357 P Q f).
Proof. exact (EQ_MP (@lem4879402 _89212 _89213 _89357 P Q f) (@lem4879401 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem4882657 {A : Type'} (P : type639 A) (Q : type1171 A) (f : type637 A) : (term920 A P f Q) = (term921 A P Q f).
Proof. exact (@lem4882656 (A -> Prop) (A -> Prop) (type1643 A) P Q f). Qed.
Lemma lem4882658 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term922 A u f y) = (term923 A u f y).
Proof. exact (@lem4882657 A (term238 A u f) (term924 A y) (@pair (A -> Prop) (A -> Prop))). Qed.
Lemma lem4882659 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term240 A u f s) = (term241 A u f s).
Proof. exact (eq_refl (term240 A u f s)). Qed.
Lemma lem4882660 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4882661 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term242 A u f s t) = (term243 A u f s t).
Proof. exact (MK_COMB (@lem4882659 A u f s) (@lem4882660 A t)). Qed.
Lemma lem4882662 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term243 A u f s t) = (term244 A u t f s).
Proof. exact (eq_refl (term243 A u f s t)). Qed.
Lemma lem4882663 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term242 A u f s t) = (term244 A u t f s).
Proof. exact (TRANS (@lem4882661 A u f s t) (@lem4882662 A u t f s)). Qed.
Lemma lem4882664 {A : Type'} (GEN_PVAR_214 : type1643 A) : (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214) = (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214).
Proof. exact (eq_refl (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_214)). Qed.
Lemma lem4882665 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term245 A GEN_PVAR_214 u f s t) = (term246 A GEN_PVAR_214 u t f s).
Proof. exact (MK_COMB (@lem4882664 A GEN_PVAR_214) (@lem4882663 A u t f s)). Qed.
Lemma lem4882666 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@pair (A -> Prop) (A -> Prop) s t) = (@pair (A -> Prop) (A -> Prop) s t).
Proof. exact (eq_refl (@pair (A -> Prop) (A -> Prop) s t)). Qed.
Lemma lem4882667 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term247 A GEN_PVAR_214 u f s t) = (term248 A GEN_PVAR_214 u f s t).
Proof. exact (MK_COMB (@lem4882665 A GEN_PVAR_214 u t f s) (@lem4882666 A s t)). Qed.
Lemma lem4882668 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term249 A GEN_PVAR_214 u f s) = (term250 A GEN_PVAR_214 u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882667 A GEN_PVAR_214 u f s t)). Qed.
Lemma lem4882669 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882670 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term251 A GEN_PVAR_214 u f s) = (term252 A GEN_PVAR_214 u f s).
Proof. exact (MK_COMB (@lem4882669 A) (@lem4882668 A GEN_PVAR_214 u f s)). Qed.
Lemma lem4882671 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) : (term253 A GEN_PVAR_214 u f) = (term254 A GEN_PVAR_214 u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4882670 A GEN_PVAR_214 u f s)). Qed.
Lemma lem4882672 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882673 {A : Type'} (GEN_PVAR_214 : type1643 A) (u : type686 A) (f : type639 A) : (term255 A GEN_PVAR_214 u f) = (term256 A GEN_PVAR_214 u f).
Proof. exact (MK_COMB (@lem4882672 A) (@lem4882671 A GEN_PVAR_214 u f)). Qed.
Lemma lem4882674 {A : Type'} (u : type686 A) (f : type639 A) : (term257 A u f) = (term258 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_214 : type1643 A => @lem4882673 A GEN_PVAR_214 u f)). Qed.
Lemma lem4882675 {A : Type'} : (@GSPEC (prod (A -> Prop) (A -> Prop))) = (@GSPEC (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@GSPEC (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4882676 {A : Type'} (u : type686 A) (f : type639 A) : (term259 A u f) = (term199 A u f).
Proof. exact (MK_COMB (@lem4882675 A) (@lem4882674 A u f)). Qed.
Lemma lem4882677 {A : Type'} (x : type1643 A) : (@IN (prod (A -> Prop) (A -> Prop)) x) = (@IN (prod (A -> Prop) (A -> Prop)) x).
Proof. exact (eq_refl (@IN (prod (A -> Prop) (A -> Prop)) x)). Qed.
Lemma lem4882678 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term260 A x u f) = (term261 A x u f).
Proof. exact (MK_COMB (@lem4882677 A x) (@lem4882676 A u f)). Qed.
Lemma lem4882679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882680 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term925 A x u f) = (term926 A x u f).
Proof. exact (MK_COMB (@lem4882679) (@lem4882678 A x u f)). Qed.
Lemma lem4882681 {A : Type'} (y : A) (x : type1643 A) : (term927 A y x) = (term928 A y x).
Proof. exact (eq_refl (term927 A y x)). Qed.
Lemma lem4882682 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (x : type1643 A) : (term929 A u f y x) = (term930 A u f y x).
Proof. exact (MK_COMB (@lem4882680 A x u f) (@lem4882681 A y x)). Qed.
Lemma lem4882683 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term931 A u f y) = (term932 A u f y).
Proof. exact (fun_ext (fun x : type1643 A => @lem4882682 A u f y x)). Qed.
Lemma lem4882684 {A : Type'} : (@ex (prod (A -> Prop) (A -> Prop))) = (@ex (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@ex (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4882685 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term922 A u f y) = (term933 A u f y).
Proof. exact (MK_COMB (@lem4882684 A) (@lem4882683 A u f y)). Qed.
Lemma lem4882686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882687 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term934 A u f y) = (term935 A u f y).
Proof. exact (MK_COMB (@lem4882686) (@lem4882685 A u f y)). Qed.
Lemma lem4882688 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term240 A u f s) = (term241 A u f s).
Proof. exact (eq_refl (term240 A u f s)). Qed.
Lemma lem4882689 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4882690 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term242 A u f s t) = (term243 A u f s t).
Proof. exact (MK_COMB (@lem4882688 A u f s) (@lem4882689 A t)). Qed.
Lemma lem4882691 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term243 A u f s t) = (term244 A u t f s).
Proof. exact (eq_refl (term243 A u f s t)). Qed.
Lemma lem4882692 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term242 A u f s t) = (term244 A u t f s).
Proof. exact (TRANS (@lem4882690 A u f s t) (@lem4882691 A u t f s)). Qed.
Lemma lem4882693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882694 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term936 A u f s t) = (term937 A u t f s).
Proof. exact (MK_COMB (@lem4882693) (@lem4882692 A u t f s)). Qed.
Lemma lem4882695 {A : Type'} (y : A) (s : A -> Prop) (t : A -> Prop) : (term938 A y s t) = (term939 A y s t).
Proof. exact (eq_refl (term938 A y s t)). Qed.
Lemma lem4882696 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) (t : A -> Prop) : (term940 A u f y s t) = (term941 A u f y s t).
Proof. exact (MK_COMB (@lem4882694 A u t f s) (@lem4882695 A y s t)). Qed.
Lemma lem4882697 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) : (term942 A u f y s) = (term943 A u f y s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882696 A u f y s t)). Qed.
Lemma lem4882698 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882699 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) : (term944 A u f y s) = (term945 A u f y s).
Proof. exact (MK_COMB (@lem4882698 A) (@lem4882697 A u f y s)). Qed.
Lemma lem4882700 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term946 A u f y) = (term947 A u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4882699 A u f y s)). Qed.
Lemma lem4882701 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882702 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term923 A u f y) = (term948 A u f y).
Proof. exact (MK_COMB (@lem4882701 A) (@lem4882700 A u f y)). Qed.
Lemma lem4882703 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : ((term922 A u f y) = (term923 A u f y)) = ((term933 A u f y) = (term948 A u f y)).
Proof. exact (MK_COMB (@lem4882687 A u f y) (@lem4882702 A u f y)). Qed.
Lemma lem4882704 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term933 A u f y) = (term948 A u f y).
Proof. exact (EQ_MP (@lem4882703 A u f y) (@lem4882658 A u f y)). Qed.
Lemma lem4882718 {A B : Type'} (x : A) (y : B) : (term285 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4882719 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term286 A x y) = y.
Proof. exact (@lem4882718 (A -> Prop) (A -> Prop) x y). Qed.
Lemma lem4882720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term286 A s t) = t.
Proof. exact (@lem4882719 A s t). Qed.
Lemma lem4882721 {A : Type'} (y : A) : (@IN A y) = (@IN A y).
Proof. exact (eq_refl (@IN A y)). Qed.
Lemma lem4882722 {A : Type'} (s : A -> Prop) (y : A) (t : A -> Prop) : (term939 A y s t) = (@IN A y t).
Proof. exact (MK_COMB (@lem4882721 A y) (@lem4882720 A s t)). Qed.
Lemma lem4882723 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term937 A u t f s) = (term937 A u t f s).
Proof. exact (eq_refl (term937 A u t f s)). Qed.
Lemma lem4882724 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) (t : A -> Prop) : (term941 A u f y s t) = (term949 A u f s y t).
Proof. exact (MK_COMB (@lem4882723 A u t f s) (@lem4882722 A s y t)). Qed.
Lemma lem4882727 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) : (term943 A u f y s) = (term950 A u f s y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882724 A u f s y t)). Qed.
Lemma lem4882728 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882729 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) : (term945 A u f y s) = (term951 A u f s y).
Proof. exact (MK_COMB (@lem4882728 A) (@lem4882727 A u f s y)). Qed.
Lemma lem4882734 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term947 A u f y) = (term952 A u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4882729 A u f s y)). Qed.
Lemma lem4882735 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882736 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term948 A u f y) = (term953 A u f y).
Proof. exact (MK_COMB (@lem4882735 A) (@lem4882734 A u f y)). Qed.
Lemma lem4882741 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term933 A u f y) = (term953 A u f y).
Proof. exact (TRANS (@lem4882704 A u f y) (@lem4882736 A u f y)). Qed.
Lemma lem4882742 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4882743 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term954 A GEN_PVAR_47 u f y) = (term955 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4882742 A GEN_PVAR_47) (@lem4882741 A u f y)). Qed.
Lemma lem4882744 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4882745 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term956 A GEN_PVAR_47 u f y) = (term957 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4882743 A GEN_PVAR_47 u f y) (@lem4882744 A y)). Qed.
Lemma lem4882746 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term958 A GEN_PVAR_47 u f) = (term959 A GEN_PVAR_47 u f).
Proof. exact (fun_ext (fun y : A => @lem4882745 A GEN_PVAR_47 u f y)). Qed.
Lemma lem4882747 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4882748 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term960 A GEN_PVAR_47 u f) = (term961 A GEN_PVAR_47 u f).
Proof. exact (MK_COMB (@lem4882747 A) (@lem4882746 A GEN_PVAR_47 u f)). Qed.
Lemma lem4882753 {A : Type'} (u : type686 A) (f : type639 A) : (term962 A u f) = (term963 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4882748 A GEN_PVAR_47 u f)). Qed.
Lemma lem4882754 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4882755 {A : Type'} (u : type686 A) (f : type639 A) : (term917 A u f) = (term964 A u f).
Proof. exact (MK_COMB (@lem4882754 A) (@lem4882753 A u f)). Qed.
Lemma lem4882756 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4882757 {A : Type'} (u : type686 A) (f : type639 A) : (term919 A u f) = (term965 A u f).
Proof. exact (MK_COMB (@lem4882756 A) (@lem4882755 A u f)). Qed.
Lemma lem4882758 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4882759 {A : Type'} (f : type639 A) (u : type686 A) : ((term917 A u f) = (@UNIONS A u)) = ((term964 A u f) = (@UNIONS A u)).
Proof. exact (MK_COMB (@lem4882757 A u f) (@lem4882758 A u)). Qed.
Lemma lem4882762 {A : Type'} (f : type639 A) (u : type686 A) : ((term964 A u f) = (@UNIONS A u)) = ((term917 A u f) = (@UNIONS A u)).
Proof. exact (SYM (@lem4882759 A f u)). Qed.
Lemma lem4882763 (t1 : Prop) : term966 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4882764 (t1 : Prop) : (term966 t1) = (term967 t1).
Proof. exact (eq_refl (term966 t1)). Qed.
Lemma lem4882765 (t1 : Prop) : term967 t1.
Proof. exact (EQ_MP (@lem4882764 t1) (@lem4882763 t1)). Qed.
Lemma lem4882766 (t1 : Prop) (t2 : Prop) : term968 t1 t2.
Proof. exact (@lem4882765 t1 t2). Qed.
Lemma lem4882767 (t1 : Prop) (t2 : Prop) : (term968 t1 t2) = (term969 t1 t2).
Proof. exact (eq_refl (term968 t1 t2)). Qed.
Lemma lem4882768 (t1 : Prop) (t2 : Prop) : term969 t1 t2.
Proof. exact (EQ_MP (@lem4882767 t1 t2) (@lem4882766 t1 t2)). Qed.
Lemma lem4882769 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term970 t1 t2 t3.
Proof. exact (@lem4882768 t1 t2 t3). Qed.
Lemma lem4882770 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term970 t1 t2 t3) = ((term893 t1 t2 t3) = (term971 t1 t2 t3)).
Proof. exact (eq_refl (term970 t1 t2 t3)). Qed.
Lemma lem4882771 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term893 t1 t2 t3) = (term971 t1 t2 t3).
Proof. exact (EQ_MP (@lem4882770 t1 t2 t3) (@lem4882769 t1 t2 t3)). Qed.
Lemma lem4882772 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term971 t1 t2 t3) = (term893 t1 t2 t3).
Proof. exact (SYM (@lem4882771 t1 t2 t3)). Qed.
Lemma lem4882773 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term296 A P f u.
Proof. exact (conj (@lem4879994 A u P f h1) (@lem4879808 A u h2)). Qed.
Lemma lem4882797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4882798 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (@lem4882797 A s t). Qed.
Lemma lem4882799 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term298 A f c) = c) = (term299 A f c).
Proof. exact (@lem4882798 A (term298 A f c) c). Qed.
Lemma lem4882808 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term300 A f c P) = (term300 A f c P).
Proof. exact (eq_refl (term300 A f c P)). Qed.
Lemma lem4882809 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4882808 A f c P) (@lem4882799 A f c)). Qed.
Lemma lem4882812 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4882813 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term194 A P f c) = (term304 A P f c).
Proof. exact (MK_COMB (@lem4882812 A f c) (@lem4882809 A P f c)). Qed.
Lemma lem4882816 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4882817 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term153 A u P f c) = (term305 A u P f c).
Proof. exact (MK_COMB (@lem4882816 A c u) (@lem4882813 A P f c)). Qed.
Lemma lem4882820 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term155 A u P f) = (term306 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4882817 A u P f c)). Qed.
Lemma lem4882821 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882822 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term157 A u P f) = (term307 A u P f).
Proof. exact (MK_COMB (@lem4882821 A) (@lem4882820 A u P f)). Qed.
Lemma lem4882827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882828 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term308 A u P f) = (term309 A u P f).
Proof. exact (MK_COMB (@lem4882827) (@lem4882822 A u P f)). Qed.
Lemma lem4882829 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4882830 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term296 A P f u) = (term310 A P f u).
Proof. exact (MK_COMB (@lem4882828 A u P f) (@lem4882829 A u)). Qed.
Lemma lem4882833 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4882834 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term311 A P f u) = (term312 A P f u).
Proof. exact (MK_COMB (@lem4882833) (@lem4882830 A P f u)). Qed.
Lemma lem4882838 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4882839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term297 A s t).
Proof. exact (@lem4882838 A s t). Qed.
Lemma lem4882840 {A : Type'} (f : type639 A) (u : type686 A) : ((term964 A u f) = (@UNIONS A u)) = (term972 A f u).
Proof. exact (@lem4882839 A (term964 A u f) (@UNIONS A u)). Qed.
Lemma lem4882865 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term973 A P f u) = (term974 A P f u).
Proof. exact (MK_COMB (@lem4882834 A P f u) (@lem4882840 A f u)). Qed.
Lemma lem4882868 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term974 A P f u) = (term973 A P f u).
Proof. exact (SYM (@lem4882865 A P f u)). Qed.
Lemma lem4882880 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4882881 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4882880 (A -> Prop) P x). Qed.
Lemma lem4882882 {A : Type'} (u : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c u) = (u c).
Proof. exact (@lem4882881 A u c). Qed.
Lemma lem4882883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4882884 {A : Type'} (u : type686 A) (c : A -> Prop) : (term63 A c u) = (term315 A u c).
Proof. exact (MK_COMB (@lem4882883) (@lem4882882 A u c)). Qed.
Lemma lem4882896 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4882897 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4882896 (A -> Prop) P x). Qed.
Lemma lem4882898 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term316 A c' f c) = (f c c').
Proof. exact (@lem4882897 A (f c) c'). Qed.
Lemma lem4882899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4882900 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term317 A c' f c) = (term318 A f c c').
Proof. exact (MK_COMB (@lem4882899) (@lem4882898 A f c c')). Qed.
Lemma lem4882901 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (P c').
Proof. exact (eq_refl (P c')). Qed.
Lemma lem4882902 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term319 A f c P c') = (term320 A f c P c').
Proof. exact (MK_COMB (@lem4882900 A f c c') (@lem4882901 A P c')). Qed.
Lemma lem4882905 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term321 A f c P) = (term322 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4882902 A f c P c')). Qed.
Lemma lem4882906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882907 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term323 A f c P) = (term324 A f c P).
Proof. exact (MK_COMB (@lem4882906 A) (@lem4882905 A f c P)). Qed.
Lemma lem4882912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882913 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term300 A f c P) = (term325 A f c P).
Proof. exact (MK_COMB (@lem4882912) (@lem4882907 A f c P)). Qed.
Lemma lem4882921 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4882922 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (@lem4882921 A s x). Qed.
Lemma lem4882923 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term328 A x f c) = (term329 A f c x).
Proof. exact (@lem4882922 A (f c) x). Qed.
Lemma lem4882931 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4882932 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4882931 (A -> Prop) P x). Qed.
Lemma lem4882933 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term316 A t f c) = (f c t).
Proof. exact (@lem4882932 A (f c) t). Qed.
Lemma lem4882934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882935 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term330 A t f c) = (term331 A f c t).
Proof. exact (MK_COMB (@lem4882934) (@lem4882933 A f c t)). Qed.
Lemma lem4882937 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4882938 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4882937 A P x). Qed.
Lemma lem4882939 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4882938 A t x). Qed.
Lemma lem4882940 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term332 A f c x t) = (term333 A f c t x).
Proof. exact (MK_COMB (@lem4882935 A f c t) (@lem4882939 A t x)). Qed.
Lemma lem4882943 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term334 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4882940 A f c t x)). Qed.
Lemma lem4882944 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4882945 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term329 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4882944 A) (@lem4882943 A f c x)). Qed.
Lemma lem4882950 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term328 A x f c) = (term336 A f c x).
Proof. exact (TRANS (@lem4882923 A f c x) (@lem4882945 A f c x)). Qed.
Lemma lem4882951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4882952 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term337 A x f c) = (term338 A f c x).
Proof. exact (MK_COMB (@lem4882951) (@lem4882950 A f c x)). Qed.
Lemma lem4882954 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4882955 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4882954 A P x). Qed.
Lemma lem4882956 {A : Type'} (c : A -> Prop) (x : A) : (@IN A x c) = (c x).
Proof. exact (@lem4882955 A c x). Qed.
Lemma lem4882957 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term328 A x f c) = (@IN A x c)) = ((term336 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4882952 A f c x) (@lem4882956 A c x)). Qed.
Lemma lem4882960 {A : Type'} (f : type639 A) (c : A -> Prop) : (term339 A f c) = (term340 A f c).
Proof. exact (fun_ext (fun x : A => @lem4882957 A f c x)). Qed.
Lemma lem4882961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4882962 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term341 A f c).
Proof. exact (MK_COMB (@lem4882961 A) (@lem4882960 A f c)). Qed.
Lemma lem4882967 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term342 A P f c).
Proof. exact (MK_COMB (@lem4882913 A f c P) (@lem4882962 A f c)). Qed.
Lemma lem4882970 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4882971 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term304 A P f c) = (term343 A P f c).
Proof. exact (MK_COMB (@lem4882970 A f c) (@lem4882967 A P f c)). Qed.
Lemma lem4882974 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term305 A u P f c) = (term344 A u P f c).
Proof. exact (MK_COMB (@lem4882884 A u c) (@lem4882971 A P f c)). Qed.
Lemma lem4882977 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term345 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4882974 A u P f c)). Qed.
Lemma lem4882978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4882979 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term307 A u P f) = (term346 A u P f).
Proof. exact (MK_COMB (@lem4882978 A) (@lem4882977 A u P f)). Qed.
Lemma lem4882984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4882985 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term309 A u P f) = (term347 A u P f).
Proof. exact (MK_COMB (@lem4882984) (@lem4882979 A u P f)). Qed.
Lemma lem4882986 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4882987 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term310 A P f u) = (term348 A P f u).
Proof. exact (MK_COMB (@lem4882985 A u P f) (@lem4882986 A u)). Qed.
Lemma lem4882990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4882991 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term312 A P f u) = (term349 A P f u).
Proof. exact (MK_COMB (@lem4882990) (@lem4882987 A P f u)). Qed.
Lemma lem4882999 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term975 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4883000 {A : Type'} (p : A -> Prop) (x : A) : (term975 A x p) = (p x).
Proof. exact (@lem4882999 A p x). Qed.
Lemma lem4883001 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term976 A x u f) = (term977 A u f x).
Proof. exact (@lem4883000 A (term978 A u f) x). Qed.
Lemma lem4883002 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term977 A u f y) = (term953 A u f y).
Proof. exact (eq_refl (term977 A u f y)). Qed.
Lemma lem4883003 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4883004 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term979 A GEN_PVAR_47 u f y) = (term955 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4883003 A GEN_PVAR_47) (@lem4883002 A u f y)). Qed.
Lemma lem4883005 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4883006 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term980 A GEN_PVAR_47 u f y) = (term957 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4883004 A GEN_PVAR_47 u f y) (@lem4883005 A y)). Qed.
Lemma lem4883007 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term981 A GEN_PVAR_47 u f) = (term959 A GEN_PVAR_47 u f).
Proof. exact (fun_ext (fun y : A => @lem4883006 A GEN_PVAR_47 u f y)). Qed.
Lemma lem4883008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4883009 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term982 A GEN_PVAR_47 u f) = (term961 A GEN_PVAR_47 u f).
Proof. exact (MK_COMB (@lem4883008 A) (@lem4883007 A GEN_PVAR_47 u f)). Qed.
Lemma lem4883010 {A : Type'} (u : type686 A) (f : type639 A) : (term983 A u f) = (term963 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4883009 A GEN_PVAR_47 u f)). Qed.
Lemma lem4883011 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4883012 {A : Type'} (u : type686 A) (f : type639 A) : (term984 A u f) = (term964 A u f).
Proof. exact (MK_COMB (@lem4883011 A) (@lem4883010 A u f)). Qed.
Lemma lem4883013 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4883014 {A : Type'} (x : A) (u : type686 A) (f : type639 A) : (term976 A x u f) = (term985 A x u f).
Proof. exact (MK_COMB (@lem4883013 A x) (@lem4883012 A u f)). Qed.
Lemma lem4883015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883016 {A : Type'} (x : A) (u : type686 A) (f : type639 A) : (term986 A x u f) = (term987 A x u f).
Proof. exact (MK_COMB (@lem4883015) (@lem4883014 A x u f)). Qed.
Lemma lem4883017 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term977 A u f x) = (term953 A u f x).
Proof. exact (eq_refl (term977 A u f x)). Qed.
Lemma lem4883018 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : ((term976 A x u f) = (term977 A u f x)) = ((term985 A x u f) = (term953 A u f x)).
Proof. exact (MK_COMB (@lem4883016 A x u f) (@lem4883017 A u f x)). Qed.
Lemma lem4883019 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term985 A x u f) = (term953 A u f x).
Proof. exact (EQ_MP (@lem4883018 A u f x) (@lem4883001 A u f x)). Qed.
Lemma lem4883033 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4883034 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4883033 (A -> Prop) P x). Qed.
Lemma lem4883035 {A : Type'} (u : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s u) = (u s).
Proof. exact (@lem4883034 A u s). Qed.
Lemma lem4883036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883037 {A : Type'} (u : type686 A) (s : A -> Prop) : (term350 A s u) = (term351 A u s).
Proof. exact (MK_COMB (@lem4883036) (@lem4883035 A u s)). Qed.
Lemma lem4883039 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4883040 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4883039 (A -> Prop) P x). Qed.
Lemma lem4883041 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term316 A t f s) = (f s t).
Proof. exact (@lem4883040 A (f s) t). Qed.
Lemma lem4883042 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term244 A u t f s) = (term352 A u f s t).
Proof. exact (MK_COMB (@lem4883037 A u s) (@lem4883041 A f s t)). Qed.
Lemma lem4883045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883046 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term937 A u t f s) = (term988 A u f s t).
Proof. exact (MK_COMB (@lem4883045) (@lem4883042 A u f s t)). Qed.
Lemma lem4883048 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4883049 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4883048 A P x). Qed.
Lemma lem4883050 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4883049 A t x). Qed.
Lemma lem4883051 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term949 A u f s x t) = (term989 A u f s t x).
Proof. exact (MK_COMB (@lem4883046 A u f s t) (@lem4883050 A t x)). Qed.
Lemma lem4883054 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term950 A u f s x) = (term990 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883051 A u f s t x)). Qed.
Lemma lem4883055 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883056 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term951 A u f s x) = (term991 A u f s x).
Proof. exact (MK_COMB (@lem4883055 A) (@lem4883054 A u f s x)). Qed.
Lemma lem4883061 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term952 A u f x) = (term992 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4883056 A u f s x)). Qed.
Lemma lem4883062 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883063 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term953 A u f x) = (term993 A u f x).
Proof. exact (MK_COMB (@lem4883062 A) (@lem4883061 A u f x)). Qed.
Lemma lem4883068 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term985 A x u f) = (term993 A u f x).
Proof. exact (TRANS (@lem4883019 A u f x) (@lem4883063 A u f x)). Qed.
Lemma lem4883069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883070 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term987 A x u f) = (term994 A u f x).
Proof. exact (MK_COMB (@lem4883069) (@lem4883068 A u f x)). Qed.
Lemma lem4883072 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4883073 {A : Type'} (s : type686 A) (x : A) : (term326 A x s) = (term327 A s x).
Proof. exact (@lem4883072 A s x). Qed.
Lemma lem4883074 {A : Type'} (u : type686 A) (x : A) : (term326 A x u) = (term327 A u x).
Proof. exact (@lem4883073 A u x). Qed.
Lemma lem4883082 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4883083 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4883082 (A -> Prop) P x). Qed.
Lemma lem4883084 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem4883083 A u t). Qed.
Lemma lem4883085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883086 {A : Type'} (u : type686 A) (t : A -> Prop) : (term350 A t u) = (term351 A u t).
Proof. exact (MK_COMB (@lem4883085) (@lem4883084 A u t)). Qed.
Lemma lem4883088 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4883089 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4883088 A P x). Qed.
Lemma lem4883090 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4883089 A t x). Qed.
Lemma lem4883091 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term995 A u x t) = (term996 A u t x).
Proof. exact (MK_COMB (@lem4883086 A u t) (@lem4883090 A t x)). Qed.
Lemma lem4883094 {A : Type'} (u : type686 A) (x : A) : (term997 A u x) = (term998 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883091 A u t x)). Qed.
Lemma lem4883095 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883096 {A : Type'} (u : type686 A) (x : A) : (term327 A u x) = (term999 A u x).
Proof. exact (MK_COMB (@lem4883095 A) (@lem4883094 A u x)). Qed.
Lemma lem4883101 {A : Type'} (u : type686 A) (x : A) : (term326 A x u) = (term999 A u x).
Proof. exact (TRANS (@lem4883074 A u x) (@lem4883096 A u x)). Qed.
Lemma lem4883102 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term985 A x u f) = (term326 A x u)) = ((term993 A u f x) = (term999 A u x)).
Proof. exact (MK_COMB (@lem4883070 A u f x) (@lem4883101 A u x)). Qed.
Lemma lem4883105 {A : Type'} (f : type639 A) (u : type686 A) : (term1000 A f u) = (term1001 A f u).
Proof. exact (fun_ext (fun x : A => @lem4883102 A f u x)). Qed.
Lemma lem4883106 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883107 {A : Type'} (f : type639 A) (u : type686 A) : (term972 A f u) = (term1002 A f u).
Proof. exact (MK_COMB (@lem4883106 A) (@lem4883105 A f u)). Qed.
Lemma lem4883112 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term974 A P f u) = (term1003 A P f u).
Proof. exact (MK_COMB (@lem4882991 A P f u) (@lem4883107 A f u)). Qed.
Lemma lem4883115 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1003 A P f u) = (term974 A P f u).
Proof. exact (SYM (@lem4883112 A P f u)). Qed.
Lemma lem4883117 (p : Prop) : p = (term360 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4883118 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1003 A P f u) = (term1004 A P f u).
Proof. exact (@lem4883117 (term1003 A P f u)). Qed.
Lemma lem4883119 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1004 A P f u) = (term1003 A P f u).
Proof. exact (SYM (@lem4883118 A P f u)). Qed.
Lemma lem4883120 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1005 A P f u) : term1005 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883123 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1004 A P f u) : term1004 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883124 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1006 A P f u.
Proof. exact (fun h0 : term1004 A P f u => @lem4883123 A P f u h0). Qed.
Lemma lem4883125 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1006 A P f u) : term1006 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883126 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1004 A P f u) : term1004 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883127 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1004 A P f u) (h2 : term1006 A P f u) : term1004 A P f u.
Proof. exact (@lem4883125 A P f u h2 (@lem4883126 A P f u h1)). Qed.
Lemma lem4883128 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1004 A P f u) : term1007 A P f u.
Proof. exact (fun h0 : term1006 A P f u => @lem4883127 A P f u h1 h0). Qed.
Lemma lem4883129 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1006 A P f u) : term1006 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883130 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1004 A P f u) (h2 : term1006 A P f u) : term1004 A P f u.
Proof. exact (@lem4883128 A P f u h1 (@lem4883129 A P f u h2)). Qed.
Lemma lem4883131 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1006 A P f u) : term1006 A P f u.
Proof. exact (fun h0 : term1004 A P f u => @lem4883130 A P f u h0 h1). Qed.
Lemma lem4883132 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1008 A P f u.
Proof. exact (fun h0 : term1006 A P f u => @lem4883131 A P f u h0). Qed.
Lemma lem4883135 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1006 A P f u.
Proof. exact (@lem4883132 A P f u (@lem4883124 A P f u)). Qed.
Lemma lem4883136 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1006 A P f u.
Proof. exact (@lem4883135 A P f u). Qed.
Lemma lem4883150 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4883151 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1004 A P f u) = (term1009 A P f u).
Proof. exact (@lem4883150 (term1005 A P f u)). Qed.
Lemma lem4883153 (t : Prop) : (term367 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4883154 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1009 A P f u) = (term1003 A P f u).
Proof. exact (@lem4883153 (term1003 A P f u)). Qed.
Lemma lem4883157 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1004 A P f u) = (term1003 A P f u).
Proof. exact (TRANS (@lem4883151 A P f u) (@lem4883154 A P f u)). Qed.
Lemma lem4883320 {A : Type'} (f : type639 A) (u : type686 A) : (term1010 A f u) = (term1011 A f u).
Proof. exact (fun_ext (fun P : type686 A => @lem4883157 A P f u)). Qed.
Lemma lem4883321 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4883322 {A : Type'} (f : type639 A) (u : type686 A) : (term1012 A f u) = (term1013 A f u).
Proof. exact (MK_COMB (@lem4883321 A) (@lem4883320 A f u)). Qed.
Lemma lem4883327 {A : Type'} (u : type686 A) : (term1014 A u) = (term1015 A u).
Proof. exact (fun_ext (fun f : type639 A => @lem4883322 A f u)). Qed.
Lemma lem4883328 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4883329 {A : Type'} (u : type686 A) : (term1016 A u) = (term1017 A u).
Proof. exact (MK_COMB (@lem4883328 A) (@lem4883327 A u)). Qed.
Lemma lem4883334 {A : Type'} : (term1018 A) = (term1019 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4883329 A u)). Qed.
Lemma lem4883335 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4883344 {A : Type'} : (term1020 A) = (term1021 A).
Proof. exact (MK_COMB (@lem4883335 A) (@lem4883334 A)). Qed.
Lemma lem4883349 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term996 A u t x) = (term996 A u t x).
Proof. exact (eq_refl (term996 A u t x)). Qed.
Lemma lem4883350 {A : Type'} (u : type686 A) (x : A) : (term998 A u x) = (term998 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883349 A u t x)). Qed.
Lemma lem4883351 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883352 {A : Type'} (u : type686 A) (x : A) : (term999 A u x) = (term999 A u x).
Proof. exact (MK_COMB (@lem4883351 A) (@lem4883350 A u x)). Qed.
Lemma lem4883361 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term989 A u f s t x) = (term989 A u f s t x).
Proof. exact (eq_refl (term989 A u f s t x)). Qed.
Lemma lem4883362 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term990 A u f s x) = (term990 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883361 A u f s t x)). Qed.
Lemma lem4883363 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883364 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term991 A u f s x) = (term991 A u f s x).
Proof. exact (MK_COMB (@lem4883363 A) (@lem4883362 A u f s x)). Qed.
Lemma lem4883365 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term992 A u f x) = (term992 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4883364 A u f s x)). Qed.
Lemma lem4883366 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883367 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term993 A u f x) = (term993 A u f x).
Proof. exact (MK_COMB (@lem4883366 A) (@lem4883365 A u f x)). Qed.
Lemma lem4883368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883369 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term994 A u f x) = (term994 A u f x).
Proof. exact (MK_COMB (@lem4883368) (@lem4883367 A u f x)). Qed.
Lemma lem4883370 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term993 A u f x) = (term999 A u x)) = ((term993 A u f x) = (term999 A u x)).
Proof. exact (MK_COMB (@lem4883369 A u f x) (@lem4883352 A u x)). Qed.
Lemma lem4883371 {A : Type'} (f : type639 A) (u : type686 A) : (term1001 A f u) = (term1001 A f u).
Proof. exact (fun_ext (fun x : A => @lem4883370 A f u x)). Qed.
Lemma lem4883372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883373 {A : Type'} (f : type639 A) (u : type686 A) : (term1002 A f u) = (term1002 A f u).
Proof. exact (MK_COMB (@lem4883372 A) (@lem4883371 A f u)). Qed.
Lemma lem4883374 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4883375 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4883380 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term333 A f c t x) = (term333 A f c t x).
Proof. exact (eq_refl (term333 A f c t x)). Qed.
Lemma lem4883381 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term335 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883380 A f c t x)). Qed.
Lemma lem4883382 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883383 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term336 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4883382 A) (@lem4883381 A f c x)). Qed.
Lemma lem4883384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883385 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term338 A f c x) = (term338 A f c x).
Proof. exact (MK_COMB (@lem4883384) (@lem4883383 A f c x)). Qed.
Lemma lem4883386 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = ((term336 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4883385 A f c x) (@lem4883375 A c x)). Qed.
Lemma lem4883387 {A : Type'} (f : type639 A) (c : A -> Prop) : (term340 A f c) = (term340 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883386 A f c x)). Qed.
Lemma lem4883388 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883389 {A : Type'} (f : type639 A) (c : A -> Prop) : (term341 A f c) = (term341 A f c).
Proof. exact (MK_COMB (@lem4883388 A) (@lem4883387 A f c)). Qed.
Lemma lem4883394 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term320 A f c P c') = (term320 A f c P c').
Proof. exact (eq_refl (term320 A f c P c')). Qed.
Lemma lem4883395 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term322 A f c P) = (term322 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4883394 A f c P c')). Qed.
Lemma lem4883396 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883397 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term324 A f c P) = (term324 A f c P).
Proof. exact (MK_COMB (@lem4883396 A) (@lem4883395 A f c P)). Qed.
Lemma lem4883398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883399 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term325 A f c P) = (term325 A f c P).
Proof. exact (MK_COMB (@lem4883398) (@lem4883397 A f c P)). Qed.
Lemma lem4883400 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term342 A P f c) = (term342 A P f c).
Proof. exact (MK_COMB (@lem4883399 A f c P) (@lem4883389 A f c)). Qed.
Lemma lem4883403 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4883404 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term343 A P f c) = (term343 A P f c).
Proof. exact (MK_COMB (@lem4883403 A f c) (@lem4883400 A P f c)). Qed.
Lemma lem4883407 {A : Type'} (u : type686 A) (c : A -> Prop) : (term315 A u c) = (term315 A u c).
Proof. exact (eq_refl (term315 A u c)). Qed.
Lemma lem4883408 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term344 A u P f c).
Proof. exact (MK_COMB (@lem4883407 A u c) (@lem4883404 A P f c)). Qed.
Lemma lem4883409 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term345 A u P f) = (term345 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4883408 A u P f c)). Qed.
Lemma lem4883410 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883411 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term346 A u P f) = (term346 A u P f).
Proof. exact (MK_COMB (@lem4883410 A) (@lem4883409 A u P f)). Qed.
Lemma lem4883412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883413 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term347 A u P f) = (term347 A u P f).
Proof. exact (MK_COMB (@lem4883412) (@lem4883411 A u P f)). Qed.
Lemma lem4883414 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term348 A P f u).
Proof. exact (MK_COMB (@lem4883413 A u P f) (@lem4883374 A u)). Qed.
Lemma lem4883415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4883416 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term349 A P f u) = (term349 A P f u).
Proof. exact (MK_COMB (@lem4883415) (@lem4883414 A P f u)). Qed.
Lemma lem4883417 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1003 A P f u) = (term1003 A P f u).
Proof. exact (MK_COMB (@lem4883416 A P f u) (@lem4883373 A f u)). Qed.
Lemma lem4883418 {A : Type'} (f : type639 A) (u : type686 A) : (term1011 A f u) = (term1011 A f u).
Proof. exact (fun_ext (fun P : type686 A => @lem4883417 A P f u)). Qed.
Lemma lem4883419 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4883420 {A : Type'} (f : type639 A) (u : type686 A) : (term1013 A f u) = (term1013 A f u).
Proof. exact (MK_COMB (@lem4883419 A) (@lem4883418 A f u)). Qed.
Lemma lem4883421 {A : Type'} (u : type686 A) : (term1015 A u) = (term1015 A u).
Proof. exact (fun_ext (fun f : type639 A => @lem4883420 A f u)). Qed.
Lemma lem4883422 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4883423 {A : Type'} (u : type686 A) : (term1017 A u) = (term1017 A u).
Proof. exact (MK_COMB (@lem4883422 A) (@lem4883421 A u)). Qed.
Lemma lem4883424 {A : Type'} : (term1019 A) = (term1019 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4883423 A u)). Qed.
Lemma lem4883425 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4883426 {A : Type'} : (term1021 A) = (term1021 A).
Proof. exact (MK_COMB (@lem4883425 A) (@lem4883424 A)). Qed.
Lemma lem4883515 {A : Type'} : (term1020 A) = (term1021 A).
Proof. exact (TRANS (@lem4883344 A) (@lem4883426 A)). Qed.
Lemma lem4883516 {A : Type'} : (term1021 A) = (term1020 A).
Proof. exact (SYM (@lem4883515 A)). Qed.
Lemma lem4883517 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term348 A P f u.
Proof. exact (h1). Qed.
Lemma lem4883519 (p : Prop) : p = (term360 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4883520 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term993 A u f x) = (term999 A u x)) = (term1022 A f u x).
Proof. exact (@lem4883519 ((term993 A u f x) = (term999 A u x))). Qed.
Lemma lem4883521 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1022 A f u x) = ((term993 A u f x) = (term999 A u x)).
Proof. exact (SYM (@lem4883520 A f u x)). Qed.
Lemma lem4883522 {A : Type'} (f : type639 A) (u : type686 A) (x : A) (h1 : term1023 A f u x) : term1023 A f u x.
Proof. exact (h1). Qed.
Lemma lem4883531 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term320 A f c P c') = (term382 A f c P c').
Proof. exact (@lem17265 (f c c') (P c')). Qed.
Lemma lem4883532 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term322 A f c P) = (term383 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4883531 A f c P c')). Qed.
Lemma lem4883533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883534 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term324 A f c P) = (term384 A f c P).
Proof. exact (MK_COMB (@lem4883533 A) (@lem4883532 A f c P)). Qed.
Lemma lem4883543 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term385 A f c t x) = (term386 A f c t x).
Proof. exact (@lem17045 (f c t) (t x)). Qed.
Lemma lem4883546 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term333 A f c t x) = (term333 A f c t x).
Proof. exact (eq_refl (term333 A f c t x)). Qed.
Lemma lem4883547 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4883548 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term389 A f c x) = (term390 A f c x).
Proof. exact (@lem4883547 A (term335 A f c x)). Qed.
Lemma lem4883549 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4883550 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4883551 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term392 A f c x t) = (term385 A f c t x).
Proof. exact (MK_COMB (@lem4883550) (@lem4883549 A f c t x)). Qed.
Lemma lem4883552 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term392 A f c x t) = (term386 A f c t x).
Proof. exact (TRANS (@lem4883551 A f c t x) (@lem4883543 A f c t x)). Qed.
Lemma lem4883553 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term393 A f c x) = (term394 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883552 A f c t x)). Qed.
Lemma lem4883554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883555 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term390 A f c x) = (term395 A f c x).
Proof. exact (MK_COMB (@lem4883554 A) (@lem4883553 A f c x)). Qed.
Lemma lem4883556 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term389 A f c x) = (term395 A f c x).
Proof. exact (TRANS (@lem4883548 A f c x) (@lem4883555 A f c x)). Qed.
Lemma lem4883557 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term335 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883546 A f c t x)). Qed.
Lemma lem4883558 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883559 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term336 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4883558 A) (@lem4883557 A f c x)). Qed.
Lemma lem4883560 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4883561 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4883562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4883563 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term397 A f c x) = (term398 A f c x).
Proof. exact (MK_COMB (@lem4883562) (@lem4883556 A f c x)). Qed.
Lemma lem4883564 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term399 A f c x) = (term400 A f c x).
Proof. exact (MK_COMB (@lem4883563 A f c x) (@lem4883561 A c x)). Qed.
Lemma lem4883565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4883566 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term401 A f c x) = (term401 A f c x).
Proof. exact (MK_COMB (@lem4883565) (@lem4883559 A f c x)). Qed.
Lemma lem4883567 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term402 A f c x) = (term402 A f c x).
Proof. exact (MK_COMB (@lem4883566 A f c x) (@lem4883560 A c x)). Qed.
Lemma lem4883568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883569 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term403 A f c x) = (term403 A f c x).
Proof. exact (MK_COMB (@lem4883568) (@lem4883567 A f c x)). Qed.
Lemma lem4883570 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term404 A f c x) = (term405 A f c x).
Proof. exact (MK_COMB (@lem4883569 A f c x) (@lem4883564 A f c x)). Qed.
Lemma lem4883571 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = (term404 A f c x).
Proof. exact (@lem17784 (term336 A f c x) (c x)). Qed.
Lemma lem4883572 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term336 A f c x) = (c x)) = (term405 A f c x).
Proof. exact (TRANS (@lem4883571 A f c x) (@lem4883570 A f c x)). Qed.
Lemma lem4883573 {A : Type'} (f : type639 A) (c : A -> Prop) : (term340 A f c) = (term406 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883572 A f c x)). Qed.
Lemma lem4883574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883575 {A : Type'} (f : type639 A) (c : A -> Prop) : (term341 A f c) = (term407 A f c).
Proof. exact (MK_COMB (@lem4883574 A) (@lem4883573 A f c)). Qed.
Lemma lem4883576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883577 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term325 A f c P) = (term408 A f c P).
Proof. exact (MK_COMB (@lem4883576) (@lem4883534 A f c P)). Qed.
Lemma lem4883578 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term342 A P f c) = (term409 A P f c).
Proof. exact (MK_COMB (@lem4883577 A f c P) (@lem4883575 A f c)). Qed.
Lemma lem4883580 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4883581 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term343 A P f c) = (term410 A P f c).
Proof. exact (MK_COMB (@lem4883580 A f c) (@lem4883578 A P f c)). Qed.
Lemma lem4883583 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4883584 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term412 A u P f c) = (term413 A u P f c).
Proof. exact (MK_COMB (@lem4883583 A u c) (@lem4883581 A P f c)). Qed.
Lemma lem4883585 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term412 A u P f c).
Proof. exact (@lem17265 (u c) (term343 A P f c)). Qed.
Lemma lem4883586 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term344 A u P f c) = (term413 A u P f c).
Proof. exact (TRANS (@lem4883585 A u P f c) (@lem4883584 A u P f c)). Qed.
Lemma lem4883587 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term345 A u P f) = (term414 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4883586 A u P f c)). Qed.
Lemma lem4883588 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883589 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term346 A u P f) = (term415 A u P f).
Proof. exact (MK_COMB (@lem4883588 A) (@lem4883587 A u P f)). Qed.
Lemma lem4883590 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4883591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883592 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term347 A u P f) = (term416 A u P f).
Proof. exact (MK_COMB (@lem4883591) (@lem4883589 A u P f)). Qed.
Lemma lem4883593 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term417 A P f u).
Proof. exact (MK_COMB (@lem4883592 A u P f) (@lem4883590 A u)). Qed.
Lemma lem4883675 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term418 A P Q) = (term419 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4883676 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term418 A P Q) = (term419 A P Q).
Proof. exact (@lem4883675 A P Q). Qed.
Lemma lem4883677 {A : Type'} (f : type639 A) (c : A -> Prop) : (term420 A f c) = (term421 A f c).
Proof. exact (@lem4883676 A (term422 A f c) (term423 A f c)). Qed.
Lemma lem4883678 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term424 A f c x) = (term402 A f c x).
Proof. exact (eq_refl (term424 A f c x)). Qed.
Lemma lem4883679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883680 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term425 A f c x) = (term403 A f c x).
Proof. exact (MK_COMB (@lem4883679) (@lem4883678 A f c x)). Qed.
Lemma lem4883681 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term426 A f c x) = (term400 A f c x).
Proof. exact (eq_refl (term426 A f c x)). Qed.
Lemma lem4883682 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term427 A f c x) = (term405 A f c x).
Proof. exact (MK_COMB (@lem4883680 A f c x) (@lem4883681 A f c x)). Qed.
Lemma lem4883683 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term406 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883682 A f c x)). Qed.
Lemma lem4883684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883685 {A : Type'} (f : type639 A) (c : A -> Prop) : (term420 A f c) = (term407 A f c).
Proof. exact (MK_COMB (@lem4883684 A) (@lem4883683 A f c)). Qed.
Lemma lem4883686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883687 {A : Type'} (f : type639 A) (c : A -> Prop) : (term429 A f c) = (term430 A f c).
Proof. exact (MK_COMB (@lem4883686) (@lem4883685 A f c)). Qed.
Lemma lem4883688 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term424 A f c x) = (term402 A f c x).
Proof. exact (eq_refl (term424 A f c x)). Qed.
Lemma lem4883689 {A : Type'} (f : type639 A) (c : A -> Prop) : (term431 A f c) = (term422 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883688 A f c x)). Qed.
Lemma lem4883690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883691 {A : Type'} (f : type639 A) (c : A -> Prop) : (term432 A f c) = (term433 A f c).
Proof. exact (MK_COMB (@lem4883690 A) (@lem4883689 A f c)). Qed.
Lemma lem4883692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883693 {A : Type'} (f : type639 A) (c : A -> Prop) : (term434 A f c) = (term435 A f c).
Proof. exact (MK_COMB (@lem4883692) (@lem4883691 A f c)). Qed.
Lemma lem4883694 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term426 A f c x) = (term400 A f c x).
Proof. exact (eq_refl (term426 A f c x)). Qed.
Lemma lem4883695 {A : Type'} (f : type639 A) (c : A -> Prop) : (term436 A f c) = (term423 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883694 A f c x)). Qed.
Lemma lem4883696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883697 {A : Type'} (f : type639 A) (c : A -> Prop) : (term437 A f c) = (term438 A f c).
Proof. exact (MK_COMB (@lem4883696 A) (@lem4883695 A f c)). Qed.
Lemma lem4883698 {A : Type'} (f : type639 A) (c : A -> Prop) : (term421 A f c) = (term439 A f c).
Proof. exact (MK_COMB (@lem4883693 A f c) (@lem4883697 A f c)). Qed.
Lemma lem4883699 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term420 A f c) = (term421 A f c)) = ((term407 A f c) = (term439 A f c)).
Proof. exact (MK_COMB (@lem4883687 A f c) (@lem4883698 A f c)). Qed.
Lemma lem4883700 {A : Type'} (f : type639 A) (c : A -> Prop) : (term407 A f c) = (term439 A f c).
Proof. exact (EQ_MP (@lem4883699 A f c) (@lem4883677 A f c)). Qed.
Lemma lem4883877 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4883878 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term409 A P f c) = (term440 A P f c).
Proof. exact (MK_COMB (@lem4883877 A f c P) (@lem4883700 A f c)). Qed.
Lemma lem4883879 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4883880 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term410 A P f c) = (term441 A P f c).
Proof. exact (MK_COMB (@lem4883879 A f c) (@lem4883878 A P f c)). Qed.
Lemma lem4883881 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4883882 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term413 A u P f c) = (term442 A u P f c).
Proof. exact (MK_COMB (@lem4883881 A u c) (@lem4883880 A P f c)). Qed.
Lemma lem4883883 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term414 A u P f) = (term443 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4883882 A u P f c)). Qed.
Lemma lem4883884 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4883885 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term415 A u P f) = (term444 A u P f).
Proof. exact (MK_COMB (@lem4883884 A) (@lem4883883 A u P f)). Qed.
Lemma lem4883934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883935 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term416 A u P f) = (term445 A u P f).
Proof. exact (MK_COMB (@lem4883934) (@lem4883885 A u P f)). Qed.
Lemma lem4883936 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4883937 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term417 A P f u) = (term446 A P f u).
Proof. exact (MK_COMB (@lem4883935 A u P f) (@lem4883936 A u)). Qed.
Lemma lem4883939 {A : Type'} (P : A -> Prop) (Q : Prop) : (term447 A P Q) = (term448 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4883940 {A : Type'} (P : type686 A) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (@lem4883939 (A -> Prop) P Q). Qed.
Lemma lem4883941 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term451 A f c x) = (term452 A f c x).
Proof. exact (@lem4883940 A (term335 A f c x) (term396 A c x)). Qed.
Lemma lem4883942 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4883943 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term453 A f c x) = (term335 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883942 A f c t x)). Qed.
Lemma lem4883944 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883945 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term454 A f c x) = (term336 A f c x).
Proof. exact (MK_COMB (@lem4883944 A) (@lem4883943 A f c x)). Qed.
Lemma lem4883946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4883947 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term455 A f c x) = (term401 A f c x).
Proof. exact (MK_COMB (@lem4883946) (@lem4883945 A f c x)). Qed.
Lemma lem4883948 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4883949 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term451 A f c x) = (term402 A f c x).
Proof. exact (MK_COMB (@lem4883947 A f c x) (@lem4883948 A c x)). Qed.
Lemma lem4883950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883951 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term456 A f c x) = (term457 A f c x).
Proof. exact (MK_COMB (@lem4883950) (@lem4883949 A f c x)). Qed.
Lemma lem4883952 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term391 A f c x t) = (term333 A f c t x).
Proof. exact (eq_refl (term391 A f c x t)). Qed.
Lemma lem4883953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4883954 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term458 A f c x t) = (term459 A f c t x).
Proof. exact (MK_COMB (@lem4883953) (@lem4883952 A f c t x)). Qed.
Lemma lem4883955 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term396 A c x).
Proof. exact (eq_refl (term396 A c x)). Qed.
Lemma lem4883956 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term460 A f t c x) = (term461 A f t c x).
Proof. exact (MK_COMB (@lem4883954 A f c t x) (@lem4883955 A c x)). Qed.
Lemma lem4883957 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term462 A f c x) = (term463 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883956 A f t c x)). Qed.
Lemma lem4883958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883959 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term452 A f c x) = (term464 A f c x).
Proof. exact (MK_COMB (@lem4883958 A) (@lem4883957 A f c x)). Qed.
Lemma lem4883960 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term451 A f c x) = (term452 A f c x)) = ((term402 A f c x) = (term464 A f c x)).
Proof. exact (MK_COMB (@lem4883951 A f c x) (@lem4883959 A f c x)). Qed.
Lemma lem4883961 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term402 A f c x) = (term464 A f c x).
Proof. exact (EQ_MP (@lem4883960 A f c x) (@lem4883941 A f c x)). Qed.
Lemma lem4883962 {A : Type'} (f : type639 A) (c : A -> Prop) : (term422 A f c) = (term465 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883961 A f c x)). Qed.
Lemma lem4883963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883964 {A : Type'} (f : type639 A) (c : A -> Prop) : (term433 A f c) = (term466 A f c).
Proof. exact (MK_COMB (@lem4883963 A) (@lem4883962 A f c)). Qed.
Lemma lem4883966 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4883967 {A : Type'} (P : type1364 A) : (term467 A P) = (term468 A P).
Proof. exact (@lem4883966 A (A -> Prop) P). Qed.
Lemma lem4883968 {A : Type'} (f : type639 A) (c : A -> Prop) : (term469 A f c) = (term470 A f c).
Proof. exact (@lem4883967 A (term471 A f c)). Qed.
Lemma lem4883969 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term472 A f c x) = (term463 A f c x).
Proof. exact (eq_refl (term472 A f c x)). Qed.
Lemma lem4883970 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4883971 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) (t : A -> Prop) : (term473 A f c x t) = (term474 A f c x t).
Proof. exact (MK_COMB (@lem4883969 A f c x) (@lem4883970 A t)). Qed.
Lemma lem4883972 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term474 A f c x t) = (term461 A f t c x).
Proof. exact (eq_refl (term474 A f c x t)). Qed.
Lemma lem4883973 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term473 A f c x t) = (term461 A f t c x).
Proof. exact (TRANS (@lem4883971 A f c x t) (@lem4883972 A f t c x)). Qed.
Lemma lem4883974 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term475 A f c x) = (term463 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4883973 A f t c x)). Qed.
Lemma lem4883975 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4883976 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term476 A f c x) = (term464 A f c x).
Proof. exact (MK_COMB (@lem4883975 A) (@lem4883974 A f c x)). Qed.
Lemma lem4883977 {A : Type'} (f : type639 A) (c : A -> Prop) : (term477 A f c) = (term465 A f c).
Proof. exact (fun_ext (fun x : A => @lem4883976 A f c x)). Qed.
Lemma lem4883978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883979 {A : Type'} (f : type639 A) (c : A -> Prop) : (term469 A f c) = (term466 A f c).
Proof. exact (MK_COMB (@lem4883978 A) (@lem4883977 A f c)). Qed.
Lemma lem4883980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4883981 {A : Type'} (f : type639 A) (c : A -> Prop) : (term478 A f c) = (term479 A f c).
Proof. exact (MK_COMB (@lem4883980) (@lem4883979 A f c)). Qed.
Lemma lem4883982 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term472 A f c x) = (term463 A f c x).
Proof. exact (eq_refl (term472 A f c x)). Qed.
Lemma lem4883983 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4883984 {A : Type'} (f : type639 A) (c : A -> Prop) (t : type1402 A) (x : A) : (term480 A f c t x) = (term481 A f c t x).
Proof. exact (MK_COMB (@lem4883982 A f c x) (@lem4883983 A t x)). Qed.
Lemma lem4883985 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term481 A f c t x) = (term482 A f t c x).
Proof. exact (eq_refl (term481 A f c t x)). Qed.
Lemma lem4883986 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term480 A f c t x) = (term482 A f t c x).
Proof. exact (TRANS (@lem4883984 A f c t x) (@lem4883985 A f t c x)). Qed.
Lemma lem4883987 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term483 A f c t) = (term484 A f t c).
Proof. exact (fun_ext (fun x : A => @lem4883986 A f t c x)). Qed.
Lemma lem4883988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4883989 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term485 A f c t) = (term486 A f t c).
Proof. exact (MK_COMB (@lem4883988 A) (@lem4883987 A f t c)). Qed.
Lemma lem4883990 {A : Type'} (f : type639 A) (c : A -> Prop) : (term487 A f c) = (term488 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4883989 A f t c)). Qed.
Lemma lem4883991 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4883992 {A : Type'} (f : type639 A) (c : A -> Prop) : (term470 A f c) = (term489 A f c).
Proof. exact (MK_COMB (@lem4883991 A) (@lem4883990 A f c)). Qed.
Lemma lem4883993 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term469 A f c) = (term470 A f c)) = ((term466 A f c) = (term489 A f c)).
Proof. exact (MK_COMB (@lem4883981 A f c) (@lem4883992 A f c)). Qed.
Lemma lem4883994 {A : Type'} (f : type639 A) (c : A -> Prop) : (term466 A f c) = (term489 A f c).
Proof. exact (EQ_MP (@lem4883993 A f c) (@lem4883968 A f c)). Qed.
Lemma lem4883995 {A : Type'} (f : type639 A) (c : A -> Prop) : (term433 A f c) = (term489 A f c).
Proof. exact (TRANS (@lem4883964 A f c) (@lem4883994 A f c)). Qed.
Lemma lem4883996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4883997 {A : Type'} (f : type639 A) (c : A -> Prop) : (term435 A f c) = (term490 A f c).
Proof. exact (MK_COMB (@lem4883996) (@lem4883995 A f c)). Qed.
Lemma lem4883998 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4883999 {A : Type'} (f : type639 A) (c : A -> Prop) : (term439 A f c) = (term491 A f c).
Proof. exact (MK_COMB (@lem4883997 A f c) (@lem4883998 A f c)). Qed.
Lemma lem4884001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4884002 {A : Type'} (P : type421 A) (Q : Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (@lem4884001 (type1402 A) P Q). Qed.
Lemma lem4884003 {A : Type'} (f : type639 A) (c : A -> Prop) : (term496 A f c) = (term497 A f c).
Proof. exact (@lem4884002 A (term488 A f c) (term438 A f c)). Qed.
Lemma lem4884004 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term498 A f c t) = (term486 A f t c).
Proof. exact (eq_refl (term498 A f c t)). Qed.
Lemma lem4884005 {A : Type'} (f : type639 A) (c : A -> Prop) : (term499 A f c) = (term488 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884004 A f t c)). Qed.
Lemma lem4884006 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884007 {A : Type'} (f : type639 A) (c : A -> Prop) : (term500 A f c) = (term489 A f c).
Proof. exact (MK_COMB (@lem4884006 A) (@lem4884005 A f c)). Qed.
Lemma lem4884008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884009 {A : Type'} (f : type639 A) (c : A -> Prop) : (term501 A f c) = (term490 A f c).
Proof. exact (MK_COMB (@lem4884008) (@lem4884007 A f c)). Qed.
Lemma lem4884010 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4884011 {A : Type'} (f : type639 A) (c : A -> Prop) : (term496 A f c) = (term491 A f c).
Proof. exact (MK_COMB (@lem4884009 A f c) (@lem4884010 A f c)). Qed.
Lemma lem4884012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884013 {A : Type'} (f : type639 A) (c : A -> Prop) : (term502 A f c) = (term503 A f c).
Proof. exact (MK_COMB (@lem4884012) (@lem4884011 A f c)). Qed.
Lemma lem4884014 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term498 A f c t) = (term486 A f t c).
Proof. exact (eq_refl (term498 A f c t)). Qed.
Lemma lem4884015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884016 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term504 A f c t) = (term505 A f t c).
Proof. exact (MK_COMB (@lem4884015) (@lem4884014 A f t c)). Qed.
Lemma lem4884017 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term438 A f c).
Proof. exact (eq_refl (term438 A f c)). Qed.
Lemma lem4884018 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term506 A t f c) = (term507 A t f c).
Proof. exact (MK_COMB (@lem4884016 A f t c) (@lem4884017 A f c)). Qed.
Lemma lem4884019 {A : Type'} (f : type639 A) (c : A -> Prop) : (term508 A f c) = (term509 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884018 A t f c)). Qed.
Lemma lem4884020 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884021 {A : Type'} (f : type639 A) (c : A -> Prop) : (term497 A f c) = (term510 A f c).
Proof. exact (MK_COMB (@lem4884020 A) (@lem4884019 A f c)). Qed.
Lemma lem4884022 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term496 A f c) = (term497 A f c)) = ((term491 A f c) = (term510 A f c)).
Proof. exact (MK_COMB (@lem4884013 A f c) (@lem4884021 A f c)). Qed.
Lemma lem4884023 {A : Type'} (f : type639 A) (c : A -> Prop) : (term491 A f c) = (term510 A f c).
Proof. exact (EQ_MP (@lem4884022 A f c) (@lem4884003 A f c)). Qed.
Lemma lem4884024 {A : Type'} (f : type639 A) (c : A -> Prop) : (term439 A f c) = (term510 A f c).
Proof. exact (TRANS (@lem4883999 A f c) (@lem4884023 A f c)). Qed.
Lemma lem4884025 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4884026 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term440 A P f c) = (term511 A P f c).
Proof. exact (MK_COMB (@lem4884025 A f c P) (@lem4884024 A f c)). Qed.
Lemma lem4884028 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4884029 {A : Type'} (P : Prop) (Q : type421 A) : (term514 A P Q) = (term515 A P Q).
Proof. exact (@lem4884028 (type1402 A) P Q). Qed.
Lemma lem4884030 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term516 A P f c) = (term517 A P f c).
Proof. exact (@lem4884029 A (term384 A f c P) (term509 A f c)). Qed.
Lemma lem4884031 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term518 A f c t) = (term507 A t f c).
Proof. exact (eq_refl (term518 A f c t)). Qed.
Lemma lem4884032 {A : Type'} (f : type639 A) (c : A -> Prop) : (term519 A f c) = (term509 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884031 A t f c)). Qed.
Lemma lem4884033 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884034 {A : Type'} (f : type639 A) (c : A -> Prop) : (term520 A f c) = (term510 A f c).
Proof. exact (MK_COMB (@lem4884033 A) (@lem4884032 A f c)). Qed.
Lemma lem4884035 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4884036 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term516 A P f c) = (term511 A P f c).
Proof. exact (MK_COMB (@lem4884035 A f c P) (@lem4884034 A f c)). Qed.
Lemma lem4884037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884038 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term521 A P f c) = (term522 A P f c).
Proof. exact (MK_COMB (@lem4884037) (@lem4884036 A P f c)). Qed.
Lemma lem4884039 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term518 A f c t) = (term507 A t f c).
Proof. exact (eq_refl (term518 A f c t)). Qed.
Lemma lem4884040 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term408 A f c P).
Proof. exact (eq_refl (term408 A f c P)). Qed.
Lemma lem4884041 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term523 A P f c t) = (term524 A P t f c).
Proof. exact (MK_COMB (@lem4884040 A f c P) (@lem4884039 A t f c)). Qed.
Lemma lem4884042 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A P f c) = (term526 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884041 A P t f c)). Qed.
Lemma lem4884043 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884044 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term517 A P f c) = (term527 A P f c).
Proof. exact (MK_COMB (@lem4884043 A) (@lem4884042 A P f c)). Qed.
Lemma lem4884045 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term516 A P f c) = (term517 A P f c)) = ((term511 A P f c) = (term527 A P f c)).
Proof. exact (MK_COMB (@lem4884038 A P f c) (@lem4884044 A P f c)). Qed.
Lemma lem4884046 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term511 A P f c) = (term527 A P f c).
Proof. exact (EQ_MP (@lem4884045 A P f c) (@lem4884030 A P f c)). Qed.
Lemma lem4884047 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term440 A P f c) = (term527 A P f c).
Proof. exact (TRANS (@lem4884026 A P f c) (@lem4884046 A P f c)). Qed.
Lemma lem4884048 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4884049 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term441 A P f c) = (term528 A P f c).
Proof. exact (MK_COMB (@lem4884048 A f c) (@lem4884047 A P f c)). Qed.
Lemma lem4884051 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4884052 {A : Type'} (P : Prop) (Q : type421 A) : (term514 A P Q) = (term515 A P Q).
Proof. exact (@lem4884051 (type1402 A) P Q). Qed.
Lemma lem4884053 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A P f c) = (term530 A P f c).
Proof. exact (@lem4884052 A (term195 A f c) (term526 A P f c)). Qed.
Lemma lem4884054 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term531 A P f c t) = (term524 A P t f c).
Proof. exact (eq_refl (term531 A P f c t)). Qed.
Lemma lem4884055 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term532 A P f c) = (term526 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884054 A P t f c)). Qed.
Lemma lem4884056 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884057 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term533 A P f c) = (term527 A P f c).
Proof. exact (MK_COMB (@lem4884056 A) (@lem4884055 A P f c)). Qed.
Lemma lem4884058 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4884059 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A P f c) = (term528 A P f c).
Proof. exact (MK_COMB (@lem4884058 A f c) (@lem4884057 A P f c)). Qed.
Lemma lem4884060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884061 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term534 A P f c) = (term535 A P f c).
Proof. exact (MK_COMB (@lem4884060) (@lem4884059 A P f c)). Qed.
Lemma lem4884062 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term531 A P f c t) = (term524 A P t f c).
Proof. exact (eq_refl (term531 A P f c t)). Qed.
Lemma lem4884063 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term303 A f c).
Proof. exact (eq_refl (term303 A f c)). Qed.
Lemma lem4884064 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term536 A P f c t) = (term537 A P t f c).
Proof. exact (MK_COMB (@lem4884063 A f c) (@lem4884062 A P t f c)). Qed.
Lemma lem4884065 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term538 A P f c) = (term539 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884064 A P t f c)). Qed.
Lemma lem4884066 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884067 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term530 A P f c) = (term540 A P f c).
Proof. exact (MK_COMB (@lem4884066 A) (@lem4884065 A P f c)). Qed.
Lemma lem4884068 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term529 A P f c) = (term530 A P f c)) = ((term528 A P f c) = (term540 A P f c)).
Proof. exact (MK_COMB (@lem4884061 A P f c) (@lem4884067 A P f c)). Qed.
Lemma lem4884069 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term528 A P f c) = (term540 A P f c).
Proof. exact (EQ_MP (@lem4884068 A P f c) (@lem4884053 A P f c)). Qed.
Lemma lem4884070 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term441 A P f c) = (term540 A P f c).
Proof. exact (TRANS (@lem4884049 A P f c) (@lem4884069 A P f c)). Qed.
Lemma lem4884071 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4884072 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term442 A u P f c) = (term541 A u P f c).
Proof. exact (MK_COMB (@lem4884071 A u c) (@lem4884070 A P f c)). Qed.
Lemma lem4884074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term542 A P Q) = (term543 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4884075 {A : Type'} (P : Prop) (Q : type421 A) : (term544 A P Q) = (term545 A P Q).
Proof. exact (@lem4884074 (type1402 A) P Q). Qed.
Lemma lem4884076 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term546 A u P f c) = (term547 A u P f c).
Proof. exact (@lem4884075 A (term381 A u c) (term539 A P f c)). Qed.
Lemma lem4884077 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term548 A P f c t) = (term537 A P t f c).
Proof. exact (eq_refl (term548 A P f c t)). Qed.
Lemma lem4884078 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term549 A P f c) = (term539 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884077 A P t f c)). Qed.
Lemma lem4884079 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884080 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term550 A P f c) = (term540 A P f c).
Proof. exact (MK_COMB (@lem4884079 A) (@lem4884078 A P f c)). Qed.
Lemma lem4884081 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4884082 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term546 A u P f c) = (term541 A u P f c).
Proof. exact (MK_COMB (@lem4884081 A u c) (@lem4884080 A P f c)). Qed.
Lemma lem4884083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884084 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term551 A u P f c) = (term552 A u P f c).
Proof. exact (MK_COMB (@lem4884083) (@lem4884082 A u P f c)). Qed.
Lemma lem4884085 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term548 A P f c t) = (term537 A P t f c).
Proof. exact (eq_refl (term548 A P f c t)). Qed.
Lemma lem4884086 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term411 A u c).
Proof. exact (eq_refl (term411 A u c)). Qed.
Lemma lem4884087 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term553 A u P f c t) = (term554 A u P t f c).
Proof. exact (MK_COMB (@lem4884086 A u c) (@lem4884085 A P t f c)). Qed.
Lemma lem4884088 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term555 A u P f c) = (term556 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884087 A u P t f c)). Qed.
Lemma lem4884089 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884090 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term547 A u P f c) = (term557 A u P f c).
Proof. exact (MK_COMB (@lem4884089 A) (@lem4884088 A u P f c)). Qed.
Lemma lem4884091 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term546 A u P f c) = (term547 A u P f c)) = ((term541 A u P f c) = (term557 A u P f c)).
Proof. exact (MK_COMB (@lem4884084 A u P f c) (@lem4884090 A u P f c)). Qed.
Lemma lem4884092 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term541 A u P f c) = (term557 A u P f c).
Proof. exact (EQ_MP (@lem4884091 A u P f c) (@lem4884076 A u P f c)). Qed.
Lemma lem4884093 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term442 A u P f c) = (term557 A u P f c).
Proof. exact (TRANS (@lem4884072 A u P f c) (@lem4884092 A u P f c)). Qed.
Lemma lem4884094 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term443 A u P f) = (term558 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4884093 A u P f c)). Qed.
Lemma lem4884095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884096 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term444 A u P f) = (term559 A u P f).
Proof. exact (MK_COMB (@lem4884095 A) (@lem4884094 A u P f)). Qed.
Lemma lem4884098 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4884099 {A : Type'} (P : type611 A) : (term560 A P) = (term561 A P).
Proof. exact (@lem4884098 (A -> Prop) (type1402 A) P). Qed.
Lemma lem4884100 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term562 A u P f) = (term563 A u P f).
Proof. exact (@lem4884099 A (term564 A u P f)). Qed.
Lemma lem4884101 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term565 A u P f c) = (term556 A u P f c).
Proof. exact (eq_refl (term565 A u P f c)). Qed.
Lemma lem4884102 {A : Type'} (t : type1402 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4884103 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) (t : type1402 A) : (term566 A u P f c t) = (term567 A u P f c t).
Proof. exact (MK_COMB (@lem4884101 A u P f c) (@lem4884102 A t)). Qed.
Lemma lem4884104 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term567 A u P f c t) = (term554 A u P t f c).
Proof. exact (eq_refl (term567 A u P f c t)). Qed.
Lemma lem4884105 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term566 A u P f c t) = (term554 A u P t f c).
Proof. exact (TRANS (@lem4884103 A u P f c t) (@lem4884104 A u P t f c)). Qed.
Lemma lem4884106 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term568 A u P f c) = (term556 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4884105 A u P t f c)). Qed.
Lemma lem4884107 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4884108 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term569 A u P f c) = (term557 A u P f c).
Proof. exact (MK_COMB (@lem4884107 A) (@lem4884106 A u P f c)). Qed.
Lemma lem4884109 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term570 A u P f) = (term558 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4884108 A u P f c)). Qed.
Lemma lem4884110 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884111 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term562 A u P f) = (term559 A u P f).
Proof. exact (MK_COMB (@lem4884110 A) (@lem4884109 A u P f)). Qed.
Lemma lem4884112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884113 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term571 A u P f) = (term572 A u P f).
Proof. exact (MK_COMB (@lem4884112) (@lem4884111 A u P f)). Qed.
Lemma lem4884114 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term565 A u P f c) = (term556 A u P f c).
Proof. exact (eq_refl (term565 A u P f c)). Qed.
Lemma lem4884115 {A : Type'} (t : type667 A) (c : A -> Prop) : (t c) = (t c).
Proof. exact (eq_refl (t c)). Qed.
Lemma lem4884116 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (t : type667 A) (c : A -> Prop) : (term573 A u P f t c) = (term574 A u P f t c).
Proof. exact (MK_COMB (@lem4884114 A u P f c) (@lem4884115 A t c)). Qed.
Lemma lem4884117 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term574 A u P f t c) = (term575 A u P t f c).
Proof. exact (eq_refl (term574 A u P f t c)). Qed.
Lemma lem4884118 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term573 A u P f t c) = (term575 A u P t f c).
Proof. exact (TRANS (@lem4884116 A u P f t c) (@lem4884117 A u P t f c)). Qed.
Lemma lem4884119 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term576 A u P f t) = (term577 A u P t f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4884118 A u P t f c)). Qed.
Lemma lem4884120 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884121 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term578 A u P f t) = (term579 A u P t f).
Proof. exact (MK_COMB (@lem4884120 A) (@lem4884119 A u P t f)). Qed.
Lemma lem4884122 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term580 A u P f) = (term581 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4884121 A u P t f)). Qed.
Lemma lem4884123 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4884124 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term563 A u P f) = (term582 A u P f).
Proof. exact (MK_COMB (@lem4884123 A) (@lem4884122 A u P f)). Qed.
Lemma lem4884125 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : ((term562 A u P f) = (term563 A u P f)) = ((term559 A u P f) = (term582 A u P f)).
Proof. exact (MK_COMB (@lem4884113 A u P f) (@lem4884124 A u P f)). Qed.
Lemma lem4884126 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term559 A u P f) = (term582 A u P f).
Proof. exact (EQ_MP (@lem4884125 A u P f) (@lem4884100 A u P f)). Qed.
Lemma lem4884127 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term444 A u P f) = (term582 A u P f).
Proof. exact (TRANS (@lem4884096 A u P f) (@lem4884126 A u P f)). Qed.
Lemma lem4884128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884129 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term445 A u P f) = (term583 A u P f).
Proof. exact (MK_COMB (@lem4884128) (@lem4884127 A u P f)). Qed.
Lemma lem4884130 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4884131 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term446 A P f u) = (term584 A P f u).
Proof. exact (MK_COMB (@lem4884129 A u P f) (@lem4884130 A u)). Qed.
Lemma lem4884133 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4884134 {A : Type'} (P : type149 A) (Q : Prop) : (term585 A P Q) = (term586 A P Q).
Proof. exact (@lem4884133 (type667 A) P Q). Qed.
Lemma lem4884135 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term587 A P f u) = (term588 A P f u).
Proof. exact (@lem4884134 A (term581 A u P f) (@FINITE (A -> Prop) u)). Qed.
Lemma lem4884136 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term589 A u P f t) = (term579 A u P t f).
Proof. exact (eq_refl (term589 A u P f t)). Qed.
Lemma lem4884137 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term590 A u P f) = (term581 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4884136 A u P t f)). Qed.
Lemma lem4884138 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4884139 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term591 A u P f) = (term582 A u P f).
Proof. exact (MK_COMB (@lem4884138 A) (@lem4884137 A u P f)). Qed.
Lemma lem4884140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884141 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term592 A u P f) = (term583 A u P f).
Proof. exact (MK_COMB (@lem4884140) (@lem4884139 A u P f)). Qed.
Lemma lem4884142 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4884143 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term587 A P f u) = (term584 A P f u).
Proof. exact (MK_COMB (@lem4884141 A u P f) (@lem4884142 A u)). Qed.
Lemma lem4884144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884145 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term593 A P f u) = (term594 A P f u).
Proof. exact (MK_COMB (@lem4884144) (@lem4884143 A P f u)). Qed.
Lemma lem4884146 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term589 A u P f t) = (term579 A u P t f).
Proof. exact (eq_refl (term589 A u P f t)). Qed.
Lemma lem4884147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884148 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term595 A u P f t) = (term596 A u P t f).
Proof. exact (MK_COMB (@lem4884147) (@lem4884146 A u P t f)). Qed.
Lemma lem4884149 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@FINITE (A -> Prop) u).
Proof. exact (eq_refl (@FINITE (A -> Prop) u)). Qed.
Lemma lem4884150 {A : Type'} (P : type686 A) (t : type667 A) (f : type639 A) (u : type686 A) : (term597 A P f t u) = (term598 A P t f u).
Proof. exact (MK_COMB (@lem4884148 A u P t f) (@lem4884149 A u)). Qed.
Lemma lem4884151 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term599 A P f u) = (term600 A P f u).
Proof. exact (fun_ext (fun t : type667 A => @lem4884150 A P t f u)). Qed.
Lemma lem4884152 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4884153 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term588 A P f u) = (term601 A P f u).
Proof. exact (MK_COMB (@lem4884152 A) (@lem4884151 A P f u)). Qed.
Lemma lem4884154 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : ((term587 A P f u) = (term588 A P f u)) = ((term584 A P f u) = (term601 A P f u)).
Proof. exact (MK_COMB (@lem4884145 A P f u) (@lem4884153 A P f u)). Qed.
Lemma lem4884155 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term584 A P f u) = (term601 A P f u).
Proof. exact (EQ_MP (@lem4884154 A P f u) (@lem4884135 A P f u)). Qed.
Lemma lem4884156 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term446 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4884131 A P f u) (@lem4884155 A P f u)). Qed.
Lemma lem4884157 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term417 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4883937 A P f u) (@lem4884156 A P f u)). Qed.
Lemma lem4884158 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term348 A P f u) = (term601 A P f u).
Proof. exact (TRANS (@lem4883593 A P f u) (@lem4884157 A P f u)). Qed.
Lemma lem4884159 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term601 A P f u.
Proof. exact (EQ_MP (@lem4884158 A P f u) (@lem4883517 A P f u h1)). Qed.
Lemma lem4884168 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term1024 A u f s t) = (term1025 A u f s t).
Proof. exact (@lem17045 (u s) (f s t)). Qed.
Lemma lem4884172 {A : Type'} (t : A -> Prop) (x : A) : (term396 A t x) = (term396 A t x).
Proof. exact (eq_refl (term396 A t x)). Qed.
Lemma lem4884174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884175 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term1026 A u f s t) = (term1027 A u f s t).
Proof. exact (MK_COMB (@lem4884174) (@lem4884168 A u f s t)). Qed.
Lemma lem4884176 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1028 A u f s t x) = (term1029 A u f s t x).
Proof. exact (MK_COMB (@lem4884175 A u f s t) (@lem4884172 A t x)). Qed.
Lemma lem4884177 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1030 A u f s t x) = (term1028 A u f s t x).
Proof. exact (@lem17045 (term352 A u f s t) (t x)). Qed.
Lemma lem4884178 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1030 A u f s t x) = (term1029 A u f s t x).
Proof. exact (TRANS (@lem4884177 A u f s t x) (@lem4884176 A u f s t x)). Qed.
Lemma lem4884181 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term989 A u f s t x) = (term989 A u f s t x).
Proof. exact (eq_refl (term989 A u f s t x)). Qed.
Lemma lem4884182 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4884183 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1031 A u f s x) = (term1032 A u f s x).
Proof. exact (@lem4884182 A (term990 A u f s x)). Qed.
Lemma lem4884184 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1033 A u f s x t) = (term989 A u f s t x).
Proof. exact (eq_refl (term1033 A u f s x t)). Qed.
Lemma lem4884185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884186 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1034 A u f s x t) = (term1030 A u f s t x).
Proof. exact (MK_COMB (@lem4884185) (@lem4884184 A u f s t x)). Qed.
Lemma lem4884187 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1034 A u f s x t) = (term1029 A u f s t x).
Proof. exact (TRANS (@lem4884186 A u f s t x) (@lem4884178 A u f s t x)). Qed.
Lemma lem4884188 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1035 A u f s x) = (term1036 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884187 A u f s t x)). Qed.
Lemma lem4884189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884190 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1032 A u f s x) = (term1037 A u f s x).
Proof. exact (MK_COMB (@lem4884189 A) (@lem4884188 A u f s x)). Qed.
Lemma lem4884191 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1031 A u f s x) = (term1037 A u f s x).
Proof. exact (TRANS (@lem4884183 A u f s x) (@lem4884190 A u f s x)). Qed.
Lemma lem4884192 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term990 A u f s x) = (term990 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884181 A u f s t x)). Qed.
Lemma lem4884193 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884194 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term991 A u f s x) = (term991 A u f s x).
Proof. exact (MK_COMB (@lem4884193 A) (@lem4884192 A u f s x)). Qed.
Lemma lem4884195 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4884196 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1038 A u f x) = (term1039 A u f x).
Proof. exact (@lem4884195 A (term992 A u f x)). Qed.
Lemma lem4884197 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1040 A u f x s) = (term991 A u f s x).
Proof. exact (eq_refl (term1040 A u f x s)). Qed.
Lemma lem4884198 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884199 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1041 A u f x s) = (term1031 A u f s x).
Proof. exact (MK_COMB (@lem4884198) (@lem4884197 A u f s x)). Qed.
Lemma lem4884200 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1041 A u f x s) = (term1037 A u f s x).
Proof. exact (TRANS (@lem4884199 A u f s x) (@lem4884191 A u f s x)). Qed.
Lemma lem4884201 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1042 A u f x) = (term1043 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884200 A u f s x)). Qed.
Lemma lem4884202 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884203 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1039 A u f x) = (term1044 A u f x).
Proof. exact (MK_COMB (@lem4884202 A) (@lem4884201 A u f x)). Qed.
Lemma lem4884204 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1038 A u f x) = (term1044 A u f x).
Proof. exact (TRANS (@lem4884196 A u f x) (@lem4884203 A u f x)). Qed.
Lemma lem4884205 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term992 A u f x) = (term992 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884194 A u f s x)). Qed.
Lemma lem4884206 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884207 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term993 A u f x) = (term993 A u f x).
Proof. exact (MK_COMB (@lem4884206 A) (@lem4884205 A u f x)). Qed.
Lemma lem4884216 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1045 A u t x) = (term1046 A u t x).
Proof. exact (@lem17045 (u t) (t x)). Qed.
Lemma lem4884219 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term996 A u t x) = (term996 A u t x).
Proof. exact (eq_refl (term996 A u t x)). Qed.
Lemma lem4884220 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4884221 {A : Type'} (u : type686 A) (x : A) : (term1047 A u x) = (term1048 A u x).
Proof. exact (@lem4884220 A (term998 A u x)). Qed.
Lemma lem4884222 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1049 A u x t) = (term996 A u t x).
Proof. exact (eq_refl (term1049 A u x t)). Qed.
Lemma lem4884223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884224 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1050 A u x t) = (term1045 A u t x).
Proof. exact (MK_COMB (@lem4884223) (@lem4884222 A u t x)). Qed.
Lemma lem4884225 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1050 A u x t) = (term1046 A u t x).
Proof. exact (TRANS (@lem4884224 A u t x) (@lem4884216 A u t x)). Qed.
Lemma lem4884226 {A : Type'} (u : type686 A) (x : A) : (term1051 A u x) = (term1052 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884225 A u t x)). Qed.
Lemma lem4884227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884228 {A : Type'} (u : type686 A) (x : A) : (term1048 A u x) = (term1053 A u x).
Proof. exact (MK_COMB (@lem4884227 A) (@lem4884226 A u x)). Qed.
Lemma lem4884229 {A : Type'} (u : type686 A) (x : A) : (term1047 A u x) = (term1053 A u x).
Proof. exact (TRANS (@lem4884221 A u x) (@lem4884228 A u x)). Qed.
Lemma lem4884230 {A : Type'} (u : type686 A) (x : A) : (term998 A u x) = (term998 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884219 A u t x)). Qed.
Lemma lem4884231 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884232 {A : Type'} (u : type686 A) (x : A) : (term999 A u x) = (term999 A u x).
Proof. exact (MK_COMB (@lem4884231 A) (@lem4884230 A u x)). Qed.
Lemma lem4884233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884234 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1054 A u f x) = (term1055 A u f x).
Proof. exact (MK_COMB (@lem4884233) (@lem4884204 A u f x)). Qed.
Lemma lem4884235 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1056 A f u x) = (term1057 A f u x).
Proof. exact (MK_COMB (@lem4884234 A u f x) (@lem4884232 A u x)). Qed.
Lemma lem4884236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884237 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1058 A u f x) = (term1058 A u f x).
Proof. exact (MK_COMB (@lem4884236) (@lem4884207 A u f x)). Qed.
Lemma lem4884238 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1059 A f u x) = (term1060 A f u x).
Proof. exact (MK_COMB (@lem4884237 A u f x) (@lem4884229 A u x)). Qed.
Lemma lem4884239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884240 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1061 A f u x) = (term1062 A f u x).
Proof. exact (MK_COMB (@lem4884239) (@lem4884238 A f u x)). Qed.
Lemma lem4884241 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1063 A f u x) = (term1064 A f u x).
Proof. exact (MK_COMB (@lem4884240 A f u x) (@lem4884235 A f u x)). Qed.
Lemma lem4884242 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1023 A f u x) = (term1063 A f u x).
Proof. exact (@lem17646 (term993 A u f x) (term999 A u x)). Qed.
Lemma lem4884243 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1023 A f u x) = (term1064 A f u x).
Proof. exact (TRANS (@lem4884242 A f u x) (@lem4884241 A f u x)). Qed.
Lemma lem4884426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4884427 {A : Type'} (P : type686 A) (Q : Prop) : (term1065 A P Q) = (term1066 A P Q).
Proof. exact (@lem4884426 (A -> Prop) P Q). Qed.
Lemma lem4884428 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1067 A f u x) = (term1068 A f u x).
Proof. exact (@lem4884427 A (term992 A u f x) (term1053 A u x)). Qed.
Lemma lem4884429 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1040 A u f x s) = (term991 A u f s x).
Proof. exact (eq_refl (term1040 A u f x s)). Qed.
Lemma lem4884430 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1069 A u f x) = (term992 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884429 A u f s x)). Qed.
Lemma lem4884431 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884432 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1070 A u f x) = (term993 A u f x).
Proof. exact (MK_COMB (@lem4884431 A) (@lem4884430 A u f x)). Qed.
Lemma lem4884433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884434 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1071 A u f x) = (term1058 A u f x).
Proof. exact (MK_COMB (@lem4884433) (@lem4884432 A u f x)). Qed.
Lemma lem4884435 {A : Type'} (u : type686 A) (x : A) : (term1053 A u x) = (term1053 A u x).
Proof. exact (eq_refl (term1053 A u x)). Qed.
Lemma lem4884436 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1067 A f u x) = (term1060 A f u x).
Proof. exact (MK_COMB (@lem4884434 A u f x) (@lem4884435 A u x)). Qed.
Lemma lem4884437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884438 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1072 A f u x) = (term1073 A f u x).
Proof. exact (MK_COMB (@lem4884437) (@lem4884436 A f u x)). Qed.
Lemma lem4884439 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1040 A u f x s) = (term991 A u f s x).
Proof. exact (eq_refl (term1040 A u f x s)). Qed.
Lemma lem4884440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884441 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1074 A u f x s) = (term1075 A u f s x).
Proof. exact (MK_COMB (@lem4884440) (@lem4884439 A u f s x)). Qed.
Lemma lem4884442 {A : Type'} (u : type686 A) (x : A) : (term1053 A u x) = (term1053 A u x).
Proof. exact (eq_refl (term1053 A u x)). Qed.
Lemma lem4884443 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1076 A f s u x) = (term1077 A f s u x).
Proof. exact (MK_COMB (@lem4884441 A u f s x) (@lem4884442 A u x)). Qed.
Lemma lem4884444 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1078 A f u x) = (term1079 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884443 A f s u x)). Qed.
Lemma lem4884445 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884446 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1068 A f u x) = (term1080 A f u x).
Proof. exact (MK_COMB (@lem4884445 A) (@lem4884444 A f u x)). Qed.
Lemma lem4884447 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1067 A f u x) = (term1068 A f u x)) = ((term1060 A f u x) = (term1080 A f u x)).
Proof. exact (MK_COMB (@lem4884438 A f u x) (@lem4884446 A f u x)). Qed.
Lemma lem4884448 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1060 A f u x) = (term1080 A f u x).
Proof. exact (EQ_MP (@lem4884447 A f u x) (@lem4884428 A f u x)). Qed.
Lemma lem4884450 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4884451 {A : Type'} (P : type686 A) (Q : Prop) : (term1065 A P Q) = (term1066 A P Q).
Proof. exact (@lem4884450 (A -> Prop) P Q). Qed.
Lemma lem4884452 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1081 A f s u x) = (term1082 A f s u x).
Proof. exact (@lem4884451 A (term990 A u f s x) (term1053 A u x)). Qed.
Lemma lem4884453 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1033 A u f s x t) = (term989 A u f s t x).
Proof. exact (eq_refl (term1033 A u f s x t)). Qed.
Lemma lem4884454 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1083 A u f s x) = (term990 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884453 A u f s t x)). Qed.
Lemma lem4884455 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884456 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1084 A u f s x) = (term991 A u f s x).
Proof. exact (MK_COMB (@lem4884455 A) (@lem4884454 A u f s x)). Qed.
Lemma lem4884457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884458 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1085 A u f s x) = (term1075 A u f s x).
Proof. exact (MK_COMB (@lem4884457) (@lem4884456 A u f s x)). Qed.
Lemma lem4884459 {A : Type'} (u : type686 A) (x : A) : (term1053 A u x) = (term1053 A u x).
Proof. exact (eq_refl (term1053 A u x)). Qed.
Lemma lem4884460 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1081 A f s u x) = (term1077 A f s u x).
Proof. exact (MK_COMB (@lem4884458 A u f s x) (@lem4884459 A u x)). Qed.
Lemma lem4884461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884462 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1086 A f s u x) = (term1087 A f s u x).
Proof. exact (MK_COMB (@lem4884461) (@lem4884460 A f s u x)). Qed.
Lemma lem4884463 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1033 A u f s x t) = (term989 A u f s t x).
Proof. exact (eq_refl (term1033 A u f s x t)). Qed.
Lemma lem4884464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884465 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1088 A u f s x t) = (term1089 A u f s t x).
Proof. exact (MK_COMB (@lem4884464) (@lem4884463 A u f s t x)). Qed.
Lemma lem4884466 {A : Type'} (u : type686 A) (x : A) : (term1053 A u x) = (term1053 A u x).
Proof. exact (eq_refl (term1053 A u x)). Qed.
Lemma lem4884467 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1090 A f s t u x) = (term1091 A f s t u x).
Proof. exact (MK_COMB (@lem4884465 A u f s t x) (@lem4884466 A u x)). Qed.
Lemma lem4884468 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1092 A f s u x) = (term1093 A f s u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884467 A f s t u x)). Qed.
Lemma lem4884469 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884470 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1082 A f s u x) = (term1094 A f s u x).
Proof. exact (MK_COMB (@lem4884469 A) (@lem4884468 A f s u x)). Qed.
Lemma lem4884471 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : ((term1081 A f s u x) = (term1082 A f s u x)) = ((term1077 A f s u x) = (term1094 A f s u x)).
Proof. exact (MK_COMB (@lem4884462 A f s u x) (@lem4884470 A f s u x)). Qed.
Lemma lem4884472 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1077 A f s u x) = (term1094 A f s u x).
Proof. exact (EQ_MP (@lem4884471 A f s u x) (@lem4884452 A f s u x)). Qed.
Lemma lem4884473 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1079 A f u x) = (term1095 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884472 A f s u x)). Qed.
Lemma lem4884474 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884475 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1080 A f u x) = (term1096 A f u x).
Proof. exact (MK_COMB (@lem4884474 A) (@lem4884473 A f u x)). Qed.
Lemma lem4884476 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1060 A f u x) = (term1096 A f u x).
Proof. exact (TRANS (@lem4884448 A f u x) (@lem4884475 A f u x)). Qed.
Lemma lem4884477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884478 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1062 A f u x) = (term1097 A f u x).
Proof. exact (MK_COMB (@lem4884477) (@lem4884476 A f u x)). Qed.
Lemma lem4884480 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4884481 {A : Type'} (P : Prop) (Q : type686 A) : (term1098 A P Q) = (term1099 A P Q).
Proof. exact (@lem4884480 (A -> Prop) P Q). Qed.
Lemma lem4884482 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1100 A f u x) = (term1101 A f u x).
Proof. exact (@lem4884481 A (term1044 A u f x) (term998 A u x)). Qed.
Lemma lem4884483 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1049 A u x t) = (term996 A u t x).
Proof. exact (eq_refl (term1049 A u x t)). Qed.
Lemma lem4884484 {A : Type'} (u : type686 A) (x : A) : (term1102 A u x) = (term998 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884483 A u t x)). Qed.
Lemma lem4884485 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884486 {A : Type'} (u : type686 A) (x : A) : (term1103 A u x) = (term999 A u x).
Proof. exact (MK_COMB (@lem4884485 A) (@lem4884484 A u x)). Qed.
Lemma lem4884487 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1055 A u f x) = (term1055 A u f x).
Proof. exact (eq_refl (term1055 A u f x)). Qed.
Lemma lem4884488 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1100 A f u x) = (term1057 A f u x).
Proof. exact (MK_COMB (@lem4884487 A u f x) (@lem4884486 A u x)). Qed.
Lemma lem4884489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884490 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1104 A f u x) = (term1105 A f u x).
Proof. exact (MK_COMB (@lem4884489) (@lem4884488 A f u x)). Qed.
Lemma lem4884491 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1049 A u x t) = (term996 A u t x).
Proof. exact (eq_refl (term1049 A u x t)). Qed.
Lemma lem4884492 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1055 A u f x) = (term1055 A u f x).
Proof. exact (eq_refl (term1055 A u f x)). Qed.
Lemma lem4884493 {A : Type'} (f : type639 A) (u : type686 A) (t : A -> Prop) (x : A) : (term1106 A f u x t) = (term1107 A f u t x).
Proof. exact (MK_COMB (@lem4884492 A u f x) (@lem4884491 A u t x)). Qed.
Lemma lem4884494 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1108 A f u x) = (term1109 A f u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884493 A f u t x)). Qed.
Lemma lem4884495 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884496 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1101 A f u x) = (term1110 A f u x).
Proof. exact (MK_COMB (@lem4884495 A) (@lem4884494 A f u x)). Qed.
Lemma lem4884497 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1100 A f u x) = (term1101 A f u x)) = ((term1057 A f u x) = (term1110 A f u x)).
Proof. exact (MK_COMB (@lem4884490 A f u x) (@lem4884496 A f u x)). Qed.
Lemma lem4884498 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1057 A f u x) = (term1110 A f u x).
Proof. exact (EQ_MP (@lem4884497 A f u x) (@lem4884482 A f u x)). Qed.
Lemma lem4884499 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1064 A f u x) = (term1111 A f u x).
Proof. exact (MK_COMB (@lem4884478 A f u x) (@lem4884498 A f u x)). Qed.
Lemma lem4884501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1112 A P Q) = (term1113 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4884502 {A : Type'} (P : type686 A) (Q : type686 A) : (term1114 A P Q) = (term1115 A P Q).
Proof. exact (@lem4884501 (A -> Prop) P Q). Qed.
Lemma lem4884503 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1116 A f u x) = (term1117 A f u x).
Proof. exact (@lem4884502 A (term1095 A f u x) (term1109 A f u x)). Qed.
Lemma lem4884504 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1118 A f u x s) = (term1094 A f s u x).
Proof. exact (eq_refl (term1118 A f u x s)). Qed.
Lemma lem4884505 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1119 A f u x) = (term1095 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884504 A f s u x)). Qed.
Lemma lem4884506 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884507 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1120 A f u x) = (term1096 A f u x).
Proof. exact (MK_COMB (@lem4884506 A) (@lem4884505 A f u x)). Qed.
Lemma lem4884508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884509 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1121 A f u x) = (term1097 A f u x).
Proof. exact (MK_COMB (@lem4884508) (@lem4884507 A f u x)). Qed.
Lemma lem4884510 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1122 A f u x s) = (term1107 A f u s x).
Proof. exact (eq_refl (term1122 A f u x s)). Qed.
Lemma lem4884511 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1123 A f u x) = (term1109 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884510 A f u s x)). Qed.
Lemma lem4884512 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884513 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1124 A f u x) = (term1110 A f u x).
Proof. exact (MK_COMB (@lem4884512 A) (@lem4884511 A f u x)). Qed.
Lemma lem4884514 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1116 A f u x) = (term1111 A f u x).
Proof. exact (MK_COMB (@lem4884509 A f u x) (@lem4884513 A f u x)). Qed.
Lemma lem4884515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884516 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1125 A f u x) = (term1126 A f u x).
Proof. exact (MK_COMB (@lem4884515) (@lem4884514 A f u x)). Qed.
Lemma lem4884517 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1118 A f u x s) = (term1094 A f s u x).
Proof. exact (eq_refl (term1118 A f u x s)). Qed.
Lemma lem4884518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884519 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1127 A f u x s) = (term1128 A f s u x).
Proof. exact (MK_COMB (@lem4884518) (@lem4884517 A f s u x)). Qed.
Lemma lem4884520 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1122 A f u x s) = (term1107 A f u s x).
Proof. exact (eq_refl (term1122 A f u x s)). Qed.
Lemma lem4884521 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1129 A f u x s) = (term1130 A f u s x).
Proof. exact (MK_COMB (@lem4884519 A f s u x) (@lem4884520 A f u s x)). Qed.
Lemma lem4884522 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1131 A f u x) = (term1132 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884521 A f u s x)). Qed.
Lemma lem4884523 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884524 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1117 A f u x) = (term1133 A f u x).
Proof. exact (MK_COMB (@lem4884523 A) (@lem4884522 A f u x)). Qed.
Lemma lem4884525 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1116 A f u x) = (term1117 A f u x)) = ((term1111 A f u x) = (term1133 A f u x)).
Proof. exact (MK_COMB (@lem4884516 A f u x) (@lem4884524 A f u x)). Qed.
Lemma lem4884526 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1111 A f u x) = (term1133 A f u x).
Proof. exact (EQ_MP (@lem4884525 A f u x) (@lem4884503 A f u x)). Qed.
Lemma lem4884529 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1134 A f u x) = (term1134 A f u x).
Proof. exact (eq_refl (term1134 A f u x)). Qed.
Lemma lem4884530 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1134 A f u x) = ((term1111 A f u x) = (term1133 A f u x)).
Proof. exact (eq_refl (term1134 A f u x)). Qed.
Lemma lem4884531 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1135 A f u x) = (term1135 A f u x).
Proof. exact (eq_refl (term1135 A f u x)). Qed.
Lemma lem4884532 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1134 A f u x) = (term1134 A f u x)) = ((term1134 A f u x) = ((term1111 A f u x) = (term1133 A f u x))).
Proof. exact (MK_COMB (@lem4884531 A f u x) (@lem4884530 A f u x)). Qed.
Lemma lem4884533 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1134 A f u x) = ((term1111 A f u x) = (term1133 A f u x)).
Proof. exact (eq_refl (term1134 A f u x)). Qed.
Lemma lem4884534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884535 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1135 A f u x) = (term1136 A f u x).
Proof. exact (MK_COMB (@lem4884534) (@lem4884533 A f u x)). Qed.
Lemma lem4884536 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1111 A f u x) = (term1133 A f u x)) = ((term1111 A f u x) = (term1133 A f u x)).
Proof. exact (eq_refl ((term1111 A f u x) = (term1133 A f u x))). Qed.
Lemma lem4884537 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1134 A f u x) = ((term1111 A f u x) = (term1133 A f u x))) = (((term1111 A f u x) = (term1133 A f u x)) = ((term1111 A f u x) = (term1133 A f u x))).
Proof. exact (MK_COMB (@lem4884535 A f u x) (@lem4884536 A f u x)). Qed.
Lemma lem4884538 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1134 A f u x) = (term1134 A f u x)) = (((term1111 A f u x) = (term1133 A f u x)) = ((term1111 A f u x) = (term1133 A f u x))).
Proof. exact (TRANS (@lem4884532 A f u x) (@lem4884537 A f u x)). Qed.
Lemma lem4884539 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1111 A f u x) = (term1133 A f u x)) = ((term1111 A f u x) = (term1133 A f u x)).
Proof. exact (EQ_MP (@lem4884538 A f u x) (@lem4884529 A f u x)). Qed.
Lemma lem4884540 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1111 A f u x) = (term1133 A f u x).
Proof. exact (EQ_MP (@lem4884539 A f u x) (@lem4884526 A f u x)). Qed.
Lemma lem4884542 {A : Type'} (P : A -> Prop) (Q : Prop) : (term447 A P Q) = (term448 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4884543 {A : Type'} (P : type686 A) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (@lem4884542 (A -> Prop) P Q). Qed.
Lemma lem4884544 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1137 A f u s x) = (term1138 A f u s x).
Proof. exact (@lem4884543 A (term1093 A f s u x) (term1107 A f u s x)). Qed.
Lemma lem4884545 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1139 A f s u x t) = (term1091 A f s t u x).
Proof. exact (eq_refl (term1139 A f s u x t)). Qed.
Lemma lem4884546 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1140 A f s u x) = (term1093 A f s u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884545 A f s t u x)). Qed.
Lemma lem4884547 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884548 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1141 A f s u x) = (term1094 A f s u x).
Proof. exact (MK_COMB (@lem4884547 A) (@lem4884546 A f s u x)). Qed.
Lemma lem4884549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884550 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1142 A f s u x) = (term1128 A f s u x).
Proof. exact (MK_COMB (@lem4884549) (@lem4884548 A f s u x)). Qed.
Lemma lem4884551 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1107 A f u s x) = (term1107 A f u s x).
Proof. exact (eq_refl (term1107 A f u s x)). Qed.
Lemma lem4884552 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1137 A f u s x) = (term1130 A f u s x).
Proof. exact (MK_COMB (@lem4884550 A f s u x) (@lem4884551 A f u s x)). Qed.
Lemma lem4884553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884554 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1143 A f u s x) = (term1144 A f u s x).
Proof. exact (MK_COMB (@lem4884553) (@lem4884552 A f u s x)). Qed.
Lemma lem4884555 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1139 A f s u x t) = (term1091 A f s t u x).
Proof. exact (eq_refl (term1139 A f s u x t)). Qed.
Lemma lem4884556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884557 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1145 A f s u x t) = (term1146 A f s t u x).
Proof. exact (MK_COMB (@lem4884556) (@lem4884555 A f s t u x)). Qed.
Lemma lem4884558 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1107 A f u s x) = (term1107 A f u s x).
Proof. exact (eq_refl (term1107 A f u s x)). Qed.
Lemma lem4884559 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1147 A t f u s x) = (term1148 A t f u s x).
Proof. exact (MK_COMB (@lem4884557 A f s t u x) (@lem4884558 A f u s x)). Qed.
Lemma lem4884560 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1149 A f u s x) = (term1150 A f u s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884559 A t f u s x)). Qed.
Lemma lem4884561 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884562 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1138 A f u s x) = (term1151 A f u s x).
Proof. exact (MK_COMB (@lem4884561 A) (@lem4884560 A f u s x)). Qed.
Lemma lem4884563 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : ((term1137 A f u s x) = (term1138 A f u s x)) = ((term1130 A f u s x) = (term1151 A f u s x)).
Proof. exact (MK_COMB (@lem4884554 A f u s x) (@lem4884562 A f u s x)). Qed.
Lemma lem4884564 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1130 A f u s x) = (term1151 A f u s x).
Proof. exact (EQ_MP (@lem4884563 A f u s x) (@lem4884544 A f u s x)). Qed.
Lemma lem4884565 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1132 A f u x) = (term1152 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884564 A f u s x)). Qed.
Lemma lem4884566 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4884567 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1133 A f u x) = (term1153 A f u x).
Proof. exact (MK_COMB (@lem4884566 A) (@lem4884565 A f u x)). Qed.
Lemma lem4884568 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1111 A f u x) = (term1153 A f u x).
Proof. exact (TRANS (@lem4884540 A f u x) (@lem4884567 A f u x)). Qed.
Lemma lem4884570 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1064 A f u x) = (term1153 A f u x).
Proof. exact (TRANS (@lem4884499 A f u x) (@lem4884568 A f u x)). Qed.
Lemma lem4884571 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1023 A f u x) = (term1153 A f u x).
Proof. exact (TRANS (@lem4884243 A f u x) (@lem4884570 A f u x)). Qed.
Lemma lem4884572 {A : Type'} (f : type639 A) (u : type686 A) (x : A) (h1 : term1023 A f u x) : term1153 A f u x.
Proof. exact (EQ_MP (@lem4884571 A f u x) (@lem4883522 A f u x h1)). Qed.
Lemma lem4884573 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1151 A f u s x) : term1151 A f u s x.
Proof. exact (h1). Qed.
Lemma lem4884574 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1148 A t f u s x) : term1148 A t f u s x.
Proof. exact (h1). Qed.
Lemma lem4884575 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term598 A P t' f u.
Proof. exact (h1). Qed.
Lemma lem4884580 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884581 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884580 A Prop f x). Qed.
Lemma lem4884583 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4884581 A s x). Qed.
Lemma lem4884588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884589 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884588 (A -> Prop) Prop f x). Qed.
Lemma lem4884591 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4884589 A u s). Qed.
Lemma lem4884592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884593 {A : Type'} (u : type686 A) (s : A -> Prop) : (term351 A u s) = (term603 A u s).
Proof. exact (MK_COMB (@lem4884592) (@lem4884591 A u s)). Qed.
Lemma lem4884594 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term996 A u s x) = (term1154 A u s x).
Proof. exact (MK_COMB (@lem4884593 A u s) (@lem4884583 A s x)). Qed.
Lemma lem4884595 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884601 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884600 A Prop f x). Qed.
Lemma lem4884603 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4884601 A t x). Qed.
Lemma lem4884604 {A : Type'} (t : A -> Prop) (x : A) : (term396 A t x) = (term606 A t x).
Proof. exact (MK_COMB (@lem4884595) (@lem4884603 A t x)). Qed.
Lemma lem4884605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884612 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884613 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884612 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884614 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4884613 A f s). Qed.
Lemma lem4884615 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4884616 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4884614 A f s) (@lem4884615 A t)). Qed.
Lemma lem4884618 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884619 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884618 (A -> Prop) Prop f x). Qed.
Lemma lem4884620 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term602 A f s t).
Proof. exact (@lem4884619 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4884622 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term602 A f s t).
Proof. exact (TRANS (@lem4884616 A f s t) (@lem4884620 A f s t)). Qed.
Lemma lem4884623 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term607 A f s t) = (term608 A f s t).
Proof. exact (MK_COMB (@lem4884605) (@lem4884622 A f s t)). Qed.
Lemma lem4884624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884630 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884629 (A -> Prop) Prop f x). Qed.
Lemma lem4884632 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4884630 A u s). Qed.
Lemma lem4884633 {A : Type'} (u : type686 A) (s : A -> Prop) : (term381 A u s) = (term605 A u s).
Proof. exact (MK_COMB (@lem4884624) (@lem4884632 A u s)). Qed.
Lemma lem4884634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884635 {A : Type'} (u : type686 A) (s : A -> Prop) : (term411 A u s) = (term652 A u s).
Proof. exact (MK_COMB (@lem4884634) (@lem4884633 A u s)). Qed.
Lemma lem4884636 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term1025 A u f s t) = (term899 A u f s t).
Proof. exact (MK_COMB (@lem4884635 A u s) (@lem4884623 A f s t)). Qed.
Lemma lem4884637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884638 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term1027 A u f s t) = (term1155 A u f s t).
Proof. exact (MK_COMB (@lem4884637) (@lem4884636 A u f s t)). Qed.
Lemma lem4884639 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1029 A u f s t x) = (term1156 A u f s t x).
Proof. exact (MK_COMB (@lem4884638 A u f s t) (@lem4884604 A t x)). Qed.
Lemma lem4884640 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1036 A u f s x) = (term1157 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884639 A u f s t x)). Qed.
Lemma lem4884641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884642 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1037 A u f s x) = (term1158 A u f s x).
Proof. exact (MK_COMB (@lem4884641 A) (@lem4884640 A u f s x)). Qed.
Lemma lem4884643 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1043 A u f x) = (term1159 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4884642 A u f s x)). Qed.
Lemma lem4884644 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884645 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1044 A u f x) = (term1160 A u f x).
Proof. exact (MK_COMB (@lem4884644 A) (@lem4884643 A u f x)). Qed.
Lemma lem4884646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884647 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1055 A u f x) = (term1161 A u f x).
Proof. exact (MK_COMB (@lem4884646) (@lem4884645 A u f x)). Qed.
Lemma lem4884648 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1107 A f u s x) = (term1162 A f u s x).
Proof. exact (MK_COMB (@lem4884647 A u f x) (@lem4884594 A u s x)). Qed.
Lemma lem4884649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884655 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884654 A Prop f x). Qed.
Lemma lem4884657 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4884655 A t x). Qed.
Lemma lem4884658 {A : Type'} (t : A -> Prop) (x : A) : (term396 A t x) = (term606 A t x).
Proof. exact (MK_COMB (@lem4884649) (@lem4884657 A t x)). Qed.
Lemma lem4884659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884664 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884665 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884664 (A -> Prop) Prop f x). Qed.
Lemma lem4884667 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem4884665 A u t). Qed.
Lemma lem4884668 {A : Type'} (u : type686 A) (t : A -> Prop) : (term381 A u t) = (term605 A u t).
Proof. exact (MK_COMB (@lem4884659) (@lem4884667 A u t)). Qed.
Lemma lem4884669 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884670 {A : Type'} (u : type686 A) (t : A -> Prop) : (term411 A u t) = (term652 A u t).
Proof. exact (MK_COMB (@lem4884669) (@lem4884668 A u t)). Qed.
Lemma lem4884671 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1046 A u t x) = (term1163 A u t x).
Proof. exact (MK_COMB (@lem4884670 A u t) (@lem4884658 A t x)). Qed.
Lemma lem4884672 {A : Type'} (u : type686 A) (x : A) : (term1052 A u x) = (term1164 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884671 A u t x)). Qed.
Lemma lem4884673 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884674 {A : Type'} (u : type686 A) (x : A) : (term1053 A u x) = (term1165 A u x).
Proof. exact (MK_COMB (@lem4884673 A) (@lem4884672 A u x)). Qed.
Lemma lem4884679 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884680 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884679 A Prop f x). Qed.
Lemma lem4884682 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4884680 A t x). Qed.
Lemma lem4884689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884690 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884689 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884691 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4884690 A f s). Qed.
Lemma lem4884692 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4884693 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4884691 A f s) (@lem4884692 A t)). Qed.
Lemma lem4884695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884696 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884695 (A -> Prop) Prop f x). Qed.
Lemma lem4884697 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term602 A f s t).
Proof. exact (@lem4884696 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4884699 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term602 A f s t).
Proof. exact (TRANS (@lem4884693 A f s t) (@lem4884697 A f s t)). Qed.
Lemma lem4884704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884705 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884704 (A -> Prop) Prop f x). Qed.
Lemma lem4884707 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4884705 A u s). Qed.
Lemma lem4884708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884709 {A : Type'} (u : type686 A) (s : A -> Prop) : (term351 A u s) = (term603 A u s).
Proof. exact (MK_COMB (@lem4884708) (@lem4884707 A u s)). Qed.
Lemma lem4884710 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term352 A u f s t) = (term604 A u f s t).
Proof. exact (MK_COMB (@lem4884709 A u s) (@lem4884699 A f s t)). Qed.
Lemma lem4884711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884712 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term988 A u f s t) = (term1166 A u f s t).
Proof. exact (MK_COMB (@lem4884711) (@lem4884710 A u f s t)). Qed.
Lemma lem4884713 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term989 A u f s t x) = (term1167 A u f s t x).
Proof. exact (MK_COMB (@lem4884712 A u f s t) (@lem4884682 A t x)). Qed.
Lemma lem4884714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884715 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1089 A u f s t x) = (term1168 A u f s t x).
Proof. exact (MK_COMB (@lem4884714) (@lem4884713 A u f s t x)). Qed.
Lemma lem4884716 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1091 A f s t u x) = (term1169 A f s t u x).
Proof. exact (MK_COMB (@lem4884715 A u f s t x) (@lem4884674 A u x)). Qed.
Lemma lem4884717 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884718 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1146 A f s t u x) = (term1170 A f s t u x).
Proof. exact (MK_COMB (@lem4884717) (@lem4884716 A f s t u x)). Qed.
Lemma lem4884719 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1148 A t f u s x) = (term1171 A t f u s x).
Proof. exact (MK_COMB (@lem4884718 A f s t u x) (@lem4884648 A f u s x)). Qed.
Lemma lem4884720 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1148 A t f u s x) : term1171 A t f u s x.
Proof. exact (EQ_MP (@lem4884719 A t f u s x) (@lem4884574 A t f u s x h1)). Qed.
Lemma lem4884725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884726 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4884725 (type686 A) Prop f x). Qed.
Lemma lem4884728 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) u).
Proof. exact (@lem4884726 A (@FINITE (A -> Prop)) u). Qed.
Lemma lem4884733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884734 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884733 A Prop f x). Qed.
Lemma lem4884736 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4884734 A c x). Qed.
Lemma lem4884737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884743 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884742 A Prop f x). Qed.
Lemma lem4884745 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4884743 A t x). Qed.
Lemma lem4884746 {A : Type'} (t : A -> Prop) (x : A) : (term396 A t x) = (term606 A t x).
Proof. exact (MK_COMB (@lem4884737) (@lem4884745 A t x)). Qed.
Lemma lem4884747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884755 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884754 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884756 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4884755 A f c). Qed.
Lemma lem4884757 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4884758 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t).
Proof. exact (MK_COMB (@lem4884756 A f c) (@lem4884757 A t)). Qed.
Lemma lem4884760 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884761 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884760 (A -> Prop) Prop f x). Qed.
Lemma lem4884762 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t) = (term602 A f c t).
Proof. exact (@lem4884761 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) t). Qed.
Lemma lem4884764 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (term602 A f c t).
Proof. exact (TRANS (@lem4884758 A f c t) (@lem4884762 A f c t)). Qed.
Lemma lem4884765 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term607 A f c t) = (term608 A f c t).
Proof. exact (MK_COMB (@lem4884747) (@lem4884764 A f c t)). Qed.
Lemma lem4884766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884767 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term609 A f c t) = (term610 A f c t).
Proof. exact (MK_COMB (@lem4884766) (@lem4884765 A f c t)). Qed.
Lemma lem4884768 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term386 A f c t x) = (term611 A f c t x).
Proof. exact (MK_COMB (@lem4884767 A f c t) (@lem4884746 A t x)). Qed.
Lemma lem4884769 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term394 A f c x) = (term612 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884768 A f c t x)). Qed.
Lemma lem4884770 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884771 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term395 A f c x) = (term613 A f c x).
Proof. exact (MK_COMB (@lem4884770 A) (@lem4884769 A f c x)). Qed.
Lemma lem4884772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884773 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term398 A f c x) = (term614 A f c x).
Proof. exact (MK_COMB (@lem4884772) (@lem4884771 A f c x)). Qed.
Lemma lem4884774 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term400 A f c x) = (term615 A f c x).
Proof. exact (MK_COMB (@lem4884773 A f c x) (@lem4884736 A c x)). Qed.
Lemma lem4884775 {A : Type'} (f : type639 A) (c : A -> Prop) : (term423 A f c) = (term616 A f c).
Proof. exact (fun_ext (fun x : A => @lem4884774 A f c x)). Qed.
Lemma lem4884776 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4884777 {A : Type'} (f : type639 A) (c : A -> Prop) : (term438 A f c) = (term617 A f c).
Proof. exact (MK_COMB (@lem4884776 A) (@lem4884775 A f c)). Qed.
Lemma lem4884778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884784 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884783 A Prop f x). Qed.
Lemma lem4884786 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4884784 A c x). Qed.
Lemma lem4884787 {A : Type'} (c : A -> Prop) (x : A) : (term396 A c x) = (term606 A c x).
Proof. exact (MK_COMB (@lem4884778) (@lem4884786 A c x)). Qed.
Lemma lem4884796 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884797 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4884796 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4884798 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4884797 A t' c). Qed.
Lemma lem4884799 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4884800 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4884798 A t' c) (@lem4884799 A x)). Qed.
Lemma lem4884802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884803 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4884802 A (A -> Prop) f x). Qed.
Lemma lem4884804 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term618 A t' c x).
Proof. exact (@lem4884803 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4884805 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term618 A t' c x).
Proof. exact (TRANS (@lem4884800 A t' c x) (@lem4884804 A t' c x)). Qed.
Lemma lem4884806 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4884807 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term619 A t' c x).
Proof. exact (MK_COMB (@lem4884805 A t' c x) (@lem4884806 A x)). Qed.
Lemma lem4884809 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884810 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4884809 A Prop f x). Qed.
Lemma lem4884811 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term619 A t' c x) = (term620 A t' c x).
Proof. exact (@lem4884810 A (term618 A t' c x) x). Qed.
Lemma lem4884813 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term620 A t' c x).
Proof. exact (TRANS (@lem4884807 A t' c x) (@lem4884811 A t' c x)). Qed.
Lemma lem4884822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884823 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4884822 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4884824 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4884823 A t' c). Qed.
Lemma lem4884825 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4884826 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4884824 A t' c) (@lem4884825 A x)). Qed.
Lemma lem4884828 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884829 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4884828 A (A -> Prop) f x). Qed.
Lemma lem4884830 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term618 A t' c x).
Proof. exact (@lem4884829 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4884832 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term618 A t' c x).
Proof. exact (TRANS (@lem4884826 A t' c x) (@lem4884830 A t' c x)). Qed.
Lemma lem4884833 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (f c).
Proof. exact (eq_refl (f c)). Qed.
Lemma lem4884834 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term621 A f t' c x) = (term622 A f t' c x).
Proof. exact (MK_COMB (@lem4884833 A f c) (@lem4884832 A t' c x)). Qed.
Lemma lem4884836 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884837 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884836 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884838 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4884837 A f c). Qed.
Lemma lem4884839 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term618 A t' c x) = (term618 A t' c x).
Proof. exact (eq_refl (term618 A t' c x)). Qed.
Lemma lem4884840 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term622 A f t' c x) = (term623 A f t' c x).
Proof. exact (MK_COMB (@lem4884838 A f c) (@lem4884839 A t' c x)). Qed.
Lemma lem4884842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884843 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884842 (A -> Prop) Prop f x). Qed.
Lemma lem4884844 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term623 A f t' c x) = (term624 A f t' c x).
Proof. exact (@lem4884843 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) (term618 A t' c x)). Qed.
Lemma lem4884845 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term622 A f t' c x) = (term624 A f t' c x).
Proof. exact (TRANS (@lem4884840 A f t' c x) (@lem4884844 A f t' c x)). Qed.
Lemma lem4884846 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term621 A f t' c x) = (term624 A f t' c x).
Proof. exact (TRANS (@lem4884834 A f t' c x) (@lem4884845 A f t' c x)). Qed.
Lemma lem4884847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884848 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term625 A f t' c x) = (term626 A f t' c x).
Proof. exact (MK_COMB (@lem4884847) (@lem4884846 A f t' c x)). Qed.
Lemma lem4884849 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term627 A f t' c x) = (term628 A f t' c x).
Proof. exact (MK_COMB (@lem4884848 A f t' c x) (@lem4884813 A t' c x)). Qed.
Lemma lem4884850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884851 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term629 A f t' c x) = (term630 A f t' c x).
Proof. exact (MK_COMB (@lem4884850) (@lem4884849 A f t' c x)). Qed.
Lemma lem4884852 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term631 A f t' c x) = (term632 A f t' c x).
Proof. exact (MK_COMB (@lem4884851 A f t' c x) (@lem4884787 A c x)). Qed.
Lemma lem4884853 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term633 A f t' c) = (term634 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4884852 A f t' c x)). Qed.
Lemma lem4884854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4884855 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term635 A f t' c) = (term636 A f t' c).
Proof. exact (MK_COMB (@lem4884854 A) (@lem4884853 A f t' c)). Qed.
Lemma lem4884856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884857 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term637 A f t' c) = (term638 A f t' c).
Proof. exact (MK_COMB (@lem4884856) (@lem4884855 A f t' c)). Qed.
Lemma lem4884858 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term640 A t' f c).
Proof. exact (MK_COMB (@lem4884857 A f t' c) (@lem4884777 A f c)). Qed.
Lemma lem4884863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884864 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884863 (A -> Prop) Prop f x). Qed.
Lemma lem4884866 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (@I ((A -> Prop) -> Prop) P c').
Proof. exact (@lem4884864 A P c'). Qed.
Lemma lem4884867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884874 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884875 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884874 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884876 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4884875 A f c). Qed.
Lemma lem4884877 {A : Type'} (c' : A -> Prop) : c' = c'.
Proof. exact (eq_refl c'). Qed.
Lemma lem4884878 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c').
Proof. exact (MK_COMB (@lem4884876 A f c) (@lem4884877 A c')). Qed.
Lemma lem4884880 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884881 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884880 (A -> Prop) Prop f x). Qed.
Lemma lem4884882 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c') = (term602 A f c c').
Proof. exact (@lem4884881 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) c'). Qed.
Lemma lem4884884 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (term602 A f c c').
Proof. exact (TRANS (@lem4884878 A f c c') (@lem4884882 A f c c')). Qed.
Lemma lem4884885 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term607 A f c c') = (term608 A f c c').
Proof. exact (MK_COMB (@lem4884867) (@lem4884884 A f c c')). Qed.
Lemma lem4884886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884887 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term609 A f c c') = (term610 A f c c').
Proof. exact (MK_COMB (@lem4884886) (@lem4884885 A f c c')). Qed.
Lemma lem4884888 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term382 A f c P c') = (term641 A f c P c').
Proof. exact (MK_COMB (@lem4884887 A f c c') (@lem4884866 A P c')). Qed.
Lemma lem4884889 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term383 A f c P) = (term642 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4884888 A f c P c')). Qed.
Lemma lem4884890 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884891 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term384 A f c P) = (term643 A f c P).
Proof. exact (MK_COMB (@lem4884890 A) (@lem4884889 A f c P)). Qed.
Lemma lem4884892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884893 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term408 A f c P) = (term644 A f c P).
Proof. exact (MK_COMB (@lem4884892) (@lem4884891 A f c P)). Qed.
Lemma lem4884894 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term645 A P t' f c) = (term646 A P t' f c).
Proof. exact (MK_COMB (@lem4884893 A f c P) (@lem4884858 A t' f c)). Qed.
Lemma lem4884895 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4884900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884901 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4884900 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4884903 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4884901 A f c). Qed.
Lemma lem4884904 {A : Type'} (f : type639 A) (c : A -> Prop) : (term195 A f c) = (term647 A f c).
Proof. exact (MK_COMB (@lem4884895 A) (@lem4884903 A f c)). Qed.
Lemma lem4884906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884907 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4884906 (type686 A) Prop f x). Qed.
Lemma lem4884908 {A : Type'} (f : type639 A) (c : A -> Prop) : (term647 A f c) = (term648 A f c).
Proof. exact (@lem4884907 A (@FINITE (A -> Prop)) (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c)). Qed.
Lemma lem4884909 {A : Type'} (f : type639 A) (c : A -> Prop) : (term195 A f c) = (term648 A f c).
Proof. exact (TRANS (@lem4884904 A f c) (@lem4884908 A f c)). Qed.
Lemma lem4884910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884911 {A : Type'} (f : type639 A) (c : A -> Prop) : (term303 A f c) = (term649 A f c).
Proof. exact (MK_COMB (@lem4884910) (@lem4884909 A f c)). Qed.
Lemma lem4884912 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term650 A P t' f c) = (term651 A P t' f c).
Proof. exact (MK_COMB (@lem4884911 A f c) (@lem4884894 A P t' f c)). Qed.
Lemma lem4884913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4884918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4884919 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4884918 (A -> Prop) Prop f x). Qed.
Lemma lem4884921 {A : Type'} (u : type686 A) (c : A -> Prop) : (u c) = (@I ((A -> Prop) -> Prop) u c).
Proof. exact (@lem4884919 A u c). Qed.
Lemma lem4884922 {A : Type'} (u : type686 A) (c : A -> Prop) : (term381 A u c) = (term605 A u c).
Proof. exact (MK_COMB (@lem4884913) (@lem4884921 A u c)). Qed.
Lemma lem4884923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884924 {A : Type'} (u : type686 A) (c : A -> Prop) : (term411 A u c) = (term652 A u c).
Proof. exact (MK_COMB (@lem4884923) (@lem4884922 A u c)). Qed.
Lemma lem4884925 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term575 A u P t' f c) = (term653 A u P t' f c).
Proof. exact (MK_COMB (@lem4884924 A u c) (@lem4884912 A P t' f c)). Qed.
Lemma lem4884926 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term577 A u P t' f) = (term654 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4884925 A u P t' f c)). Qed.
Lemma lem4884927 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884928 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term579 A u P t' f) = (term655 A u P t' f).
Proof. exact (MK_COMB (@lem4884927 A) (@lem4884926 A u P t' f)). Qed.
Lemma lem4884929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884930 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term596 A u P t' f) = (term656 A u P t' f).
Proof. exact (MK_COMB (@lem4884929) (@lem4884928 A u P t' f)). Qed.
Lemma lem4884931 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) : (term598 A P t' f u) = (term657 A P t' f u).
Proof. exact (MK_COMB (@lem4884930 A u P t' f) (@lem4884728 A u)). Qed.
Lemma lem4884932 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term657 A P t' f u.
Proof. exact (EQ_MP (@lem4884931 A P t' f u) (@lem4884575 A P t' f u h1)). Qed.
Lemma lem4884934 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term655 A u P t' f.
Proof. exact (proj1 (@lem4884932 A P t' f u h1)). Qed.
Lemma lem4884935 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1169 A f s t u x.
Proof. exact (h1). Qed.
Lemma lem4884936 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1162 A f u s x.
Proof. exact (h1). Qed.
Lemma lem4884937 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1165 A u x.
Proof. exact (proj2 (@lem4884935 A f s t u x h1)). Qed.
Lemma lem4884938 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1167 A u f s t x.
Proof. exact (proj1 (@lem4884935 A f s t u x h1)). Qed.
Lemma lem4884940 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term604 A u f s t.
Proof. exact (proj1 (@lem4884938 A f s t u x h1)). Qed.
Lemma lem4884943 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1154 A u s x.
Proof. exact (proj2 (@lem4884936 A f u s x h1)). Qed.
Lemma lem4884944 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1160 A u f x.
Proof. exact (proj1 (@lem4884936 A f u s x h1)). Qed.
Lemma lem4884948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4884949 {A : Type'} (P : type686 A) (Q : Prop) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4884948 (A -> Prop) P Q). Qed.
Lemma lem4884950 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term663 A f c x).
Proof. exact (@lem4884949 A (term612 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4884951 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4884952 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term612 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884951 A f c t x)). Qed.
Lemma lem4884953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884954 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term613 A f c x).
Proof. exact (MK_COMB (@lem4884953 A) (@lem4884952 A f c x)). Qed.
Lemma lem4884955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884956 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term667 A f c x) = (term614 A f c x).
Proof. exact (MK_COMB (@lem4884955) (@lem4884954 A f c x)). Qed.
Lemma lem4884957 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4884958 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term615 A f c x).
Proof. exact (MK_COMB (@lem4884956 A f c x) (@lem4884957 A c x)). Qed.
Lemma lem4884959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884960 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term668 A f c x) = (term669 A f c x).
Proof. exact (MK_COMB (@lem4884959) (@lem4884958 A f c x)). Qed.
Lemma lem4884961 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4884962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4884963 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term670 A f c x t) = (term671 A f c t x).
Proof. exact (MK_COMB (@lem4884962) (@lem4884961 A f c t x)). Qed.
Lemma lem4884964 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4884965 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term672 A f t c x) = (term673 A f t c x).
Proof. exact (MK_COMB (@lem4884963 A f c t x) (@lem4884964 A c x)). Qed.
Lemma lem4884966 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term674 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4884965 A f t c x)). Qed.
Lemma lem4884967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4884968 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term663 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4884967 A) (@lem4884966 A f c x)). Qed.
Lemma lem4884969 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A f c x) = (term663 A f c x)) = ((term615 A f c x) = (term676 A f c x)).
Proof. exact (MK_COMB (@lem4884960 A f c x) (@lem4884968 A f c x)). Qed.
Lemma lem4884970 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term615 A f c x) = (term676 A f c x).
Proof. exact (EQ_MP (@lem4884969 A f c x) (@lem4884950 A f c x)). Qed.
Lemma lem4884971 {A : Type'} (f : type639 A) (c : A -> Prop) : (term616 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4884970 A f c x)). Qed.
Lemma lem4884972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4884973 {A : Type'} (f : type639 A) (c : A -> Prop) : (term617 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4884972 A) (@lem4884971 A f c)). Qed.
Lemma lem4884974 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term638 A f t' c) = (term638 A f t' c).
Proof. exact (eq_refl (term638 A f t' c)). Qed.
Lemma lem4884975 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4884974 A f t' c) (@lem4884973 A f c)). Qed.
Lemma lem4884977 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4884978 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (@lem4884977 A P Q). Qed.
Lemma lem4884979 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term681 A t' f c).
Proof. exact (@lem4884978 A (term634 A f t' c) (term677 A f c)). Qed.
Lemma lem4884980 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4884981 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term683 A f t' c) = (term634 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4884980 A f t' c x)). Qed.
Lemma lem4884982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4884983 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term684 A f t' c) = (term636 A f t' c).
Proof. exact (MK_COMB (@lem4884982 A) (@lem4884981 A f t' c)). Qed.
Lemma lem4884984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884985 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term685 A f t' c) = (term638 A f t' c).
Proof. exact (MK_COMB (@lem4884984) (@lem4884983 A f t' c)). Qed.
Lemma lem4884986 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4884987 {A : Type'} (f : type639 A) (c : A -> Prop) : (term687 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4884986 A f c x)). Qed.
Lemma lem4884988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4884989 {A : Type'} (f : type639 A) (c : A -> Prop) : (term688 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4884988 A) (@lem4884987 A f c)). Qed.
Lemma lem4884990 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4884985 A f t' c) (@lem4884989 A f c)). Qed.
Lemma lem4884991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4884992 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term689 A t' f c) = (term690 A t' f c).
Proof. exact (MK_COMB (@lem4884991) (@lem4884990 A t' f c)). Qed.
Lemma lem4884993 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4884994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4884995 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term691 A f t' c x) = (term692 A f t' c x).
Proof. exact (MK_COMB (@lem4884994) (@lem4884993 A f t' c x)). Qed.
Lemma lem4884996 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4884997 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term693 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4884995 A f t' c x) (@lem4884996 A f c x)). Qed.
Lemma lem4884998 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A t' f c) = (term696 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4884997 A t' f c x)). Qed.
Lemma lem4884999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885000 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A t' f c) = (term697 A t' f c).
Proof. exact (MK_COMB (@lem4884999 A) (@lem4884998 A t' f c)). Qed.
Lemma lem4885001 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term680 A t' f c) = (term681 A t' f c)) = ((term679 A t' f c) = (term697 A t' f c)).
Proof. exact (MK_COMB (@lem4884992 A t' f c) (@lem4885000 A t' f c)). Qed.
Lemma lem4885002 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term697 A t' f c).
Proof. exact (EQ_MP (@lem4885001 A t' f c) (@lem4884979 A t' f c)). Qed.
Lemma lem4885004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885005 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885004 (A -> Prop) P Q). Qed.
Lemma lem4885006 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term703 A t' f c x).
Proof. exact (@lem4885005 A (term632 A f t' c x) (term675 A f c x)). Qed.
Lemma lem4885007 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4885008 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term705 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885007 A f t c x)). Qed.
Lemma lem4885009 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885010 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term706 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4885009 A) (@lem4885008 A f c x)). Qed.
Lemma lem4885011 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4885012 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4885011 A f t' c x) (@lem4885010 A f c x)). Qed.
Lemma lem4885013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885014 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term707 A t' f c x) = (term708 A t' f c x).
Proof. exact (MK_COMB (@lem4885013) (@lem4885012 A t' f c x)). Qed.
Lemma lem4885015 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4885016 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4885017 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term709 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (MK_COMB (@lem4885016 A f t' c x) (@lem4885015 A f t c x)). Qed.
Lemma lem4885018 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885017 A t' f t c x)). Qed.
Lemma lem4885019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885020 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4885019 A) (@lem4885018 A t' f c x)). Qed.
Lemma lem4885021 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term702 A t' f c x) = (term703 A t' f c x)) = ((term694 A t' f c x) = (term713 A t' f c x)).
Proof. exact (MK_COMB (@lem4885014 A t' f c x) (@lem4885020 A t' f c x)). Qed.
Lemma lem4885022 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term694 A t' f c x) = (term713 A t' f c x).
Proof. exact (EQ_MP (@lem4885021 A t' f c x) (@lem4885006 A t' f c x)). Qed.
Lemma lem4885023 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885022 A t' f c x)). Qed.
Lemma lem4885024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885025 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4885024 A) (@lem4885023 A t' f c)). Qed.
Lemma lem4885026 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4885002 A t' f c) (@lem4885025 A t' f c)). Qed.
Lemma lem4885027 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4884975 A t' f c) (@lem4885026 A t' f c)). Qed.
Lemma lem4885028 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term644 A f c P) = (term644 A f c P).
Proof. exact (eq_refl (term644 A f c P)). Qed.
Lemma lem4885029 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4885028 A f c P) (@lem4885027 A t' f c)). Qed.
Lemma lem4885033 {A : Type'} (P : A -> Prop) (Q : Prop) : (term717 A P Q) = (term718 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4885034 {A : Type'} (P : type686 A) (Q : Prop) : (term719 A P Q) = (term720 A P Q).
Proof. exact (@lem4885033 (A -> Prop) P Q). Qed.
Lemma lem4885035 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term722 A P t' f c).
Proof. exact (@lem4885034 A (term642 A f c P) (term715 A t' f c)). Qed.
Lemma lem4885036 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4885037 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term724 A f c P) = (term642 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885036 A f c P c')). Qed.
Lemma lem4885038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885039 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term725 A f c P) = (term643 A f c P).
Proof. exact (MK_COMB (@lem4885038 A) (@lem4885037 A f c P)). Qed.
Lemma lem4885040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885041 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term726 A f c P) = (term644 A f c P).
Proof. exact (MK_COMB (@lem4885040) (@lem4885039 A f c P)). Qed.
Lemma lem4885042 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4885043 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4885041 A f c P) (@lem4885042 A t' f c)). Qed.
Lemma lem4885044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885045 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c) = (term728 A P t' f c).
Proof. exact (MK_COMB (@lem4885044) (@lem4885043 A P t' f c)). Qed.
Lemma lem4885046 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4885047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885048 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term729 A f c P c') = (term730 A f c P c').
Proof. exact (MK_COMB (@lem4885047) (@lem4885046 A f c P c')). Qed.
Lemma lem4885049 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4885050 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term731 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885048 A f c P c') (@lem4885049 A t' f c)). Qed.
Lemma lem4885051 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P t' f c) = (term734 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885050 A P c' t' f c)). Qed.
Lemma lem4885052 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885053 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term722 A P t' f c) = (term735 A P t' f c).
Proof. exact (MK_COMB (@lem4885052 A) (@lem4885051 A P t' f c)). Qed.
Lemma lem4885054 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term721 A P t' f c) = (term722 A P t' f c)) = ((term716 A P t' f c) = (term735 A P t' f c)).
Proof. exact (MK_COMB (@lem4885045 A P t' f c) (@lem4885053 A P t' f c)). Qed.
Lemma lem4885055 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term735 A P t' f c).
Proof. exact (EQ_MP (@lem4885054 A P t' f c) (@lem4885035 A P t' f c)). Qed.
Lemma lem4885057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4885057 A P Q). Qed.
Lemma lem4885059 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term737 A P c' t' f c).
Proof. exact (@lem4885058 A (term641 A f c P c') (term714 A t' f c)). Qed.
Lemma lem4885060 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4885061 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term739 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885060 A t' f c x)). Qed.
Lemma lem4885062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885063 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4885062 A) (@lem4885061 A t' f c)). Qed.
Lemma lem4885064 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885065 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885064 A f c P c') (@lem4885063 A t' f c)). Qed.
Lemma lem4885066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885067 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term742 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885066) (@lem4885065 A P c' t' f c)). Qed.
Lemma lem4885068 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4885069 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885070 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term743 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885069 A f c P c') (@lem4885068 A t' f c x)). Qed.
Lemma lem4885071 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term745 A P c' t' f c) = (term746 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885070 A P c' t' f c x)). Qed.
Lemma lem4885072 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885073 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885072 A) (@lem4885071 A P c' t' f c)). Qed.
Lemma lem4885074 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term736 A P c' t' f c) = (term737 A P c' t' f c)) = ((term732 A P c' t' f c) = (term747 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4885067 A P c' t' f c) (@lem4885073 A P c' t' f c)). Qed.
Lemma lem4885075 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (EQ_MP (@lem4885074 A P c' t' f c) (@lem4885059 A P c' t' f c)). Qed.
Lemma lem4885077 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885078 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885077 (A -> Prop) P Q). Qed.
Lemma lem4885079 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term749 A P c' t' f c x).
Proof. exact (@lem4885078 A (term641 A f c P c') (term712 A t' f c x)). Qed.
Lemma lem4885080 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4885081 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term751 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885080 A t' f t c x)). Qed.
Lemma lem4885082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885083 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4885082 A) (@lem4885081 A t' f c x)). Qed.
Lemma lem4885084 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885085 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885084 A f c P c') (@lem4885083 A t' f c x)). Qed.
Lemma lem4885086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885087 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term754 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885086) (@lem4885085 A P c' t' f c x)). Qed.
Lemma lem4885088 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4885089 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885090 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term755 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885089 A f c P c') (@lem4885088 A t' f t c x)). Qed.
Lemma lem4885091 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term757 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885090 A P c' t' f t c x)). Qed.
Lemma lem4885092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885093 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885092 A) (@lem4885091 A P c' t' f c x)). Qed.
Lemma lem4885094 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term748 A P c' t' f c x) = (term749 A P c' t' f c x)) = ((term744 A P c' t' f c x) = (term759 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885087 A P c' t' f c x) (@lem4885093 A P c' t' f c x)). Qed.
Lemma lem4885095 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4885094 A P c' t' f c x) (@lem4885079 A P c' t' f c x)). Qed.
Lemma lem4885096 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885095 A P c' t' f c x)). Qed.
Lemma lem4885097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885098 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885097 A) (@lem4885096 A P c' t' f c)). Qed.
Lemma lem4885099 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (TRANS (@lem4885075 A P c' t' f c) (@lem4885098 A P c' t' f c)). Qed.
Lemma lem4885100 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885099 A P c' t' f c)). Qed.
Lemma lem4885101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885102 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4885101 A) (@lem4885100 A P t' f c)). Qed.
Lemma lem4885103 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4885055 A P t' f c) (@lem4885102 A P t' f c)). Qed.
Lemma lem4885104 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4885029 A P t' f c) (@lem4885103 A P t' f c)). Qed.
Lemma lem4885105 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885106 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4885105 A f c) (@lem4885104 A P t' f c)). Qed.
Lemma lem4885108 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885109 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885108 (A -> Prop) P Q). Qed.
Lemma lem4885110 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term766 A P t' f c).
Proof. exact (@lem4885109 A (term648 A f c) (term762 A P t' f c)). Qed.
Lemma lem4885111 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4885112 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term768 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885111 A P c' t' f c)). Qed.
Lemma lem4885113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885114 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term769 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4885113 A) (@lem4885112 A P t' f c)). Qed.
Lemma lem4885115 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885116 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4885115 A f c) (@lem4885114 A P t' f c)). Qed.
Lemma lem4885117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885118 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A P t' f c) = (term771 A P t' f c).
Proof. exact (MK_COMB (@lem4885117) (@lem4885116 A P t' f c)). Qed.
Lemma lem4885119 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4885120 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885121 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885120 A f c) (@lem4885119 A P c' t' f c)). Qed.
Lemma lem4885122 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term775 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885121 A P c' t' f c)). Qed.
Lemma lem4885123 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885124 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term766 A P t' f c) = (term776 A P t' f c).
Proof. exact (MK_COMB (@lem4885123 A) (@lem4885122 A P t' f c)). Qed.
Lemma lem4885125 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term765 A P t' f c) = (term766 A P t' f c)) = ((term764 A P t' f c) = (term776 A P t' f c)).
Proof. exact (MK_COMB (@lem4885118 A P t' f c) (@lem4885124 A P t' f c)). Qed.
Lemma lem4885126 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term776 A P t' f c).
Proof. exact (EQ_MP (@lem4885125 A P t' f c) (@lem4885110 A P t' f c)). Qed.
Lemma lem4885128 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885129 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4885128 A P Q). Qed.
Lemma lem4885130 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term778 A P c' t' f c).
Proof. exact (@lem4885129 A (term648 A f c) (term760 A P c' t' f c)). Qed.
Lemma lem4885131 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4885132 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885131 A P c' t' f c x)). Qed.
Lemma lem4885133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885134 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885133 A) (@lem4885132 A P c' t' f c)). Qed.
Lemma lem4885135 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885136 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885135 A f c) (@lem4885134 A P c' t' f c)). Qed.
Lemma lem4885137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885138 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A P c' t' f c) = (term783 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885137) (@lem4885136 A P c' t' f c)). Qed.
Lemma lem4885139 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4885140 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885141 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885140 A f c) (@lem4885139 A P c' t' f c x)). Qed.
Lemma lem4885142 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term787 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885141 A P c' t' f c x)). Qed.
Lemma lem4885143 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885144 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885143 A) (@lem4885142 A P c' t' f c)). Qed.
Lemma lem4885145 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term777 A P c' t' f c) = (term778 A P c' t' f c)) = ((term773 A P c' t' f c) = (term788 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4885138 A P c' t' f c) (@lem4885144 A P c' t' f c)). Qed.
Lemma lem4885146 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (EQ_MP (@lem4885145 A P c' t' f c) (@lem4885130 A P c' t' f c)). Qed.
Lemma lem4885148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885149 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885148 (A -> Prop) P Q). Qed.
Lemma lem4885150 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term790 A P c' t' f c x).
Proof. exact (@lem4885149 A (term648 A f c) (term758 A P c' t' f c x)). Qed.
Lemma lem4885151 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4885152 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term792 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885151 A P c' t' f t c x)). Qed.
Lemma lem4885153 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885154 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term793 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885153 A) (@lem4885152 A P c' t' f c x)). Qed.
Lemma lem4885155 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885156 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885155 A f c) (@lem4885154 A P c' t' f c x)). Qed.
Lemma lem4885157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885158 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A P c' t' f c x) = (term795 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885157) (@lem4885156 A P c' t' f c x)). Qed.
Lemma lem4885159 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4885160 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885161 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885160 A f c) (@lem4885159 A P c' t' f t c x)). Qed.
Lemma lem4885162 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885161 A P c' t' f t c x)). Qed.
Lemma lem4885163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885164 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885163 A) (@lem4885162 A P c' t' f c x)). Qed.
Lemma lem4885165 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term789 A P c' t' f c x) = (term790 A P c' t' f c x)) = ((term785 A P c' t' f c x) = (term800 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885158 A P c' t' f c x) (@lem4885164 A P c' t' f c x)). Qed.
Lemma lem4885166 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term785 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4885165 A P c' t' f c x) (@lem4885150 A P c' t' f c x)). Qed.
Lemma lem4885167 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885166 A P c' t' f c x)). Qed.
Lemma lem4885168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885169 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term788 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885168 A) (@lem4885167 A P c' t' f c)). Qed.
Lemma lem4885170 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (TRANS (@lem4885146 A P c' t' f c) (@lem4885169 A P c' t' f c)). Qed.
Lemma lem4885171 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885170 A P c' t' f c)). Qed.
Lemma lem4885172 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885173 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term776 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4885172 A) (@lem4885171 A P t' f c)). Qed.
Lemma lem4885174 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4885126 A P t' f c) (@lem4885173 A P t' f c)). Qed.
Lemma lem4885175 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4885106 A P t' f c) (@lem4885174 A P t' f c)). Qed.
Lemma lem4885176 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885177 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4885176 A u c) (@lem4885175 A P t' f c)). Qed.
Lemma lem4885179 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885180 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4885179 (A -> Prop) P Q). Qed.
Lemma lem4885181 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term811 A u P t' f c).
Proof. exact (@lem4885180 A (term605 A u c) (term803 A P t' f c)). Qed.
Lemma lem4885182 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4885183 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term813 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885182 A P c' t' f c)). Qed.
Lemma lem4885184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885185 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term814 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4885184 A) (@lem4885183 A P t' f c)). Qed.
Lemma lem4885186 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885187 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4885186 A u c) (@lem4885185 A P t' f c)). Qed.
Lemma lem4885188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885189 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term815 A u P t' f c) = (term816 A u P t' f c).
Proof. exact (MK_COMB (@lem4885188) (@lem4885187 A u P t' f c)). Qed.
Lemma lem4885190 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4885191 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885192 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term817 A u P t' f c c') = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885191 A u c) (@lem4885190 A P c' t' f c)). Qed.
Lemma lem4885193 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term819 A u P t' f c) = (term820 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885192 A u P c' t' f c)). Qed.
Lemma lem4885194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885195 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term811 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (MK_COMB (@lem4885194 A) (@lem4885193 A u P t' f c)). Qed.
Lemma lem4885196 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term810 A u P t' f c) = (term811 A u P t' f c)) = ((term805 A u P t' f c) = (term821 A u P t' f c)).
Proof. exact (MK_COMB (@lem4885189 A u P t' f c) (@lem4885195 A u P t' f c)). Qed.
Lemma lem4885197 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (EQ_MP (@lem4885196 A u P t' f c) (@lem4885181 A u P t' f c)). Qed.
Lemma lem4885199 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885200 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (@lem4885199 A P Q). Qed.
Lemma lem4885201 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term823 A u P c' t' f c).
Proof. exact (@lem4885200 A (term605 A u c) (term801 A P c' t' f c)). Qed.
Lemma lem4885202 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4885203 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term825 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885202 A P c' t' f c x)). Qed.
Lemma lem4885204 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885205 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term826 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885204 A) (@lem4885203 A P c' t' f c)). Qed.
Lemma lem4885206 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885207 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885206 A u c) (@lem4885205 A P c' t' f c)). Qed.
Lemma lem4885208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885209 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term827 A u P c' t' f c) = (term828 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885208) (@lem4885207 A u P c' t' f c)). Qed.
Lemma lem4885210 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4885211 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885212 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term829 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885211 A u c) (@lem4885210 A P c' t' f c x)). Qed.
Lemma lem4885213 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term831 A u P c' t' f c) = (term832 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885212 A u P c' t' f c x)). Qed.
Lemma lem4885214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885215 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term823 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885214 A) (@lem4885213 A u P c' t' f c)). Qed.
Lemma lem4885216 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term822 A u P c' t' f c) = (term823 A u P c' t' f c)) = ((term818 A u P c' t' f c) = (term833 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4885209 A u P c' t' f c) (@lem4885215 A u P c' t' f c)). Qed.
Lemma lem4885217 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4885216 A u P c' t' f c) (@lem4885201 A u P c' t' f c)). Qed.
Lemma lem4885219 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885220 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4885219 (A -> Prop) P Q). Qed.
Lemma lem4885221 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term835 A u P c' t' f c x).
Proof. exact (@lem4885220 A (term605 A u c) (term799 A P c' t' f c x)). Qed.
Lemma lem4885222 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4885223 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term837 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885222 A P c' t' f t c x)). Qed.
Lemma lem4885224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885225 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term838 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885224 A) (@lem4885223 A P c' t' f c x)). Qed.
Lemma lem4885226 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885227 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885226 A u c) (@lem4885225 A P c' t' f c x)). Qed.
Lemma lem4885228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885229 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term839 A u P c' t' f c x) = (term840 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885228) (@lem4885227 A u P c' t' f c x)). Qed.
Lemma lem4885230 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4885231 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885232 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term841 A u P c' t' f c x t) = (term842 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885231 A u c) (@lem4885230 A P c' t' f t c x)). Qed.
Lemma lem4885233 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term843 A u P c' t' f c x) = (term844 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885232 A u P c' t' f t c x)). Qed.
Lemma lem4885234 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885235 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term835 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885234 A) (@lem4885233 A u P c' t' f c x)). Qed.
Lemma lem4885236 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term834 A u P c' t' f c x) = (term835 A u P c' t' f c x)) = ((term830 A u P c' t' f c x) = (term845 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885229 A u P c' t' f c x) (@lem4885235 A u P c' t' f c x)). Qed.
Lemma lem4885237 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term830 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4885236 A u P c' t' f c x) (@lem4885221 A u P c' t' f c x)). Qed.
Lemma lem4885238 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term832 A u P c' t' f c) = (term846 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885237 A u P c' t' f c x)). Qed.
Lemma lem4885239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885240 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term833 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885239 A) (@lem4885238 A u P c' t' f c)). Qed.
Lemma lem4885241 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (TRANS (@lem4885217 A u P c' t' f c) (@lem4885240 A u P c' t' f c)). Qed.
Lemma lem4885242 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term820 A u P t' f c) = (term848 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885241 A u P c' t' f c)). Qed.
Lemma lem4885243 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885244 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term821 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (MK_COMB (@lem4885243 A) (@lem4885242 A u P t' f c)). Qed.
Lemma lem4885245 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4885197 A u P t' f c) (@lem4885244 A u P t' f c)). Qed.
Lemma lem4885246 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4885177 A u P t' f c) (@lem4885245 A u P t' f c)). Qed.
Lemma lem4885247 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term654 A u P t' f) = (term850 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4885246 A u P t' f c)). Qed.
Lemma lem4885248 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885249 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term655 A u P t' f) = (term851 A u P t' f).
Proof. exact (MK_COMB (@lem4885248 A) (@lem4885247 A u P t' f)). Qed.
Lemma lem4885262 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term673 A f t c x) = (term673 A f t c x).
Proof. exact (eq_refl (term673 A f t c x)). Qed.
Lemma lem4885279 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term632 A f t' c x) = (term852 A f t' c x).
Proof. exact (@lem19699 (term624 A f t' c x) (term620 A t' c x) (term606 A c x)). Qed.
Lemma lem4885280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885281 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term853 A f t' c x).
Proof. exact (MK_COMB (@lem4885280) (@lem4885279 A f t' c x)). Qed.
Lemma lem4885282 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f t c x) = (term854 A t' f t c x).
Proof. exact (MK_COMB (@lem4885281 A f t' c x) (@lem4885262 A f t c x)). Qed.
Lemma lem4885291 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885292 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f t c x) = (term855 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885291 A f c P c') (@lem4885282 A t' f t c x)). Qed.
Lemma lem4885295 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885296 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term797 A P c' t' f t c x) = (term856 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885295 A f c) (@lem4885292 A P c' t' f t c x)). Qed.
Lemma lem4885299 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885300 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term857 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885299 A u c) (@lem4885296 A P c' t' f t c x)). Qed.
Lemma lem4885301 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term858 A u P c' t' f t c x).
Proof. exact (@lem19490 (term648 A f c) (term605 A u c) (term855 A P c' t' f t c x)). Qed.
Lemma lem4885302 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term860 A P c' u t' f t c x).
Proof. exact (@lem19490 (term641 A f c P c') (term605 A u c) (term854 A t' f t c x)). Qed.
Lemma lem4885303 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term862 A t' u f t c x).
Proof. exact (@lem19490 (term852 A f t' c x) (term605 A u c) (term673 A f t c x)). Qed.
Lemma lem4885304 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term863 A u f t c x) = (term863 A u f t c x).
Proof. exact (eq_refl (term863 A u f t c x)). Qed.
Lemma lem4885311 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term864 A u f t' c x) = (term865 A f u t' c x).
Proof. exact (@lem19490 (term866 A f t' c x) (term605 A u c) (term867 A t' c x)). Qed.
Lemma lem4885312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885313 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term868 A u f t' c x) = (term869 A f u t' c x).
Proof. exact (MK_COMB (@lem4885312) (@lem4885311 A f u t' c x)). Qed.
Lemma lem4885314 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term862 A t' u f t c x) = (term870 A t' u f t c x).
Proof. exact (MK_COMB (@lem4885313 A f u t' c x) (@lem4885304 A u f t c x)). Qed.
Lemma lem4885315 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term870 A t' u f t c x).
Proof. exact (TRANS (@lem4885303 A t' u f t c x) (@lem4885314 A t' u f t c x)). Qed.
Lemma lem4885318 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term871 A u f c P c') = (term871 A u f c P c').
Proof. exact (eq_refl (term871 A u f c P c')). Qed.
Lemma lem4885319 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term860 A P c' u t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4885318 A u f c P c') (@lem4885315 A t' u f t c x)). Qed.
Lemma lem4885320 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885302 A P c' u t' f t c x) (@lem4885319 A P c' t' u f t c x)). Qed.
Lemma lem4885323 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term873 A u f c) = (term873 A u f c).
Proof. exact (eq_refl (term873 A u f c)). Qed.
Lemma lem4885324 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term858 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4885323 A u f c) (@lem4885320 A P c' t' u f t c x)). Qed.
Lemma lem4885325 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885301 A u P c' t' f t c x) (@lem4885324 A P c' t' u f t c x)). Qed.
Lemma lem4885326 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885300 A u P c' t' f t c x) (@lem4885325 A P c' t' u f t c x)). Qed.
Lemma lem4885327 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term844 A u P c' t' f c x) = (term875 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885326 A P c' t' u f t c x)). Qed.
Lemma lem4885328 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885329 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term845 A u P c' t' f c x) = (term876 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4885328 A) (@lem4885327 A P c' t' u f c x)). Qed.
Lemma lem4885330 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term846 A u P c' t' f c) = (term877 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4885329 A P c' t' u f c x)). Qed.
Lemma lem4885331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885332 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term847 A u P c' t' f c) = (term878 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4885331 A) (@lem4885330 A P c' t' u f c)). Qed.
Lemma lem4885333 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term848 A u P t' f c) = (term879 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885332 A P c' t' u f c)). Qed.
Lemma lem4885334 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885335 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term849 A u P t' f c) = (term880 A P t' u f c).
Proof. exact (MK_COMB (@lem4885334 A) (@lem4885333 A P t' u f c)). Qed.
Lemma lem4885336 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term850 A u P t' f) = (term881 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4885335 A P t' u f c)). Qed.
Lemma lem4885337 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885338 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term851 A u P t' f) = (term882 A P t' u f).
Proof. exact (MK_COMB (@lem4885337 A) (@lem4885336 A P t' u f)). Qed.
Lemma lem4885339 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term655 A u P t' f) = (term882 A P t' u f).
Proof. exact (TRANS (@lem4885249 A u P t' f) (@lem4885338 A P t' u f)). Qed.
Lemma lem4885340 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term882 A P t' u f.
Proof. exact (EQ_MP (@lem4885339 A P t' u f) (@lem4884934 A P t' f u h1)). Qed.
Lemma lem4885352 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1163 A u t x) = (term1163 A u t x).
Proof. exact (eq_refl (term1163 A u t x)). Qed.
Lemma lem4885353 {A : Type'} (u : type686 A) (x : A) : (term1164 A u x) = (term1164 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885352 A u t x)). Qed.
Lemma lem4885354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885356 {A : Type'} (u : type686 A) (x : A) : (term1165 A u x) = (term1165 A u x).
Proof. exact (MK_COMB (@lem4885354 A) (@lem4885353 A u x)). Qed.
Lemma lem4885357 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1165 A u x.
Proof. exact (EQ_MP (@lem4885356 A u x) (@lem4884937 A f s t u x h1)). Qed.
Lemma lem4885371 {A : Type'} (P : A -> Prop) (Q : Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4885372 {A : Type'} (P : type686 A) (Q : Prop) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4885371 (A -> Prop) P Q). Qed.
Lemma lem4885373 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term663 A f c x).
Proof. exact (@lem4885372 A (term612 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4885374 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4885375 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term612 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885374 A f c t x)). Qed.
Lemma lem4885376 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885377 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term613 A f c x).
Proof. exact (MK_COMB (@lem4885376 A) (@lem4885375 A f c x)). Qed.
Lemma lem4885378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4885379 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term667 A f c x) = (term614 A f c x).
Proof. exact (MK_COMB (@lem4885378) (@lem4885377 A f c x)). Qed.
Lemma lem4885380 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4885381 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term662 A f c x) = (term615 A f c x).
Proof. exact (MK_COMB (@lem4885379 A f c x) (@lem4885380 A c x)). Qed.
Lemma lem4885382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885383 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term668 A f c x) = (term669 A f c x).
Proof. exact (MK_COMB (@lem4885382) (@lem4885381 A f c x)). Qed.
Lemma lem4885384 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term664 A f c x t) = (term611 A f c t x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4885385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4885386 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term670 A f c x t) = (term671 A f c t x).
Proof. exact (MK_COMB (@lem4885385) (@lem4885384 A f c t x)). Qed.
Lemma lem4885387 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4885388 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term672 A f t c x) = (term673 A f t c x).
Proof. exact (MK_COMB (@lem4885386 A f c t x) (@lem4885387 A c x)). Qed.
Lemma lem4885389 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term674 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885388 A f t c x)). Qed.
Lemma lem4885390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885391 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term663 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4885390 A) (@lem4885389 A f c x)). Qed.
Lemma lem4885392 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A f c x) = (term663 A f c x)) = ((term615 A f c x) = (term676 A f c x)).
Proof. exact (MK_COMB (@lem4885383 A f c x) (@lem4885391 A f c x)). Qed.
Lemma lem4885393 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term615 A f c x) = (term676 A f c x).
Proof. exact (EQ_MP (@lem4885392 A f c x) (@lem4885373 A f c x)). Qed.
Lemma lem4885394 {A : Type'} (f : type639 A) (c : A -> Prop) : (term616 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4885393 A f c x)). Qed.
Lemma lem4885395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885396 {A : Type'} (f : type639 A) (c : A -> Prop) : (term617 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4885395 A) (@lem4885394 A f c)). Qed.
Lemma lem4885397 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term638 A f t' c) = (term638 A f t' c).
Proof. exact (eq_refl (term638 A f t' c)). Qed.
Lemma lem4885398 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4885397 A f t' c) (@lem4885396 A f c)). Qed.
Lemma lem4885400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4885401 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term418 A P Q).
Proof. exact (@lem4885400 A P Q). Qed.
Lemma lem4885402 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term681 A t' f c).
Proof. exact (@lem4885401 A (term634 A f t' c) (term677 A f c)). Qed.
Lemma lem4885403 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4885404 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term683 A f t' c) = (term634 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4885403 A f t' c x)). Qed.
Lemma lem4885405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885406 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term684 A f t' c) = (term636 A f t' c).
Proof. exact (MK_COMB (@lem4885405 A) (@lem4885404 A f t' c)). Qed.
Lemma lem4885407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885408 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term685 A f t' c) = (term638 A f t' c).
Proof. exact (MK_COMB (@lem4885407) (@lem4885406 A f t' c)). Qed.
Lemma lem4885409 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4885410 {A : Type'} (f : type639 A) (c : A -> Prop) : (term687 A f c) = (term677 A f c).
Proof. exact (fun_ext (fun x : A => @lem4885409 A f c x)). Qed.
Lemma lem4885411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885412 {A : Type'} (f : type639 A) (c : A -> Prop) : (term688 A f c) = (term678 A f c).
Proof. exact (MK_COMB (@lem4885411 A) (@lem4885410 A f c)). Qed.
Lemma lem4885413 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term680 A t' f c) = (term679 A t' f c).
Proof. exact (MK_COMB (@lem4885408 A f t' c) (@lem4885412 A f c)). Qed.
Lemma lem4885414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885415 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term689 A t' f c) = (term690 A t' f c).
Proof. exact (MK_COMB (@lem4885414) (@lem4885413 A t' f c)). Qed.
Lemma lem4885416 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term682 A f t' c x) = (term632 A f t' c x).
Proof. exact (eq_refl (term682 A f t' c x)). Qed.
Lemma lem4885417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885418 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term691 A f t' c x) = (term692 A f t' c x).
Proof. exact (MK_COMB (@lem4885417) (@lem4885416 A f t' c x)). Qed.
Lemma lem4885419 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term686 A f c x) = (term676 A f c x).
Proof. exact (eq_refl (term686 A f c x)). Qed.
Lemma lem4885420 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term693 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4885418 A f t' c x) (@lem4885419 A f c x)). Qed.
Lemma lem4885421 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A t' f c) = (term696 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885420 A t' f c x)). Qed.
Lemma lem4885422 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885423 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A t' f c) = (term697 A t' f c).
Proof. exact (MK_COMB (@lem4885422 A) (@lem4885421 A t' f c)). Qed.
Lemma lem4885424 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term680 A t' f c) = (term681 A t' f c)) = ((term679 A t' f c) = (term697 A t' f c)).
Proof. exact (MK_COMB (@lem4885415 A t' f c) (@lem4885423 A t' f c)). Qed.
Lemma lem4885425 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term697 A t' f c).
Proof. exact (EQ_MP (@lem4885424 A t' f c) (@lem4885402 A t' f c)). Qed.
Lemma lem4885427 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885428 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885427 (A -> Prop) P Q). Qed.
Lemma lem4885429 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term703 A t' f c x).
Proof. exact (@lem4885428 A (term632 A f t' c x) (term675 A f c x)). Qed.
Lemma lem4885430 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4885431 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term705 A f c x) = (term675 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885430 A f t c x)). Qed.
Lemma lem4885432 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885433 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term706 A f c x) = (term676 A f c x).
Proof. exact (MK_COMB (@lem4885432 A) (@lem4885431 A f c x)). Qed.
Lemma lem4885434 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4885435 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term702 A t' f c x) = (term694 A t' f c x).
Proof. exact (MK_COMB (@lem4885434 A f t' c x) (@lem4885433 A f c x)). Qed.
Lemma lem4885436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885437 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term707 A t' f c x) = (term708 A t' f c x).
Proof. exact (MK_COMB (@lem4885436) (@lem4885435 A t' f c x)). Qed.
Lemma lem4885438 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term704 A f c x t) = (term673 A f t c x).
Proof. exact (eq_refl (term704 A f c x t)). Qed.
Lemma lem4885439 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term692 A f t' c x).
Proof. exact (eq_refl (term692 A f t' c x)). Qed.
Lemma lem4885440 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term709 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (MK_COMB (@lem4885439 A f t' c x) (@lem4885438 A f t c x)). Qed.
Lemma lem4885441 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885440 A t' f t c x)). Qed.
Lemma lem4885442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885443 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4885442 A) (@lem4885441 A t' f c x)). Qed.
Lemma lem4885444 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term702 A t' f c x) = (term703 A t' f c x)) = ((term694 A t' f c x) = (term713 A t' f c x)).
Proof. exact (MK_COMB (@lem4885437 A t' f c x) (@lem4885443 A t' f c x)). Qed.
Lemma lem4885445 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term694 A t' f c x) = (term713 A t' f c x).
Proof. exact (EQ_MP (@lem4885444 A t' f c x) (@lem4885429 A t' f c x)). Qed.
Lemma lem4885446 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885445 A t' f c x)). Qed.
Lemma lem4885447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885448 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4885447 A) (@lem4885446 A t' f c)). Qed.
Lemma lem4885449 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term679 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4885425 A t' f c) (@lem4885448 A t' f c)). Qed.
Lemma lem4885450 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term715 A t' f c).
Proof. exact (TRANS (@lem4885398 A t' f c) (@lem4885449 A t' f c)). Qed.
Lemma lem4885451 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term644 A f c P) = (term644 A f c P).
Proof. exact (eq_refl (term644 A f c P)). Qed.
Lemma lem4885452 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4885451 A f c P) (@lem4885450 A t' f c)). Qed.
Lemma lem4885456 {A : Type'} (P : A -> Prop) (Q : Prop) : (term717 A P Q) = (term718 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4885457 {A : Type'} (P : type686 A) (Q : Prop) : (term719 A P Q) = (term720 A P Q).
Proof. exact (@lem4885456 (A -> Prop) P Q). Qed.
Lemma lem4885458 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term722 A P t' f c).
Proof. exact (@lem4885457 A (term642 A f c P) (term715 A t' f c)). Qed.
Lemma lem4885459 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4885460 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term724 A f c P) = (term642 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885459 A f c P c')). Qed.
Lemma lem4885461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885462 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term725 A f c P) = (term643 A f c P).
Proof. exact (MK_COMB (@lem4885461 A) (@lem4885460 A f c P)). Qed.
Lemma lem4885463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885464 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term726 A f c P) = (term644 A f c P).
Proof. exact (MK_COMB (@lem4885463) (@lem4885462 A f c P)). Qed.
Lemma lem4885465 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4885466 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term721 A P t' f c) = (term716 A P t' f c).
Proof. exact (MK_COMB (@lem4885464 A f c P) (@lem4885465 A t' f c)). Qed.
Lemma lem4885467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885468 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c) = (term728 A P t' f c).
Proof. exact (MK_COMB (@lem4885467) (@lem4885466 A P t' f c)). Qed.
Lemma lem4885469 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term723 A f c P c') = (term641 A f c P c').
Proof. exact (eq_refl (term723 A f c P c')). Qed.
Lemma lem4885470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885471 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term729 A f c P c') = (term730 A f c P c').
Proof. exact (MK_COMB (@lem4885470) (@lem4885469 A f c P c')). Qed.
Lemma lem4885472 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term715 A t' f c) = (term715 A t' f c).
Proof. exact (eq_refl (term715 A t' f c)). Qed.
Lemma lem4885473 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term731 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885471 A f c P c') (@lem4885472 A t' f c)). Qed.
Lemma lem4885474 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P t' f c) = (term734 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885473 A P c' t' f c)). Qed.
Lemma lem4885475 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885476 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term722 A P t' f c) = (term735 A P t' f c).
Proof. exact (MK_COMB (@lem4885475 A) (@lem4885474 A P t' f c)). Qed.
Lemma lem4885477 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term721 A P t' f c) = (term722 A P t' f c)) = ((term716 A P t' f c) = (term735 A P t' f c)).
Proof. exact (MK_COMB (@lem4885468 A P t' f c) (@lem4885476 A P t' f c)). Qed.
Lemma lem4885478 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term735 A P t' f c).
Proof. exact (EQ_MP (@lem4885477 A P t' f c) (@lem4885458 A P t' f c)). Qed.
Lemma lem4885480 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885481 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4885480 A P Q). Qed.
Lemma lem4885482 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term737 A P c' t' f c).
Proof. exact (@lem4885481 A (term641 A f c P c') (term714 A t' f c)). Qed.
Lemma lem4885483 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4885484 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term739 A t' f c) = (term714 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885483 A t' f c x)). Qed.
Lemma lem4885485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885486 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A t' f c) = (term715 A t' f c).
Proof. exact (MK_COMB (@lem4885485 A) (@lem4885484 A t' f c)). Qed.
Lemma lem4885487 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885488 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P c' t' f c) = (term732 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885487 A f c P c') (@lem4885486 A t' f c)). Qed.
Lemma lem4885489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885490 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term742 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885489) (@lem4885488 A P c' t' f c)). Qed.
Lemma lem4885491 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term738 A t' f c x) = (term713 A t' f c x).
Proof. exact (eq_refl (term738 A t' f c x)). Qed.
Lemma lem4885492 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885493 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term743 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885492 A f c P c') (@lem4885491 A t' f c x)). Qed.
Lemma lem4885494 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term745 A P c' t' f c) = (term746 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885493 A P c' t' f c x)). Qed.
Lemma lem4885495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885496 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885495 A) (@lem4885494 A P c' t' f c)). Qed.
Lemma lem4885497 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term736 A P c' t' f c) = (term737 A P c' t' f c)) = ((term732 A P c' t' f c) = (term747 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4885490 A P c' t' f c) (@lem4885496 A P c' t' f c)). Qed.
Lemma lem4885498 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (EQ_MP (@lem4885497 A P c' t' f c) (@lem4885482 A P c' t' f c)). Qed.
Lemma lem4885500 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885501 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885500 (A -> Prop) P Q). Qed.
Lemma lem4885502 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term749 A P c' t' f c x).
Proof. exact (@lem4885501 A (term641 A f c P c') (term712 A t' f c x)). Qed.
Lemma lem4885503 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4885504 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term751 A t' f c x) = (term712 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885503 A t' f t c x)). Qed.
Lemma lem4885505 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885506 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A t' f c x) = (term713 A t' f c x).
Proof. exact (MK_COMB (@lem4885505 A) (@lem4885504 A t' f c x)). Qed.
Lemma lem4885507 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885508 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term748 A P c' t' f c x) = (term744 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885507 A f c P c') (@lem4885506 A t' f c x)). Qed.
Lemma lem4885509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885510 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term754 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885509) (@lem4885508 A P c' t' f c x)). Qed.
Lemma lem4885511 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term750 A t' f c x t) = (term710 A t' f t c x).
Proof. exact (eq_refl (term750 A t' f c x t)). Qed.
Lemma lem4885512 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885513 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term755 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885512 A f c P c') (@lem4885511 A t' f t c x)). Qed.
Lemma lem4885514 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term757 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885513 A P c' t' f t c x)). Qed.
Lemma lem4885515 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885516 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885515 A) (@lem4885514 A P c' t' f c x)). Qed.
Lemma lem4885517 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term748 A P c' t' f c x) = (term749 A P c' t' f c x)) = ((term744 A P c' t' f c x) = (term759 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885510 A P c' t' f c x) (@lem4885516 A P c' t' f c x)). Qed.
Lemma lem4885518 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4885517 A P c' t' f c x) (@lem4885502 A P c' t' f c x)). Qed.
Lemma lem4885519 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885518 A P c' t' f c x)). Qed.
Lemma lem4885520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885521 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885520 A) (@lem4885519 A P c' t' f c)). Qed.
Lemma lem4885522 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (TRANS (@lem4885498 A P c' t' f c) (@lem4885521 A P c' t' f c)). Qed.
Lemma lem4885523 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885522 A P c' t' f c)). Qed.
Lemma lem4885524 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885525 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4885524 A) (@lem4885523 A P t' f c)). Qed.
Lemma lem4885526 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term716 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4885478 A P t' f c) (@lem4885525 A P t' f c)). Qed.
Lemma lem4885527 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term646 A P t' f c) = (term763 A P t' f c).
Proof. exact (TRANS (@lem4885452 A P t' f c) (@lem4885526 A P t' f c)). Qed.
Lemma lem4885528 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885529 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4885528 A f c) (@lem4885527 A P t' f c)). Qed.
Lemma lem4885531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885532 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885531 (A -> Prop) P Q). Qed.
Lemma lem4885533 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term766 A P t' f c).
Proof. exact (@lem4885532 A (term648 A f c) (term762 A P t' f c)). Qed.
Lemma lem4885534 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4885535 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term768 A P t' f c) = (term762 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885534 A P c' t' f c)). Qed.
Lemma lem4885536 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885537 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term769 A P t' f c) = (term763 A P t' f c).
Proof. exact (MK_COMB (@lem4885536 A) (@lem4885535 A P t' f c)). Qed.
Lemma lem4885538 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885539 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4885538 A f c) (@lem4885537 A P t' f c)). Qed.
Lemma lem4885540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885541 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A P t' f c) = (term771 A P t' f c).
Proof. exact (MK_COMB (@lem4885540) (@lem4885539 A P t' f c)). Qed.
Lemma lem4885542 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term767 A P t' f c c') = (term761 A P c' t' f c).
Proof. exact (eq_refl (term767 A P t' f c c')). Qed.
Lemma lem4885543 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885544 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885543 A f c) (@lem4885542 A P c' t' f c)). Qed.
Lemma lem4885545 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term775 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885544 A P c' t' f c)). Qed.
Lemma lem4885546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885547 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term766 A P t' f c) = (term776 A P t' f c).
Proof. exact (MK_COMB (@lem4885546 A) (@lem4885545 A P t' f c)). Qed.
Lemma lem4885548 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term765 A P t' f c) = (term766 A P t' f c)) = ((term764 A P t' f c) = (term776 A P t' f c)).
Proof. exact (MK_COMB (@lem4885541 A P t' f c) (@lem4885547 A P t' f c)). Qed.
Lemma lem4885549 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term776 A P t' f c).
Proof. exact (EQ_MP (@lem4885548 A P t' f c) (@lem4885533 A P t' f c)). Qed.
Lemma lem4885551 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885552 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (@lem4885551 A P Q). Qed.
Lemma lem4885553 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term778 A P c' t' f c).
Proof. exact (@lem4885552 A (term648 A f c) (term760 A P c' t' f c)). Qed.
Lemma lem4885554 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4885555 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A P c' t' f c) = (term760 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885554 A P c' t' f c x)). Qed.
Lemma lem4885556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885557 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885556 A) (@lem4885555 A P c' t' f c)). Qed.
Lemma lem4885558 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885559 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A P c' t' f c) = (term773 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885558 A f c) (@lem4885557 A P c' t' f c)). Qed.
Lemma lem4885560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885561 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A P c' t' f c) = (term783 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885560) (@lem4885559 A P c' t' f c)). Qed.
Lemma lem4885562 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term779 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (eq_refl (term779 A P c' t' f c x)). Qed.
Lemma lem4885563 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885564 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885563 A f c) (@lem4885562 A P c' t' f c x)). Qed.
Lemma lem4885565 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term787 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885564 A P c' t' f c x)). Qed.
Lemma lem4885566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885567 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885566 A) (@lem4885565 A P c' t' f c)). Qed.
Lemma lem4885568 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term777 A P c' t' f c) = (term778 A P c' t' f c)) = ((term773 A P c' t' f c) = (term788 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4885561 A P c' t' f c) (@lem4885567 A P c' t' f c)). Qed.
Lemma lem4885569 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term788 A P c' t' f c).
Proof. exact (EQ_MP (@lem4885568 A P c' t' f c) (@lem4885553 A P c' t' f c)). Qed.
Lemma lem4885571 {A : Type'} (P : Prop) (Q : A -> Prop) : (term698 A P Q) = (term699 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4885572 {A : Type'} (P : Prop) (Q : type686 A) : (term700 A P Q) = (term701 A P Q).
Proof. exact (@lem4885571 (A -> Prop) P Q). Qed.
Lemma lem4885573 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term790 A P c' t' f c x).
Proof. exact (@lem4885572 A (term648 A f c) (term758 A P c' t' f c x)). Qed.
Lemma lem4885574 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4885575 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term792 A P c' t' f c x) = (term758 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885574 A P c' t' f t c x)). Qed.
Lemma lem4885576 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885577 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term793 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885576 A) (@lem4885575 A P c' t' f c x)). Qed.
Lemma lem4885578 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885579 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A P c' t' f c x) = (term785 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885578 A f c) (@lem4885577 A P c' t' f c x)). Qed.
Lemma lem4885580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885581 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A P c' t' f c x) = (term795 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885580) (@lem4885579 A P c' t' f c x)). Qed.
Lemma lem4885582 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term791 A P c' t' f c x t) = (term756 A P c' t' f t c x).
Proof. exact (eq_refl (term791 A P c' t' f c x t)). Qed.
Lemma lem4885583 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885584 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885583 A f c) (@lem4885582 A P c' t' f t c x)). Qed.
Lemma lem4885585 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885584 A P c' t' f t c x)). Qed.
Lemma lem4885586 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885587 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885586 A) (@lem4885585 A P c' t' f c x)). Qed.
Lemma lem4885588 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term789 A P c' t' f c x) = (term790 A P c' t' f c x)) = ((term785 A P c' t' f c x) = (term800 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885581 A P c' t' f c x) (@lem4885587 A P c' t' f c x)). Qed.
Lemma lem4885589 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term785 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4885588 A P c' t' f c x) (@lem4885573 A P c' t' f c x)). Qed.
Lemma lem4885590 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885589 A P c' t' f c x)). Qed.
Lemma lem4885591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885592 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term788 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885591 A) (@lem4885590 A P c' t' f c)). Qed.
Lemma lem4885593 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (TRANS (@lem4885569 A P c' t' f c) (@lem4885592 A P c' t' f c)). Qed.
Lemma lem4885594 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885593 A P c' t' f c)). Qed.
Lemma lem4885595 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885596 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term776 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4885595 A) (@lem4885594 A P t' f c)). Qed.
Lemma lem4885597 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term764 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4885549 A P t' f c) (@lem4885596 A P t' f c)). Qed.
Lemma lem4885598 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term651 A P t' f c) = (term804 A P t' f c).
Proof. exact (TRANS (@lem4885529 A P t' f c) (@lem4885597 A P t' f c)). Qed.
Lemma lem4885599 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885600 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4885599 A u c) (@lem4885598 A P t' f c)). Qed.
Lemma lem4885602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885603 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4885602 (A -> Prop) P Q). Qed.
Lemma lem4885604 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term811 A u P t' f c).
Proof. exact (@lem4885603 A (term605 A u c) (term803 A P t' f c)). Qed.
Lemma lem4885605 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4885606 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term813 A P t' f c) = (term803 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885605 A P c' t' f c)). Qed.
Lemma lem4885607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885608 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term814 A P t' f c) = (term804 A P t' f c).
Proof. exact (MK_COMB (@lem4885607 A) (@lem4885606 A P t' f c)). Qed.
Lemma lem4885609 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885610 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term810 A u P t' f c) = (term805 A u P t' f c).
Proof. exact (MK_COMB (@lem4885609 A u c) (@lem4885608 A P t' f c)). Qed.
Lemma lem4885611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885612 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term815 A u P t' f c) = (term816 A u P t' f c).
Proof. exact (MK_COMB (@lem4885611) (@lem4885610 A u P t' f c)). Qed.
Lemma lem4885613 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term812 A P t' f c c') = (term802 A P c' t' f c).
Proof. exact (eq_refl (term812 A P t' f c c')). Qed.
Lemma lem4885614 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885615 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term817 A u P t' f c c') = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885614 A u c) (@lem4885613 A P c' t' f c)). Qed.
Lemma lem4885616 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term819 A u P t' f c) = (term820 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885615 A u P c' t' f c)). Qed.
Lemma lem4885617 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885618 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term811 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (MK_COMB (@lem4885617 A) (@lem4885616 A u P t' f c)). Qed.
Lemma lem4885619 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term810 A u P t' f c) = (term811 A u P t' f c)) = ((term805 A u P t' f c) = (term821 A u P t' f c)).
Proof. exact (MK_COMB (@lem4885612 A u P t' f c) (@lem4885618 A u P t' f c)). Qed.
Lemma lem4885620 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term821 A u P t' f c).
Proof. exact (EQ_MP (@lem4885619 A u P t' f c) (@lem4885604 A u P t' f c)). Qed.
Lemma lem4885622 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885623 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (@lem4885622 A P Q). Qed.
Lemma lem4885624 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term823 A u P c' t' f c).
Proof. exact (@lem4885623 A (term605 A u c) (term801 A P c' t' f c)). Qed.
Lemma lem4885625 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4885626 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term825 A P c' t' f c) = (term801 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885625 A P c' t' f c x)). Qed.
Lemma lem4885627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885628 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term826 A P c' t' f c) = (term802 A P c' t' f c).
Proof. exact (MK_COMB (@lem4885627 A) (@lem4885626 A P c' t' f c)). Qed.
Lemma lem4885629 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885630 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term822 A u P c' t' f c) = (term818 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885629 A u c) (@lem4885628 A P c' t' f c)). Qed.
Lemma lem4885631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885632 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term827 A u P c' t' f c) = (term828 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885631) (@lem4885630 A u P c' t' f c)). Qed.
Lemma lem4885633 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term824 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (eq_refl (term824 A P c' t' f c x)). Qed.
Lemma lem4885634 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885635 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term829 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885634 A u c) (@lem4885633 A P c' t' f c x)). Qed.
Lemma lem4885636 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term831 A u P c' t' f c) = (term832 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885635 A u P c' t' f c x)). Qed.
Lemma lem4885637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885638 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term823 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885637 A) (@lem4885636 A u P c' t' f c)). Qed.
Lemma lem4885639 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term822 A u P c' t' f c) = (term823 A u P c' t' f c)) = ((term818 A u P c' t' f c) = (term833 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4885632 A u P c' t' f c) (@lem4885638 A u P c' t' f c)). Qed.
Lemma lem4885640 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term833 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4885639 A u P c' t' f c) (@lem4885624 A u P c' t' f c)). Qed.
Lemma lem4885642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term806 A P Q) = (term807 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4885643 {A : Type'} (P : Prop) (Q : type686 A) : (term808 A P Q) = (term809 A P Q).
Proof. exact (@lem4885642 (A -> Prop) P Q). Qed.
Lemma lem4885644 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term835 A u P c' t' f c x).
Proof. exact (@lem4885643 A (term605 A u c) (term799 A P c' t' f c x)). Qed.
Lemma lem4885645 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4885646 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term837 A P c' t' f c x) = (term799 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885645 A P c' t' f t c x)). Qed.
Lemma lem4885647 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885648 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term838 A P c' t' f c x) = (term800 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4885647 A) (@lem4885646 A P c' t' f c x)). Qed.
Lemma lem4885649 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885650 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term834 A u P c' t' f c x) = (term830 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885649 A u c) (@lem4885648 A P c' t' f c x)). Qed.
Lemma lem4885651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4885652 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term839 A u P c' t' f c x) = (term840 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885651) (@lem4885650 A u P c' t' f c x)). Qed.
Lemma lem4885653 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term836 A P c' t' f c x t) = (term797 A P c' t' f t c x).
Proof. exact (eq_refl (term836 A P c' t' f c x t)). Qed.
Lemma lem4885654 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885655 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term841 A u P c' t' f c x t) = (term842 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885654 A u c) (@lem4885653 A P c' t' f t c x)). Qed.
Lemma lem4885656 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term843 A u P c' t' f c x) = (term844 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885655 A u P c' t' f t c x)). Qed.
Lemma lem4885657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885658 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term835 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4885657 A) (@lem4885656 A u P c' t' f c x)). Qed.
Lemma lem4885659 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term834 A u P c' t' f c x) = (term835 A u P c' t' f c x)) = ((term830 A u P c' t' f c x) = (term845 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4885652 A u P c' t' f c x) (@lem4885658 A u P c' t' f c x)). Qed.
Lemma lem4885660 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term830 A u P c' t' f c x) = (term845 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4885659 A u P c' t' f c x) (@lem4885644 A u P c' t' f c x)). Qed.
Lemma lem4885661 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term832 A u P c' t' f c) = (term846 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4885660 A u P c' t' f c x)). Qed.
Lemma lem4885662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885663 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term833 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4885662 A) (@lem4885661 A u P c' t' f c)). Qed.
Lemma lem4885664 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term818 A u P c' t' f c) = (term847 A u P c' t' f c).
Proof. exact (TRANS (@lem4885640 A u P c' t' f c) (@lem4885663 A u P c' t' f c)). Qed.
Lemma lem4885665 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term820 A u P t' f c) = (term848 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885664 A u P c' t' f c)). Qed.
Lemma lem4885666 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885667 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term821 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (MK_COMB (@lem4885666 A) (@lem4885665 A u P t' f c)). Qed.
Lemma lem4885668 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term805 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4885620 A u P t' f c) (@lem4885667 A u P t' f c)). Qed.
Lemma lem4885669 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term653 A u P t' f c) = (term849 A u P t' f c).
Proof. exact (TRANS (@lem4885600 A u P t' f c) (@lem4885668 A u P t' f c)). Qed.
Lemma lem4885670 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term654 A u P t' f) = (term850 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4885669 A u P t' f c)). Qed.
Lemma lem4885671 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885672 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term655 A u P t' f) = (term851 A u P t' f).
Proof. exact (MK_COMB (@lem4885671 A) (@lem4885670 A u P t' f)). Qed.
Lemma lem4885685 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term673 A f t c x) = (term673 A f t c x).
Proof. exact (eq_refl (term673 A f t c x)). Qed.
Lemma lem4885702 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term632 A f t' c x) = (term852 A f t' c x).
Proof. exact (@lem19699 (term624 A f t' c x) (term620 A t' c x) (term606 A c x)). Qed.
Lemma lem4885703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885704 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term692 A f t' c x) = (term853 A f t' c x).
Proof. exact (MK_COMB (@lem4885703) (@lem4885702 A f t' c x)). Qed.
Lemma lem4885705 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f t c x) = (term854 A t' f t c x).
Proof. exact (MK_COMB (@lem4885704 A f t' c x) (@lem4885685 A f t c x)). Qed.
Lemma lem4885714 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term730 A f c P c') = (term730 A f c P c').
Proof. exact (eq_refl (term730 A f c P c')). Qed.
Lemma lem4885715 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f t c x) = (term855 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885714 A f c P c') (@lem4885705 A t' f t c x)). Qed.
Lemma lem4885718 {A : Type'} (f : type639 A) (c : A -> Prop) : (term649 A f c) = (term649 A f c).
Proof. exact (eq_refl (term649 A f c)). Qed.
Lemma lem4885719 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term797 A P c' t' f t c x) = (term856 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885718 A f c) (@lem4885715 A P c' t' f t c x)). Qed.
Lemma lem4885722 {A : Type'} (u : type686 A) (c : A -> Prop) : (term652 A u c) = (term652 A u c).
Proof. exact (eq_refl (term652 A u c)). Qed.
Lemma lem4885723 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term857 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4885722 A u c) (@lem4885719 A P c' t' f t c x)). Qed.
Lemma lem4885724 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term858 A u P c' t' f t c x).
Proof. exact (@lem19490 (term648 A f c) (term605 A u c) (term855 A P c' t' f t c x)). Qed.
Lemma lem4885725 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term860 A P c' u t' f t c x).
Proof. exact (@lem19490 (term641 A f c P c') (term605 A u c) (term854 A t' f t c x)). Qed.
Lemma lem4885726 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term862 A t' u f t c x).
Proof. exact (@lem19490 (term852 A f t' c x) (term605 A u c) (term673 A f t c x)). Qed.
Lemma lem4885727 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term863 A u f t c x) = (term863 A u f t c x).
Proof. exact (eq_refl (term863 A u f t c x)). Qed.
Lemma lem4885734 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term864 A u f t' c x) = (term865 A f u t' c x).
Proof. exact (@lem19490 (term866 A f t' c x) (term605 A u c) (term867 A t' c x)). Qed.
Lemma lem4885735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4885736 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term868 A u f t' c x) = (term869 A f u t' c x).
Proof. exact (MK_COMB (@lem4885735) (@lem4885734 A f u t' c x)). Qed.
Lemma lem4885737 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term862 A t' u f t c x) = (term870 A t' u f t c x).
Proof. exact (MK_COMB (@lem4885736 A f u t' c x) (@lem4885727 A u f t c x)). Qed.
Lemma lem4885738 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term861 A u t' f t c x) = (term870 A t' u f t c x).
Proof. exact (TRANS (@lem4885726 A t' u f t c x) (@lem4885737 A t' u f t c x)). Qed.
Lemma lem4885741 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term871 A u f c P c') = (term871 A u f c P c').
Proof. exact (eq_refl (term871 A u f c P c')). Qed.
Lemma lem4885742 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term860 A P c' u t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4885741 A u f c P c') (@lem4885738 A t' u f t c x)). Qed.
Lemma lem4885743 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term859 A u P c' t' f t c x) = (term872 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885725 A P c' u t' f t c x) (@lem4885742 A P c' t' u f t c x)). Qed.
Lemma lem4885746 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term873 A u f c) = (term873 A u f c).
Proof. exact (eq_refl (term873 A u f c)). Qed.
Lemma lem4885747 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term858 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4885746 A u f c) (@lem4885743 A P c' t' u f t c x)). Qed.
Lemma lem4885748 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term857 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885724 A u P c' t' f t c x) (@lem4885747 A P c' t' u f t c x)). Qed.
Lemma lem4885749 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term842 A u P c' t' f t c x) = (term874 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4885723 A u P c' t' f t c x) (@lem4885748 A P c' t' u f t c x)). Qed.
Lemma lem4885750 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term844 A u P c' t' f c x) = (term875 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885749 A P c' t' u f t c x)). Qed.
Lemma lem4885751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885752 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term845 A u P c' t' f c x) = (term876 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4885751 A) (@lem4885750 A P c' t' u f c x)). Qed.
Lemma lem4885753 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term846 A u P c' t' f c) = (term877 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4885752 A P c' t' u f c x)). Qed.
Lemma lem4885754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4885755 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term847 A u P c' t' f c) = (term878 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4885754 A) (@lem4885753 A P c' t' u f c)). Qed.
Lemma lem4885756 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term848 A u P t' f c) = (term879 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4885755 A P c' t' u f c)). Qed.
Lemma lem4885757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885758 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term849 A u P t' f c) = (term880 A P t' u f c).
Proof. exact (MK_COMB (@lem4885757 A) (@lem4885756 A P t' u f c)). Qed.
Lemma lem4885759 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term850 A u P t' f) = (term881 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4885758 A P t' u f c)). Qed.
Lemma lem4885760 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885761 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term851 A u P t' f) = (term882 A P t' u f).
Proof. exact (MK_COMB (@lem4885760 A) (@lem4885759 A P t' u f)). Qed.
Lemma lem4885762 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term655 A u P t' f) = (term882 A P t' u f).
Proof. exact (TRANS (@lem4885672 A u P t' f) (@lem4885761 A P t' u f)). Qed.
Lemma lem4885763 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term882 A P t' u f.
Proof. exact (EQ_MP (@lem4885762 A P t' u f) (@lem4884934 A P t' f u h1)). Qed.
Lemma lem4885781 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1156 A u f s t x) = (term1156 A u f s t x).
Proof. exact (eq_refl (term1156 A u f s t x)). Qed.
Lemma lem4885782 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1157 A u f s x) = (term1157 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4885781 A u f s t x)). Qed.
Lemma lem4885783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885784 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1158 A u f s x) = (term1158 A u f s x).
Proof. exact (MK_COMB (@lem4885783 A) (@lem4885782 A u f s x)). Qed.
Lemma lem4885785 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1159 A u f x) = (term1159 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4885784 A u f s x)). Qed.
Lemma lem4885786 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4885788 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1160 A u f x) = (term1160 A u f x).
Proof. exact (MK_COMB (@lem4885786 A) (@lem4885785 A u f x)). Qed.
Lemma lem4885789 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1160 A u f x.
Proof. exact (EQ_MP (@lem4885788 A u f x) (@lem4884944 A f u s x h1)). Qed.
Lemma lem4885798 {A : Type'} (_60388 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term883 A P t' u f _60388.
Proof. exact (@lem4885340 A P t' f u h1 _60388). Qed.
Lemma lem4885799 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) : (term883 A P t' u f _60388) = (term880 A P t' u f _60388).
Proof. exact (eq_refl (term883 A P t' u f _60388)). Qed.
Lemma lem4885800 {A : Type'} (_60388 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term880 A P t' u f _60388.
Proof. exact (EQ_MP (@lem4885799 A P t' u f _60388) (@lem4885798 A _60388 P t' f u h1)). Qed.
Lemma lem4885801 {A : Type'} (_60388 : A -> Prop) (_60389 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term884 A P t' u f _60388 _60389.
Proof. exact (@lem4885800 A _60388 P t' f u h1 _60389). Qed.
Lemma lem4885802 {A : Type'} (P : type686 A) (_60389 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) : (term884 A P t' u f _60388 _60389) = (term878 A P _60389 t' u f _60388).
Proof. exact (eq_refl (term884 A P t' u f _60388 _60389)). Qed.
Lemma lem4885803 {A : Type'} (_60389 : A -> Prop) (_60388 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term878 A P _60389 t' u f _60388.
Proof. exact (EQ_MP (@lem4885802 A P _60389 t' u f _60388) (@lem4885801 A _60388 _60389 P t' f u h1)). Qed.
Lemma lem4885804 {A : Type'} (_60389 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term885 A P _60389 t' u f _60388 _60390.
Proof. exact (@lem4885803 A _60389 _60388 P t' f u h1 _60390). Qed.
Lemma lem4885805 {A : Type'} (P : type686 A) (_60389 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60390 : A) : (term885 A P _60389 t' u f _60388 _60390) = (term876 A P _60389 t' u f _60388 _60390).
Proof. exact (eq_refl (term885 A P _60389 t' u f _60388 _60390)). Qed.
Lemma lem4885806 {A : Type'} (_60389 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term876 A P _60389 t' u f _60388 _60390.
Proof. exact (EQ_MP (@lem4885805 A P _60389 t' u f _60388 _60390) (@lem4885804 A _60389 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4885807 {A : Type'} (_60389 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (_60391 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term886 A P _60389 t' u f _60388 _60390 _60391.
Proof. exact (@lem4885806 A _60389 _60388 _60390 P t' f u h1 _60391). Qed.
Lemma lem4885808 {A : Type'} (P : type686 A) (_60389 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term886 A P _60389 t' u f _60388 _60390 _60391) = (term874 A P _60389 t' u f _60391 _60388 _60390).
Proof. exact (eq_refl (term886 A P _60389 t' u f _60388 _60390 _60391)). Qed.
Lemma lem4885809 {A : Type'} (_60389 : A -> Prop) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term874 A P _60389 t' u f _60391 _60388 _60390.
Proof. exact (EQ_MP (@lem4885808 A P _60389 t' u f _60391 _60388 _60390) (@lem4885807 A _60389 _60388 _60390 _60391 P t' f u h1)). Qed.
Lemma lem4885810 {A : Type'} (_60392 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1172 A u x _60392.
Proof. exact (@lem4885357 A f s t u x h1 _60392). Qed.
Lemma lem4885811 {A : Type'} (u : type686 A) (_60392 : A -> Prop) (x : A) : (term1172 A u x _60392) = (term1163 A u _60392 x).
Proof. exact (eq_refl (term1172 A u x _60392)). Qed.
Lemma lem4885813 {A : Type'} (_60393 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term883 A P t' u f _60393.
Proof. exact (@lem4885763 A P t' f u h1 _60393). Qed.
Lemma lem4885814 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60393 : A -> Prop) : (term883 A P t' u f _60393) = (term880 A P t' u f _60393).
Proof. exact (eq_refl (term883 A P t' u f _60393)). Qed.
Lemma lem4885815 {A : Type'} (_60393 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term880 A P t' u f _60393.
Proof. exact (EQ_MP (@lem4885814 A P t' u f _60393) (@lem4885813 A _60393 P t' f u h1)). Qed.
Lemma lem4885816 {A : Type'} (_60393 : A -> Prop) (_60394 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term884 A P t' u f _60393 _60394.
Proof. exact (@lem4885815 A _60393 P t' f u h1 _60394). Qed.
Lemma lem4885817 {A : Type'} (P : type686 A) (_60394 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60393 : A -> Prop) : (term884 A P t' u f _60393 _60394) = (term878 A P _60394 t' u f _60393).
Proof. exact (eq_refl (term884 A P t' u f _60393 _60394)). Qed.
Lemma lem4885818 {A : Type'} (_60394 : A -> Prop) (_60393 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term878 A P _60394 t' u f _60393.
Proof. exact (EQ_MP (@lem4885817 A P _60394 t' u f _60393) (@lem4885816 A _60393 _60394 P t' f u h1)). Qed.
Lemma lem4885819 {A : Type'} (_60394 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term885 A P _60394 t' u f _60393 _60395.
Proof. exact (@lem4885818 A _60394 _60393 P t' f u h1 _60395). Qed.
Lemma lem4885820 {A : Type'} (P : type686 A) (_60394 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60393 : A -> Prop) (_60395 : A) : (term885 A P _60394 t' u f _60393 _60395) = (term876 A P _60394 t' u f _60393 _60395).
Proof. exact (eq_refl (term885 A P _60394 t' u f _60393 _60395)). Qed.
Lemma lem4885821 {A : Type'} (_60394 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term876 A P _60394 t' u f _60393 _60395.
Proof. exact (EQ_MP (@lem4885820 A P _60394 t' u f _60393 _60395) (@lem4885819 A _60394 _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885822 {A : Type'} (_60394 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (_60396 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term886 A P _60394 t' u f _60393 _60395 _60396.
Proof. exact (@lem4885821 A _60394 _60393 _60395 P t' f u h1 _60396). Qed.
Lemma lem4885823 {A : Type'} (P : type686 A) (_60394 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60396 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) : (term886 A P _60394 t' u f _60393 _60395 _60396) = (term874 A P _60394 t' u f _60396 _60393 _60395).
Proof. exact (eq_refl (term886 A P _60394 t' u f _60393 _60395 _60396)). Qed.
Lemma lem4885824 {A : Type'} (_60394 : A -> Prop) (_60396 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term874 A P _60394 t' u f _60396 _60393 _60395.
Proof. exact (EQ_MP (@lem4885823 A P _60394 t' u f _60396 _60393 _60395) (@lem4885822 A _60394 _60393 _60395 _60396 P t' f u h1)). Qed.
Lemma lem4885825 {A : Type'} (_60397 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1173 A u f x _60397.
Proof. exact (@lem4885789 A f u s x h1 _60397). Qed.
Lemma lem4885826 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (x : A) : (term1173 A u f x _60397) = (term1158 A u f _60397 x).
Proof. exact (eq_refl (term1173 A u f x _60397)). Qed.
Lemma lem4885827 {A : Type'} (_60397 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1158 A u f _60397 x.
Proof. exact (EQ_MP (@lem4885826 A u f _60397 x) (@lem4885825 A _60397 f u s x h1)). Qed.
Lemma lem4885828 {A : Type'} (_60397 : A -> Prop) (_60398 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1174 A u f _60397 x _60398.
Proof. exact (@lem4885827 A _60397 f u s x h1 _60398). Qed.
Lemma lem4885829 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1174 A u f _60397 x _60398) = (term1156 A u f _60397 _60398 x).
Proof. exact (eq_refl (term1174 A u f _60397 x _60398)). Qed.
Lemma lem4885830 {A : Type'} (_60397 : A -> Prop) (_60398 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1156 A u f _60397 _60398 x.
Proof. exact (EQ_MP (@lem4885829 A u f _60397 _60398 x) (@lem4885828 A _60397 _60398 f u s x h1)). Qed.
Lemma lem4885831 {A : Type'} (_60389 : A -> Prop) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term872 A P _60389 t' u f _60391 _60388 _60390.
Proof. exact (proj2 (@lem4885809 A _60389 _60391 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4885833 {A : Type'} (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term870 A t' u f _60391 _60388 _60390.
Proof. exact (proj2 (@lem4885831 A (@el (A -> Prop)) _60391 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4885835 {A : Type'} (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term863 A u f _60391 _60388 _60390.
Proof. exact (proj2 (@lem4885833 A _60391 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4885839 {A : Type'} (_60394 : A -> Prop) (_60396 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term872 A P _60394 t' u f _60396 _60393 _60395.
Proof. exact (proj2 (@lem4885824 A _60394 _60396 _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885841 {A : Type'} (_60396 : A -> Prop) (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term870 A t' u f _60396 _60393 _60395.
Proof. exact (proj2 (@lem4885839 A (@el (A -> Prop)) _60396 _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885844 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term865 A f u t' _60393 _60395.
Proof. exact (proj1 (@lem4885841 A (@el (A -> Prop)) _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885854 {A : Type'} (_60392 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1163 A u _60392 x.
Proof. exact (EQ_MP (@lem4885811 A u _60392 x) (@lem4885810 A _60392 f s t u x h1)). Qed.
Lemma lem4885887 {A : Type'} (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term673 A f _60391 _60388 _60390) = (term1175 A f _60391 _60388 _60390).
Proof. exact (@lem4882772 (term608 A f _60388 _60391) (term606 A _60391 _60390) (@I (A -> Prop) _60388 _60390)). Qed.
Lemma lem4885888 {A : Type'} (u : type686 A) (_60388 : A -> Prop) : (term652 A u _60388) = (term652 A u _60388).
Proof. exact (eq_refl (term652 A u _60388)). Qed.
Lemma lem4885891 {A : Type'} (u : type686 A) (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term863 A u f _60391 _60388 _60390) = (term1176 A u f _60391 _60388 _60390).
Proof. exact (MK_COMB (@lem4885888 A u _60388) (@lem4885887 A f _60391 _60388 _60390)). Qed.
Lemma lem4885892 {A : Type'} (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1176 A u f _60391 _60388 _60390.
Proof. exact (EQ_MP (@lem4885891 A u f _60391 _60388 _60390) (@lem4885835 A _60391 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4885925 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1156 A u f _60397 _60398 x) = (term1177 A u f _60397 _60398 x).
Proof. exact (@lem4882772 (term605 A u _60397) (term608 A f _60397 _60398) (term606 A _60398 x)). Qed.
Lemma lem4885926 {A : Type'} (_60397 : A -> Prop) (_60398 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1177 A u f _60397 _60398 x.
Proof. exact (EQ_MP (@lem4885925 A u f _60397 _60398 x) (@lem4885830 A _60397 _60398 f u s x h1)). Qed.
Lemma lem4885972 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1178 A u f t' _60393 _60395.
Proof. exact (proj1 (@lem4885844 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885982 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1179 A u t' _60393 _60395.
Proof. exact (proj2 (@lem4885844 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4885984 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4884940 A f s t u x h1)). Qed.
Lemma lem4885985 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4885984 A f s t u x h1). Qed.
Lemma lem4885987 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4885988 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4885987 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4885989 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4885988 A u s) (@lem4885985 A f s t u x h1)). Qed.
Lemma lem4885991 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4884940 A f s t u x h1)). Qed.
Lemma lem4885992 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4885991 A f s t u x h1). Qed.
Lemma lem4885994 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4885995 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4885994 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4885996 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4885995 A u s) (@lem4885992 A f s t u x h1)). Qed.
Lemma lem4885998 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term602 A f s t.
Proof. exact (proj2 (@lem4884940 A f s t u x h1)). Qed.
Lemma lem4885999 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term890 A f s t.
Proof. exact (fun h0 : term608 A f s t => @lem4885998 A f s t u x h1). Qed.
Lemma lem4886001 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886002 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term890 A f s t) = (term602 A f s t).
Proof. exact (@lem4886001 (term602 A f s t)). Qed.
Lemma lem4886003 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term602 A f s t.
Proof. exact (EQ_MP (@lem4886002 A f s t) (@lem4885999 A f s t u x h1)). Qed.
Lemma lem4886005 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4884938 A f s t u x h1)). Qed.
Lemma lem4886006 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1180 A t x.
Proof. exact (fun h0 : term606 A t x => @lem4886005 A f s t u x h1). Qed.
Lemma lem4886008 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886009 {A : Type'} (t : A -> Prop) (x : A) : (term1180 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4886008 (@I (A -> Prop) t x)). Qed.
Lemma lem4886010 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4886009 A t x) (@lem4886006 A f s t u x h1)). Qed.
Lemma lem4886026 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886027 {A : Type'} (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term1175 A f _60391 _60388 _60390) = (term1181 A f _60391 _60388 _60390).
Proof. exact (@lem4886026 (term606 A _60391 _60390) (term608 A f _60388 _60391) (@I (A -> Prop) _60388 _60390)). Qed.
Lemma lem4886041 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886042 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1182 A f _60391 _60388 _60390) = (term1183 A _60390 f _60388 _60391).
Proof. exact (@lem4886041 (@I (A -> Prop) _60388 _60390) (term608 A f _60388 _60391)). Qed.
Lemma lem4886048 {A : Type'} (_60391 : A -> Prop) (_60390 : A) : (term1184 A _60391 _60390) = (term1184 A _60391 _60390).
Proof. exact (eq_refl (term1184 A _60391 _60390)). Qed.
Lemma lem4886049 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1181 A f _60391 _60388 _60390) = (term1185 A _60390 f _60388 _60391).
Proof. exact (MK_COMB (@lem4886048 A _60391 _60390) (@lem4886042 A _60390 f _60388 _60391)). Qed.
Lemma lem4886053 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886054 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1185 A _60390 f _60388 _60391) = (term1186 A _60390 f _60388 _60391).
Proof. exact (@lem4886053 (@I (A -> Prop) _60388 _60390) (term606 A _60391 _60390) (term608 A f _60388 _60391)). Qed.
Lemma lem4886070 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1181 A f _60391 _60388 _60390) = (term1186 A _60390 f _60388 _60391).
Proof. exact (TRANS (@lem4886049 A _60390 f _60388 _60391) (@lem4886054 A _60390 f _60388 _60391)). Qed.
Lemma lem4886071 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1175 A f _60391 _60388 _60390) = (term1186 A _60390 f _60388 _60391).
Proof. exact (TRANS (@lem4886027 A f _60391 _60388 _60390) (@lem4886070 A _60390 f _60388 _60391)). Qed.
Lemma lem4886072 {A : Type'} (u : type686 A) (_60388 : A -> Prop) : (term652 A u _60388) = (term652 A u _60388).
Proof. exact (eq_refl (term652 A u _60388)). Qed.
Lemma lem4886073 {A : Type'} (u : type686 A) (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1176 A u f _60391 _60388 _60390) = (term1187 A u _60390 f _60388 _60391).
Proof. exact (MK_COMB (@lem4886072 A u _60388) (@lem4886071 A _60390 f _60388 _60391)). Qed.
Lemma lem4886077 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886078 {A : Type'} (u : type686 A) (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1187 A u _60390 f _60388 _60391) = (term1188 A u _60390 f _60388 _60391).
Proof. exact (@lem4886077 (@I (A -> Prop) _60388 _60390) (term605 A u _60388) (term1189 A _60390 f _60388 _60391)). Qed.
Lemma lem4886092 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886093 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1190 A u _60390 f _60388 _60391) = (term1191 A _60390 u f _60388 _60391).
Proof. exact (@lem4886092 (term606 A _60391 _60390) (term605 A u _60388) (term608 A f _60388 _60391)). Qed.
Lemma lem4886109 {A : Type'} (_60388 : A -> Prop) (_60390 : A) : (term1192 A _60388 _60390) = (term1192 A _60388 _60390).
Proof. exact (eq_refl (term1192 A _60388 _60390)). Qed.
Lemma lem4886110 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1188 A u _60390 f _60388 _60391) = (term1193 A _60390 u f _60388 _60391).
Proof. exact (MK_COMB (@lem4886109 A _60388 _60390) (@lem4886093 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886121 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1187 A u _60390 f _60388 _60391) = (term1193 A _60390 u f _60388 _60391).
Proof. exact (TRANS (@lem4886078 A u _60390 f _60388 _60391) (@lem4886110 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886122 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1176 A u f _60391 _60388 _60390) = (term1193 A _60390 u f _60388 _60391).
Proof. exact (TRANS (@lem4886073 A u _60390 f _60388 _60391) (@lem4886121 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886124 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1194 A u f _60391 _60388 _60390) = (term1195 A _60390 u f _60388 _60391).
Proof. exact (MK_COMB (@lem4886123) (@lem4886122 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886148 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886149 {A : Type'} (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term611 A f _60388 _60391 _60390) = (term1189 A _60390 f _60388 _60391).
Proof. exact (@lem4886148 (term606 A _60391 _60390) (term608 A f _60388 _60391)). Qed.
Lemma lem4886155 {A : Type'} (u : type686 A) (_60388 : A -> Prop) : (term652 A u _60388) = (term652 A u _60388).
Proof. exact (eq_refl (term652 A u _60388)). Qed.
Lemma lem4886156 {A : Type'} (u : type686 A) (_60390 : A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1177 A u f _60388 _60391 _60390) = (term1190 A u _60390 f _60388 _60391).
Proof. exact (MK_COMB (@lem4886155 A u _60388) (@lem4886149 A _60390 f _60388 _60391)). Qed.
Lemma lem4886160 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886161 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1190 A u _60390 f _60388 _60391) = (term1191 A _60390 u f _60388 _60391).
Proof. exact (@lem4886160 (term606 A _60391 _60390) (term605 A u _60388) (term608 A f _60388 _60391)). Qed.
Lemma lem4886177 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1177 A u f _60388 _60391 _60390) = (term1191 A _60390 u f _60388 _60391).
Proof. exact (TRANS (@lem4886156 A u _60390 f _60388 _60391) (@lem4886161 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886178 {A : Type'} (_60388 : A -> Prop) (_60390 : A) : (term1192 A _60388 _60390) = (term1192 A _60388 _60390).
Proof. exact (eq_refl (term1192 A _60388 _60390)). Qed.
Lemma lem4886179 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1196 A u f _60388 _60391 _60390) = (term1193 A _60390 u f _60388 _60391).
Proof. exact (MK_COMB (@lem4886178 A _60388 _60390) (@lem4886177 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886190 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : ((term1176 A u f _60391 _60388 _60390) = (term1196 A u f _60388 _60391 _60390)) = ((term1193 A _60390 u f _60388 _60391) = (term1193 A _60390 u f _60388 _60391)).
Proof. exact (MK_COMB (@lem4886124 A _60390 u f _60388 _60391) (@lem4886179 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4886193 (x : Prop) : (x = x) = True.
Proof. exact (@lem4886192 Prop x). Qed.
Lemma lem4886194 {A : Type'} (_60390 : A) (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : ((term1193 A _60390 u f _60388 _60391) = (term1193 A _60390 u f _60388 _60391)) = True.
Proof. exact (@lem4886193 (term1193 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886195 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : ((term1176 A u f _60391 _60388 _60390) = (term1196 A u f _60388 _60391 _60390)) = True.
Proof. exact (TRANS (@lem4886190 A _60390 u f _60388 _60391) (@lem4886194 A _60390 u f _60388 _60391)). Qed.
Lemma lem4886196 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : True = ((term1176 A u f _60391 _60388 _60390) = (term1196 A u f _60388 _60391 _60390)).
Proof. exact (SYM (@lem4886195 A u f _60388 _60391 _60390)). Qed.
Lemma lem4886197 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1176 A u f _60391 _60388 _60390) = (term1196 A u f _60388 _60391 _60390).
Proof. exact (EQ_MP (@lem4886196 A u f _60388 _60391 _60390) (@lem0)). Qed.
Lemma lem4886198 {A : Type'} (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1196 A u f _60388 _60391 _60390.
Proof. exact (EQ_MP (@lem4886197 A u f _60388 _60391 _60390) (@lem4885892 A _60391 _60388 _60390 P t' f u h1)). Qed.
Lemma lem4886200 (b : Prop) (a : Prop) : (a \/ b) = (term897 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4886201 {A : Type'} (u : type686 A) (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term1196 A u f _60388 _60391 _60390) = (term1197 A u f _60391 _60388 _60390).
Proof. exact (@lem4886200 (term1177 A u f _60388 _60391 _60390) (@I (A -> Prop) _60388 _60390)). Qed.
Lemma lem4886203 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4886204 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1198 A u f _60388 _60391 _60390) = (term1199 A u f _60388 _60391 _60390).
Proof. exact (@lem4886203 (term605 A u _60388) (term611 A f _60388 _60391 _60390)). Qed.
Lemma lem4886206 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886207 {A : Type'} (u : type686 A) (_60388 : A -> Prop) : (term904 A u _60388) = (@I ((A -> Prop) -> Prop) u _60388).
Proof. exact (@lem4886206 (@I ((A -> Prop) -> Prop) u _60388)). Qed.
Lemma lem4886208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886209 {A : Type'} (u : type686 A) (_60388 : A -> Prop) : (term905 A u _60388) = (term603 A u _60388).
Proof. exact (MK_COMB (@lem4886208) (@lem4886207 A u _60388)). Qed.
Lemma lem4886211 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4886212 {A : Type'} (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1200 A f _60388 _60391 _60390) = (term1201 A f _60388 _60391 _60390).
Proof. exact (@lem4886211 (term608 A f _60388 _60391) (term606 A _60391 _60390)). Qed.
Lemma lem4886214 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886215 {A : Type'} (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term906 A f _60388 _60391) = (term602 A f _60388 _60391).
Proof. exact (@lem4886214 (term602 A f _60388 _60391)). Qed.
Lemma lem4886216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886217 {A : Type'} (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) : (term1202 A f _60388 _60391) = (term1203 A f _60388 _60391).
Proof. exact (MK_COMB (@lem4886216) (@lem4886215 A f _60388 _60391)). Qed.
Lemma lem4886219 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886220 {A : Type'} (_60391 : A -> Prop) (_60390 : A) : (term1204 A _60391 _60390) = (@I (A -> Prop) _60391 _60390).
Proof. exact (@lem4886219 (@I (A -> Prop) _60391 _60390)). Qed.
Lemma lem4886221 {A : Type'} (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1201 A f _60388 _60391 _60390) = (term1205 A f _60388 _60391 _60390).
Proof. exact (MK_COMB (@lem4886217 A f _60388 _60391) (@lem4886220 A _60391 _60390)). Qed.
Lemma lem4886222 {A : Type'} (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1200 A f _60388 _60391 _60390) = (term1205 A f _60388 _60391 _60390).
Proof. exact (TRANS (@lem4886212 A f _60388 _60391 _60390) (@lem4886221 A f _60388 _60391 _60390)). Qed.
Lemma lem4886223 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1199 A u f _60388 _60391 _60390) = (term1206 A u f _60388 _60391 _60390).
Proof. exact (MK_COMB (@lem4886209 A u _60388) (@lem4886222 A f _60388 _60391 _60390)). Qed.
Lemma lem4886224 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1198 A u f _60388 _60391 _60390) = (term1206 A u f _60388 _60391 _60390).
Proof. exact (TRANS (@lem4886204 A u f _60388 _60391 _60390) (@lem4886223 A u f _60388 _60391 _60390)). Qed.
Lemma lem4886225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4886226 {A : Type'} (u : type686 A) (f : type639 A) (_60388 : A -> Prop) (_60391 : A -> Prop) (_60390 : A) : (term1207 A u f _60388 _60391 _60390) = (term1208 A u f _60388 _60391 _60390).
Proof. exact (MK_COMB (@lem4886225) (@lem4886224 A u f _60388 _60391 _60390)). Qed.
Lemma lem4886227 {A : Type'} (_60388 : A -> Prop) (_60390 : A) : (@I (A -> Prop) _60388 _60390) = (@I (A -> Prop) _60388 _60390).
Proof. exact (eq_refl (@I (A -> Prop) _60388 _60390)). Qed.
Lemma lem4886228 {A : Type'} (u : type686 A) (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term1197 A u f _60391 _60388 _60390) = (term1209 A u f _60391 _60388 _60390).
Proof. exact (MK_COMB (@lem4886226 A u f _60388 _60391 _60390) (@lem4886227 A _60388 _60390)). Qed.
Lemma lem4886229 {A : Type'} (u : type686 A) (f : type639 A) (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) : (term1196 A u f _60388 _60391 _60390) = (term1209 A u f _60391 _60388 _60390).
Proof. exact (TRANS (@lem4886201 A u f _60391 _60388 _60390) (@lem4886228 A u f _60391 _60388 _60390)). Qed.
Lemma lem4886231 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1205 A f s t x.
Proof. exact (conj (@lem4886003 A f s t u x h1) (@lem4886010 A f s t u x h1)). Qed.
Lemma lem4886232 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1206 A u f s t x.
Proof. exact (conj (@lem4885996 A f s t u x h1) (@lem4886231 A f s t u x h1)). Qed.
Lemma lem4886234 {A : Type'} (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1209 A u f _60391 _60388 _60390.
Proof. exact (EQ_MP (@lem4886229 A u f _60391 _60388 _60390) (@lem4886198 A _60388 _60391 _60390 P t' f u h1)). Qed.
Lemma lem4886235 {A : Type'} (_60391 : A -> Prop) (_60388 : A -> Prop) (_60390 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1209 A u f _60391 _60388 _60390.
Proof. exact (@lem4886234 A _60391 _60388 _60390 P t' f u h1). Qed.
Lemma lem4886236 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1209 A u f t s x.
Proof. exact (@lem4886235 A t s x P t' f u h1). Qed.
Lemma lem4886239 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : @I (A -> Prop) s x.
Proof. exact (@lem4886236 A t s x P t' f u h1 (@lem4886232 A f s t u x h2)). Qed.
Lemma lem4886240 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : term1180 A s x.
Proof. exact (fun h0 : term606 A s x => @lem4886239 A P t' f s t u x h1 h2). Qed.
Lemma lem4886242 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886243 {A : Type'} (s : A -> Prop) (x : A) : (term1180 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4886242 (@I (A -> Prop) s x)). Qed.
Lemma lem4886244 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4886243 A s x) (@lem4886240 A P t' f s t u x h1 h2)). Qed.
Lemma lem4886246 (a : Prop) (b : Prop) : (term1210 a b) = (term1211 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4886247 {A : Type'} (u : type686 A) (_60392 : A -> Prop) (x : A) : (term1163 A u _60392 x) = (term1212 A u _60392 x).
Proof. exact (@lem4886246 (@I ((A -> Prop) -> Prop) u _60392) (@I (A -> Prop) _60392 x)). Qed.
Lemma lem4886249 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4886250 {A : Type'} (u : type686 A) (_60392 : A -> Prop) (x : A) : (term1212 A u _60392 x) = (term1213 A u _60392 x).
Proof. exact (@lem4886249 (term1154 A u _60392 x)). Qed.
Lemma lem4886251 {A : Type'} (u : type686 A) (_60392 : A -> Prop) (x : A) : (term1163 A u _60392 x) = (term1213 A u _60392 x).
Proof. exact (TRANS (@lem4886247 A u _60392 x) (@lem4886250 A u _60392 x)). Qed.
Lemma lem4886253 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : term1154 A u s x.
Proof. exact (conj (@lem4885989 A f s t u x h2) (@lem4886244 A P t' f s t u x h1 h2)). Qed.
Lemma lem4886255 {A : Type'} (_60392 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1213 A u _60392 x.
Proof. exact (EQ_MP (@lem4886251 A u _60392 x) (@lem4885854 A _60392 f s t u x h1)). Qed.
Lemma lem4886256 {A : Type'} (_60392 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1213 A u _60392 x.
Proof. exact (@lem4886255 A _60392 f s t u x h1). Qed.
Lemma lem4886257 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1169 A f s t u x) : term1213 A u s x.
Proof. exact (@lem4886256 A s f s t u x h1). Qed.
Lemma lem4886260 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : False.
Proof. exact (@lem4886257 A f s t u x h2 (@lem4886253 A P t' f s t u x h1 h2)). Qed.
Lemma lem4886261 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : term911.
Proof. exact (fun h0 : ~ False => @lem4886260 A P t' f s t u x h1 h2). Qed.
Lemma lem4886263 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886264 : term911 = False.
Proof. exact (@lem4886263 False). Qed.
Lemma lem4886265 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term598 A P t' f u) (h2 : term1169 A f s t u x) : False.
Proof. exact (EQ_MP (@lem4886264) (@lem4886261 A P t' f s t u x h1 h2)). Qed.
Lemma lem4886267 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4884943 A f u s x h1)). Qed.
Lemma lem4886268 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4886267 A f u s x h1). Qed.
Lemma lem4886270 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886271 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4886270 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4886272 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4886271 A u s) (@lem4886268 A f u s x h1)). Qed.
Lemma lem4886274 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4884943 A f u s x h1)). Qed.
Lemma lem4886275 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4886274 A f u s x h1). Qed.
Lemma lem4886277 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886278 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4886277 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4886279 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4886278 A u s) (@lem4886275 A f u s x h1)). Qed.
Lemma lem4886281 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4884943 A f u s x h1)). Qed.
Lemma lem4886282 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1180 A s x.
Proof. exact (fun h0 : term606 A s x => @lem4886281 A f u s x h1). Qed.
Lemma lem4886284 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886285 {A : Type'} (s : A -> Prop) (x : A) : (term1180 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4886284 (@I (A -> Prop) s x)). Qed.
Lemma lem4886286 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4886285 A s x) (@lem4886282 A f u s x h1)). Qed.
Lemma lem4886292 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886293 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1178 A u f t' _60393 _60395) = (term1214 A f t' u _60393 _60395).
Proof. exact (@lem4886292 (term624 A f t' _60393 _60395) (term605 A u _60393) (term606 A _60393 _60395)). Qed.
Lemma lem4886307 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886308 {A : Type'} (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1163 A u _60393 _60395) = (term1215 A _60395 u _60393).
Proof. exact (@lem4886307 (term606 A _60393 _60395) (term605 A u _60393)). Qed.
Lemma lem4886314 {A : Type'} (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1216 A f t' _60393 _60395) = (term1216 A f t' _60393 _60395).
Proof. exact (eq_refl (term1216 A f t' _60393 _60395)). Qed.
Lemma lem4886315 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1214 A f t' u _60393 _60395) = (term1217 A f t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886314 A f t' _60393 _60395) (@lem4886308 A _60395 u _60393)). Qed.
Lemma lem4886326 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1178 A u f t' _60393 _60395) = (term1217 A f t' _60395 u _60393).
Proof. exact (TRANS (@lem4886293 A f t' u _60393 _60395) (@lem4886315 A f t' _60395 u _60393)). Qed.
Lemma lem4886327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886328 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1218 A u f t' _60393 _60395) = (term1219 A f t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886327) (@lem4886326 A f t' _60395 u _60393)). Qed.
Lemma lem4886342 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886343 {A : Type'} (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1163 A u _60393 _60395) = (term1215 A _60395 u _60393).
Proof. exact (@lem4886342 (term606 A _60393 _60395) (term605 A u _60393)). Qed.
Lemma lem4886349 {A : Type'} (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1216 A f t' _60393 _60395) = (term1216 A f t' _60393 _60395).
Proof. exact (eq_refl (term1216 A f t' _60393 _60395)). Qed.
Lemma lem4886350 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1214 A f t' u _60393 _60395) = (term1217 A f t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886349 A f t' _60393 _60395) (@lem4886343 A _60395 u _60393)). Qed.
Lemma lem4886361 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : ((term1178 A u f t' _60393 _60395) = (term1214 A f t' u _60393 _60395)) = ((term1217 A f t' _60395 u _60393) = (term1217 A f t' _60395 u _60393)).
Proof. exact (MK_COMB (@lem4886328 A f t' _60395 u _60393) (@lem4886350 A f t' _60395 u _60393)). Qed.
Lemma lem4886363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4886364 (x : Prop) : (x = x) = True.
Proof. exact (@lem4886363 Prop x). Qed.
Lemma lem4886365 {A : Type'} (f : type639 A) (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : ((term1217 A f t' _60395 u _60393) = (term1217 A f t' _60395 u _60393)) = True.
Proof. exact (@lem4886364 (term1217 A f t' _60395 u _60393)). Qed.
Lemma lem4886366 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : ((term1178 A u f t' _60393 _60395) = (term1214 A f t' u _60393 _60395)) = True.
Proof. exact (TRANS (@lem4886361 A f t' _60395 u _60393) (@lem4886365 A f t' _60395 u _60393)). Qed.
Lemma lem4886367 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : True = ((term1178 A u f t' _60393 _60395) = (term1214 A f t' u _60393 _60395)).
Proof. exact (SYM (@lem4886366 A f t' u _60393 _60395)). Qed.
Lemma lem4886368 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1178 A u f t' _60393 _60395) = (term1214 A f t' u _60393 _60395).
Proof. exact (EQ_MP (@lem4886367 A f t' u _60393 _60395) (@lem0)). Qed.
Lemma lem4886369 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1214 A f t' u _60393 _60395.
Proof. exact (EQ_MP (@lem4886368 A f t' u _60393 _60395) (@lem4885972 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4886371 (b : Prop) (a : Prop) : (a \/ b) = (term897 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4886372 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1214 A f t' u _60393 _60395) = (term1220 A u f t' _60393 _60395).
Proof. exact (@lem4886371 (term1163 A u _60393 _60395) (term624 A f t' _60393 _60395)). Qed.
Lemma lem4886374 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4886375 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1221 A u _60393 _60395) = (term1222 A u _60393 _60395).
Proof. exact (@lem4886374 (term605 A u _60393) (term606 A _60393 _60395)). Qed.
Lemma lem4886377 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886378 {A : Type'} (u : type686 A) (_60393 : A -> Prop) : (term904 A u _60393) = (@I ((A -> Prop) -> Prop) u _60393).
Proof. exact (@lem4886377 (@I ((A -> Prop) -> Prop) u _60393)). Qed.
Lemma lem4886379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886380 {A : Type'} (u : type686 A) (_60393 : A -> Prop) : (term905 A u _60393) = (term603 A u _60393).
Proof. exact (MK_COMB (@lem4886379) (@lem4886378 A u _60393)). Qed.
Lemma lem4886382 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886383 {A : Type'} (_60393 : A -> Prop) (_60395 : A) : (term1204 A _60393 _60395) = (@I (A -> Prop) _60393 _60395).
Proof. exact (@lem4886382 (@I (A -> Prop) _60393 _60395)). Qed.
Lemma lem4886384 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1222 A u _60393 _60395) = (term1154 A u _60393 _60395).
Proof. exact (MK_COMB (@lem4886380 A u _60393) (@lem4886383 A _60393 _60395)). Qed.
Lemma lem4886385 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1221 A u _60393 _60395) = (term1154 A u _60393 _60395).
Proof. exact (TRANS (@lem4886375 A u _60393 _60395) (@lem4886384 A u _60393 _60395)). Qed.
Lemma lem4886386 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4886387 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1223 A u _60393 _60395) = (term1224 A u _60393 _60395).
Proof. exact (MK_COMB (@lem4886386) (@lem4886385 A u _60393 _60395)). Qed.
Lemma lem4886388 {A : Type'} (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term624 A f t' _60393 _60395) = (term624 A f t' _60393 _60395).
Proof. exact (eq_refl (term624 A f t' _60393 _60395)). Qed.
Lemma lem4886389 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1220 A u f t' _60393 _60395) = (term1225 A u f t' _60393 _60395).
Proof. exact (MK_COMB (@lem4886387 A u _60393 _60395) (@lem4886388 A f t' _60393 _60395)). Qed.
Lemma lem4886390 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1214 A f t' u _60393 _60395) = (term1225 A u f t' _60393 _60395).
Proof. exact (TRANS (@lem4886372 A u f t' _60393 _60395) (@lem4886389 A u f t' _60393 _60395)). Qed.
Lemma lem4886392 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1154 A u s x.
Proof. exact (conj (@lem4886279 A f u s x h1) (@lem4886286 A f u s x h1)). Qed.
Lemma lem4886394 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1225 A u f t' _60393 _60395.
Proof. exact (EQ_MP (@lem4886390 A u f t' _60393 _60395) (@lem4886369 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4886395 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1225 A u f t' _60393 _60395.
Proof. exact (@lem4886394 A _60393 _60395 P t' f u h1). Qed.
Lemma lem4886396 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1225 A u f t' s x.
Proof. exact (@lem4886395 A s x P t' f u h1). Qed.
Lemma lem4886399 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term624 A f t' s x.
Proof. exact (@lem4886396 A s x P t' f u h2 (@lem4886392 A f u s x h1)). Qed.
Lemma lem4886400 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term1226 A f t' s x.
Proof. exact (fun h0 : term1227 A f t' s x => @lem4886399 A s x P t' f u h1 h2). Qed.
Lemma lem4886402 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886403 {A : Type'} (f : type639 A) (t' : type667 A) (s : A -> Prop) (x : A) : (term1226 A f t' s x) = (term624 A f t' s x).
Proof. exact (@lem4886402 (term624 A f t' s x)). Qed.
Lemma lem4886404 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term624 A f t' s x.
Proof. exact (EQ_MP (@lem4886403 A f t' s x) (@lem4886400 A s x P t' f u h1 h2)). Qed.
Lemma lem4886406 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4884943 A f u s x h1)). Qed.
Lemma lem4886407 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term888 A u s.
Proof. exact (fun h0 : term605 A u s => @lem4886406 A f u s x h1). Qed.
Lemma lem4886409 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886410 {A : Type'} (u : type686 A) (s : A -> Prop) : (term888 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4886409 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4886411 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4886410 A u s) (@lem4886407 A f u s x h1)). Qed.
Lemma lem4886413 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4884943 A f u s x h1)). Qed.
Lemma lem4886414 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1180 A s x.
Proof. exact (fun h0 : term606 A s x => @lem4886413 A f u s x h1). Qed.
Lemma lem4886416 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886417 {A : Type'} (s : A -> Prop) (x : A) : (term1180 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4886416 (@I (A -> Prop) s x)). Qed.
Lemma lem4886418 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4886417 A s x) (@lem4886414 A f u s x h1)). Qed.
Lemma lem4886424 (q : Prop) (p : Prop) (r : Prop) : (term893 p q r) = (term893 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4886425 {A : Type'} (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1179 A u t' _60393 _60395) = (term1228 A t' u _60393 _60395).
Proof. exact (@lem4886424 (term620 A t' _60393 _60395) (term605 A u _60393) (term606 A _60393 _60395)). Qed.
Lemma lem4886439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886440 {A : Type'} (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1163 A u _60393 _60395) = (term1215 A _60395 u _60393).
Proof. exact (@lem4886439 (term606 A _60393 _60395) (term605 A u _60393)). Qed.
Lemma lem4886446 {A : Type'} (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1229 A t' _60393 _60395) = (term1229 A t' _60393 _60395).
Proof. exact (eq_refl (term1229 A t' _60393 _60395)). Qed.
Lemma lem4886447 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1228 A t' u _60393 _60395) = (term1230 A t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886446 A t' _60393 _60395) (@lem4886440 A _60395 u _60393)). Qed.
Lemma lem4886458 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1179 A u t' _60393 _60395) = (term1230 A t' _60395 u _60393).
Proof. exact (TRANS (@lem4886425 A t' u _60393 _60395) (@lem4886447 A t' _60395 u _60393)). Qed.
Lemma lem4886459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4886460 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1231 A u t' _60393 _60395) = (term1232 A t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886459) (@lem4886458 A t' _60395 u _60393)). Qed.
Lemma lem4886474 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4886475 {A : Type'} (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1163 A u _60393 _60395) = (term1215 A _60395 u _60393).
Proof. exact (@lem4886474 (term606 A _60393 _60395) (term605 A u _60393)). Qed.
Lemma lem4886481 {A : Type'} (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1229 A t' _60393 _60395) = (term1229 A t' _60393 _60395).
Proof. exact (eq_refl (term1229 A t' _60393 _60395)). Qed.
Lemma lem4886482 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : (term1228 A t' u _60393 _60395) = (term1230 A t' _60395 u _60393).
Proof. exact (MK_COMB (@lem4886481 A t' _60393 _60395) (@lem4886475 A _60395 u _60393)). Qed.
Lemma lem4886493 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : ((term1179 A u t' _60393 _60395) = (term1228 A t' u _60393 _60395)) = ((term1230 A t' _60395 u _60393) = (term1230 A t' _60395 u _60393)).
Proof. exact (MK_COMB (@lem4886460 A t' _60395 u _60393) (@lem4886482 A t' _60395 u _60393)). Qed.
Lemma lem4886495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4886496 (x : Prop) : (x = x) = True.
Proof. exact (@lem4886495 Prop x). Qed.
Lemma lem4886497 {A : Type'} (t' : type667 A) (_60395 : A) (u : type686 A) (_60393 : A -> Prop) : ((term1230 A t' _60395 u _60393) = (term1230 A t' _60395 u _60393)) = True.
Proof. exact (@lem4886496 (term1230 A t' _60395 u _60393)). Qed.
Lemma lem4886498 {A : Type'} (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : ((term1179 A u t' _60393 _60395) = (term1228 A t' u _60393 _60395)) = True.
Proof. exact (TRANS (@lem4886493 A t' _60395 u _60393) (@lem4886497 A t' _60395 u _60393)). Qed.
Lemma lem4886499 {A : Type'} (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : True = ((term1179 A u t' _60393 _60395) = (term1228 A t' u _60393 _60395)).
Proof. exact (SYM (@lem4886498 A t' u _60393 _60395)). Qed.
Lemma lem4886500 {A : Type'} (t' : type667 A) (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1179 A u t' _60393 _60395) = (term1228 A t' u _60393 _60395).
Proof. exact (EQ_MP (@lem4886499 A t' u _60393 _60395) (@lem0)). Qed.
Lemma lem4886501 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1228 A t' u _60393 _60395.
Proof. exact (EQ_MP (@lem4886500 A t' u _60393 _60395) (@lem4885982 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4886503 (b : Prop) (a : Prop) : (a \/ b) = (term897 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4886504 {A : Type'} (u : type686 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1228 A t' u _60393 _60395) = (term1233 A u t' _60393 _60395).
Proof. exact (@lem4886503 (term1163 A u _60393 _60395) (term620 A t' _60393 _60395)). Qed.
Lemma lem4886506 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4886507 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1221 A u _60393 _60395) = (term1222 A u _60393 _60395).
Proof. exact (@lem4886506 (term605 A u _60393) (term606 A _60393 _60395)). Qed.
Lemma lem4886509 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886510 {A : Type'} (u : type686 A) (_60393 : A -> Prop) : (term904 A u _60393) = (@I ((A -> Prop) -> Prop) u _60393).
Proof. exact (@lem4886509 (@I ((A -> Prop) -> Prop) u _60393)). Qed.
Lemma lem4886511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4886512 {A : Type'} (u : type686 A) (_60393 : A -> Prop) : (term905 A u _60393) = (term603 A u _60393).
Proof. exact (MK_COMB (@lem4886511) (@lem4886510 A u _60393)). Qed.
Lemma lem4886514 (a : Prop) : (term367 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4886515 {A : Type'} (_60393 : A -> Prop) (_60395 : A) : (term1204 A _60393 _60395) = (@I (A -> Prop) _60393 _60395).
Proof. exact (@lem4886514 (@I (A -> Prop) _60393 _60395)). Qed.
Lemma lem4886516 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1222 A u _60393 _60395) = (term1154 A u _60393 _60395).
Proof. exact (MK_COMB (@lem4886512 A u _60393) (@lem4886515 A _60393 _60395)). Qed.
Lemma lem4886517 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1221 A u _60393 _60395) = (term1154 A u _60393 _60395).
Proof. exact (TRANS (@lem4886507 A u _60393 _60395) (@lem4886516 A u _60393 _60395)). Qed.
Lemma lem4886518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4886519 {A : Type'} (u : type686 A) (_60393 : A -> Prop) (_60395 : A) : (term1223 A u _60393 _60395) = (term1224 A u _60393 _60395).
Proof. exact (MK_COMB (@lem4886518) (@lem4886517 A u _60393 _60395)). Qed.
Lemma lem4886520 {A : Type'} (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term620 A t' _60393 _60395) = (term620 A t' _60393 _60395).
Proof. exact (eq_refl (term620 A t' _60393 _60395)). Qed.
Lemma lem4886521 {A : Type'} (u : type686 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1233 A u t' _60393 _60395) = (term1234 A u t' _60393 _60395).
Proof. exact (MK_COMB (@lem4886519 A u _60393 _60395) (@lem4886520 A t' _60393 _60395)). Qed.
Lemma lem4886522 {A : Type'} (u : type686 A) (t' : type667 A) (_60393 : A -> Prop) (_60395 : A) : (term1228 A t' u _60393 _60395) = (term1234 A u t' _60393 _60395).
Proof. exact (TRANS (@lem4886504 A u t' _60393 _60395) (@lem4886521 A u t' _60393 _60395)). Qed.
Lemma lem4886524 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1154 A u s x.
Proof. exact (conj (@lem4886411 A f u s x h1) (@lem4886418 A f u s x h1)). Qed.
Lemma lem4886526 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1234 A u t' _60393 _60395.
Proof. exact (EQ_MP (@lem4886522 A u t' _60393 _60395) (@lem4886501 A _60393 _60395 P t' f u h1)). Qed.
Lemma lem4886527 {A : Type'} (_60393 : A -> Prop) (_60395 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1234 A u t' _60393 _60395.
Proof. exact (@lem4886526 A _60393 _60395 P t' f u h1). Qed.
Lemma lem4886528 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term598 A P t' f u) : term1234 A u t' s x.
Proof. exact (@lem4886527 A s x P t' f u h1). Qed.
Lemma lem4886531 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term620 A t' s x.
Proof. exact (@lem4886528 A s x P t' f u h2 (@lem4886524 A f u s x h1)). Qed.
Lemma lem4886532 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term1235 A t' s x.
Proof. exact (fun h0 : term1236 A t' s x => @lem4886531 A s x P t' f u h1 h2). Qed.
Lemma lem4886534 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886535 {A : Type'} (t' : type667 A) (s : A -> Prop) (x : A) : (term1235 A t' s x) = (term620 A t' s x).
Proof. exact (@lem4886534 (term620 A t' s x)). Qed.
Lemma lem4886536 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term620 A t' s x.
Proof. exact (EQ_MP (@lem4886535 A t' s x) (@lem4886532 A s x P t' f u h1 h2)). Qed.
Lemma lem4886538 (a : Prop) (b : Prop) : (term1210 a b) = (term1211 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4886539 {A : Type'} (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term611 A f _60397 _60398 x) = (term1237 A f _60397 _60398 x).
Proof. exact (@lem4886538 (term602 A f _60397 _60398) (@I (A -> Prop) _60398 x)). Qed.
Lemma lem4886540 {A : Type'} (u : type686 A) (_60397 : A -> Prop) : (term652 A u _60397) = (term652 A u _60397).
Proof. exact (eq_refl (term652 A u _60397)). Qed.
Lemma lem4886541 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1177 A u f _60397 _60398 x) = (term1238 A u f _60397 _60398 x).
Proof. exact (MK_COMB (@lem4886540 A u _60397) (@lem4886539 A f _60397 _60398 x)). Qed.
Lemma lem4886543 (a : Prop) (b : Prop) : (term1210 a b) = (term1211 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4886544 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1238 A u f _60397 _60398 x) = (term1239 A u f _60397 _60398 x).
Proof. exact (@lem4886543 (@I ((A -> Prop) -> Prop) u _60397) (term1205 A f _60397 _60398 x)). Qed.
Lemma lem4886545 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1177 A u f _60397 _60398 x) = (term1239 A u f _60397 _60398 x).
Proof. exact (TRANS (@lem4886541 A u f _60397 _60398 x) (@lem4886544 A u f _60397 _60398 x)). Qed.
Lemma lem4886547 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4886548 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1239 A u f _60397 _60398 x) = (term1240 A u f _60397 _60398 x).
Proof. exact (@lem4886547 (term1206 A u f _60397 _60398 x)). Qed.
Lemma lem4886549 {A : Type'} (u : type686 A) (f : type639 A) (_60397 : A -> Prop) (_60398 : A -> Prop) (x : A) : (term1177 A u f _60397 _60398 x) = (term1240 A u f _60397 _60398 x).
Proof. exact (TRANS (@lem4886545 A u f _60397 _60398 x) (@lem4886548 A u f _60397 _60398 x)). Qed.
Lemma lem4886551 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term628 A f t' s x.
Proof. exact (conj (@lem4886404 A s x P t' f u h1 h2) (@lem4886536 A s x P t' f u h1 h2)). Qed.
Lemma lem4886552 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term1241 A u f t' s x.
Proof. exact (conj (@lem4886272 A f u s x h1) (@lem4886551 A s x P t' f u h1 h2)). Qed.
Lemma lem4886554 {A : Type'} (_60397 : A -> Prop) (_60398 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1240 A u f _60397 _60398 x.
Proof. exact (EQ_MP (@lem4886549 A u f _60397 _60398 x) (@lem4885926 A _60397 _60398 f u s x h1)). Qed.
Lemma lem4886555 {A : Type'} (_60397 : A -> Prop) (_60398 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1240 A u f _60397 _60398 x.
Proof. exact (@lem4886554 A _60397 _60398 f u s x h1). Qed.
Lemma lem4886556 {A : Type'} (t' : type667 A) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1162 A f u s x) : term1242 A u f t' s x.
Proof. exact (@lem4886555 A s (term618 A t' s x) f u s x h1). Qed.
Lemma lem4886559 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : False.
Proof. exact (@lem4886556 A t' f u s x h1 (@lem4886552 A s x P t' f u h1 h2)). Qed.
Lemma lem4886560 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : term911.
Proof. exact (fun h0 : ~ False => @lem4886559 A s x P t' f u h1 h2). Qed.
Lemma lem4886562 (p : Prop) : (term889 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4886563 : term911 = False.
Proof. exact (@lem4886562 False). Qed.
Lemma lem4886564 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1162 A f u s x) (h2 : term598 A P t' f u) : False.
Proof. exact (EQ_MP (@lem4886563) (@lem4886560 A s x P t' f u h1 h2)). Qed.
Lemma lem4886565 {A : Type'} (P : type686 A) (t' : type667 A) (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term598 A P t' f u) (h2 : term1148 A t f u s x) : False.
Proof. exact (or_elim (@lem4884720 A t f u s x h2) (fun h0 : term1169 A f s t u x => @lem4886265 A P t' f s t u x h1 h0) (fun h0 : term1162 A f u s x => @lem4886564 A s x P t' f u h0 h1)). Qed.
Lemma lem4886566 {A : Type'} (P : type686 A) (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term348 A P f u) (h2 : term1148 A t f u s x) : False.
Proof. exact (ex_elim (@lem4884159 A P f u h1) (fun t' : type667 A => fun h0 : term600 A P f u t' => @lem4886565 A P t' t f u s x h0 h2)). Qed.
Lemma lem4886567 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1151 A f u s x) (h2 : term348 A P f u) : False.
Proof. exact (ex_elim (@lem4884573 A f u s x h1) (fun t : A -> Prop => fun h0 : term1150 A f u s x t => @lem4886566 A P t f u s x h2 h0)). Qed.
Lemma lem4886568 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1023 A f u x) (h2 : term348 A P f u) : False.
Proof. exact (ex_elim (@lem4884572 A f u x h1) (fun s : A -> Prop => fun h0 : term1152 A f u x s => @lem4886567 A s x P f u h0 h2)). Qed.
Lemma lem4886569 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1023 A f u x) (h2 : term348 A P f u) : (term1023 A f u x) = False.
Proof. exact (prop_ext (fun h3 : term1023 A f u x => @lem4886568 A x P f u h1 h2) (fun h3 : False => @lem4883522 A f u x h1)). Qed.
Lemma lem4886570 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1023 A f u x) (h2 : term348 A P f u) : False.
Proof. exact (EQ_MP (@lem4886569 A x P f u h1 h2) (@lem4883522 A f u x h1)). Qed.
Lemma lem4886571 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term1022 A f u x.
Proof. exact (fun h0 : term1023 A f u x => @lem4886570 A x P f u h0 h1). Qed.
Lemma lem4886572 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : (term993 A u f x) = (term999 A u x).
Proof. exact (EQ_MP (@lem4883521 A f u x) (@lem4886571 A x P f u h1)). Qed.
Lemma lem4886577 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term348 A P f u) : term1002 A f u.
Proof. exact (fun x : A => @lem4886572 A x P f u h1). Qed.
Lemma lem4886578 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1003 A P f u.
Proof. exact (fun h0 : term348 A P f u => @lem4886577 A P f u h0). Qed.
Lemma lem4886583 {A : Type'} (f : type639 A) (u : type686 A) : term1013 A f u.
Proof. exact (fun P : type686 A => @lem4886578 A P f u). Qed.
Lemma lem4886588 {A : Type'} (u : type686 A) : term1017 A u.
Proof. exact (fun f : type639 A => @lem4886583 A f u). Qed.
Lemma lem4886593 {A : Type'} : term1021 A.
Proof. exact (fun u : type686 A => @lem4886588 A u). Qed.
Lemma lem4886594 {A : Type'} : term1020 A.
Proof. exact (EQ_MP (@lem4883516 A) (@lem4886593 A)). Qed.
Lemma lem4886595 {A : Type'} (u : type686 A) : term1243 A u.
Proof. exact (@lem4886594 A u). Qed.
Lemma lem4886596 {A : Type'} (u : type686 A) : (term1243 A u) = (term1016 A u).
Proof. exact (eq_refl (term1243 A u)). Qed.
Lemma lem4886597 {A : Type'} (u : type686 A) : term1016 A u.
Proof. exact (EQ_MP (@lem4886596 A u) (@lem4886595 A u)). Qed.
Lemma lem4886598 {A : Type'} (u : type686 A) (f : type639 A) : term1244 A u f.
Proof. exact (@lem4886597 A u f). Qed.
Lemma lem4886599 {A : Type'} (f : type639 A) (u : type686 A) : (term1244 A u f) = (term1012 A f u).
Proof. exact (eq_refl (term1244 A u f)). Qed.
Lemma lem4886600 {A : Type'} (f : type639 A) (u : type686 A) : term1012 A f u.
Proof. exact (EQ_MP (@lem4886599 A f u) (@lem4886598 A u f)). Qed.
Lemma lem4886601 {A : Type'} (f : type639 A) (u : type686 A) (P : type686 A) : term1245 A f u P.
Proof. exact (@lem4886600 A f u P). Qed.
Lemma lem4886602 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1245 A f u P) = (term1004 A P f u).
Proof. exact (eq_refl (term1245 A f u P)). Qed.
Lemma lem4886603 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1004 A P f u.
Proof. exact (EQ_MP (@lem4886602 A P f u) (@lem4886601 A f u P)). Qed.
Lemma lem4886605 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1004 A P f u.
Proof. exact (@lem4883136 A P f u (@lem4886603 A P f u)). Qed.
Lemma lem4886606 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1005 A P f u) : False.
Proof. exact (@lem4886605 A P f u (@lem4883120 A P f u h1)). Qed.
Lemma lem4886607 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1005 A P f u) : (term1005 A P f u) = False.
Proof. exact (prop_ext (fun h2 : term1005 A P f u => @lem4886606 A P f u h1) (fun h2 : False => @lem4883120 A P f u h1)). Qed.
Lemma lem4886608 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1005 A P f u) : False.
Proof. exact (EQ_MP (@lem4886607 A P f u h1) (@lem4883120 A P f u h1)). Qed.
Lemma lem4886609 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1004 A P f u.
Proof. exact (fun h0 : term1005 A P f u => @lem4886608 A P f u h0). Qed.
Lemma lem4886610 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term1003 A P f u.
Proof. exact (EQ_MP (@lem4883119 A P f u) (@lem4886609 A P f u)). Qed.
Lemma lem4886611 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term974 A P f u.
Proof. exact (EQ_MP (@lem4883115 A P f u) (@lem4886610 A P f u)). Qed.
Lemma lem4886612 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term973 A P f u.
Proof. exact (EQ_MP (@lem4882868 A P f u) (@lem4886611 A P f u)). Qed.
Lemma lem4886613 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term964 A u f) = (@UNIONS A u).
Proof. exact (@lem4886612 A P f u (@lem4882773 A P f u h1 h2)). Qed.
Lemma lem4886614 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term917 A u f) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4882762 A f u) (@lem4886613 A P f u h1 h2)). Qed.
Lemma lem4886615 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : (term294 A u f) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4882648 A f u) (@lem4886614 A P f u h1 h2)). Qed.
Lemma lem4886616 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term295 A P f u.
Proof. exact (conj (@lem4882615 A P f u h1 h2) (@lem4886615 A P f u h1 h2)). Qed.
Lemma lem4886617 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term227 A P f u.
Proof. exact (EQ_MP (@lem4880459 A P f u) (@lem4886616 A P f u h1 h2)). Qed.
Lemma lem4886618 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term228 A P f u.
Proof. exact (EQ_MP (@lem4880346 A P f u h1 h2) (@lem4886617 A P f u h1 h2)). Qed.
Lemma lem4886619 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @FINITE (A -> Prop) u) : term136 A P u.
Proof. exact (ex_intro (term1246 A P u) (term1247 A u f) (@lem4886618 A P f u h1 h2)). Qed.
Lemma lem4886620 {A : Type'} (f : type639 A) (P : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : term176 A f P u.
Proof. exact (fun h0 : term157 A u P f => @lem4886619 A P f u h0 h1). Qed.
Lemma lem4886625 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : term179 A P u.
Proof. exact (fun f : type639 A => @lem4886620 A f P u h1). Qed.
Lemma lem4886626 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : term137 A P u.
Proof. exact (EQ_MP (@lem4879993 A P u) (@lem4886625 A P u h1)). Qed.
Lemma lem4886627 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : term112 A P u.
Proof. exact (EQ_MP (@lem4879853 A P u) (@lem4886626 A P u h1)). Qed.
Lemma lem4886628 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : (@UNIONS A u) = s.
Proof. exact (proj2 (@lem4879809 A P u s h1)). Qed.
Lemma lem4886629 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term69 A u P.
Proof. exact (proj1 (@lem4879809 A P u s h1)). Qed.
Lemma lem4886630 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : (@UNIONS A u) = s) : term114 A u P s.
Proof. exact (EQ_MP (@lem4879825 A P u s h2) (@lem4886627 A P u h1)). Qed.
Lemma lem4886631 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : (@UNIONS A u) = s) : term59 A P s.
Proof. exact (@lem4886630 A P u s h2 h3 (@lem4879812 A u P h1)). Qed.
Lemma lem4886632 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term73 A P u s) : ((@UNIONS A u) = s) = (term59 A P s).
Proof. exact (prop_ext (fun h4 : (@UNIONS A u) = s => @lem4886631 A P u s h1 h2 h4) (fun h4 : term59 A P s => @lem4886628 A P u s h3)). Qed.
Lemma lem4886633 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @FINITE (A -> Prop) u) (h3 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4886632 A P u s h1 h2 h3) (@lem4886628 A P u s h3)). Qed.
Lemma lem4886634 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term73 A P u s) : (term69 A u P) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : term69 A u P => @lem4886633 A P u s h3 h1 h2) (fun h3 : term59 A P s => @lem4886629 A P u s h2)). Qed.
Lemma lem4886635 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4886634 A P u s h1 h2) (@lem4886629 A P u s h2)). Qed.
Lemma lem4886636 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : term1248 A u P s.
Proof. exact (fun h0 : term73 A P u s => @lem4886635 A P u s h1 h0). Qed.
Lemma lem4886637 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term73 A P u s.
Proof. exact (proj2 (@lem4879806 A P u s h1)). Qed.
Lemma lem4886638 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4879806 A P u s h1)). Qed.
Lemma lem4886639 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (@lem4886636 A P s u h1 (@lem4879807 A P u s h2)). Qed.
Lemma lem4886640 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term73 A P u s) : (@FINITE (A -> Prop) u) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : @FINITE (A -> Prop) u => @lem4886639 A P u s h1 h2) (fun h3 : term59 A P s => @lem4879808 A u h1)). Qed.
Lemma lem4886641 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4886640 A P u s h1 h2) (@lem4879808 A u h1)). Qed.
Lemma lem4886642 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term76 A P u s) : (term73 A P u s) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : term73 A P u s => @lem4886641 A P u s h1 h3) (fun h3 : term59 A P s => @lem4886637 A P u s h2)). Qed.
Lemma lem4886643 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @FINITE (A -> Prop) u) (h2 : term76 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4886642 A P u s h1 h2) (@lem4886637 A P u s h2)). Qed.
Lemma lem4886644 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : (@FINITE (A -> Prop) u) = (term59 A P s).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) u => @lem4886643 A P u s h2 h1) (fun h2 : term59 A P s => @lem4886638 A P u s h1)). Qed.
Lemma lem4886645 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4886644 A P u s h1) (@lem4886638 A P u s h1)). Qed.
Lemma lem4886646 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : term105 A u P s.
Proof. exact (fun h0 : term76 A P u s => @lem4886645 A P u s h0). Qed.
Lemma lem4886651 {A : Type'} (P : type686 A) (s : A -> Prop) : term108 A P s.
Proof. exact (fun u : type686 A => @lem4886646 A u P s). Qed.
Lemma lem4886653 {A : Type'} (P : type686 A) (s : A -> Prop) : term90 A P s.
Proof. exact (EQ_MP (@lem4879805 A P s) (@lem4886651 A P s)). Qed.
Lemma lem4886654 {A : Type'} (P : type686 A) (s : A -> Prop) : term1249 A P s.
Proof. exact (conj (@lem4886653 A P s) (@lem4879522 A P s)). Qed.
Lemma lem4886655 {A : Type'} (P : type686 A) (s : A -> Prop) : (term1249 A P s) = ((term82 A P s) = (@UNION_OF A (@FINITE (A -> Prop)) P s)).
Proof. exact (@lem32 (term82 A P s) (@UNION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4886656 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (@UNION_OF A (@FINITE (A -> Prop)) P s).
Proof. exact (EQ_MP (@lem4886655 A P s) (@lem4886654 A P s)). Qed.
Lemma lem4886661 {A : Type'} (P : type686 A) : term51 A P.
Proof. exact (fun s : A -> Prop => @lem4886656 A P s). Qed.
Lemma lem4886662 {A : Type'} (P : type686 A) : (term50 A P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (EQ_MP (@lem4879508 A P) (@lem4886661 A P)). Qed.
Lemma lem4886667 {A : Type'} : term1250 A.
Proof. exact (fun P : type686 A => @lem4886662 A P). Qed.
