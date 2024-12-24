Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8049688_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8049402 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8049403 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8049404 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8049403 _141927 _141928 _141929 s) (@lem8049402 _141927 _141928 _141929 s)). Qed.
Lemma lem8049405 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8049404 _141927 _141928 _141929 s t). Qed.
Lemma lem8049406 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049407 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8049406 _141927 _141928 _141929 s t) (@lem8049405 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049408 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8049407 _141927 _141928 _141929 s t x). Qed.
Lemma lem8049409 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049410 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8049409 _141927 _141928 _141929 x s t) (@lem8049408 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049411 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8049410 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8049412 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049438 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem8049439 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem8049438 _83095 p). Qed.
Lemma lem8049440 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem8049441 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem8049440 _83095 p) (@lem8049439 _83095 p)). Qed.
Lemma lem8049442 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem8049441 _83095 p x). Qed.
Lemma lem8049443 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem8049452 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8049453 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8049454 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8049453 A s) (@lem8049452 A s)). Qed.
Lemma lem8049455 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8049454 A s t). Qed.
Lemma lem8049456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8049473 {_89711 _89725 : Type'} : term18 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem8049474 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term19 _89711 _89725 P.
Proof. exact (@lem8049473 _89711 _89725 P). Qed.
Lemma lem8049475 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term19 _89711 _89725 P) = (term20 _89711 _89725 P).
Proof. exact (eq_refl (term19 _89711 _89725 P)). Qed.
Lemma lem8049476 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term20 _89711 _89725 P.
Proof. exact (EQ_MP (@lem8049475 _89711 _89725 P) (@lem8049474 _89711 _89725 P)). Qed.
Lemma lem8049477 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term21 _89711 _89725 P f.
Proof. exact (@lem8049476 _89711 _89725 P f). Qed.
Lemma lem8049478 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P f) = ((term22 _89711 _89725 P f) = (term23 _89711 _89725 P f)).
Proof. exact (eq_refl (term21 _89711 _89725 P f)). Qed.
Lemma lem8049496 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8049456 A s t) (@lem8049455 A s t)). Qed.
Lemma lem8049497 {_142951 _142952 _142953 : Type'} (s : type16 _142951 _142952 _142953) (t : type16 _142951 _142952 _142953) : (s = t) = (term24 _142951 _142952 _142953 s t).
Proof. exact (@lem8049496 (type2 _142951 _142952 _142953) s t). Qed.
Lemma lem8049498 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f)) = (term27 _142951 _142952 _142953 g f).
Proof. exact (@lem8049497 _142951 _142952 _142953 (term25 _142951 _142952 _142953 f g) (term26 _142951 _142952 _142953 f)). Qed.
Lemma lem8049504 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term28 _140454 _140455 _140456 P) = (term29 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8049505 {_142951 _142952 _142953 : Type'} (P : type16 _142951 _142952 _142953) : (term28 _142951 _142952 _142953 P) = (term29 _142951 _142952 _142953 P).
Proof. exact (@lem8049504 _142951 _142952 _142953 P). Qed.
Lemma lem8049506 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term30 _142951 _142952 _142953 g f) = (term31 _142951 _142952 _142953 g f).
Proof. exact (@lem8049505 _142951 _142952 _142953 (term32 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049507 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term33 _142951 _142952 _142953 g f x) = ((term34 _142951 _142952 _142953 x f g) = (term35 _142951 _142952 _142953 x f)).
Proof. exact (eq_refl (term33 _142951 _142952 _142953 g f x)). Qed.
Lemma lem8049508 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term36 _142951 _142952 _142953 g f) = (term32 _142951 _142952 _142953 g f).
Proof. exact (fun_ext (fun x : type2 _142951 _142952 _142953 => @lem8049507 _142951 _142952 _142953 g x f)). Qed.
Lemma lem8049509 {_142951 _142952 _142953 : Type'} : (@all (cart _142951 (finite_sum _142952 _142953))) = (@all (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@all (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049510 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term30 _142951 _142952 _142953 g f) = (term27 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8049509 _142951 _142952 _142953) (@lem8049508 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049512 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term37 _142951 _142952 _142953 g f) = (term38 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8049511) (@lem8049510 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049513 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) : (term39 _142951 _142952 _142953 g f x y) = ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y f)).
Proof. exact (eq_refl (term39 _142951 _142952 _142953 g f x y)). Qed.
Lemma lem8049514 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (f : type56 _142951 _142952) : (term42 _142951 _142952 _142953 g f x) = (term43 _142951 _142952 _142953 g x f).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049513 _142951 _142952 _142953 g x y f)). Qed.
Lemma lem8049515 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8049516 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (f : type56 _142951 _142952) : (term44 _142951 _142952 _142953 g f x) = (term45 _142951 _142952 _142953 g x f).
Proof. exact (MK_COMB (@lem8049515 _142951 _142953) (@lem8049514 _142951 _142952 _142953 g x f)). Qed.
Lemma lem8049517 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term46 _142951 _142952 _142953 g f) = (term47 _142951 _142952 _142953 g f).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8049516 _142951 _142952 _142953 g x f)). Qed.
Lemma lem8049518 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8049519 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term31 _142951 _142952 _142953 g f) = (term48 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8049518 _142951 _142952) (@lem8049517 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049520 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : ((term30 _142951 _142952 _142953 g f) = (term31 _142951 _142952 _142953 g f)) = ((term27 _142951 _142952 _142953 g f) = (term48 _142951 _142952 _142953 g f)).
Proof. exact (MK_COMB (@lem8049512 _142951 _142952 _142953 g f) (@lem8049519 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049521 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term27 _142951 _142952 _142953 g f) = (term48 _142951 _142952 _142953 g f).
Proof. exact (EQ_MP (@lem8049520 _142951 _142952 _142953 g f) (@lem8049506 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049528 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f)) = (term48 _142951 _142952 _142953 g f).
Proof. exact (TRANS (@lem8049498 _142951 _142952 _142953 g f) (@lem8049521 _142951 _142952 _142953 g f)). Qed.
Lemma lem8049540 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049412 _141927 _141928 _141929 x s y t) (@lem8049411 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049541 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049540 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049542 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term40 _142951 _142952 _142953 x y f g) = (term49 _142951 _142952 _142953 x f y g).
Proof. exact (@lem8049541 _142951 _142952 _142953 x (@INTERS (cart _142951 _142952) f) y (@INTERS (cart _142951 _142953) g)). Qed.
Lemma lem8049546 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : g = (@EMPTY ((cart _142951 _142953) -> Prop)).
Proof. exact (h1). Qed.
Lemma lem8049547 {_142951 _142953 : Type'} : (@INTERS (cart _142951 _142953)) = (@INTERS (cart _142951 _142953)).
Proof. exact (eq_refl (@INTERS (cart _142951 _142953))). Qed.
Lemma lem8049548 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (@INTERS (cart _142951 _142953) g) = (@INTERS (cart _142951 _142953) (@EMPTY ((cart _142951 _142953) -> Prop))).
Proof. exact (MK_COMB (@lem8049547 _142951 _142953) (@lem8049546 _142951 _142953 g h1)). Qed.
Lemma lem8049549 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y) = (@IN (cart _142951 _142953) y).
Proof. exact (eq_refl (@IN (cart _142951 _142953) y)). Qed.
Lemma lem8049550 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term50 _142951 _142953 y g) = (term51 _142951 _142953 y).
Proof. exact (MK_COMB (@lem8049549 _142951 _142953 y) (@lem8049548 _142951 _142953 g h1)). Qed.
Lemma lem8049551 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) : (term52 _142951 _142952 x f) = (term52 _142951 _142952 x f).
Proof. exact (eq_refl (term52 _142951 _142952 x f)). Qed.
Lemma lem8049552 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term49 _142951 _142952 _142953 x f y g) = (term53 _142951 _142952 _142953 x f y).
Proof. exact (MK_COMB (@lem8049551 _142951 _142952 x f) (@lem8049550 _142951 _142953 y g h1)). Qed.
Lemma lem8049555 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term40 _142951 _142952 _142953 x y f g) = (term53 _142951 _142952 _142953 x f y).
Proof. exact (TRANS (@lem8049542 _142951 _142952 _142953 x f y g) (@lem8049552 _142951 _142952 _142953 x f y g h1)). Qed.
Lemma lem8049556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049557 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term54 _142951 _142952 _142953 x y f g) = (term55 _142951 _142952 _142953 x f y).
Proof. exact (MK_COMB (@lem8049556) (@lem8049555 _142951 _142952 _142953 x f y g h1)). Qed.
Lemma lem8049559 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P f) = (term23 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem8049478 _89711 _89725 P f) (@lem8049477 _89711 _89725 P f)). Qed.
Lemma lem8049560 {_142951 _142952 _142953 : Type'} (P : type56 _142951 _142952) (f : type52 _142951 _142952 _142953) : (term56 _142951 _142952 _142953 P f) = (term57 _142951 _142952 _142953 P f).
Proof. exact (@lem8049559 (type2 _142951 _142952 _142953) (type24 _142951 _142952) P f). Qed.
Lemma lem8049561 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term58 _142951 _142952 _142953 f) = (term59 _142951 _142952 _142953 f).
Proof. exact (@lem8049560 _142951 _142952 _142953 (term60 _142951 _142952 f) (term61 _142951 _142952 _142953)). Qed.
Lemma lem8049562 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) : (term62 _142951 _142952 f s) = (@IN ((cart _142951 _142952) -> Prop) s f).
Proof. exact (eq_refl (term62 _142951 _142952 f s)). Qed.
Lemma lem8049563 {_142951 _142952 _142953 : Type'} (GEN_PVAR_366 : type16 _142951 _142952 _142953) : (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_366) = (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_366).
Proof. exact (eq_refl (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_366)). Qed.
Lemma lem8049564 {_142951 _142952 _142953 : Type'} (GEN_PVAR_366 : type16 _142951 _142952 _142953) (s : type24 _142951 _142952) (f : type56 _142951 _142952) : (term63 _142951 _142952 _142953 GEN_PVAR_366 f s) = (term64 _142951 _142952 _142953 GEN_PVAR_366 s f).
Proof. exact (MK_COMB (@lem8049563 _142951 _142952 _142953 GEN_PVAR_366) (@lem8049562 _142951 _142952 s f)). Qed.
Lemma lem8049565 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) : (term65 _142951 _142952 _142953 s) = (@PCROSS _142951 _142952 _142953 s (@UNIV (cart _142951 _142953))).
Proof. exact (eq_refl (term65 _142951 _142952 _142953 s)). Qed.
Lemma lem8049566 {_142951 _142952 _142953 : Type'} (GEN_PVAR_366 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term66 _142951 _142952 _142953 GEN_PVAR_366 f s) = (term67 _142951 _142952 _142953 GEN_PVAR_366 f s).
Proof. exact (MK_COMB (@lem8049564 _142951 _142952 _142953 GEN_PVAR_366 s f) (@lem8049565 _142951 _142952 _142953 s)). Qed.
Lemma lem8049567 {_142951 _142952 _142953 : Type'} (GEN_PVAR_366 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term68 _142951 _142952 _142953 GEN_PVAR_366 f) = (term69 _142951 _142952 _142953 GEN_PVAR_366 f).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049566 _142951 _142952 _142953 GEN_PVAR_366 f s)). Qed.
Lemma lem8049568 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049569 {_142951 _142952 _142953 : Type'} (GEN_PVAR_366 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term70 _142951 _142952 _142953 GEN_PVAR_366 f) = (term71 _142951 _142952 _142953 GEN_PVAR_366 f).
Proof. exact (MK_COMB (@lem8049568 _142951 _142952) (@lem8049567 _142951 _142952 _142953 GEN_PVAR_366 f)). Qed.
Lemma lem8049570 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term72 _142951 _142952 _142953 f) = (term73 _142951 _142952 _142953 f).
Proof. exact (fun_ext (fun GEN_PVAR_366 : type16 _142951 _142952 _142953 => @lem8049569 _142951 _142952 _142953 GEN_PVAR_366 f)). Qed.
Lemma lem8049571 {_142951 _142952 _142953 : Type'} : (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049572 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term74 _142951 _142952 _142953 f) = (term75 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049571 _142951 _142952 _142953) (@lem8049570 _142951 _142952 _142953 f)). Qed.
Lemma lem8049573 {_142951 _142952 _142953 : Type'} : (@INTERS (cart _142951 (finite_sum _142952 _142953))) = (@INTERS (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@INTERS (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049574 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term58 _142951 _142952 _142953 f) = (term26 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049573 _142951 _142952 _142953) (@lem8049572 _142951 _142952 _142953 f)). Qed.
Lemma lem8049575 {_142951 _142952 _142953 : Type'} : (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049576 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term76 _142951 _142952 _142953 f) = (term77 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049575 _142951 _142952 _142953) (@lem8049574 _142951 _142952 _142953 f)). Qed.
Lemma lem8049577 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) : (term62 _142951 _142952 f s) = (@IN ((cart _142951 _142952) -> Prop) s f).
Proof. exact (eq_refl (term62 _142951 _142952 f s)). Qed.
Lemma lem8049578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8049579 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) : (term78 _142951 _142952 f s) = (term79 _142951 _142952 s f).
Proof. exact (MK_COMB (@lem8049578) (@lem8049577 _142951 _142952 s f)). Qed.
Lemma lem8049580 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) : (term65 _142951 _142952 _142953 s) = (@PCROSS _142951 _142952 _142953 s (@UNIV (cart _142951 _142953))).
Proof. exact (eq_refl (term65 _142951 _142952 _142953 s)). Qed.
Lemma lem8049581 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : (@IN (cart _142951 (finite_sum _142952 _142953)) a) = (@IN (cart _142951 (finite_sum _142952 _142953)) a).
Proof. exact (eq_refl (@IN (cart _142951 (finite_sum _142952 _142953)) a)). Qed.
Lemma lem8049582 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) : (term80 _142951 _142952 _142953 a s) = (term81 _142951 _142952 _142953 a s).
Proof. exact (MK_COMB (@lem8049581 _142951 _142952 _142953 a) (@lem8049580 _142951 _142952 _142953 s)). Qed.
Lemma lem8049583 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) : (term82 _142951 _142952 _142953 f a s) = (term83 _142951 _142952 _142953 f a s).
Proof. exact (MK_COMB (@lem8049579 _142951 _142952 s f) (@lem8049582 _142951 _142952 _142953 a s)). Qed.
Lemma lem8049584 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term84 _142951 _142952 _142953 f a) = (term85 _142951 _142952 _142953 f a).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049583 _142951 _142952 _142953 f a s)). Qed.
Lemma lem8049585 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049586 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term86 _142951 _142952 _142953 f a) = (term87 _142951 _142952 _142953 f a).
Proof. exact (MK_COMB (@lem8049585 _142951 _142952) (@lem8049584 _142951 _142952 _142953 f a)). Qed.
Lemma lem8049587 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56)). Qed.
Lemma lem8049588 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term88 _142951 _142952 _142953 GEN_PVAR_56 f a) = (term89 _142951 _142952 _142953 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem8049587 _142951 _142952 _142953 GEN_PVAR_56) (@lem8049586 _142951 _142952 _142953 f a)). Qed.
Lemma lem8049589 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049590 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term90 _142951 _142952 _142953 GEN_PVAR_56 f a) = (term91 _142951 _142952 _142953 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem8049588 _142951 _142952 _142953 GEN_PVAR_56 f a) (@lem8049589 _142951 _142952 _142953 a)). Qed.
Lemma lem8049591 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term92 _142951 _142952 _142953 GEN_PVAR_56 f) = (term93 _142951 _142952 _142953 GEN_PVAR_56 f).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049590 _142951 _142952 _142953 GEN_PVAR_56 f a)). Qed.
Lemma lem8049592 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049593 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term94 _142951 _142952 _142953 GEN_PVAR_56 f) = (term95 _142951 _142952 _142953 GEN_PVAR_56 f).
Proof. exact (MK_COMB (@lem8049592 _142951 _142952 _142953) (@lem8049591 _142951 _142952 _142953 GEN_PVAR_56 f)). Qed.
Lemma lem8049594 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term96 _142951 _142952 _142953 f) = (term97 _142951 _142952 _142953 f).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _142951 _142952 _142953 => @lem8049593 _142951 _142952 _142953 GEN_PVAR_56 f)). Qed.
Lemma lem8049595 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049596 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term59 _142951 _142952 _142953 f) = (term98 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049595 _142951 _142952 _142953) (@lem8049594 _142951 _142952 _142953 f)). Qed.
Lemma lem8049597 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : ((term58 _142951 _142952 _142953 f) = (term59 _142951 _142952 _142953 f)) = ((term26 _142951 _142952 _142953 f) = (term98 _142951 _142952 _142953 f)).
Proof. exact (MK_COMB (@lem8049576 _142951 _142952 _142953 f) (@lem8049596 _142951 _142952 _142953 f)). Qed.
Lemma lem8049598 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term26 _142951 _142952 _142953 f) = (term98 _142951 _142952 _142953 f).
Proof. exact (EQ_MP (@lem8049597 _142951 _142952 _142953 f) (@lem8049561 _142951 _142952 _142953 f)). Qed.
Lemma lem8049611 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term99 _142951 _142952 _142953 x y) = (term99 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term99 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049612 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) : (term41 _142951 _142952 _142953 x y f) = (term100 _142951 _142952 _142953 x y f).
Proof. exact (MK_COMB (@lem8049611 _142951 _142952 _142953 x y) (@lem8049598 _142951 _142952 _142953 f)). Qed.
Lemma lem8049614 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem8049443 _83095 p x) (@lem8049442 _83095 p x)). Qed.
Lemma lem8049615 {_142951 _142952 _142953 : Type'} (p : type16 _142951 _142952 _142953) (x : type2 _142951 _142952 _142953) : (term101 _142951 _142952 _142953 x p) = (p x).
Proof. exact (@lem8049614 (type2 _142951 _142952 _142953) p x). Qed.
Lemma lem8049616 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term102 _142951 _142952 _142953 x y f) = (term103 _142951 _142952 _142953 f x y).
Proof. exact (@lem8049615 _142951 _142952 _142953 (term104 _142951 _142952 _142953 f) (@pastecart _142951 _142952 _142953 x y)). Qed.
Lemma lem8049617 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term105 _142951 _142952 _142953 f a) = (term87 _142951 _142952 _142953 f a).
Proof. exact (eq_refl (term105 _142951 _142952 _142953 f a)). Qed.
Lemma lem8049618 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56)). Qed.
Lemma lem8049619 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term106 _142951 _142952 _142953 GEN_PVAR_56 f a) = (term89 _142951 _142952 _142953 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem8049618 _142951 _142952 _142953 GEN_PVAR_56) (@lem8049617 _142951 _142952 _142953 f a)). Qed.
Lemma lem8049620 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049621 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (a : type2 _142951 _142952 _142953) : (term107 _142951 _142952 _142953 GEN_PVAR_56 f a) = (term91 _142951 _142952 _142953 GEN_PVAR_56 f a).
Proof. exact (MK_COMB (@lem8049619 _142951 _142952 _142953 GEN_PVAR_56 f a) (@lem8049620 _142951 _142952 _142953 a)). Qed.
Lemma lem8049622 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term108 _142951 _142952 _142953 GEN_PVAR_56 f) = (term93 _142951 _142952 _142953 GEN_PVAR_56 f).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049621 _142951 _142952 _142953 GEN_PVAR_56 f a)). Qed.
Lemma lem8049623 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049624 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) : (term109 _142951 _142952 _142953 GEN_PVAR_56 f) = (term95 _142951 _142952 _142953 GEN_PVAR_56 f).
Proof. exact (MK_COMB (@lem8049623 _142951 _142952 _142953) (@lem8049622 _142951 _142952 _142953 GEN_PVAR_56 f)). Qed.
Lemma lem8049625 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term110 _142951 _142952 _142953 f) = (term97 _142951 _142952 _142953 f).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _142951 _142952 _142953 => @lem8049624 _142951 _142952 _142953 GEN_PVAR_56 f)). Qed.
Lemma lem8049626 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049627 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term111 _142951 _142952 _142953 f) = (term98 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049626 _142951 _142952 _142953) (@lem8049625 _142951 _142952 _142953 f)). Qed.
Lemma lem8049628 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term99 _142951 _142952 _142953 x y) = (term99 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term99 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049629 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) : (term102 _142951 _142952 _142953 x y f) = (term100 _142951 _142952 _142953 x y f).
Proof. exact (MK_COMB (@lem8049628 _142951 _142952 _142953 x y) (@lem8049627 _142951 _142952 _142953 f)). Qed.
Lemma lem8049630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049631 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) : (term112 _142951 _142952 _142953 x y f) = (term113 _142951 _142952 _142953 x y f).
Proof. exact (MK_COMB (@lem8049630) (@lem8049629 _142951 _142952 _142953 x y f)). Qed.
Lemma lem8049632 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term103 _142951 _142952 _142953 f x y) = (term114 _142951 _142952 _142953 f x y).
Proof. exact (eq_refl (term103 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049633 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term102 _142951 _142952 _142953 x y f) = (term103 _142951 _142952 _142953 f x y)) = ((term100 _142951 _142952 _142953 x y f) = (term114 _142951 _142952 _142953 f x y)).
Proof. exact (MK_COMB (@lem8049631 _142951 _142952 _142953 x y f) (@lem8049632 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049634 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term100 _142951 _142952 _142953 x y f) = (term114 _142951 _142952 _142953 f x y).
Proof. exact (EQ_MP (@lem8049633 _142951 _142952 _142953 f x y) (@lem8049616 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049644 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049412 _141927 _141928 _141929 x s y t) (@lem8049411 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049645 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049644 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049646 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) : (term115 _142951 _142952 _142953 x y s) = (term116 _142951 _142952 _142953 x s y).
Proof. exact (@lem8049645 _142951 _142952 _142953 x s y (@UNIV (cart _142951 _142953))). Qed.
Lemma lem8049649 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) : (term79 _142951 _142952 s f) = (term79 _142951 _142952 s f).
Proof. exact (eq_refl (term79 _142951 _142952 s f)). Qed.
Lemma lem8049650 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) : (term117 _142951 _142952 _142953 f x y s) = (term118 _142951 _142952 _142953 f x s y).
Proof. exact (MK_COMB (@lem8049649 _142951 _142952 s f) (@lem8049646 _142951 _142952 _142953 x s y)). Qed.
Lemma lem8049653 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term119 _142951 _142952 _142953 f x y) = (term120 _142951 _142952 _142953 f x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049650 _142951 _142952 _142953 f x s y)). Qed.
Lemma lem8049654 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049655 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term114 _142951 _142952 _142953 f x y) = (term121 _142951 _142952 _142953 f x y).
Proof. exact (MK_COMB (@lem8049654 _142951 _142952) (@lem8049653 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049662 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term100 _142951 _142952 _142953 x y f) = (term121 _142951 _142952 _142953 f x y).
Proof. exact (TRANS (@lem8049634 _142951 _142952 _142953 f x y) (@lem8049655 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049663 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term41 _142951 _142952 _142953 x y f) = (term121 _142951 _142952 _142953 f x y).
Proof. exact (TRANS (@lem8049612 _142951 _142952 _142953 x y f) (@lem8049662 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049664 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y f)) = ((term53 _142951 _142952 _142953 x f y) = (term121 _142951 _142952 _142953 f x y)).
Proof. exact (MK_COMB (@lem8049557 _142951 _142952 _142953 x f y g h1) (@lem8049663 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8049669 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term43 _142951 _142952 _142953 g x f) = (term122 _142951 _142952 _142953 f x).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049664 _142951 _142952 _142953 f x y g h1)). Qed.
Lemma lem8049670 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8049671 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term45 _142951 _142952 _142953 g x f) = (term123 _142951 _142952 _142953 f x).
Proof. exact (MK_COMB (@lem8049670 _142951 _142953) (@lem8049669 _142951 _142952 _142953 f x g h1)). Qed.
Lemma lem8049678 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term47 _142951 _142952 _142953 g f) = (term124 _142951 _142952 _142953 f).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8049671 _142951 _142952 _142953 f x g h1)). Qed.
Lemma lem8049679 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8049680 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term48 _142951 _142952 _142953 g f) = (term125 _142951 _142952 _142953 f).
Proof. exact (MK_COMB (@lem8049679 _142951 _142952) (@lem8049678 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8049687 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f)) = (term125 _142951 _142952 _142953 f).
Proof. exact (TRANS (@lem8049528 _142951 _142952 _142953 g f) (@lem8049680 _142951 _142952 _142953 f g h1)). Qed.
Lemma lem8049688 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : (term125 _142951 _142952 _142953 f) = ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f)).
Proof. exact (SYM (@lem8049687 _142951 _142952 _142953 f g h1)). Qed.
