Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BOUND_term_abbrevs.
Require Import SUM_CONST_spec.
Require Import SUM_LE_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7132379 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : (term0 _132484 s c) = (term1 _132484 s c)) : (term0 _132484 s c) = (term1 _132484 s c).
Proof. exact (h1). Qed.
Lemma lem7132380 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : (term0 _132484 s c) = (term1 _132484 s c)) : (term1 _132484 s c) = (term0 _132484 s c).
Proof. exact (SYM (@lem7132379 _132484 s c h1)). Qed.
Lemma lem7132381 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : (term1 _132484 s c) = (term0 _132484 s c)) : (term1 _132484 s c) = (term0 _132484 s c).
Proof. exact (h1). Qed.
Lemma lem7132382 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : (term1 _132484 s c) = (term0 _132484 s c)) : (term0 _132484 s c) = (term1 _132484 s c).
Proof. exact (SYM (@lem7132381 _132484 s c h1)). Qed.
Lemma lem7132383 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : ((term0 _132484 s c) = (term1 _132484 s c)) = ((term1 _132484 s c) = (term0 _132484 s c)).
Proof. exact (prop_ext (fun h1 : (term0 _132484 s c) = (term1 _132484 s c) => @lem7132380 _132484 s c h1) (fun h1 : (term1 _132484 s c) = (term0 _132484 s c) => @lem7132382 _132484 s c h1)). Qed.
Lemma lem7132384 {_132484 : Type'} (s : _132484 -> Prop) : (term2 _132484 s) = (term2 _132484 s).
Proof. exact (eq_refl (term2 _132484 s)). Qed.
Lemma lem7132385 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term3 _132484 s c) = (term4 _132484 s c).
Proof. exact (MK_COMB (@lem7132384 _132484 s) (@lem7132383 _132484 s c)). Qed.
Lemma lem7132386 {_132484 : Type'} (c : real) : (term5 _132484 c) = (term6 _132484 c).
Proof. exact (fun_ext (fun s : _132484 -> Prop => @lem7132385 _132484 s c)). Qed.
Lemma lem7132387 {_132484 : Type'} : (@all (_132484 -> Prop)) = (@all (_132484 -> Prop)).
Proof. exact (eq_refl (@all (_132484 -> Prop))). Qed.
Lemma lem7132388 {_132484 : Type'} (c : real) : (term7 _132484 c) = (term8 _132484 c).
Proof. exact (MK_COMB (@lem7132387 _132484) (@lem7132386 _132484 c)). Qed.
Lemma lem7132389 {_132484 : Type'} : (term9 _132484) = (term10 _132484).
Proof. exact (fun_ext (fun c : real => @lem7132388 _132484 c)). Qed.
Lemma lem7132390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132391 {_132484 : Type'} : (term11 _132484) = (term12 _132484).
Proof. exact (MK_COMB (@lem7132390) (@lem7132389 _132484)). Qed.
Lemma lem7132392 {_132484 : Type'} : term12 _132484.
Proof. exact (EQ_MP (@lem7132391 _132484) (@lem7085323 _132484)). Qed.
Lemma lem7132393 {_132081 : Type'} (f : _132081 -> real) : term13 _132081 f.
Proof. exact (@lem7071845 _132081 f). Qed.
Lemma lem7132394 {_132081 : Type'} (f : _132081 -> real) : (term13 _132081 f) = (term14 _132081 f).
Proof. exact (eq_refl (term13 _132081 f)). Qed.
Lemma lem7132395 {_132081 : Type'} (f : _132081 -> real) : term14 _132081 f.
Proof. exact (EQ_MP (@lem7132394 _132081 f) (@lem7132393 _132081 f)). Qed.
Lemma lem7132396 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term15 _132081 f g.
Proof. exact (@lem7132395 _132081 f g). Qed.
Lemma lem7132397 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term15 _132081 f g) = (term16 _132081 f g).
Proof. exact (eq_refl (term15 _132081 f g)). Qed.
Lemma lem7132398 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term16 _132081 f g.
Proof. exact (EQ_MP (@lem7132397 _132081 f g) (@lem7132396 _132081 f g)). Qed.
Lemma lem7132399 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) : term17 _132081 f g s.
Proof. exact (@lem7132398 _132081 f g s). Qed.
Lemma lem7132400 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term17 _132081 f g s) = (term18 _132081 f s g).
Proof. exact (eq_refl (term17 _132081 f g s)). Qed.
Lemma lem7132401 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term18 _132081 f s g.
Proof. exact (EQ_MP (@lem7132400 _132081 f s g) (@lem7132399 _132081 f g s)). Qed.
Lemma lem7132402 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term19 _132081 s f g) : term19 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7132403 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term19 _132081 s f g) : term20 _132081 f s g.
Proof. exact (@lem7132401 _132081 f s g (@lem7132402 _132081 s f g h1)). Qed.
Lemma lem7132404 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term20 _132081 f s g) = ((term20 _132081 f s g) = True).
Proof. exact (@lem7 (term20 _132081 f s g)). Qed.
Lemma lem7132405 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term19 _132081 s f g) : (term20 _132081 f s g) = True.
Proof. exact (EQ_MP (@lem7132404 _132081 f s g) (@lem7132403 _132081 s f g h1)). Qed.
Lemma lem7132411 {_132484 : Type'} (c : real) : term21 _132484 c.
Proof. exact (@lem7132392 _132484 c). Qed.
Lemma lem7132412 {_132484 : Type'} (c : real) : (term21 _132484 c) = (term8 _132484 c).
Proof. exact (eq_refl (term21 _132484 c)). Qed.
Lemma lem7132413 {_132484 : Type'} (c : real) : term8 _132484 c.
Proof. exact (EQ_MP (@lem7132412 _132484 c) (@lem7132411 _132484 c)). Qed.
Lemma lem7132414 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term22 _132484 c s.
Proof. exact (@lem7132413 _132484 c s). Qed.
Lemma lem7132415 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term22 _132484 c s) = (term4 _132484 s c).
Proof. exact (eq_refl (term22 _132484 c s)). Qed.
Lemma lem7132416 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term4 _132484 s c.
Proof. exact (EQ_MP (@lem7132415 _132484 s c) (@lem7132414 _132484 c s)). Qed.
Lemma lem7132417 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7132418 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term1 _132484 s c) = (term0 _132484 s c).
Proof. exact (@lem7132416 _132484 s c (@lem7132417 _132484 s h1)). Qed.
Lemma lem7132439 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7132440 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7132439 p q p' q'). Qed.
Lemma lem7132441 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7132440 p q p'). Qed.
Lemma lem7132442 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term26 A f s b.
Proof. exact (@lem7132441 (term27 A s f b) (term28 A f s b)). Qed.
Lemma lem7132443 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) : term29 A f s b p'.
Proof. exact (@lem7132442 A f s b p'). Qed.
Lemma lem7132444 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) : (term29 A f s b p') = (term30 A f s b p').
Proof. exact (eq_refl (term29 A f s b p')). Qed.
Lemma lem7132445 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) : term30 A f s b p'.
Proof. exact (EQ_MP (@lem7132444 A f s b p') (@lem7132443 A f s b p')). Qed.
Lemma lem7132446 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) (q' : Prop) : term31 A f s b p' q'.
Proof. exact (@lem7132445 A f s b p' q'). Qed.
Lemma lem7132447 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) (q' : Prop) : (term31 A f s b p' q') = (term32 A f s b p' q').
Proof. exact (eq_refl (term31 A f s b p' q')). Qed.
Lemma lem7132448 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) (p' : Prop) (q' : Prop) : term32 A f s b p' q'.
Proof. exact (EQ_MP (@lem7132447 A f s b p' q') (@lem7132446 A f s b p' q')). Qed.
Lemma lem7132478 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term27 A s f b) = (term27 A s f b).
Proof. exact (eq_refl (term27 A s f b)). Qed.
Lemma lem7132479 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (q' : Prop) : term33 A s f b q'.
Proof. exact (@lem7132448 A f s b (term27 A s f b) q'). Qed.
Lemma lem7132480 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (q' : Prop) : term34 A s f b q'.
Proof. exact (@lem7132479 A s f b q' (@lem7132478 A s f b)). Qed.
Lemma lem7132481 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term27 A s f b.
Proof. exact (h1). Qed.
Lemma lem7132482 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term35 A s f b.
Proof. exact (proj2 (@lem7132481 A s f b h1)). Qed.
Lemma lem7132483 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term36 A s f b x.
Proof. exact (@lem7132482 A s f b h1 x). Qed.
Lemma lem7132484 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term36 A s f b x) = (term37 A s f x b).
Proof. exact (eq_refl (term36 A s f b x)). Qed.
Lemma lem7132485 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term37 A s f x b.
Proof. exact (EQ_MP (@lem7132484 A s f x b) (@lem7132483 A x s f b h1)). Qed.
Lemma lem7132486 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7132487 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : term38 A f x b.
Proof. exact (@lem7132485 A x s f b h1 (@lem7132486 A x s h2)). Qed.
Lemma lem7132488 {A : Type'} (f : A -> real) (x : A) (b : real) : (term38 A f x b) = ((term38 A f x b) = True).
Proof. exact (@lem7 (term38 A f x b)). Qed.
Lemma lem7132489 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term38 A f x b) = True.
Proof. exact (EQ_MP (@lem7132488 A f x b) (@lem7132487 A f b x s h1 h2)). Qed.
Lemma lem7132495 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : @FINITE A s.
Proof. exact (proj1 (@lem7132481 A s f b h1)). Qed.
Lemma lem7132496 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7132499 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term4 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7132418 _132484 c s h0). Qed.
Lemma lem7132500 {A : Type'} (s : A -> Prop) (c : real) : term4 A s c.
Proof. exact (@lem7132499 A s c). Qed.
Lemma lem7132501 {A : Type'} (s : A -> Prop) (b : real) : term4 A s b.
Proof. exact (@lem7132500 A s b). Qed.
Lemma lem7132503 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7132496 A s) (@lem7132495 A s f b h1)). Qed.
Lemma lem7132504 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : True = (@FINITE A s).
Proof. exact (SYM (@lem7132503 A s f b h1)). Qed.
Lemma lem7132505 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : @FINITE A s.
Proof. exact (EQ_MP (@lem7132504 A s f b h1) (@lem0)). Qed.
Lemma lem7132506 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term1 A s b) = (term0 A s b).
Proof. exact (@lem7132501 A s b (@lem7132505 A s f b h1)). Qed.
Lemma lem7132507 {A : Type'} (s : A -> Prop) (f : A -> real) : (term39 A s f) = (term39 A s f).
Proof. exact (eq_refl (term39 A s f)). Qed.
Lemma lem7132508 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term28 A f s b) = (term40 A f s b).
Proof. exact (MK_COMB (@lem7132507 A s f) (@lem7132506 A s f b h1)). Qed.
Lemma lem7132510 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term41 _132081 f s g.
Proof. exact (fun h0 : term19 _132081 s f g => @lem7132405 _132081 s f g h0). Qed.
Lemma lem7132511 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term41 A f s g.
Proof. exact (@lem7132510 A f s g). Qed.
Lemma lem7132512 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term42 A f s b.
Proof. exact (@lem7132511 A f s (term43 A b)). Qed.
Lemma lem7132516 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7132496 A s) (@lem7132495 A s f b h1)). Qed.
Lemma lem7132517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7132518 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term44 A s) = (and True).
Proof. exact (MK_COMB (@lem7132517) (@lem7132516 A s f b h1)). Qed.
Lemma lem7132526 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7132527 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem7132526 p q p' q'). Qed.
Lemma lem7132528 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem7132527 p q p'). Qed.
Lemma lem7132529 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) : term45 A s f b x.
Proof. exact (@lem7132528 (@IN A x s) (term46 A f b x)). Qed.
Lemma lem7132530 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) : term47 A s f b x p'.
Proof. exact (@lem7132529 A s f b x p'). Qed.
Lemma lem7132531 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) : (term47 A s f b x p') = (term48 A s f b x p').
Proof. exact (eq_refl (term47 A s f b x p')). Qed.
Lemma lem7132532 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) : term48 A s f b x p'.
Proof. exact (EQ_MP (@lem7132531 A s f b x p') (@lem7132530 A s f b x p')). Qed.
Lemma lem7132533 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) (q' : Prop) : term49 A s f b x p' q'.
Proof. exact (@lem7132532 A s f b x p' q'). Qed.
Lemma lem7132534 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) (q' : Prop) : (term49 A s f b x p' q') = (term50 A s f b x p' q').
Proof. exact (eq_refl (term49 A s f b x p' q')). Qed.
Lemma lem7132535 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) (p' : Prop) (q' : Prop) : term50 A s f b x p' q'.
Proof. exact (EQ_MP (@lem7132534 A s f b x p' q') (@lem7132533 A s f b x p' q')). Qed.
Lemma lem7132536 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7132537 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term51 A f b x s q'.
Proof. exact (@lem7132535 A s f b x (@IN A x s) q'). Qed.
Lemma lem7132538 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term52 A f b x s q'.
Proof. exact (@lem7132537 A f b x s q' (@lem7132536 A x s)). Qed.
Lemma lem7132539 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7132540 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7132543 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7132544 {A : Type'} (f : A -> real) (y : A) : (term54 A f y) = (f y).
Proof. exact (@lem7132543 A real f y). Qed.
Lemma lem7132545 {A : Type'} (b : real) (x : A) : (term55 A b x) = (term56 A b x).
Proof. exact (@lem7132544 A (term43 A b) x). Qed.
Lemma lem7132546 {A : Type'} (n : A) (b : real) : (term56 A b n) = b.
Proof. exact (eq_refl (term56 A b n)). Qed.
Lemma lem7132547 {A : Type'} (b : real) : (term57 A b) = (term43 A b).
Proof. exact (fun_ext (fun n : A => @lem7132546 A n b)). Qed.
Lemma lem7132548 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7132549 {A : Type'} (b : real) (x : A) : (term55 A b x) = (term56 A b x).
Proof. exact (MK_COMB (@lem7132547 A b) (@lem7132548 A x)). Qed.
Lemma lem7132550 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7132551 {A : Type'} (b : real) (x : A) : (term58 A b x) = (term59 A b x).
Proof. exact (MK_COMB (@lem7132550) (@lem7132549 A b x)). Qed.
Lemma lem7132552 {A : Type'} (x : A) (b : real) : (term56 A b x) = b.
Proof. exact (eq_refl (term56 A b x)). Qed.
Lemma lem7132553 {A : Type'} (x : A) (b : real) : ((term55 A b x) = (term56 A b x)) = ((term56 A b x) = b).
Proof. exact (MK_COMB (@lem7132551 A b x) (@lem7132552 A x b)). Qed.
Lemma lem7132554 {A : Type'} (x : A) (b : real) : (term56 A b x) = b.
Proof. exact (EQ_MP (@lem7132553 A x b) (@lem7132545 A b x)). Qed.
Lemma lem7132555 {A : Type'} (f : A -> real) (x : A) : (term60 A f x) = (term60 A f x).
Proof. exact (eq_refl (term60 A f x)). Qed.
Lemma lem7132556 {A : Type'} (f : A -> real) (x : A) (b : real) : (term46 A f b x) = (term38 A f x b).
Proof. exact (MK_COMB (@lem7132555 A f x) (@lem7132554 A x b)). Qed.
Lemma lem7132558 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term61 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem7132489 A f b x s h1 h0). Qed.
Lemma lem7132559 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term61 A s f x b.
Proof. exact (@lem7132558 A x s f b h1). Qed.
Lemma lem7132561 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7132540 A x s) (@lem7132539 A x s h1)). Qed.
Lemma lem7132562 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem7132561 A x s h1)). Qed.
Lemma lem7132563 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7132562 A x s h1) (@lem0)). Qed.
Lemma lem7132564 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term38 A f x b) = True.
Proof. exact (@lem7132559 A x s f b h1 (@lem7132563 A x s h2)). Qed.
Lemma lem7132565 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term46 A f b x) = True.
Proof. exact (TRANS (@lem7132556 A f x b) (@lem7132564 A f b x s h1 h2)). Qed.
Lemma lem7132566 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term62 A s f b x.
Proof. exact (fun h0 : @IN A x s => @lem7132565 A f b x s h1 h0). Qed.
Lemma lem7132567 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : term63 A f b x s.
Proof. exact (@lem7132538 A f b x s True). Qed.
Lemma lem7132568 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term64 A s f b x) = (term65 A x s).
Proof. exact (@lem7132567 A f b x s (@lem7132566 A x s f b h1)). Qed.
Lemma lem7132570 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7132571 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = True.
Proof. exact (@lem7132570 (@IN A x s)). Qed.
Lemma lem7132572 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term64 A s f b x) = True.
Proof. exact (TRANS (@lem7132568 A x s f b h1) (@lem7132571 A x s)). Qed.
Lemma lem7132573 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term66 A s f b) = (term67 A).
Proof. exact (fun_ext (fun x : A => @lem7132572 A x s f b h1)). Qed.
Lemma lem7132574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7132575 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term68 A s f b) = (term69 A).
Proof. exact (MK_COMB (@lem7132574 A) (@lem7132573 A s f b h1)). Qed.
Lemma lem7132577 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7132578 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (@lem7132577 A t). Qed.
Lemma lem7132579 {A : Type'} : (term69 A) = True.
Proof. exact (@lem7132578 A True). Qed.
Lemma lem7132580 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term68 A s f b) = True.
Proof. exact (TRANS (@lem7132575 A s f b h1) (@lem7132579 A)). Qed.
Lemma lem7132581 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term71 A s f b) = (True /\ True).
Proof. exact (MK_COMB (@lem7132518 A s f b h1) (@lem7132580 A s f b h1)). Qed.
Lemma lem7132583 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7132584 : (True /\ True) = True.
Proof. exact (@lem7132583 True). Qed.
Lemma lem7132585 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term71 A s f b) = True.
Proof. exact (TRANS (@lem7132581 A s f b h1) (@lem7132584)). Qed.
Lemma lem7132586 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : True = (term71 A s f b).
Proof. exact (SYM (@lem7132585 A s f b h1)). Qed.
Lemma lem7132587 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : term71 A s f b.
Proof. exact (EQ_MP (@lem7132586 A s f b h1) (@lem0)). Qed.
Lemma lem7132588 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term40 A f s b) = True.
Proof. exact (@lem7132512 A f s b (@lem7132587 A s f b h1)). Qed.
Lemma lem7132589 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term27 A s f b) : (term28 A f s b) = True.
Proof. exact (TRANS (@lem7132508 A s f b h1) (@lem7132588 A s f b h1)). Qed.
Lemma lem7132590 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term72 A f s b.
Proof. exact (fun h0 : term27 A s f b => @lem7132589 A s f b h0). Qed.
Lemma lem7132591 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : term73 A s f b.
Proof. exact (@lem7132480 A s f b True). Qed.
Lemma lem7132592 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term74 A f s b) = (term75 A s f b).
Proof. exact (@lem7132591 A s f b (@lem7132590 A f s b)). Qed.
Lemma lem7132594 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7132595 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term75 A s f b) = True.
Proof. exact (@lem7132594 (term27 A s f b)). Qed.
Lemma lem7132596 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : (term74 A f s b) = True.
Proof. exact (TRANS (@lem7132592 A s f b) (@lem7132595 A s f b)). Qed.
Lemma lem7132597 {A : Type'} (f : A -> real) (s : A -> Prop) : (term76 A f s) = term77.
Proof. exact (fun_ext (fun b : real => @lem7132596 A f s b)). Qed.
Lemma lem7132598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7132599 {A : Type'} (f : A -> real) (s : A -> Prop) : (term78 A f s) = term79.
Proof. exact (MK_COMB (@lem7132598) (@lem7132597 A f s)). Qed.
Lemma lem7132601 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7132602 (t : Prop) : (term80 t) = t.
Proof. exact (@lem7132601 real t). Qed.
Lemma lem7132603 : term79 = True.
Proof. exact (@lem7132602 True). Qed.
Lemma lem7132604 {A : Type'} (f : A -> real) (s : A -> Prop) : (term78 A f s) = True.
Proof. exact (TRANS (@lem7132599 A f s) (@lem7132603)). Qed.
Lemma lem7132605 {A : Type'} (s : A -> Prop) : (term81 A s) = (term82 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7132604 A f s)). Qed.
Lemma lem7132606 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7132607 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A).
Proof. exact (MK_COMB (@lem7132606 A) (@lem7132605 A s)). Qed.
Lemma lem7132609 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7132610 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem7132609 (A -> real) t). Qed.
Lemma lem7132611 {A : Type'} : (term84 A) = True.
Proof. exact (@lem7132610 A True). Qed.
Lemma lem7132612 {A : Type'} (s : A -> Prop) : (term83 A s) = True.
Proof. exact (TRANS (@lem7132607 A s) (@lem7132611 A)). Qed.
Lemma lem7132613 {A : Type'} : (term86 A) = (term87 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7132612 A s)). Qed.
Lemma lem7132614 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7132615 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem7132614 A) (@lem7132613 A)). Qed.
Lemma lem7132617 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7132618 {A : Type'} (t : Prop) : (term90 A t) = t.
Proof. exact (@lem7132617 (A -> Prop) t). Qed.
Lemma lem7132619 {A : Type'} : (term89 A) = True.
Proof. exact (@lem7132618 A True). Qed.
Lemma lem7132620 {A : Type'} : (term88 A) = True.
Proof. exact (TRANS (@lem7132615 A) (@lem7132619 A)). Qed.
Lemma lem7132621 {A : Type'} : True = (term88 A).
Proof. exact (SYM (@lem7132620 A)). Qed.
Lemma lem7132622 {A : Type'} : term88 A.
Proof. exact (EQ_MP (@lem7132621 A) (@lem0)). Qed.
