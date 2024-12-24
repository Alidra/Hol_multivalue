Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_DEGENERATE_term_abbrevs.
Require Import iterate_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm82_spec.
Lemma lem6924404 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6924405 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem6924406 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem6924405 A B s) (@lem6924404 A B s)). Qed.
Lemma lem6924407 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem6924406 A B s f). Qed.
Lemma lem6924408 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem6924409 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem6924408 A B s f) (@lem6924407 A B s f)). Qed.
Lemma lem6924410 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term4 A B s f op.
Proof. exact (@lem6924409 A B s f op). Qed.
Lemma lem6924411 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term4 A B s f op) = ((@support A B op f s) = (term5 A B s f op)).
Proof. exact (eq_refl (term4 A B s f op)). Qed.
Lemma lem6924413 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem6924414 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem6924415 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem6924414 _119779 A f) (@lem6924413 _119779 A f)). Qed.
Lemma lem6924416 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem6924415 _119779 A f s). Qed.
Lemma lem6924417 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem6924418 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem6924417 _119779 A f s) (@lem6924416 _119779 A f s)). Qed.
Lemma lem6924419 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem6924418 _119779 A f s op). Qed.
Lemma lem6924420 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem6924435 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924436 {_126453 : Type'} : (@nsum _126453) = (@iterate nat _126453 Nat.add).
Proof. exact (@lem6924435 _126453). Qed.
Lemma lem6924437 {_126453 : Type'} (s : _126453 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6924438 {_126453 : Type'} (s : _126453 -> Prop) : (@nsum _126453 s) = (@iterate nat _126453 Nat.add s).
Proof. exact (MK_COMB (@lem6924436 _126453) (@lem6924437 _126453 s)). Qed.
Lemma lem6924439 {_126453 : Type'} (f : _126453 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924440 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (@nsum _126453 s f) = (@iterate nat _126453 Nat.add s f).
Proof. exact (MK_COMB (@lem6924438 _126453 s) (@lem6924439 _126453 f)). Qed.
Lemma lem6924441 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6924442 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term12 _126453 s f) = (term13 _126453 s f).
Proof. exact (MK_COMB (@lem6924441) (@lem6924440 _126453 s f)). Qed.
Lemma lem6924443 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6924444 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : ((@nsum _126453 s f) = (NUMERAL 0)) = ((@iterate nat _126453 Nat.add s f) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6924442 _126453 s f) (@lem6924443)). Qed.
Lemma lem6924447 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term14 _126453 s f) = (term14 _126453 s f).
Proof. exact (eq_refl (term14 _126453 s f)). Qed.
Lemma lem6924448 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term15 _126453 s f) = (term16 _126453 s f).
Proof. exact (MK_COMB (@lem6924447 _126453 s f) (@lem6924444 _126453 s f)). Qed.
Lemma lem6924451 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term16 _126453 s f) = (term15 _126453 s f).
Proof. exact (SYM (@lem6924448 _126453 s f)). Qed.
Lemma lem6924455 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term17 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6924456 (p : Prop) (q : Prop) (p' : Prop) : term18 p q p'.
Proof. exact (fun q' : Prop => @lem6924455 p q p' q'). Qed.
Lemma lem6924457 (p : Prop) (q : Prop) : term19 p q.
Proof. exact (fun p' : Prop => @lem6924456 p q p'). Qed.
Lemma lem6924458 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term20 _126453 s f.
Proof. exact (@lem6924457 (term21 _126453 s f) ((@iterate nat _126453 Nat.add s f) = (NUMERAL 0))). Qed.
Lemma lem6924459 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) : term22 _126453 s f p'.
Proof. exact (@lem6924458 _126453 s f p'). Qed.
Lemma lem6924460 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) : (term22 _126453 s f p') = (term23 _126453 s f p').
Proof. exact (eq_refl (term22 _126453 s f p')). Qed.
Lemma lem6924461 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) : term23 _126453 s f p'.
Proof. exact (EQ_MP (@lem6924460 _126453 s f p') (@lem6924459 _126453 s f p')). Qed.
Lemma lem6924462 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) (q' : Prop) : term24 _126453 s f p' q'.
Proof. exact (@lem6924461 _126453 s f p' q'). Qed.
Lemma lem6924463 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) (q' : Prop) : (term24 _126453 s f p' q') = (term25 _126453 s f p' q').
Proof. exact (eq_refl (term24 _126453 s f p' q')). Qed.
Lemma lem6924464 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (p' : Prop) (q' : Prop) : term25 _126453 s f p' q'.
Proof. exact (EQ_MP (@lem6924463 _126453 s f p' q') (@lem6924462 _126453 s f p' q')). Qed.
Lemma lem6924473 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term21 _126453 s f) = (term21 _126453 s f).
Proof. exact (eq_refl (term21 _126453 s f)). Qed.
Lemma lem6924474 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (q' : Prop) : term26 _126453 s f q'.
Proof. exact (@lem6924464 _126453 s f (term21 _126453 s f) q'). Qed.
Lemma lem6924475 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (q' : Prop) : term27 _126453 s f q'.
Proof. exact (@lem6924474 _126453 s f q' (@lem6924473 _126453 s f)). Qed.
Lemma lem6924476 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : term21 _126453 s f.
Proof. exact (h1). Qed.
Lemma lem6924477 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term28 _126453 s f.
Proof. exact (@lem82 (term29 _126453 s f)). Qed.
Lemma lem6924482 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem6924420 _119779 A f s op) (@lem6924419 _119779 A f s op)). Qed.
Lemma lem6924483 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (op : type1606) : (@iterate nat _126453 op s f) = (term30 _126453 f s op).
Proof. exact (@lem6924482 nat _126453 f s op). Qed.
Lemma lem6924484 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) : (@iterate nat _126453 Nat.add s f) = (term31 _126453 f s).
Proof. exact (@lem6924483 _126453 f s Nat.add). Qed.
Lemma lem6924486 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term32 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6924487 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term33 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6924486 _2963 g t e g' t' e'). Qed.
Lemma lem6924488 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term34 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6924487 _2963 g t e g' t'). Qed.
Lemma lem6924489 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term35 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6924488 _2963 g t e g'). Qed.
Lemma lem6924490 (g : Prop) (t : nat) (e : nat) : term36 g t e.
Proof. exact (@lem6924489 nat g t e). Qed.
Lemma lem6924491 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) : term37 _126453 f s.
Proof. exact (@lem6924490 (term38 _126453 f s) (term39 _126453 f s) (@neutral nat Nat.add)). Qed.
Lemma lem6924492 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) : term40 _126453 f s g'.
Proof. exact (@lem6924491 _126453 f s g'). Qed.
Lemma lem6924493 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) : (term40 _126453 f s g') = (term41 _126453 f s g').
Proof. exact (eq_refl (term40 _126453 f s g')). Qed.
Lemma lem6924494 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) : term41 _126453 f s g'.
Proof. exact (EQ_MP (@lem6924493 _126453 f s g') (@lem6924492 _126453 f s g')). Qed.
Lemma lem6924495 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) : term42 _126453 f s g' t'.
Proof. exact (@lem6924494 _126453 f s g' t'). Qed.
Lemma lem6924496 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) : (term42 _126453 f s g' t') = (term43 _126453 f s g' t').
Proof. exact (eq_refl (term42 _126453 f s g' t')). Qed.
Lemma lem6924497 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) : term43 _126453 f s g' t'.
Proof. exact (EQ_MP (@lem6924496 _126453 f s g' t') (@lem6924495 _126453 f s g' t')). Qed.
Lemma lem6924498 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term44 _126453 f s g' t' e'.
Proof. exact (@lem6924497 _126453 f s g' t' e'). Qed.
Lemma lem6924499 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term44 _126453 f s g' t' e') = (term45 _126453 f s g' t' e').
Proof. exact (eq_refl (term44 _126453 f s g' t' e')). Qed.
Lemma lem6924500 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term45 _126453 f s g' t' e'.
Proof. exact (EQ_MP (@lem6924499 _126453 f s g' t' e') (@lem6924498 _126453 f s g' t' e')). Qed.
Lemma lem6924502 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term5 A B s f op).
Proof. exact (EQ_MP (@lem6924411 A B s f op) (@lem6924410 A B s f op)). Qed.
Lemma lem6924503 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (op : type1606) : (@support _126453 nat op f s) = (term46 _126453 s f op).
Proof. exact (@lem6924502 _126453 nat s f op). Qed.
Lemma lem6924504 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (@support _126453 nat Nat.add f s) = (term47 _126453 s f).
Proof. exact (@lem6924503 _126453 s f Nat.add). Qed.
Lemma lem6924514 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6924515 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : (term48 _126453 f x) = (term48 _126453 f x).
Proof. exact (eq_refl (term48 _126453 f x)). Qed.
Lemma lem6924516 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6924515 _126453 f x) (@lem6924514)). Qed.
Lemma lem6924519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6924520 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : (term49 _126453 f x) = (term50 _126453 f x).
Proof. exact (MK_COMB (@lem6924519) (@lem6924516 _126453 f x)). Qed.
Lemma lem6924523 {_126453 : Type'} (x : _126453) (s : _126453 -> Prop) : (term51 _126453 x s) = (term51 _126453 x s).
Proof. exact (eq_refl (term51 _126453 x s)). Qed.
Lemma lem6924524 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term52 _126453 s f x) = (term53 _126453 s f x).
Proof. exact (MK_COMB (@lem6924523 _126453 x s) (@lem6924520 _126453 f x)). Qed.
Lemma lem6924529 {_126453 : Type'} (GEN_PVAR_237 : _126453) : (@SETSPEC _126453 GEN_PVAR_237) = (@SETSPEC _126453 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _126453 GEN_PVAR_237)). Qed.
Lemma lem6924530 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term54 _126453 GEN_PVAR_237 s f x) = (term55 _126453 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6924529 _126453 GEN_PVAR_237) (@lem6924524 _126453 s f x)). Qed.
Lemma lem6924535 {_126453 : Type'} (x : _126453) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6924536 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term56 _126453 GEN_PVAR_237 s f x) = (term57 _126453 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6924530 _126453 GEN_PVAR_237 s f x) (@lem6924535 _126453 x)). Qed.
Lemma lem6924541 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) : (term58 _126453 GEN_PVAR_237 s f) = (term59 _126453 GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : _126453 => @lem6924536 _126453 GEN_PVAR_237 s f x)). Qed.
Lemma lem6924546 {_126453 : Type'} : (@ex _126453) = (@ex _126453).
Proof. exact (eq_refl (@ex _126453)). Qed.
Lemma lem6924547 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) : (term60 _126453 GEN_PVAR_237 s f) = (term61 _126453 GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem6924546 _126453) (@lem6924541 _126453 GEN_PVAR_237 s f)). Qed.
Lemma lem6924556 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term62 _126453 s f) = (term63 _126453 s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _126453 => @lem6924547 _126453 GEN_PVAR_237 s f)). Qed.
Lemma lem6924565 {_126453 : Type'} : (@GSPEC _126453) = (@GSPEC _126453).
Proof. exact (eq_refl (@GSPEC _126453)). Qed.
Lemma lem6924566 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term47 _126453 s f) = (term64 _126453 s f).
Proof. exact (MK_COMB (@lem6924565 _126453) (@lem6924556 _126453 s f)). Qed.
Lemma lem6924575 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (@support _126453 nat Nat.add f s) = (term64 _126453 s f).
Proof. exact (TRANS (@lem6924504 _126453 s f) (@lem6924566 _126453 s f)). Qed.
Lemma lem6924576 {_126453 : Type'} : (@FINITE _126453) = (@FINITE _126453).
Proof. exact (eq_refl (@FINITE _126453)). Qed.
Lemma lem6924577 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term38 _126453 f s) = (term29 _126453 s f).
Proof. exact (MK_COMB (@lem6924576 _126453) (@lem6924575 _126453 s f)). Qed.
Lemma lem6924579 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term29 _126453 s f) = False.
Proof. exact (@lem6924477 _126453 s f (@lem6924476 _126453 s f h1)). Qed.
Lemma lem6924580 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term29 _126453 s f) = False.
Proof. exact (@lem6924579 _126453 s f h1). Qed.
Lemma lem6924581 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term38 _126453 f s) = False.
Proof. exact (TRANS (@lem6924577 _126453 s f) (@lem6924580 _126453 s f h1)). Qed.
Lemma lem6924582 {_126453 : Type'} (f : _126453 -> nat) (s : _126453 -> Prop) (t' : nat) (e' : nat) : term65 _126453 f s t' e'.
Proof. exact (@lem6924500 _126453 f s False t' e'). Qed.
Lemma lem6924583 {_126453 : Type'} (t' : nat) (e' : nat) (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : term66 _126453 f s t' e'.
Proof. exact (@lem6924582 _126453 f s t' e' (@lem6924581 _126453 s f h1)). Qed.
Lemma lem6924588 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term5 A B s f op).
Proof. exact (EQ_MP (@lem6924411 A B s f op) (@lem6924410 A B s f op)). Qed.
Lemma lem6924589 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (op : type1606) : (@support _126453 nat op f s) = (term46 _126453 s f op).
Proof. exact (@lem6924588 _126453 nat s f op). Qed.
Lemma lem6924590 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (@support _126453 nat Nat.add f s) = (term47 _126453 s f).
Proof. exact (@lem6924589 _126453 s f Nat.add). Qed.
Lemma lem6924600 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6924601 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : (term48 _126453 f x) = (term48 _126453 f x).
Proof. exact (eq_refl (term48 _126453 f x)). Qed.
Lemma lem6924602 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6924601 _126453 f x) (@lem6924600)). Qed.
Lemma lem6924605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6924606 {_126453 : Type'} (f : _126453 -> nat) (x : _126453) : (term49 _126453 f x) = (term50 _126453 f x).
Proof. exact (MK_COMB (@lem6924605) (@lem6924602 _126453 f x)). Qed.
Lemma lem6924609 {_126453 : Type'} (x : _126453) (s : _126453 -> Prop) : (term51 _126453 x s) = (term51 _126453 x s).
Proof. exact (eq_refl (term51 _126453 x s)). Qed.
Lemma lem6924610 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term52 _126453 s f x) = (term53 _126453 s f x).
Proof. exact (MK_COMB (@lem6924609 _126453 x s) (@lem6924606 _126453 f x)). Qed.
Lemma lem6924615 {_126453 : Type'} (GEN_PVAR_237 : _126453) : (@SETSPEC _126453 GEN_PVAR_237) = (@SETSPEC _126453 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _126453 GEN_PVAR_237)). Qed.
Lemma lem6924616 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term54 _126453 GEN_PVAR_237 s f x) = (term55 _126453 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6924615 _126453 GEN_PVAR_237) (@lem6924610 _126453 s f x)). Qed.
Lemma lem6924621 {_126453 : Type'} (x : _126453) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6924622 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) (x : _126453) : (term56 _126453 GEN_PVAR_237 s f x) = (term57 _126453 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6924616 _126453 GEN_PVAR_237 s f x) (@lem6924621 _126453 x)). Qed.
Lemma lem6924627 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) : (term58 _126453 GEN_PVAR_237 s f) = (term59 _126453 GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : _126453 => @lem6924622 _126453 GEN_PVAR_237 s f x)). Qed.
Lemma lem6924632 {_126453 : Type'} : (@ex _126453) = (@ex _126453).
Proof. exact (eq_refl (@ex _126453)). Qed.
Lemma lem6924633 {_126453 : Type'} (GEN_PVAR_237 : _126453) (s : _126453 -> Prop) (f : _126453 -> nat) : (term60 _126453 GEN_PVAR_237 s f) = (term61 _126453 GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem6924632 _126453) (@lem6924627 _126453 GEN_PVAR_237 s f)). Qed.
Lemma lem6924642 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term62 _126453 s f) = (term63 _126453 s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _126453 => @lem6924633 _126453 GEN_PVAR_237 s f)). Qed.
Lemma lem6924651 {_126453 : Type'} : (@GSPEC _126453) = (@GSPEC _126453).
Proof. exact (eq_refl (@GSPEC _126453)). Qed.
Lemma lem6924652 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term47 _126453 s f) = (term64 _126453 s f).
Proof. exact (MK_COMB (@lem6924651 _126453) (@lem6924642 _126453 s f)). Qed.
Lemma lem6924661 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (@support _126453 nat Nat.add f s) = (term64 _126453 s f).
Proof. exact (TRANS (@lem6924590 _126453 s f) (@lem6924652 _126453 s f)). Qed.
Lemma lem6924662 {_126453 : Type'} (f : _126453 -> nat) : (term67 _126453 f) = (term67 _126453 f).
Proof. exact (eq_refl (term67 _126453 f)). Qed.
Lemma lem6924663 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term68 _126453 f s) = (term69 _126453 s f).
Proof. exact (MK_COMB (@lem6924662 _126453 f) (@lem6924661 _126453 s f)). Qed.
Lemma lem6924673 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6924674 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term39 _126453 f s) = (term70 _126453 s f).
Proof. exact (MK_COMB (@lem6924663 _126453 s f) (@lem6924673)). Qed.
Lemma lem6924683 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term71 _126453 s f.
Proof. exact (fun h0 : False => @lem6924674 _126453 s f). Qed.
Lemma lem6924684 {_126453 : Type'} (e' : nat) (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : term72 _126453 s f e'.
Proof. exact (@lem6924583 _126453 (term70 _126453 s f) e' s f h1). Qed.
Lemma lem6924685 {_126453 : Type'} (e' : nat) (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : term73 _126453 s f e'.
Proof. exact (@lem6924684 _126453 e' s f h1 (@lem6924683 _126453 s f)). Qed.
Lemma lem6924692 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6924693 : term74.
Proof. exact (fun h0 : ~ False => @lem6924692). Qed.
Lemma lem6924694 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : term75 _126453 s f.
Proof. exact (@lem6924685 _126453 (NUMERAL 0) s f h1). Qed.
Lemma lem6924695 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term31 _126453 f s) = (term76 _126453 s f).
Proof. exact (@lem6924694 _126453 s f h1 (@lem6924693)). Qed.
Lemma lem6924697 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6924698 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6924697 nat t1 t2). Qed.
Lemma lem6924699 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term76 _126453 s f) = (NUMERAL 0).
Proof. exact (@lem6924698 (term70 _126453 s f) (NUMERAL 0)). Qed.
Lemma lem6924700 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term31 _126453 f s) = (NUMERAL 0).
Proof. exact (TRANS (@lem6924695 _126453 s f h1) (@lem6924699 _126453 s f)). Qed.
Lemma lem6924701 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (@iterate nat _126453 Nat.add s f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6924484 _126453 f s) (@lem6924700 _126453 s f h1)). Qed.
Lemma lem6924702 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6924703 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : (term13 _126453 s f) = term77.
Proof. exact (MK_COMB (@lem6924702) (@lem6924701 _126453 s f h1)). Qed.
Lemma lem6924704 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6924705 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : ((@iterate nat _126453 Nat.add s f) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6924703 _126453 s f h1) (@lem6924704)). Qed.
Lemma lem6924707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6924708 (x : nat) : (x = x) = True.
Proof. exact (@lem6924707 nat x). Qed.
Lemma lem6924709 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6924708 (NUMERAL 0)). Qed.
Lemma lem6924710 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) (h1 : term21 _126453 s f) : ((@iterate nat _126453 Nat.add s f) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem6924705 _126453 s f h1) (@lem6924709)). Qed.
Lemma lem6924711 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term78 _126453 s f.
Proof. exact (fun h0 : term21 _126453 s f => @lem6924710 _126453 s f h0). Qed.
Lemma lem6924712 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term79 _126453 s f.
Proof. exact (@lem6924475 _126453 s f True). Qed.
Lemma lem6924713 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term16 _126453 s f) = (term80 _126453 s f).
Proof. exact (@lem6924712 _126453 s f (@lem6924711 _126453 s f)). Qed.
Lemma lem6924715 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6924716 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term80 _126453 s f) = True.
Proof. exact (@lem6924715 (term21 _126453 s f)). Qed.
Lemma lem6924717 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : (term16 _126453 s f) = True.
Proof. exact (TRANS (@lem6924713 _126453 s f) (@lem6924716 _126453 s f)). Qed.
Lemma lem6924718 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : True = (term16 _126453 s f).
Proof. exact (SYM (@lem6924717 _126453 s f)). Qed.
Lemma lem6924719 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term16 _126453 s f.
Proof. exact (EQ_MP (@lem6924718 _126453 s f) (@lem0)). Qed.
Lemma lem6924720 {_126453 : Type'} (s : _126453 -> Prop) (f : _126453 -> nat) : term15 _126453 s f.
Proof. exact (EQ_MP (@lem6924451 _126453 s f) (@lem6924719 _126453 s f)). Qed.
Lemma lem6924725 {_126453 : Type'} (f : _126453 -> nat) : term81 _126453 f.
Proof. exact (fun s : _126453 -> Prop => @lem6924720 _126453 s f). Qed.
Lemma lem6924730 {_126453 : Type'} : term82 _126453.
Proof. exact (fun f : _126453 -> nat => @lem6924725 _126453 f). Qed.
