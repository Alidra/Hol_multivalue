Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPERADMISSIBLE_MATCH_SEQPATTERN_term_abbrevs.
Require Import SUPERADMISSIBLE_COND_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm8096294_spec.
Require Import thm8099922_spec.
Lemma lem8291441 {A B P : Type'} (lt2 : type1402 A) : term0 A B P lt2.
Proof. exact (@lem8291440 A B P lt2). Qed.
Lemma lem8291442 {A B P : Type'} (lt2 : type1402 A) : (term0 A B P lt2) = (term1 A B P lt2).
Proof. exact (eq_refl (term0 A B P lt2)). Qed.
Lemma lem8291443 {A B P : Type'} (lt2 : type1402 A) : term1 A B P lt2.
Proof. exact (EQ_MP (@lem8291442 A B P lt2) (@lem8291441 A B P lt2)). Qed.
Lemma lem8291444 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term2 A B P lt2 p.
Proof. exact (@lem8291443 A B P lt2 p). Qed.
Lemma lem8291445 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term2 A B P lt2 p) = (term3 A B P lt2 p).
Proof. exact (eq_refl (term2 A B P lt2 p)). Qed.
Lemma lem8291446 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term3 A B P lt2 p.
Proof. exact (EQ_MP (@lem8291445 A B P lt2 p) (@lem8291444 A B P lt2 p)). Qed.
Lemma lem8291447 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (P' : type560 A B P) : term4 A B P lt2 p P'.
Proof. exact (@lem8291446 A B P lt2 p P'). Qed.
Lemma lem8291448 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (P' : type560 A B P) : (term4 A B P lt2 p P') = (term5 A B P lt2 p P').
Proof. exact (eq_refl (term4 A B P lt2 p P')). Qed.
Lemma lem8291449 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (P' : type560 A B P) : term5 A B P lt2 p P'.
Proof. exact (EQ_MP (@lem8291448 A B P lt2 p P') (@lem8291447 A B P lt2 p P')). Qed.
Lemma lem8291450 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (P' : type560 A B P) (s : P -> A) : term6 A B P lt2 p P' s.
Proof. exact (@lem8291449 A B P lt2 p P' s). Qed.
Lemma lem8291451 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) : (term6 A B P lt2 p P' s) = (term7 A B P lt2 p s P').
Proof. exact (eq_refl (term6 A B P lt2 p P' s)). Qed.
Lemma lem8291452 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) : term7 A B P lt2 p s P'.
Proof. exact (EQ_MP (@lem8291451 A B P lt2 p s P') (@lem8291450 A B P lt2 p P' s)). Qed.
Lemma lem8291453 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) : term8 A B P lt2 p s P' h.
Proof. exact (@lem8291452 A B P lt2 p s P' h). Qed.
Lemma lem8291454 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) : (term8 A B P lt2 p s P' h) = (term9 A B P lt2 p s P' h).
Proof. exact (eq_refl (term8 A B P lt2 p s P' h)). Qed.
Lemma lem8291455 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) : term9 A B P lt2 p s P' h.
Proof. exact (EQ_MP (@lem8291454 A B P lt2 p s P' h) (@lem8291453 A B P lt2 p s P' h)). Qed.
Lemma lem8291456 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) (k : type558 A B P) : term10 A B P lt2 p s P' h k.
Proof. exact (@lem8291455 A B P lt2 p s P' h k). Qed.
Lemma lem8291457 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) (k : type558 A B P) : (term10 A B P lt2 p s P' h k) = (term11 A B P lt2 p s P' h k).
Proof. exact (eq_refl (term10 A B P lt2 p s P' h k)). Qed.
Lemma lem8291458 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) (k : type558 A B P) : term11 A B P lt2 p s P' h k.
Proof. exact (EQ_MP (@lem8291457 A B P lt2 p s P' h k) (@lem8291456 A B P lt2 p s P' h k)). Qed.
Lemma lem8291459 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) (k : type558 A B P) : (term11 A B P lt2 p s P' h k) = ((term11 A B P lt2 p s P' h k) = True).
Proof. exact (@lem7 (term11 A B P lt2 p s P' h k)). Qed.
Lemma lem8291508 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (s : type1470 _143642 _143649) : (term12 _143642 _143649 x r s) = (term13 _143642 _143649 r x s).
Proof. exact (EQ_MP (@lem8096294 _143642 _143649 r x s) (@lem8099922 _143642 _143649 r s x)). Qed.
Lemma lem8291509 {_145655 _145656 : Type'} (r : type1413 _145655 _145656) (x : _145655) (s : type1413 _145655 _145656) : (term14 _145655 _145656 x r s) = (term15 _145655 _145656 r x s).
Proof. exact (@lem8291508 _145656 _145655 r x s). Qed.
Lemma lem8291510 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term16 _145540 _145655 _145656 P e c1 c2 f x) = (term17 _145540 _145655 _145656 P c1 e c2 f x).
Proof. exact (@lem8291509 _145655 _145656 (c1 f x) (e f x) (c2 f x)). Qed.
Lemma lem8291515 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term18 _145540 _145655 _145656 P e c1 c2 f) = (term19 _145540 _145655 _145656 P c1 e c2 f).
Proof. exact (fun_ext (fun x : P => @lem8291510 _145540 _145655 _145656 P c1 e c2 f x)). Qed.
Lemma lem8291516 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term20 _145540 _145655 _145656 P e c1 c2) = (term21 _145540 _145655 _145656 P c1 e c2).
Proof. exact (fun_ext (fun f : _145540 -> _145656 => @lem8291515 _145540 _145655 _145656 P c1 e c2 f)). Qed.
Lemma lem8291517 {_145540 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) : (@superadmissible _145540 _145656 P lt2 p s) = (@superadmissible _145540 _145656 P lt2 p s).
Proof. exact (eq_refl (@superadmissible _145540 _145656 P lt2 p s)). Qed.
Lemma lem8291518 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term22 _145540 _145655 _145656 P lt2 p s e c1 c2) = (term23 _145540 _145655 _145656 P lt2 p s c1 e c2).
Proof. exact (MK_COMB (@lem8291517 _145540 _145656 P lt2 p s) (@lem8291516 _145540 _145655 _145656 P c1 e c2)). Qed.
Lemma lem8291519 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term24 _145540 _145655 _145656 P lt2 p c1 s e c2) = (term24 _145540 _145655 _145656 P lt2 p c1 s e c2).
Proof. exact (eq_refl (term24 _145540 _145655 _145656 P lt2 p c1 s e c2)). Qed.
Lemma lem8291520 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term25 _145540 _145655 _145656 P lt2 p s e c1 c2) = (term26 _145540 _145655 _145656 P lt2 p s c1 e c2).
Proof. exact (MK_COMB (@lem8291519 _145540 _145655 _145656 P lt2 p c1 s e c2) (@lem8291518 _145540 _145655 _145656 P lt2 p s c1 e c2)). Qed.
Lemma lem8291522 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (P' : type560 A B P) (h : type558 A B P) (k : type558 A B P) : (term11 A B P lt2 p s P' h k) = True.
Proof. exact (EQ_MP (@lem8291459 A B P lt2 p s P' h k) (@lem8291458 A B P lt2 p s P' h k)). Qed.
Lemma lem8291523 {_145540 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (P' : type560 _145540 _145656 P) (h : type558 _145540 _145656 P) (k : type558 _145540 _145656 P) : (term11 _145540 _145656 P lt2 p s P' h k) = True.
Proof. exact (@lem8291522 _145540 _145656 P lt2 p s P' h k). Qed.
Lemma lem8291524 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term27 _145540 _145655 _145656 P lt2 p s c1 e c2) = True.
Proof. exact (@lem8291523 _145540 _145656 P lt2 p s (term28 _145540 _145655 _145656 P c1 e) (term29 _145540 _145655 _145656 P e c1) (term29 _145540 _145655 _145656 P e c2)). Qed.
Lemma lem8291525 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term30 _145540 _145655 _145656 P c1 e f) = (term31 _145540 _145655 _145656 P c1 e f).
Proof. exact (eq_refl (term30 _145540 _145655 _145656 P c1 e f)). Qed.
Lemma lem8291526 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8291527 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term33 _145540 _145655 _145656 P c1 e f x).
Proof. exact (MK_COMB (@lem8291525 _145540 _145655 _145656 P c1 e f) (@lem8291526 P x)). Qed.
Lemma lem8291528 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term33 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (eq_refl (term33 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291529 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (TRANS (@lem8291527 _145540 _145655 _145656 P c1 e f x) (@lem8291528 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291530 {_145540 _145656 P : Type'} (p : type560 _145540 _145656 P) (f : _145540 -> _145656) (x : P) : (term35 _145540 _145656 P p f x) = (term35 _145540 _145656 P p f x).
Proof. exact (eq_refl (term35 _145540 _145656 P p f x)). Qed.
Lemma lem8291531 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term36 _145540 _145655 _145656 P p c1 e f x) = (term37 _145540 _145655 _145656 P p c1 e f x).
Proof. exact (MK_COMB (@lem8291530 _145540 _145656 P p f x) (@lem8291529 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291532 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term38 _145540 _145655 _145656 P p c1 e f) = (term39 _145540 _145655 _145656 P p c1 e f).
Proof. exact (fun_ext (fun x : P => @lem8291531 _145540 _145655 _145656 P p c1 e f x)). Qed.
Lemma lem8291533 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) : (term40 _145540 _145655 _145656 P p c1 e) = (term41 _145540 _145655 _145656 P p c1 e).
Proof. exact (fun_ext (fun f : _145540 -> _145656 => @lem8291532 _145540 _145655 _145656 P p c1 e f)). Qed.
Lemma lem8291534 {_145540 _145656 P : Type'} (lt2 : type1402 _145540) : (@superadmissible _145540 _145656 P lt2) = (@superadmissible _145540 _145656 P lt2).
Proof. exact (eq_refl (@superadmissible _145540 _145656 P lt2)). Qed.
Lemma lem8291535 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) : (term42 _145540 _145655 _145656 P lt2 p c1 e) = (term43 _145540 _145655 _145656 P lt2 p c1 e).
Proof. exact (MK_COMB (@lem8291534 _145540 _145656 P lt2) (@lem8291533 _145540 _145655 _145656 P p c1 e)). Qed.
Lemma lem8291536 {_145540 P : Type'} (s : P -> _145540) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8291537 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (s : P -> _145540) : (term44 _145540 _145655 _145656 P lt2 p c1 e s) = (term45 _145540 _145655 _145656 P lt2 p c1 e s).
Proof. exact (MK_COMB (@lem8291535 _145540 _145655 _145656 P lt2 p c1 e) (@lem8291536 _145540 P s)). Qed.
Lemma lem8291538 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) : (term29 _145540 _145655 _145656 P e c1) = (term29 _145540 _145655 _145656 P e c1).
Proof. exact (eq_refl (term29 _145540 _145655 _145656 P e c1)). Qed.
Lemma lem8291539 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) : (term46 _145540 _145655 _145656 P lt2 p s e c1) = (term47 _145540 _145655 _145656 P lt2 p s e c1).
Proof. exact (MK_COMB (@lem8291537 _145540 _145655 _145656 P lt2 p c1 e s) (@lem8291538 _145540 _145655 _145656 P e c1)). Qed.
Lemma lem8291540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8291541 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) : (term48 _145540 _145655 _145656 P lt2 p s e c1) = (term49 _145540 _145655 _145656 P lt2 p s e c1).
Proof. exact (MK_COMB (@lem8291540) (@lem8291539 _145540 _145655 _145656 P lt2 p s e c1)). Qed.
Lemma lem8291542 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term30 _145540 _145655 _145656 P c1 e f) = (term31 _145540 _145655 _145656 P c1 e f).
Proof. exact (eq_refl (term30 _145540 _145655 _145656 P c1 e f)). Qed.
Lemma lem8291543 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8291544 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term33 _145540 _145655 _145656 P c1 e f x).
Proof. exact (MK_COMB (@lem8291542 _145540 _145655 _145656 P c1 e f) (@lem8291543 P x)). Qed.
Lemma lem8291545 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term33 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (eq_refl (term33 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291546 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (TRANS (@lem8291544 _145540 _145655 _145656 P c1 e f x) (@lem8291545 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8291548 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term50 _145540 _145655 _145656 P c1 e f x) = (term51 _145540 _145655 _145656 P c1 e f x).
Proof. exact (MK_COMB (@lem8291547) (@lem8291546 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291549 {_145540 _145656 P : Type'} (p : type560 _145540 _145656 P) (f : _145540 -> _145656) (x : P) : (term35 _145540 _145656 P p f x) = (term35 _145540 _145656 P p f x).
Proof. exact (eq_refl (term35 _145540 _145656 P p f x)). Qed.
Lemma lem8291550 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term52 _145540 _145655 _145656 P p c1 e f x) = (term53 _145540 _145655 _145656 P p c1 e f x).
Proof. exact (MK_COMB (@lem8291549 _145540 _145656 P p f x) (@lem8291548 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291551 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term54 _145540 _145655 _145656 P p c1 e f) = (term55 _145540 _145655 _145656 P p c1 e f).
Proof. exact (fun_ext (fun x : P => @lem8291550 _145540 _145655 _145656 P p c1 e f x)). Qed.
Lemma lem8291552 {_145540 _145655 _145656 P : Type'} (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) : (term56 _145540 _145655 _145656 P p c1 e) = (term57 _145540 _145655 _145656 P p c1 e).
Proof. exact (fun_ext (fun f : _145540 -> _145656 => @lem8291551 _145540 _145655 _145656 P p c1 e f)). Qed.
Lemma lem8291553 {_145540 _145656 P : Type'} (lt2 : type1402 _145540) : (@superadmissible _145540 _145656 P lt2) = (@superadmissible _145540 _145656 P lt2).
Proof. exact (eq_refl (@superadmissible _145540 _145656 P lt2)). Qed.
Lemma lem8291554 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) : (term58 _145540 _145655 _145656 P lt2 p c1 e) = (term59 _145540 _145655 _145656 P lt2 p c1 e).
Proof. exact (MK_COMB (@lem8291553 _145540 _145656 P lt2) (@lem8291552 _145540 _145655 _145656 P p c1 e)). Qed.
Lemma lem8291555 {_145540 P : Type'} (s : P -> _145540) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8291556 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (s : P -> _145540) : (term60 _145540 _145655 _145656 P lt2 p c1 e s) = (term61 _145540 _145655 _145656 P lt2 p c1 e s).
Proof. exact (MK_COMB (@lem8291554 _145540 _145655 _145656 P lt2 p c1 e) (@lem8291555 _145540 P s)). Qed.
Lemma lem8291557 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term29 _145540 _145655 _145656 P e c2) = (term29 _145540 _145655 _145656 P e c2).
Proof. exact (eq_refl (term29 _145540 _145655 _145656 P e c2)). Qed.
Lemma lem8291558 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term62 _145540 _145655 _145656 P lt2 p c1 s e c2) = (term63 _145540 _145655 _145656 P lt2 p c1 s e c2).
Proof. exact (MK_COMB (@lem8291556 _145540 _145655 _145656 P lt2 p c1 e s) (@lem8291557 _145540 _145655 _145656 P e c2)). Qed.
Lemma lem8291559 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term64 _145540 _145655 _145656 P lt2 p c1 s e c2) = (term65 _145540 _145655 _145656 P lt2 p c1 s e c2).
Proof. exact (MK_COMB (@lem8291541 _145540 _145655 _145656 P lt2 p s e c1) (@lem8291558 _145540 _145655 _145656 P lt2 p c1 s e c2)). Qed.
Lemma lem8291560 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) : (term66 _145540 _145655 _145656 P lt2 p s c1 e) = (term66 _145540 _145655 _145656 P lt2 p s c1 e).
Proof. exact (eq_refl (term66 _145540 _145655 _145656 P lt2 p s c1 e)). Qed.
Lemma lem8291561 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term67 _145540 _145655 _145656 P lt2 p c1 s e c2) = (term68 _145540 _145655 _145656 P lt2 p c1 s e c2).
Proof. exact (MK_COMB (@lem8291560 _145540 _145655 _145656 P lt2 p s c1 e) (@lem8291559 _145540 _145655 _145656 P lt2 p c1 s e c2)). Qed.
Lemma lem8291562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8291563 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term69 _145540 _145655 _145656 P lt2 p c1 s e c2) = (term24 _145540 _145655 _145656 P lt2 p c1 s e c2).
Proof. exact (MK_COMB (@lem8291562) (@lem8291561 _145540 _145655 _145656 P lt2 p c1 s e c2)). Qed.
Lemma lem8291564 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term30 _145540 _145655 _145656 P c1 e f) = (term31 _145540 _145655 _145656 P c1 e f).
Proof. exact (eq_refl (term30 _145540 _145655 _145656 P c1 e f)). Qed.
Lemma lem8291565 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8291566 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term33 _145540 _145655 _145656 P c1 e f x).
Proof. exact (MK_COMB (@lem8291564 _145540 _145655 _145656 P c1 e f) (@lem8291565 P x)). Qed.
Lemma lem8291567 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term33 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (eq_refl (term33 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291568 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term32 _145540 _145655 _145656 P c1 e f x) = (term34 _145540 _145655 _145656 P c1 e f x).
Proof. exact (TRANS (@lem8291566 _145540 _145655 _145656 P c1 e f x) (@lem8291567 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291569 {_145656 : Type'} : (@COND _145656) = (@COND _145656).
Proof. exact (eq_refl (@COND _145656)). Qed.
Lemma lem8291570 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term70 _145540 _145655 _145656 P c1 e f x) = (term71 _145540 _145655 _145656 P c1 e f x).
Proof. exact (MK_COMB (@lem8291569 _145656) (@lem8291568 _145540 _145655 _145656 P c1 e f x)). Qed.
Lemma lem8291571 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term72 _145540 _145655 _145656 P e c1 f) = (term73 _145540 _145655 _145656 P e c1 f).
Proof. exact (eq_refl (term72 _145540 _145655 _145656 P e c1 f)). Qed.
Lemma lem8291572 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8291573 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term74 _145540 _145655 _145656 P e c1 f x) = (term75 _145540 _145655 _145656 P e c1 f x).
Proof. exact (MK_COMB (@lem8291571 _145540 _145655 _145656 P e c1 f) (@lem8291572 P x)). Qed.
Lemma lem8291574 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term75 _145540 _145655 _145656 P e c1 f x) = (term76 _145540 _145655 _145656 P e c1 f x).
Proof. exact (eq_refl (term75 _145540 _145655 _145656 P e c1 f x)). Qed.
Lemma lem8291575 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term74 _145540 _145655 _145656 P e c1 f x) = (term76 _145540 _145655 _145656 P e c1 f x).
Proof. exact (TRANS (@lem8291573 _145540 _145655 _145656 P e c1 f x) (@lem8291574 _145540 _145655 _145656 P e c1 f x)). Qed.
Lemma lem8291576 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term77 _145540 _145655 _145656 P e c1 f x) = (term78 _145540 _145655 _145656 P e c1 f x).
Proof. exact (MK_COMB (@lem8291570 _145540 _145655 _145656 P c1 e f x) (@lem8291575 _145540 _145655 _145656 P e c1 f x)). Qed.
Lemma lem8291577 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term72 _145540 _145655 _145656 P e c2 f) = (term73 _145540 _145655 _145656 P e c2 f).
Proof. exact (eq_refl (term72 _145540 _145655 _145656 P e c2 f)). Qed.
Lemma lem8291578 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8291579 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term74 _145540 _145655 _145656 P e c2 f x) = (term75 _145540 _145655 _145656 P e c2 f x).
Proof. exact (MK_COMB (@lem8291577 _145540 _145655 _145656 P e c2 f) (@lem8291578 P x)). Qed.
Lemma lem8291580 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term75 _145540 _145655 _145656 P e c2 f x) = (term76 _145540 _145655 _145656 P e c2 f x).
Proof. exact (eq_refl (term75 _145540 _145655 _145656 P e c2 f x)). Qed.
Lemma lem8291581 {_145540 _145655 _145656 P : Type'} (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term74 _145540 _145655 _145656 P e c2 f x) = (term76 _145540 _145655 _145656 P e c2 f x).
Proof. exact (TRANS (@lem8291579 _145540 _145655 _145656 P e c2 f x) (@lem8291580 _145540 _145655 _145656 P e c2 f x)). Qed.
Lemma lem8291582 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) (x : P) : (term79 _145540 _145655 _145656 P c1 e c2 f x) = (term17 _145540 _145655 _145656 P c1 e c2 f x).
Proof. exact (MK_COMB (@lem8291576 _145540 _145655 _145656 P e c1 f x) (@lem8291581 _145540 _145655 _145656 P e c2 f x)). Qed.
Lemma lem8291583 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) (f : _145540 -> _145656) : (term80 _145540 _145655 _145656 P c1 e c2 f) = (term19 _145540 _145655 _145656 P c1 e c2 f).
Proof. exact (fun_ext (fun x : P => @lem8291582 _145540 _145655 _145656 P c1 e c2 f x)). Qed.
Lemma lem8291584 {_145540 _145655 _145656 P : Type'} (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term81 _145540 _145655 _145656 P c1 e c2) = (term21 _145540 _145655 _145656 P c1 e c2).
Proof. exact (fun_ext (fun f : _145540 -> _145656 => @lem8291583 _145540 _145655 _145656 P c1 e c2 f)). Qed.
Lemma lem8291585 {_145540 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) : (@superadmissible _145540 _145656 P lt2 p s) = (@superadmissible _145540 _145656 P lt2 p s).
Proof. exact (eq_refl (@superadmissible _145540 _145656 P lt2 p s)). Qed.
Lemma lem8291586 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term82 _145540 _145655 _145656 P lt2 p s c1 e c2) = (term23 _145540 _145655 _145656 P lt2 p s c1 e c2).
Proof. exact (MK_COMB (@lem8291585 _145540 _145656 P lt2 p s) (@lem8291584 _145540 _145655 _145656 P c1 e c2)). Qed.
Lemma lem8291587 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term27 _145540 _145655 _145656 P lt2 p s c1 e c2) = (term26 _145540 _145655 _145656 P lt2 p s c1 e c2).
Proof. exact (MK_COMB (@lem8291563 _145540 _145655 _145656 P lt2 p c1 s e c2) (@lem8291586 _145540 _145655 _145656 P lt2 p s c1 e c2)). Qed.
Lemma lem8291588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8291589 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term83 _145540 _145655 _145656 P lt2 p s c1 e c2) = (term84 _145540 _145655 _145656 P lt2 p s c1 e c2).
Proof. exact (MK_COMB (@lem8291588) (@lem8291587 _145540 _145655 _145656 P lt2 p s c1 e c2)). Qed.
Lemma lem8291590 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem8291591 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : ((term27 _145540 _145655 _145656 P lt2 p s c1 e c2) = True) = ((term26 _145540 _145655 _145656 P lt2 p s c1 e c2) = True).
Proof. exact (MK_COMB (@lem8291589 _145540 _145655 _145656 P lt2 p s c1 e c2) (@lem8291590)). Qed.
Lemma lem8291592 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (e : type577 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term26 _145540 _145655 _145656 P lt2 p s c1 e c2) = True.
Proof. exact (EQ_MP (@lem8291591 _145540 _145655 _145656 P lt2 p s c1 e c2) (@lem8291524 _145540 _145655 _145656 P lt2 p s c1 e c2)). Qed.
Lemma lem8291593 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (e : type577 _145540 _145655 _145656 P) (c1 : type576 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term25 _145540 _145655 _145656 P lt2 p s e c1 c2) = True.
Proof. exact (TRANS (@lem8291520 _145540 _145655 _145656 P lt2 p s c1 e c2) (@lem8291592 _145540 _145655 _145656 P lt2 p s c1 e c2)). Qed.
Lemma lem8291594 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term85 _145540 _145655 _145656 P lt2 p s c1 c2) = (term86 _145540 _145655 _145656 P).
Proof. exact (fun_ext (fun e : type577 _145540 _145655 _145656 P => @lem8291593 _145540 _145655 _145656 P lt2 p s e c1 c2)). Qed.
Lemma lem8291595 {_145540 _145655 _145656 P : Type'} : (@all ((_145540 -> _145656) -> P -> _145655)) = (@all ((_145540 -> _145656) -> P -> _145655)).
Proof. exact (eq_refl (@all ((_145540 -> _145656) -> P -> _145655))). Qed.
Lemma lem8291596 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term87 _145540 _145655 _145656 P lt2 p s c1 c2) = (term88 _145540 _145655 _145656 P).
Proof. exact (MK_COMB (@lem8291595 _145540 _145655 _145656 P) (@lem8291594 _145540 _145655 _145656 P lt2 p s c1 c2)). Qed.
Lemma lem8291598 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291599 {_145540 _145655 _145656 P : Type'} (t : Prop) : (term90 _145540 _145655 _145656 P t) = t.
Proof. exact (@lem8291598 (type577 _145540 _145655 _145656 P) t). Qed.
Lemma lem8291600 {_145540 _145655 _145656 P : Type'} : (term88 _145540 _145655 _145656 P) = True.
Proof. exact (@lem8291599 _145540 _145655 _145656 P True). Qed.
Lemma lem8291601 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) (c2 : type576 _145540 _145655 _145656 P) : (term87 _145540 _145655 _145656 P lt2 p s c1 c2) = True.
Proof. exact (TRANS (@lem8291596 _145540 _145655 _145656 P lt2 p s c1 c2) (@lem8291600 _145540 _145655 _145656 P)). Qed.
Lemma lem8291602 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) : (term91 _145540 _145655 _145656 P lt2 p s c1) = (term92 _145540 _145655 _145656 P).
Proof. exact (fun_ext (fun c2 : type576 _145540 _145655 _145656 P => @lem8291601 _145540 _145655 _145656 P lt2 p s c1 c2)). Qed.
Lemma lem8291603 {_145540 _145655 _145656 P : Type'} : (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop)) = (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop)).
Proof. exact (eq_refl (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop))). Qed.
Lemma lem8291604 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) : (term93 _145540 _145655 _145656 P lt2 p s c1) = (term94 _145540 _145655 _145656 P).
Proof. exact (MK_COMB (@lem8291603 _145540 _145655 _145656 P) (@lem8291602 _145540 _145655 _145656 P lt2 p s c1)). Qed.
Lemma lem8291606 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291607 {_145540 _145655 _145656 P : Type'} (t : Prop) : (term95 _145540 _145655 _145656 P t) = t.
Proof. exact (@lem8291606 (type576 _145540 _145655 _145656 P) t). Qed.
Lemma lem8291608 {_145540 _145655 _145656 P : Type'} : (term94 _145540 _145655 _145656 P) = True.
Proof. exact (@lem8291607 _145540 _145655 _145656 P True). Qed.
Lemma lem8291609 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) (c1 : type576 _145540 _145655 _145656 P) : (term93 _145540 _145655 _145656 P lt2 p s c1) = True.
Proof. exact (TRANS (@lem8291604 _145540 _145655 _145656 P lt2 p s c1) (@lem8291608 _145540 _145655 _145656 P)). Qed.
Lemma lem8291610 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) : (term96 _145540 _145655 _145656 P lt2 p s) = (term92 _145540 _145655 _145656 P).
Proof. exact (fun_ext (fun c1 : type576 _145540 _145655 _145656 P => @lem8291609 _145540 _145655 _145656 P lt2 p s c1)). Qed.
Lemma lem8291611 {_145540 _145655 _145656 P : Type'} : (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop)) = (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop)).
Proof. exact (eq_refl (@all ((_145540 -> _145656) -> P -> _145655 -> _145656 -> Prop))). Qed.
Lemma lem8291612 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) : (term97 _145540 _145655 _145656 P lt2 p s) = (term94 _145540 _145655 _145656 P).
Proof. exact (MK_COMB (@lem8291611 _145540 _145655 _145656 P) (@lem8291610 _145540 _145655 _145656 P lt2 p s)). Qed.
Lemma lem8291614 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291615 {_145540 _145655 _145656 P : Type'} (t : Prop) : (term95 _145540 _145655 _145656 P t) = t.
Proof. exact (@lem8291614 (type576 _145540 _145655 _145656 P) t). Qed.
Lemma lem8291616 {_145540 _145655 _145656 P : Type'} : (term94 _145540 _145655 _145656 P) = True.
Proof. exact (@lem8291615 _145540 _145655 _145656 P True). Qed.
Lemma lem8291617 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) (s : P -> _145540) : (term97 _145540 _145655 _145656 P lt2 p s) = True.
Proof. exact (TRANS (@lem8291612 _145540 _145655 _145656 P lt2 p s) (@lem8291616 _145540 _145655 _145656 P)). Qed.
Lemma lem8291618 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) : (term98 _145540 _145655 _145656 P lt2 p) = (term99 _145540 P).
Proof. exact (fun_ext (fun s : P -> _145540 => @lem8291617 _145540 _145655 _145656 P lt2 p s)). Qed.
Lemma lem8291619 {_145540 P : Type'} : (@all (P -> _145540)) = (@all (P -> _145540)).
Proof. exact (eq_refl (@all (P -> _145540))). Qed.
Lemma lem8291620 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) : (term100 _145540 _145655 _145656 P lt2 p) = (term101 _145540 P).
Proof. exact (MK_COMB (@lem8291619 _145540 P) (@lem8291618 _145540 _145655 _145656 P lt2 p)). Qed.
Lemma lem8291622 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291623 {_145540 P : Type'} (t : Prop) : (term102 _145540 P t) = t.
Proof. exact (@lem8291622 (P -> _145540) t). Qed.
Lemma lem8291624 {_145540 P : Type'} : (term101 _145540 P) = True.
Proof. exact (@lem8291623 _145540 P True). Qed.
Lemma lem8291625 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) (p : type560 _145540 _145656 P) : (term100 _145540 _145655 _145656 P lt2 p) = True.
Proof. exact (TRANS (@lem8291620 _145540 _145655 _145656 P lt2 p) (@lem8291624 _145540 P)). Qed.
Lemma lem8291626 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) : (term103 _145540 _145655 _145656 P lt2) = (term104 _145540 _145656 P).
Proof. exact (fun_ext (fun p : type560 _145540 _145656 P => @lem8291625 _145540 _145655 _145656 P lt2 p)). Qed.
Lemma lem8291627 {_145540 _145656 P : Type'} : (@all ((_145540 -> _145656) -> P -> Prop)) = (@all ((_145540 -> _145656) -> P -> Prop)).
Proof. exact (eq_refl (@all ((_145540 -> _145656) -> P -> Prop))). Qed.
Lemma lem8291628 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) : (term105 _145540 _145655 _145656 P lt2) = (term106 _145540 _145656 P).
Proof. exact (MK_COMB (@lem8291627 _145540 _145656 P) (@lem8291626 _145540 _145655 _145656 P lt2)). Qed.
Lemma lem8291630 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291631 {_145540 _145656 P : Type'} (t : Prop) : (term107 _145540 _145656 P t) = t.
Proof. exact (@lem8291630 (type560 _145540 _145656 P) t). Qed.
Lemma lem8291632 {_145540 _145656 P : Type'} : (term106 _145540 _145656 P) = True.
Proof. exact (@lem8291631 _145540 _145656 P True). Qed.
Lemma lem8291633 {_145540 _145655 _145656 P : Type'} (lt2 : type1402 _145540) : (term105 _145540 _145655 _145656 P lt2) = True.
Proof. exact (TRANS (@lem8291628 _145540 _145655 _145656 P lt2) (@lem8291632 _145540 _145656 P)). Qed.
Lemma lem8291634 {_145540 _145655 _145656 P : Type'} : (term108 _145540 _145655 _145656 P) = (term109 _145540).
Proof. exact (fun_ext (fun lt2 : type1402 _145540 => @lem8291633 _145540 _145655 _145656 P lt2)). Qed.
Lemma lem8291635 {_145540 : Type'} : (@all (_145540 -> _145540 -> Prop)) = (@all (_145540 -> _145540 -> Prop)).
Proof. exact (eq_refl (@all (_145540 -> _145540 -> Prop))). Qed.
Lemma lem8291636 {_145540 _145655 _145656 P : Type'} : (term110 _145540 _145655 _145656 P) = (term111 _145540).
Proof. exact (MK_COMB (@lem8291635 _145540) (@lem8291634 _145540 _145655 _145656 P)). Qed.
Lemma lem8291638 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8291639 {_145540 : Type'} (t : Prop) : (term112 _145540 t) = t.
Proof. exact (@lem8291638 (type1402 _145540) t). Qed.
Lemma lem8291640 {_145540 : Type'} : (term111 _145540) = True.
Proof. exact (@lem8291639 _145540 True). Qed.
Lemma lem8291641 {_145540 _145655 _145656 P : Type'} : (term110 _145540 _145655 _145656 P) = True.
Proof. exact (TRANS (@lem8291636 _145540 _145655 _145656 P) (@lem8291640 _145540)). Qed.
Lemma lem8291642 {_145540 _145655 _145656 P : Type'} : True = (term110 _145540 _145655 _145656 P).
Proof. exact (SYM (@lem8291641 _145540 _145655 _145656 P)). Qed.
Lemma lem8291643 {_145540 _145655 _145656 P : Type'} : term110 _145540 _145655 _145656 P.
Proof. exact (EQ_MP (@lem8291642 _145540 _145655 _145656 P) (@lem0)). Qed.
