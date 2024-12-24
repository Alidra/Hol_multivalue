Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPERADMISSIBLE_CONST_term_abbrevs.
Require Import ADMISSIBLE_CONST_spec.
Require Import ADMISSIBLE_IMP_SUPERADMISSIBLE_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem8239495 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) : term0 _143669 _143670 _143671 _143672 _143673 lt2 p.
Proof. exact (@lem8100074 _143669 _143670 _143671 _143672 _143673 lt2 p). Qed.
Lemma lem8239496 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) : (term0 _143669 _143670 _143671 _143672 _143673 lt2 p) = (term1 _143669 _143670 _143671 _143672 _143673 lt2 p).
Proof. exact (eq_refl (term0 _143669 _143670 _143671 _143672 _143673 lt2 p)). Qed.
Lemma lem8239497 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) : term1 _143669 _143670 _143671 _143672 _143673 lt2 p.
Proof. exact (EQ_MP (@lem8239496 _143669 _143670 _143671 _143672 _143673 lt2 p) (@lem8239495 _143669 _143670 _143671 _143672 _143673 lt2 p)). Qed.
Lemma lem8239498 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) : term2 _143669 _143670 _143671 _143672 _143673 lt2 p s.
Proof. exact (@lem8239497 _143669 _143670 _143671 _143672 _143673 lt2 p s). Qed.
Lemma lem8239499 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) : (term2 _143669 _143670 _143671 _143672 _143673 lt2 p s) = (term3 _143669 _143670 _143671 _143672 _143673 lt2 p s).
Proof. exact (eq_refl (term2 _143669 _143670 _143671 _143672 _143673 lt2 p s)). Qed.
Lemma lem8239500 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) : term3 _143669 _143670 _143671 _143672 _143673 lt2 p s.
Proof. exact (EQ_MP (@lem8239499 _143669 _143670 _143671 _143672 _143673 lt2 p s) (@lem8239498 _143669 _143670 _143671 _143672 _143673 lt2 p s)). Qed.
Lemma lem8239501 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) (c : _143672 -> _143673) : term4 _143669 _143670 _143671 _143672 _143673 lt2 p s c.
Proof. exact (@lem8239500 _143669 _143670 _143671 _143672 _143673 lt2 p s c). Qed.
Lemma lem8239502 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) (c : _143672 -> _143673) : (term4 _143669 _143670 _143671 _143672 _143673 lt2 p s c) = (term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c).
Proof. exact (eq_refl (term4 _143669 _143670 _143671 _143672 _143673 lt2 p s c)). Qed.
Lemma lem8239503 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) (c : _143672 -> _143673) : term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c.
Proof. exact (EQ_MP (@lem8239502 _143669 _143670 _143671 _143672 _143673 lt2 p s c) (@lem8239501 _143669 _143670 _143671 _143672 _143673 lt2 p s c)). Qed.
Lemma lem8239504 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) (c : _143672 -> _143673) : (term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c) = ((term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c) = True).
Proof. exact (@lem7 (term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c)). Qed.
Lemma lem8239506 {A B P : Type'} (h1 : term6 A B P) : term6 A B P.
Proof. exact (h1). Qed.
Lemma lem8239507 {A B P : Type'} (lt2 : type1402 A) (h1 : term6 A B P) : term7 A B P lt2.
Proof. exact (@lem8239506 A B P h1 lt2). Qed.
Lemma lem8239508 {A B P : Type'} (lt2 : type1402 A) : (term7 A B P lt2) = (term8 A B P lt2).
Proof. exact (eq_refl (term7 A B P lt2)). Qed.
Lemma lem8239509 {A B P : Type'} (lt2 : type1402 A) (h1 : term6 A B P) : term8 A B P lt2.
Proof. exact (EQ_MP (@lem8239508 A B P lt2) (@lem8239507 A B P lt2 h1)). Qed.
Lemma lem8239510 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (h1 : term6 A B P) : term9 A B P lt2 p.
Proof. exact (@lem8239509 A B P lt2 h1 p). Qed.
Lemma lem8239511 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term9 A B P lt2 p) = (term10 A B P lt2 p).
Proof. exact (eq_refl (term9 A B P lt2 p)). Qed.
Lemma lem8239512 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (h1 : term6 A B P) : term10 A B P lt2 p.
Proof. exact (EQ_MP (@lem8239511 A B P lt2 p) (@lem8239510 A B P lt2 p h1)). Qed.
Lemma lem8239513 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (h1 : term6 A B P) : term11 A B P lt2 p s.
Proof. exact (@lem8239512 A B P lt2 p h1 s). Qed.
Lemma lem8239514 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) : (term11 A B P lt2 p s) = (term12 A B P lt2 p s).
Proof. exact (eq_refl (term11 A B P lt2 p s)). Qed.
Lemma lem8239515 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (h1 : term6 A B P) : term12 A B P lt2 p s.
Proof. exact (EQ_MP (@lem8239514 A B P lt2 p s) (@lem8239513 A B P lt2 p s h1)). Qed.
Lemma lem8239516 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : term6 A B P) : term13 A B P lt2 p s t.
Proof. exact (@lem8239515 A B P lt2 p s h1 t). Qed.
Lemma lem8239517 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : (term13 A B P lt2 p s t) = (term14 A B P lt2 p s t).
Proof. exact (eq_refl (term13 A B P lt2 p s t)). Qed.
Lemma lem8239518 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : term6 A B P) : term14 A B P lt2 p s t.
Proof. exact (EQ_MP (@lem8239517 A B P lt2 p s t) (@lem8239516 A B P lt2 p s t h1)). Qed.
Lemma lem8239519 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : @admissible A B A B P lt2 p s t) : @admissible A B A B P lt2 p s t.
Proof. exact (h1). Qed.
Lemma lem8239520 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : term6 A B P) (h2 : @admissible A B A B P lt2 p s t) : @superadmissible A B P lt2 p s t.
Proof. exact (@lem8239518 A B P lt2 p s t h1 (@lem8239519 A B P lt2 p s t h2)). Qed.
Lemma lem8239521 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : @admissible A B A B P lt2 p s t) : term15 A B P lt2 p s t.
Proof. exact (fun h0 : term6 A B P => @lem8239520 A B P lt2 p s t h0 h1). Qed.
Lemma lem8239522 {A B P : Type'} (h1 : term6 A B P) : term6 A B P.
Proof. exact (h1). Qed.
Lemma lem8239523 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : term6 A B P) (h2 : @admissible A B A B P lt2 p s t) : @superadmissible A B P lt2 p s t.
Proof. exact (@lem8239521 A B P lt2 p s t h2 (@lem8239522 A B P h1)). Qed.
Lemma lem8239524 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) (h1 : term6 A B P) : term14 A B P lt2 p s t.
Proof. exact (fun h0 : @admissible A B A B P lt2 p s t => @lem8239523 A B P lt2 p s t h1 h0). Qed.
Lemma lem8239525 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (h1 : term6 A B P) : term12 A B P lt2 p s.
Proof. exact (fun t : type558 A B P => @lem8239524 A B P lt2 p s t h1). Qed.
Lemma lem8239526 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (h1 : term6 A B P) : term10 A B P lt2 p.
Proof. exact (fun s : P -> A => @lem8239525 A B P lt2 p s h1). Qed.
Lemma lem8239527 {A B P : Type'} (lt2 : type1402 A) (h1 : term6 A B P) : term8 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8239526 A B P lt2 p h1). Qed.
Lemma lem8239528 {A B P : Type'} (h1 : term6 A B P) : term6 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8239527 A B P lt2 h1). Qed.
Lemma lem8239529 {A B P : Type'} : term16 A B P.
Proof. exact (fun h0 : term6 A B P => @lem8239528 A B P h0). Qed.
Lemma lem8239530 {A B P : Type'} : term6 A B P.
Proof. exact (@lem8239529 A B P (@lem8239494 A B P)). Qed.
Lemma lem8239531 {A B P : Type'} (lt2 : type1402 A) : term7 A B P lt2.
Proof. exact (@lem8239530 A B P lt2). Qed.
Lemma lem8239532 {A B P : Type'} (lt2 : type1402 A) : (term7 A B P lt2) = (term8 A B P lt2).
Proof. exact (eq_refl (term7 A B P lt2)). Qed.
Lemma lem8239533 {A B P : Type'} (lt2 : type1402 A) : term8 A B P lt2.
Proof. exact (EQ_MP (@lem8239532 A B P lt2) (@lem8239531 A B P lt2)). Qed.
Lemma lem8239534 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term9 A B P lt2 p.
Proof. exact (@lem8239533 A B P lt2 p). Qed.
Lemma lem8239535 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term9 A B P lt2 p) = (term10 A B P lt2 p).
Proof. exact (eq_refl (term9 A B P lt2 p)). Qed.
Lemma lem8239536 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term10 A B P lt2 p.
Proof. exact (EQ_MP (@lem8239535 A B P lt2 p) (@lem8239534 A B P lt2 p)). Qed.
Lemma lem8239537 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) : term11 A B P lt2 p s.
Proof. exact (@lem8239536 A B P lt2 p s). Qed.
Lemma lem8239538 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) : (term11 A B P lt2 p s) = (term12 A B P lt2 p s).
Proof. exact (eq_refl (term11 A B P lt2 p s)). Qed.
Lemma lem8239539 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) : term12 A B P lt2 p s.
Proof. exact (EQ_MP (@lem8239538 A B P lt2 p s) (@lem8239537 A B P lt2 p s)). Qed.
Lemma lem8239540 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : term13 A B P lt2 p s t.
Proof. exact (@lem8239539 A B P lt2 p s t). Qed.
Lemma lem8239541 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : (term13 A B P lt2 p s t) = (term14 A B P lt2 p s t).
Proof. exact (eq_refl (term13 A B P lt2 p s t)). Qed.
Lemma lem8239544 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : term14 A B P lt2 p s t.
Proof. exact (EQ_MP (@lem8239541 A B P lt2 p s t) (@lem8239540 A B P lt2 p s t)). Qed.
Lemma lem8239545 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (t : type573 _145219 _145220 _145221) : term17 _145219 _145220 _145221 lt2 p s t.
Proof. exact (@lem8239544 _145219 _145221 _145220 lt2 p s t). Qed.
Lemma lem8239546 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (c : _145220 -> _145221) : term18 _145219 _145220 _145221 lt2 p s c.
Proof. exact (@lem8239545 _145219 _145220 _145221 lt2 p s (term19 _145219 _145220 _145221 c)). Qed.
Lemma lem8239548 {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : type1470 _143669 _143670) (p : type560 _143670 _143671 _143672) (s : _143672 -> _143669) (c : _143672 -> _143673) : (term5 _143669 _143670 _143671 _143672 _143673 lt2 p s c) = True.
Proof. exact (EQ_MP (@lem8239504 _143669 _143670 _143671 _143672 _143673 lt2 p s c) (@lem8239503 _143669 _143670 _143671 _143672 _143673 lt2 p s c)). Qed.
Lemma lem8239549 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (c : _145220 -> _145221) : (term20 _145219 _145220 _145221 lt2 p s c) = True.
Proof. exact (@lem8239548 _145219 _145219 _145221 _145220 _145221 lt2 p s c). Qed.
Lemma lem8239550 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (c : _145220 -> _145221) : True = (term20 _145219 _145220 _145221 lt2 p s c).
Proof. exact (SYM (@lem8239549 _145219 _145220 _145221 lt2 p s c)). Qed.
Lemma lem8239551 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (c : _145220 -> _145221) : term20 _145219 _145220 _145221 lt2 p s c.
Proof. exact (EQ_MP (@lem8239550 _145219 _145220 _145221 lt2 p s c) (@lem0)). Qed.
Lemma lem8239552 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) (c : _145220 -> _145221) : term21 _145219 _145220 _145221 lt2 p s c.
Proof. exact (@lem8239546 _145219 _145220 _145221 lt2 p s c (@lem8239551 _145219 _145220 _145221 lt2 p s c)). Qed.
Lemma lem8239557 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) (s : _145220 -> _145219) : term22 _145219 _145220 _145221 lt2 p s.
Proof. exact (fun c : _145220 -> _145221 => @lem8239552 _145219 _145220 _145221 lt2 p s c). Qed.
Lemma lem8239562 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) (p : type575 _145219 _145220 _145221) : term23 _145219 _145220 _145221 lt2 p.
Proof. exact (fun s : _145220 -> _145219 => @lem8239557 _145219 _145220 _145221 lt2 p s). Qed.
Lemma lem8239567 {_145219 _145220 _145221 : Type'} (lt2 : type1402 _145219) : term24 _145219 _145220 _145221 lt2.
Proof. exact (fun p : type575 _145219 _145220 _145221 => @lem8239562 _145219 _145220 _145221 lt2 p). Qed.
