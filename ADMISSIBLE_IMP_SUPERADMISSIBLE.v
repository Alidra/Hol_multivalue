Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_IMP_SUPERADMISSIBLE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import admissible_spec.
Require Import superadmissible_spec.
Require Import tailadmissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21761_spec.
Lemma lem8233444 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8233445 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8233446 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8233445 t1) (@lem8233444 t1)). Qed.
Lemma lem8233447 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8233446 t1 t2). Qed.
Lemma lem8233448 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8233449 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8233448 t1 t2) (@lem8233447 t1 t2)). Qed.
Lemma lem8233450 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8233449 t1 t2 t3). Qed.
Lemma lem8233451 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8233452 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8233451 t1 t2 t3) (@lem8233450 t1 t2 t3)). Qed.
Lemma lem8233453 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8233452 t1 t2 t3)). Qed.
Lemma lem8233454 {A B P : Type'} (lt2 : type1402 A) : term7 A B P lt2.
Proof. exact (@lem8094644 A B P lt2). Qed.
Lemma lem8233455 {A B P : Type'} (lt2 : type1402 A) : (term7 A B P lt2) = (term8 A B P lt2).
Proof. exact (eq_refl (term7 A B P lt2)). Qed.
Lemma lem8233456 {A B P : Type'} (lt2 : type1402 A) : term8 A B P lt2.
Proof. exact (EQ_MP (@lem8233455 A B P lt2) (@lem8233454 A B P lt2)). Qed.
Lemma lem8233457 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : term9 A B P lt2 s.
Proof. exact (@lem8233456 A B P lt2 s). Qed.
Lemma lem8233458 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : (term9 A B P lt2 s) = (term10 A B P lt2 s).
Proof. exact (eq_refl (term9 A B P lt2 s)). Qed.
Lemma lem8233459 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : term10 A B P lt2 s.
Proof. exact (EQ_MP (@lem8233458 A B P lt2 s) (@lem8233457 A B P lt2 s)). Qed.
Lemma lem8233460 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term11 A B P lt2 s p.
Proof. exact (@lem8233459 A B P lt2 s p). Qed.
Lemma lem8233461 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term11 A B P lt2 s p) = (term12 A B P lt2 s p).
Proof. exact (eq_refl (term11 A B P lt2 s p)). Qed.
Lemma lem8233462 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term12 A B P lt2 s p.
Proof. exact (EQ_MP (@lem8233461 A B P lt2 s p) (@lem8233460 A B P lt2 s p)). Qed.
Lemma lem8233463 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : term13 A B P lt2 s p t.
Proof. exact (@lem8233462 A B P lt2 s p t). Qed.
Lemma lem8233464 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (term13 A B P lt2 s p t) = ((@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t)).
Proof. exact (eq_refl (term13 A B P lt2 s p t)). Qed.
Lemma lem8233466 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term15 _143606 _143608 _143614 lt2.
Proof. exact (@lem8096071 _143606 _143608 _143614 lt2). Qed.
Lemma lem8233467 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : (term15 _143606 _143608 _143614 lt2) = (term16 _143606 _143608 _143614 lt2).
Proof. exact (eq_refl (term15 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8233468 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term16 _143606 _143608 _143614 lt2.
Proof. exact (EQ_MP (@lem8233467 _143606 _143608 _143614 lt2) (@lem8233466 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8233469 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term17 _143606 _143608 _143614 lt2 p.
Proof. exact (@lem8233468 _143606 _143608 _143614 lt2 p). Qed.
Lemma lem8233470 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : (term17 _143606 _143608 _143614 lt2 p) = (term18 _143606 _143608 _143614 lt2 p).
Proof. exact (eq_refl (term17 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8233471 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term18 _143606 _143608 _143614 lt2 p.
Proof. exact (EQ_MP (@lem8233470 _143606 _143608 _143614 lt2 p) (@lem8233469 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8233472 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term19 _143606 _143608 _143614 lt2 p s.
Proof. exact (@lem8233471 _143606 _143608 _143614 lt2 p s). Qed.
Lemma lem8233473 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : (term19 _143606 _143608 _143614 lt2 p s) = (term20 _143606 _143608 _143614 lt2 p s).
Proof. exact (eq_refl (term19 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8233474 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term20 _143606 _143608 _143614 lt2 p s.
Proof. exact (EQ_MP (@lem8233473 _143606 _143608 _143614 lt2 p s) (@lem8233472 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8233475 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : term21 _143606 _143608 _143614 lt2 p s t.
Proof. exact (@lem8233474 _143606 _143608 _143614 lt2 p s t). Qed.
Lemma lem8233476 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (term21 _143606 _143608 _143614 lt2 p s t) = ((@superadmissible _143606 _143608 _143614 lt2 p s t) = (term22 _143606 _143608 _143614 lt2 p s t)).
Proof. exact (eq_refl (term21 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8233478 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term23 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8233479 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term23 _143449 _143452 _143456 _143457 _143462 p) = (term24 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term23 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8233480 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term24 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8233479 _143449 _143452 _143456 _143457 _143462 p) (@lem8233478 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8233481 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term25 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8233480 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8233482 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term25 _143449 _143452 _143456 _143457 _143462 p lt2) = (term26 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term25 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8233483 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term26 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8233482 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8233481 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8233484 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term27 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8233483 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8233485 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term27 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term28 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term27 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8233486 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term28 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8233485 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8233484 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8233487 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8233486 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8233488 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8233509 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8233488 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8233487 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8233510 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (@admissible A B A B P lt2 p s t) = (term31 A B P p lt2 s t).
Proof. exact (@lem8233509 A B A B P p lt2 s t). Qed.
Lemma lem8233539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8233540 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term32 A B P lt2 p s t) = (term33 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8233539) (@lem8233510 A B P p lt2 s t)). Qed.
Lemma lem8233542 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (@superadmissible _143606 _143608 _143614 lt2 p s t) = (term22 _143606 _143608 _143614 lt2 p s t).
Proof. exact (EQ_MP (@lem8233476 _143606 _143608 _143614 lt2 p s t) (@lem8233475 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8233543 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : (@superadmissible A B P lt2 p s t) = (term22 A B P lt2 p s t).
Proof. exact (@lem8233542 A B P lt2 p s t). Qed.
Lemma lem8233547 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8233488 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8233487 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8233548 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type560 A B P) : (@admissible A B A Prop P lt2 p s t) = (term34 A B P p lt2 s t).
Proof. exact (@lem8233547 A B A Prop P p lt2 s t). Qed.
Lemma lem8233549 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term35 A B P lt2 s p) = (term36 A B P lt2 s p).
Proof. exact (@lem8233548 A B P (term37 A B P) lt2 s p). Qed.
Lemma lem8233567 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233568 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8233567 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8233569 {A B P : Type'} (f : A -> B) : (term40 A B P f) = (term41 A B P f).
Proof. exact (@lem8233568 A B P (term37 A B P) f). Qed.
Lemma lem8233570 {A B P : Type'} (f : A -> B) : (term41 A B P f) = (term42 P).
Proof. exact (eq_refl (term41 A B P f)). Qed.
Lemma lem8233571 {A B P : Type'} : (term43 A B P) = (term37 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8233570 A B P f)). Qed.
Lemma lem8233572 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8233573 {A B P : Type'} (f : A -> B) : (term40 A B P f) = (term41 A B P f).
Proof. exact (MK_COMB (@lem8233571 A B P) (@lem8233572 A B f)). Qed.
Lemma lem8233574 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8233575 {A B P : Type'} (f : A -> B) : (term44 A B P f) = (term45 A B P f).
Proof. exact (MK_COMB (@lem8233574 P) (@lem8233573 A B P f)). Qed.
Lemma lem8233576 {A B P : Type'} (f : A -> B) : (term41 A B P f) = (term42 P).
Proof. exact (eq_refl (term41 A B P f)). Qed.
Lemma lem8233577 {A B P : Type'} (f : A -> B) : ((term40 A B P f) = (term41 A B P f)) = ((term41 A B P f) = (term42 P)).
Proof. exact (MK_COMB (@lem8233575 A B P f) (@lem8233576 A B P f)). Qed.
Lemma lem8233578 {A B P : Type'} (f : A -> B) : (term41 A B P f) = (term42 P).
Proof. exact (EQ_MP (@lem8233577 A B P f) (@lem8233569 A B P f)). Qed.
Lemma lem8233579 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233580 {A B P : Type'} (f : A -> B) (a : P) : (term46 A B P f a) = (term47 P a).
Proof. exact (MK_COMB (@lem8233578 A B P f) (@lem8233579 P a)). Qed.
Lemma lem8233582 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233583 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8233582 P Prop f y). Qed.
Lemma lem8233584 {P : Type'} (a : P) : (term49 P a) = (term47 P a).
Proof. exact (@lem8233583 P (term42 P) a). Qed.
Lemma lem8233585 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (eq_refl (term47 P a)). Qed.
Lemma lem8233586 {P : Type'} : (term50 P) = (term42 P).
Proof. exact (fun_ext (fun a : P => @lem8233585 P a)). Qed.
Lemma lem8233587 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233588 {P : Type'} (a : P) : (term49 P a) = (term47 P a).
Proof. exact (MK_COMB (@lem8233586 P) (@lem8233587 P a)). Qed.
Lemma lem8233589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8233590 {P : Type'} (a : P) : (term51 P a) = (term52 P a).
Proof. exact (MK_COMB (@lem8233589) (@lem8233588 P a)). Qed.
Lemma lem8233591 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (eq_refl (term47 P a)). Qed.
Lemma lem8233592 {P : Type'} (a : P) : ((term49 P a) = (term47 P a)) = ((term47 P a) = True).
Proof. exact (MK_COMB (@lem8233590 P a) (@lem8233591 P a)). Qed.
Lemma lem8233593 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (EQ_MP (@lem8233592 P a) (@lem8233584 P a)). Qed.
Lemma lem8233594 {A B P : Type'} (f : A -> B) (a : P) : (term46 A B P f a) = True.
Proof. exact (TRANS (@lem8233580 A B P f a) (@lem8233593 P a)). Qed.
Lemma lem8233595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233596 {A B P : Type'} (f : A -> B) (a : P) : (term53 A B P f a) = (and True).
Proof. exact (MK_COMB (@lem8233595) (@lem8233594 A B P f a)). Qed.
Lemma lem8233600 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233601 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8233600 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8233602 {A B P : Type'} (g : A -> B) : (term40 A B P g) = (term41 A B P g).
Proof. exact (@lem8233601 A B P (term37 A B P) g). Qed.
Lemma lem8233603 {A B P : Type'} (f : A -> B) : (term41 A B P f) = (term42 P).
Proof. exact (eq_refl (term41 A B P f)). Qed.
Lemma lem8233604 {A B P : Type'} : (term43 A B P) = (term37 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8233603 A B P f)). Qed.
Lemma lem8233605 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8233606 {A B P : Type'} (g : A -> B) : (term40 A B P g) = (term41 A B P g).
Proof. exact (MK_COMB (@lem8233604 A B P) (@lem8233605 A B g)). Qed.
Lemma lem8233607 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8233608 {A B P : Type'} (g : A -> B) : (term44 A B P g) = (term45 A B P g).
Proof. exact (MK_COMB (@lem8233607 P) (@lem8233606 A B P g)). Qed.
Lemma lem8233609 {A B P : Type'} (g : A -> B) : (term41 A B P g) = (term42 P).
Proof. exact (eq_refl (term41 A B P g)). Qed.
Lemma lem8233610 {A B P : Type'} (g : A -> B) : ((term40 A B P g) = (term41 A B P g)) = ((term41 A B P g) = (term42 P)).
Proof. exact (MK_COMB (@lem8233608 A B P g) (@lem8233609 A B P g)). Qed.
Lemma lem8233611 {A B P : Type'} (g : A -> B) : (term41 A B P g) = (term42 P).
Proof. exact (EQ_MP (@lem8233610 A B P g) (@lem8233602 A B P g)). Qed.
Lemma lem8233612 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233613 {A B P : Type'} (g : A -> B) (a : P) : (term46 A B P g a) = (term47 P a).
Proof. exact (MK_COMB (@lem8233611 A B P g) (@lem8233612 P a)). Qed.
Lemma lem8233615 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233616 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8233615 P Prop f y). Qed.
Lemma lem8233617 {P : Type'} (a : P) : (term49 P a) = (term47 P a).
Proof. exact (@lem8233616 P (term42 P) a). Qed.
Lemma lem8233618 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (eq_refl (term47 P a)). Qed.
Lemma lem8233619 {P : Type'} : (term50 P) = (term42 P).
Proof. exact (fun_ext (fun a : P => @lem8233618 P a)). Qed.
Lemma lem8233620 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233621 {P : Type'} (a : P) : (term49 P a) = (term47 P a).
Proof. exact (MK_COMB (@lem8233619 P) (@lem8233620 P a)). Qed.
Lemma lem8233622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8233623 {P : Type'} (a : P) : (term51 P a) = (term52 P a).
Proof. exact (MK_COMB (@lem8233622) (@lem8233621 P a)). Qed.
Lemma lem8233624 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (eq_refl (term47 P a)). Qed.
Lemma lem8233625 {P : Type'} (a : P) : ((term49 P a) = (term47 P a)) = ((term47 P a) = True).
Proof. exact (MK_COMB (@lem8233623 P a) (@lem8233624 P a)). Qed.
Lemma lem8233626 {P : Type'} (a : P) : (term47 P a) = True.
Proof. exact (EQ_MP (@lem8233625 P a) (@lem8233617 P a)). Qed.
Lemma lem8233627 {A B P : Type'} (g : A -> B) (a : P) : (term46 A B P g a) = True.
Proof. exact (TRANS (@lem8233613 A B P g a) (@lem8233626 P a)). Qed.
Lemma lem8233628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233629 {A B P : Type'} (g : A -> B) (a : P) : (term53 A B P g a) = (and True).
Proof. exact (MK_COMB (@lem8233628) (@lem8233627 A B P g a)). Qed.
Lemma lem8233638 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (eq_refl (term54 A B P lt2 s a f g)). Qed.
Lemma lem8233639 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term55 A B P lt2 s a f g) = (term56 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8233629 A B P g a) (@lem8233638 A B P lt2 s a f g)). Qed.
Lemma lem8233641 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8233642 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term56 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (@lem8233641 (term54 A B P lt2 s a f g)). Qed.
Lemma lem8233651 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term55 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8233639 A B P lt2 s a f g) (@lem8233642 A B P lt2 s a f g)). Qed.
Lemma lem8233652 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term57 A B P lt2 s a f g) = (term56 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8233596 A B P f a) (@lem8233651 A B P lt2 s a f g)). Qed.
Lemma lem8233654 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8233655 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term56 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (@lem8233654 (term54 A B P lt2 s a f g)). Qed.
Lemma lem8233664 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term57 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8233652 A B P lt2 s a f g) (@lem8233655 A B P lt2 s a f g)). Qed.
Lemma lem8233665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8233666 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term58 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8233665) (@lem8233664 A B P lt2 s a f g)). Qed.
Lemma lem8233669 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = ((p f a) = (p g a)).
Proof. exact (eq_refl ((p f a) = (p g a))). Qed.
Lemma lem8233670 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term60 A B P lt2 s f p g a) = (term61 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8233666 A B P lt2 s a f g) (@lem8233669 A B P f p g a)). Qed.
Lemma lem8233673 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term62 A B P lt2 s f p g) = (term63 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8233670 A B P lt2 s f p g a)). Qed.
Lemma lem8233674 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8233675 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term64 A B P lt2 s f p g) = (term65 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8233674 P) (@lem8233673 A B P lt2 s f p g)). Qed.
Lemma lem8233680 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term66 A B P lt2 s f p) = (term67 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8233675 A B P lt2 s f p g)). Qed.
Lemma lem8233681 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8233682 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term68 A B P lt2 s f p) = (term69 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8233681 A B) (@lem8233680 A B P lt2 s f p)). Qed.
Lemma lem8233687 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term70 A B P lt2 s p) = (term71 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8233682 A B P lt2 s f p)). Qed.
Lemma lem8233688 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8233689 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term36 A B P lt2 s p) = (term72 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8233688 A B) (@lem8233687 A B P lt2 s p)). Qed.
Lemma lem8233694 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term35 A B P lt2 s p) = (term72 A B P lt2 s p).
Proof. exact (TRANS (@lem8233549 A B P lt2 s p) (@lem8233689 A B P lt2 s p)). Qed.
Lemma lem8233695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8233696 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term73 A B P lt2 s p) = (term74 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8233695) (@lem8233694 A B P lt2 s p)). Qed.
Lemma lem8233698 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t).
Proof. exact (EQ_MP (@lem8233464 A B P lt2 s p t) (@lem8233463 A B P lt2 s p t)). Qed.
Lemma lem8233699 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t).
Proof. exact (@lem8233698 A B P lt2 s p t). Qed.
Lemma lem8233776 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (term22 A B P lt2 p s t) = (term75 A B P lt2 s p t).
Proof. exact (MK_COMB (@lem8233696 A B P lt2 s p) (@lem8233699 A B P lt2 s p t)). Qed.
Lemma lem8233779 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@superadmissible A B P lt2 p s t) = (term75 A B P lt2 s p t).
Proof. exact (TRANS (@lem8233543 A B P lt2 p s t) (@lem8233776 A B P lt2 s p t)). Qed.
Lemma lem8233780 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (term76 A B P lt2 p s t) = (term77 A B P lt2 s p t).
Proof. exact (MK_COMB (@lem8233540 A B P p lt2 s t) (@lem8233779 A B P lt2 s p t)). Qed.
Lemma lem8233783 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term78 A B P lt2 p s) = (term79 A B P lt2 s p).
Proof. exact (fun_ext (fun t : type558 A B P => @lem8233780 A B P lt2 s p t)). Qed.
Lemma lem8233784 {A B P : Type'} : (@all ((A -> B) -> P -> B)) = (@all ((A -> B) -> P -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> B))). Qed.
Lemma lem8233785 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term80 A B P lt2 p s) = (term81 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8233784 A B P) (@lem8233783 A B P lt2 s p)). Qed.
Lemma lem8233790 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term82 A B P lt2 p) = (term83 A B P lt2 p).
Proof. exact (fun_ext (fun s : P -> A => @lem8233785 A B P lt2 s p)). Qed.
Lemma lem8233791 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8233792 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term84 A B P lt2 p) = (term85 A B P lt2 p).
Proof. exact (MK_COMB (@lem8233791 A P) (@lem8233790 A B P lt2 p)). Qed.
Lemma lem8233797 {A B P : Type'} (lt2 : type1402 A) : (term86 A B P lt2) = (term87 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8233792 A B P lt2 p)). Qed.
Lemma lem8233798 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8233799 {A B P : Type'} (lt2 : type1402 A) : (term88 A B P lt2) = (term89 A B P lt2).
Proof. exact (MK_COMB (@lem8233798 A B P) (@lem8233797 A B P lt2)). Qed.
Lemma lem8233804 {A B P : Type'} : (term90 A B P) = (term91 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8233799 A B P lt2)). Qed.
Lemma lem8233805 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8233806 {A B P : Type'} : (term92 A B P) = (term93 A B P).
Proof. exact (MK_COMB (@lem8233805 A) (@lem8233804 A B P)). Qed.
Lemma lem8233811 {A B P : Type'} : (term93 A B P) = (term92 A B P).
Proof. exact (SYM (@lem8233806 A B P)). Qed.
Lemma lem8233812 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term31 A B P p lt2 s t.
Proof. exact (h1). Qed.
Lemma lem8233813 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term72 A B P lt2 s p) : term72 A B P lt2 s p.
Proof. exact (h1). Qed.
Lemma lem8233855 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233856 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8233855 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8233857 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (@lem8233856 A B P (term96 A B P) f). Qed.
Lemma lem8233858 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8233859 {A B P : Type'} : (term98 A B P) = (term96 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8233858 A B P f)). Qed.
Lemma lem8233860 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8233861 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (MK_COMB (@lem8233859 A B P) (@lem8233860 A B f)). Qed.
Lemma lem8233862 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8233863 {A B P : Type'} (f : A -> B) : (term99 A B P f) = (term100 A B P f).
Proof. exact (MK_COMB (@lem8233862 P) (@lem8233861 A B P f)). Qed.
Lemma lem8233864 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8233865 {A B P : Type'} (f : A -> B) : ((term94 A B P f) = (term95 A B P f)) = ((term95 A B P f) = (term97 P)).
Proof. exact (MK_COMB (@lem8233863 A B P f) (@lem8233864 A B P f)). Qed.
Lemma lem8233866 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (EQ_MP (@lem8233865 A B P f) (@lem8233857 A B P f)). Qed.
Lemma lem8233867 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233868 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = (term102 P a).
Proof. exact (MK_COMB (@lem8233866 A B P f) (@lem8233867 P a)). Qed.
Lemma lem8233870 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233871 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8233870 P Prop f y). Qed.
Lemma lem8233872 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (@lem8233871 P (term97 P) a). Qed.
Lemma lem8233873 {P : Type'} (x : P) : (term102 P x) = False.
Proof. exact (eq_refl (term102 P x)). Qed.
Lemma lem8233874 {P : Type'} : (term104 P) = (term97 P).
Proof. exact (fun_ext (fun x : P => @lem8233873 P x)). Qed.
Lemma lem8233875 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233876 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (MK_COMB (@lem8233874 P) (@lem8233875 P a)). Qed.
Lemma lem8233877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8233878 {P : Type'} (a : P) : (term105 P a) = (term106 P a).
Proof. exact (MK_COMB (@lem8233877) (@lem8233876 P a)). Qed.
Lemma lem8233879 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (eq_refl (term102 P a)). Qed.
Lemma lem8233880 {P : Type'} (a : P) : ((term103 P a) = (term102 P a)) = ((term102 P a) = False).
Proof. exact (MK_COMB (@lem8233878 P a) (@lem8233879 P a)). Qed.
Lemma lem8233881 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (EQ_MP (@lem8233880 P a) (@lem8233872 P a)). Qed.
Lemma lem8233882 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = False.
Proof. exact (TRANS (@lem8233868 A B P f a) (@lem8233881 P a)). Qed.
Lemma lem8233883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233884 {A B P : Type'} (f : A -> B) (a : P) : (term107 A B P f a) = (and False).
Proof. exact (MK_COMB (@lem8233883) (@lem8233882 A B P f a)). Qed.
Lemma lem8233886 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233887 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term108 A B P f y) = (f y).
Proof. exact (@lem8233886 (A -> B) (P -> A) f y). Qed.
Lemma lem8233888 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (@lem8233887 A B P (term111 A B P anything) f). Qed.
Lemma lem8233889 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8233890 {A B P : Type'} (anything : P -> A) : (term112 A B P anything) = (term111 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8233889 A B P f anything)). Qed.
Lemma lem8233891 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8233892 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (MK_COMB (@lem8233890 A B P anything) (@lem8233891 A B f)). Qed.
Lemma lem8233893 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8233894 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term113 A B P anything f) = (term114 A B P anything f).
Proof. exact (MK_COMB (@lem8233893 A P) (@lem8233892 A B P anything f)). Qed.
Lemma lem8233895 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8233896 {A B P : Type'} (f : A -> B) (anything : P -> A) : ((term109 A B P anything f) = (term110 A B P anything f)) = ((term110 A B P anything f) = anything).
Proof. exact (MK_COMB (@lem8233894 A B P anything f) (@lem8233895 A B P f anything)). Qed.
Lemma lem8233897 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (EQ_MP (@lem8233896 A B P f anything) (@lem8233888 A B P anything f)). Qed.
Lemma lem8233898 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233899 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term115 A B P anything f a) = (anything a).
Proof. exact (MK_COMB (@lem8233897 A B P f anything) (@lem8233898 P a)). Qed.
Lemma lem8233900 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8233901 {A B P : Type'} (f : A -> B) (lt2 : type1402 A) (y : A) (anything : P -> A) (a : P) : (term116 A B P lt2 y anything f a) = (term117 A P lt2 y anything a).
Proof. exact (MK_COMB (@lem8233900 A lt2 y) (@lem8233899 A B P f anything a)). Qed.
Lemma lem8233902 {A B P : Type'} (f : A -> B) (lt2 : type1402 A) (y : A) (anything : P -> A) (a : P) : (term118 A B P lt2 y anything f a) = (term119 A P lt2 y anything a).
Proof. exact (MK_COMB (@lem8233884 A B P f a) (@lem8233901 A B P f lt2 y anything a)). Qed.
Lemma lem8233904 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8233905 {A P : Type'} (lt2 : type1402 A) (y : A) (anything : P -> A) (a : P) : (term119 A P lt2 y anything a) = False.
Proof. exact (@lem8233904 (term117 A P lt2 y anything a)). Qed.
Lemma lem8233906 {A B P : Type'} (lt2 : type1402 A) (y : A) (anything : P -> A) (f : A -> B) (a : P) : (term118 A B P lt2 y anything f a) = False.
Proof. exact (TRANS (@lem8233902 A B P f lt2 y anything a) (@lem8233905 A P lt2 y anything a)). Qed.
Lemma lem8233907 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8233908 {A B P : Type'} (lt2 : type1402 A) (y : A) (anything : P -> A) (f : A -> B) (a : P) : (term120 A B P lt2 y anything f a) = (imp False).
Proof. exact (MK_COMB (@lem8233907) (@lem8233906 A B P lt2 y anything f a)). Qed.
Lemma lem8233909 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term117 A P lt2 y s a) = (term117 A P lt2 y s a).
Proof. exact (eq_refl (term117 A P lt2 y s a)). Qed.
Lemma lem8233910 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term121 A B P anything f lt2 y s a) = (term122 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8233908 A B P lt2 y anything f a) (@lem8233909 A P lt2 y s a)). Qed.
Lemma lem8233912 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8233913 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term122 A P lt2 y s a) = True.
Proof. exact (@lem8233912 (term117 A P lt2 y s a)). Qed.
Lemma lem8233914 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term121 A B P anything f lt2 y s a) = True.
Proof. exact (TRANS (@lem8233910 A B P anything f lt2 y s a) (@lem8233913 A P lt2 y s a)). Qed.
Lemma lem8233915 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term123 A B P anything f lt2 s a) = (term42 A).
Proof. exact (fun_ext (fun y : A => @lem8233914 A B P anything f lt2 y s a)). Qed.
Lemma lem8233916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8233917 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term124 A B P anything f lt2 s a) = (term125 A).
Proof. exact (MK_COMB (@lem8233916 A) (@lem8233915 A B P anything f lt2 s a)). Qed.
Lemma lem8233919 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8233920 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (@lem8233919 A t). Qed.
Lemma lem8233921 {A : Type'} : (term125 A) = True.
Proof. exact (@lem8233920 A True). Qed.
Lemma lem8233922 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term124 A B P anything f lt2 s a) = True.
Proof. exact (TRANS (@lem8233917 A B P anything f lt2 s a) (@lem8233921 A)). Qed.
Lemma lem8233923 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term127 A B P anything f lt2 s) = (term42 P).
Proof. exact (fun_ext (fun a : P => @lem8233922 A B P anything f lt2 s a)). Qed.
Lemma lem8233924 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8233925 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term128 A B P anything f lt2 s) = (term125 P).
Proof. exact (MK_COMB (@lem8233924 P) (@lem8233923 A B P anything f lt2 s)). Qed.
Lemma lem8233927 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8233928 {P : Type'} (t : Prop) : (term126 P t) = t.
Proof. exact (@lem8233927 P t). Qed.
Lemma lem8233929 {P : Type'} : (term125 P) = True.
Proof. exact (@lem8233928 P True). Qed.
Lemma lem8233930 {A B P : Type'} (anything : P -> A) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term128 A B P anything f lt2 s) = True.
Proof. exact (TRANS (@lem8233925 A B P anything f lt2 s) (@lem8233929 P)). Qed.
Lemma lem8233931 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) : (term129 A B P anything lt2 s) = (term130 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem8233930 A B P anything f lt2 s)). Qed.
Lemma lem8233932 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8233933 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) : (term131 A B P anything lt2 s) = (term132 A B).
Proof. exact (MK_COMB (@lem8233932 A B) (@lem8233931 A B P anything lt2 s)). Qed.
Lemma lem8233935 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8233936 {A B : Type'} (t : Prop) : (term133 A B t) = t.
Proof. exact (@lem8233935 (A -> B) t). Qed.
Lemma lem8233937 {A B : Type'} : (term132 A B) = True.
Proof. exact (@lem8233936 A B True). Qed.
Lemma lem8233938 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) : (term131 A B P anything lt2 s) = True.
Proof. exact (TRANS (@lem8233933 A B P anything lt2 s) (@lem8233937 A B)). Qed.
Lemma lem8233939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233940 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) : (term134 A B P anything lt2 s) = (and True).
Proof. exact (MK_COMB (@lem8233939) (@lem8233938 A B P anything lt2 s)). Qed.
Lemma lem8233970 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233971 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8233970 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8233972 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (@lem8233971 A B P (term96 A B P) f). Qed.
Lemma lem8233973 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8233974 {A B P : Type'} : (term98 A B P) = (term96 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8233973 A B P f)). Qed.
Lemma lem8233975 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8233976 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (MK_COMB (@lem8233974 A B P) (@lem8233975 A B f)). Qed.
Lemma lem8233977 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8233978 {A B P : Type'} (f : A -> B) : (term99 A B P f) = (term100 A B P f).
Proof. exact (MK_COMB (@lem8233977 P) (@lem8233976 A B P f)). Qed.
Lemma lem8233979 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8233980 {A B P : Type'} (f : A -> B) : ((term94 A B P f) = (term95 A B P f)) = ((term95 A B P f) = (term97 P)).
Proof. exact (MK_COMB (@lem8233978 A B P f) (@lem8233979 A B P f)). Qed.
Lemma lem8233981 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (EQ_MP (@lem8233980 A B P f) (@lem8233972 A B P f)). Qed.
Lemma lem8233982 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233983 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = (term102 P a).
Proof. exact (MK_COMB (@lem8233981 A B P f) (@lem8233982 P a)). Qed.
Lemma lem8233985 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8233986 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8233985 P Prop f y). Qed.
Lemma lem8233987 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (@lem8233986 P (term97 P) a). Qed.
Lemma lem8233988 {P : Type'} (x : P) : (term102 P x) = False.
Proof. exact (eq_refl (term102 P x)). Qed.
Lemma lem8233989 {P : Type'} : (term104 P) = (term97 P).
Proof. exact (fun_ext (fun x : P => @lem8233988 P x)). Qed.
Lemma lem8233990 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8233991 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (MK_COMB (@lem8233989 P) (@lem8233990 P a)). Qed.
Lemma lem8233992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8233993 {P : Type'} (a : P) : (term105 P a) = (term106 P a).
Proof. exact (MK_COMB (@lem8233992) (@lem8233991 P a)). Qed.
Lemma lem8233994 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (eq_refl (term102 P a)). Qed.
Lemma lem8233995 {P : Type'} (a : P) : ((term103 P a) = (term102 P a)) = ((term102 P a) = False).
Proof. exact (MK_COMB (@lem8233993 P a) (@lem8233994 P a)). Qed.
Lemma lem8233996 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (EQ_MP (@lem8233995 P a) (@lem8233987 P a)). Qed.
Lemma lem8233997 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = False.
Proof. exact (TRANS (@lem8233983 A B P f a) (@lem8233996 P a)). Qed.
Lemma lem8233998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8233999 {A B P : Type'} (f : A -> B) (a : P) : (term135 A B P f a) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8233998) (@lem8233997 A B P f a)). Qed.
Lemma lem8234001 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234002 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8234001 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8234003 {A B P : Type'} (g : A -> B) : (term94 A B P g) = (term95 A B P g).
Proof. exact (@lem8234002 A B P (term96 A B P) g). Qed.
Lemma lem8234004 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8234005 {A B P : Type'} : (term98 A B P) = (term96 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8234004 A B P f)). Qed.
Lemma lem8234006 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8234007 {A B P : Type'} (g : A -> B) : (term94 A B P g) = (term95 A B P g).
Proof. exact (MK_COMB (@lem8234005 A B P) (@lem8234006 A B g)). Qed.
Lemma lem8234008 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8234009 {A B P : Type'} (g : A -> B) : (term99 A B P g) = (term100 A B P g).
Proof. exact (MK_COMB (@lem8234008 P) (@lem8234007 A B P g)). Qed.
Lemma lem8234010 {A B P : Type'} (g : A -> B) : (term95 A B P g) = (term97 P).
Proof. exact (eq_refl (term95 A B P g)). Qed.
Lemma lem8234011 {A B P : Type'} (g : A -> B) : ((term94 A B P g) = (term95 A B P g)) = ((term95 A B P g) = (term97 P)).
Proof. exact (MK_COMB (@lem8234009 A B P g) (@lem8234010 A B P g)). Qed.
Lemma lem8234012 {A B P : Type'} (g : A -> B) : (term95 A B P g) = (term97 P).
Proof. exact (EQ_MP (@lem8234011 A B P g) (@lem8234003 A B P g)). Qed.
Lemma lem8234013 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234014 {A B P : Type'} (g : A -> B) (a : P) : (term101 A B P g a) = (term102 P a).
Proof. exact (MK_COMB (@lem8234012 A B P g) (@lem8234013 P a)). Qed.
Lemma lem8234016 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234017 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8234016 P Prop f y). Qed.
Lemma lem8234018 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (@lem8234017 P (term97 P) a). Qed.
Lemma lem8234019 {P : Type'} (x : P) : (term102 P x) = False.
Proof. exact (eq_refl (term102 P x)). Qed.
Lemma lem8234020 {P : Type'} : (term104 P) = (term97 P).
Proof. exact (fun_ext (fun x : P => @lem8234019 P x)). Qed.
Lemma lem8234021 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234022 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (MK_COMB (@lem8234020 P) (@lem8234021 P a)). Qed.
Lemma lem8234023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8234024 {P : Type'} (a : P) : (term105 P a) = (term106 P a).
Proof. exact (MK_COMB (@lem8234023) (@lem8234022 P a)). Qed.
Lemma lem8234025 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (eq_refl (term102 P a)). Qed.
Lemma lem8234026 {P : Type'} (a : P) : ((term103 P a) = (term102 P a)) = ((term102 P a) = False).
Proof. exact (MK_COMB (@lem8234024 P a) (@lem8234025 P a)). Qed.
Lemma lem8234027 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (EQ_MP (@lem8234026 P a) (@lem8234018 P a)). Qed.
Lemma lem8234028 {A B P : Type'} (g : A -> B) (a : P) : (term101 A B P g a) = False.
Proof. exact (TRANS (@lem8234014 A B P g a) (@lem8234027 P a)). Qed.
Lemma lem8234029 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : ((term101 A B P f a) = (term101 A B P g a)) = (False = False).
Proof. exact (MK_COMB (@lem8233999 A B P f a) (@lem8234028 A B P g a)). Qed.
Lemma lem8234031 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8234032 : (False = False) = (~ False).
Proof. exact (@lem8234031 False). Qed.
Lemma lem8234034 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8234035 : (False = False) = True.
Proof. exact (TRANS (@lem8234032) (@lem8234034)). Qed.
Lemma lem8234036 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : ((term101 A B P f a) = (term101 A B P g a)) = True.
Proof. exact (TRANS (@lem8234029 A B P f g a) (@lem8234035)). Qed.
Lemma lem8234037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234038 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : (term136 A B P f g a) = (and True).
Proof. exact (MK_COMB (@lem8234037) (@lem8234036 A B P f g a)). Qed.
Lemma lem8234044 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234045 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term108 A B P f y) = (f y).
Proof. exact (@lem8234044 (A -> B) (P -> A) f y). Qed.
Lemma lem8234046 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (@lem8234045 A B P (term111 A B P anything) f). Qed.
Lemma lem8234047 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8234048 {A B P : Type'} (anything : P -> A) : (term112 A B P anything) = (term111 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8234047 A B P f anything)). Qed.
Lemma lem8234049 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234050 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (MK_COMB (@lem8234048 A B P anything) (@lem8234049 A B f)). Qed.
Lemma lem8234051 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8234052 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term113 A B P anything f) = (term114 A B P anything f).
Proof. exact (MK_COMB (@lem8234051 A P) (@lem8234050 A B P anything f)). Qed.
Lemma lem8234053 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8234054 {A B P : Type'} (f : A -> B) (anything : P -> A) : ((term109 A B P anything f) = (term110 A B P anything f)) = ((term110 A B P anything f) = anything).
Proof. exact (MK_COMB (@lem8234052 A B P anything f) (@lem8234053 A B P f anything)). Qed.
Lemma lem8234055 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (EQ_MP (@lem8234054 A B P f anything) (@lem8234046 A B P anything f)). Qed.
Lemma lem8234056 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234057 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term115 A B P anything f a) = (anything a).
Proof. exact (MK_COMB (@lem8234055 A B P f anything) (@lem8234056 P a)). Qed.
Lemma lem8234058 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8234059 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term137 A B P anything f a) = (term138 A P anything a).
Proof. exact (MK_COMB (@lem8234058 A) (@lem8234057 A B P f anything a)). Qed.
Lemma lem8234061 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234062 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term108 A B P f y) = (f y).
Proof. exact (@lem8234061 (A -> B) (P -> A) f y). Qed.
Lemma lem8234063 {A B P : Type'} (anything : P -> A) (g : A -> B) : (term109 A B P anything g) = (term110 A B P anything g).
Proof. exact (@lem8234062 A B P (term111 A B P anything) g). Qed.
Lemma lem8234064 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8234065 {A B P : Type'} (anything : P -> A) : (term112 A B P anything) = (term111 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8234064 A B P f anything)). Qed.
Lemma lem8234066 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8234067 {A B P : Type'} (anything : P -> A) (g : A -> B) : (term109 A B P anything g) = (term110 A B P anything g).
Proof. exact (MK_COMB (@lem8234065 A B P anything) (@lem8234066 A B g)). Qed.
Lemma lem8234068 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8234069 {A B P : Type'} (anything : P -> A) (g : A -> B) : (term113 A B P anything g) = (term114 A B P anything g).
Proof. exact (MK_COMB (@lem8234068 A P) (@lem8234067 A B P anything g)). Qed.
Lemma lem8234070 {A B P : Type'} (g : A -> B) (anything : P -> A) : (term110 A B P anything g) = anything.
Proof. exact (eq_refl (term110 A B P anything g)). Qed.
Lemma lem8234071 {A B P : Type'} (g : A -> B) (anything : P -> A) : ((term109 A B P anything g) = (term110 A B P anything g)) = ((term110 A B P anything g) = anything).
Proof. exact (MK_COMB (@lem8234069 A B P anything g) (@lem8234070 A B P g anything)). Qed.
Lemma lem8234072 {A B P : Type'} (g : A -> B) (anything : P -> A) : (term110 A B P anything g) = anything.
Proof. exact (EQ_MP (@lem8234071 A B P g anything) (@lem8234063 A B P anything g)). Qed.
Lemma lem8234073 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234074 {A B P : Type'} (g : A -> B) (anything : P -> A) (a : P) : (term115 A B P anything g a) = (anything a).
Proof. exact (MK_COMB (@lem8234072 A B P g anything) (@lem8234073 P a)). Qed.
Lemma lem8234075 {A B P : Type'} (f : A -> B) (g : A -> B) (anything : P -> A) (a : P) : ((term115 A B P anything f a) = (term115 A B P anything g a)) = ((anything a) = (anything a)).
Proof. exact (MK_COMB (@lem8234059 A B P f anything a) (@lem8234074 A B P g anything a)). Qed.
Lemma lem8234077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8234078 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem8234077 A x). Qed.
Lemma lem8234079 {A P : Type'} (anything : P -> A) (a : P) : ((anything a) = (anything a)) = True.
Proof. exact (@lem8234078 A (anything a)). Qed.
Lemma lem8234080 {A B P : Type'} (f : A -> B) (anything : P -> A) (g : A -> B) (a : P) : ((term115 A B P anything f a) = (term115 A B P anything g a)) = True.
Proof. exact (TRANS (@lem8234075 A B P f g anything a) (@lem8234079 A P anything a)). Qed.
Lemma lem8234081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234082 {A B P : Type'} (f : A -> B) (anything : P -> A) (g : A -> B) (a : P) : (term139 A B P f anything g a) = (and True).
Proof. exact (MK_COMB (@lem8234081) (@lem8234080 A B P f anything g a)). Qed.
Lemma lem8234086 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234087 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term140 A B P f y) = (f y).
Proof. exact (@lem8234086 (A -> B) (P -> B) f y). Qed.
Lemma lem8234088 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term141 A B P p t fixed f) = (term142 A B P p t fixed f).
Proof. exact (@lem8234087 A B P (term143 A B P p t fixed) f). Qed.
Lemma lem8234089 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (eq_refl (term142 A B P p t fixed f)). Qed.
Lemma lem8234090 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term145 A B P p t fixed) = (term143 A B P p t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234089 A B P p t f fixed)). Qed.
Lemma lem8234091 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234092 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term141 A B P p t fixed f) = (term142 A B P p t fixed f).
Proof. exact (MK_COMB (@lem8234090 A B P p t fixed) (@lem8234091 A B f)). Qed.
Lemma lem8234093 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8234094 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term146 A B P p t fixed f) = (term147 A B P p t fixed f).
Proof. exact (MK_COMB (@lem8234093 B P) (@lem8234092 A B P p t fixed f)). Qed.
Lemma lem8234095 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (eq_refl (term142 A B P p t fixed f)). Qed.
Lemma lem8234096 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : ((term141 A B P p t fixed f) = (term142 A B P p t fixed f)) = ((term142 A B P p t fixed f) = (term144 A B P p t f fixed)).
Proof. exact (MK_COMB (@lem8234094 A B P p t fixed f) (@lem8234095 A B P p t f fixed)). Qed.
Lemma lem8234097 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (EQ_MP (@lem8234096 A B P p t f fixed) (@lem8234088 A B P p t fixed f)). Qed.
Lemma lem8234098 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234099 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term148 A B P p t fixed f a) = (term149 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234097 A B P p t f fixed) (@lem8234098 P a)). Qed.
Lemma lem8234101 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234102 {B P : Type'} (f : P -> B) (y : P) : (term150 B P f y) = (f y).
Proof. exact (@lem8234101 P B f y). Qed.
Lemma lem8234103 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term151 A B P p t f fixed a) = (term149 A B P p t f fixed a).
Proof. exact (@lem8234102 B P (term144 A B P p t f fixed) a). Qed.
Lemma lem8234104 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (eq_refl (term149 A B P p t f fixed a)). Qed.
Lemma lem8234105 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term153 A B P p t f fixed) = (term144 A B P p t f fixed).
Proof. exact (fun_ext (fun a : P => @lem8234104 A B P p t f a fixed)). Qed.
Lemma lem8234106 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234107 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term151 A B P p t f fixed a) = (term149 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234105 A B P p t f fixed) (@lem8234106 P a)). Qed.
Lemma lem8234108 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234109 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term154 A B P p t f fixed a) = (term155 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234108 B) (@lem8234107 A B P p t f fixed a)). Qed.
Lemma lem8234110 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (eq_refl (term149 A B P p t f fixed a)). Qed.
Lemma lem8234111 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((term151 A B P p t f fixed a) = (term149 A B P p t f fixed a)) = ((term149 A B P p t f fixed a) = (term152 A B P p t f a fixed)).
Proof. exact (MK_COMB (@lem8234109 A B P p t f fixed a) (@lem8234110 A B P p t f a fixed)). Qed.
Lemma lem8234112 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (EQ_MP (@lem8234111 A B P p t f a fixed) (@lem8234103 A B P p t f fixed a)). Qed.
Lemma lem8234113 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term148 A B P p t fixed f a) = (term152 A B P p t f a fixed).
Proof. exact (TRANS (@lem8234099 A B P p t f fixed a) (@lem8234112 A B P p t f a fixed)). Qed.
Lemma lem8234114 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234115 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term156 A B P p t fixed f a) = (term157 A B P p t f a fixed).
Proof. exact (MK_COMB (@lem8234114 B) (@lem8234113 A B P p t f a fixed)). Qed.
Lemma lem8234117 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234118 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term140 A B P f y) = (f y).
Proof. exact (@lem8234117 (A -> B) (P -> B) f y). Qed.
Lemma lem8234119 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (g : A -> B) : (term141 A B P p t fixed g) = (term142 A B P p t fixed g).
Proof. exact (@lem8234118 A B P (term143 A B P p t fixed) g). Qed.
Lemma lem8234120 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (eq_refl (term142 A B P p t fixed f)). Qed.
Lemma lem8234121 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term145 A B P p t fixed) = (term143 A B P p t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234120 A B P p t f fixed)). Qed.
Lemma lem8234122 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8234123 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (g : A -> B) : (term141 A B P p t fixed g) = (term142 A B P p t fixed g).
Proof. exact (MK_COMB (@lem8234121 A B P p t fixed) (@lem8234122 A B g)). Qed.
Lemma lem8234124 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8234125 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (g : A -> B) : (term146 A B P p t fixed g) = (term147 A B P p t fixed g).
Proof. exact (MK_COMB (@lem8234124 B P) (@lem8234123 A B P p t fixed g)). Qed.
Lemma lem8234126 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : (term142 A B P p t fixed g) = (term144 A B P p t g fixed).
Proof. exact (eq_refl (term142 A B P p t fixed g)). Qed.
Lemma lem8234127 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : ((term141 A B P p t fixed g) = (term142 A B P p t fixed g)) = ((term142 A B P p t fixed g) = (term144 A B P p t g fixed)).
Proof. exact (MK_COMB (@lem8234125 A B P p t fixed g) (@lem8234126 A B P p t g fixed)). Qed.
Lemma lem8234128 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : (term142 A B P p t fixed g) = (term144 A B P p t g fixed).
Proof. exact (EQ_MP (@lem8234127 A B P p t g fixed) (@lem8234119 A B P p t fixed g)). Qed.
Lemma lem8234129 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234130 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) (a : P) : (term148 A B P p t fixed g a) = (term149 A B P p t g fixed a).
Proof. exact (MK_COMB (@lem8234128 A B P p t g fixed) (@lem8234129 P a)). Qed.
Lemma lem8234132 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234133 {B P : Type'} (f : P -> B) (y : P) : (term150 B P f y) = (f y).
Proof. exact (@lem8234132 P B f y). Qed.
Lemma lem8234134 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) (a : P) : (term151 A B P p t g fixed a) = (term149 A B P p t g fixed a).
Proof. exact (@lem8234133 B P (term144 A B P p t g fixed) a). Qed.
Lemma lem8234135 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term149 A B P p t g fixed a) = (term152 A B P p t g a fixed).
Proof. exact (eq_refl (term149 A B P p t g fixed a)). Qed.
Lemma lem8234136 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : (term153 A B P p t g fixed) = (term144 A B P p t g fixed).
Proof. exact (fun_ext (fun a : P => @lem8234135 A B P p t g a fixed)). Qed.
Lemma lem8234137 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234138 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) (a : P) : (term151 A B P p t g fixed a) = (term149 A B P p t g fixed a).
Proof. exact (MK_COMB (@lem8234136 A B P p t g fixed) (@lem8234137 P a)). Qed.
Lemma lem8234139 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234140 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) (a : P) : (term154 A B P p t g fixed a) = (term155 A B P p t g fixed a).
Proof. exact (MK_COMB (@lem8234139 B) (@lem8234138 A B P p t g fixed a)). Qed.
Lemma lem8234141 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term149 A B P p t g fixed a) = (term152 A B P p t g a fixed).
Proof. exact (eq_refl (term149 A B P p t g fixed a)). Qed.
Lemma lem8234142 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : ((term151 A B P p t g fixed a) = (term149 A B P p t g fixed a)) = ((term149 A B P p t g fixed a) = (term152 A B P p t g a fixed)).
Proof. exact (MK_COMB (@lem8234140 A B P p t g fixed a) (@lem8234141 A B P p t g a fixed)). Qed.
Lemma lem8234143 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term149 A B P p t g fixed a) = (term152 A B P p t g a fixed).
Proof. exact (EQ_MP (@lem8234142 A B P p t g a fixed) (@lem8234134 A B P p t g fixed a)). Qed.
Lemma lem8234144 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term148 A B P p t fixed g a) = (term152 A B P p t g a fixed).
Proof. exact (TRANS (@lem8234130 A B P p t g fixed a) (@lem8234143 A B P p t g a fixed)). Qed.
Lemma lem8234145 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : ((term148 A B P p t fixed f a) = (term148 A B P p t fixed g a)) = ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)).
Proof. exact (MK_COMB (@lem8234115 A B P p t f a fixed) (@lem8234144 A B P p t g a fixed)). Qed.
Lemma lem8234148 {A B P : Type'} (anything : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term158 A B P anything f p t fixed g a) = (term159 A B P f p t g a fixed).
Proof. exact (MK_COMB (@lem8234082 A B P f anything g a) (@lem8234145 A B P f p t g a fixed)). Qed.
Lemma lem8234150 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8234151 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term159 A B P f p t g a fixed) = ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)).
Proof. exact (@lem8234150 ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed))). Qed.
Lemma lem8234154 {A B P : Type'} (anything : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term158 A B P anything f p t fixed g a) = ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)).
Proof. exact (TRANS (@lem8234148 A B P anything f p t g a fixed) (@lem8234151 A B P f p t g a fixed)). Qed.
Lemma lem8234155 {A B P : Type'} (anything : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term160 A B P anything f p t fixed g a) = (term159 A B P f p t g a fixed).
Proof. exact (MK_COMB (@lem8234038 A B P f g a) (@lem8234154 A B P anything f p t g a fixed)). Qed.
Lemma lem8234157 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8234158 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term159 A B P f p t g a fixed) = ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)).
Proof. exact (@lem8234157 ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed))). Qed.
Lemma lem8234161 {A B P : Type'} (anything : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term160 A B P anything f p t fixed g a) = ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)).
Proof. exact (TRANS (@lem8234155 A B P anything f p t g a fixed) (@lem8234158 A B P f p t g a fixed)). Qed.
Lemma lem8234162 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234163 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term161 A B P lt2 s anything f p t fixed g a) = (term162 A B P lt2 s f p t g a fixed).
Proof. exact (MK_COMB (@lem8234162 A B P lt2 s a f g) (@lem8234161 A B P anything f p t g a fixed)). Qed.
Lemma lem8234166 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : (term163 A B P lt2 s anything f p t fixed g) = (term164 A B P lt2 s f p t g fixed).
Proof. exact (fun_ext (fun a : P => @lem8234163 A B P anything lt2 s f p t g a fixed)). Qed.
Lemma lem8234167 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8234168 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (fixed : B) : (term165 A B P lt2 s anything f p t fixed g) = (term166 A B P lt2 s f p t g fixed).
Proof. exact (MK_COMB (@lem8234167 P) (@lem8234166 A B P anything lt2 s f p t g fixed)). Qed.
Lemma lem8234173 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term167 A B P lt2 s anything f p t fixed) = (term168 A B P lt2 s f p t fixed).
Proof. exact (fun_ext (fun g : A -> B => @lem8234168 A B P anything lt2 s f p t g fixed)). Qed.
Lemma lem8234174 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234175 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term169 A B P lt2 s anything f p t fixed) = (term170 A B P lt2 s f p t fixed).
Proof. exact (MK_COMB (@lem8234174 A B) (@lem8234173 A B P anything lt2 s f p t fixed)). Qed.
Lemma lem8234180 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term171 A B P lt2 s anything p t fixed) = (term172 A B P lt2 s p t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234175 A B P anything lt2 s f p t fixed)). Qed.
Lemma lem8234181 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234182 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term173 A B P lt2 s anything p t fixed) = (term174 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8234181 A B) (@lem8234180 A B P anything lt2 s p t fixed)). Qed.
Lemma lem8234187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234188 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term175 A B P lt2 s anything p t fixed) = (term176 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8234187) (@lem8234182 A B P anything lt2 s p t fixed)). Qed.
Lemma lem8234202 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234203 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term39 A B P f y) = (f y).
Proof. exact (@lem8234202 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8234204 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (@lem8234203 A B P (term96 A B P) f). Qed.
Lemma lem8234205 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8234206 {A B P : Type'} : (term98 A B P) = (term96 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8234205 A B P f)). Qed.
Lemma lem8234207 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234208 {A B P : Type'} (f : A -> B) : (term94 A B P f) = (term95 A B P f).
Proof. exact (MK_COMB (@lem8234206 A B P) (@lem8234207 A B f)). Qed.
Lemma lem8234209 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8234210 {A B P : Type'} (f : A -> B) : (term99 A B P f) = (term100 A B P f).
Proof. exact (MK_COMB (@lem8234209 P) (@lem8234208 A B P f)). Qed.
Lemma lem8234211 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (eq_refl (term95 A B P f)). Qed.
Lemma lem8234212 {A B P : Type'} (f : A -> B) : ((term94 A B P f) = (term95 A B P f)) = ((term95 A B P f) = (term97 P)).
Proof. exact (MK_COMB (@lem8234210 A B P f) (@lem8234211 A B P f)). Qed.
Lemma lem8234213 {A B P : Type'} (f : A -> B) : (term95 A B P f) = (term97 P).
Proof. exact (EQ_MP (@lem8234212 A B P f) (@lem8234204 A B P f)). Qed.
Lemma lem8234214 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234215 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = (term102 P a).
Proof. exact (MK_COMB (@lem8234213 A B P f) (@lem8234214 P a)). Qed.
Lemma lem8234217 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234218 {P : Type'} (f : P -> Prop) (y : P) : (term48 P f y) = (f y).
Proof. exact (@lem8234217 P Prop f y). Qed.
Lemma lem8234219 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (@lem8234218 P (term97 P) a). Qed.
Lemma lem8234220 {P : Type'} (x : P) : (term102 P x) = False.
Proof. exact (eq_refl (term102 P x)). Qed.
Lemma lem8234221 {P : Type'} : (term104 P) = (term97 P).
Proof. exact (fun_ext (fun x : P => @lem8234220 P x)). Qed.
Lemma lem8234222 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234223 {P : Type'} (a : P) : (term103 P a) = (term102 P a).
Proof. exact (MK_COMB (@lem8234221 P) (@lem8234222 P a)). Qed.
Lemma lem8234224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8234225 {P : Type'} (a : P) : (term105 P a) = (term106 P a).
Proof. exact (MK_COMB (@lem8234224) (@lem8234223 P a)). Qed.
Lemma lem8234226 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (eq_refl (term102 P a)). Qed.
Lemma lem8234227 {P : Type'} (a : P) : ((term103 P a) = (term102 P a)) = ((term102 P a) = False).
Proof. exact (MK_COMB (@lem8234225 P a) (@lem8234226 P a)). Qed.
Lemma lem8234228 {P : Type'} (a : P) : (term102 P a) = False.
Proof. exact (EQ_MP (@lem8234227 P a) (@lem8234219 P a)). Qed.
Lemma lem8234229 {A B P : Type'} (f : A -> B) (a : P) : (term101 A B P f a) = False.
Proof. exact (TRANS (@lem8234215 A B P f a) (@lem8234228 P a)). Qed.
Lemma lem8234230 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234231 {A B P : Type'} (f : A -> B) (a : P) : (term177 A B P f a) = (@COND B False).
Proof. exact (MK_COMB (@lem8234230 B) (@lem8234229 A B P f a)). Qed.
Lemma lem8234233 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234234 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term108 A B P f y) = (f y).
Proof. exact (@lem8234233 (A -> B) (P -> A) f y). Qed.
Lemma lem8234235 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (@lem8234234 A B P (term111 A B P anything) f). Qed.
Lemma lem8234236 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8234237 {A B P : Type'} (anything : P -> A) : (term112 A B P anything) = (term111 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8234236 A B P f anything)). Qed.
Lemma lem8234238 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234239 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term109 A B P anything f) = (term110 A B P anything f).
Proof. exact (MK_COMB (@lem8234237 A B P anything) (@lem8234238 A B f)). Qed.
Lemma lem8234240 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8234241 {A B P : Type'} (anything : P -> A) (f : A -> B) : (term113 A B P anything f) = (term114 A B P anything f).
Proof. exact (MK_COMB (@lem8234240 A P) (@lem8234239 A B P anything f)). Qed.
Lemma lem8234242 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (eq_refl (term110 A B P anything f)). Qed.
Lemma lem8234243 {A B P : Type'} (f : A -> B) (anything : P -> A) : ((term109 A B P anything f) = (term110 A B P anything f)) = ((term110 A B P anything f) = anything).
Proof. exact (MK_COMB (@lem8234241 A B P anything f) (@lem8234242 A B P f anything)). Qed.
Lemma lem8234244 {A B P : Type'} (f : A -> B) (anything : P -> A) : (term110 A B P anything f) = anything.
Proof. exact (EQ_MP (@lem8234243 A B P f anything) (@lem8234235 A B P anything f)). Qed.
Lemma lem8234245 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234246 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term115 A B P anything f a) = (anything a).
Proof. exact (MK_COMB (@lem8234244 A B P f anything) (@lem8234245 P a)). Qed.
Lemma lem8234247 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234248 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term178 A B P anything f a) = (term179 A B P f anything a).
Proof. exact (MK_COMB (@lem8234247 A B f) (@lem8234246 A B P f anything a)). Qed.
Lemma lem8234249 {A B P : Type'} (f : A -> B) (anything : P -> A) (a : P) : (term180 A B P anything f a) = (term181 A B P f anything a).
Proof. exact (MK_COMB (@lem8234231 A B P f a) (@lem8234248 A B P f anything a)). Qed.
Lemma lem8234251 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234252 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term140 A B P f y) = (f y).
Proof. exact (@lem8234251 (A -> B) (P -> B) f y). Qed.
Lemma lem8234253 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term141 A B P p t fixed f) = (term142 A B P p t fixed f).
Proof. exact (@lem8234252 A B P (term143 A B P p t fixed) f). Qed.
Lemma lem8234254 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (eq_refl (term142 A B P p t fixed f)). Qed.
Lemma lem8234255 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term145 A B P p t fixed) = (term143 A B P p t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234254 A B P p t f fixed)). Qed.
Lemma lem8234256 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8234257 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term141 A B P p t fixed f) = (term142 A B P p t fixed f).
Proof. exact (MK_COMB (@lem8234255 A B P p t fixed) (@lem8234256 A B f)). Qed.
Lemma lem8234258 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8234259 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (f : A -> B) : (term146 A B P p t fixed f) = (term147 A B P p t fixed f).
Proof. exact (MK_COMB (@lem8234258 B P) (@lem8234257 A B P p t fixed f)). Qed.
Lemma lem8234260 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (eq_refl (term142 A B P p t fixed f)). Qed.
Lemma lem8234261 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : ((term141 A B P p t fixed f) = (term142 A B P p t fixed f)) = ((term142 A B P p t fixed f) = (term144 A B P p t f fixed)).
Proof. exact (MK_COMB (@lem8234259 A B P p t fixed f) (@lem8234260 A B P p t f fixed)). Qed.
Lemma lem8234262 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term142 A B P p t fixed f) = (term144 A B P p t f fixed).
Proof. exact (EQ_MP (@lem8234261 A B P p t f fixed) (@lem8234253 A B P p t fixed f)). Qed.
Lemma lem8234263 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234264 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term148 A B P p t fixed f a) = (term149 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234262 A B P p t f fixed) (@lem8234263 P a)). Qed.
Lemma lem8234266 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8234267 {B P : Type'} (f : P -> B) (y : P) : (term150 B P f y) = (f y).
Proof. exact (@lem8234266 P B f y). Qed.
Lemma lem8234268 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term151 A B P p t f fixed a) = (term149 A B P p t f fixed a).
Proof. exact (@lem8234267 B P (term144 A B P p t f fixed) a). Qed.
Lemma lem8234269 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (eq_refl (term149 A B P p t f fixed a)). Qed.
Lemma lem8234270 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term153 A B P p t f fixed) = (term144 A B P p t f fixed).
Proof. exact (fun_ext (fun a : P => @lem8234269 A B P p t f a fixed)). Qed.
Lemma lem8234271 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8234272 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term151 A B P p t f fixed a) = (term149 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234270 A B P p t f fixed) (@lem8234271 P a)). Qed.
Lemma lem8234273 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234274 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) (a : P) : (term154 A B P p t f fixed a) = (term155 A B P p t f fixed a).
Proof. exact (MK_COMB (@lem8234273 B) (@lem8234272 A B P p t f fixed a)). Qed.
Lemma lem8234275 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (eq_refl (term149 A B P p t f fixed a)). Qed.
Lemma lem8234276 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((term151 A B P p t f fixed a) = (term149 A B P p t f fixed a)) = ((term149 A B P p t f fixed a) = (term152 A B P p t f a fixed)).
Proof. exact (MK_COMB (@lem8234274 A B P p t f fixed a) (@lem8234275 A B P p t f a fixed)). Qed.
Lemma lem8234277 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term149 A B P p t f fixed a) = (term152 A B P p t f a fixed).
Proof. exact (EQ_MP (@lem8234276 A B P p t f a fixed) (@lem8234268 A B P p t f fixed a)). Qed.
Lemma lem8234278 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term148 A B P p t fixed f a) = (term152 A B P p t f a fixed).
Proof. exact (TRANS (@lem8234264 A B P p t f fixed a) (@lem8234277 A B P p t f a fixed)). Qed.
Lemma lem8234279 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term182 A B P anything p t fixed f a) = (term183 A B P anything p t f a fixed).
Proof. exact (MK_COMB (@lem8234249 A B P f anything a) (@lem8234278 A B P p t f a fixed)). Qed.
Lemma lem8234281 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8234282 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem8234281 B t1 t2). Qed.
Lemma lem8234283 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term183 A B P anything p t f a fixed) = (term152 A B P p t f a fixed).
Proof. exact (@lem8234282 B (term179 A B P f anything a) (term152 A B P p t f a fixed)). Qed.
Lemma lem8234284 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term182 A B P anything p t fixed f a) = (term152 A B P p t f a fixed).
Proof. exact (TRANS (@lem8234279 A B P anything p t f a fixed) (@lem8234283 A B P anything p t f a fixed)). Qed.
Lemma lem8234285 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term184 A B P t f a).
Proof. exact (eq_refl (term184 A B P t f a)). Qed.
Lemma lem8234286 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((t f a) = (term182 A B P anything p t fixed f a)) = ((t f a) = (term152 A B P p t f a fixed)).
Proof. exact (MK_COMB (@lem8234285 A B P t f a) (@lem8234284 A B P anything p t f a fixed)). Qed.
Lemma lem8234289 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term185 A B P p f a) = (term185 A B P p f a).
Proof. exact (eq_refl (term185 A B P p f a)). Qed.
Lemma lem8234290 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term186 A B P anything p t fixed f a) = (term187 A B P p t f a fixed).
Proof. exact (MK_COMB (@lem8234289 A B P p f a) (@lem8234286 A B P anything p t f a fixed)). Qed.
Lemma lem8234293 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term188 A B P anything p t fixed f) = (term189 A B P p t f fixed).
Proof. exact (fun_ext (fun a : P => @lem8234290 A B P anything p t f a fixed)). Qed.
Lemma lem8234294 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8234295 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term190 A B P anything p t fixed f) = (term191 A B P p t f fixed).
Proof. exact (MK_COMB (@lem8234294 P) (@lem8234293 A B P anything p t f fixed)). Qed.
Lemma lem8234300 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term192 A B P anything p t fixed) = (term193 A B P p t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234295 A B P anything p t f fixed)). Qed.
Lemma lem8234301 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234302 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term194 A B P anything p t fixed) = (term195 A B P p t fixed).
Proof. exact (MK_COMB (@lem8234301 A B) (@lem8234300 A B P anything p t fixed)). Qed.
Lemma lem8234307 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term196 A B P lt2 s anything p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8234188 A B P anything lt2 s p t fixed) (@lem8234302 A B P anything p t fixed)). Qed.
Lemma lem8234310 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term198 A B P lt2 s anything p t fixed) = (term199 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8233940 A B P anything lt2 s) (@lem8234307 A B P anything lt2 s p t fixed)). Qed.
Lemma lem8234312 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8234313 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term199 A B P lt2 s p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (@lem8234312 (term197 A B P lt2 s p t fixed)). Qed.
Lemma lem8234352 {A B P : Type'} (anything : P -> A) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term198 A B P lt2 s anything p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (TRANS (@lem8234310 A B P anything lt2 s p t fixed) (@lem8234313 A B P lt2 s p t fixed)). Qed.
Lemma lem8234353 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (anything : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term197 A B P lt2 s p t fixed) = (term198 A B P lt2 s anything p t fixed).
Proof. exact (SYM (@lem8234352 A B P anything lt2 s p t fixed)). Qed.
Lemma lem8234355 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8234356 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term197 A B P lt2 s p t fixed) = (term201 A B P lt2 s p t fixed).
Proof. exact (@lem8234355 (term197 A B P lt2 s p t fixed)). Qed.
Lemma lem8234357 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term201 A B P lt2 s p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (SYM (@lem8234356 A B P lt2 s p t fixed)). Qed.
Lemma lem8234358 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term202 A B P lt2 s p t fixed) : term202 A B P lt2 s p t fixed.
Proof. exact (h1). Qed.
Lemma lem8234361 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term203 A B P lt2 s p t fixed) : term203 A B P lt2 s p t fixed.
Proof. exact (h1). Qed.
Lemma lem8234362 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term204 A B P lt2 s p t fixed.
Proof. exact (fun h0 : term203 A B P lt2 s p t fixed => @lem8234361 A B P lt2 s p t fixed h0). Qed.
Lemma lem8234363 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term204 A B P lt2 s p t fixed) : term204 A B P lt2 s p t fixed.
Proof. exact (h1). Qed.
Lemma lem8234364 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term203 A B P lt2 s p t fixed) : term203 A B P lt2 s p t fixed.
Proof. exact (h1). Qed.
Lemma lem8234365 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term203 A B P lt2 s p t fixed) (h2 : term204 A B P lt2 s p t fixed) : term203 A B P lt2 s p t fixed.
Proof. exact (@lem8234363 A B P lt2 s p t fixed h2 (@lem8234364 A B P lt2 s p t fixed h1)). Qed.
Lemma lem8234366 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term203 A B P lt2 s p t fixed) : term205 A B P lt2 s p t fixed.
Proof. exact (fun h0 : term204 A B P lt2 s p t fixed => @lem8234365 A B P lt2 s p t fixed h1 h0). Qed.
Lemma lem8234367 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term204 A B P lt2 s p t fixed) : term204 A B P lt2 s p t fixed.
Proof. exact (h1). Qed.
Lemma lem8234368 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term203 A B P lt2 s p t fixed) (h2 : term204 A B P lt2 s p t fixed) : term203 A B P lt2 s p t fixed.
Proof. exact (@lem8234366 A B P lt2 s p t fixed h1 (@lem8234367 A B P lt2 s p t fixed h2)). Qed.
Lemma lem8234369 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term204 A B P lt2 s p t fixed) : term204 A B P lt2 s p t fixed.
Proof. exact (fun h0 : term203 A B P lt2 s p t fixed => @lem8234368 A B P lt2 s p t fixed h0 h1). Qed.
Lemma lem8234370 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term206 A B P lt2 s p t fixed.
Proof. exact (fun h0 : term204 A B P lt2 s p t fixed => @lem8234369 A B P lt2 s p t fixed h0). Qed.
Lemma lem8234373 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term204 A B P lt2 s p t fixed.
Proof. exact (@lem8234370 A B P lt2 s p t fixed (@lem8234362 A B P lt2 s p t fixed)). Qed.
Lemma lem8234374 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term204 A B P lt2 s p t fixed.
Proof. exact (@lem8234373 A B P lt2 s p t fixed). Qed.
Lemma lem8234444 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8234445 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term201 A B P lt2 s p t fixed) = (term207 A B P lt2 s p t fixed).
Proof. exact (@lem8234444 (term202 A B P lt2 s p t fixed)). Qed.
Lemma lem8234447 (t : Prop) : (term208 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8234448 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term207 A B P lt2 s p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (@lem8234447 (term197 A B P lt2 s p t fixed)). Qed.
Lemma lem8234451 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term201 A B P lt2 s p t fixed) = (term197 A B P lt2 s p t fixed).
Proof. exact (TRANS (@lem8234445 A B P lt2 s p t fixed) (@lem8234448 A B P lt2 s p t fixed)). Qed.
Lemma lem8234482 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term74 A B P lt2 s p) = (term74 A B P lt2 s p).
Proof. exact (eq_refl (term74 A B P lt2 s p)). Qed.
Lemma lem8234483 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term209 A B P lt2 s p t fixed) = (term210 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8234482 A B P lt2 s p) (@lem8234451 A B P lt2 s p t fixed)). Qed.
Lemma lem8234486 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term33 A B P p lt2 s t) = (term33 A B P p lt2 s t).
Proof. exact (eq_refl (term33 A B P p lt2 s t)). Qed.
Lemma lem8234487 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term203 A B P lt2 s p t fixed) = (term211 A B P lt2 s p t fixed).
Proof. exact (MK_COMB (@lem8234486 A B P p lt2 s t) (@lem8234483 A B P lt2 s p t fixed)). Qed.
Lemma lem8234490 {A B P : Type'} (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term212 A B P s p t fixed) = (term213 A B P s p t fixed).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8234487 A B P lt2 s p t fixed)). Qed.
Lemma lem8234491 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8234492 {A B P : Type'} (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term214 A B P s p t fixed) = (term215 A B P s p t fixed).
Proof. exact (MK_COMB (@lem8234491 A) (@lem8234490 A B P s p t fixed)). Qed.
Lemma lem8234497 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term216 A B P p t fixed) = (term217 A B P p t fixed).
Proof. exact (fun_ext (fun s : P -> A => @lem8234492 A B P s p t fixed)). Qed.
Lemma lem8234498 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8234499 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term218 A B P p t fixed) = (term219 A B P p t fixed).
Proof. exact (MK_COMB (@lem8234498 A P) (@lem8234497 A B P p t fixed)). Qed.
Lemma lem8234504 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term220 A B P t fixed) = (term221 A B P t fixed).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8234499 A B P p t fixed)). Qed.
Lemma lem8234505 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8234506 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term222 A B P t fixed) = (term223 A B P t fixed).
Proof. exact (MK_COMB (@lem8234505 A B P) (@lem8234504 A B P t fixed)). Qed.
Lemma lem8234511 {A B P : Type'} (fixed : B) : (term224 A B P fixed) = (term225 A B P fixed).
Proof. exact (fun_ext (fun t : type558 A B P => @lem8234506 A B P t fixed)). Qed.
Lemma lem8234512 {A B P : Type'} : (@all ((A -> B) -> P -> B)) = (@all ((A -> B) -> P -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> B))). Qed.
Lemma lem8234513 {A B P : Type'} (fixed : B) : (term226 A B P fixed) = (term227 A B P fixed).
Proof. exact (MK_COMB (@lem8234512 A B P) (@lem8234511 A B P fixed)). Qed.
Lemma lem8234518 {A B P : Type'} : (term228 A B P) = (term229 A B P).
Proof. exact (fun_ext (fun fixed : B => @lem8234513 A B P fixed)). Qed.
Lemma lem8234519 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8234528 {A B P : Type'} : (term230 A B P) = (term231 A B P).
Proof. exact (MK_COMB (@lem8234519 B) (@lem8234518 A B P)). Qed.
Lemma lem8234532 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8234533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234534 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term185 A B P p f a) = (imp False).
Proof. exact (MK_COMB (@lem8234533) (@lem8234532 A B P p f a h1)). Qed.
Lemma lem8234536 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8234537 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234538 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term232 A B P p f a) = (@COND B False).
Proof. exact (MK_COMB (@lem8234537 B) (@lem8234536 A B P p f a h1)). Qed.
Lemma lem8234539 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8234540 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term233 A B P p t f a) = (term234 A B P t f a).
Proof. exact (MK_COMB (@lem8234538 A B P p f a h1) (@lem8234539 A B P t f a)). Qed.
Lemma lem8234541 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234542 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term152 A B P p t f a fixed) = (term235 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8234540 A B P t p f a h1) (@lem8234541 B fixed)). Qed.
Lemma lem8234544 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8234545 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem8234544 B t1 t2). Qed.
Lemma lem8234546 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term235 A B P t f a fixed) = fixed.
Proof. exact (@lem8234545 B (t f a) fixed). Qed.
Lemma lem8234547 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term152 A B P p t f a fixed) = fixed.
Proof. exact (TRANS (@lem8234542 A B P t fixed p f a h1) (@lem8234546 A B P t f a fixed)). Qed.
Lemma lem8234548 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term184 A B P t f a).
Proof. exact (eq_refl (term184 A B P t f a)). Qed.
Lemma lem8234549 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : ((t f a) = (term152 A B P p t f a fixed)) = ((t f a) = fixed).
Proof. exact (MK_COMB (@lem8234548 A B P t f a) (@lem8234547 A B P t fixed p f a h1)). Qed.
Lemma lem8234552 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term187 A B P p t f a fixed) = (term236 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8234534 A B P p f a h1) (@lem8234549 A B P t fixed p f a h1)). Qed.
Lemma lem8234554 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8234555 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term236 A B P t f a fixed) = True.
Proof. exact (@lem8234554 ((t f a) = fixed)). Qed.
Lemma lem8234556 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term187 A B P p t f a fixed) = True.
Proof. exact (TRANS (@lem8234552 A B P t fixed p f a h1) (@lem8234555 A B P t f a fixed)). Qed.
Lemma lem8234557 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : term237 A B P p t f a fixed.
Proof. exact (fun h0 : (p f a) = False => @lem8234556 A B P t fixed p f a h0). Qed.
Lemma lem8234559 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8234560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234561 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term185 A B P p f a) = (imp True).
Proof. exact (MK_COMB (@lem8234560) (@lem8234559 A B P p f a h1)). Qed.
Lemma lem8234563 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8234564 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234565 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term232 A B P p f a) = (@COND B True).
Proof. exact (MK_COMB (@lem8234564 B) (@lem8234563 A B P p f a h1)). Qed.
Lemma lem8234566 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8234567 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term233 A B P p t f a) = (term238 A B P t f a).
Proof. exact (MK_COMB (@lem8234565 A B P p f a h1) (@lem8234566 A B P t f a)). Qed.
Lemma lem8234568 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234569 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term152 A B P p t f a fixed) = (term239 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8234567 A B P t p f a h1) (@lem8234568 B fixed)). Qed.
Lemma lem8234571 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8234572 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem8234571 B t2 t1). Qed.
Lemma lem8234573 {A B P : Type'} (fixed : B) (t : type558 A B P) (f : A -> B) (a : P) : (term239 A B P t f a fixed) = (t f a).
Proof. exact (@lem8234572 B fixed (t f a)). Qed.
Lemma lem8234574 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term152 A B P p t f a fixed) = (t f a).
Proof. exact (TRANS (@lem8234569 A B P t fixed p f a h1) (@lem8234573 A B P fixed t f a)). Qed.
Lemma lem8234575 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term184 A B P t f a).
Proof. exact (eq_refl (term184 A B P t f a)). Qed.
Lemma lem8234576 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((t f a) = (term152 A B P p t f a fixed)) = ((t f a) = (t f a)).
Proof. exact (MK_COMB (@lem8234575 A B P t f a) (@lem8234574 A B P fixed t p f a h1)). Qed.
Lemma lem8234578 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8234579 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem8234578 B x). Qed.
Lemma lem8234580 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : ((t f a) = (t f a)) = True.
Proof. exact (@lem8234579 B (t f a)). Qed.
Lemma lem8234581 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((t f a) = (term152 A B P p t f a fixed)) = True.
Proof. exact (TRANS (@lem8234576 A B P fixed t p f a h1) (@lem8234580 A B P t f a)). Qed.
Lemma lem8234582 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term187 A B P p t f a fixed) = (True -> True).
Proof. exact (MK_COMB (@lem8234561 A B P p f a h1) (@lem8234581 A B P t fixed p f a h1)). Qed.
Lemma lem8234584 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8234585 : (True -> True) = True.
Proof. exact (@lem8234584 True). Qed.
Lemma lem8234586 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term187 A B P p t f a fixed) = True.
Proof. exact (TRANS (@lem8234582 A B P t fixed p f a h1) (@lem8234585)). Qed.
Lemma lem8234587 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : term240 A B P p t f a fixed.
Proof. exact (fun h0 : (p f a) = True => @lem8234586 A B P t fixed p f a h0). Qed.
Lemma lem8234588 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : term241 A B P p t f a fixed.
Proof. exact (conj (@lem8234557 A B P p t f a fixed) (@lem8234587 A B P p t f a fixed)). Qed.
Lemma lem8234590 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term242 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8234591 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) : term243 A B P t fixed p f a.
Proof. exact (@lem8234590 (term187 A B P p t f a fixed) True (p f a) True). Qed.
Lemma lem8234592 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) : (term187 A B P p t f a fixed) = (term244 A B P p f a).
Proof. exact (@lem8234591 A B P t fixed p f a (@lem8234588 A B P p t f a fixed)). Qed.
Lemma lem8234594 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8234595 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term245 A B P p f a) = True.
Proof. exact (@lem8234594 (p f a)). Qed.
Lemma lem8234597 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8234598 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term246 A B P p f a) = True.
Proof. exact (@lem8234597 (term247 A B P p f a)). Qed.
Lemma lem8234599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234600 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term248 A B P p f a) = (and True).
Proof. exact (MK_COMB (@lem8234599) (@lem8234598 A B P p f a)). Qed.
Lemma lem8234601 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term244 A B P p f a) = (True /\ True).
Proof. exact (MK_COMB (@lem8234600 A B P p f a) (@lem8234595 A B P p f a)). Qed.
Lemma lem8234603 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8234604 : (True /\ True) = True.
Proof. exact (@lem8234603 True). Qed.
Lemma lem8234605 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term244 A B P p f a) = True.
Proof. exact (TRANS (@lem8234601 A B P p f a) (@lem8234604)). Qed.
Lemma lem8234610 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term187 A B P p t f a fixed) = True.
Proof. exact (TRANS (@lem8234592 A B P t fixed p f a) (@lem8234605 A B P p f a)). Qed.
Lemma lem8234611 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term189 A B P p t f fixed) = (term42 P).
Proof. exact (fun_ext (fun a : P => @lem8234610 A B P p t f a fixed)). Qed.
Lemma lem8234612 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8234613 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (f : A -> B) (fixed : B) : (term191 A B P p t f fixed) = (term125 P).
Proof. exact (MK_COMB (@lem8234612 P) (@lem8234611 A B P p t f fixed)). Qed.
Lemma lem8234614 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term193 A B P p t fixed) = (term249 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8234613 A B P p t f fixed)). Qed.
Lemma lem8234615 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234616 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term195 A B P p t fixed) = (term250 A B P).
Proof. exact (MK_COMB (@lem8234615 A B) (@lem8234614 A B P p t fixed)). Qed.
Lemma lem8234628 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8234629 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234630 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term232 A B P p f a) = (@COND B False).
Proof. exact (MK_COMB (@lem8234629 B) (@lem8234628 A B P p f a h1)). Qed.
Lemma lem8234631 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8234632 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term233 A B P p t f a) = (term234 A B P t f a).
Proof. exact (MK_COMB (@lem8234630 A B P p f a h1) (@lem8234631 A B P t f a)). Qed.
Lemma lem8234633 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234634 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term152 A B P p t f a fixed) = (term235 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8234632 A B P t p f a h1) (@lem8234633 B fixed)). Qed.
Lemma lem8234636 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8234637 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem8234636 B t1 t2). Qed.
Lemma lem8234638 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term235 A B P t f a fixed) = fixed.
Proof. exact (@lem8234637 B (t f a) fixed). Qed.
Lemma lem8234639 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term152 A B P p t f a fixed) = fixed.
Proof. exact (TRANS (@lem8234634 A B P t fixed p f a h1) (@lem8234638 A B P t f a fixed)). Qed.
Lemma lem8234640 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234641 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term157 A B P p t f a fixed) = (@eq B fixed).
Proof. exact (MK_COMB (@lem8234640 B) (@lem8234639 A B P t fixed p f a h1)). Qed.
Lemma lem8234642 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term152 A B P p t g a fixed) = (term152 A B P p t g a fixed).
Proof. exact (eq_refl (term152 A B P p t g a fixed)). Qed.
Lemma lem8234643 {A B P : Type'} (t : type558 A B P) (g : A -> B) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)) = (fixed = (term152 A B P p t g a fixed)).
Proof. exact (MK_COMB (@lem8234641 A B P t fixed p f a h1) (@lem8234642 A B P p t g a fixed)). Qed.
Lemma lem8234646 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234647 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (g : A -> B) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term162 A B P lt2 s f p t g a fixed) = (term251 A B P lt2 s f p t g a fixed).
Proof. exact (MK_COMB (@lem8234646 A B P lt2 s a f g) (@lem8234643 A B P t g fixed p f a h1)). Qed.
Lemma lem8234650 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : term252 A B P lt2 s f p t g a fixed.
Proof. exact (fun h0 : (p f a) = False => @lem8234647 A B P lt2 s t g fixed p f a h0). Qed.
Lemma lem8234660 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8234661 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234662 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term232 A B P p f a) = (@COND B True).
Proof. exact (MK_COMB (@lem8234661 B) (@lem8234660 A B P p f a h1)). Qed.
Lemma lem8234663 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8234664 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term233 A B P p t f a) = (term238 A B P t f a).
Proof. exact (MK_COMB (@lem8234662 A B P p f a h1) (@lem8234663 A B P t f a)). Qed.
Lemma lem8234665 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234666 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term152 A B P p t f a fixed) = (term239 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8234664 A B P t p f a h1) (@lem8234665 B fixed)). Qed.
Lemma lem8234668 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8234669 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem8234668 B t2 t1). Qed.
Lemma lem8234670 {A B P : Type'} (fixed : B) (t : type558 A B P) (f : A -> B) (a : P) : (term239 A B P t f a fixed) = (t f a).
Proof. exact (@lem8234669 B fixed (t f a)). Qed.
Lemma lem8234671 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term152 A B P p t f a fixed) = (t f a).
Proof. exact (TRANS (@lem8234666 A B P t fixed p f a h1) (@lem8234670 A B P fixed t f a)). Qed.
Lemma lem8234672 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8234673 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term157 A B P p t f a fixed) = (term184 A B P t f a).
Proof. exact (MK_COMB (@lem8234672 B) (@lem8234671 A B P fixed t p f a h1)). Qed.
Lemma lem8234674 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term152 A B P p t g a fixed) = (term152 A B P p t g a fixed).
Proof. exact (eq_refl (term152 A B P p t g a fixed)). Qed.
Lemma lem8234675 {A B P : Type'} (t : type558 A B P) (g : A -> B) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((term152 A B P p t f a fixed) = (term152 A B P p t g a fixed)) = ((t f a) = (term152 A B P p t g a fixed)).
Proof. exact (MK_COMB (@lem8234673 A B P fixed t p f a h1) (@lem8234674 A B P p t g a fixed)). Qed.
Lemma lem8234678 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234679 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (g : A -> B) (fixed : B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term162 A B P lt2 s f p t g a fixed) = (term253 A B P lt2 s f p t g a fixed).
Proof. exact (MK_COMB (@lem8234678 A B P lt2 s a f g) (@lem8234675 A B P t g fixed p f a h1)). Qed.
Lemma lem8234682 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : term254 A B P lt2 s f p t g a fixed.
Proof. exact (fun h0 : (p f a) = True => @lem8234679 A B P lt2 s t g fixed p f a h0). Qed.
Lemma lem8234683 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : term255 A B P lt2 s f p t g a fixed.
Proof. exact (conj (@lem8234650 A B P lt2 s f p t g a fixed) (@lem8234682 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234685 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term242 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8234686 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : term256 A B P lt2 s f p t g a fixed.
Proof. exact (@lem8234685 (term162 A B P lt2 s f p t g a fixed) (term253 A B P lt2 s f p t g a fixed) (p f a) (term251 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234701 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term162 A B P lt2 s f p t g a fixed) = (term257 A B P lt2 s f p t g a fixed).
Proof. exact (@lem8234686 A B P lt2 s f p t g a fixed (@lem8234683 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234713 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (p g a) = False.
Proof. exact (h1). Qed.
Lemma lem8234714 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234715 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term232 A B P p g a) = (@COND B False).
Proof. exact (MK_COMB (@lem8234714 B) (@lem8234713 A B P p g a h1)). Qed.
Lemma lem8234716 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8234717 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term233 A B P p t g a) = (term234 A B P t g a).
Proof. exact (MK_COMB (@lem8234715 A B P p g a h1) (@lem8234716 A B P t g a)). Qed.
Lemma lem8234718 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234719 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term152 A B P p t g a fixed) = (term235 A B P t g a fixed).
Proof. exact (MK_COMB (@lem8234717 A B P t p g a h1) (@lem8234718 B fixed)). Qed.
Lemma lem8234721 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8234722 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem8234721 B t1 t2). Qed.
Lemma lem8234723 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term235 A B P t g a fixed) = fixed.
Proof. exact (@lem8234722 B (t g a) fixed). Qed.
Lemma lem8234724 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term152 A B P p t g a fixed) = fixed.
Proof. exact (TRANS (@lem8234719 A B P t fixed p g a h1) (@lem8234723 A B P t g a fixed)). Qed.
Lemma lem8234725 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term184 A B P t f a).
Proof. exact (eq_refl (term184 A B P t f a)). Qed.
Lemma lem8234726 {A B P : Type'} (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : ((t f a) = (term152 A B P p t g a fixed)) = ((t f a) = fixed).
Proof. exact (MK_COMB (@lem8234725 A B P t f a) (@lem8234724 A B P t fixed p g a h1)). Qed.
Lemma lem8234729 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234730 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term253 A B P lt2 s f p t g a fixed) = (term258 A B P lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234729 A B P lt2 s a f g) (@lem8234726 A B P t f fixed p g a h1)). Qed.
Lemma lem8234733 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8234734 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term260 A B P lt2 s f p t g a fixed) = (term261 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234733 A B P p f a) (@lem8234730 A B P lt2 s t f fixed p g a h1)). Qed.
Lemma lem8234737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234738 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term262 A B P lt2 s f p t g a fixed) = (term263 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234737) (@lem8234734 A B P lt2 s t f fixed p g a h1)). Qed.
Lemma lem8234748 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (p g a) = False.
Proof. exact (h1). Qed.
Lemma lem8234749 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234750 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term232 A B P p g a) = (@COND B False).
Proof. exact (MK_COMB (@lem8234749 B) (@lem8234748 A B P p g a h1)). Qed.
Lemma lem8234751 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8234752 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term233 A B P p t g a) = (term234 A B P t g a).
Proof. exact (MK_COMB (@lem8234750 A B P p g a h1) (@lem8234751 A B P t g a)). Qed.
Lemma lem8234753 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234754 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term152 A B P p t g a fixed) = (term235 A B P t g a fixed).
Proof. exact (MK_COMB (@lem8234752 A B P t p g a h1) (@lem8234753 B fixed)). Qed.
Lemma lem8234756 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8234757 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem8234756 B t1 t2). Qed.
Lemma lem8234758 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term235 A B P t g a fixed) = fixed.
Proof. exact (@lem8234757 B (t g a) fixed). Qed.
Lemma lem8234759 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term152 A B P p t g a fixed) = fixed.
Proof. exact (TRANS (@lem8234754 A B P t fixed p g a h1) (@lem8234758 A B P t g a fixed)). Qed.
Lemma lem8234760 {B : Type'} (fixed : B) : (@eq B fixed) = (@eq B fixed).
Proof. exact (eq_refl (@eq B fixed)). Qed.
Lemma lem8234761 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (fixed = (term152 A B P p t g a fixed)) = (fixed = fixed).
Proof. exact (MK_COMB (@lem8234760 B fixed) (@lem8234759 A B P t fixed p g a h1)). Qed.
Lemma lem8234763 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8234764 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem8234763 B x). Qed.
Lemma lem8234765 {B : Type'} (fixed : B) : (fixed = fixed) = True.
Proof. exact (@lem8234764 B fixed). Qed.
Lemma lem8234766 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (fixed = (term152 A B P p t g a fixed)) = True.
Proof. exact (TRANS (@lem8234761 A B P t fixed p g a h1) (@lem8234765 B fixed)). Qed.
Lemma lem8234767 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234768 {A B P : Type'} (t : type558 A B P) (fixed : B) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term251 A B P lt2 s f p t g a fixed) = (term264 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234767 A B P lt2 s a f g) (@lem8234766 A B P t fixed p g a h1)). Qed.
Lemma lem8234770 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8234771 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term264 A B P lt2 s a f g) = True.
Proof. exact (@lem8234770 (term54 A B P lt2 s a f g)). Qed.
Lemma lem8234772 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term251 A B P lt2 s f p t g a fixed) = True.
Proof. exact (TRANS (@lem8234768 A B P t fixed lt2 s f p g a h1) (@lem8234771 A B P lt2 s a f g)). Qed.
Lemma lem8234773 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term265 A B P p f a) = (term265 A B P p f a).
Proof. exact (eq_refl (term265 A B P p f a)). Qed.
Lemma lem8234774 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term266 A B P lt2 s f p t g a fixed) = (term245 A B P p f a).
Proof. exact (MK_COMB (@lem8234773 A B P p f a) (@lem8234772 A B P lt2 s f t fixed p g a h1)). Qed.
Lemma lem8234776 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8234777 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term245 A B P p f a) = True.
Proof. exact (@lem8234776 (p f a)). Qed.
Lemma lem8234778 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term266 A B P lt2 s f p t g a fixed) = True.
Proof. exact (TRANS (@lem8234774 A B P lt2 s t fixed f p g a h1) (@lem8234777 A B P p f a)). Qed.
Lemma lem8234779 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term257 A B P lt2 s f p t g a fixed) = (term267 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234738 A B P lt2 s t f fixed p g a h1) (@lem8234778 A B P lt2 s f t fixed p g a h1)). Qed.
Lemma lem8234781 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8234782 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term267 A B P p lt2 s g t f a fixed) = (term261 A B P p lt2 s g t f a fixed).
Proof. exact (@lem8234781 (term261 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234785 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term257 A B P lt2 s f p t g a fixed) = (term261 A B P p lt2 s g t f a fixed).
Proof. exact (TRANS (@lem8234779 A B P lt2 s t f fixed p g a h1) (@lem8234782 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234786 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : term268 A B P p lt2 s g t f a fixed.
Proof. exact (fun h0 : (p g a) = False => @lem8234785 A B P lt2 s t f fixed p g a h0). Qed.
Lemma lem8234796 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (p g a) = True.
Proof. exact (h1). Qed.
Lemma lem8234797 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234798 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term232 A B P p g a) = (@COND B True).
Proof. exact (MK_COMB (@lem8234797 B) (@lem8234796 A B P p g a h1)). Qed.
Lemma lem8234799 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8234800 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term233 A B P p t g a) = (term238 A B P t g a).
Proof. exact (MK_COMB (@lem8234798 A B P p g a h1) (@lem8234799 A B P t g a)). Qed.
Lemma lem8234801 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234802 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term152 A B P p t g a fixed) = (term239 A B P t g a fixed).
Proof. exact (MK_COMB (@lem8234800 A B P t p g a h1) (@lem8234801 B fixed)). Qed.
Lemma lem8234804 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8234805 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem8234804 B t2 t1). Qed.
Lemma lem8234806 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term239 A B P t g a fixed) = (t g a).
Proof. exact (@lem8234805 B fixed (t g a)). Qed.
Lemma lem8234807 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term152 A B P p t g a fixed) = (t g a).
Proof. exact (TRANS (@lem8234802 A B P t fixed p g a h1) (@lem8234806 A B P fixed t g a)). Qed.
Lemma lem8234808 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term184 A B P t f a).
Proof. exact (eq_refl (term184 A B P t f a)). Qed.
Lemma lem8234809 {A B P : Type'} (fixed : B) (f : A -> B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : ((t f a) = (term152 A B P p t g a fixed)) = ((t f a) = (t g a)).
Proof. exact (MK_COMB (@lem8234808 A B P t f a) (@lem8234807 A B P fixed t p g a h1)). Qed.
Lemma lem8234812 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234813 {A B P : Type'} (fixed : B) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term253 A B P lt2 s f p t g a fixed) = (term269 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234812 A B P lt2 s a f g) (@lem8234809 A B P fixed f t p g a h1)). Qed.
Lemma lem8234816 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8234817 {A B P : Type'} (fixed : B) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term260 A B P lt2 s f p t g a fixed) = (term270 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234816 A B P p f a) (@lem8234813 A B P fixed lt2 s f t p g a h1)). Qed.
Lemma lem8234820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234821 {A B P : Type'} (fixed : B) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term262 A B P lt2 s f p t g a fixed) = (term271 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234820) (@lem8234817 A B P fixed lt2 s f t p g a h1)). Qed.
Lemma lem8234831 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (p g a) = True.
Proof. exact (h1). Qed.
Lemma lem8234832 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8234833 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term232 A B P p g a) = (@COND B True).
Proof. exact (MK_COMB (@lem8234832 B) (@lem8234831 A B P p g a h1)). Qed.
Lemma lem8234834 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8234835 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term233 A B P p t g a) = (term238 A B P t g a).
Proof. exact (MK_COMB (@lem8234833 A B P p g a h1) (@lem8234834 A B P t g a)). Qed.
Lemma lem8234836 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8234837 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term152 A B P p t g a fixed) = (term239 A B P t g a fixed).
Proof. exact (MK_COMB (@lem8234835 A B P t p g a h1) (@lem8234836 B fixed)). Qed.
Lemma lem8234839 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8234840 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem8234839 B t2 t1). Qed.
Lemma lem8234841 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term239 A B P t g a fixed) = (t g a).
Proof. exact (@lem8234840 B fixed (t g a)). Qed.
Lemma lem8234842 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term152 A B P p t g a fixed) = (t g a).
Proof. exact (TRANS (@lem8234837 A B P t fixed p g a h1) (@lem8234841 A B P fixed t g a)). Qed.
Lemma lem8234843 {B : Type'} (fixed : B) : (@eq B fixed) = (@eq B fixed).
Proof. exact (eq_refl (@eq B fixed)). Qed.
Lemma lem8234844 {A B P : Type'} (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (fixed = (term152 A B P p t g a fixed)) = (fixed = (t g a)).
Proof. exact (MK_COMB (@lem8234843 B fixed) (@lem8234842 A B P fixed t p g a h1)). Qed.
Lemma lem8234847 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (eq_refl (term59 A B P lt2 s a f g)). Qed.
Lemma lem8234848 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term251 A B P lt2 s f p t g a fixed) = (term272 A B P lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234847 A B P lt2 s a f g) (@lem8234844 A B P fixed t p g a h1)). Qed.
Lemma lem8234851 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term265 A B P p f a) = (term265 A B P p f a).
Proof. exact (eq_refl (term265 A B P p f a)). Qed.
Lemma lem8234852 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term266 A B P lt2 s f p t g a fixed) = (term273 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234851 A B P p f a) (@lem8234848 A B P lt2 s f fixed t p g a h1)). Qed.
Lemma lem8234855 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term257 A B P lt2 s f p t g a fixed) = (term274 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234821 A B P fixed lt2 s f t p g a h1) (@lem8234852 A B P lt2 s f fixed t p g a h1)). Qed.
Lemma lem8234858 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : term275 A B P p lt2 s f fixed t g a.
Proof. exact (fun h0 : (p g a) = True => @lem8234855 A B P lt2 s f fixed t p g a h0). Qed.
Lemma lem8234859 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : term276 A B P p lt2 s f fixed t g a.
Proof. exact (conj (@lem8234786 A B P p lt2 s g t f a fixed) (@lem8234858 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8234861 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term242 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8234862 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : term277 A B P p lt2 s g t f a fixed.
Proof. exact (@lem8234861 (term257 A B P lt2 s f p t g a fixed) (term274 A B P p lt2 s f fixed t g a) (p g a) (term261 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234877 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term257 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed).
Proof. exact (@lem8234862 A B P p lt2 s g t f a fixed (@lem8234859 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8234878 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((t f a) = fixed) = ((t f a) = fixed).
Proof. exact (eq_refl ((t f a) = fixed)). Qed.
Lemma lem8234883 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term279 A B P lt2 s a f g z)). Qed.
Lemma lem8234884 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term280 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8234883 A B P lt2 s a f g z)). Qed.
Lemma lem8234885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8234886 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234885 A) (@lem8234884 A B P lt2 s a f g)). Qed.
Lemma lem8234887 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234888 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234887) (@lem8234886 A B P lt2 s a f g)). Qed.
Lemma lem8234889 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term258 A B P lt2 s g t f a fixed) = (term258 A B P lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234888 A B P lt2 s a f g) (@lem8234878 A B P t f a fixed)). Qed.
Lemma lem8234894 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8234895 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term261 A B P p lt2 s g t f a fixed) = (term261 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234894 A B P p f a) (@lem8234889 A B P lt2 s g t f a fixed)). Qed.
Lemma lem8234898 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term265 A B P p g a) = (term265 A B P p g a).
Proof. exact (eq_refl (term265 A B P p g a)). Qed.
Lemma lem8234899 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term281 A B P p lt2 s g t f a fixed) = (term281 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234898 A B P p g a) (@lem8234895 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234900 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (fixed = (t g a)) = (fixed = (t g a)).
Proof. exact (eq_refl (fixed = (t g a))). Qed.
Lemma lem8234905 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term279 A B P lt2 s a f g z)). Qed.
Lemma lem8234906 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term280 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8234905 A B P lt2 s a f g z)). Qed.
Lemma lem8234907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8234908 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234907 A) (@lem8234906 A B P lt2 s a f g)). Qed.
Lemma lem8234909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234910 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234909) (@lem8234908 A B P lt2 s a f g)). Qed.
Lemma lem8234911 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term272 A B P lt2 s f fixed t g a) = (term272 A B P lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234910 A B P lt2 s a f g) (@lem8234900 A B P fixed t g a)). Qed.
Lemma lem8234914 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term265 A B P p f a) = (term265 A B P p f a).
Proof. exact (eq_refl (term265 A B P p f a)). Qed.
Lemma lem8234915 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term273 A B P p lt2 s f fixed t g a) = (term273 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234914 A B P p f a) (@lem8234911 A B P lt2 s f fixed t g a)). Qed.
Lemma lem8234916 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8234921 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term279 A B P lt2 s a f g z)). Qed.
Lemma lem8234922 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term280 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8234921 A B P lt2 s a f g z)). Qed.
Lemma lem8234923 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8234924 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234923 A) (@lem8234922 A B P lt2 s a f g)). Qed.
Lemma lem8234925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234926 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234925) (@lem8234924 A B P lt2 s a f g)). Qed.
Lemma lem8234927 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term269 A B P lt2 s f t g a) = (term269 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234926 A B P lt2 s a f g) (@lem8234916 A B P f t g a)). Qed.
Lemma lem8234932 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8234933 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term270 A B P p lt2 s f t g a) = (term270 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234932 A B P p f a) (@lem8234927 A B P lt2 s f t g a)). Qed.
Lemma lem8234934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234935 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term271 A B P p lt2 s f t g a) = (term271 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8234934) (@lem8234933 A B P p lt2 s f t g a)). Qed.
Lemma lem8234936 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term274 A B P p lt2 s f fixed t g a) = (term274 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234935 A B P p lt2 s f t g a) (@lem8234915 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8234941 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term259 A B P p g a) = (term259 A B P p g a).
Proof. exact (eq_refl (term259 A B P p g a)). Qed.
Lemma lem8234942 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term282 A B P p lt2 s f fixed t g a) = (term282 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234941 A B P p g a) (@lem8234936 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8234943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234944 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term283 A B P p lt2 s f fixed t g a) = (term283 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8234943) (@lem8234942 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8234945 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term278 A B P p lt2 s g t f a fixed) = (term278 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8234944 A B P p lt2 s f fixed t g a) (@lem8234899 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234946 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term284 A B P lt2 s f p t g a fixed) = (term284 A B P lt2 s f p t g a fixed).
Proof. exact (eq_refl (term284 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234947 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((term257 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed)) = ((term257 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed)).
Proof. exact (MK_COMB (@lem8234946 A B P lt2 s f p t g a fixed) (@lem8234945 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234948 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term257 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed).
Proof. exact (EQ_MP (@lem8234947 A B P p lt2 s g t f a fixed) (@lem8234877 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234949 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (t : type558 A B P) (g : A -> B) (a : P) (fixed : B) : (term285 A B P lt2 s f p t g a fixed) = (term285 A B P lt2 s f p t g a fixed).
Proof. exact (eq_refl (term285 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234950 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((term162 A B P lt2 s f p t g a fixed) = (term257 A B P lt2 s f p t g a fixed)) = ((term162 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed)).
Proof. exact (MK_COMB (@lem8234949 A B P lt2 s f p t g a fixed) (@lem8234948 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234951 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term162 A B P lt2 s f p t g a fixed) = (term278 A B P p lt2 s g t f a fixed).
Proof. exact (EQ_MP (@lem8234950 A B P p lt2 s g t f a fixed) (@lem8234701 A B P lt2 s f p t g a fixed)). Qed.
Lemma lem8234952 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (fixed : B) : (term164 A B P lt2 s f p t g fixed) = (term286 A B P p lt2 s g t f fixed).
Proof. exact (fun_ext (fun a : P => @lem8234951 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8234953 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8234954 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (fixed : B) : (term166 A B P lt2 s f p t g fixed) = (term287 A B P p lt2 s g t f fixed).
Proof. exact (MK_COMB (@lem8234953 P) (@lem8234952 A B P p lt2 s g t f fixed)). Qed.
Lemma lem8234955 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) : (term168 A B P lt2 s f p t fixed) = (term288 A B P p lt2 s t f fixed).
Proof. exact (fun_ext (fun g : A -> B => @lem8234954 A B P p lt2 s g t f fixed)). Qed.
Lemma lem8234956 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234957 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (f : A -> B) (fixed : B) : (term170 A B P lt2 s f p t fixed) = (term289 A B P p lt2 s t f fixed).
Proof. exact (MK_COMB (@lem8234956 A B) (@lem8234955 A B P p lt2 s t f fixed)). Qed.
Lemma lem8234958 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term172 A B P lt2 s p t fixed) = (term290 A B P p lt2 s t fixed).
Proof. exact (fun_ext (fun f : A -> B => @lem8234957 A B P p lt2 s t f fixed)). Qed.
Lemma lem8234959 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234960 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term174 A B P lt2 s p t fixed) = (term291 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8234959 A B) (@lem8234958 A B P p lt2 s t fixed)). Qed.
Lemma lem8234961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8234962 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term176 A B P lt2 s p t fixed) = (term292 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8234961) (@lem8234960 A B P p lt2 s t fixed)). Qed.
Lemma lem8234963 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term197 A B P lt2 s p t fixed) = (term293 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8234962 A B P p lt2 s t fixed) (@lem8234616 A B P p t fixed)). Qed.
Lemma lem8234968 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = ((p f a) = (p g a)).
Proof. exact (eq_refl ((p f a) = (p g a))). Qed.
Lemma lem8234973 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term279 A B P lt2 s a f g z)). Qed.
Lemma lem8234974 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term280 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8234973 A B P lt2 s a f g z)). Qed.
Lemma lem8234975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8234976 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234975 A) (@lem8234974 A B P lt2 s a f g)). Qed.
Lemma lem8234977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234978 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term59 A B P lt2 s a f g) = (term59 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234977) (@lem8234976 A B P lt2 s a f g)). Qed.
Lemma lem8234979 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term61 A B P lt2 s f p g a) = (term61 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8234978 A B P lt2 s a f g) (@lem8234968 A B P f p g a)). Qed.
Lemma lem8234980 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term63 A B P lt2 s f p g) = (term63 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8234979 A B P lt2 s f p g a)). Qed.
Lemma lem8234981 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8234982 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term65 A B P lt2 s f p g) = (term65 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8234981 P) (@lem8234980 A B P lt2 s f p g)). Qed.
Lemma lem8234983 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term67 A B P lt2 s f p) = (term67 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8234982 A B P lt2 s f p g)). Qed.
Lemma lem8234984 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234985 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term69 A B P lt2 s f p) = (term69 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8234984 A B) (@lem8234983 A B P lt2 s f p)). Qed.
Lemma lem8234986 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term71 A B P lt2 s p) = (term71 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8234985 A B P lt2 s f p)). Qed.
Lemma lem8234987 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8234988 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term72 A B P lt2 s p) = (term72 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8234987 A B) (@lem8234986 A B P lt2 s p)). Qed.
Lemma lem8234989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8234990 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term74 A B P lt2 s p) = (term74 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8234989) (@lem8234988 A B P lt2 s p)). Qed.
Lemma lem8234991 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term210 A B P lt2 s p t fixed) = (term294 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8234990 A B P lt2 s p) (@lem8234963 A B P p lt2 s t fixed)). Qed.
Lemma lem8234992 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8234997 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term279 A B P lt2 s a f g z)). Qed.
Lemma lem8234998 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term280 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8234997 A B P lt2 s a f g z)). Qed.
Lemma lem8234999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8235000 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term54 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8234999 A) (@lem8234998 A B P lt2 s a f g)). Qed.
Lemma lem8235003 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term295 A B P p g a) = (term295 A B P p g a).
Proof. exact (eq_refl (term295 A B P p g a)). Qed.
Lemma lem8235004 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term296 A B P p lt2 s a f g) = (term296 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235003 A B P p g a) (@lem8235000 A B P lt2 s a f g)). Qed.
Lemma lem8235007 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term295 A B P p f a) = (term295 A B P p f a).
Proof. exact (eq_refl (term295 A B P p f a)). Qed.
Lemma lem8235008 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term297 A B P p lt2 s a f g) = (term297 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235007 A B P p f a) (@lem8235004 A B P p lt2 s a f g)). Qed.
Lemma lem8235009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8235010 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term298 A B P p lt2 s a f g) = (term298 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235009) (@lem8235008 A B P p lt2 s a f g)). Qed.
Lemma lem8235011 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term299 A B P p lt2 s f t g a) = (term299 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235010 A B P p lt2 s a f g) (@lem8234992 A B P f t g a)). Qed.
Lemma lem8235012 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term300 A B P p lt2 s f t g) = (term300 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8235011 A B P p lt2 s f t g a)). Qed.
Lemma lem8235013 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235014 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term301 A B P p lt2 s f t g) = (term301 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235013 P) (@lem8235012 A B P p lt2 s f t g)). Qed.
Lemma lem8235015 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term302 A B P p lt2 s f t) = (term302 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8235014 A B P p lt2 s f t g)). Qed.
Lemma lem8235016 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235017 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term303 A B P p lt2 s f t) = (term303 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235016 A B) (@lem8235015 A B P p lt2 s f t)). Qed.
Lemma lem8235018 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term304 A B P p lt2 s t) = (term304 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8235017 A B P p lt2 s f t)). Qed.
Lemma lem8235019 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235020 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term31 A B P p lt2 s t) = (term31 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235019 A B) (@lem8235018 A B P p lt2 s t)). Qed.
Lemma lem8235021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8235022 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term33 A B P p lt2 s t) = (term33 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235021) (@lem8235020 A B P p lt2 s t)). Qed.
Lemma lem8235023 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term211 A B P lt2 s p t fixed) = (term305 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8235022 A B P p lt2 s t) (@lem8234991 A B P p lt2 s t fixed)). Qed.
Lemma lem8235024 {A B P : Type'} (p : type560 A B P) (s : P -> A) (t : type558 A B P) (fixed : B) : (term213 A B P s p t fixed) = (term306 A B P p s t fixed).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8235023 A B P p lt2 s t fixed)). Qed.
Lemma lem8235025 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8235026 {A B P : Type'} (p : type560 A B P) (s : P -> A) (t : type558 A B P) (fixed : B) : (term215 A B P s p t fixed) = (term307 A B P p s t fixed).
Proof. exact (MK_COMB (@lem8235025 A) (@lem8235024 A B P p s t fixed)). Qed.
Lemma lem8235027 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term217 A B P p t fixed) = (term308 A B P p t fixed).
Proof. exact (fun_ext (fun s : P -> A => @lem8235026 A B P p s t fixed)). Qed.
Lemma lem8235028 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8235029 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term219 A B P p t fixed) = (term309 A B P p t fixed).
Proof. exact (MK_COMB (@lem8235028 A P) (@lem8235027 A B P p t fixed)). Qed.
Lemma lem8235030 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term221 A B P t fixed) = (term310 A B P t fixed).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8235029 A B P p t fixed)). Qed.
Lemma lem8235031 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8235032 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term223 A B P t fixed) = (term311 A B P t fixed).
Proof. exact (MK_COMB (@lem8235031 A B P) (@lem8235030 A B P t fixed)). Qed.
Lemma lem8235033 {A B P : Type'} (fixed : B) : (term225 A B P fixed) = (term312 A B P fixed).
Proof. exact (fun_ext (fun t : type558 A B P => @lem8235032 A B P t fixed)). Qed.
Lemma lem8235034 {A B P : Type'} : (@all ((A -> B) -> P -> B)) = (@all ((A -> B) -> P -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> B))). Qed.
Lemma lem8235035 {A B P : Type'} (fixed : B) : (term227 A B P fixed) = (term313 A B P fixed).
Proof. exact (MK_COMB (@lem8235034 A B P) (@lem8235033 A B P fixed)). Qed.
Lemma lem8235036 {A B P : Type'} : (term229 A B P) = (term314 A B P).
Proof. exact (fun_ext (fun fixed : B => @lem8235035 A B P fixed)). Qed.
Lemma lem8235037 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8235038 {A B P : Type'} : (term231 A B P) = (term315 A B P).
Proof. exact (MK_COMB (@lem8235037 B) (@lem8235036 A B P)). Qed.
Lemma lem8235039 {A B P : Type'} : (term230 A B P) = (term315 A B P).
Proof. exact (TRANS (@lem8234528 A B P) (@lem8235038 A B P)). Qed.
Lemma lem8235199 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8235200 {A B : Type'} (t : Prop) : (term133 A B t) = t.
Proof. exact (@lem8235199 (A -> B) t). Qed.
Lemma lem8235201 {A B P : Type'} : (term250 A B P) = (term125 P).
Proof. exact (@lem8235200 A B (term125 P)). Qed.
Lemma lem8235203 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8235204 {P : Type'} (t : Prop) : (term126 P t) = t.
Proof. exact (@lem8235203 P t). Qed.
Lemma lem8235205 {P : Type'} : (term125 P) = True.
Proof. exact (@lem8235204 P True). Qed.
Lemma lem8235206 {A B P : Type'} : (term250 A B P) = True.
Proof. exact (TRANS (@lem8235201 A B P) (@lem8235205 P)). Qed.
Lemma lem8235207 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term292 A B P p lt2 s t fixed) = (term292 A B P p lt2 s t fixed).
Proof. exact (eq_refl (term292 A B P p lt2 s t fixed)). Qed.
Lemma lem8235208 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term293 A B P p lt2 s t fixed) = (term316 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8235207 A B P p lt2 s t fixed) (@lem8235206 A B P)). Qed.
Lemma lem8235210 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem8235211 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term316 A B P p lt2 s t fixed) = (term291 A B P p lt2 s t fixed).
Proof. exact (@lem8235210 (term291 A B P p lt2 s t fixed)). Qed.
Lemma lem8235274 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term293 A B P p lt2 s t fixed) = (term291 A B P p lt2 s t fixed).
Proof. exact (TRANS (@lem8235208 A B P p lt2 s t fixed) (@lem8235211 A B P p lt2 s t fixed)). Qed.
Lemma lem8235275 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term74 A B P lt2 s p) = (term74 A B P lt2 s p).
Proof. exact (eq_refl (term74 A B P lt2 s p)). Qed.
Lemma lem8235276 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term294 A B P p lt2 s t fixed) = (term317 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8235275 A B P lt2 s p) (@lem8235274 A B P p lt2 s t fixed)). Qed.
Lemma lem8235279 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term33 A B P p lt2 s t) = (term33 A B P p lt2 s t).
Proof. exact (eq_refl (term33 A B P p lt2 s t)). Qed.
Lemma lem8235280 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : (term305 A B P p lt2 s t fixed) = (term318 A B P p lt2 s t fixed).
Proof. exact (MK_COMB (@lem8235279 A B P p lt2 s t) (@lem8235276 A B P p lt2 s t fixed)). Qed.
Lemma lem8235283 {A B P : Type'} (p : type560 A B P) (s : P -> A) (t : type558 A B P) (fixed : B) : (term306 A B P p s t fixed) = (term319 A B P p s t fixed).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8235280 A B P p lt2 s t fixed)). Qed.
Lemma lem8235284 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8235285 {A B P : Type'} (p : type560 A B P) (s : P -> A) (t : type558 A B P) (fixed : B) : (term307 A B P p s t fixed) = (term320 A B P p s t fixed).
Proof. exact (MK_COMB (@lem8235284 A) (@lem8235283 A B P p s t fixed)). Qed.
Lemma lem8235292 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term308 A B P p t fixed) = (term321 A B P p t fixed).
Proof. exact (fun_ext (fun s : P -> A => @lem8235285 A B P p s t fixed)). Qed.
Lemma lem8235293 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8235294 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term309 A B P p t fixed) = (term322 A B P p t fixed).
Proof. exact (MK_COMB (@lem8235293 A P) (@lem8235292 A B P p t fixed)). Qed.
Lemma lem8235301 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term310 A B P t fixed) = (term323 A B P t fixed).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8235294 A B P p t fixed)). Qed.
Lemma lem8235302 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8235303 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term311 A B P t fixed) = (term324 A B P t fixed).
Proof. exact (MK_COMB (@lem8235302 A B P) (@lem8235301 A B P t fixed)). Qed.
Lemma lem8235310 {A B P : Type'} (fixed : B) : (term312 A B P fixed) = (term325 A B P fixed).
Proof. exact (fun_ext (fun t : type558 A B P => @lem8235303 A B P t fixed)). Qed.
Lemma lem8235311 {A B P : Type'} : (@all ((A -> B) -> P -> B)) = (@all ((A -> B) -> P -> B)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> B))). Qed.
Lemma lem8235312 {A B P : Type'} (fixed : B) : (term313 A B P fixed) = (term326 A B P fixed).
Proof. exact (MK_COMB (@lem8235311 A B P) (@lem8235310 A B P fixed)). Qed.
Lemma lem8235319 {A B P : Type'} : (term314 A B P) = (term327 A B P).
Proof. exact (fun_ext (fun fixed : B => @lem8235312 A B P fixed)). Qed.
Lemma lem8235320 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8235321 {A B P : Type'} : (term315 A B P) = (term328 A B P).
Proof. exact (MK_COMB (@lem8235320 B) (@lem8235319 A B P)). Qed.
Lemma lem8235328 {A B P : Type'} : (term230 A B P) = (term328 A B P).
Proof. exact (TRANS (@lem8235039 A B P) (@lem8235321 A B P)). Qed.
Lemma lem8235329 {A B P : Type'} : (term328 A B P) = (term230 A B P).
Proof. exact (SYM (@lem8235328 A B P)). Qed.
Lemma lem8235330 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term31 A B P p lt2 s t.
Proof. exact (h1). Qed.
Lemma lem8235331 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term72 A B P lt2 s p) : term72 A B P lt2 s p.
Proof. exact (h1). Qed.
Lemma lem8235333 (p : Prop) : p = (term200 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8235334 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term278 A B P p lt2 s g t f a fixed) = (term329 A B P p lt2 s g t f a fixed).
Proof. exact (@lem8235333 (term278 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8235335 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term329 A B P p lt2 s g t f a fixed) = (term278 A B P p lt2 s g t f a fixed).
Proof. exact (SYM (@lem8235334 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8235336 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term330 A B P p lt2 s g t f a fixed) : term330 A B P p lt2 s g t f a fixed.
Proof. exact (h1). Qed.
Lemma lem8235345 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term331 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term117 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8235346 {A : Type'} (P : A -> Prop) : (term333 A P) = (term334 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8235347 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term335 A B P lt2 s a f g) = (term336 A B P lt2 s a f g).
Proof. exact (@lem8235346 A (term280 A B P lt2 s a f g)). Qed.
Lemma lem8235348 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term337 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term337 A B P lt2 s a f g z)). Qed.
Lemma lem8235349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8235350 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term338 A B P lt2 s a f g z) = (term331 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235349) (@lem8235348 A B P lt2 s a f g z)). Qed.
Lemma lem8235351 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term338 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8235350 A B P lt2 s a f g z) (@lem8235345 A B P lt2 s a f g z)). Qed.
Lemma lem8235352 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term339 A B P lt2 s a f g) = (term340 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235351 A B P lt2 s a f g z)). Qed.
Lemma lem8235353 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235354 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term336 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235353 A) (@lem8235352 A B P lt2 s a f g)). Qed.
Lemma lem8235355 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term335 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8235347 A B P lt2 s a f g) (@lem8235354 A B P lt2 s a f g)). Qed.
Lemma lem8235357 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term259 A B P p g a) = (term259 A B P p g a).
Proof. exact (eq_refl (term259 A B P p g a)). Qed.
Lemma lem8235358 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term342 A B P p lt2 s a f g) = (term343 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235357 A B P p g a) (@lem8235355 A B P lt2 s a f g)). Qed.
Lemma lem8235359 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term344 A B P p lt2 s a f g) = (term342 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term54 A B P lt2 s a f g)). Qed.
Lemma lem8235360 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term344 A B P p lt2 s a f g) = (term343 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8235359 A B P p lt2 s a f g) (@lem8235358 A B P p lt2 s a f g)). Qed.
Lemma lem8235362 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8235363 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term345 A B P p lt2 s a f g) = (term346 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235362 A B P p f a) (@lem8235360 A B P p lt2 s a f g)). Qed.
Lemma lem8235364 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term347 A B P p lt2 s a f g) = (term345 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term296 A B P p lt2 s a f g)). Qed.
Lemma lem8235365 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term347 A B P p lt2 s a f g) = (term346 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8235364 A B P p lt2 s a f g) (@lem8235363 A B P p lt2 s a f g)). Qed.
Lemma lem8235366 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8235367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235368 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term348 A B P p lt2 s a f g) = (term349 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235367) (@lem8235365 A B P p lt2 s a f g)). Qed.
Lemma lem8235369 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term350 A B P p lt2 s f t g a) = (term351 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235368 A B P p lt2 s a f g) (@lem8235366 A B P f t g a)). Qed.
Lemma lem8235370 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term299 A B P p lt2 s f t g a) = (term350 A B P p lt2 s f t g a).
Proof. exact (@lem17265 (term297 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8235371 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term299 A B P p lt2 s f t g a) = (term351 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8235370 A B P p lt2 s f t g a) (@lem8235369 A B P p lt2 s f t g a)). Qed.
Lemma lem8235372 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term300 A B P p lt2 s f t g) = (term352 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8235371 A B P p lt2 s f t g a)). Qed.
Lemma lem8235373 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235374 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term301 A B P p lt2 s f t g) = (term353 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235373 P) (@lem8235372 A B P p lt2 s f t g)). Qed.
Lemma lem8235375 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term302 A B P p lt2 s f t) = (term354 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8235374 A B P p lt2 s f t g)). Qed.
Lemma lem8235376 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235377 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term303 A B P p lt2 s f t) = (term355 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235376 A B) (@lem8235375 A B P p lt2 s f t)). Qed.
Lemma lem8235378 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term304 A B P p lt2 s t) = (term356 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8235377 A B P p lt2 s f t)). Qed.
Lemma lem8235379 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235380 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term31 A B P p lt2 s t) = (term357 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235379 A B) (@lem8235378 A B P p lt2 s t)). Qed.
Lemma lem8235487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term358 A P Q) = (term359 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8235488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term358 A P Q) = (term359 A P Q).
Proof. exact (@lem8235487 A P Q). Qed.
Lemma lem8235489 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term360 A B P p lt2 s a f g) = (term361 A B P p lt2 s a f g).
Proof. exact (@lem8235488 A (term247 A B P p g a) (term340 A B P lt2 s a f g)). Qed.
Lemma lem8235490 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term362 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (eq_refl (term362 A B P lt2 s a f g z)). Qed.
Lemma lem8235491 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term363 A B P lt2 s a f g) = (term340 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235490 A B P lt2 s a f g z)). Qed.
Lemma lem8235492 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235493 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term364 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235492 A) (@lem8235491 A B P lt2 s a f g)). Qed.
Lemma lem8235494 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term259 A B P p g a) = (term259 A B P p g a).
Proof. exact (eq_refl (term259 A B P p g a)). Qed.
Lemma lem8235495 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term360 A B P p lt2 s a f g) = (term343 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235494 A B P p g a) (@lem8235493 A B P lt2 s a f g)). Qed.
Lemma lem8235496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235497 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term365 A B P p lt2 s a f g) = (term366 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235496) (@lem8235495 A B P p lt2 s a f g)). Qed.
Lemma lem8235498 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term362 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (eq_refl (term362 A B P lt2 s a f g z)). Qed.
Lemma lem8235499 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term259 A B P p g a) = (term259 A B P p g a).
Proof. exact (eq_refl (term259 A B P p g a)). Qed.
Lemma lem8235500 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term367 A B P p lt2 s a f g z) = (term368 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235499 A B P p g a) (@lem8235498 A B P lt2 s a f g z)). Qed.
Lemma lem8235501 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term369 A B P p lt2 s a f g) = (term370 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235500 A B P p lt2 s a f g z)). Qed.
Lemma lem8235502 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235503 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term361 A B P p lt2 s a f g) = (term371 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235502 A) (@lem8235501 A B P p lt2 s a f g)). Qed.
Lemma lem8235504 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term360 A B P p lt2 s a f g) = (term361 A B P p lt2 s a f g)) = ((term343 A B P p lt2 s a f g) = (term371 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8235497 A B P p lt2 s a f g) (@lem8235503 A B P p lt2 s a f g)). Qed.
Lemma lem8235505 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term343 A B P p lt2 s a f g) = (term371 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8235504 A B P p lt2 s a f g) (@lem8235489 A B P p lt2 s a f g)). Qed.
Lemma lem8235506 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8235507 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term346 A B P p lt2 s a f g) = (term372 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235506 A B P p f a) (@lem8235505 A B P p lt2 s a f g)). Qed.
Lemma lem8235509 {A : Type'} (P : Prop) (Q : A -> Prop) : (term358 A P Q) = (term359 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8235510 {A : Type'} (P : Prop) (Q : A -> Prop) : (term358 A P Q) = (term359 A P Q).
Proof. exact (@lem8235509 A P Q). Qed.
Lemma lem8235511 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term373 A B P p lt2 s a f g) = (term374 A B P p lt2 s a f g).
Proof. exact (@lem8235510 A (term247 A B P p f a) (term370 A B P p lt2 s a f g)). Qed.
Lemma lem8235512 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term375 A B P p lt2 s a f g z) = (term368 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term375 A B P p lt2 s a f g z)). Qed.
Lemma lem8235513 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term376 A B P p lt2 s a f g) = (term370 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235512 A B P p lt2 s a f g z)). Qed.
Lemma lem8235514 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235515 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term377 A B P p lt2 s a f g) = (term371 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235514 A) (@lem8235513 A B P p lt2 s a f g)). Qed.
Lemma lem8235516 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8235517 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term373 A B P p lt2 s a f g) = (term372 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235516 A B P p f a) (@lem8235515 A B P p lt2 s a f g)). Qed.
Lemma lem8235518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235519 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term378 A B P p lt2 s a f g) = (term379 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235518) (@lem8235517 A B P p lt2 s a f g)). Qed.
Lemma lem8235520 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term375 A B P p lt2 s a f g z) = (term368 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term375 A B P p lt2 s a f g z)). Qed.
Lemma lem8235521 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term259 A B P p f a).
Proof. exact (eq_refl (term259 A B P p f a)). Qed.
Lemma lem8235522 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term380 A B P p lt2 s a f g z) = (term381 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235521 A B P p f a) (@lem8235520 A B P p lt2 s a f g z)). Qed.
Lemma lem8235523 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term382 A B P p lt2 s a f g) = (term383 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235522 A B P p lt2 s a f g z)). Qed.
Lemma lem8235524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235525 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term374 A B P p lt2 s a f g) = (term384 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235524 A) (@lem8235523 A B P p lt2 s a f g)). Qed.
Lemma lem8235526 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term373 A B P p lt2 s a f g) = (term374 A B P p lt2 s a f g)) = ((term372 A B P p lt2 s a f g) = (term384 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8235519 A B P p lt2 s a f g) (@lem8235525 A B P p lt2 s a f g)). Qed.
Lemma lem8235527 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term372 A B P p lt2 s a f g) = (term384 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8235526 A B P p lt2 s a f g) (@lem8235511 A B P p lt2 s a f g)). Qed.
Lemma lem8235528 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term346 A B P p lt2 s a f g) = (term384 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8235507 A B P p lt2 s a f g) (@lem8235527 A B P p lt2 s a f g)). Qed.
Lemma lem8235529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235530 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term349 A B P p lt2 s a f g) = (term385 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235529) (@lem8235528 A B P p lt2 s a f g)). Qed.
Lemma lem8235531 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8235532 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term351 A B P p lt2 s f t g a) = (term386 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235530 A B P p lt2 s a f g) (@lem8235531 A B P f t g a)). Qed.
Lemma lem8235534 {A : Type'} (P : A -> Prop) (Q : Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8235535 {A : Type'} (P : A -> Prop) (Q : Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (@lem8235534 A P Q). Qed.
Lemma lem8235536 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term389 A B P p lt2 s f t g a) = (term390 A B P p lt2 s f t g a).
Proof. exact (@lem8235535 A (term383 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8235537 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term391 A B P p lt2 s a f g z) = (term381 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term391 A B P p lt2 s a f g z)). Qed.
Lemma lem8235538 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term392 A B P p lt2 s a f g) = (term383 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235537 A B P p lt2 s a f g z)). Qed.
Lemma lem8235539 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235540 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term393 A B P p lt2 s a f g) = (term384 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235539 A) (@lem8235538 A B P p lt2 s a f g)). Qed.
Lemma lem8235541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235542 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term394 A B P p lt2 s a f g) = (term385 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8235541) (@lem8235540 A B P p lt2 s a f g)). Qed.
Lemma lem8235543 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8235544 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term389 A B P p lt2 s f t g a) = (term386 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235542 A B P p lt2 s a f g) (@lem8235543 A B P f t g a)). Qed.
Lemma lem8235545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235546 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term395 A B P p lt2 s f t g a) = (term396 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235545) (@lem8235544 A B P p lt2 s f t g a)). Qed.
Lemma lem8235547 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term391 A B P p lt2 s a f g z) = (term381 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term391 A B P p lt2 s a f g z)). Qed.
Lemma lem8235548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235549 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term397 A B P p lt2 s a f g z) = (term398 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235548) (@lem8235547 A B P p lt2 s a f g z)). Qed.
Lemma lem8235550 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8235551 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term399 A B P p lt2 s z f t g a) = (term400 A B P p lt2 s z f t g a).
Proof. exact (MK_COMB (@lem8235549 A B P p lt2 s a f g z) (@lem8235550 A B P f t g a)). Qed.
Lemma lem8235552 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term401 A B P p lt2 s f t g a) = (term402 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8235551 A B P p lt2 s z f t g a)). Qed.
Lemma lem8235553 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235554 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term390 A B P p lt2 s f t g a) = (term403 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235553 A) (@lem8235552 A B P p lt2 s f t g a)). Qed.
Lemma lem8235555 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((term389 A B P p lt2 s f t g a) = (term390 A B P p lt2 s f t g a)) = ((term386 A B P p lt2 s f t g a) = (term403 A B P p lt2 s f t g a)).
Proof. exact (MK_COMB (@lem8235546 A B P p lt2 s f t g a) (@lem8235554 A B P p lt2 s f t g a)). Qed.
Lemma lem8235556 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term386 A B P p lt2 s f t g a) = (term403 A B P p lt2 s f t g a).
Proof. exact (EQ_MP (@lem8235555 A B P p lt2 s f t g a) (@lem8235536 A B P p lt2 s f t g a)). Qed.
Lemma lem8235557 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term351 A B P p lt2 s f t g a) = (term403 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8235532 A B P p lt2 s f t g a) (@lem8235556 A B P p lt2 s f t g a)). Qed.
Lemma lem8235558 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term352 A B P p lt2 s f t g) = (term404 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8235557 A B P p lt2 s f t g a)). Qed.
Lemma lem8235559 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235560 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term353 A B P p lt2 s f t g) = (term405 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235559 P) (@lem8235558 A B P p lt2 s f t g)). Qed.
Lemma lem8235562 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235563 {A P : Type'} (P' : type1470 A P) : (term408 A P P') = (term409 A P P').
Proof. exact (@lem8235562 P A P'). Qed.
Lemma lem8235564 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term410 A B P p lt2 s f t g) = (term411 A B P p lt2 s f t g).
Proof. exact (@lem8235563 A P (term412 A B P p lt2 s f t g)). Qed.
Lemma lem8235565 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term413 A B P p lt2 s f t g a) = (term402 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term413 A B P p lt2 s f t g a)). Qed.
Lemma lem8235566 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235567 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (z : A) : (term414 A B P p lt2 s f t g a z) = (term415 A B P p lt2 s f t g a z).
Proof. exact (MK_COMB (@lem8235565 A B P p lt2 s f t g a) (@lem8235566 A z)). Qed.
Lemma lem8235568 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term415 A B P p lt2 s f t g a z) = (term400 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term415 A B P p lt2 s f t g a z)). Qed.
Lemma lem8235569 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term414 A B P p lt2 s f t g a z) = (term400 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8235567 A B P p lt2 s f t g a z) (@lem8235568 A B P p lt2 s z f t g a)). Qed.
Lemma lem8235570 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term416 A B P p lt2 s f t g a) = (term402 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8235569 A B P p lt2 s z f t g a)). Qed.
Lemma lem8235571 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235572 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term417 A B P p lt2 s f t g a) = (term403 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235571 A) (@lem8235570 A B P p lt2 s f t g a)). Qed.
Lemma lem8235573 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term418 A B P p lt2 s f t g) = (term404 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8235572 A B P p lt2 s f t g a)). Qed.
Lemma lem8235574 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235575 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term410 A B P p lt2 s f t g) = (term405 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235574 P) (@lem8235573 A B P p lt2 s f t g)). Qed.
Lemma lem8235576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235577 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term419 A B P p lt2 s f t g) = (term420 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235576) (@lem8235575 A B P p lt2 s f t g)). Qed.
Lemma lem8235578 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term413 A B P p lt2 s f t g a) = (term402 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term413 A B P p lt2 s f t g a)). Qed.
Lemma lem8235579 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8235580 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (z : P -> A) (a : P) : (term421 A B P p lt2 s f t g z a) = (term422 A B P p lt2 s f t g z a).
Proof. exact (MK_COMB (@lem8235578 A B P p lt2 s f t g a) (@lem8235579 A P z a)). Qed.
Lemma lem8235581 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term422 A B P p lt2 s f t g z a) = (term423 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term422 A B P p lt2 s f t g z a)). Qed.
Lemma lem8235582 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term421 A B P p lt2 s f t g z a) = (term423 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8235580 A B P p lt2 s f t g z a) (@lem8235581 A B P p lt2 s z f t g a)). Qed.
Lemma lem8235583 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term424 A B P p lt2 s f t g z) = (term425 A B P p lt2 s z f t g).
Proof. exact (fun_ext (fun a : P => @lem8235582 A B P p lt2 s z f t g a)). Qed.
Lemma lem8235584 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235585 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term426 A B P p lt2 s f t g z) = (term427 A B P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8235584 P) (@lem8235583 A B P p lt2 s z f t g)). Qed.
Lemma lem8235586 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term428 A B P p lt2 s f t g) = (term429 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8235585 A B P p lt2 s z f t g)). Qed.
Lemma lem8235587 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8235588 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term411 A B P p lt2 s f t g) = (term430 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235587 A P) (@lem8235586 A B P p lt2 s f t g)). Qed.
Lemma lem8235589 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : ((term410 A B P p lt2 s f t g) = (term411 A B P p lt2 s f t g)) = ((term405 A B P p lt2 s f t g) = (term430 A B P p lt2 s f t g)).
Proof. exact (MK_COMB (@lem8235577 A B P p lt2 s f t g) (@lem8235588 A B P p lt2 s f t g)). Qed.
Lemma lem8235590 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term405 A B P p lt2 s f t g) = (term430 A B P p lt2 s f t g).
Proof. exact (EQ_MP (@lem8235589 A B P p lt2 s f t g) (@lem8235564 A B P p lt2 s f t g)). Qed.
Lemma lem8235591 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term353 A B P p lt2 s f t g) = (term430 A B P p lt2 s f t g).
Proof. exact (TRANS (@lem8235560 A B P p lt2 s f t g) (@lem8235590 A B P p lt2 s f t g)). Qed.
Lemma lem8235592 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term354 A B P p lt2 s f t) = (term431 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8235591 A B P p lt2 s f t g)). Qed.
Lemma lem8235593 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235594 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term355 A B P p lt2 s f t) = (term432 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235593 A B) (@lem8235592 A B P p lt2 s f t)). Qed.
Lemma lem8235596 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235597 {A B P : Type'} (P' : type537 A B P) : (term433 A B P P') = (term434 A B P P').
Proof. exact (@lem8235596 (A -> B) (P -> A) P'). Qed.
Lemma lem8235598 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term435 A B P p lt2 s f t) = (term436 A B P p lt2 s f t).
Proof. exact (@lem8235597 A B P (term437 A B P p lt2 s f t)). Qed.
Lemma lem8235599 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term438 A B P p lt2 s f t g) = (term429 A B P p lt2 s f t g).
Proof. exact (eq_refl (term438 A B P p lt2 s f t g)). Qed.
Lemma lem8235600 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235601 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (z : P -> A) : (term439 A B P p lt2 s f t g z) = (term440 A B P p lt2 s f t g z).
Proof. exact (MK_COMB (@lem8235599 A B P p lt2 s f t g) (@lem8235600 A P z)). Qed.
Lemma lem8235602 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term440 A B P p lt2 s f t g z) = (term427 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term440 A B P p lt2 s f t g z)). Qed.
Lemma lem8235603 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term439 A B P p lt2 s f t g z) = (term427 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8235601 A B P p lt2 s f t g z) (@lem8235602 A B P p lt2 s z f t g)). Qed.
Lemma lem8235604 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term441 A B P p lt2 s f t g) = (term429 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8235603 A B P p lt2 s z f t g)). Qed.
Lemma lem8235605 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8235606 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term442 A B P p lt2 s f t g) = (term430 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8235605 A P) (@lem8235604 A B P p lt2 s f t g)). Qed.
Lemma lem8235607 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term443 A B P p lt2 s f t) = (term431 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8235606 A B P p lt2 s f t g)). Qed.
Lemma lem8235608 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235609 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term435 A B P p lt2 s f t) = (term432 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235608 A B) (@lem8235607 A B P p lt2 s f t)). Qed.
Lemma lem8235610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235611 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term444 A B P p lt2 s f t) = (term445 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235610) (@lem8235609 A B P p lt2 s f t)). Qed.
Lemma lem8235612 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term438 A B P p lt2 s f t g) = (term429 A B P p lt2 s f t g).
Proof. exact (eq_refl (term438 A B P p lt2 s f t g)). Qed.
Lemma lem8235613 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8235614 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (z : type557 A B P) (g : A -> B) : (term446 A B P p lt2 s f t z g) = (term447 A B P p lt2 s f t z g).
Proof. exact (MK_COMB (@lem8235612 A B P p lt2 s f t g) (@lem8235613 A B P z g)). Qed.
Lemma lem8235615 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term447 A B P p lt2 s f t z g) = (term448 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term447 A B P p lt2 s f t z g)). Qed.
Lemma lem8235616 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term446 A B P p lt2 s f t z g) = (term448 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8235614 A B P p lt2 s f t z g) (@lem8235615 A B P p lt2 s z f t g)). Qed.
Lemma lem8235617 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) : (term449 A B P p lt2 s f t z) = (term450 A B P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8235616 A B P p lt2 s z f t g)). Qed.
Lemma lem8235618 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235619 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) : (term451 A B P p lt2 s f t z) = (term452 A B P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8235618 A B) (@lem8235617 A B P p lt2 s z f t)). Qed.
Lemma lem8235620 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term453 A B P p lt2 s f t) = (term454 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8235619 A B P p lt2 s z f t)). Qed.
Lemma lem8235621 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8235622 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term436 A B P p lt2 s f t) = (term455 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235621 A B P) (@lem8235620 A B P p lt2 s f t)). Qed.
Lemma lem8235623 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : ((term435 A B P p lt2 s f t) = (term436 A B P p lt2 s f t)) = ((term432 A B P p lt2 s f t) = (term455 A B P p lt2 s f t)).
Proof. exact (MK_COMB (@lem8235611 A B P p lt2 s f t) (@lem8235622 A B P p lt2 s f t)). Qed.
Lemma lem8235624 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term432 A B P p lt2 s f t) = (term455 A B P p lt2 s f t).
Proof. exact (EQ_MP (@lem8235623 A B P p lt2 s f t) (@lem8235598 A B P p lt2 s f t)). Qed.
Lemma lem8235625 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term355 A B P p lt2 s f t) = (term455 A B P p lt2 s f t).
Proof. exact (TRANS (@lem8235594 A B P p lt2 s f t) (@lem8235624 A B P p lt2 s f t)). Qed.
Lemma lem8235626 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term356 A B P p lt2 s t) = (term456 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8235625 A B P p lt2 s f t)). Qed.
Lemma lem8235627 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235628 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term357 A B P p lt2 s t) = (term457 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235627 A B) (@lem8235626 A B P p lt2 s t)). Qed.
Lemma lem8235630 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235631 {A B P : Type'} (P' : type495 A B P) : (term458 A B P P') = (term459 A B P P').
Proof. exact (@lem8235630 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8235632 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term460 A B P p lt2 s t) = (term461 A B P p lt2 s t).
Proof. exact (@lem8235631 A B P (term462 A B P p lt2 s t)). Qed.
Lemma lem8235633 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term463 A B P p lt2 s t f) = (term454 A B P p lt2 s f t).
Proof. exact (eq_refl (term463 A B P p lt2 s t f)). Qed.
Lemma lem8235634 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235635 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (z : type557 A B P) : (term464 A B P p lt2 s t f z) = (term465 A B P p lt2 s f t z).
Proof. exact (MK_COMB (@lem8235633 A B P p lt2 s f t) (@lem8235634 A B P z)). Qed.
Lemma lem8235636 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) : (term465 A B P p lt2 s f t z) = (term452 A B P p lt2 s z f t).
Proof. exact (eq_refl (term465 A B P p lt2 s f t z)). Qed.
Lemma lem8235637 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type558 A B P) : (term464 A B P p lt2 s t f z) = (term452 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8235635 A B P p lt2 s f t z) (@lem8235636 A B P p lt2 s z f t)). Qed.
Lemma lem8235638 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term466 A B P p lt2 s t f) = (term454 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8235637 A B P p lt2 s z f t)). Qed.
Lemma lem8235639 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8235640 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term467 A B P p lt2 s t f) = (term455 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8235639 A B P) (@lem8235638 A B P p lt2 s f t)). Qed.
Lemma lem8235641 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term468 A B P p lt2 s t) = (term456 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8235640 A B P p lt2 s f t)). Qed.
Lemma lem8235642 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235643 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term460 A B P p lt2 s t) = (term457 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235642 A B) (@lem8235641 A B P p lt2 s t)). Qed.
Lemma lem8235644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235645 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term469 A B P p lt2 s t) = (term470 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235644) (@lem8235643 A B P p lt2 s t)). Qed.
Lemma lem8235646 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) : (term463 A B P p lt2 s t f) = (term454 A B P p lt2 s f t).
Proof. exact (eq_refl (term463 A B P p lt2 s t f)). Qed.
Lemma lem8235647 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8235648 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (z : type518 A B P) (f : A -> B) : (term471 A B P p lt2 s t z f) = (term472 A B P p lt2 s t z f).
Proof. exact (MK_COMB (@lem8235646 A B P p lt2 s f t) (@lem8235647 A B P z f)). Qed.
Lemma lem8235649 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type558 A B P) : (term472 A B P p lt2 s t z f) = (term473 A B P p lt2 s z f t).
Proof. exact (eq_refl (term472 A B P p lt2 s t z f)). Qed.
Lemma lem8235650 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type558 A B P) : (term471 A B P p lt2 s t z f) = (term473 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8235648 A B P p lt2 s t z f) (@lem8235649 A B P p lt2 s z f t)). Qed.
Lemma lem8235651 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type558 A B P) : (term474 A B P p lt2 s t z) = (term475 A B P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8235650 A B P p lt2 s z f t)). Qed.
Lemma lem8235652 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235653 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type558 A B P) : (term476 A B P p lt2 s t z) = (term477 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8235652 A B) (@lem8235651 A B P p lt2 s z t)). Qed.
Lemma lem8235654 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term478 A B P p lt2 s t) = (term479 A B P p lt2 s t).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8235653 A B P p lt2 s z t)). Qed.
Lemma lem8235655 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8235656 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term461 A B P p lt2 s t) = (term480 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8235655 A B P) (@lem8235654 A B P p lt2 s t)). Qed.
Lemma lem8235657 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : ((term460 A B P p lt2 s t) = (term461 A B P p lt2 s t)) = ((term457 A B P p lt2 s t) = (term480 A B P p lt2 s t)).
Proof. exact (MK_COMB (@lem8235645 A B P p lt2 s t) (@lem8235656 A B P p lt2 s t)). Qed.
Lemma lem8235658 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term457 A B P p lt2 s t) = (term480 A B P p lt2 s t).
Proof. exact (EQ_MP (@lem8235657 A B P p lt2 s t) (@lem8235632 A B P p lt2 s t)). Qed.
Lemma lem8235660 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term357 A B P p lt2 s t) = (term480 A B P p lt2 s t).
Proof. exact (TRANS (@lem8235628 A B P p lt2 s t) (@lem8235658 A B P p lt2 s t)). Qed.
Lemma lem8235661 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (term31 A B P p lt2 s t) = (term480 A B P p lt2 s t).
Proof. exact (TRANS (@lem8235380 A B P p lt2 s t) (@lem8235660 A B P p lt2 s t)). Qed.
Lemma lem8235662 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term480 A B P p lt2 s t.
Proof. exact (EQ_MP (@lem8235661 A B P p lt2 s t) (@lem8235330 A B P p lt2 s t h1)). Qed.
Lemma lem8235669 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term331 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term117 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8235670 {A : Type'} (P : A -> Prop) : (term333 A P) = (term334 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8235671 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term335 A B P lt2 s a f g) = (term336 A B P lt2 s a f g).
Proof. exact (@lem8235670 A (term280 A B P lt2 s a f g)). Qed.
Lemma lem8235672 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term337 A B P lt2 s a f g z) = (term279 A B P lt2 s a f g z).
Proof. exact (eq_refl (term337 A B P lt2 s a f g z)). Qed.
Lemma lem8235673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8235674 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term338 A B P lt2 s a f g z) = (term331 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235673) (@lem8235672 A B P lt2 s a f g z)). Qed.
Lemma lem8235675 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term338 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8235674 A B P lt2 s a f g z) (@lem8235669 A B P lt2 s a f g z)). Qed.
Lemma lem8235676 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term339 A B P lt2 s a f g) = (term340 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235675 A B P lt2 s a f g z)). Qed.
Lemma lem8235677 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235678 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term336 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235677 A) (@lem8235676 A B P lt2 s a f g)). Qed.
Lemma lem8235679 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term335 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8235671 A B P lt2 s a f g) (@lem8235678 A B P lt2 s a f g)). Qed.
Lemma lem8235694 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = (term481 A B P f p g a).
Proof. exact (@lem17784 (p f a) (p g a)). Qed.
Lemma lem8235695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235696 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term482 A B P lt2 s a f g) = (term483 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235695) (@lem8235679 A B P lt2 s a f g)). Qed.
Lemma lem8235697 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term484 A B P lt2 s f p g a) = (term485 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8235696 A B P lt2 s a f g) (@lem8235694 A B P f p g a)). Qed.
Lemma lem8235698 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term61 A B P lt2 s f p g a) = (term484 A B P lt2 s f p g a).
Proof. exact (@lem17265 (term54 A B P lt2 s a f g) ((p f a) = (p g a))). Qed.
Lemma lem8235699 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term61 A B P lt2 s f p g a) = (term485 A B P lt2 s f p g a).
Proof. exact (TRANS (@lem8235698 A B P lt2 s f p g a) (@lem8235697 A B P lt2 s f p g a)). Qed.
Lemma lem8235700 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term63 A B P lt2 s f p g) = (term486 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8235699 A B P lt2 s f p g a)). Qed.
Lemma lem8235701 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235702 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term65 A B P lt2 s f p g) = (term487 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235701 P) (@lem8235700 A B P lt2 s f p g)). Qed.
Lemma lem8235703 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term67 A B P lt2 s f p) = (term488 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8235702 A B P lt2 s f p g)). Qed.
Lemma lem8235704 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235705 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term69 A B P lt2 s f p) = (term489 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235704 A B) (@lem8235703 A B P lt2 s f p)). Qed.
Lemma lem8235706 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term71 A B P lt2 s p) = (term490 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8235705 A B P lt2 s f p)). Qed.
Lemma lem8235707 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235708 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term72 A B P lt2 s p) = (term491 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8235707 A B) (@lem8235706 A B P lt2 s p)). Qed.
Lemma lem8235815 {A : Type'} (P : A -> Prop) (Q : Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8235816 {A : Type'} (P : A -> Prop) (Q : Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (@lem8235815 A P Q). Qed.
Lemma lem8235817 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term492 A B P lt2 s f p g a) = (term493 A B P lt2 s f p g a).
Proof. exact (@lem8235816 A (term340 A B P lt2 s a f g) (term481 A B P f p g a)). Qed.
Lemma lem8235818 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term362 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (eq_refl (term362 A B P lt2 s a f g z)). Qed.
Lemma lem8235819 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term363 A B P lt2 s a f g) = (term340 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235818 A B P lt2 s a f g z)). Qed.
Lemma lem8235820 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235821 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term364 A B P lt2 s a f g) = (term341 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235820 A) (@lem8235819 A B P lt2 s a f g)). Qed.
Lemma lem8235822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235823 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term494 A B P lt2 s a f g) = (term483 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235822) (@lem8235821 A B P lt2 s a f g)). Qed.
Lemma lem8235824 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term481 A B P f p g a) = (term481 A B P f p g a).
Proof. exact (eq_refl (term481 A B P f p g a)). Qed.
Lemma lem8235825 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term492 A B P lt2 s f p g a) = (term485 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8235823 A B P lt2 s a f g) (@lem8235824 A B P f p g a)). Qed.
Lemma lem8235826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235827 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term495 A B P lt2 s f p g a) = (term496 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8235826) (@lem8235825 A B P lt2 s f p g a)). Qed.
Lemma lem8235828 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term362 A B P lt2 s a f g z) = (term332 A B P lt2 s a f g z).
Proof. exact (eq_refl (term362 A B P lt2 s a f g z)). Qed.
Lemma lem8235829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235830 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term497 A B P lt2 s a f g z) = (term498 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8235829) (@lem8235828 A B P lt2 s a f g z)). Qed.
Lemma lem8235831 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term481 A B P f p g a) = (term481 A B P f p g a).
Proof. exact (eq_refl (term481 A B P f p g a)). Qed.
Lemma lem8235832 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term499 A B P lt2 s z f p g a) = (term500 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8235830 A B P lt2 s a f g z) (@lem8235831 A B P f p g a)). Qed.
Lemma lem8235833 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term501 A B P lt2 s f p g a) = (term502 A B P lt2 s f p g a).
Proof. exact (fun_ext (fun z : A => @lem8235832 A B P lt2 s z f p g a)). Qed.
Lemma lem8235834 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235835 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term493 A B P lt2 s f p g a) = (term503 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8235834 A) (@lem8235833 A B P lt2 s f p g a)). Qed.
Lemma lem8235836 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((term492 A B P lt2 s f p g a) = (term493 A B P lt2 s f p g a)) = ((term485 A B P lt2 s f p g a) = (term503 A B P lt2 s f p g a)).
Proof. exact (MK_COMB (@lem8235827 A B P lt2 s f p g a) (@lem8235835 A B P lt2 s f p g a)). Qed.
Lemma lem8235837 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term485 A B P lt2 s f p g a) = (term503 A B P lt2 s f p g a).
Proof. exact (EQ_MP (@lem8235836 A B P lt2 s f p g a) (@lem8235817 A B P lt2 s f p g a)). Qed.
Lemma lem8235838 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term486 A B P lt2 s f p g) = (term504 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8235837 A B P lt2 s f p g a)). Qed.
Lemma lem8235839 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235840 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term487 A B P lt2 s f p g) = (term505 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235839 P) (@lem8235838 A B P lt2 s f p g)). Qed.
Lemma lem8235842 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235843 {A P : Type'} (P' : type1470 A P) : (term408 A P P') = (term409 A P P').
Proof. exact (@lem8235842 P A P'). Qed.
Lemma lem8235844 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term506 A B P lt2 s f p g) = (term507 A B P lt2 s f p g).
Proof. exact (@lem8235843 A P (term508 A B P lt2 s f p g)). Qed.
Lemma lem8235845 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term509 A B P lt2 s f p g a) = (term502 A B P lt2 s f p g a).
Proof. exact (eq_refl (term509 A B P lt2 s f p g a)). Qed.
Lemma lem8235846 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235847 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (z : A) : (term510 A B P lt2 s f p g a z) = (term511 A B P lt2 s f p g a z).
Proof. exact (MK_COMB (@lem8235845 A B P lt2 s f p g a) (@lem8235846 A z)). Qed.
Lemma lem8235848 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term511 A B P lt2 s f p g a z) = (term500 A B P lt2 s z f p g a).
Proof. exact (eq_refl (term511 A B P lt2 s f p g a z)). Qed.
Lemma lem8235849 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term510 A B P lt2 s f p g a z) = (term500 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8235847 A B P lt2 s f p g a z) (@lem8235848 A B P lt2 s z f p g a)). Qed.
Lemma lem8235850 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term512 A B P lt2 s f p g a) = (term502 A B P lt2 s f p g a).
Proof. exact (fun_ext (fun z : A => @lem8235849 A B P lt2 s z f p g a)). Qed.
Lemma lem8235851 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8235852 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term513 A B P lt2 s f p g a) = (term503 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8235851 A) (@lem8235850 A B P lt2 s f p g a)). Qed.
Lemma lem8235853 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term514 A B P lt2 s f p g) = (term504 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8235852 A B P lt2 s f p g a)). Qed.
Lemma lem8235854 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235855 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term506 A B P lt2 s f p g) = (term505 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235854 P) (@lem8235853 A B P lt2 s f p g)). Qed.
Lemma lem8235856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235857 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term515 A B P lt2 s f p g) = (term516 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235856) (@lem8235855 A B P lt2 s f p g)). Qed.
Lemma lem8235858 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term509 A B P lt2 s f p g a) = (term502 A B P lt2 s f p g a).
Proof. exact (eq_refl (term509 A B P lt2 s f p g a)). Qed.
Lemma lem8235859 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8235860 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (z : P -> A) (a : P) : (term517 A B P lt2 s f p g z a) = (term518 A B P lt2 s f p g z a).
Proof. exact (MK_COMB (@lem8235858 A B P lt2 s f p g a) (@lem8235859 A P z a)). Qed.
Lemma lem8235861 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term518 A B P lt2 s f p g z a) = (term519 A B P lt2 s z f p g a).
Proof. exact (eq_refl (term518 A B P lt2 s f p g z a)). Qed.
Lemma lem8235862 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term517 A B P lt2 s f p g z a) = (term519 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8235860 A B P lt2 s f p g z a) (@lem8235861 A B P lt2 s z f p g a)). Qed.
Lemma lem8235863 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term520 A B P lt2 s f p g z) = (term521 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8235862 A B P lt2 s z f p g a)). Qed.
Lemma lem8235864 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8235865 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term522 A B P lt2 s f p g z) = (term523 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8235864 P) (@lem8235863 A B P lt2 s z f p g)). Qed.
Lemma lem8235866 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term524 A B P lt2 s f p g) = (term525 A B P lt2 s f p g).
Proof. exact (fun_ext (fun z : P -> A => @lem8235865 A B P lt2 s z f p g)). Qed.
Lemma lem8235867 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8235868 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term507 A B P lt2 s f p g) = (term526 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235867 A P) (@lem8235866 A B P lt2 s f p g)). Qed.
Lemma lem8235869 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : ((term506 A B P lt2 s f p g) = (term507 A B P lt2 s f p g)) = ((term505 A B P lt2 s f p g) = (term526 A B P lt2 s f p g)).
Proof. exact (MK_COMB (@lem8235857 A B P lt2 s f p g) (@lem8235868 A B P lt2 s f p g)). Qed.
Lemma lem8235870 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term505 A B P lt2 s f p g) = (term526 A B P lt2 s f p g).
Proof. exact (EQ_MP (@lem8235869 A B P lt2 s f p g) (@lem8235844 A B P lt2 s f p g)). Qed.
Lemma lem8235871 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term487 A B P lt2 s f p g) = (term526 A B P lt2 s f p g).
Proof. exact (TRANS (@lem8235840 A B P lt2 s f p g) (@lem8235870 A B P lt2 s f p g)). Qed.
Lemma lem8235872 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term488 A B P lt2 s f p) = (term527 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8235871 A B P lt2 s f p g)). Qed.
Lemma lem8235873 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235874 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term489 A B P lt2 s f p) = (term528 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235873 A B) (@lem8235872 A B P lt2 s f p)). Qed.
Lemma lem8235876 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235877 {A B P : Type'} (P' : type537 A B P) : (term433 A B P P') = (term434 A B P P').
Proof. exact (@lem8235876 (A -> B) (P -> A) P'). Qed.
Lemma lem8235878 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term529 A B P lt2 s f p) = (term530 A B P lt2 s f p).
Proof. exact (@lem8235877 A B P (term531 A B P lt2 s f p)). Qed.
Lemma lem8235879 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term532 A B P lt2 s f p g) = (term525 A B P lt2 s f p g).
Proof. exact (eq_refl (term532 A B P lt2 s f p g)). Qed.
Lemma lem8235880 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235881 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (z : P -> A) : (term533 A B P lt2 s f p g z) = (term534 A B P lt2 s f p g z).
Proof. exact (MK_COMB (@lem8235879 A B P lt2 s f p g) (@lem8235880 A P z)). Qed.
Lemma lem8235882 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term534 A B P lt2 s f p g z) = (term523 A B P lt2 s z f p g).
Proof. exact (eq_refl (term534 A B P lt2 s f p g z)). Qed.
Lemma lem8235883 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term533 A B P lt2 s f p g z) = (term523 A B P lt2 s z f p g).
Proof. exact (TRANS (@lem8235881 A B P lt2 s f p g z) (@lem8235882 A B P lt2 s z f p g)). Qed.
Lemma lem8235884 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term535 A B P lt2 s f p g) = (term525 A B P lt2 s f p g).
Proof. exact (fun_ext (fun z : P -> A => @lem8235883 A B P lt2 s z f p g)). Qed.
Lemma lem8235885 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8235886 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term536 A B P lt2 s f p g) = (term526 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8235885 A P) (@lem8235884 A B P lt2 s f p g)). Qed.
Lemma lem8235887 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term537 A B P lt2 s f p) = (term527 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8235886 A B P lt2 s f p g)). Qed.
Lemma lem8235888 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235889 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term529 A B P lt2 s f p) = (term528 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235888 A B) (@lem8235887 A B P lt2 s f p)). Qed.
Lemma lem8235890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235891 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term538 A B P lt2 s f p) = (term539 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235890) (@lem8235889 A B P lt2 s f p)). Qed.
Lemma lem8235892 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term532 A B P lt2 s f p g) = (term525 A B P lt2 s f p g).
Proof. exact (eq_refl (term532 A B P lt2 s f p g)). Qed.
Lemma lem8235893 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8235894 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (z : type557 A B P) (g : A -> B) : (term540 A B P lt2 s f p z g) = (term541 A B P lt2 s f p z g).
Proof. exact (MK_COMB (@lem8235892 A B P lt2 s f p g) (@lem8235893 A B P z g)). Qed.
Lemma lem8235895 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term541 A B P lt2 s f p z g) = (term542 A B P lt2 s z f p g).
Proof. exact (eq_refl (term541 A B P lt2 s f p z g)). Qed.
Lemma lem8235896 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term540 A B P lt2 s f p z g) = (term542 A B P lt2 s z f p g).
Proof. exact (TRANS (@lem8235894 A B P lt2 s f p z g) (@lem8235895 A B P lt2 s z f p g)). Qed.
Lemma lem8235897 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term543 A B P lt2 s f p z) = (term544 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8235896 A B P lt2 s z f p g)). Qed.
Lemma lem8235898 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235899 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term545 A B P lt2 s f p z) = (term546 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8235898 A B) (@lem8235897 A B P lt2 s z f p)). Qed.
Lemma lem8235900 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term547 A B P lt2 s f p) = (term548 A B P lt2 s f p).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8235899 A B P lt2 s z f p)). Qed.
Lemma lem8235901 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8235902 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term530 A B P lt2 s f p) = (term549 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235901 A B P) (@lem8235900 A B P lt2 s f p)). Qed.
Lemma lem8235903 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : ((term529 A B P lt2 s f p) = (term530 A B P lt2 s f p)) = ((term528 A B P lt2 s f p) = (term549 A B P lt2 s f p)).
Proof. exact (MK_COMB (@lem8235891 A B P lt2 s f p) (@lem8235902 A B P lt2 s f p)). Qed.
Lemma lem8235904 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term528 A B P lt2 s f p) = (term549 A B P lt2 s f p).
Proof. exact (EQ_MP (@lem8235903 A B P lt2 s f p) (@lem8235878 A B P lt2 s f p)). Qed.
Lemma lem8235905 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term489 A B P lt2 s f p) = (term549 A B P lt2 s f p).
Proof. exact (TRANS (@lem8235874 A B P lt2 s f p) (@lem8235904 A B P lt2 s f p)). Qed.
Lemma lem8235906 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term490 A B P lt2 s p) = (term550 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8235905 A B P lt2 s f p)). Qed.
Lemma lem8235907 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235908 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term491 A B P lt2 s p) = (term551 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8235907 A B) (@lem8235906 A B P lt2 s p)). Qed.
Lemma lem8235910 {A B : Type'} (P : type1413 A B) : (term406 A B P) = (term407 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8235911 {A B P : Type'} (P' : type495 A B P) : (term458 A B P P') = (term459 A B P P').
Proof. exact (@lem8235910 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8235912 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term552 A B P lt2 s p) = (term553 A B P lt2 s p).
Proof. exact (@lem8235911 A B P (term554 A B P lt2 s p)). Qed.
Lemma lem8235913 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term555 A B P lt2 s p f) = (term548 A B P lt2 s f p).
Proof. exact (eq_refl (term555 A B P lt2 s p f)). Qed.
Lemma lem8235914 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8235915 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (z : type557 A B P) : (term556 A B P lt2 s p f z) = (term557 A B P lt2 s f p z).
Proof. exact (MK_COMB (@lem8235913 A B P lt2 s f p) (@lem8235914 A B P z)). Qed.
Lemma lem8235916 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term557 A B P lt2 s f p z) = (term546 A B P lt2 s z f p).
Proof. exact (eq_refl (term557 A B P lt2 s f p z)). Qed.
Lemma lem8235917 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term556 A B P lt2 s p f z) = (term546 A B P lt2 s z f p).
Proof. exact (TRANS (@lem8235915 A B P lt2 s f p z) (@lem8235916 A B P lt2 s z f p)). Qed.
Lemma lem8235918 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term558 A B P lt2 s p f) = (term548 A B P lt2 s f p).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8235917 A B P lt2 s z f p)). Qed.
Lemma lem8235919 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8235920 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term559 A B P lt2 s p f) = (term549 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8235919 A B P) (@lem8235918 A B P lt2 s f p)). Qed.
Lemma lem8235921 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term560 A B P lt2 s p) = (term550 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8235920 A B P lt2 s f p)). Qed.
Lemma lem8235922 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235923 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term552 A B P lt2 s p) = (term551 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8235922 A B) (@lem8235921 A B P lt2 s p)). Qed.
Lemma lem8235924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8235925 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term561 A B P lt2 s p) = (term562 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8235924) (@lem8235923 A B P lt2 s p)). Qed.
Lemma lem8235926 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term555 A B P lt2 s p f) = (term548 A B P lt2 s f p).
Proof. exact (eq_refl (term555 A B P lt2 s p f)). Qed.
Lemma lem8235927 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8235928 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) : (term563 A B P lt2 s p z f) = (term564 A B P lt2 s p z f).
Proof. exact (MK_COMB (@lem8235926 A B P lt2 s f p) (@lem8235927 A B P z f)). Qed.
Lemma lem8235929 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term564 A B P lt2 s p z f) = (term565 A B P lt2 s z f p).
Proof. exact (eq_refl (term564 A B P lt2 s p z f)). Qed.
Lemma lem8235930 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term563 A B P lt2 s p z f) = (term565 A B P lt2 s z f p).
Proof. exact (TRANS (@lem8235928 A B P lt2 s p z f) (@lem8235929 A B P lt2 s z f p)). Qed.
Lemma lem8235931 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term566 A B P lt2 s p z) = (term567 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8235930 A B P lt2 s z f p)). Qed.
Lemma lem8235932 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8235933 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term568 A B P lt2 s p z) = (term569 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8235932 A B) (@lem8235931 A B P lt2 s z p)). Qed.
Lemma lem8235934 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term570 A B P lt2 s p) = (term571 A B P lt2 s p).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8235933 A B P lt2 s z p)). Qed.
Lemma lem8235935 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8235936 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term553 A B P lt2 s p) = (term572 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8235935 A B P) (@lem8235934 A B P lt2 s p)). Qed.
Lemma lem8235937 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : ((term552 A B P lt2 s p) = (term553 A B P lt2 s p)) = ((term551 A B P lt2 s p) = (term572 A B P lt2 s p)).
Proof. exact (MK_COMB (@lem8235925 A B P lt2 s p) (@lem8235936 A B P lt2 s p)). Qed.
Lemma lem8235938 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term551 A B P lt2 s p) = (term572 A B P lt2 s p).
Proof. exact (EQ_MP (@lem8235937 A B P lt2 s p) (@lem8235912 A B P lt2 s p)). Qed.
Lemma lem8235940 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term491 A B P lt2 s p) = (term572 A B P lt2 s p).
Proof. exact (TRANS (@lem8235908 A B P lt2 s p) (@lem8235938 A B P lt2 s p)). Qed.
Lemma lem8235941 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term72 A B P lt2 s p) = (term572 A B P lt2 s p).
Proof. exact (TRANS (@lem8235708 A B P lt2 s p) (@lem8235940 A B P lt2 s p)). Qed.
Lemma lem8235942 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term72 A B P lt2 s p) : term572 A B P lt2 s p.
Proof. exact (EQ_MP (@lem8235941 A B P lt2 s p) (@lem8235331 A B P lt2 s p h1)). Qed.
Lemma lem8235945 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term573 A B P p g a) = (p g a).
Proof. exact (@lem16933 (p g a)). Qed.
Lemma lem8235948 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term573 A B P p f a) = (p f a).
Proof. exact (@lem16933 (p f a)). Qed.
Lemma lem8235955 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term574 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term117 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8235956 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term575 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235955 A B P lt2 s a f g z)). Qed.
Lemma lem8235957 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8235958 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term576 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235957 A) (@lem8235956 A B P lt2 s a f g)). Qed.
Lemma lem8235959 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term577 A B P f t g a) = (term577 A B P f t g a).
Proof. exact (eq_refl (term577 A B P f t g a)). Qed.
Lemma lem8235960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8235961 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term578 A B P lt2 s a f g) = (term579 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235960) (@lem8235958 A B P lt2 s a f g)). Qed.
Lemma lem8235962 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term580 A B P lt2 s f t g a) = (term581 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235961 A B P lt2 s a f g) (@lem8235959 A B P f t g a)). Qed.
Lemma lem8235963 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term582 A B P lt2 s f t g a) = (term580 A B P lt2 s f t g a).
Proof. exact (@lem17362 (term54 A B P lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8235964 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term582 A B P lt2 s f t g a) = (term581 A B P lt2 s f t g a).
Proof. exact (TRANS (@lem8235963 A B P lt2 s f t g a) (@lem8235962 A B P lt2 s f t g a)). Qed.
Lemma lem8235965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8235966 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term583 A B P p f a) = (term295 A B P p f a).
Proof. exact (MK_COMB (@lem8235965) (@lem8235948 A B P p f a)). Qed.
Lemma lem8235967 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term584 A B P p lt2 s f t g a) = (term585 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235966 A B P p f a) (@lem8235964 A B P lt2 s f t g a)). Qed.
Lemma lem8235968 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term586 A B P p lt2 s f t g a) = (term584 A B P p lt2 s f t g a).
Proof. exact (@lem17160 (term247 A B P p f a) (term269 A B P lt2 s f t g a)). Qed.
Lemma lem8235969 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term586 A B P p lt2 s f t g a) = (term585 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8235968 A B P p lt2 s f t g a) (@lem8235967 A B P p lt2 s f t g a)). Qed.
Lemma lem8235977 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term574 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term117 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8235978 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term575 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8235977 A B P lt2 s a f g z)). Qed.
Lemma lem8235979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8235980 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term576 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235979 A) (@lem8235978 A B P lt2 s a f g)). Qed.
Lemma lem8235981 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term587 A B P fixed t g a) = (term587 A B P fixed t g a).
Proof. exact (eq_refl (term587 A B P fixed t g a)). Qed.
Lemma lem8235982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8235983 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term578 A B P lt2 s a f g) = (term579 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8235982) (@lem8235980 A B P lt2 s a f g)). Qed.
Lemma lem8235984 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term588 A B P lt2 s f fixed t g a) = (term589 A B P lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8235983 A B P lt2 s a f g) (@lem8235981 A B P fixed t g a)). Qed.
Lemma lem8235985 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term590 A B P lt2 s f fixed t g a) = (term588 A B P lt2 s f fixed t g a).
Proof. exact (@lem17362 (term54 A B P lt2 s a f g) (fixed = (t g a))). Qed.
Lemma lem8235986 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term590 A B P lt2 s f fixed t g a) = (term589 A B P lt2 s f fixed t g a).
Proof. exact (TRANS (@lem8235985 A B P lt2 s f fixed t g a) (@lem8235984 A B P lt2 s f fixed t g a)). Qed.
Lemma lem8235988 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term591 A B P p f a) = (term591 A B P p f a).
Proof. exact (eq_refl (term591 A B P p f a)). Qed.
Lemma lem8235989 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term592 A B P p lt2 s f fixed t g a) = (term593 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8235988 A B P p f a) (@lem8235986 A B P lt2 s f fixed t g a)). Qed.
Lemma lem8235990 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term594 A B P p lt2 s f fixed t g a) = (term592 A B P p lt2 s f fixed t g a).
Proof. exact (@lem17160 (p f a) (term272 A B P lt2 s f fixed t g a)). Qed.
Lemma lem8235991 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term594 A B P p lt2 s f fixed t g a) = (term593 A B P p lt2 s f fixed t g a).
Proof. exact (TRANS (@lem8235990 A B P p lt2 s f fixed t g a) (@lem8235989 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8235992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8235993 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term595 A B P p lt2 s f t g a) = (term596 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8235992) (@lem8235969 A B P p lt2 s f t g a)). Qed.
Lemma lem8235994 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term597 A B P p lt2 s f fixed t g a) = (term598 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8235993 A B P p lt2 s f t g a) (@lem8235991 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8235995 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term599 A B P p lt2 s f fixed t g a) = (term597 A B P p lt2 s f fixed t g a).
Proof. exact (@lem17045 (term270 A B P p lt2 s f t g a) (term273 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8235996 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term599 A B P p lt2 s f fixed t g a) = (term598 A B P p lt2 s f fixed t g a).
Proof. exact (TRANS (@lem8235995 A B P p lt2 s f fixed t g a) (@lem8235994 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8235997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8235998 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term583 A B P p g a) = (term295 A B P p g a).
Proof. exact (MK_COMB (@lem8235997) (@lem8235945 A B P p g a)). Qed.
Lemma lem8235999 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term600 A B P p lt2 s f fixed t g a) = (term601 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8235998 A B P p g a) (@lem8235996 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236000 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term602 A B P p lt2 s f fixed t g a) = (term600 A B P p lt2 s f fixed t g a).
Proof. exact (@lem17160 (term247 A B P p g a) (term274 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236001 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term602 A B P p lt2 s f fixed t g a) = (term601 A B P p lt2 s f fixed t g a).
Proof. exact (TRANS (@lem8236000 A B P p lt2 s f fixed t g a) (@lem8235999 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236005 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term573 A B P p f a) = (p f a).
Proof. exact (@lem16933 (p f a)). Qed.
Lemma lem8236012 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term279 A B P lt2 s a f g z) = (term574 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term117 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8236013 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term280 A B P lt2 s a f g) = (term575 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8236012 A B P lt2 s a f g z)). Qed.
Lemma lem8236014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8236015 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term54 A B P lt2 s a f g) = (term576 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236014 A) (@lem8236013 A B P lt2 s a f g)). Qed.
Lemma lem8236016 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term603 A B P t f a fixed) = (term603 A B P t f a fixed).
Proof. exact (eq_refl (term603 A B P t f a fixed)). Qed.
Lemma lem8236017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236018 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term578 A B P lt2 s a f g) = (term579 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236017) (@lem8236015 A B P lt2 s a f g)). Qed.
Lemma lem8236019 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term604 A B P lt2 s g t f a fixed) = (term605 A B P lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236018 A B P lt2 s a f g) (@lem8236016 A B P t f a fixed)). Qed.
Lemma lem8236020 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term606 A B P lt2 s g t f a fixed) = (term604 A B P lt2 s g t f a fixed).
Proof. exact (@lem17362 (term54 A B P lt2 s a f g) ((t f a) = fixed)). Qed.
Lemma lem8236021 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term606 A B P lt2 s g t f a fixed) = (term605 A B P lt2 s g t f a fixed).
Proof. exact (TRANS (@lem8236020 A B P lt2 s g t f a fixed) (@lem8236019 A B P lt2 s g t f a fixed)). Qed.
Lemma lem8236022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236023 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term583 A B P p f a) = (term295 A B P p f a).
Proof. exact (MK_COMB (@lem8236022) (@lem8236005 A B P p f a)). Qed.
Lemma lem8236024 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term607 A B P p lt2 s g t f a fixed) = (term608 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236023 A B P p f a) (@lem8236021 A B P lt2 s g t f a fixed)). Qed.
Lemma lem8236025 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term609 A B P p lt2 s g t f a fixed) = (term607 A B P p lt2 s g t f a fixed).
Proof. exact (@lem17160 (term247 A B P p f a) (term258 A B P lt2 s g t f a fixed)). Qed.
Lemma lem8236026 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term609 A B P p lt2 s g t f a fixed) = (term608 A B P p lt2 s g t f a fixed).
Proof. exact (TRANS (@lem8236025 A B P p lt2 s g t f a fixed) (@lem8236024 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236028 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term591 A B P p g a) = (term591 A B P p g a).
Proof. exact (eq_refl (term591 A B P p g a)). Qed.
Lemma lem8236029 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term610 A B P p lt2 s g t f a fixed) = (term611 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236028 A B P p g a) (@lem8236026 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236030 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term612 A B P p lt2 s g t f a fixed) = (term610 A B P p lt2 s g t f a fixed).
Proof. exact (@lem17160 (p g a) (term261 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236031 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term612 A B P p lt2 s g t f a fixed) = (term611 A B P p lt2 s g t f a fixed).
Proof. exact (TRANS (@lem8236030 A B P p lt2 s g t f a fixed) (@lem8236029 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236033 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term613 A B P p lt2 s f fixed t g a) = (term614 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236032) (@lem8236001 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236034 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term615 A B P p lt2 s g t f a fixed) = (term616 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236033 A B P p lt2 s f fixed t g a) (@lem8236031 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236035 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term330 A B P p lt2 s g t f a fixed) = (term615 A B P p lt2 s g t f a fixed).
Proof. exact (@lem17045 (term282 A B P p lt2 s f fixed t g a) (term281 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236184 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term330 A B P p lt2 s g t f a fixed) = (term616 A B P p lt2 s g t f a fixed).
Proof. exact (TRANS (@lem8236035 A B P p lt2 s g t f a fixed) (@lem8236034 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236185 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term330 A B P p lt2 s g t f a fixed) : term616 A B P p lt2 s g t f a fixed.
Proof. exact (EQ_MP (@lem8236184 A B P p lt2 s g t f a fixed) (@lem8235336 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8236186 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term569 A B P lt2 s z p.
Proof. exact (h1). Qed.
Lemma lem8236187 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term477 A B P p lt2 s z' t.
Proof. exact (h1). Qed.
Lemma lem8236188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236189 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236197 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236196 (A -> B) (P -> B) f x). Qed.
Lemma lem8236198 {A B P : Type'} (t : type558 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> B) t f).
Proof. exact (@lem8236197 A B P t f). Qed.
Lemma lem8236199 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236200 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> B) t f a).
Proof. exact (MK_COMB (@lem8236198 A B P t f) (@lem8236199 P a)). Qed.
Lemma lem8236202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236203 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236202 P B f x). Qed.
Lemma lem8236204 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t f a) = (term617 A B P t f a).
Proof. exact (@lem8236203 B P (@I ((A -> B) -> P -> B) t f) a). Qed.
Lemma lem8236206 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (term617 A B P t f a).
Proof. exact (TRANS (@lem8236200 A B P t f a) (@lem8236204 A B P t f a)). Qed.
Lemma lem8236207 {B : Type'} (fixed : B) : fixed = fixed.
Proof. exact (eq_refl fixed). Qed.
Lemma lem8236208 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term618 A B P t f a).
Proof. exact (MK_COMB (@lem8236189 B) (@lem8236206 A B P t f a)). Qed.
Lemma lem8236209 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : ((t f a) = fixed) = ((term617 A B P t f a) = fixed).
Proof. exact (MK_COMB (@lem8236208 A B P t f a) (@lem8236207 B fixed)). Qed.
Lemma lem8236210 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term603 A B P t f a fixed) = (term619 A B P t f a fixed).
Proof. exact (MK_COMB (@lem8236188) (@lem8236209 A B P t f a fixed)). Qed.
Lemma lem8236211 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236216 A B f x). Qed.
Lemma lem8236219 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8236217 A B f z). Qed.
Lemma lem8236224 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236224 A B f x). Qed.
Lemma lem8236227 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8236225 A B g z). Qed.
Lemma lem8236228 {A B : Type'} (f : A -> B) (z : A) : (term620 A B f z) = (term621 A B f z).
Proof. exact (MK_COMB (@lem8236211 B) (@lem8236219 A B f z)). Qed.
Lemma lem8236229 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8236228 A B f z) (@lem8236227 A B g z)). Qed.
Lemma lem8236230 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236238 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236237 P A f x). Qed.
Lemma lem8236240 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8236238 A P s a). Qed.
Lemma lem8236241 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8236242 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term622 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236241 A lt2 z) (@lem8236240 A P s a)). Qed.
Lemma lem8236244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236245 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8236244 A (A -> Prop) f x). Qed.
Lemma lem8236246 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8236245 A lt2 z). Qed.
Lemma lem8236247 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8236248 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term623 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236246 A lt2 z) (@lem8236247 A P s a)). Qed.
Lemma lem8236250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236251 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8236250 A Prop f x). Qed.
Lemma lem8236252 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term623 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (@lem8236251 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8236253 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236248 A P lt2 z s a) (@lem8236252 A P lt2 z s a)). Qed.
Lemma lem8236254 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236242 A P lt2 z s a) (@lem8236253 A P lt2 z s a)). Qed.
Lemma lem8236255 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term625 A P lt2 z s a) = (term626 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236230) (@lem8236254 A P lt2 z s a)). Qed.
Lemma lem8236256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236257 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term627 A P lt2 z s a) = (term628 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236256) (@lem8236255 A P lt2 z s a)). Qed.
Lemma lem8236258 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term574 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8236257 A P lt2 z s a) (@lem8236229 A B f g z)). Qed.
Lemma lem8236259 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term575 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8236258 A B P lt2 s a f g z)). Qed.
Lemma lem8236260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8236261 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term576 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236260 A) (@lem8236259 A B P lt2 s a f g)). Qed.
Lemma lem8236262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236263 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term579 A B P lt2 s a f g) = (term632 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236262) (@lem8236261 A B P lt2 s a f g)). Qed.
Lemma lem8236264 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term605 A B P lt2 s g t f a fixed) = (term633 A B P lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236263 A B P lt2 s a f g) (@lem8236210 A B P t f a fixed)). Qed.
Lemma lem8236271 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236272 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236271 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236273 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236272 A B P p f). Qed.
Lemma lem8236274 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236275 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236273 A B P p f) (@lem8236274 P a)). Qed.
Lemma lem8236277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236278 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236277 P Prop f x). Qed.
Lemma lem8236279 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236278 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236281 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236275 A B P p f a) (@lem8236279 A B P p f a)). Qed.
Lemma lem8236282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236283 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term295 A B P p f a) = (term635 A B P p f a).
Proof. exact (MK_COMB (@lem8236282) (@lem8236281 A B P p f a)). Qed.
Lemma lem8236284 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term608 A B P p lt2 s g t f a fixed) = (term636 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236283 A B P p f a) (@lem8236264 A B P lt2 s g t f a fixed)). Qed.
Lemma lem8236285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236292 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236293 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236292 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236294 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8236293 A B P p g). Qed.
Lemma lem8236295 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236296 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8236294 A B P p g) (@lem8236295 P a)). Qed.
Lemma lem8236298 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236299 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236298 P Prop f x). Qed.
Lemma lem8236300 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term634 A B P p g a).
Proof. exact (@lem8236299 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8236302 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term634 A B P p g a).
Proof. exact (TRANS (@lem8236296 A B P p g a) (@lem8236300 A B P p g a)). Qed.
Lemma lem8236303 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term247 A B P p g a) = (term637 A B P p g a).
Proof. exact (MK_COMB (@lem8236285) (@lem8236302 A B P p g a)). Qed.
Lemma lem8236304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236305 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term591 A B P p g a) = (term638 A B P p g a).
Proof. exact (MK_COMB (@lem8236304) (@lem8236303 A B P p g a)). Qed.
Lemma lem8236306 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term611 A B P p lt2 s g t f a fixed) = (term639 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236305 A B P p g a) (@lem8236284 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236317 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236316 (A -> B) (P -> B) f x). Qed.
Lemma lem8236318 {A B P : Type'} (t : type558 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> B) t g).
Proof. exact (@lem8236317 A B P t g). Qed.
Lemma lem8236319 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236320 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> B) t g a).
Proof. exact (MK_COMB (@lem8236318 A B P t g) (@lem8236319 P a)). Qed.
Lemma lem8236322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236323 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236322 P B f x). Qed.
Lemma lem8236324 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t g a) = (term617 A B P t g a).
Proof. exact (@lem8236323 B P (@I ((A -> B) -> P -> B) t g) a). Qed.
Lemma lem8236326 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (term617 A B P t g a).
Proof. exact (TRANS (@lem8236320 A B P t g a) (@lem8236324 A B P t g a)). Qed.
Lemma lem8236327 {B : Type'} (fixed : B) : (@eq B fixed) = (@eq B fixed).
Proof. exact (eq_refl (@eq B fixed)). Qed.
Lemma lem8236328 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (fixed = (t g a)) = (fixed = (term617 A B P t g a)).
Proof. exact (MK_COMB (@lem8236327 B fixed) (@lem8236326 A B P t g a)). Qed.
Lemma lem8236329 {A B P : Type'} (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term587 A B P fixed t g a) = (term640 A B P fixed t g a).
Proof. exact (MK_COMB (@lem8236307) (@lem8236328 A B P fixed t g a)). Qed.
Lemma lem8236330 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236335 A B f x). Qed.
Lemma lem8236338 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8236336 A B f z). Qed.
Lemma lem8236343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236344 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236343 A B f x). Qed.
Lemma lem8236346 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8236344 A B g z). Qed.
Lemma lem8236347 {A B : Type'} (f : A -> B) (z : A) : (term620 A B f z) = (term621 A B f z).
Proof. exact (MK_COMB (@lem8236330 B) (@lem8236338 A B f z)). Qed.
Lemma lem8236348 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8236347 A B f z) (@lem8236346 A B g z)). Qed.
Lemma lem8236349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236357 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236356 P A f x). Qed.
Lemma lem8236359 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8236357 A P s a). Qed.
Lemma lem8236360 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8236361 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term622 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236360 A lt2 z) (@lem8236359 A P s a)). Qed.
Lemma lem8236363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236364 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8236363 A (A -> Prop) f x). Qed.
Lemma lem8236365 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8236364 A lt2 z). Qed.
Lemma lem8236366 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8236367 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term623 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236365 A lt2 z) (@lem8236366 A P s a)). Qed.
Lemma lem8236369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236370 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8236369 A Prop f x). Qed.
Lemma lem8236371 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term623 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (@lem8236370 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8236372 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236367 A P lt2 z s a) (@lem8236371 A P lt2 z s a)). Qed.
Lemma lem8236373 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236361 A P lt2 z s a) (@lem8236372 A P lt2 z s a)). Qed.
Lemma lem8236374 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term625 A P lt2 z s a) = (term626 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236349) (@lem8236373 A P lt2 z s a)). Qed.
Lemma lem8236375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236376 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term627 A P lt2 z s a) = (term628 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236375) (@lem8236374 A P lt2 z s a)). Qed.
Lemma lem8236377 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term574 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8236376 A P lt2 z s a) (@lem8236348 A B f g z)). Qed.
Lemma lem8236378 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term575 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8236377 A B P lt2 s a f g z)). Qed.
Lemma lem8236379 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8236380 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term576 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236379 A) (@lem8236378 A B P lt2 s a f g)). Qed.
Lemma lem8236381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236382 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term579 A B P lt2 s a f g) = (term632 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236381) (@lem8236380 A B P lt2 s a f g)). Qed.
Lemma lem8236383 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term589 A B P lt2 s f fixed t g a) = (term641 A B P lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236382 A B P lt2 s a f g) (@lem8236329 A B P fixed t g a)). Qed.
Lemma lem8236384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236392 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236391 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236393 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236392 A B P p f). Qed.
Lemma lem8236394 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236395 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236393 A B P p f) (@lem8236394 P a)). Qed.
Lemma lem8236397 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236398 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236397 P Prop f x). Qed.
Lemma lem8236399 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236398 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236401 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236395 A B P p f a) (@lem8236399 A B P p f a)). Qed.
Lemma lem8236402 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term247 A B P p f a) = (term637 A B P p f a).
Proof. exact (MK_COMB (@lem8236384) (@lem8236401 A B P p f a)). Qed.
Lemma lem8236403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236404 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term591 A B P p f a) = (term638 A B P p f a).
Proof. exact (MK_COMB (@lem8236403) (@lem8236402 A B P p f a)). Qed.
Lemma lem8236405 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term593 A B P p lt2 s f fixed t g a) = (term642 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236404 A B P p f a) (@lem8236383 A B P lt2 s f fixed t g a)). Qed.
Lemma lem8236406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236407 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236415 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236414 (A -> B) (P -> B) f x). Qed.
Lemma lem8236416 {A B P : Type'} (t : type558 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> B) t f).
Proof. exact (@lem8236415 A B P t f). Qed.
Lemma lem8236417 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236418 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> B) t f a).
Proof. exact (MK_COMB (@lem8236416 A B P t f) (@lem8236417 P a)). Qed.
Lemma lem8236420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236421 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236420 P B f x). Qed.
Lemma lem8236422 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t f a) = (term617 A B P t f a).
Proof. exact (@lem8236421 B P (@I ((A -> B) -> P -> B) t f) a). Qed.
Lemma lem8236424 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (term617 A B P t f a).
Proof. exact (TRANS (@lem8236418 A B P t f a) (@lem8236422 A B P t f a)). Qed.
Lemma lem8236431 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236432 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236431 (A -> B) (P -> B) f x). Qed.
Lemma lem8236433 {A B P : Type'} (t : type558 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> B) t g).
Proof. exact (@lem8236432 A B P t g). Qed.
Lemma lem8236434 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236435 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> B) t g a).
Proof. exact (MK_COMB (@lem8236433 A B P t g) (@lem8236434 P a)). Qed.
Lemma lem8236437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236438 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236437 P B f x). Qed.
Lemma lem8236439 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t g a) = (term617 A B P t g a).
Proof. exact (@lem8236438 B P (@I ((A -> B) -> P -> B) t g) a). Qed.
Lemma lem8236441 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (term617 A B P t g a).
Proof. exact (TRANS (@lem8236435 A B P t g a) (@lem8236439 A B P t g a)). Qed.
Lemma lem8236442 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term618 A B P t f a).
Proof. exact (MK_COMB (@lem8236407 B) (@lem8236424 A B P t f a)). Qed.
Lemma lem8236443 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((term617 A B P t f a) = (term617 A B P t g a)).
Proof. exact (MK_COMB (@lem8236442 A B P t f a) (@lem8236441 A B P t g a)). Qed.
Lemma lem8236444 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term577 A B P f t g a) = (term643 A B P f t g a).
Proof. exact (MK_COMB (@lem8236406) (@lem8236443 A B P f t g a)). Qed.
Lemma lem8236445 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236451 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236450 A B f x). Qed.
Lemma lem8236453 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8236451 A B f z). Qed.
Lemma lem8236458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236459 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236458 A B f x). Qed.
Lemma lem8236461 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8236459 A B g z). Qed.
Lemma lem8236462 {A B : Type'} (f : A -> B) (z : A) : (term620 A B f z) = (term621 A B f z).
Proof. exact (MK_COMB (@lem8236445 B) (@lem8236453 A B f z)). Qed.
Lemma lem8236463 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8236462 A B f z) (@lem8236461 A B g z)). Qed.
Lemma lem8236464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236472 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236471 P A f x). Qed.
Lemma lem8236474 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8236472 A P s a). Qed.
Lemma lem8236475 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8236476 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term622 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236475 A lt2 z) (@lem8236474 A P s a)). Qed.
Lemma lem8236478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236479 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8236478 A (A -> Prop) f x). Qed.
Lemma lem8236480 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8236479 A lt2 z). Qed.
Lemma lem8236481 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8236482 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term623 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236480 A lt2 z) (@lem8236481 A P s a)). Qed.
Lemma lem8236484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236485 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8236484 A Prop f x). Qed.
Lemma lem8236486 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term623 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (@lem8236485 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8236487 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term622 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236482 A P lt2 z s a) (@lem8236486 A P lt2 z s a)). Qed.
Lemma lem8236488 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term117 A P lt2 z s a) = (term624 A P lt2 z s a).
Proof. exact (TRANS (@lem8236476 A P lt2 z s a) (@lem8236487 A P lt2 z s a)). Qed.
Lemma lem8236489 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term625 A P lt2 z s a) = (term626 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236464) (@lem8236488 A P lt2 z s a)). Qed.
Lemma lem8236490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236491 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term627 A P lt2 z s a) = (term628 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8236490) (@lem8236489 A P lt2 z s a)). Qed.
Lemma lem8236492 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term574 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8236491 A P lt2 z s a) (@lem8236463 A B f g z)). Qed.
Lemma lem8236493 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term575 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8236492 A B P lt2 s a f g z)). Qed.
Lemma lem8236494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8236495 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term576 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236494 A) (@lem8236493 A B P lt2 s a f g)). Qed.
Lemma lem8236496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236497 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term579 A B P lt2 s a f g) = (term632 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8236496) (@lem8236495 A B P lt2 s a f g)). Qed.
Lemma lem8236498 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term581 A B P lt2 s f t g a) = (term644 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8236497 A B P lt2 s a f g) (@lem8236444 A B P f t g a)). Qed.
Lemma lem8236505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236506 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236505 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236507 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236506 A B P p f). Qed.
Lemma lem8236508 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236509 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236507 A B P p f) (@lem8236508 P a)). Qed.
Lemma lem8236511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236512 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236511 P Prop f x). Qed.
Lemma lem8236513 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236512 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236515 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236509 A B P p f a) (@lem8236513 A B P p f a)). Qed.
Lemma lem8236516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236517 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term295 A B P p f a) = (term635 A B P p f a).
Proof. exact (MK_COMB (@lem8236516) (@lem8236515 A B P p f a)). Qed.
Lemma lem8236518 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term585 A B P p lt2 s f t g a) = (term645 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8236517 A B P p f a) (@lem8236498 A B P lt2 s f t g a)). Qed.
Lemma lem8236519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236520 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term596 A B P p lt2 s f t g a) = (term646 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8236519) (@lem8236518 A B P p lt2 s f t g a)). Qed.
Lemma lem8236521 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term598 A B P p lt2 s f fixed t g a) = (term647 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236520 A B P p lt2 s f t g a) (@lem8236405 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236528 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236529 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236528 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236530 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8236529 A B P p g). Qed.
Lemma lem8236531 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236532 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8236530 A B P p g) (@lem8236531 P a)). Qed.
Lemma lem8236534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236535 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236534 P Prop f x). Qed.
Lemma lem8236536 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term634 A B P p g a).
Proof. exact (@lem8236535 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8236538 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term634 A B P p g a).
Proof. exact (TRANS (@lem8236532 A B P p g a) (@lem8236536 A B P p g a)). Qed.
Lemma lem8236539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236540 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term295 A B P p g a) = (term635 A B P p g a).
Proof. exact (MK_COMB (@lem8236539) (@lem8236538 A B P p g a)). Qed.
Lemma lem8236541 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term601 A B P p lt2 s f fixed t g a) = (term648 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236540 A B P p g a) (@lem8236521 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236543 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) : (term614 A B P p lt2 s f fixed t g a) = (term649 A B P p lt2 s f fixed t g a).
Proof. exact (MK_COMB (@lem8236542) (@lem8236541 A B P p lt2 s f fixed t g a)). Qed.
Lemma lem8236544 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) : (term616 A B P p lt2 s g t f a fixed) = (term650 A B P p lt2 s g t f a fixed).
Proof. exact (MK_COMB (@lem8236543 A B P p lt2 s f fixed t g a) (@lem8236306 A B P p lt2 s g t f a fixed)). Qed.
Lemma lem8236545 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term330 A B P p lt2 s g t f a fixed) : term650 A B P p lt2 s g t f a fixed.
Proof. exact (EQ_MP (@lem8236544 A B P p lt2 s g t f a fixed) (@lem8236185 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8236552 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236553 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236552 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236554 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8236553 A B P p g). Qed.
Lemma lem8236555 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236556 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8236554 A B P p g) (@lem8236555 P a)). Qed.
Lemma lem8236558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236559 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236558 P Prop f x). Qed.
Lemma lem8236560 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term634 A B P p g a).
Proof. exact (@lem8236559 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8236562 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term634 A B P p g a).
Proof. exact (TRANS (@lem8236556 A B P p g a) (@lem8236560 A B P p g a)). Qed.
Lemma lem8236563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236571 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236570 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236572 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236571 A B P p f). Qed.
Lemma lem8236573 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236574 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236572 A B P p f) (@lem8236573 P a)). Qed.
Lemma lem8236576 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236577 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236576 P Prop f x). Qed.
Lemma lem8236578 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236577 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236580 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236574 A B P p f a) (@lem8236578 A B P p f a)). Qed.
Lemma lem8236581 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term247 A B P p f a) = (term637 A B P p f a).
Proof. exact (MK_COMB (@lem8236563) (@lem8236580 A B P p f a)). Qed.
Lemma lem8236582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236583 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term651 A B P p f a).
Proof. exact (MK_COMB (@lem8236582) (@lem8236581 A B P p f a)). Qed.
Lemma lem8236584 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term652 A B P f p g a) = (term653 A B P f p g a).
Proof. exact (MK_COMB (@lem8236583 A B P p f a) (@lem8236562 A B P p g a)). Qed.
Lemma lem8236585 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236592 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236593 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236592 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236594 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8236593 A B P p g). Qed.
Lemma lem8236595 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236596 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8236594 A B P p g) (@lem8236595 P a)). Qed.
Lemma lem8236598 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236599 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236598 P Prop f x). Qed.
Lemma lem8236600 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term634 A B P p g a).
Proof. exact (@lem8236599 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8236602 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term634 A B P p g a).
Proof. exact (TRANS (@lem8236596 A B P p g a) (@lem8236600 A B P p g a)). Qed.
Lemma lem8236603 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term247 A B P p g a) = (term637 A B P p g a).
Proof. exact (MK_COMB (@lem8236585) (@lem8236602 A B P p g a)). Qed.
Lemma lem8236610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236611 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236610 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236612 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236611 A B P p f). Qed.
Lemma lem8236613 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236614 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236612 A B P p f) (@lem8236613 P a)). Qed.
Lemma lem8236616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236617 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236616 P Prop f x). Qed.
Lemma lem8236618 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236617 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236620 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236614 A B P p f a) (@lem8236618 A B P p f a)). Qed.
Lemma lem8236621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236622 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term265 A B P p f a) = (term654 A B P p f a).
Proof. exact (MK_COMB (@lem8236621) (@lem8236620 A B P p f a)). Qed.
Lemma lem8236623 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term655 A B P f p g a) = (term656 A B P f p g a).
Proof. exact (MK_COMB (@lem8236622 A B P p f a) (@lem8236603 A B P p g a)). Qed.
Lemma lem8236624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236625 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term657 A B P f p g a) = (term658 A B P f p g a).
Proof. exact (MK_COMB (@lem8236624) (@lem8236623 A B P f p g a)). Qed.
Lemma lem8236626 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term481 A B P f p g a) = (term659 A B P f p g a).
Proof. exact (MK_COMB (@lem8236625 A B P f p g a) (@lem8236584 A B P f p g a)). Qed.
Lemma lem8236627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236628 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236629 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8236638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236639 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236638 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236640 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8236639 A B P z f). Qed.
Lemma lem8236641 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236642 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8236640 A B P z f) (@lem8236641 A B g)). Qed.
Lemma lem8236644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236645 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236644 (A -> B) (P -> A) f x). Qed.
Lemma lem8236646 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term660 A B P z f g).
Proof. exact (@lem8236645 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8236647 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term660 A B P z f g).
Proof. exact (TRANS (@lem8236642 A B P z f g) (@lem8236646 A B P z f g)). Qed.
Lemma lem8236648 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236649 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term661 A B P z f g a).
Proof. exact (MK_COMB (@lem8236647 A B P z f g) (@lem8236648 P a)). Qed.
Lemma lem8236651 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236652 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236651 P A f x). Qed.
Lemma lem8236653 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z f g a) = (term662 A B P z f g a).
Proof. exact (@lem8236652 A P (term660 A B P z f g) a). Qed.
Lemma lem8236655 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term662 A B P z f g a).
Proof. exact (TRANS (@lem8236649 A B P z f g a) (@lem8236653 A B P z f g a)). Qed.
Lemma lem8236656 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term663 A B P z f g a) = (term664 A B P z f g a).
Proof. exact (MK_COMB (@lem8236629 A B f) (@lem8236655 A B P z f g a)). Qed.
Lemma lem8236658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236659 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236658 A B f x). Qed.
Lemma lem8236660 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term664 A B P z f g a) = (term665 A B P z f g a).
Proof. exact (@lem8236659 A B f (term662 A B P z f g a)). Qed.
Lemma lem8236661 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term663 A B P z f g a) = (term665 A B P z f g a).
Proof. exact (TRANS (@lem8236656 A B P z f g a) (@lem8236660 A B P z f g a)). Qed.
Lemma lem8236662 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236671 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236672 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236671 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236673 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8236672 A B P z f). Qed.
Lemma lem8236674 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236675 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8236673 A B P z f) (@lem8236674 A B g)). Qed.
Lemma lem8236677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236678 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236677 (A -> B) (P -> A) f x). Qed.
Lemma lem8236679 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term660 A B P z f g).
Proof. exact (@lem8236678 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8236680 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term660 A B P z f g).
Proof. exact (TRANS (@lem8236675 A B P z f g) (@lem8236679 A B P z f g)). Qed.
Lemma lem8236681 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236682 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term661 A B P z f g a).
Proof. exact (MK_COMB (@lem8236680 A B P z f g) (@lem8236681 P a)). Qed.
Lemma lem8236684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236685 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236684 P A f x). Qed.
Lemma lem8236686 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z f g a) = (term662 A B P z f g a).
Proof. exact (@lem8236685 A P (term660 A B P z f g) a). Qed.
Lemma lem8236688 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term662 A B P z f g a).
Proof. exact (TRANS (@lem8236682 A B P z f g a) (@lem8236686 A B P z f g a)). Qed.
Lemma lem8236689 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term666 A B P z f g a) = (term667 A B P z f g a).
Proof. exact (MK_COMB (@lem8236662 A B g) (@lem8236688 A B P z f g a)). Qed.
Lemma lem8236691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236691 A B f x). Qed.
Lemma lem8236693 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term667 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (@lem8236692 A B g (term662 A B P z f g a)). Qed.
Lemma lem8236694 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term666 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (TRANS (@lem8236689 A B P z f g a) (@lem8236693 A B P z f g a)). Qed.
Lemma lem8236695 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term669 A B P z f g a) = (term670 A B P z f g a).
Proof. exact (MK_COMB (@lem8236628 B) (@lem8236661 A B P z f g a)). Qed.
Lemma lem8236696 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term663 A B P z f g a) = (term666 A B P z f g a)) = ((term665 A B P z f g a) = (term668 A B P z f g a)).
Proof. exact (MK_COMB (@lem8236695 A B P z f g a) (@lem8236694 A B P z f g a)). Qed.
Lemma lem8236697 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term671 A B P z f g a) = (term672 A B P z f g a).
Proof. exact (MK_COMB (@lem8236627) (@lem8236696 A B P z f g a)). Qed.
Lemma lem8236698 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8236707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236708 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236707 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236709 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8236708 A B P z f). Qed.
Lemma lem8236710 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236711 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8236709 A B P z f) (@lem8236710 A B g)). Qed.
Lemma lem8236713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236714 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236713 (A -> B) (P -> A) f x). Qed.
Lemma lem8236715 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term660 A B P z f g).
Proof. exact (@lem8236714 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8236716 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term660 A B P z f g).
Proof. exact (TRANS (@lem8236711 A B P z f g) (@lem8236715 A B P z f g)). Qed.
Lemma lem8236717 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236718 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term661 A B P z f g a).
Proof. exact (MK_COMB (@lem8236716 A B P z f g) (@lem8236717 P a)). Qed.
Lemma lem8236720 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236721 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236720 P A f x). Qed.
Lemma lem8236722 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z f g a) = (term662 A B P z f g a).
Proof. exact (@lem8236721 A P (term660 A B P z f g) a). Qed.
Lemma lem8236724 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term662 A B P z f g a).
Proof. exact (TRANS (@lem8236718 A B P z f g a) (@lem8236722 A B P z f g a)). Qed.
Lemma lem8236729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236730 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236729 P A f x). Qed.
Lemma lem8236732 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8236730 A P s a). Qed.
Lemma lem8236733 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term673 A B P lt2 z f g a) = (term674 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8236698 A lt2) (@lem8236724 A B P z f g a)). Qed.
Lemma lem8236734 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term675 A B P lt2 z f g s a) = (term676 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8236733 A B P lt2 z f g a) (@lem8236732 A P s a)). Qed.
Lemma lem8236736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236737 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8236736 A (A -> Prop) f x). Qed.
Lemma lem8236738 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term674 A B P lt2 z f g a) = (term677 A B P lt2 z f g a).
Proof. exact (@lem8236737 A lt2 (term662 A B P z f g a)). Qed.
Lemma lem8236739 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8236740 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term676 A B P lt2 z f g s a) = (term678 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8236738 A B P lt2 z f g a) (@lem8236739 A P s a)). Qed.
Lemma lem8236742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236743 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8236742 A Prop f x). Qed.
Lemma lem8236744 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term678 A B P lt2 z f g s a) = (term679 A B P lt2 z f g s a).
Proof. exact (@lem8236743 A (term677 A B P lt2 z f g a) (@I (P -> A) s a)). Qed.
Lemma lem8236745 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term676 A B P lt2 z f g s a) = (term679 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8236740 A B P lt2 z f g s a) (@lem8236744 A B P lt2 z f g s a)). Qed.
Lemma lem8236746 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term675 A B P lt2 z f g s a) = (term679 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8236734 A B P lt2 z f g s a) (@lem8236745 A B P lt2 z f g s a)). Qed.
Lemma lem8236747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236748 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term680 A B P lt2 z f g s a) = (term681 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8236747) (@lem8236746 A B P lt2 z f g s a)). Qed.
Lemma lem8236749 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term682 A B P lt2 s z f g a) = (term683 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8236748 A B P lt2 z f g s a) (@lem8236697 A B P z f g a)). Qed.
Lemma lem8236750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236751 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term684 A B P lt2 s z f g a) = (term685 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8236750) (@lem8236749 A B P lt2 s z f g a)). Qed.
Lemma lem8236752 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term686 A B P lt2 s z f p g a) = (term687 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8236751 A B P lt2 s z f g a) (@lem8236626 A B P f p g a)). Qed.
Lemma lem8236753 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term688 A B P lt2 s z f p g) = (term689 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8236752 A B P lt2 s z f p g a)). Qed.
Lemma lem8236754 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8236755 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term690 A B P lt2 s z f p g) = (term691 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8236754 P) (@lem8236753 A B P lt2 s z f p g)). Qed.
Lemma lem8236756 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term692 A B P lt2 s z f p) = (term693 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8236755 A B P lt2 s z f p g)). Qed.
Lemma lem8236757 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8236758 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term565 A B P lt2 s z f p) = (term694 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8236757 A B) (@lem8236756 A B P lt2 s z f p)). Qed.
Lemma lem8236759 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term567 A B P lt2 s z p) = (term695 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8236758 A B P lt2 s z f p)). Qed.
Lemma lem8236760 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8236761 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term569 A B P lt2 s z p) = (term696 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8236760 A B) (@lem8236759 A B P lt2 s z p)). Qed.
Lemma lem8236762 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term696 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8236761 A B P lt2 s z p) (@lem8236186 A B P lt2 s z p h1)). Qed.
Lemma lem8236763 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236771 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236770 (A -> B) (P -> B) f x). Qed.
Lemma lem8236772 {A B P : Type'} (t : type558 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> B) t f).
Proof. exact (@lem8236771 A B P t f). Qed.
Lemma lem8236773 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236774 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> B) t f a).
Proof. exact (MK_COMB (@lem8236772 A B P t f) (@lem8236773 P a)). Qed.
Lemma lem8236776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236777 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236776 P B f x). Qed.
Lemma lem8236778 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t f a) = (term617 A B P t f a).
Proof. exact (@lem8236777 B P (@I ((A -> B) -> P -> B) t f) a). Qed.
Lemma lem8236780 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (t f a) = (term617 A B P t f a).
Proof. exact (TRANS (@lem8236774 A B P t f a) (@lem8236778 A B P t f a)). Qed.
Lemma lem8236787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236788 {A B P : Type'} (f : type558 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> B) f x).
Proof. exact (@lem8236787 (A -> B) (P -> B) f x). Qed.
Lemma lem8236789 {A B P : Type'} (t : type558 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> B) t g).
Proof. exact (@lem8236788 A B P t g). Qed.
Lemma lem8236790 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236791 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> B) t g a).
Proof. exact (MK_COMB (@lem8236789 A B P t g) (@lem8236790 P a)). Qed.
Lemma lem8236793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236794 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8236793 P B f x). Qed.
Lemma lem8236795 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> B) t g a) = (term617 A B P t g a).
Proof. exact (@lem8236794 B P (@I ((A -> B) -> P -> B) t g) a). Qed.
Lemma lem8236797 {A B P : Type'} (t : type558 A B P) (g : A -> B) (a : P) : (t g a) = (term617 A B P t g a).
Proof. exact (TRANS (@lem8236791 A B P t g a) (@lem8236795 A B P t g a)). Qed.
Lemma lem8236798 {A B P : Type'} (t : type558 A B P) (f : A -> B) (a : P) : (term184 A B P t f a) = (term618 A B P t f a).
Proof. exact (MK_COMB (@lem8236763 B) (@lem8236780 A B P t f a)). Qed.
Lemma lem8236799 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((term617 A B P t f a) = (term617 A B P t g a)).
Proof. exact (MK_COMB (@lem8236798 A B P t f a) (@lem8236797 A B P t g a)). Qed.
Lemma lem8236800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236801 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8236802 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8236811 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236812 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236811 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236813 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8236812 A B P z' f). Qed.
Lemma lem8236814 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236815 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8236813 A B P z' f) (@lem8236814 A B g)). Qed.
Lemma lem8236817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236818 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236817 (A -> B) (P -> A) f x). Qed.
Lemma lem8236819 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term660 A B P z' f g).
Proof. exact (@lem8236818 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8236820 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term660 A B P z' f g).
Proof. exact (TRANS (@lem8236815 A B P z' f g) (@lem8236819 A B P z' f g)). Qed.
Lemma lem8236821 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236822 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term661 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236820 A B P z' f g) (@lem8236821 P a)). Qed.
Lemma lem8236824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236825 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236824 P A f x). Qed.
Lemma lem8236826 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z' f g a) = (term662 A B P z' f g a).
Proof. exact (@lem8236825 A P (term660 A B P z' f g) a). Qed.
Lemma lem8236828 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term662 A B P z' f g a).
Proof. exact (TRANS (@lem8236822 A B P z' f g a) (@lem8236826 A B P z' f g a)). Qed.
Lemma lem8236829 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term663 A B P z' f g a) = (term664 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236802 A B f) (@lem8236828 A B P z' f g a)). Qed.
Lemma lem8236831 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236831 A B f x). Qed.
Lemma lem8236833 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term664 A B P z' f g a) = (term665 A B P z' f g a).
Proof. exact (@lem8236832 A B f (term662 A B P z' f g a)). Qed.
Lemma lem8236834 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term663 A B P z' f g a) = (term665 A B P z' f g a).
Proof. exact (TRANS (@lem8236829 A B P z' f g a) (@lem8236833 A B P z' f g a)). Qed.
Lemma lem8236835 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236845 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236844 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236846 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8236845 A B P z' f). Qed.
Lemma lem8236847 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236848 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8236846 A B P z' f) (@lem8236847 A B g)). Qed.
Lemma lem8236850 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236851 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236850 (A -> B) (P -> A) f x). Qed.
Lemma lem8236852 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term660 A B P z' f g).
Proof. exact (@lem8236851 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8236853 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term660 A B P z' f g).
Proof. exact (TRANS (@lem8236848 A B P z' f g) (@lem8236852 A B P z' f g)). Qed.
Lemma lem8236854 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236855 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term661 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236853 A B P z' f g) (@lem8236854 P a)). Qed.
Lemma lem8236857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236858 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236857 P A f x). Qed.
Lemma lem8236859 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z' f g a) = (term662 A B P z' f g a).
Proof. exact (@lem8236858 A P (term660 A B P z' f g) a). Qed.
Lemma lem8236861 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term662 A B P z' f g a).
Proof. exact (TRANS (@lem8236855 A B P z' f g a) (@lem8236859 A B P z' f g a)). Qed.
Lemma lem8236862 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term666 A B P z' f g a) = (term667 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236835 A B g) (@lem8236861 A B P z' f g a)). Qed.
Lemma lem8236864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8236864 A B f x). Qed.
Lemma lem8236866 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term667 A B P z' f g a) = (term668 A B P z' f g a).
Proof. exact (@lem8236865 A B g (term662 A B P z' f g a)). Qed.
Lemma lem8236867 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term666 A B P z' f g a) = (term668 A B P z' f g a).
Proof. exact (TRANS (@lem8236862 A B P z' f g a) (@lem8236866 A B P z' f g a)). Qed.
Lemma lem8236868 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term669 A B P z' f g a) = (term670 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236801 B) (@lem8236834 A B P z' f g a)). Qed.
Lemma lem8236869 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term663 A B P z' f g a) = (term666 A B P z' f g a)) = ((term665 A B P z' f g a) = (term668 A B P z' f g a)).
Proof. exact (MK_COMB (@lem8236868 A B P z' f g a) (@lem8236867 A B P z' f g a)). Qed.
Lemma lem8236870 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term671 A B P z' f g a) = (term672 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236800) (@lem8236869 A B P z' f g a)). Qed.
Lemma lem8236871 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8236880 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236881 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8236880 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8236882 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8236881 A B P z' f). Qed.
Lemma lem8236883 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8236884 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8236882 A B P z' f) (@lem8236883 A B g)). Qed.
Lemma lem8236886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236887 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8236886 (A -> B) (P -> A) f x). Qed.
Lemma lem8236888 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term660 A B P z' f g).
Proof. exact (@lem8236887 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8236889 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term660 A B P z' f g).
Proof. exact (TRANS (@lem8236884 A B P z' f g) (@lem8236888 A B P z' f g)). Qed.
Lemma lem8236890 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236891 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term661 A B P z' f g a).
Proof. exact (MK_COMB (@lem8236889 A B P z' f g) (@lem8236890 P a)). Qed.
Lemma lem8236893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236894 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236893 P A f x). Qed.
Lemma lem8236895 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term661 A B P z' f g a) = (term662 A B P z' f g a).
Proof. exact (@lem8236894 A P (term660 A B P z' f g) a). Qed.
Lemma lem8236897 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term662 A B P z' f g a).
Proof. exact (TRANS (@lem8236891 A B P z' f g a) (@lem8236895 A B P z' f g a)). Qed.
Lemma lem8236902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236903 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8236902 P A f x). Qed.
Lemma lem8236905 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8236903 A P s a). Qed.
Lemma lem8236906 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term673 A B P lt2 z' f g a) = (term674 A B P lt2 z' f g a).
Proof. exact (MK_COMB (@lem8236871 A lt2) (@lem8236897 A B P z' f g a)). Qed.
Lemma lem8236907 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term675 A B P lt2 z' f g s a) = (term676 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8236906 A B P lt2 z' f g a) (@lem8236905 A P s a)). Qed.
Lemma lem8236909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236910 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8236909 A (A -> Prop) f x). Qed.
Lemma lem8236911 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term674 A B P lt2 z' f g a) = (term677 A B P lt2 z' f g a).
Proof. exact (@lem8236910 A lt2 (term662 A B P z' f g a)). Qed.
Lemma lem8236912 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8236913 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term676 A B P lt2 z' f g s a) = (term678 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8236911 A B P lt2 z' f g a) (@lem8236912 A P s a)). Qed.
Lemma lem8236915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236916 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8236915 A Prop f x). Qed.
Lemma lem8236917 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term678 A B P lt2 z' f g s a) = (term679 A B P lt2 z' f g s a).
Proof. exact (@lem8236916 A (term677 A B P lt2 z' f g a) (@I (P -> A) s a)). Qed.
Lemma lem8236918 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term676 A B P lt2 z' f g s a) = (term679 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8236913 A B P lt2 z' f g s a) (@lem8236917 A B P lt2 z' f g s a)). Qed.
Lemma lem8236919 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term675 A B P lt2 z' f g s a) = (term679 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8236907 A B P lt2 z' f g s a) (@lem8236918 A B P lt2 z' f g s a)). Qed.
Lemma lem8236920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8236921 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term680 A B P lt2 z' f g s a) = (term681 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8236920) (@lem8236919 A B P lt2 z' f g s a)). Qed.
Lemma lem8236922 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term682 A B P lt2 s z' f g a) = (term683 A B P lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8236921 A B P lt2 z' f g s a) (@lem8236870 A B P z' f g a)). Qed.
Lemma lem8236923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236931 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236930 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236932 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8236931 A B P p g). Qed.
Lemma lem8236933 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236934 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8236932 A B P p g) (@lem8236933 P a)). Qed.
Lemma lem8236936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236937 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236936 P Prop f x). Qed.
Lemma lem8236938 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term634 A B P p g a).
Proof. exact (@lem8236937 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8236940 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term634 A B P p g a).
Proof. exact (TRANS (@lem8236934 A B P p g a) (@lem8236938 A B P p g a)). Qed.
Lemma lem8236941 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term247 A B P p g a) = (term637 A B P p g a).
Proof. exact (MK_COMB (@lem8236923) (@lem8236940 A B P p g a)). Qed.
Lemma lem8236942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236943 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term259 A B P p g a) = (term651 A B P p g a).
Proof. exact (MK_COMB (@lem8236942) (@lem8236941 A B P p g a)). Qed.
Lemma lem8236944 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term697 A B P p lt2 s z' f g a) = (term698 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8236943 A B P p g a) (@lem8236922 A B P lt2 s z' f g a)). Qed.
Lemma lem8236945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8236952 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236953 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8236952 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8236954 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8236953 A B P p f). Qed.
Lemma lem8236955 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8236956 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8236954 A B P p f) (@lem8236955 P a)). Qed.
Lemma lem8236958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8236959 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8236958 P Prop f x). Qed.
Lemma lem8236960 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term634 A B P p f a).
Proof. exact (@lem8236959 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8236962 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term634 A B P p f a).
Proof. exact (TRANS (@lem8236956 A B P p f a) (@lem8236960 A B P p f a)). Qed.
Lemma lem8236963 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term247 A B P p f a) = (term637 A B P p f a).
Proof. exact (MK_COMB (@lem8236945) (@lem8236962 A B P p f a)). Qed.
Lemma lem8236964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236965 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term259 A B P p f a) = (term651 A B P p f a).
Proof. exact (MK_COMB (@lem8236964) (@lem8236963 A B P p f a)). Qed.
Lemma lem8236966 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term699 A B P p lt2 s z' f g a) = (term700 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8236965 A B P p f a) (@lem8236944 A B P p lt2 s z' f g a)). Qed.
Lemma lem8236967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8236968 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term701 A B P p lt2 s z' f g a) = (term702 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8236967) (@lem8236966 A B P p lt2 s z' f g a)). Qed.
Lemma lem8236969 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term703 A B P p lt2 s z' f t g a) = (term704 A B P p lt2 s z' f t g a).
Proof. exact (MK_COMB (@lem8236968 A B P p lt2 s z' f g a) (@lem8236799 A B P f t g a)). Qed.
Lemma lem8236970 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term705 A B P p lt2 s z' f t g) = (term706 A B P p lt2 s z' f t g).
Proof. exact (fun_ext (fun a : P => @lem8236969 A B P p lt2 s z' f t g a)). Qed.
Lemma lem8236971 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8236972 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term707 A B P p lt2 s z' f t g) = (term708 A B P p lt2 s z' f t g).
Proof. exact (MK_COMB (@lem8236971 P) (@lem8236970 A B P p lt2 s z' f t g)). Qed.
Lemma lem8236973 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) : (term709 A B P p lt2 s z' f t) = (term710 A B P p lt2 s z' f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8236972 A B P p lt2 s z' f t g)). Qed.
Lemma lem8236974 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8236975 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) : (term473 A B P p lt2 s z' f t) = (term711 A B P p lt2 s z' f t).
Proof. exact (MK_COMB (@lem8236974 A B) (@lem8236973 A B P p lt2 s z' f t)). Qed.
Lemma lem8236976 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) : (term475 A B P p lt2 s z' t) = (term712 A B P p lt2 s z' t).
Proof. exact (fun_ext (fun f : A -> B => @lem8236975 A B P p lt2 s z' f t)). Qed.
Lemma lem8236977 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8236978 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) : (term477 A B P p lt2 s z' t) = (term713 A B P p lt2 s z' t).
Proof. exact (MK_COMB (@lem8236977 A B) (@lem8236976 A B P p lt2 s z' t)). Qed.
Lemma lem8236979 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term713 A B P p lt2 s z' t.
Proof. exact (EQ_MP (@lem8236978 A B P p lt2 s z' t) (@lem8236187 A B P p lt2 s z' t h1)). Qed.
Lemma lem8236980 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term648 A B P p lt2 s f fixed t g a.
Proof. exact (h1). Qed.
Lemma lem8236981 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term639 A B P p lt2 s g t f a fixed.
Proof. exact (h1). Qed.
Lemma lem8236982 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term647 A B P p lt2 s f fixed t g a.
Proof. exact (proj2 (@lem8236980 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8236984 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term645 A B P p lt2 s f t g a.
Proof. exact (h1). Qed.
Lemma lem8236985 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term642 A B P p lt2 s f fixed t g a.
Proof. exact (h1). Qed.
Lemma lem8236986 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term644 A B P lt2 s f t g a.
Proof. exact (proj2 (@lem8236984 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8236989 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term631 A B P lt2 s a f g.
Proof. exact (proj1 (@lem8236986 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8236990 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term641 A B P lt2 s f fixed t g a.
Proof. exact (proj2 (@lem8236985 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8236993 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term631 A B P lt2 s a f g.
Proof. exact (proj1 (@lem8236990 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8236994 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term636 A B P p lt2 s g t f a fixed.
Proof. exact (proj2 (@lem8236981 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8236996 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term633 A B P lt2 s g t f a fixed.
Proof. exact (proj2 (@lem8236994 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8236999 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term631 A B P lt2 s a f g.
Proof. exact (proj1 (@lem8236996 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8237058 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : ((term617 A B P t f a) = (term617 A B P t g a)) = ((term617 A B P t f a) = (term617 A B P t g a)).
Proof. exact (eq_refl ((term617 A B P t f a) = (term617 A B P t g a))). Qed.
Lemma lem8237075 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term698 A B P p lt2 s z' f g a) = (term714 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term679 A B P lt2 z' f g s a) (term637 A B P p g a) (term672 A B P z' f g a)). Qed.
Lemma lem8237078 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term651 A B P p f a) = (term651 A B P p f a).
Proof. exact (eq_refl (term651 A B P p f a)). Qed.
Lemma lem8237079 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term700 A B P p lt2 s z' f g a) = (term715 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8237078 A B P p f a) (@lem8237075 A B P lt2 s p z' f g a)). Qed.
Lemma lem8237086 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term715 A B P lt2 s p z' f g a) = (term716 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term717 A B P p lt2 z' f g s a) (term637 A B P p f a) (term718 A B P p z' f g a)). Qed.
Lemma lem8237087 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term700 A B P p lt2 s z' f g a) = (term716 A B P lt2 s p z' f g a).
Proof. exact (TRANS (@lem8237079 A B P lt2 s p z' f g a) (@lem8237086 A B P lt2 s p z' f g a)). Qed.
Lemma lem8237088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8237089 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term702 A B P p lt2 s z' f g a) = (term719 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8237088) (@lem8237087 A B P lt2 s p z' f g a)). Qed.
Lemma lem8237090 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term704 A B P p lt2 s z' f t g a) = (term720 A B P lt2 s p z' f t g a).
Proof. exact (MK_COMB (@lem8237089 A B P lt2 s p z' f g a) (@lem8237058 A B P f t g a)). Qed.
Lemma lem8237097 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term720 A B P lt2 s p z' f t g a) = (term721 A B P lt2 s p z' f t g a).
Proof. exact (@lem19699 (term722 A B P p lt2 z' f g s a) (term723 A B P p z' f g a) ((term617 A B P t f a) = (term617 A B P t g a))). Qed.
Lemma lem8237098 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term704 A B P p lt2 s z' f t g a) = (term721 A B P lt2 s p z' f t g a).
Proof. exact (TRANS (@lem8237090 A B P lt2 s p z' f t g a) (@lem8237097 A B P lt2 s p z' f t g a)). Qed.
Lemma lem8237099 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term706 A B P p lt2 s z' f t g) = (term724 A B P lt2 s p z' f t g).
Proof. exact (fun_ext (fun a : P => @lem8237098 A B P lt2 s p z' f t g a)). Qed.
Lemma lem8237100 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8237101 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) (g : A -> B) : (term708 A B P p lt2 s z' f t g) = (term725 A B P lt2 s p z' f t g).
Proof. exact (MK_COMB (@lem8237100 P) (@lem8237099 A B P lt2 s p z' f t g)). Qed.
Lemma lem8237102 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) : (term710 A B P p lt2 s z' f t) = (term726 A B P lt2 s p z' f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8237101 A B P lt2 s p z' f t g)). Qed.
Lemma lem8237103 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237104 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type558 A B P) : (term711 A B P p lt2 s z' f t) = (term727 A B P lt2 s p z' f t).
Proof. exact (MK_COMB (@lem8237103 A B) (@lem8237102 A B P lt2 s p z' f t)). Qed.
Lemma lem8237105 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (t : type558 A B P) : (term712 A B P p lt2 s z' t) = (term728 A B P lt2 s p z' t).
Proof. exact (fun_ext (fun f : A -> B => @lem8237104 A B P lt2 s p z' f t)). Qed.
Lemma lem8237106 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237108 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (t : type558 A B P) : (term713 A B P p lt2 s z' t) = (term729 A B P lt2 s p z' t).
Proof. exact (MK_COMB (@lem8237106 A B) (@lem8237105 A B P lt2 s p z' t)). Qed.
Lemma lem8237109 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term729 A B P lt2 s p z' t.
Proof. exact (EQ_MP (@lem8237108 A B P lt2 s p z' t) (@lem8236979 A B P p lt2 s z' t h1)). Qed.
Lemma lem8237125 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term629 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (eq_refl (term629 A B P lt2 s a f g z)). Qed.
Lemma lem8237126 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term630 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8237125 A B P lt2 s a f g z)). Qed.
Lemma lem8237127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8237129 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term631 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8237127 A) (@lem8237126 A B P lt2 s a f g)). Qed.
Lemma lem8237130 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term631 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8237129 A B P lt2 s a f g) (@lem8236989 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237161 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term687 A B P lt2 s z f p g a) = (term730 A B P lt2 s z f p g a).
Proof. exact (@lem19490 (term656 A B P f p g a) (term683 A B P lt2 s z f g a) (term653 A B P f p g a)). Qed.
Lemma lem8237168 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term731 A B P lt2 s z f p g a) = (term732 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term679 A B P lt2 z f g s a) (term672 A B P z f g a) (term653 A B P f p g a)). Qed.
Lemma lem8237175 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term733 A B P lt2 s z f p g a) = (term734 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term679 A B P lt2 z f g s a) (term672 A B P z f g a) (term656 A B P f p g a)). Qed.
Lemma lem8237176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8237177 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term735 A B P lt2 s z f p g a) = (term736 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8237176) (@lem8237175 A B P lt2 s z f p g a)). Qed.
Lemma lem8237178 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term730 A B P lt2 s z f p g a) = (term737 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8237177 A B P lt2 s z f p g a) (@lem8237168 A B P lt2 s z f p g a)). Qed.
Lemma lem8237180 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term687 A B P lt2 s z f p g a) = (term737 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8237161 A B P lt2 s z f p g a) (@lem8237178 A B P lt2 s z f p g a)). Qed.
Lemma lem8237181 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term689 A B P lt2 s z f p g) = (term738 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8237180 A B P lt2 s z f p g a)). Qed.
Lemma lem8237182 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8237183 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term691 A B P lt2 s z f p g) = (term739 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8237182 P) (@lem8237181 A B P lt2 s z f p g)). Qed.
Lemma lem8237184 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term693 A B P lt2 s z f p) = (term740 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8237183 A B P lt2 s z f p g)). Qed.
Lemma lem8237185 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237186 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term694 A B P lt2 s z f p) = (term741 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8237185 A B) (@lem8237184 A B P lt2 s z f p)). Qed.
Lemma lem8237187 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term695 A B P lt2 s z p) = (term742 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8237186 A B P lt2 s z f p)). Qed.
Lemma lem8237188 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237190 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term696 A B P lt2 s z p) = (term743 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8237188 A B) (@lem8237187 A B P lt2 s z p)). Qed.
Lemma lem8237191 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term743 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8237190 A B P lt2 s z p) (@lem8236762 A B P lt2 s z p h1)). Qed.
Lemma lem8237260 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term629 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (eq_refl (term629 A B P lt2 s a f g z)). Qed.
Lemma lem8237261 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term630 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8237260 A B P lt2 s a f g z)). Qed.
Lemma lem8237262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8237264 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term631 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8237262 A) (@lem8237261 A B P lt2 s a f g)). Qed.
Lemma lem8237265 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term631 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8237264 A B P lt2 s a f g) (@lem8236993 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237296 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term687 A B P lt2 s z f p g a) = (term730 A B P lt2 s z f p g a).
Proof. exact (@lem19490 (term656 A B P f p g a) (term683 A B P lt2 s z f g a) (term653 A B P f p g a)). Qed.
Lemma lem8237303 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term731 A B P lt2 s z f p g a) = (term732 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term679 A B P lt2 z f g s a) (term672 A B P z f g a) (term653 A B P f p g a)). Qed.
Lemma lem8237310 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term733 A B P lt2 s z f p g a) = (term734 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term679 A B P lt2 z f g s a) (term672 A B P z f g a) (term656 A B P f p g a)). Qed.
Lemma lem8237311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8237312 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term735 A B P lt2 s z f p g a) = (term736 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8237311) (@lem8237310 A B P lt2 s z f p g a)). Qed.
Lemma lem8237313 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term730 A B P lt2 s z f p g a) = (term737 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8237312 A B P lt2 s z f p g a) (@lem8237303 A B P lt2 s z f p g a)). Qed.
Lemma lem8237315 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term687 A B P lt2 s z f p g a) = (term737 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8237296 A B P lt2 s z f p g a) (@lem8237313 A B P lt2 s z f p g a)). Qed.
Lemma lem8237316 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term689 A B P lt2 s z f p g) = (term738 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8237315 A B P lt2 s z f p g a)). Qed.
Lemma lem8237317 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8237318 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term691 A B P lt2 s z f p g) = (term739 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8237317 P) (@lem8237316 A B P lt2 s z f p g)). Qed.
Lemma lem8237319 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term693 A B P lt2 s z f p) = (term740 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8237318 A B P lt2 s z f p g)). Qed.
Lemma lem8237320 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237321 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term694 A B P lt2 s z f p) = (term741 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8237320 A B) (@lem8237319 A B P lt2 s z f p)). Qed.
Lemma lem8237322 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term695 A B P lt2 s z p) = (term742 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8237321 A B P lt2 s z f p)). Qed.
Lemma lem8237323 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8237325 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term696 A B P lt2 s z p) = (term743 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8237323 A B) (@lem8237322 A B P lt2 s z p)). Qed.
Lemma lem8237326 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term743 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8237325 A B P lt2 s z p) (@lem8236762 A B P lt2 s z p h1)). Qed.
Lemma lem8237395 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term629 A B P lt2 s a f g z) = (term629 A B P lt2 s a f g z).
Proof. exact (eq_refl (term629 A B P lt2 s a f g z)). Qed.
Lemma lem8237396 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term630 A B P lt2 s a f g) = (term630 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8237395 A B P lt2 s a f g z)). Qed.
Lemma lem8237397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8237399 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term631 A B P lt2 s a f g) = (term631 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8237397 A) (@lem8237396 A B P lt2 s a f g)). Qed.
Lemma lem8237400 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term631 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8237399 A B P lt2 s a f g) (@lem8236999 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8237414 {A B P : Type'} (_109608 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term744 A B P lt2 s p z' t _109608.
Proof. exact (@lem8237109 A B P p lt2 s z' t h1 _109608). Qed.
Lemma lem8237415 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) : (term744 A B P lt2 s p z' t _109608) = (term727 A B P lt2 s p z' _109608 t).
Proof. exact (eq_refl (term744 A B P lt2 s p z' t _109608)). Qed.
Lemma lem8237416 {A B P : Type'} (_109608 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term727 A B P lt2 s p z' _109608 t.
Proof. exact (EQ_MP (@lem8237415 A B P lt2 s p z' _109608 t) (@lem8237414 A B P _109608 p lt2 s z' t h1)). Qed.
Lemma lem8237417 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term745 A B P lt2 s p z' _109608 t _109609.
Proof. exact (@lem8237416 A B P _109608 p lt2 s z' t h1 _109609). Qed.
Lemma lem8237418 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) : (term745 A B P lt2 s p z' _109608 t _109609) = (term725 A B P lt2 s p z' _109608 t _109609).
Proof. exact (eq_refl (term745 A B P lt2 s p z' _109608 t _109609)). Qed.
Lemma lem8237419 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term725 A B P lt2 s p z' _109608 t _109609.
Proof. exact (EQ_MP (@lem8237418 A B P lt2 s p z' _109608 t _109609) (@lem8237417 A B P _109608 _109609 p lt2 s z' t h1)). Qed.
Lemma lem8237420 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term746 A B P lt2 s p z' _109608 t _109609 _109610.
Proof. exact (@lem8237419 A B P _109608 _109609 p lt2 s z' t h1 _109610). Qed.
Lemma lem8237421 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term746 A B P lt2 s p z' _109608 t _109609 _109610) = (term721 A B P lt2 s p z' _109608 t _109609 _109610).
Proof. exact (eq_refl (term746 A B P lt2 s p z' _109608 t _109609 _109610)). Qed.
Lemma lem8237422 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term721 A B P lt2 s p z' _109608 t _109609 _109610.
Proof. exact (EQ_MP (@lem8237421 A B P lt2 s p z' _109608 t _109609 _109610) (@lem8237420 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8237423 {A B P : Type'} (_109611 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term747 A B P lt2 s a f g _109611.
Proof. exact (@lem8237130 A B P p lt2 s f t g a h1 _109611). Qed.
Lemma lem8237424 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109611 : A) : (term747 A B P lt2 s a f g _109611) = (term629 A B P lt2 s a f g _109611).
Proof. exact (eq_refl (term747 A B P lt2 s a f g _109611)). Qed.
Lemma lem8237426 {A B P : Type'} (_109612 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term748 A B P lt2 s z p _109612.
Proof. exact (@lem8237191 A B P lt2 s z p h1 _109612). Qed.
Lemma lem8237427 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) : (term748 A B P lt2 s z p _109612) = (term741 A B P lt2 s z _109612 p).
Proof. exact (eq_refl (term748 A B P lt2 s z p _109612)). Qed.
Lemma lem8237428 {A B P : Type'} (_109612 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term741 A B P lt2 s z _109612 p.
Proof. exact (EQ_MP (@lem8237427 A B P lt2 s z _109612 p) (@lem8237426 A B P _109612 lt2 s z p h1)). Qed.
Lemma lem8237429 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term749 A B P lt2 s z _109612 p _109613.
Proof. exact (@lem8237428 A B P _109612 lt2 s z p h1 _109613). Qed.
Lemma lem8237430 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) : (term749 A B P lt2 s z _109612 p _109613) = (term739 A B P lt2 s z _109612 p _109613).
Proof. exact (eq_refl (term749 A B P lt2 s z _109612 p _109613)). Qed.
Lemma lem8237431 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term739 A B P lt2 s z _109612 p _109613.
Proof. exact (EQ_MP (@lem8237430 A B P lt2 s z _109612 p _109613) (@lem8237429 A B P _109612 _109613 lt2 s z p h1)). Qed.
Lemma lem8237432 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term750 A B P lt2 s z _109612 p _109613 _109614.
Proof. exact (@lem8237431 A B P _109612 _109613 lt2 s z p h1 _109614). Qed.
Lemma lem8237433 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term750 A B P lt2 s z _109612 p _109613 _109614) = (term737 A B P lt2 s z _109612 p _109613 _109614).
Proof. exact (eq_refl (term750 A B P lt2 s z _109612 p _109613 _109614)). Qed.
Lemma lem8237434 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term737 A B P lt2 s z _109612 p _109613 _109614.
Proof. exact (EQ_MP (@lem8237433 A B P lt2 s z _109612 p _109613 _109614) (@lem8237432 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8237444 {A B P : Type'} (_109618 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term747 A B P lt2 s a f g _109618.
Proof. exact (@lem8237265 A B P p lt2 s f fixed t g a h1 _109618). Qed.
Lemma lem8237445 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109618 : A) : (term747 A B P lt2 s a f g _109618) = (term629 A B P lt2 s a f g _109618).
Proof. exact (eq_refl (term747 A B P lt2 s a f g _109618)). Qed.
Lemma lem8237447 {A B P : Type'} (_109619 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term748 A B P lt2 s z p _109619.
Proof. exact (@lem8237326 A B P lt2 s z p h1 _109619). Qed.
Lemma lem8237448 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) : (term748 A B P lt2 s z p _109619) = (term741 A B P lt2 s z _109619 p).
Proof. exact (eq_refl (term748 A B P lt2 s z p _109619)). Qed.
Lemma lem8237449 {A B P : Type'} (_109619 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term741 A B P lt2 s z _109619 p.
Proof. exact (EQ_MP (@lem8237448 A B P lt2 s z _109619 p) (@lem8237447 A B P _109619 lt2 s z p h1)). Qed.
Lemma lem8237450 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term749 A B P lt2 s z _109619 p _109620.
Proof. exact (@lem8237449 A B P _109619 lt2 s z p h1 _109620). Qed.
Lemma lem8237451 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) : (term749 A B P lt2 s z _109619 p _109620) = (term739 A B P lt2 s z _109619 p _109620).
Proof. exact (eq_refl (term749 A B P lt2 s z _109619 p _109620)). Qed.
Lemma lem8237452 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term739 A B P lt2 s z _109619 p _109620.
Proof. exact (EQ_MP (@lem8237451 A B P lt2 s z _109619 p _109620) (@lem8237450 A B P _109619 _109620 lt2 s z p h1)). Qed.
Lemma lem8237453 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term750 A B P lt2 s z _109619 p _109620 _109621.
Proof. exact (@lem8237452 A B P _109619 _109620 lt2 s z p h1 _109621). Qed.
Lemma lem8237454 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term750 A B P lt2 s z _109619 p _109620 _109621) = (term737 A B P lt2 s z _109619 p _109620 _109621).
Proof. exact (eq_refl (term750 A B P lt2 s z _109619 p _109620 _109621)). Qed.
Lemma lem8237455 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term737 A B P lt2 s z _109619 p _109620 _109621.
Proof. exact (EQ_MP (@lem8237454 A B P lt2 s z _109619 p _109620 _109621) (@lem8237453 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8237465 {A B P : Type'} (_109625 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term747 A B P lt2 s a f g _109625.
Proof. exact (@lem8237400 A B P p lt2 s g t f a fixed h1 _109625). Qed.
Lemma lem8237466 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109625 : A) : (term747 A B P lt2 s a f g _109625) = (term629 A B P lt2 s a f g _109625).
Proof. exact (eq_refl (term747 A B P lt2 s a f g _109625)). Qed.
Lemma lem8237468 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term751 A B P p z' _109608 t _109609 _109610.
Proof. exact (proj2 (@lem8237422 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8237469 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term752 A B P p lt2 z' s _109608 t _109609 _109610.
Proof. exact (proj1 (@lem8237422 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8237479 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term734 A B P lt2 s z _109612 p _109613 _109614.
Proof. exact (proj1 (@lem8237434 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8237486 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term732 A B P lt2 s z _109619 p _109620 _109621.
Proof. exact (proj2 (@lem8237455 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8237501 {A B P : Type'} (_109611 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term629 A B P lt2 s a f g _109611.
Proof. exact (EQ_MP (@lem8237424 A B P lt2 s a f g _109611) (@lem8237423 A B P _109611 p lt2 s f t g a h1)). Qed.
Lemma lem8237503 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term643 A B P f t g a.
Proof. exact (proj2 (@lem8236986 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237507 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term752 A B P p lt2 z' s _109608 t _109609 _109610) = (term753 A B P p lt2 z' s _109608 t _109609 _109610).
Proof. exact (@lem8233453 (term637 A B P p _109608 _109610) (term717 A B P p lt2 z' _109608 _109609 s _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8237514 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term754 A B P p lt2 z' s _109608 t _109609 _109610) = (term755 A B P p lt2 z' s _109608 t _109609 _109610).
Proof. exact (@lem8233453 (term637 A B P p _109609 _109610) (term679 A B P lt2 z' _109608 _109609 s _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8237515 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8237518 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term753 A B P p lt2 z' s _109608 t _109609 _109610) = (term756 A B P p lt2 z' s _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8237515 A B P p _109608 _109610) (@lem8237514 A B P p lt2 z' s _109608 t _109609 _109610)). Qed.
Lemma lem8237520 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term752 A B P p lt2 z' s _109608 t _109609 _109610) = (term756 A B P p lt2 z' s _109608 t _109609 _109610).
Proof. exact (TRANS (@lem8237507 A B P p lt2 z' s _109608 t _109609 _109610) (@lem8237518 A B P p lt2 z' s _109608 t _109609 _109610)). Qed.
Lemma lem8237521 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term756 A B P p lt2 z' s _109608 t _109609 _109610.
Proof. exact (EQ_MP (@lem8237520 A B P p lt2 z' s _109608 t _109609 _109610) (@lem8237469 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8237525 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term751 A B P p z' _109608 t _109609 _109610) = (term757 A B P p z' _109608 t _109609 _109610).
Proof. exact (@lem8233453 (term637 A B P p _109608 _109610) (term718 A B P p z' _109608 _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8237532 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term758 A B P p z' _109608 t _109609 _109610) = (term759 A B P p z' _109608 t _109609 _109610).
Proof. exact (@lem8233453 (term637 A B P p _109609 _109610) (term672 A B P z' _109608 _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8237533 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8237536 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term757 A B P p z' _109608 t _109609 _109610) = (term760 A B P p z' _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8237533 A B P p _109608 _109610) (@lem8237532 A B P p z' _109608 t _109609 _109610)). Qed.
Lemma lem8237538 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term751 A B P p z' _109608 t _109609 _109610) = (term760 A B P p z' _109608 t _109609 _109610).
Proof. exact (TRANS (@lem8237525 A B P p z' _109608 t _109609 _109610) (@lem8237536 A B P p z' _109608 t _109609 _109610)). Qed.
Lemma lem8237539 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term760 A B P p z' _109608 t _109609 _109610.
Proof. exact (EQ_MP (@lem8237538 A B P p z' _109608 t _109609 _109610) (@lem8237468 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8237583 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term637 A B P p f a.
Proof. exact (proj1 (@lem8236985 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237589 {A B P : Type'} (_109618 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term629 A B P lt2 s a f g _109618.
Proof. exact (EQ_MP (@lem8237445 A B P lt2 s a f g _109618) (@lem8237444 A B P _109618 p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237657 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term761 A B P lt2 z s _109612 p _109613 _109614.
Proof. exact (proj1 (@lem8237479 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8237667 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term762 A B P z _109612 p _109613 _109614.
Proof. exact (proj2 (@lem8237479 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8237669 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term637 A B P p g a.
Proof. exact (proj1 (@lem8236981 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8237677 {A B P : Type'} (_109625 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term629 A B P lt2 s a f g _109625.
Proof. exact (EQ_MP (@lem8237466 A B P lt2 s a f g _109625) (@lem8237465 A B P _109625 p lt2 s g t f a fixed h1)). Qed.
Lemma lem8237725 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term763 A B P lt2 z s _109619 p _109620 _109621.
Proof. exact (proj1 (@lem8237486 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8237735 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term764 A B P z _109619 p _109620 _109621.
Proof. exact (proj2 (@lem8237486 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8237941 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term634 A B P p f a.
Proof. exact (proj1 (@lem8236984 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237942 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term765 A B P p f a.
Proof. exact (fun h0 : term637 A B P p f a => @lem8237941 A B P p lt2 s f t g a h1). Qed.
Lemma lem8237944 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8237945 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term765 A B P p f a) = (term634 A B P p f a).
Proof. exact (@lem8237944 (term634 A B P p f a)). Qed.
Lemma lem8237946 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term634 A B P p f a.
Proof. exact (EQ_MP (@lem8237945 A B P p f a) (@lem8237942 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237948 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (proj1 (@lem8236980 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237949 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term765 A B P p g a.
Proof. exact (fun h0 : term637 A B P p g a => @lem8237948 A B P p lt2 s f fixed t g a h1). Qed.
Lemma lem8237951 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8237952 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term765 A B P p g a) = (term634 A B P p g a).
Proof. exact (@lem8237951 (term634 A B P p g a)). Qed.
Lemma lem8237953 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (EQ_MP (@lem8237952 A B P p g a) (@lem8237949 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237955 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term634 A B P p f a.
Proof. exact (proj1 (@lem8236984 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237956 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term765 A B P p f a.
Proof. exact (fun h0 : term637 A B P p f a => @lem8237955 A B P p lt2 s f t g a h1). Qed.
Lemma lem8237958 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8237959 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term765 A B P p f a) = (term634 A B P p f a).
Proof. exact (@lem8237958 (term634 A B P p f a)). Qed.
Lemma lem8237960 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term634 A B P p f a.
Proof. exact (EQ_MP (@lem8237959 A B P p f a) (@lem8237956 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8237962 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (proj1 (@lem8236980 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237963 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term765 A B P p g a.
Proof. exact (fun h0 : term637 A B P p g a => @lem8237962 A B P p lt2 s f fixed t g a h1). Qed.
Lemma lem8237965 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8237966 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term765 A B P p g a) = (term634 A B P p g a).
Proof. exact (@lem8237965 (term634 A B P p g a)). Qed.
Lemma lem8237967 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (EQ_MP (@lem8237966 A B P p g a) (@lem8237963 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8237970 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term643 A B P f t g a) : term643 A B P f t g a.
Proof. exact (h1). Qed.
Lemma lem8237971 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term643 A B P f t g a) : term767 A B P f t g a.
Proof. exact (fun h0 : (term617 A B P t f a) = (term617 A B P t g a) => @lem8237970 A B P f t g a h1). Qed.
Lemma lem8237973 (p : Prop) : (term768 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8237974 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term767 A B P f t g a) = (term643 A B P f t g a).
Proof. exact (@lem8237973 ((term617 A B P t f a) = (term617 A B P t g a))). Qed.
Lemma lem8237975 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term643 A B P f t g a) : term643 A B P f t g a.
Proof. exact (EQ_MP (@lem8237974 A B P f t g a) (@lem8237971 A B P f t g a h1)). Qed.
Lemma lem8237991 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8237992 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term755 A B P p lt2 z' s _109608 t _109609 _109610) = (term769 A B P lt2 z' s p _109608 t _109609 _109610).
Proof. exact (@lem8237991 (term679 A B P lt2 z' _109608 _109609 s _109610) (term637 A B P p _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8238006 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238007 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term770 A B P p _109608 t _109609 _109610) = (term771 A B P _109608 t p _109609 _109610).
Proof. exact (@lem8238006 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238015 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term772 A B P lt2 z' _109608 _109609 s _109610) = (term772 A B P lt2 z' _109608 _109609 s _109610).
Proof. exact (eq_refl (term772 A B P lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238016 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term769 A B P lt2 z' s p _109608 t _109609 _109610) = (term773 A B P lt2 z' s _109608 t p _109609 _109610).
Proof. exact (MK_COMB (@lem8238015 A B P lt2 z' _109608 _109609 s _109610) (@lem8238007 A B P _109608 t p _109609 _109610)). Qed.
Lemma lem8238020 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238021 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (s : P -> A) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term773 A B P lt2 z' s _109608 t p _109609 _109610) = (term774 A B P t lt2 z' _109608 s p _109609 _109610).
Proof. exact (@lem8238020 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term679 A B P lt2 z' _109608 _109609 s _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238039 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (s : P -> A) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term769 A B P lt2 z' s p _109608 t _109609 _109610) = (term774 A B P t lt2 z' _109608 s p _109609 _109610).
Proof. exact (TRANS (@lem8238016 A B P lt2 z' s _109608 t p _109609 _109610) (@lem8238021 A B P t lt2 z' _109608 s p _109609 _109610)). Qed.
Lemma lem8238040 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (s : P -> A) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term755 A B P p lt2 z' s _109608 t _109609 _109610) = (term774 A B P t lt2 z' _109608 s p _109609 _109610).
Proof. exact (TRANS (@lem8237992 A B P lt2 z' s p _109608 t _109609 _109610) (@lem8238039 A B P t lt2 z' _109608 s p _109609 _109610)). Qed.
Lemma lem8238041 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8238042 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (s : P -> A) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term775 A B P t lt2 z' _109608 s p _109609 _109610).
Proof. exact (MK_COMB (@lem8238041 A B P p _109608 _109610) (@lem8238040 A B P t lt2 z' _109608 s p _109609 _109610)). Qed.
Lemma lem8238046 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238047 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (s : P -> A) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term775 A B P t lt2 z' _109608 s p _109609 _109610) = (term776 A B P t lt2 z' _109608 s p _109609 _109610).
Proof. exact (@lem8238046 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109608 _109610) (term777 A B P lt2 z' _109608 s p _109609 _109610)). Qed.
Lemma lem8238063 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238064 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term778 A B P lt2 z' _109608 s p _109609 _109610) = (term779 A B P lt2 z' s _109608 p _109609 _109610).
Proof. exact (@lem8238063 (term679 A B P lt2 z' _109608 _109609 s _109610) (term637 A B P p _109608 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238080 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term780 A B P _109608 t _109609 _109610) = (term780 A B P _109608 t _109609 _109610).
Proof. exact (eq_refl (term780 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238081 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term776 A B P t lt2 z' _109608 s p _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238080 A B P _109608 t _109609 _109610) (@lem8238064 A B P lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238092 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term775 A B P t lt2 z' _109608 s p _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238047 A B P t lt2 z' _109608 s p _109609 _109610) (@lem8238081 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238093 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238042 A B P t lt2 z' _109608 s p _109609 _109610) (@lem8238092 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8238095 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term782 A B P p lt2 z' s _109608 t _109609 _109610) = (term783 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238094) (@lem8238093 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238119 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238120 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term770 A B P p _109608 t _109609 _109610) = (term771 A B P _109608 t p _109609 _109610).
Proof. exact (@lem8238119 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238128 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8238129 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term784 A B P p _109608 t _109609 _109610) = (term785 A B P _109608 t p _109609 _109610).
Proof. exact (MK_COMB (@lem8238128 A B P p _109608 _109610) (@lem8238120 A B P _109608 t p _109609 _109610)). Qed.
Lemma lem8238133 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238134 {A B P : Type'} (t : type558 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term785 A B P _109608 t p _109609 _109610) = (term786 A B P t _109608 p _109609 _109610).
Proof. exact (@lem8238133 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109608 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238152 {A B P : Type'} (t : type558 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term784 A B P p _109608 t _109609 _109610) = (term786 A B P t _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238129 A B P _109608 t p _109609 _109610) (@lem8238134 A B P t _109608 p _109609 _109610)). Qed.
Lemma lem8238153 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term772 A B P lt2 z' _109608 _109609 s _109610) = (term772 A B P lt2 z' _109608 _109609 s _109610).
Proof. exact (eq_refl (term772 A B P lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238154 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (t : type558 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term787 A B P lt2 z' s p _109608 t _109609 _109610) = (term788 A B P lt2 z' s t _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238153 A B P lt2 z' _109608 _109609 s _109610) (@lem8238152 A B P t _109608 p _109609 _109610)). Qed.
Lemma lem8238158 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238159 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term788 A B P lt2 z' s t _109608 p _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (@lem8238158 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term679 A B P lt2 z' _109608 _109609 s _109610) (term789 A B P _109608 p _109609 _109610)). Qed.
Lemma lem8238187 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term787 A B P lt2 z' s p _109608 t _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238154 A B P lt2 z' s t _109608 p _109609 _109610) (@lem8238159 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238188 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : ((term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term787 A B P lt2 z' s p _109608 t _109609 _109610)) = ((term781 A B P t lt2 z' s _109608 p _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610)).
Proof. exact (MK_COMB (@lem8238095 A B P t lt2 z' s _109608 p _109609 _109610) (@lem8238187 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8238191 (x : Prop) : (x = x) = True.
Proof. exact (@lem8238190 Prop x). Qed.
Lemma lem8238192 {A B P : Type'} (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : ((term781 A B P t lt2 z' s _109608 p _109609 _109610) = (term781 A B P t lt2 z' s _109608 p _109609 _109610)) = True.
Proof. exact (@lem8238191 (term781 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238193 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : ((term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term787 A B P lt2 z' s p _109608 t _109609 _109610)) = True.
Proof. exact (TRANS (@lem8238188 A B P t lt2 z' s _109608 p _109609 _109610) (@lem8238192 A B P t lt2 z' s _109608 p _109609 _109610)). Qed.
Lemma lem8238194 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : True = ((term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term787 A B P lt2 z' s p _109608 t _109609 _109610)).
Proof. exact (SYM (@lem8238193 A B P lt2 z' s p _109608 t _109609 _109610)). Qed.
Lemma lem8238195 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term756 A B P p lt2 z' s _109608 t _109609 _109610) = (term787 A B P lt2 z' s p _109608 t _109609 _109610).
Proof. exact (EQ_MP (@lem8238194 A B P lt2 z' s p _109608 t _109609 _109610) (@lem0)). Qed.
Lemma lem8238196 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term787 A B P lt2 z' s p _109608 t _109609 _109610.
Proof. exact (EQ_MP (@lem8238195 A B P lt2 z' s p _109608 t _109609 _109610) (@lem8237521 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8238198 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238199 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term787 A B P lt2 z' s p _109608 t _109609 _109610) = (term791 A B P p t lt2 z' _109608 _109609 s _109610).
Proof. exact (@lem8238198 (term784 A B P p _109608 t _109609 _109610) (term679 A B P lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238201 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238202 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term794 A B P p _109608 t _109609 _109610) = (term795 A B P p _109608 t _109609 _109610).
Proof. exact (@lem8238201 (term637 A B P p _109608 _109610) (term770 A B P p _109608 t _109609 _109610)). Qed.
Lemma lem8238204 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238205 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term796 A B P p _109608 _109610) = (term634 A B P p _109608 _109610).
Proof. exact (@lem8238204 (term634 A B P p _109608 _109610)). Qed.
Lemma lem8238206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8238207 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term797 A B P p _109608 _109610) = (term635 A B P p _109608 _109610).
Proof. exact (MK_COMB (@lem8238206) (@lem8238205 A B P p _109608 _109610)). Qed.
Lemma lem8238209 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238210 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term798 A B P p _109608 t _109609 _109610) = (term799 A B P p _109608 t _109609 _109610).
Proof. exact (@lem8238209 (term637 A B P p _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8238212 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238213 {A B P : Type'} (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term796 A B P p _109609 _109610) = (term634 A B P p _109609 _109610).
Proof. exact (@lem8238212 (term634 A B P p _109609 _109610)). Qed.
Lemma lem8238214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8238215 {A B P : Type'} (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term797 A B P p _109609 _109610) = (term635 A B P p _109609 _109610).
Proof. exact (MK_COMB (@lem8238214) (@lem8238213 A B P p _109609 _109610)). Qed.
Lemma lem8238216 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term643 A B P _109608 t _109609 _109610) = (term643 A B P _109608 t _109609 _109610).
Proof. exact (eq_refl (term643 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238217 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term799 A B P p _109608 t _109609 _109610) = (term800 A B P p _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8238215 A B P p _109609 _109610) (@lem8238216 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238218 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term798 A B P p _109608 t _109609 _109610) = (term800 A B P p _109608 t _109609 _109610).
Proof. exact (TRANS (@lem8238210 A B P p _109608 t _109609 _109610) (@lem8238217 A B P p _109608 t _109609 _109610)). Qed.
Lemma lem8238219 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term795 A B P p _109608 t _109609 _109610) = (term801 A B P p _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8238207 A B P p _109608 _109610) (@lem8238218 A B P p _109608 t _109609 _109610)). Qed.
Lemma lem8238220 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term794 A B P p _109608 t _109609 _109610) = (term801 A B P p _109608 t _109609 _109610).
Proof. exact (TRANS (@lem8238202 A B P p _109608 t _109609 _109610) (@lem8238219 A B P p _109608 t _109609 _109610)). Qed.
Lemma lem8238221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238222 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term802 A B P p _109608 t _109609 _109610) = (term803 A B P p _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8238221) (@lem8238220 A B P p _109608 t _109609 _109610)). Qed.
Lemma lem8238223 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term679 A B P lt2 z' _109608 _109609 s _109610) = (term679 A B P lt2 z' _109608 _109609 s _109610).
Proof. exact (eq_refl (term679 A B P lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238224 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term791 A B P p t lt2 z' _109608 _109609 s _109610) = (term804 A B P p t lt2 z' _109608 _109609 s _109610).
Proof. exact (MK_COMB (@lem8238222 A B P p _109608 t _109609 _109610) (@lem8238223 A B P lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238225 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (s : P -> A) (_109610 : P) : (term787 A B P lt2 z' s p _109608 t _109609 _109610) = (term804 A B P p t lt2 z' _109608 _109609 s _109610).
Proof. exact (TRANS (@lem8238199 A B P p t lt2 z' _109608 _109609 s _109610) (@lem8238224 A B P p t lt2 z' _109608 _109609 s _109610)). Qed.
Lemma lem8238227 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term643 A B P f t g a) (h2 : term648 A B P p lt2 s f fixed t g a) : term800 A B P p f t g a.
Proof. exact (conj (@lem8237967 A B P p lt2 s f fixed t g a h2) (@lem8237975 A B P f t g a h1)). Qed.
Lemma lem8238228 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term643 A B P f t g a) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term801 A B P p f t g a.
Proof. exact (conj (@lem8237960 A B P p lt2 s f t g a h2) (@lem8238227 A B P p lt2 s f fixed t g a h1 h3)). Qed.
Lemma lem8238230 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term804 A B P p t lt2 z' _109608 _109609 s _109610.
Proof. exact (EQ_MP (@lem8238225 A B P p t lt2 z' _109608 _109609 s _109610) (@lem8238196 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8238231 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term804 A B P p t lt2 z' _109608 _109609 s _109610.
Proof. exact (@lem8238230 A B P _109608 _109609 _109610 p lt2 s z' t h1). Qed.
Lemma lem8238232 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term804 A B P p t lt2 z' f g s a.
Proof. exact (@lem8238231 A B P f g a p lt2 s z' t h1). Qed.
Lemma lem8238235 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term679 A B P lt2 z' f g s a.
Proof. exact (@lem8238232 A B P f g a p lt2 s z' t h1 (@lem8238228 A B P p lt2 s f fixed t g a h2 h3 h4)). Qed.
Lemma lem8238236 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term805 A B P lt2 z' f g s a.
Proof. exact (fun h0 : term806 A B P lt2 z' f g s a => @lem8238235 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4). Qed.
Lemma lem8238238 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238239 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term805 A B P lt2 z' f g s a) = (term679 A B P lt2 z' f g s a).
Proof. exact (@lem8238238 (term679 A B P lt2 z' f g s a)). Qed.
Lemma lem8238240 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term679 A B P lt2 z' f g s a.
Proof. exact (EQ_MP (@lem8238239 A B P lt2 z' f g s a) (@lem8238236 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238246 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238247 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109611) = (term807 A B P f g lt2 _109611 s a).
Proof. exact (@lem8238246 ((@I (A -> B) f _109611) = (@I (A -> B) g _109611)) (term626 A P lt2 _109611 s a)). Qed.
Lemma lem8238255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8238256 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term808 A B P lt2 s a f g _109611) = (term809 A B P f g lt2 _109611 s a).
Proof. exact (MK_COMB (@lem8238255) (@lem8238247 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238264 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term807 A B P f g lt2 _109611 s a) = (term807 A B P f g lt2 _109611 s a).
Proof. exact (eq_refl (term807 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238265 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109611) = (term807 A B P f g lt2 _109611 s a)) = ((term807 A B P f g lt2 _109611 s a) = (term807 A B P f g lt2 _109611 s a)).
Proof. exact (MK_COMB (@lem8238256 A B P f g lt2 _109611 s a) (@lem8238264 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238267 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8238268 (x : Prop) : (x = x) = True.
Proof. exact (@lem8238267 Prop x). Qed.
Lemma lem8238269 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : ((term807 A B P f g lt2 _109611 s a) = (term807 A B P f g lt2 _109611 s a)) = True.
Proof. exact (@lem8238268 (term807 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238270 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109611) = (term807 A B P f g lt2 _109611 s a)) = True.
Proof. exact (TRANS (@lem8238265 A B P f g lt2 _109611 s a) (@lem8238269 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238271 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : True = ((term629 A B P lt2 s a f g _109611) = (term807 A B P f g lt2 _109611 s a)).
Proof. exact (SYM (@lem8238270 A B P f g lt2 _109611 s a)). Qed.
Lemma lem8238272 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109611) = (term807 A B P f g lt2 _109611 s a).
Proof. exact (EQ_MP (@lem8238271 A B P f g lt2 _109611 s a) (@lem0)). Qed.
Lemma lem8238273 {A B P : Type'} (_109611 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term807 A B P f g lt2 _109611 s a.
Proof. exact (EQ_MP (@lem8238272 A B P f g lt2 _109611 s a) (@lem8237501 A B P _109611 p lt2 s f t g a h1)). Qed.
Lemma lem8238275 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238276 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109611 : A) : (term807 A B P f g lt2 _109611 s a) = (term810 A B P lt2 s a f g _109611).
Proof. exact (@lem8238275 (term626 A P lt2 _109611 s a) ((@I (A -> B) f _109611) = (@I (A -> B) g _109611))). Qed.
Lemma lem8238278 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238279 {A P : Type'} (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term811 A P lt2 _109611 s a) = (term624 A P lt2 _109611 s a).
Proof. exact (@lem8238278 (term624 A P lt2 _109611 s a)). Qed.
Lemma lem8238280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238281 {A P : Type'} (lt2 : type1402 A) (_109611 : A) (s : P -> A) (a : P) : (term812 A P lt2 _109611 s a) = (term813 A P lt2 _109611 s a).
Proof. exact (MK_COMB (@lem8238280) (@lem8238279 A P lt2 _109611 s a)). Qed.
Lemma lem8238282 {A B : Type'} (f : A -> B) (g : A -> B) (_109611 : A) : ((@I (A -> B) f _109611) = (@I (A -> B) g _109611)) = ((@I (A -> B) f _109611) = (@I (A -> B) g _109611)).
Proof. exact (eq_refl ((@I (A -> B) f _109611) = (@I (A -> B) g _109611))). Qed.
Lemma lem8238283 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109611 : A) : (term810 A B P lt2 s a f g _109611) = (term814 A B P lt2 s a f g _109611).
Proof. exact (MK_COMB (@lem8238281 A P lt2 _109611 s a) (@lem8238282 A B f g _109611)). Qed.
Lemma lem8238284 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109611 : A) : (term807 A B P f g lt2 _109611 s a) = (term814 A B P lt2 s a f g _109611).
Proof. exact (TRANS (@lem8238276 A B P lt2 s a f g _109611) (@lem8238283 A B P lt2 s a f g _109611)). Qed.
Lemma lem8238287 {A B P : Type'} (_109611 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term814 A B P lt2 s a f g _109611.
Proof. exact (EQ_MP (@lem8238284 A B P lt2 s a f g _109611) (@lem8238273 A B P _109611 p lt2 s f t g a h1)). Qed.
Lemma lem8238288 {A B P : Type'} (_109611 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term814 A B P lt2 s a f g _109611.
Proof. exact (@lem8238287 A B P _109611 p lt2 s f t g a h1). Qed.
Lemma lem8238289 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term815 A B P lt2 s z' f g a.
Proof. exact (@lem8238288 A B P (term662 A B P z' f g a) p lt2 s f t g a h1). Qed.
Lemma lem8238292 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : (term665 A B P z' f g a) = (term668 A B P z' f g a).
Proof. exact (@lem8238289 A B P z' p lt2 s f t g a h3 (@lem8238240 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238293 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term816 A B P z' f g a.
Proof. exact (fun h0 : term672 A B P z' f g a => @lem8238292 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4). Qed.
Lemma lem8238295 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238296 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term816 A B P z' f g a) = ((term665 A B P z' f g a) = (term668 A B P z' f g a)).
Proof. exact (@lem8238295 ((term665 A B P z' f g a) = (term668 A B P z' f g a))). Qed.
Lemma lem8238297 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : (term665 A B P z' f g a) = (term668 A B P z' f g a).
Proof. exact (EQ_MP (@lem8238296 A B P z' f g a) (@lem8238293 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238313 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238314 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term759 A B P p z' _109608 t _109609 _109610) = (term817 A B P z' p _109608 t _109609 _109610).
Proof. exact (@lem8238313 (term672 A B P z' _109608 _109609 _109610) (term637 A B P p _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8238330 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238331 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term770 A B P p _109608 t _109609 _109610) = (term771 A B P _109608 t p _109609 _109610).
Proof. exact (@lem8238330 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238339 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term818 A B P z' _109608 _109609 _109610) = (term818 A B P z' _109608 _109609 _109610).
Proof. exact (eq_refl (term818 A B P z' _109608 _109609 _109610)). Qed.
Lemma lem8238340 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term817 A B P z' p _109608 t _109609 _109610) = (term819 A B P z' _109608 t p _109609 _109610).
Proof. exact (MK_COMB (@lem8238339 A B P z' _109608 _109609 _109610) (@lem8238331 A B P _109608 t p _109609 _109610)). Qed.
Lemma lem8238344 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238345 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term819 A B P z' _109608 t p _109609 _109610) = (term820 A B P t z' _109608 p _109609 _109610).
Proof. exact (@lem8238344 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term672 A B P z' _109608 _109609 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238365 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term817 A B P z' p _109608 t _109609 _109610) = (term820 A B P t z' _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238340 A B P z' _109608 t p _109609 _109610) (@lem8238345 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238366 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term759 A B P p z' _109608 t _109609 _109610) = (term820 A B P t z' _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238314 A B P z' p _109608 t _109609 _109610) (@lem8238365 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238367 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8238368 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term760 A B P p z' _109608 t _109609 _109610) = (term821 A B P t z' _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238367 A B P p _109608 _109610) (@lem8238366 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238372 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238373 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term821 A B P t z' _109608 p _109609 _109610) = (term822 A B P t z' _109608 p _109609 _109610).
Proof. exact (@lem8238372 ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) (term637 A B P p _109608 _109610) (term823 A B P z' _109608 p _109609 _109610)). Qed.
Lemma lem8238389 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238390 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term824 A B P z' _109608 p _109609 _109610) = (term825 A B P z' _109608 p _109609 _109610).
Proof. exact (@lem8238389 (term672 A B P z' _109608 _109609 _109610) (term637 A B P p _109608 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238408 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term780 A B P _109608 t _109609 _109610) = (term780 A B P _109608 t _109609 _109610).
Proof. exact (eq_refl (term780 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238409 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term822 A B P t z' _109608 p _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238408 A B P _109608 t _109609 _109610) (@lem8238390 A B P z' _109608 p _109609 _109610)). Qed.
Lemma lem8238420 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term821 A B P t z' _109608 p _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238373 A B P t z' _109608 p _109609 _109610) (@lem8238409 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238421 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term760 A B P p z' _109608 t _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238368 A B P t z' _109608 p _109609 _109610) (@lem8238420 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8238423 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term827 A B P p z' _109608 t _109609 _109610) = (term828 A B P t z' _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238422) (@lem8238421 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238449 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238450 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term718 A B P p z' _109608 _109609 _109610) = (term823 A B P z' _109608 p _109609 _109610).
Proof. exact (@lem8238449 (term672 A B P z' _109608 _109609 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238458 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term651 A B P p _109608 _109610) = (term651 A B P p _109608 _109610).
Proof. exact (eq_refl (term651 A B P p _109608 _109610)). Qed.
Lemma lem8238459 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term723 A B P p z' _109608 _109609 _109610) = (term824 A B P z' _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238458 A B P p _109608 _109610) (@lem8238450 A B P z' _109608 p _109609 _109610)). Qed.
Lemma lem8238463 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238464 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term824 A B P z' _109608 p _109609 _109610) = (term825 A B P z' _109608 p _109609 _109610).
Proof. exact (@lem8238463 (term672 A B P z' _109608 _109609 _109610) (term637 A B P p _109608 _109610) (term637 A B P p _109609 _109610)). Qed.
Lemma lem8238482 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term723 A B P p z' _109608 _109609 _109610) = (term825 A B P z' _109608 p _109609 _109610).
Proof. exact (TRANS (@lem8238459 A B P z' _109608 p _109609 _109610) (@lem8238464 A B P z' _109608 p _109609 _109610)). Qed.
Lemma lem8238483 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term780 A B P _109608 t _109609 _109610) = (term780 A B P _109608 t _109609 _109610).
Proof. exact (eq_refl (term780 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238484 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term829 A B P t p z' _109608 _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610).
Proof. exact (MK_COMB (@lem8238483 A B P _109608 t _109609 _109610) (@lem8238482 A B P z' _109608 p _109609 _109610)). Qed.
Lemma lem8238495 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : ((term760 A B P p z' _109608 t _109609 _109610) = (term829 A B P t p z' _109608 _109609 _109610)) = ((term826 A B P t z' _109608 p _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610)).
Proof. exact (MK_COMB (@lem8238423 A B P t z' _109608 p _109609 _109610) (@lem8238484 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238497 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8238498 (x : Prop) : (x = x) = True.
Proof. exact (@lem8238497 Prop x). Qed.
Lemma lem8238499 {A B P : Type'} (t : type558 A B P) (z' : type518 A B P) (_109608 : A -> B) (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : ((term826 A B P t z' _109608 p _109609 _109610) = (term826 A B P t z' _109608 p _109609 _109610)) = True.
Proof. exact (@lem8238498 (term826 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238500 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : ((term760 A B P p z' _109608 t _109609 _109610) = (term829 A B P t p z' _109608 _109609 _109610)) = True.
Proof. exact (TRANS (@lem8238495 A B P t z' _109608 p _109609 _109610) (@lem8238499 A B P t z' _109608 p _109609 _109610)). Qed.
Lemma lem8238501 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : True = ((term760 A B P p z' _109608 t _109609 _109610) = (term829 A B P t p z' _109608 _109609 _109610)).
Proof. exact (SYM (@lem8238500 A B P t p z' _109608 _109609 _109610)). Qed.
Lemma lem8238502 {A B P : Type'} (t : type558 A B P) (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term760 A B P p z' _109608 t _109609 _109610) = (term829 A B P t p z' _109608 _109609 _109610).
Proof. exact (EQ_MP (@lem8238501 A B P t p z' _109608 _109609 _109610) (@lem0)). Qed.
Lemma lem8238503 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term829 A B P t p z' _109608 _109609 _109610.
Proof. exact (EQ_MP (@lem8238502 A B P t p z' _109608 _109609 _109610) (@lem8237539 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8238505 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238506 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term829 A B P t p z' _109608 _109609 _109610) = (term830 A B P p z' _109608 t _109609 _109610).
Proof. exact (@lem8238505 (term723 A B P p z' _109608 _109609 _109610) ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8238508 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238509 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term831 A B P p z' _109608 _109609 _109610) = (term832 A B P p z' _109608 _109609 _109610).
Proof. exact (@lem8238508 (term637 A B P p _109608 _109610) (term718 A B P p z' _109608 _109609 _109610)). Qed.
Lemma lem8238511 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238512 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term796 A B P p _109608 _109610) = (term634 A B P p _109608 _109610).
Proof. exact (@lem8238511 (term634 A B P p _109608 _109610)). Qed.
Lemma lem8238513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8238514 {A B P : Type'} (p : type560 A B P) (_109608 : A -> B) (_109610 : P) : (term797 A B P p _109608 _109610) = (term635 A B P p _109608 _109610).
Proof. exact (MK_COMB (@lem8238513) (@lem8238512 A B P p _109608 _109610)). Qed.
Lemma lem8238516 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238517 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term833 A B P p z' _109608 _109609 _109610) = (term834 A B P p z' _109608 _109609 _109610).
Proof. exact (@lem8238516 (term637 A B P p _109609 _109610) (term672 A B P z' _109608 _109609 _109610)). Qed.
Lemma lem8238519 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238520 {A B P : Type'} (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term796 A B P p _109609 _109610) = (term634 A B P p _109609 _109610).
Proof. exact (@lem8238519 (term634 A B P p _109609 _109610)). Qed.
Lemma lem8238521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8238522 {A B P : Type'} (p : type560 A B P) (_109609 : A -> B) (_109610 : P) : (term797 A B P p _109609 _109610) = (term635 A B P p _109609 _109610).
Proof. exact (MK_COMB (@lem8238521) (@lem8238520 A B P p _109609 _109610)). Qed.
Lemma lem8238524 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238525 {A B P : Type'} (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term835 A B P z' _109608 _109609 _109610) = ((term665 A B P z' _109608 _109609 _109610) = (term668 A B P z' _109608 _109609 _109610)).
Proof. exact (@lem8238524 ((term665 A B P z' _109608 _109609 _109610) = (term668 A B P z' _109608 _109609 _109610))). Qed.
Lemma lem8238526 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term834 A B P p z' _109608 _109609 _109610) = (term836 A B P p z' _109608 _109609 _109610).
Proof. exact (MK_COMB (@lem8238522 A B P p _109609 _109610) (@lem8238525 A B P z' _109608 _109609 _109610)). Qed.
Lemma lem8238527 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term833 A B P p z' _109608 _109609 _109610) = (term836 A B P p z' _109608 _109609 _109610).
Proof. exact (TRANS (@lem8238517 A B P p z' _109608 _109609 _109610) (@lem8238526 A B P p z' _109608 _109609 _109610)). Qed.
Lemma lem8238528 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term832 A B P p z' _109608 _109609 _109610) = (term837 A B P p z' _109608 _109609 _109610).
Proof. exact (MK_COMB (@lem8238514 A B P p _109608 _109610) (@lem8238527 A B P p z' _109608 _109609 _109610)). Qed.
Lemma lem8238529 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term831 A B P p z' _109608 _109609 _109610) = (term837 A B P p z' _109608 _109609 _109610).
Proof. exact (TRANS (@lem8238509 A B P p z' _109608 _109609 _109610) (@lem8238528 A B P p z' _109608 _109609 _109610)). Qed.
Lemma lem8238530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238531 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) : (term838 A B P p z' _109608 _109609 _109610) = (term839 A B P p z' _109608 _109609 _109610).
Proof. exact (MK_COMB (@lem8238530) (@lem8238529 A B P p z' _109608 _109609 _109610)). Qed.
Lemma lem8238532 {A B P : Type'} (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)) = ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610)).
Proof. exact (eq_refl ((term617 A B P t _109608 _109610) = (term617 A B P t _109609 _109610))). Qed.
Lemma lem8238533 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term830 A B P p z' _109608 t _109609 _109610) = (term840 A B P p z' _109608 t _109609 _109610).
Proof. exact (MK_COMB (@lem8238531 A B P p z' _109608 _109609 _109610) (@lem8238532 A B P _109608 t _109609 _109610)). Qed.
Lemma lem8238534 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109608 : A -> B) (t : type558 A B P) (_109609 : A -> B) (_109610 : P) : (term829 A B P t p z' _109608 _109609 _109610) = (term840 A B P p z' _109608 t _109609 _109610).
Proof. exact (TRANS (@lem8238506 A B P p z' _109608 t _109609 _109610) (@lem8238533 A B P p z' _109608 t _109609 _109610)). Qed.
Lemma lem8238536 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term836 A B P p z' f g a.
Proof. exact (conj (@lem8237953 A B P p lt2 s f fixed t g a h4) (@lem8238297 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238537 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term837 A B P p z' f g a.
Proof. exact (conj (@lem8237946 A B P p lt2 s f t g a h3) (@lem8238536 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238539 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term840 A B P p z' _109608 t _109609 _109610.
Proof. exact (EQ_MP (@lem8238534 A B P p z' _109608 t _109609 _109610) (@lem8238503 A B P _109608 _109609 _109610 p lt2 s z' t h1)). Qed.
Lemma lem8238540 {A B P : Type'} (_109608 : A -> B) (_109609 : A -> B) (_109610 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term840 A B P p z' _109608 t _109609 _109610.
Proof. exact (@lem8238539 A B P _109608 _109609 _109610 p lt2 s z' t h1). Qed.
Lemma lem8238541 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type558 A B P) (h1 : term477 A B P p lt2 s z' t) : term840 A B P p z' f t g a.
Proof. exact (@lem8238540 A B P f g a p lt2 s z' t h1). Qed.
Lemma lem8238544 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term643 A B P f t g a) (h3 : term645 A B P p lt2 s f t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : (term617 A B P t f a) = (term617 A B P t g a).
Proof. exact (@lem8238541 A B P f g a p lt2 s z' t h1 (@lem8238537 A B P z' p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238545 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term841 A B P f t g a.
Proof. exact (fun h0 : term643 A B P f t g a => @lem8238544 A B P z' p lt2 s f fixed t g a h1 h0 h2 h3). Qed.
Lemma lem8238547 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238548 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term841 A B P f t g a) = ((term617 A B P t f a) = (term617 A B P t g a)).
Proof. exact (@lem8238547 ((term617 A B P t f a) = (term617 A B P t g a))). Qed.
Lemma lem8238549 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : (term617 A B P t f a) = (term617 A B P t g a).
Proof. exact (EQ_MP (@lem8238548 A B P f t g a) (@lem8238545 A B P z' p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238552 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8238554 {A B P : Type'} (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) : (term643 A B P f t g a) = (term842 A B P f t g a).
Proof. exact (@lem8238552 ((term617 A B P t f a) = (term617 A B P t g a))). Qed.
Lemma lem8238557 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term645 A B P p lt2 s f t g a) : term842 A B P f t g a.
Proof. exact (EQ_MP (@lem8238554 A B P f t g a) (@lem8237503 A B P p lt2 s f t g a h1)). Qed.
Lemma lem8238560 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : False.
Proof. exact (@lem8238557 A B P p lt2 s f t g a h2 (@lem8238549 A B P z' p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238561 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term843.
Proof. exact (fun h0 : ~ False => @lem8238560 A B P z' p lt2 s f fixed t g a h1 h2 h3). Qed.
Lemma lem8238563 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238564 : term843 = False.
Proof. exact (@lem8238563 False). Qed.
Lemma lem8238565 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term477 A B P p lt2 s z' t) (h2 : term645 A B P p lt2 s f t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : False.
Proof. exact (EQ_MP (@lem8238564) (@lem8238561 A B P z' p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238752 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : term637 A B P p f a) : term637 A B P p f a.
Proof. exact (h1). Qed.
Lemma lem8238753 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : term637 A B P p f a) : term844 A B P p f a.
Proof. exact (fun h0 : term634 A B P p f a => @lem8238752 A B P p f a h1). Qed.
Lemma lem8238755 (p : Prop) : (term768 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8238756 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term844 A B P p f a) = (term637 A B P p f a).
Proof. exact (@lem8238755 (term634 A B P p f a)). Qed.
Lemma lem8238757 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : term637 A B P p f a) : term637 A B P p f a.
Proof. exact (EQ_MP (@lem8238756 A B P p f a) (@lem8238753 A B P p f a h1)). Qed.
Lemma lem8238759 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (proj1 (@lem8236980 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238760 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term765 A B P p g a.
Proof. exact (fun h0 : term637 A B P p g a => @lem8238759 A B P p lt2 s f fixed t g a h1). Qed.
Lemma lem8238762 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238763 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term765 A B P p g a) = (term634 A B P p g a).
Proof. exact (@lem8238762 (term634 A B P p g a)). Qed.
Lemma lem8238764 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (EQ_MP (@lem8238763 A B P p g a) (@lem8238760 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238766 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238767 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (s : P -> A) (_109614 : P) : (term761 A B P lt2 z s _109612 p _109613 _109614) = (term845 A B P p lt2 z _109612 _109613 s _109614).
Proof. exact (@lem8238766 (term656 A B P _109612 p _109613 _109614) (term679 A B P lt2 z _109612 _109613 s _109614)). Qed.
Lemma lem8238769 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238770 {A B P : Type'} (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term846 A B P _109612 p _109613 _109614) = (term847 A B P _109612 p _109613 _109614).
Proof. exact (@lem8238769 (term634 A B P p _109612 _109614) (term637 A B P p _109613 _109614)). Qed.
Lemma lem8238772 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238773 {A B P : Type'} (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term796 A B P p _109613 _109614) = (term634 A B P p _109613 _109614).
Proof. exact (@lem8238772 (term634 A B P p _109613 _109614)). Qed.
Lemma lem8238774 {A B P : Type'} (p : type560 A B P) (_109612 : A -> B) (_109614 : P) : (term638 A B P p _109612 _109614) = (term638 A B P p _109612 _109614).
Proof. exact (eq_refl (term638 A B P p _109612 _109614)). Qed.
Lemma lem8238775 {A B P : Type'} (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term847 A B P _109612 p _109613 _109614) = (term848 A B P _109612 p _109613 _109614).
Proof. exact (MK_COMB (@lem8238774 A B P p _109612 _109614) (@lem8238773 A B P p _109613 _109614)). Qed.
Lemma lem8238776 {A B P : Type'} (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term846 A B P _109612 p _109613 _109614) = (term848 A B P _109612 p _109613 _109614).
Proof. exact (TRANS (@lem8238770 A B P _109612 p _109613 _109614) (@lem8238775 A B P _109612 p _109613 _109614)). Qed.
Lemma lem8238777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238778 {A B P : Type'} (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term849 A B P _109612 p _109613 _109614) = (term850 A B P _109612 p _109613 _109614).
Proof. exact (MK_COMB (@lem8238777) (@lem8238776 A B P _109612 p _109613 _109614)). Qed.
Lemma lem8238779 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (s : P -> A) (_109614 : P) : (term679 A B P lt2 z _109612 _109613 s _109614) = (term679 A B P lt2 z _109612 _109613 s _109614).
Proof. exact (eq_refl (term679 A B P lt2 z _109612 _109613 s _109614)). Qed.
Lemma lem8238780 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (s : P -> A) (_109614 : P) : (term845 A B P p lt2 z _109612 _109613 s _109614) = (term851 A B P p lt2 z _109612 _109613 s _109614).
Proof. exact (MK_COMB (@lem8238778 A B P _109612 p _109613 _109614) (@lem8238779 A B P lt2 z _109612 _109613 s _109614)). Qed.
Lemma lem8238781 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (s : P -> A) (_109614 : P) : (term761 A B P lt2 z s _109612 p _109613 _109614) = (term851 A B P p lt2 z _109612 _109613 s _109614).
Proof. exact (TRANS (@lem8238767 A B P p lt2 z _109612 _109613 s _109614) (@lem8238780 A B P p lt2 z _109612 _109613 s _109614)). Qed.
Lemma lem8238783 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term637 A B P p f a) (h2 : term648 A B P p lt2 s f fixed t g a) : term848 A B P f p g a.
Proof. exact (conj (@lem8238757 A B P p f a h1) (@lem8238764 A B P p lt2 s f fixed t g a h2)). Qed.
Lemma lem8238785 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term851 A B P p lt2 z _109612 _109613 s _109614.
Proof. exact (EQ_MP (@lem8238781 A B P p lt2 z _109612 _109613 s _109614) (@lem8237657 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8238786 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term851 A B P p lt2 z _109612 _109613 s _109614.
Proof. exact (@lem8238785 A B P _109612 _109613 _109614 lt2 s z p h1). Qed.
Lemma lem8238787 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term851 A B P p lt2 z f g s a.
Proof. exact (@lem8238786 A B P f g a lt2 s z p h1). Qed.
Lemma lem8238790 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term648 A B P p lt2 s f fixed t g a) : term679 A B P lt2 z f g s a.
Proof. exact (@lem8238787 A B P f g a lt2 s z p h1 (@lem8238783 A B P p lt2 s f fixed t g a h2 h3)). Qed.
Lemma lem8238791 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term648 A B P p lt2 s f fixed t g a) : term805 A B P lt2 z f g s a.
Proof. exact (fun h0 : term806 A B P lt2 z f g s a => @lem8238790 A B P z p lt2 s f fixed t g a h1 h2 h3). Qed.
Lemma lem8238793 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238794 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term805 A B P lt2 z f g s a) = (term679 A B P lt2 z f g s a).
Proof. exact (@lem8238793 (term679 A B P lt2 z f g s a)). Qed.
Lemma lem8238795 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term648 A B P p lt2 s f fixed t g a) : term679 A B P lt2 z f g s a.
Proof. exact (EQ_MP (@lem8238794 A B P lt2 z f g s a) (@lem8238791 A B P z p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8238802 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109618) = (term807 A B P f g lt2 _109618 s a).
Proof. exact (@lem8238801 ((@I (A -> B) f _109618) = (@I (A -> B) g _109618)) (term626 A P lt2 _109618 s a)). Qed.
Lemma lem8238810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8238811 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term808 A B P lt2 s a f g _109618) = (term809 A B P f g lt2 _109618 s a).
Proof. exact (MK_COMB (@lem8238810) (@lem8238802 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238819 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term807 A B P f g lt2 _109618 s a) = (term807 A B P f g lt2 _109618 s a).
Proof. exact (eq_refl (term807 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238820 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109618) = (term807 A B P f g lt2 _109618 s a)) = ((term807 A B P f g lt2 _109618 s a) = (term807 A B P f g lt2 _109618 s a)).
Proof. exact (MK_COMB (@lem8238811 A B P f g lt2 _109618 s a) (@lem8238819 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8238823 (x : Prop) : (x = x) = True.
Proof. exact (@lem8238822 Prop x). Qed.
Lemma lem8238824 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : ((term807 A B P f g lt2 _109618 s a) = (term807 A B P f g lt2 _109618 s a)) = True.
Proof. exact (@lem8238823 (term807 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238825 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109618) = (term807 A B P f g lt2 _109618 s a)) = True.
Proof. exact (TRANS (@lem8238820 A B P f g lt2 _109618 s a) (@lem8238824 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238826 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : True = ((term629 A B P lt2 s a f g _109618) = (term807 A B P f g lt2 _109618 s a)).
Proof. exact (SYM (@lem8238825 A B P f g lt2 _109618 s a)). Qed.
Lemma lem8238827 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109618) = (term807 A B P f g lt2 _109618 s a).
Proof. exact (EQ_MP (@lem8238826 A B P f g lt2 _109618 s a) (@lem0)). Qed.
Lemma lem8238828 {A B P : Type'} (_109618 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term807 A B P f g lt2 _109618 s a.
Proof. exact (EQ_MP (@lem8238827 A B P f g lt2 _109618 s a) (@lem8237589 A B P _109618 p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238830 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238831 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109618 : A) : (term807 A B P f g lt2 _109618 s a) = (term810 A B P lt2 s a f g _109618).
Proof. exact (@lem8238830 (term626 A P lt2 _109618 s a) ((@I (A -> B) f _109618) = (@I (A -> B) g _109618))). Qed.
Lemma lem8238833 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238834 {A P : Type'} (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term811 A P lt2 _109618 s a) = (term624 A P lt2 _109618 s a).
Proof. exact (@lem8238833 (term624 A P lt2 _109618 s a)). Qed.
Lemma lem8238835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238836 {A P : Type'} (lt2 : type1402 A) (_109618 : A) (s : P -> A) (a : P) : (term812 A P lt2 _109618 s a) = (term813 A P lt2 _109618 s a).
Proof. exact (MK_COMB (@lem8238835) (@lem8238834 A P lt2 _109618 s a)). Qed.
Lemma lem8238837 {A B : Type'} (f : A -> B) (g : A -> B) (_109618 : A) : ((@I (A -> B) f _109618) = (@I (A -> B) g _109618)) = ((@I (A -> B) f _109618) = (@I (A -> B) g _109618)).
Proof. exact (eq_refl ((@I (A -> B) f _109618) = (@I (A -> B) g _109618))). Qed.
Lemma lem8238838 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109618 : A) : (term810 A B P lt2 s a f g _109618) = (term814 A B P lt2 s a f g _109618).
Proof. exact (MK_COMB (@lem8238836 A P lt2 _109618 s a) (@lem8238837 A B f g _109618)). Qed.
Lemma lem8238839 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109618 : A) : (term807 A B P f g lt2 _109618 s a) = (term814 A B P lt2 s a f g _109618).
Proof. exact (TRANS (@lem8238831 A B P lt2 s a f g _109618) (@lem8238838 A B P lt2 s a f g _109618)). Qed.
Lemma lem8238842 {A B P : Type'} (_109618 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term814 A B P lt2 s a f g _109618.
Proof. exact (EQ_MP (@lem8238839 A B P lt2 s a f g _109618) (@lem8238828 A B P _109618 p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238843 {A B P : Type'} (_109618 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term814 A B P lt2 s a f g _109618.
Proof. exact (@lem8238842 A B P _109618 p lt2 s f fixed t g a h1). Qed.
Lemma lem8238844 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term815 A B P lt2 s z f g a.
Proof. exact (@lem8238843 A B P (term662 A B P z f g a) p lt2 s f fixed t g a h1). Qed.
Lemma lem8238847 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term642 A B P p lt2 s f fixed t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : (term665 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (@lem8238844 A B P z p lt2 s f fixed t g a h3 (@lem8238795 A B P z p lt2 s f fixed t g a h1 h2 h4)). Qed.
Lemma lem8238848 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term642 A B P p lt2 s f fixed t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term816 A B P z f g a.
Proof. exact (fun h0 : term672 A B P z f g a => @lem8238847 A B P z p lt2 s f fixed t g a h1 h2 h3 h4). Qed.
Lemma lem8238850 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238851 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term816 A B P z f g a) = ((term665 A B P z f g a) = (term668 A B P z f g a)).
Proof. exact (@lem8238850 ((term665 A B P z f g a) = (term668 A B P z f g a))). Qed.
Lemma lem8238852 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term642 A B P p lt2 s f fixed t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : (term665 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (EQ_MP (@lem8238851 A B P z f g a) (@lem8238848 A B P z p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238854 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (proj1 (@lem8236980 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238855 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term765 A B P p g a.
Proof. exact (fun h0 : term637 A B P p g a => @lem8238854 A B P p lt2 s f fixed t g a h1). Qed.
Lemma lem8238857 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238858 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term765 A B P p g a) = (term634 A B P p g a).
Proof. exact (@lem8238857 (term634 A B P p g a)). Qed.
Lemma lem8238859 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p g a.
Proof. exact (EQ_MP (@lem8238858 A B P p g a) (@lem8238855 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8238866 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term762 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614).
Proof. exact (@lem8238865 (term634 A B P p _109612 _109614) (term672 A B P z _109612 _109613 _109614) (term637 A B P p _109613 _109614)). Qed.
Lemma lem8238884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8238885 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term853 A B P z _109612 p _109613 _109614) = (term854 A B P z _109612 p _109613 _109614).
Proof. exact (MK_COMB (@lem8238884) (@lem8238866 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238903 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term852 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614).
Proof. exact (eq_refl (term852 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238904 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : ((term762 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614)) = ((term852 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614)).
Proof. exact (MK_COMB (@lem8238885 A B P z _109612 p _109613 _109614) (@lem8238903 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8238907 (x : Prop) : (x = x) = True.
Proof. exact (@lem8238906 Prop x). Qed.
Lemma lem8238908 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : ((term852 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614)) = True.
Proof. exact (@lem8238907 (term852 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238909 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : ((term762 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614)) = True.
Proof. exact (TRANS (@lem8238904 A B P z _109612 p _109613 _109614) (@lem8238908 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238910 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : True = ((term762 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614)).
Proof. exact (SYM (@lem8238909 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238911 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term762 A B P z _109612 p _109613 _109614) = (term852 A B P z _109612 p _109613 _109614).
Proof. exact (EQ_MP (@lem8238910 A B P z _109612 p _109613 _109614) (@lem0)). Qed.
Lemma lem8238912 {A B P : Type'} (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term852 A B P z _109612 p _109613 _109614.
Proof. exact (EQ_MP (@lem8238911 A B P z _109612 p _109613 _109614) (@lem8237667 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8238914 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8238915 {A B P : Type'} (z : type518 A B P) (_109613 : A -> B) (p : type560 A B P) (_109612 : A -> B) (_109614 : P) : (term852 A B P z _109612 p _109613 _109614) = (term855 A B P z _109613 p _109612 _109614).
Proof. exact (@lem8238914 (term823 A B P z _109612 p _109613 _109614) (term634 A B P p _109612 _109614)). Qed.
Lemma lem8238917 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8238918 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term856 A B P z _109612 p _109613 _109614) = (term857 A B P z _109612 p _109613 _109614).
Proof. exact (@lem8238917 (term672 A B P z _109612 _109613 _109614) (term637 A B P p _109613 _109614)). Qed.
Lemma lem8238920 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238921 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) : (term835 A B P z _109612 _109613 _109614) = ((term665 A B P z _109612 _109613 _109614) = (term668 A B P z _109612 _109613 _109614)).
Proof. exact (@lem8238920 ((term665 A B P z _109612 _109613 _109614) = (term668 A B P z _109612 _109613 _109614))). Qed.
Lemma lem8238922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8238923 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (_109613 : A -> B) (_109614 : P) : (term858 A B P z _109612 _109613 _109614) = (term859 A B P z _109612 _109613 _109614).
Proof. exact (MK_COMB (@lem8238922) (@lem8238921 A B P z _109612 _109613 _109614)). Qed.
Lemma lem8238925 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8238926 {A B P : Type'} (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term796 A B P p _109613 _109614) = (term634 A B P p _109613 _109614).
Proof. exact (@lem8238925 (term634 A B P p _109613 _109614)). Qed.
Lemma lem8238927 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term857 A B P z _109612 p _109613 _109614) = (term860 A B P z _109612 p _109613 _109614).
Proof. exact (MK_COMB (@lem8238923 A B P z _109612 _109613 _109614) (@lem8238926 A B P p _109613 _109614)). Qed.
Lemma lem8238928 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term856 A B P z _109612 p _109613 _109614) = (term860 A B P z _109612 p _109613 _109614).
Proof. exact (TRANS (@lem8238918 A B P z _109612 p _109613 _109614) (@lem8238927 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8238930 {A B P : Type'} (z : type518 A B P) (_109612 : A -> B) (p : type560 A B P) (_109613 : A -> B) (_109614 : P) : (term861 A B P z _109612 p _109613 _109614) = (term862 A B P z _109612 p _109613 _109614).
Proof. exact (MK_COMB (@lem8238929) (@lem8238928 A B P z _109612 p _109613 _109614)). Qed.
Lemma lem8238931 {A B P : Type'} (p : type560 A B P) (_109612 : A -> B) (_109614 : P) : (term634 A B P p _109612 _109614) = (term634 A B P p _109612 _109614).
Proof. exact (eq_refl (term634 A B P p _109612 _109614)). Qed.
Lemma lem8238932 {A B P : Type'} (z : type518 A B P) (_109613 : A -> B) (p : type560 A B P) (_109612 : A -> B) (_109614 : P) : (term855 A B P z _109613 p _109612 _109614) = (term863 A B P z _109613 p _109612 _109614).
Proof. exact (MK_COMB (@lem8238930 A B P z _109612 p _109613 _109614) (@lem8238931 A B P p _109612 _109614)). Qed.
Lemma lem8238933 {A B P : Type'} (z : type518 A B P) (_109613 : A -> B) (p : type560 A B P) (_109612 : A -> B) (_109614 : P) : (term852 A B P z _109612 p _109613 _109614) = (term863 A B P z _109613 p _109612 _109614).
Proof. exact (TRANS (@lem8238915 A B P z _109613 p _109612 _109614) (@lem8238932 A B P z _109613 p _109612 _109614)). Qed.
Lemma lem8238935 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term642 A B P p lt2 s f fixed t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term860 A B P z f p g a.
Proof. exact (conj (@lem8238852 A B P z p lt2 s f fixed t g a h1 h2 h3 h4) (@lem8238859 A B P p lt2 s f fixed t g a h4)). Qed.
Lemma lem8238937 {A B P : Type'} (_109613 : A -> B) (_109612 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term863 A B P z _109613 p _109612 _109614.
Proof. exact (EQ_MP (@lem8238933 A B P z _109613 p _109612 _109614) (@lem8238912 A B P _109612 _109613 _109614 lt2 s z p h1)). Qed.
Lemma lem8238938 {A B P : Type'} (_109613 : A -> B) (_109612 : A -> B) (_109614 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term863 A B P z _109613 p _109612 _109614.
Proof. exact (@lem8238937 A B P _109613 _109612 _109614 lt2 s z p h1). Qed.
Lemma lem8238939 {A B P : Type'} (g : A -> B) (f : A -> B) (a : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term863 A B P z g p f a.
Proof. exact (@lem8238938 A B P g f a lt2 s z p h1). Qed.
Lemma lem8238942 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p f a) (h3 : term642 A B P p lt2 s f fixed t g a) (h4 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p f a.
Proof. exact (@lem8238939 A B P g f a lt2 s z p h1 (@lem8238935 A B P z p lt2 s f fixed t g a h1 h2 h3 h4)). Qed.
Lemma lem8238943 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term642 A B P p lt2 s f fixed t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term765 A B P p f a.
Proof. exact (fun h0 : term637 A B P p f a => @lem8238942 A B P z p lt2 s f fixed t g a h1 h0 h2 h3). Qed.
Lemma lem8238945 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238946 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term765 A B P p f a) = (term634 A B P p f a).
Proof. exact (@lem8238945 (term634 A B P p f a)). Qed.
Lemma lem8238947 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term642 A B P p lt2 s f fixed t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term634 A B P p f a.
Proof. exact (EQ_MP (@lem8238946 A B P p f a) (@lem8238943 A B P z p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238950 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8238952 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term637 A B P p f a) = (term864 A B P p f a).
Proof. exact (@lem8238950 (term634 A B P p f a)). Qed.
Lemma lem8238955 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term642 A B P p lt2 s f fixed t g a) : term864 A B P p f a.
Proof. exact (EQ_MP (@lem8238952 A B P p f a) (@lem8237583 A B P p lt2 s f fixed t g a h1)). Qed.
Lemma lem8238958 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term642 A B P p lt2 s f fixed t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : False.
Proof. exact (@lem8238955 A B P p lt2 s f fixed t g a h2 (@lem8238947 A B P z p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8238959 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term642 A B P p lt2 s f fixed t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : term843.
Proof. exact (fun h0 : ~ False => @lem8238958 A B P z p lt2 s f fixed t g a h1 h2 h3). Qed.
Lemma lem8238961 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8238962 : term843 = False.
Proof. exact (@lem8238961 False). Qed.
Lemma lem8238963 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term642 A B P p lt2 s f fixed t g a) (h3 : term648 A B P p lt2 s f fixed t g a) : False.
Proof. exact (EQ_MP (@lem8238962) (@lem8238959 A B P z p lt2 s f fixed t g a h1 h2 h3)). Qed.
Lemma lem8239149 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p f a.
Proof. exact (proj1 (@lem8236994 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239150 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term765 A B P p f a.
Proof. exact (fun h0 : term637 A B P p f a => @lem8239149 A B P p lt2 s g t f a fixed h1). Qed.
Lemma lem8239152 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239153 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term765 A B P p f a) = (term634 A B P p f a).
Proof. exact (@lem8239152 (term634 A B P p f a)). Qed.
Lemma lem8239154 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p f a.
Proof. exact (EQ_MP (@lem8239153 A B P p f a) (@lem8239150 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239157 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : term637 A B P p g a) : term637 A B P p g a.
Proof. exact (h1). Qed.
Lemma lem8239158 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : term637 A B P p g a) : term844 A B P p g a.
Proof. exact (fun h0 : term634 A B P p g a => @lem8239157 A B P p g a h1). Qed.
Lemma lem8239160 (p : Prop) : (term768 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8239161 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term844 A B P p g a) = (term637 A B P p g a).
Proof. exact (@lem8239160 (term634 A B P p g a)). Qed.
Lemma lem8239162 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : term637 A B P p g a) : term637 A B P p g a.
Proof. exact (EQ_MP (@lem8239161 A B P p g a) (@lem8239158 A B P p g a h1)). Qed.
Lemma lem8239164 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8239165 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (s : P -> A) (_109621 : P) : (term763 A B P lt2 z s _109619 p _109620 _109621) = (term865 A B P p lt2 z _109619 _109620 s _109621).
Proof. exact (@lem8239164 (term653 A B P _109619 p _109620 _109621) (term679 A B P lt2 z _109619 _109620 s _109621)). Qed.
Lemma lem8239167 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8239168 {A B P : Type'} (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term866 A B P _109619 p _109620 _109621) = (term867 A B P _109619 p _109620 _109621).
Proof. exact (@lem8239167 (term637 A B P p _109619 _109621) (term634 A B P p _109620 _109621)). Qed.
Lemma lem8239170 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8239171 {A B P : Type'} (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term796 A B P p _109619 _109621) = (term634 A B P p _109619 _109621).
Proof. exact (@lem8239170 (term634 A B P p _109619 _109621)). Qed.
Lemma lem8239172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8239173 {A B P : Type'} (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term797 A B P p _109619 _109621) = (term635 A B P p _109619 _109621).
Proof. exact (MK_COMB (@lem8239172) (@lem8239171 A B P p _109619 _109621)). Qed.
Lemma lem8239174 {A B P : Type'} (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term637 A B P p _109620 _109621) = (term637 A B P p _109620 _109621).
Proof. exact (eq_refl (term637 A B P p _109620 _109621)). Qed.
Lemma lem8239175 {A B P : Type'} (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term867 A B P _109619 p _109620 _109621) = (term868 A B P _109619 p _109620 _109621).
Proof. exact (MK_COMB (@lem8239173 A B P p _109619 _109621) (@lem8239174 A B P p _109620 _109621)). Qed.
Lemma lem8239176 {A B P : Type'} (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term866 A B P _109619 p _109620 _109621) = (term868 A B P _109619 p _109620 _109621).
Proof. exact (TRANS (@lem8239168 A B P _109619 p _109620 _109621) (@lem8239175 A B P _109619 p _109620 _109621)). Qed.
Lemma lem8239177 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239178 {A B P : Type'} (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term869 A B P _109619 p _109620 _109621) = (term870 A B P _109619 p _109620 _109621).
Proof. exact (MK_COMB (@lem8239177) (@lem8239176 A B P _109619 p _109620 _109621)). Qed.
Lemma lem8239179 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (s : P -> A) (_109621 : P) : (term679 A B P lt2 z _109619 _109620 s _109621) = (term679 A B P lt2 z _109619 _109620 s _109621).
Proof. exact (eq_refl (term679 A B P lt2 z _109619 _109620 s _109621)). Qed.
Lemma lem8239180 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (s : P -> A) (_109621 : P) : (term865 A B P p lt2 z _109619 _109620 s _109621) = (term871 A B P p lt2 z _109619 _109620 s _109621).
Proof. exact (MK_COMB (@lem8239178 A B P _109619 p _109620 _109621) (@lem8239179 A B P lt2 z _109619 _109620 s _109621)). Qed.
Lemma lem8239181 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (s : P -> A) (_109621 : P) : (term763 A B P lt2 z s _109619 p _109620 _109621) = (term871 A B P p lt2 z _109619 _109620 s _109621).
Proof. exact (TRANS (@lem8239165 A B P p lt2 z _109619 _109620 s _109621) (@lem8239180 A B P p lt2 z _109619 _109620 s _109621)). Qed.
Lemma lem8239183 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term637 A B P p g a) (h2 : term639 A B P p lt2 s g t f a fixed) : term868 A B P f p g a.
Proof. exact (conj (@lem8239154 A B P p lt2 s g t f a fixed h2) (@lem8239162 A B P p g a h1)). Qed.
Lemma lem8239185 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term871 A B P p lt2 z _109619 _109620 s _109621.
Proof. exact (EQ_MP (@lem8239181 A B P p lt2 z _109619 _109620 s _109621) (@lem8237725 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8239186 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term871 A B P p lt2 z _109619 _109620 s _109621.
Proof. exact (@lem8239185 A B P _109619 _109620 _109621 lt2 s z p h1). Qed.
Lemma lem8239187 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term871 A B P p lt2 z f g s a.
Proof. exact (@lem8239186 A B P f g a lt2 s z p h1). Qed.
Lemma lem8239190 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term679 A B P lt2 z f g s a.
Proof. exact (@lem8239187 A B P f g a lt2 s z p h1 (@lem8239183 A B P p lt2 s g t f a fixed h2 h3)). Qed.
Lemma lem8239191 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term805 A B P lt2 z f g s a.
Proof. exact (fun h0 : term806 A B P lt2 z f g s a => @lem8239190 A B P z p lt2 s g t f a fixed h1 h2 h3). Qed.
Lemma lem8239193 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239194 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term805 A B P lt2 z f g s a) = (term679 A B P lt2 z f g s a).
Proof. exact (@lem8239193 (term679 A B P lt2 z f g s a)). Qed.
Lemma lem8239195 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term679 A B P lt2 z f g s a.
Proof. exact (EQ_MP (@lem8239194 A B P lt2 z f g s a) (@lem8239191 A B P z p lt2 s g t f a fixed h1 h2 h3)). Qed.
Lemma lem8239201 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8239202 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109625) = (term807 A B P f g lt2 _109625 s a).
Proof. exact (@lem8239201 ((@I (A -> B) f _109625) = (@I (A -> B) g _109625)) (term626 A P lt2 _109625 s a)). Qed.
Lemma lem8239210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8239211 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term808 A B P lt2 s a f g _109625) = (term809 A B P f g lt2 _109625 s a).
Proof. exact (MK_COMB (@lem8239210) (@lem8239202 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239219 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term807 A B P f g lt2 _109625 s a) = (term807 A B P f g lt2 _109625 s a).
Proof. exact (eq_refl (term807 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239220 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109625) = (term807 A B P f g lt2 _109625 s a)) = ((term807 A B P f g lt2 _109625 s a) = (term807 A B P f g lt2 _109625 s a)).
Proof. exact (MK_COMB (@lem8239211 A B P f g lt2 _109625 s a) (@lem8239219 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239222 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8239223 (x : Prop) : (x = x) = True.
Proof. exact (@lem8239222 Prop x). Qed.
Lemma lem8239224 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : ((term807 A B P f g lt2 _109625 s a) = (term807 A B P f g lt2 _109625 s a)) = True.
Proof. exact (@lem8239223 (term807 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239225 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : ((term629 A B P lt2 s a f g _109625) = (term807 A B P f g lt2 _109625 s a)) = True.
Proof. exact (TRANS (@lem8239220 A B P f g lt2 _109625 s a) (@lem8239224 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239226 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : True = ((term629 A B P lt2 s a f g _109625) = (term807 A B P f g lt2 _109625 s a)).
Proof. exact (SYM (@lem8239225 A B P f g lt2 _109625 s a)). Qed.
Lemma lem8239227 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term629 A B P lt2 s a f g _109625) = (term807 A B P f g lt2 _109625 s a).
Proof. exact (EQ_MP (@lem8239226 A B P f g lt2 _109625 s a) (@lem0)). Qed.
Lemma lem8239228 {A B P : Type'} (_109625 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term807 A B P f g lt2 _109625 s a.
Proof. exact (EQ_MP (@lem8239227 A B P f g lt2 _109625 s a) (@lem8237677 A B P _109625 p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239230 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8239231 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109625 : A) : (term807 A B P f g lt2 _109625 s a) = (term810 A B P lt2 s a f g _109625).
Proof. exact (@lem8239230 (term626 A P lt2 _109625 s a) ((@I (A -> B) f _109625) = (@I (A -> B) g _109625))). Qed.
Lemma lem8239233 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8239234 {A P : Type'} (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term811 A P lt2 _109625 s a) = (term624 A P lt2 _109625 s a).
Proof. exact (@lem8239233 (term624 A P lt2 _109625 s a)). Qed.
Lemma lem8239235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239236 {A P : Type'} (lt2 : type1402 A) (_109625 : A) (s : P -> A) (a : P) : (term812 A P lt2 _109625 s a) = (term813 A P lt2 _109625 s a).
Proof. exact (MK_COMB (@lem8239235) (@lem8239234 A P lt2 _109625 s a)). Qed.
Lemma lem8239237 {A B : Type'} (f : A -> B) (g : A -> B) (_109625 : A) : ((@I (A -> B) f _109625) = (@I (A -> B) g _109625)) = ((@I (A -> B) f _109625) = (@I (A -> B) g _109625)).
Proof. exact (eq_refl ((@I (A -> B) f _109625) = (@I (A -> B) g _109625))). Qed.
Lemma lem8239238 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109625 : A) : (term810 A B P lt2 s a f g _109625) = (term814 A B P lt2 s a f g _109625).
Proof. exact (MK_COMB (@lem8239236 A P lt2 _109625 s a) (@lem8239237 A B f g _109625)). Qed.
Lemma lem8239239 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_109625 : A) : (term807 A B P f g lt2 _109625 s a) = (term814 A B P lt2 s a f g _109625).
Proof. exact (TRANS (@lem8239231 A B P lt2 s a f g _109625) (@lem8239238 A B P lt2 s a f g _109625)). Qed.
Lemma lem8239242 {A B P : Type'} (_109625 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term814 A B P lt2 s a f g _109625.
Proof. exact (EQ_MP (@lem8239239 A B P lt2 s a f g _109625) (@lem8239228 A B P _109625 p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239243 {A B P : Type'} (_109625 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term814 A B P lt2 s a f g _109625.
Proof. exact (@lem8239242 A B P _109625 p lt2 s g t f a fixed h1). Qed.
Lemma lem8239244 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term815 A B P lt2 s z f g a.
Proof. exact (@lem8239243 A B P (term662 A B P z f g a) p lt2 s g t f a fixed h1). Qed.
Lemma lem8239247 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : (term665 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (@lem8239244 A B P z p lt2 s g t f a fixed h3 (@lem8239195 A B P z p lt2 s g t f a fixed h1 h2 h3)). Qed.
Lemma lem8239248 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term816 A B P z f g a.
Proof. exact (fun h0 : term672 A B P z f g a => @lem8239247 A B P z p lt2 s g t f a fixed h1 h2 h3). Qed.
Lemma lem8239250 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239251 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term816 A B P z f g a) = ((term665 A B P z f g a) = (term668 A B P z f g a)).
Proof. exact (@lem8239250 ((term665 A B P z f g a) = (term668 A B P z f g a))). Qed.
Lemma lem8239252 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : (term665 A B P z f g a) = (term668 A B P z f g a).
Proof. exact (EQ_MP (@lem8239251 A B P z f g a) (@lem8239248 A B P z p lt2 s g t f a fixed h1 h2 h3)). Qed.
Lemma lem8239254 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p f a.
Proof. exact (proj1 (@lem8236994 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239255 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term765 A B P p f a.
Proof. exact (fun h0 : term637 A B P p f a => @lem8239254 A B P p lt2 s g t f a fixed h1). Qed.
Lemma lem8239257 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239258 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term765 A B P p f a) = (term634 A B P p f a).
Proof. exact (@lem8239257 (term634 A B P p f a)). Qed.
Lemma lem8239259 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p f a.
Proof. exact (EQ_MP (@lem8239258 A B P p f a) (@lem8239255 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8239278 {A B P : Type'} (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term653 A B P _109619 p _109620 _109621) = (term656 A B P _109620 p _109619 _109621).
Proof. exact (@lem8239277 (term634 A B P p _109620 _109621) (term637 A B P p _109619 _109621)). Qed.
Lemma lem8239284 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) : (term818 A B P z _109619 _109620 _109621) = (term818 A B P z _109619 _109620 _109621).
Proof. exact (eq_refl (term818 A B P z _109619 _109620 _109621)). Qed.
Lemma lem8239285 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term764 A B P z _109619 p _109620 _109621) = (term872 A B P z _109620 p _109619 _109621).
Proof. exact (MK_COMB (@lem8239284 A B P z _109619 _109620 _109621) (@lem8239278 A B P _109620 p _109619 _109621)). Qed.
Lemma lem8239289 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8239290 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term872 A B P z _109620 p _109619 _109621) = (term873 A B P z _109620 p _109619 _109621).
Proof. exact (@lem8239289 (term634 A B P p _109620 _109621) (term672 A B P z _109619 _109620 _109621) (term637 A B P p _109619 _109621)). Qed.
Lemma lem8239308 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term764 A B P z _109619 p _109620 _109621) = (term873 A B P z _109620 p _109619 _109621).
Proof. exact (TRANS (@lem8239285 A B P z _109620 p _109619 _109621) (@lem8239290 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8239310 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term874 A B P z _109619 p _109620 _109621) = (term875 A B P z _109620 p _109619 _109621).
Proof. exact (MK_COMB (@lem8239309) (@lem8239308 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239328 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term873 A B P z _109620 p _109619 _109621) = (term873 A B P z _109620 p _109619 _109621).
Proof. exact (eq_refl (term873 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239329 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : ((term764 A B P z _109619 p _109620 _109621) = (term873 A B P z _109620 p _109619 _109621)) = ((term873 A B P z _109620 p _109619 _109621) = (term873 A B P z _109620 p _109619 _109621)).
Proof. exact (MK_COMB (@lem8239310 A B P z _109620 p _109619 _109621) (@lem8239328 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239331 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8239332 (x : Prop) : (x = x) = True.
Proof. exact (@lem8239331 Prop x). Qed.
Lemma lem8239333 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : ((term873 A B P z _109620 p _109619 _109621) = (term873 A B P z _109620 p _109619 _109621)) = True.
Proof. exact (@lem8239332 (term873 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239334 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : ((term764 A B P z _109619 p _109620 _109621) = (term873 A B P z _109620 p _109619 _109621)) = True.
Proof. exact (TRANS (@lem8239329 A B P z _109620 p _109619 _109621) (@lem8239333 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239335 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : True = ((term764 A B P z _109619 p _109620 _109621) = (term873 A B P z _109620 p _109619 _109621)).
Proof. exact (SYM (@lem8239334 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239336 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term764 A B P z _109619 p _109620 _109621) = (term873 A B P z _109620 p _109619 _109621).
Proof. exact (EQ_MP (@lem8239335 A B P z _109620 p _109619 _109621) (@lem0)). Qed.
Lemma lem8239337 {A B P : Type'} (_109620 : A -> B) (_109619 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term873 A B P z _109620 p _109619 _109621.
Proof. exact (EQ_MP (@lem8239336 A B P z _109620 p _109619 _109621) (@lem8237735 A B P _109619 _109620 _109621 lt2 s z p h1)). Qed.
Lemma lem8239339 (b : Prop) (a : Prop) : (a \/ b) = (term790 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8239340 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term873 A B P z _109620 p _109619 _109621) = (term876 A B P z _109619 p _109620 _109621).
Proof. exact (@lem8239339 (term877 A B P z _109620 p _109619 _109621) (term634 A B P p _109620 _109621)). Qed.
Lemma lem8239342 (a : Prop) (b : Prop) : (term792 a b) = (term793 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8239343 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term878 A B P z _109620 p _109619 _109621) = (term879 A B P z _109620 p _109619 _109621).
Proof. exact (@lem8239342 (term672 A B P z _109619 _109620 _109621) (term637 A B P p _109619 _109621)). Qed.
Lemma lem8239345 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8239346 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) : (term835 A B P z _109619 _109620 _109621) = ((term665 A B P z _109619 _109620 _109621) = (term668 A B P z _109619 _109620 _109621)).
Proof. exact (@lem8239345 ((term665 A B P z _109619 _109620 _109621) = (term668 A B P z _109619 _109620 _109621))). Qed.
Lemma lem8239347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8239348 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) : (term858 A B P z _109619 _109620 _109621) = (term859 A B P z _109619 _109620 _109621).
Proof. exact (MK_COMB (@lem8239347) (@lem8239346 A B P z _109619 _109620 _109621)). Qed.
Lemma lem8239350 (a : Prop) : (term208 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8239351 {A B P : Type'} (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term796 A B P p _109619 _109621) = (term634 A B P p _109619 _109621).
Proof. exact (@lem8239350 (term634 A B P p _109619 _109621)). Qed.
Lemma lem8239352 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term879 A B P z _109620 p _109619 _109621) = (term880 A B P z _109620 p _109619 _109621).
Proof. exact (MK_COMB (@lem8239348 A B P z _109619 _109620 _109621) (@lem8239351 A B P p _109619 _109621)). Qed.
Lemma lem8239353 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term878 A B P z _109620 p _109619 _109621) = (term880 A B P z _109620 p _109619 _109621).
Proof. exact (TRANS (@lem8239343 A B P z _109620 p _109619 _109621) (@lem8239352 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239355 {A B P : Type'} (z : type518 A B P) (_109620 : A -> B) (p : type560 A B P) (_109619 : A -> B) (_109621 : P) : (term881 A B P z _109620 p _109619 _109621) = (term882 A B P z _109620 p _109619 _109621).
Proof. exact (MK_COMB (@lem8239354) (@lem8239353 A B P z _109620 p _109619 _109621)). Qed.
Lemma lem8239356 {A B P : Type'} (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term634 A B P p _109620 _109621) = (term634 A B P p _109620 _109621).
Proof. exact (eq_refl (term634 A B P p _109620 _109621)). Qed.
Lemma lem8239357 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term876 A B P z _109619 p _109620 _109621) = (term883 A B P z _109619 p _109620 _109621).
Proof. exact (MK_COMB (@lem8239355 A B P z _109620 p _109619 _109621) (@lem8239356 A B P p _109620 _109621)). Qed.
Lemma lem8239358 {A B P : Type'} (z : type518 A B P) (_109619 : A -> B) (p : type560 A B P) (_109620 : A -> B) (_109621 : P) : (term873 A B P z _109620 p _109619 _109621) = (term883 A B P z _109619 p _109620 _109621).
Proof. exact (TRANS (@lem8239340 A B P z _109619 p _109620 _109621) (@lem8239357 A B P z _109619 p _109620 _109621)). Qed.
Lemma lem8239360 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term880 A B P z g p f a.
Proof. exact (conj (@lem8239252 A B P z p lt2 s g t f a fixed h1 h2 h3) (@lem8239259 A B P p lt2 s g t f a fixed h3)). Qed.
Lemma lem8239362 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term883 A B P z _109619 p _109620 _109621.
Proof. exact (EQ_MP (@lem8239358 A B P z _109619 p _109620 _109621) (@lem8239337 A B P _109620 _109619 _109621 lt2 s z p h1)). Qed.
Lemma lem8239363 {A B P : Type'} (_109619 : A -> B) (_109620 : A -> B) (_109621 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term883 A B P z _109619 p _109620 _109621.
Proof. exact (@lem8239362 A B P _109619 _109620 _109621 lt2 s z p h1). Qed.
Lemma lem8239364 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term569 A B P lt2 s z p) : term883 A B P z f p g a.
Proof. exact (@lem8239363 A B P f g a lt2 s z p h1). Qed.
Lemma lem8239367 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term637 A B P p g a) (h3 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p g a.
Proof. exact (@lem8239364 A B P f g a lt2 s z p h1 (@lem8239360 A B P z p lt2 s g t f a fixed h1 h2 h3)). Qed.
Lemma lem8239368 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term639 A B P p lt2 s g t f a fixed) : term765 A B P p g a.
Proof. exact (fun h0 : term637 A B P p g a => @lem8239367 A B P z p lt2 s g t f a fixed h1 h0 h2). Qed.
Lemma lem8239370 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239371 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term765 A B P p g a) = (term634 A B P p g a).
Proof. exact (@lem8239370 (term634 A B P p g a)). Qed.
Lemma lem8239372 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term639 A B P p lt2 s g t f a fixed) : term634 A B P p g a.
Proof. exact (EQ_MP (@lem8239371 A B P p g a) (@lem8239368 A B P z p lt2 s g t f a fixed h1 h2)). Qed.
Lemma lem8239375 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8239377 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term637 A B P p g a) = (term864 A B P p g a).
Proof. exact (@lem8239375 (term634 A B P p g a)). Qed.
Lemma lem8239380 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term639 A B P p lt2 s g t f a fixed) : term864 A B P p g a.
Proof. exact (EQ_MP (@lem8239377 A B P p g a) (@lem8237669 A B P p lt2 s g t f a fixed h1)). Qed.
Lemma lem8239383 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term639 A B P p lt2 s g t f a fixed) : False.
Proof. exact (@lem8239380 A B P p lt2 s g t f a fixed h2 (@lem8239372 A B P z p lt2 s g t f a fixed h1 h2)). Qed.
Lemma lem8239384 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term639 A B P p lt2 s g t f a fixed) : term843.
Proof. exact (fun h0 : ~ False => @lem8239383 A B P z p lt2 s g t f a fixed h1 h2). Qed.
Lemma lem8239386 (p : Prop) : (term766 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8239387 : term843 = False.
Proof. exact (@lem8239386 False). Qed.
Lemma lem8239388 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term639 A B P p lt2 s g t f a fixed) : False.
Proof. exact (EQ_MP (@lem8239387) (@lem8239384 A B P z p lt2 s g t f a fixed h1 h2)). Qed.
Lemma lem8239389 {A B P : Type'} (z : type518 A B P) (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (fixed : B) (t : type558 A B P) (g : A -> B) (a : P) (h1 : term569 A B P lt2 s z p) (h2 : term477 A B P p lt2 s z' t) (h3 : term648 A B P p lt2 s f fixed t g a) : False.
Proof. exact (or_elim (@lem8236982 A B P p lt2 s f fixed t g a h3) (fun h0 : term645 A B P p lt2 s f t g a => @lem8238565 A B P z' p lt2 s f fixed t g a h2 h0 h3) (fun h0 : term642 A B P p lt2 s f fixed t g a => @lem8238963 A B P z p lt2 s f fixed t g a h1 h0 h3)). Qed.
Lemma lem8239390 {A B P : Type'} (z : type518 A B P) (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term569 A B P lt2 s z p) (h2 : term477 A B P p lt2 s z' t) (h3 : term330 A B P p lt2 s g t f a fixed) : False.
Proof. exact (or_elim (@lem8236545 A B P p lt2 s g t f a fixed h3) (fun h0 : term648 A B P p lt2 s f fixed t g a => @lem8239389 A B P z z' p lt2 s f fixed t g a h1 h2 h0) (fun h0 : term639 A B P p lt2 s g t f a fixed => @lem8239388 A B P z p lt2 s g t f a fixed h1 h0)). Qed.
Lemma lem8239391 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term31 A B P p lt2 s t) (h2 : term569 A B P lt2 s z p) (h3 : term330 A B P p lt2 s g t f a fixed) : False.
Proof. exact (ex_elim (@lem8235662 A B P p lt2 s t h1) (fun z' : type518 A B P => fun h0 : term479 A B P p lt2 s t z' => @lem8239390 A B P z z' p lt2 s g t f a fixed h2 h0 h3)). Qed.
Lemma lem8239392 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term330 A B P p lt2 s g t f a fixed) : False.
Proof. exact (ex_elim (@lem8235942 A B P lt2 s p h1) (fun z : type518 A B P => fun h0 : term571 A B P lt2 s p z => @lem8239391 A B P z p lt2 s g t f a fixed h2 h0 h3)). Qed.
Lemma lem8239393 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term330 A B P p lt2 s g t f a fixed) : (term330 A B P p lt2 s g t f a fixed) = False.
Proof. exact (prop_ext (fun h4 : term330 A B P p lt2 s g t f a fixed => @lem8239392 A B P p lt2 s g t f a fixed h1 h2 h3) (fun h4 : False => @lem8235336 A B P p lt2 s g t f a fixed h3)). Qed.
Lemma lem8239394 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : A -> B) (t : type558 A B P) (f : A -> B) (a : P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term330 A B P p lt2 s g t f a fixed) : False.
Proof. exact (EQ_MP (@lem8239393 A B P p lt2 s g t f a fixed h1 h2 h3) (@lem8235336 A B P p lt2 s g t f a fixed h3)). Qed.
Lemma lem8239395 {A B P : Type'} (g : A -> B) (f : A -> B) (a : P) (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term329 A B P p lt2 s g t f a fixed.
Proof. exact (fun h0 : term330 A B P p lt2 s g t f a fixed => @lem8239394 A B P p lt2 s g t f a fixed h1 h2 h0). Qed.
Lemma lem8239396 {A B P : Type'} (g : A -> B) (f : A -> B) (a : P) (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term278 A B P p lt2 s g t f a fixed.
Proof. exact (EQ_MP (@lem8235335 A B P p lt2 s g t f a fixed) (@lem8239395 A B P g f a fixed p lt2 s t h1 h2)). Qed.
Lemma lem8239401 {A B P : Type'} (g : A -> B) (f : A -> B) (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term287 A B P p lt2 s g t f fixed.
Proof. exact (fun a : P => @lem8239396 A B P g f a fixed p lt2 s t h1 h2). Qed.
Lemma lem8239406 {A B P : Type'} (f : A -> B) (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term289 A B P p lt2 s t f fixed.
Proof. exact (fun g : A -> B => @lem8239401 A B P g f fixed p lt2 s t h1 h2). Qed.
Lemma lem8239411 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term291 A B P p lt2 s t fixed.
Proof. exact (fun f : A -> B => @lem8239406 A B P f fixed p lt2 s t h1 h2). Qed.
Lemma lem8239412 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term317 A B P p lt2 s t fixed.
Proof. exact (fun h0 : term72 A B P lt2 s p => @lem8239411 A B P fixed p lt2 s t h0 h1). Qed.
Lemma lem8239413 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (fixed : B) : term318 A B P p lt2 s t fixed.
Proof. exact (fun h0 : term31 A B P p lt2 s t => @lem8239412 A B P fixed p lt2 s t h0). Qed.
Lemma lem8239418 {A B P : Type'} (p : type560 A B P) (s : P -> A) (t : type558 A B P) (fixed : B) : term320 A B P p s t fixed.
Proof. exact (fun lt2 : type1402 A => @lem8239413 A B P p lt2 s t fixed). Qed.
Lemma lem8239423 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : term322 A B P p t fixed.
Proof. exact (fun s : P -> A => @lem8239418 A B P p s t fixed). Qed.
Lemma lem8239428 {A B P : Type'} (t : type558 A B P) (fixed : B) : term324 A B P t fixed.
Proof. exact (fun p : type560 A B P => @lem8239423 A B P p t fixed). Qed.
Lemma lem8239433 {A B P : Type'} (fixed : B) : term326 A B P fixed.
Proof. exact (fun t : type558 A B P => @lem8239428 A B P t fixed). Qed.
Lemma lem8239438 {A B P : Type'} : term328 A B P.
Proof. exact (fun fixed : B => @lem8239433 A B P fixed). Qed.
Lemma lem8239439 {A B P : Type'} : term230 A B P.
Proof. exact (EQ_MP (@lem8235329 A B P) (@lem8239438 A B P)). Qed.
Lemma lem8239440 {A B P : Type'} (fixed : B) : term884 A B P fixed.
Proof. exact (@lem8239439 A B P fixed). Qed.
Lemma lem8239441 {A B P : Type'} (fixed : B) : (term884 A B P fixed) = (term226 A B P fixed).
Proof. exact (eq_refl (term884 A B P fixed)). Qed.
Lemma lem8239442 {A B P : Type'} (fixed : B) : term226 A B P fixed.
Proof. exact (EQ_MP (@lem8239441 A B P fixed) (@lem8239440 A B P fixed)). Qed.
Lemma lem8239443 {A B P : Type'} (fixed : B) (t : type558 A B P) : term885 A B P fixed t.
Proof. exact (@lem8239442 A B P fixed t). Qed.
Lemma lem8239444 {A B P : Type'} (t : type558 A B P) (fixed : B) : (term885 A B P fixed t) = (term222 A B P t fixed).
Proof. exact (eq_refl (term885 A B P fixed t)). Qed.
Lemma lem8239445 {A B P : Type'} (t : type558 A B P) (fixed : B) : term222 A B P t fixed.
Proof. exact (EQ_MP (@lem8239444 A B P t fixed) (@lem8239443 A B P fixed t)). Qed.
Lemma lem8239446 {A B P : Type'} (t : type558 A B P) (fixed : B) (p : type560 A B P) : term886 A B P t fixed p.
Proof. exact (@lem8239445 A B P t fixed p). Qed.
Lemma lem8239447 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term886 A B P t fixed p) = (term218 A B P p t fixed).
Proof. exact (eq_refl (term886 A B P t fixed p)). Qed.
Lemma lem8239448 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) : term218 A B P p t fixed.
Proof. exact (EQ_MP (@lem8239447 A B P p t fixed) (@lem8239446 A B P t fixed p)). Qed.
Lemma lem8239449 {A B P : Type'} (p : type560 A B P) (t : type558 A B P) (fixed : B) (s : P -> A) : term887 A B P p t fixed s.
Proof. exact (@lem8239448 A B P p t fixed s). Qed.
Lemma lem8239450 {A B P : Type'} (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term887 A B P p t fixed s) = (term214 A B P s p t fixed).
Proof. exact (eq_refl (term887 A B P p t fixed s)). Qed.
Lemma lem8239451 {A B P : Type'} (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term214 A B P s p t fixed.
Proof. exact (EQ_MP (@lem8239450 A B P s p t fixed) (@lem8239449 A B P p t fixed s)). Qed.
Lemma lem8239452 {A B P : Type'} (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (lt2 : type1402 A) : term888 A B P s p t fixed lt2.
Proof. exact (@lem8239451 A B P s p t fixed lt2). Qed.
Lemma lem8239453 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : (term888 A B P s p t fixed lt2) = (term203 A B P lt2 s p t fixed).
Proof. exact (eq_refl (term888 A B P s p t fixed lt2)). Qed.
Lemma lem8239454 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term203 A B P lt2 s p t fixed.
Proof. exact (EQ_MP (@lem8239453 A B P lt2 s p t fixed) (@lem8239452 A B P s p t fixed lt2)). Qed.
Lemma lem8239456 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) : term203 A B P lt2 s p t fixed.
Proof. exact (@lem8234374 A B P lt2 s p t fixed (@lem8239454 A B P lt2 s p t fixed)). Qed.
Lemma lem8239457 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term209 A B P lt2 s p t fixed.
Proof. exact (@lem8239456 A B P lt2 s p t fixed (@lem8233812 A B P p lt2 s t h1)). Qed.
Lemma lem8239458 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term201 A B P lt2 s p t fixed.
Proof. exact (@lem8239457 A B P fixed p lt2 s t h2 (@lem8233813 A B P lt2 s p h1)). Qed.
Lemma lem8239459 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term202 A B P lt2 s p t fixed) : False.
Proof. exact (@lem8239458 A B P fixed p lt2 s t h1 h2 (@lem8234358 A B P lt2 s p t fixed h3)). Qed.
Lemma lem8239460 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term202 A B P lt2 s p t fixed) : (term202 A B P lt2 s p t fixed) = False.
Proof. exact (prop_ext (fun h4 : term202 A B P lt2 s p t fixed => @lem8239459 A B P lt2 s p t fixed h1 h2 h3) (fun h4 : False => @lem8234358 A B P lt2 s p t fixed h3)). Qed.
Lemma lem8239461 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) (fixed : B) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) (h3 : term202 A B P lt2 s p t fixed) : False.
Proof. exact (EQ_MP (@lem8239460 A B P lt2 s p t fixed h1 h2 h3) (@lem8234358 A B P lt2 s p t fixed h3)). Qed.
Lemma lem8239462 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term201 A B P lt2 s p t fixed.
Proof. exact (fun h0 : term202 A B P lt2 s p t fixed => @lem8239461 A B P lt2 s p t fixed h1 h2 h0). Qed.
Lemma lem8239463 {A B P : Type'} (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term197 A B P lt2 s p t fixed.
Proof. exact (EQ_MP (@lem8234357 A B P lt2 s p t fixed) (@lem8239462 A B P fixed p lt2 s t h1 h2)). Qed.
Lemma lem8239464 {A B P : Type'} (anything : P -> A) (fixed : B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term198 A B P lt2 s anything p t fixed.
Proof. exact (EQ_MP (@lem8234353 A B P lt2 s anything p t fixed) (@lem8239463 A B P fixed p lt2 s t h1 h2)). Qed.
Lemma lem8239465 {A B P : Type'} (anything : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term889 A B P lt2 s p t anything.
Proof. exact (ex_intro (term890 A B P lt2 s p t anything) (term891 A B P p t) (@lem8239464 A B P anything (@el B) p lt2 s t h1 h2)). Qed.
Lemma lem8239466 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term892 A B P lt2 s p t.
Proof. exact (ex_intro (term893 A B P lt2 s p t) (term894 A B P) (@lem8239465 A B P (@el (P -> A)) p lt2 s t h1 h2)). Qed.
Lemma lem8239467 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term14 A B P lt2 s p t.
Proof. exact (ex_intro (term895 A B P lt2 s p t) (term96 A B P) (@lem8239466 A B P p lt2 s t h1 h2)). Qed.
Lemma lem8239468 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : (term72 A B P lt2 s p) = (term14 A B P lt2 s p t).
Proof. exact (prop_ext (fun h3 : term72 A B P lt2 s p => @lem8239467 A B P p lt2 s t h1 h2) (fun h3 : term14 A B P lt2 s p t => @lem8233813 A B P lt2 s p h1)). Qed.
Lemma lem8239469 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term72 A B P lt2 s p) (h2 : term31 A B P p lt2 s t) : term14 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8239468 A B P p lt2 s t h1 h2) (@lem8233813 A B P lt2 s p h1)). Qed.
Lemma lem8239470 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term75 A B P lt2 s p t.
Proof. exact (fun h0 : term72 A B P lt2 s p => @lem8239469 A B P p lt2 s t h0 h1). Qed.
Lemma lem8239471 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : (term31 A B P p lt2 s t) = (term75 A B P lt2 s p t).
Proof. exact (prop_ext (fun h2 : term31 A B P p lt2 s t => @lem8239470 A B P p lt2 s t h1) (fun h2 : term75 A B P lt2 s p t => @lem8233812 A B P p lt2 s t h1)). Qed.
Lemma lem8239472 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) (h1 : term31 A B P p lt2 s t) : term75 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8239471 A B P p lt2 s t h1) (@lem8233812 A B P p lt2 s t h1)). Qed.
Lemma lem8239473 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : term77 A B P lt2 s p t.
Proof. exact (fun h0 : term31 A B P p lt2 s t => @lem8239472 A B P p lt2 s t h0). Qed.
Lemma lem8239478 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term81 A B P lt2 s p.
Proof. exact (fun t : type558 A B P => @lem8239473 A B P lt2 s p t). Qed.
Lemma lem8239483 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term85 A B P lt2 p.
Proof. exact (fun s : P -> A => @lem8239478 A B P lt2 s p). Qed.
Lemma lem8239488 {A B P : Type'} (lt2 : type1402 A) : term89 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8239483 A B P lt2 p). Qed.
Lemma lem8239493 {A B P : Type'} : term93 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8239488 A B P lt2). Qed.
Lemma lem8239494 {A B P : Type'} : term92 A B P.
Proof. exact (EQ_MP (@lem8233811 A B P) (@lem8239493 A B P)). Qed.
