Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPERADMISSIBLE_TAIL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
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
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Lemma lem8239568 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8239569 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8239570 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8239569 t1) (@lem8239568 t1)). Qed.
Lemma lem8239571 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8239570 t1 t2). Qed.
Lemma lem8239572 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8239573 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8239572 t1 t2) (@lem8239571 t1 t2)). Qed.
Lemma lem8239574 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8239573 t1 t2 t3). Qed.
Lemma lem8239575 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8239576 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8239575 t1 t2 t3) (@lem8239574 t1 t2 t3)). Qed.
Lemma lem8239577 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8239576 t1 t2 t3)). Qed.
Lemma lem8239578 {A B P : Type'} (lt2 : type1402 A) : term7 A B P lt2.
Proof. exact (@lem8094644 A B P lt2). Qed.
Lemma lem8239579 {A B P : Type'} (lt2 : type1402 A) : (term7 A B P lt2) = (term8 A B P lt2).
Proof. exact (eq_refl (term7 A B P lt2)). Qed.
Lemma lem8239580 {A B P : Type'} (lt2 : type1402 A) : term8 A B P lt2.
Proof. exact (EQ_MP (@lem8239579 A B P lt2) (@lem8239578 A B P lt2)). Qed.
Lemma lem8239581 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : term9 A B P lt2 s.
Proof. exact (@lem8239580 A B P lt2 s). Qed.
Lemma lem8239582 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : (term9 A B P lt2 s) = (term10 A B P lt2 s).
Proof. exact (eq_refl (term9 A B P lt2 s)). Qed.
Lemma lem8239583 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) : term10 A B P lt2 s.
Proof. exact (EQ_MP (@lem8239582 A B P lt2 s) (@lem8239581 A B P lt2 s)). Qed.
Lemma lem8239584 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term11 A B P lt2 s p.
Proof. exact (@lem8239583 A B P lt2 s p). Qed.
Lemma lem8239585 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term11 A B P lt2 s p) = (term12 A B P lt2 s p).
Proof. exact (eq_refl (term11 A B P lt2 s p)). Qed.
Lemma lem8239586 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term12 A B P lt2 s p.
Proof. exact (EQ_MP (@lem8239585 A B P lt2 s p) (@lem8239584 A B P lt2 s p)). Qed.
Lemma lem8239587 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : term13 A B P lt2 s p t.
Proof. exact (@lem8239586 A B P lt2 s p t). Qed.
Lemma lem8239588 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (term13 A B P lt2 s p t) = ((@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t)).
Proof. exact (eq_refl (term13 A B P lt2 s p t)). Qed.
Lemma lem8239590 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term15 _143606 _143608 _143614 lt2.
Proof. exact (@lem8096071 _143606 _143608 _143614 lt2). Qed.
Lemma lem8239591 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : (term15 _143606 _143608 _143614 lt2) = (term16 _143606 _143608 _143614 lt2).
Proof. exact (eq_refl (term15 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8239592 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term16 _143606 _143608 _143614 lt2.
Proof. exact (EQ_MP (@lem8239591 _143606 _143608 _143614 lt2) (@lem8239590 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8239593 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term17 _143606 _143608 _143614 lt2 p.
Proof. exact (@lem8239592 _143606 _143608 _143614 lt2 p). Qed.
Lemma lem8239594 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : (term17 _143606 _143608 _143614 lt2 p) = (term18 _143606 _143608 _143614 lt2 p).
Proof. exact (eq_refl (term17 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8239595 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term18 _143606 _143608 _143614 lt2 p.
Proof. exact (EQ_MP (@lem8239594 _143606 _143608 _143614 lt2 p) (@lem8239593 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8239596 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term19 _143606 _143608 _143614 lt2 p s.
Proof. exact (@lem8239595 _143606 _143608 _143614 lt2 p s). Qed.
Lemma lem8239597 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : (term19 _143606 _143608 _143614 lt2 p s) = (term20 _143606 _143608 _143614 lt2 p s).
Proof. exact (eq_refl (term19 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8239598 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term20 _143606 _143608 _143614 lt2 p s.
Proof. exact (EQ_MP (@lem8239597 _143606 _143608 _143614 lt2 p s) (@lem8239596 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8239599 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : term21 _143606 _143608 _143614 lt2 p s t.
Proof. exact (@lem8239598 _143606 _143608 _143614 lt2 p s t). Qed.
Lemma lem8239600 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (term21 _143606 _143608 _143614 lt2 p s t) = ((@superadmissible _143606 _143608 _143614 lt2 p s t) = (term22 _143606 _143608 _143614 lt2 p s t)).
Proof. exact (eq_refl (term21 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8239602 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term23 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8239603 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term23 _143449 _143452 _143456 _143457 _143462 p) = (term24 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term23 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8239604 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term24 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8239603 _143449 _143452 _143456 _143457 _143462 p) (@lem8239602 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8239605 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term25 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8239604 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8239606 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term25 _143449 _143452 _143456 _143457 _143462 p lt2) = (term26 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term25 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8239607 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term26 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8239606 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8239605 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8239608 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term27 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8239607 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8239609 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term27 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term28 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term27 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8239610 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term28 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8239609 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8239608 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8239611 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8239610 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8239612 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term29 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8239635 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8239612 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8239611 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8239636 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (@admissible A B A A P lt2 p s t) = (term31 A B P p lt2 s t).
Proof. exact (@lem8239635 A B A A P p lt2 s t). Qed.
Lemma lem8239665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8239666 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term32 A B P lt2 p s t) = (term33 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8239665) (@lem8239636 A B P p lt2 s t)). Qed.
Lemma lem8239683 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term34 A B P p t lt2 s) = (term34 A B P p t lt2 s).
Proof. exact (eq_refl (term34 A B P p t lt2 s)). Qed.
Lemma lem8239684 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term35 A B P p t lt2 s) = (term36 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8239666 A B P p lt2 s t) (@lem8239683 A B P p t lt2 s)). Qed.
Lemma lem8239687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239688 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term37 A B P p t lt2 s) = (term38 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8239687) (@lem8239684 A B P p t lt2 s)). Qed.
Lemma lem8239690 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (@superadmissible _143606 _143608 _143614 lt2 p s t) = (term22 _143606 _143608 _143614 lt2 p s t).
Proof. exact (EQ_MP (@lem8239600 _143606 _143608 _143614 lt2 p s t) (@lem8239599 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8239691 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type558 A B P) : (@superadmissible A B P lt2 p s t) = (term22 A B P lt2 p s t).
Proof. exact (@lem8239690 A B P lt2 p s t). Qed.
Lemma lem8239692 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (t : type557 A B P) : (term39 A B P lt2 p s t) = (term40 A B P lt2 p s t).
Proof. exact (@lem8239691 A B P lt2 p s (term41 A B P t)). Qed.
Lemma lem8239696 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term30 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8239612 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8239611 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8239697 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type560 A B P) : (@admissible A B A Prop P lt2 p s t) = (term42 A B P p lt2 s t).
Proof. exact (@lem8239696 A B A Prop P p lt2 s t). Qed.
Lemma lem8239698 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term43 A B P lt2 s p) = (term44 A B P lt2 s p).
Proof. exact (@lem8239697 A B P (term45 A B P) lt2 s p). Qed.
Lemma lem8239716 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239717 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8239716 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8239718 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (@lem8239717 A B P (term45 A B P) f). Qed.
Lemma lem8239719 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8239720 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8239719 A B P f)). Qed.
Lemma lem8239721 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8239722 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (MK_COMB (@lem8239720 A B P) (@lem8239721 A B f)). Qed.
Lemma lem8239723 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8239724 {A B P : Type'} (f : A -> B) : (term52 A B P f) = (term53 A B P f).
Proof. exact (MK_COMB (@lem8239723 P) (@lem8239722 A B P f)). Qed.
Lemma lem8239725 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8239726 {A B P : Type'} (f : A -> B) : ((term48 A B P f) = (term49 A B P f)) = ((term49 A B P f) = (term50 P)).
Proof. exact (MK_COMB (@lem8239724 A B P f) (@lem8239725 A B P f)). Qed.
Lemma lem8239727 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (EQ_MP (@lem8239726 A B P f) (@lem8239718 A B P f)). Qed.
Lemma lem8239728 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239729 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = (term55 P a).
Proof. exact (MK_COMB (@lem8239727 A B P f) (@lem8239728 P a)). Qed.
Lemma lem8239731 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239732 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8239731 P Prop f y). Qed.
Lemma lem8239733 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8239732 P (term50 P) a). Qed.
Lemma lem8239734 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8239735 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun a : P => @lem8239734 P a)). Qed.
Lemma lem8239736 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239737 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8239735 P) (@lem8239736 P a)). Qed.
Lemma lem8239738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8239739 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8239738) (@lem8239737 P a)). Qed.
Lemma lem8239740 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8239741 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8239739 P a) (@lem8239740 P a)). Qed.
Lemma lem8239742 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8239741 P a) (@lem8239733 P a)). Qed.
Lemma lem8239743 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = True.
Proof. exact (TRANS (@lem8239729 A B P f a) (@lem8239742 P a)). Qed.
Lemma lem8239744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8239745 {A B P : Type'} (f : A -> B) (a : P) : (term61 A B P f a) = (and True).
Proof. exact (MK_COMB (@lem8239744) (@lem8239743 A B P f a)). Qed.
Lemma lem8239749 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239750 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8239749 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8239751 {A B P : Type'} (g : A -> B) : (term48 A B P g) = (term49 A B P g).
Proof. exact (@lem8239750 A B P (term45 A B P) g). Qed.
Lemma lem8239752 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8239753 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8239752 A B P f)). Qed.
Lemma lem8239754 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8239755 {A B P : Type'} (g : A -> B) : (term48 A B P g) = (term49 A B P g).
Proof. exact (MK_COMB (@lem8239753 A B P) (@lem8239754 A B g)). Qed.
Lemma lem8239756 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8239757 {A B P : Type'} (g : A -> B) : (term52 A B P g) = (term53 A B P g).
Proof. exact (MK_COMB (@lem8239756 P) (@lem8239755 A B P g)). Qed.
Lemma lem8239758 {A B P : Type'} (g : A -> B) : (term49 A B P g) = (term50 P).
Proof. exact (eq_refl (term49 A B P g)). Qed.
Lemma lem8239759 {A B P : Type'} (g : A -> B) : ((term48 A B P g) = (term49 A B P g)) = ((term49 A B P g) = (term50 P)).
Proof. exact (MK_COMB (@lem8239757 A B P g) (@lem8239758 A B P g)). Qed.
Lemma lem8239760 {A B P : Type'} (g : A -> B) : (term49 A B P g) = (term50 P).
Proof. exact (EQ_MP (@lem8239759 A B P g) (@lem8239751 A B P g)). Qed.
Lemma lem8239761 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239762 {A B P : Type'} (g : A -> B) (a : P) : (term54 A B P g a) = (term55 P a).
Proof. exact (MK_COMB (@lem8239760 A B P g) (@lem8239761 P a)). Qed.
Lemma lem8239764 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239765 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8239764 P Prop f y). Qed.
Lemma lem8239766 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8239765 P (term50 P) a). Qed.
Lemma lem8239767 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8239768 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun a : P => @lem8239767 P a)). Qed.
Lemma lem8239769 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239770 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8239768 P) (@lem8239769 P a)). Qed.
Lemma lem8239771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8239772 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8239771) (@lem8239770 P a)). Qed.
Lemma lem8239773 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8239774 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8239772 P a) (@lem8239773 P a)). Qed.
Lemma lem8239775 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8239774 P a) (@lem8239766 P a)). Qed.
Lemma lem8239776 {A B P : Type'} (g : A -> B) (a : P) : (term54 A B P g a) = True.
Proof. exact (TRANS (@lem8239762 A B P g a) (@lem8239775 P a)). Qed.
Lemma lem8239777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8239778 {A B P : Type'} (g : A -> B) (a : P) : (term61 A B P g a) = (and True).
Proof. exact (MK_COMB (@lem8239777) (@lem8239776 A B P g a)). Qed.
Lemma lem8239787 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (eq_refl (term62 A B P lt2 s a f g)). Qed.
Lemma lem8239788 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term63 A B P lt2 s a f g) = (term64 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8239778 A B P g a) (@lem8239787 A B P lt2 s a f g)). Qed.
Lemma lem8239790 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8239791 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term64 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (@lem8239790 (term62 A B P lt2 s a f g)). Qed.
Lemma lem8239800 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term63 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8239788 A B P lt2 s a f g) (@lem8239791 A B P lt2 s a f g)). Qed.
Lemma lem8239801 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term65 A B P lt2 s a f g) = (term64 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8239745 A B P f a) (@lem8239800 A B P lt2 s a f g)). Qed.
Lemma lem8239803 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8239804 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term64 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (@lem8239803 (term62 A B P lt2 s a f g)). Qed.
Lemma lem8239813 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term65 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8239801 A B P lt2 s a f g) (@lem8239804 A B P lt2 s a f g)). Qed.
Lemma lem8239814 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239815 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term66 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8239814) (@lem8239813 A B P lt2 s a f g)). Qed.
Lemma lem8239818 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = ((p f a) = (p g a)).
Proof. exact (eq_refl ((p f a) = (p g a))). Qed.
Lemma lem8239819 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term68 A B P lt2 s f p g a) = (term69 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8239815 A B P lt2 s a f g) (@lem8239818 A B P f p g a)). Qed.
Lemma lem8239822 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term70 A B P lt2 s f p g) = (term71 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8239819 A B P lt2 s f p g a)). Qed.
Lemma lem8239823 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8239824 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term72 A B P lt2 s f p g) = (term73 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8239823 P) (@lem8239822 A B P lt2 s f p g)). Qed.
Lemma lem8239829 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term74 A B P lt2 s f p) = (term75 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8239824 A B P lt2 s f p g)). Qed.
Lemma lem8239830 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8239831 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term76 A B P lt2 s f p) = (term77 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8239830 A B) (@lem8239829 A B P lt2 s f p)). Qed.
Lemma lem8239836 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term78 A B P lt2 s p) = (term79 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8239831 A B P lt2 s f p)). Qed.
Lemma lem8239837 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8239838 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term44 A B P lt2 s p) = (term80 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8239837 A B) (@lem8239836 A B P lt2 s p)). Qed.
Lemma lem8239843 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term43 A B P lt2 s p) = (term80 A B P lt2 s p).
Proof. exact (TRANS (@lem8239698 A B P lt2 s p) (@lem8239838 A B P lt2 s p)). Qed.
Lemma lem8239844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8239845 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term81 A B P lt2 s p) = (term82 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8239844) (@lem8239843 A B P lt2 s p)). Qed.
Lemma lem8239847 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t).
Proof. exact (EQ_MP (@lem8239588 A B P lt2 s p t) (@lem8239587 A B P lt2 s p t)). Qed.
Lemma lem8239848 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type558 A B P) : (@tailadmissible A B P lt2 p s t) = (term14 A B P lt2 s p t).
Proof. exact (@lem8239847 A B P lt2 s p t). Qed.
Lemma lem8239849 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term83 A B P lt2 p s t) = (term84 A B P lt2 s p t).
Proof. exact (@lem8239848 A B P lt2 s p (term41 A B P t)). Qed.
Lemma lem8239927 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239928 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term85 A B P f y) = (f y).
Proof. exact (@lem8239927 (A -> B) (P -> B) f y). Qed.
Lemma lem8239929 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term86 A B P t f) = (term87 A B P t f).
Proof. exact (@lem8239928 A B P (term41 A B P t) f). Qed.
Lemma lem8239930 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term87 A B P t f) = (term88 A B P t f).
Proof. exact (eq_refl (term87 A B P t f)). Qed.
Lemma lem8239931 {A B P : Type'} (t : type557 A B P) : (term89 A B P t) = (term41 A B P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8239930 A B P t f)). Qed.
Lemma lem8239932 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8239933 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term86 A B P t f) = (term87 A B P t f).
Proof. exact (MK_COMB (@lem8239931 A B P t) (@lem8239932 A B f)). Qed.
Lemma lem8239934 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8239935 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term90 A B P t f) = (term91 A B P t f).
Proof. exact (MK_COMB (@lem8239934 B P) (@lem8239933 A B P t f)). Qed.
Lemma lem8239936 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term87 A B P t f) = (term88 A B P t f).
Proof. exact (eq_refl (term87 A B P t f)). Qed.
Lemma lem8239937 {A B P : Type'} (t : type557 A B P) (f : A -> B) : ((term86 A B P t f) = (term87 A B P t f)) = ((term87 A B P t f) = (term88 A B P t f)).
Proof. exact (MK_COMB (@lem8239935 A B P t f) (@lem8239936 A B P t f)). Qed.
Lemma lem8239938 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term87 A B P t f) = (term88 A B P t f).
Proof. exact (EQ_MP (@lem8239937 A B P t f) (@lem8239929 A B P t f)). Qed.
Lemma lem8239939 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239940 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term92 A B P t f a) = (term93 A B P t f a).
Proof. exact (MK_COMB (@lem8239938 A B P t f) (@lem8239939 P a)). Qed.
Lemma lem8239942 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8239943 {B P : Type'} (f : P -> B) (y : P) : (term94 B P f y) = (f y).
Proof. exact (@lem8239942 P B f y). Qed.
Lemma lem8239944 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term95 A B P t f a) = (term93 A B P t f a).
Proof. exact (@lem8239943 B P (term88 A B P t f) a). Qed.
Lemma lem8239945 {A B P : Type'} (t : type557 A B P) (f : A -> B) (x : P) : (term93 A B P t f x) = (term96 A B P t f x).
Proof. exact (eq_refl (term93 A B P t f x)). Qed.
Lemma lem8239946 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term97 A B P t f) = (term88 A B P t f).
Proof. exact (fun_ext (fun x : P => @lem8239945 A B P t f x)). Qed.
Lemma lem8239947 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8239948 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term95 A B P t f a) = (term93 A B P t f a).
Proof. exact (MK_COMB (@lem8239946 A B P t f) (@lem8239947 P a)). Qed.
Lemma lem8239949 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8239950 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term98 A B P t f a) = (term99 A B P t f a).
Proof. exact (MK_COMB (@lem8239949 B) (@lem8239948 A B P t f a)). Qed.
Lemma lem8239951 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term93 A B P t f a) = (term96 A B P t f a).
Proof. exact (eq_refl (term93 A B P t f a)). Qed.
Lemma lem8239952 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : ((term95 A B P t f a) = (term93 A B P t f a)) = ((term93 A B P t f a) = (term96 A B P t f a)).
Proof. exact (MK_COMB (@lem8239950 A B P t f a) (@lem8239951 A B P t f a)). Qed.
Lemma lem8239953 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term93 A B P t f a) = (term96 A B P t f a).
Proof. exact (EQ_MP (@lem8239952 A B P t f a) (@lem8239944 A B P t f a)). Qed.
Lemma lem8239954 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term92 A B P t f a) = (term96 A B P t f a).
Proof. exact (TRANS (@lem8239940 A B P t f a) (@lem8239953 A B P t f a)). Qed.
Lemma lem8239955 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8239956 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term100 A B P t f a) = (term101 A B P t f a).
Proof. exact (MK_COMB (@lem8239955 B) (@lem8239954 A B P t f a)). Qed.
Lemma lem8239957 {A B P : Type'} (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) (f : A -> B) (a : P) : (term102 A B P P' G H f a) = (term102 A B P P' G H f a).
Proof. exact (eq_refl (term102 A B P P' G H f a)). Qed.
Lemma lem8239958 {A B P : Type'} (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) (f : A -> B) (a : P) : ((term92 A B P t f a) = (term102 A B P P' G H f a)) = ((term96 A B P t f a) = (term102 A B P P' G H f a)).
Proof. exact (MK_COMB (@lem8239956 A B P t f a) (@lem8239957 A B P P' G H f a)). Qed.
Lemma lem8239961 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term103 A B P p f a) = (term103 A B P p f a).
Proof. exact (eq_refl (term103 A B P p f a)). Qed.
Lemma lem8239962 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) (f : A -> B) (a : P) : (term104 A B P p t P' G H f a) = (term105 A B P p t P' G H f a).
Proof. exact (MK_COMB (@lem8239961 A B P p f a) (@lem8239958 A B P t P' G H f a)). Qed.
Lemma lem8239965 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) (f : A -> B) : (term106 A B P p t P' G H f) = (term107 A B P p t P' G H f).
Proof. exact (fun_ext (fun a : P => @lem8239962 A B P p t P' G H f a)). Qed.
Lemma lem8239966 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8239967 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) (f : A -> B) : (term108 A B P p t P' G H f) = (term109 A B P p t P' G H f).
Proof. exact (MK_COMB (@lem8239966 P) (@lem8239965 A B P p t P' G H f)). Qed.
Lemma lem8239972 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) : (term110 A B P p t P' G H) = (term111 A B P p t P' G H).
Proof. exact (fun_ext (fun f : A -> B => @lem8239967 A B P p t P' G H f)). Qed.
Lemma lem8239973 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8239974 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) : (term112 A B P p t P' G H) = (term113 A B P p t P' G H).
Proof. exact (MK_COMB (@lem8239973 A B) (@lem8239972 A B P p t P' G H)). Qed.
Lemma lem8239979 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) : (term114 A B P lt2 s P' G H) = (term114 A B P lt2 s P' G H).
Proof. exact (eq_refl (term114 A B P lt2 s P' G H)). Qed.
Lemma lem8239980 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) : (term115 A B P lt2 s p t P' G H) = (term116 A B P lt2 s p t P' G H).
Proof. exact (MK_COMB (@lem8239979 A B P lt2 s P' G H) (@lem8239974 A B P p t P' G H)). Qed.
Lemma lem8239983 {A B P : Type'} (P' : type560 A B P) (G : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term117 A B P P' G lt2 s) = (term117 A B P P' G lt2 s).
Proof. exact (eq_refl (term117 A B P P' G lt2 s)). Qed.
Lemma lem8239984 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) (H : type558 A B P) : (term118 A B P lt2 s p t P' G H) = (term119 A B P lt2 s p t P' G H).
Proof. exact (MK_COMB (@lem8239983 A B P P' G lt2 s) (@lem8239980 A B P lt2 s p t P' G H)). Qed.
Lemma lem8239987 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) : (term120 A B P lt2 s p t P' G) = (term121 A B P lt2 s p t P' G).
Proof. exact (fun_ext (fun H : type558 A B P => @lem8239984 A B P lt2 s p t P' G H)). Qed.
Lemma lem8239988 {A B P : Type'} : (@ex ((A -> B) -> P -> B)) = (@ex ((A -> B) -> P -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> B))). Qed.
Lemma lem8239989 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) (G : type557 A B P) : (term122 A B P lt2 s p t P' G) = (term123 A B P lt2 s p t P' G).
Proof. exact (MK_COMB (@lem8239988 A B P) (@lem8239987 A B P lt2 s p t P' G)). Qed.
Lemma lem8239994 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) : (term124 A B P lt2 s p t P') = (term125 A B P lt2 s p t P').
Proof. exact (fun_ext (fun G : type557 A B P => @lem8239989 A B P lt2 s p t P' G)). Qed.
Lemma lem8239995 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8239996 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) (P' : type560 A B P) : (term126 A B P lt2 s p t P') = (term127 A B P lt2 s p t P').
Proof. exact (MK_COMB (@lem8239995 A B P) (@lem8239994 A B P lt2 s p t P')). Qed.
Lemma lem8240001 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term128 A B P lt2 s p t) = (term129 A B P lt2 s p t).
Proof. exact (fun_ext (fun P' : type560 A B P => @lem8239996 A B P lt2 s p t P')). Qed.
Lemma lem8240002 {A B P : Type'} : (@ex ((A -> B) -> P -> Prop)) = (@ex ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> Prop))). Qed.
Lemma lem8240003 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term84 A B P lt2 s p t) = (term130 A B P lt2 s p t).
Proof. exact (MK_COMB (@lem8240002 A B P) (@lem8240001 A B P lt2 s p t)). Qed.
Lemma lem8240008 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term83 A B P lt2 p s t) = (term130 A B P lt2 s p t).
Proof. exact (TRANS (@lem8239849 A B P lt2 s p t) (@lem8240003 A B P lt2 s p t)). Qed.
Lemma lem8240009 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term40 A B P lt2 p s t) = (term131 A B P lt2 s p t).
Proof. exact (MK_COMB (@lem8239845 A B P lt2 s p) (@lem8240008 A B P lt2 s p t)). Qed.
Lemma lem8240012 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term39 A B P lt2 p s t) = (term131 A B P lt2 s p t).
Proof. exact (TRANS (@lem8239692 A B P lt2 p s t) (@lem8240009 A B P lt2 s p t)). Qed.
Lemma lem8240013 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : (term132 A B P lt2 p s t) = (term133 A B P lt2 s p t).
Proof. exact (MK_COMB (@lem8239688 A B P p t lt2 s) (@lem8240012 A B P lt2 s p t)). Qed.
Lemma lem8240016 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term134 A B P lt2 p s) = (term135 A B P lt2 s p).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8240013 A B P lt2 s p t)). Qed.
Lemma lem8240017 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8240018 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term136 A B P lt2 p s) = (term137 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8240017 A B P) (@lem8240016 A B P lt2 s p)). Qed.
Lemma lem8240023 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term138 A B P lt2 p) = (term139 A B P lt2 p).
Proof. exact (fun_ext (fun s : P -> A => @lem8240018 A B P lt2 s p)). Qed.
Lemma lem8240024 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8240025 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : (term140 A B P lt2 p) = (term141 A B P lt2 p).
Proof. exact (MK_COMB (@lem8240024 A P) (@lem8240023 A B P lt2 p)). Qed.
Lemma lem8240030 {A B P : Type'} (lt2 : type1402 A) : (term142 A B P lt2) = (term143 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8240025 A B P lt2 p)). Qed.
Lemma lem8240031 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8240032 {A B P : Type'} (lt2 : type1402 A) : (term144 A B P lt2) = (term145 A B P lt2).
Proof. exact (MK_COMB (@lem8240031 A B P) (@lem8240030 A B P lt2)). Qed.
Lemma lem8240037 {A B P : Type'} : (term146 A B P) = (term147 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8240032 A B P lt2)). Qed.
Lemma lem8240038 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8240039 {A B P : Type'} : (term148 A B P) = (term149 A B P).
Proof. exact (MK_COMB (@lem8240038 A) (@lem8240037 A B P)). Qed.
Lemma lem8240044 {A B P : Type'} : (term149 A B P) = (term148 A B P).
Proof. exact (SYM (@lem8240039 A B P)). Qed.
Lemma lem8240045 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term36 A B P p t lt2 s) : term36 A B P p t lt2 s.
Proof. exact (h1). Qed.
Lemma lem8240046 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term34 A B P p t lt2 s.
Proof. exact (h1). Qed.
Lemma lem8240047 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term31 A B P p lt2 s t) : term31 A B P p lt2 s t.
Proof. exact (h1). Qed.
Lemma lem8240048 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term80 A B P lt2 s p) : term80 A B P lt2 s p.
Proof. exact (h1). Qed.
Lemma lem8240098 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240099 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8240098 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8240100 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (@lem8240099 A B P (term45 A B P) f). Qed.
Lemma lem8240101 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240102 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8240101 A B P f)). Qed.
Lemma lem8240103 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240104 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (MK_COMB (@lem8240102 A B P) (@lem8240103 A B f)). Qed.
Lemma lem8240105 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8240106 {A B P : Type'} (f : A -> B) : (term52 A B P f) = (term53 A B P f).
Proof. exact (MK_COMB (@lem8240105 P) (@lem8240104 A B P f)). Qed.
Lemma lem8240107 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240108 {A B P : Type'} (f : A -> B) : ((term48 A B P f) = (term49 A B P f)) = ((term49 A B P f) = (term50 P)).
Proof. exact (MK_COMB (@lem8240106 A B P f) (@lem8240107 A B P f)). Qed.
Lemma lem8240109 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (EQ_MP (@lem8240108 A B P f) (@lem8240100 A B P f)). Qed.
Lemma lem8240110 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240111 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240109 A B P f) (@lem8240110 P a)). Qed.
Lemma lem8240113 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240114 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8240113 P Prop f y). Qed.
Lemma lem8240115 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8240114 P (term50 P) a). Qed.
Lemma lem8240116 {P : Type'} (x : P) : (term55 P x) = True.
Proof. exact (eq_refl (term55 P x)). Qed.
Lemma lem8240117 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun x : P => @lem8240116 P x)). Qed.
Lemma lem8240118 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240119 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240117 P) (@lem8240118 P a)). Qed.
Lemma lem8240120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8240121 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8240120) (@lem8240119 P a)). Qed.
Lemma lem8240122 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8240123 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8240121 P a) (@lem8240122 P a)). Qed.
Lemma lem8240124 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8240123 P a) (@lem8240115 P a)). Qed.
Lemma lem8240125 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = True.
Proof. exact (TRANS (@lem8240111 A B P f a) (@lem8240124 P a)). Qed.
Lemma lem8240126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240127 {A B P : Type'} (f : A -> B) (a : P) : (term61 A B P f a) = (and True).
Proof. exact (MK_COMB (@lem8240126) (@lem8240125 A B P f a)). Qed.
Lemma lem8240129 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240130 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term150 A B P f y) = (f y).
Proof. exact (@lem8240129 (A -> B) (P -> A) f y). Qed.
Lemma lem8240131 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (@lem8240130 A B P (term153 A B P p t s) f). Qed.
Lemma lem8240132 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240133 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term155 A B P p t s) = (term153 A B P p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240132 A B P p t f s)). Qed.
Lemma lem8240134 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240135 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (MK_COMB (@lem8240133 A B P p t s) (@lem8240134 A B f)). Qed.
Lemma lem8240136 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8240137 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term156 A B P p t s f) = (term157 A B P p t s f).
Proof. exact (MK_COMB (@lem8240136 A P) (@lem8240135 A B P p t s f)). Qed.
Lemma lem8240138 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240139 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term151 A B P p t s f) = (term152 A B P p t s f)) = ((term152 A B P p t s f) = (term154 A B P p t f s)).
Proof. exact (MK_COMB (@lem8240137 A B P p t s f) (@lem8240138 A B P p t f s)). Qed.
Lemma lem8240140 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (EQ_MP (@lem8240139 A B P p t f s) (@lem8240131 A B P p t s f)). Qed.
Lemma lem8240141 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240142 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240140 A B P p t f s) (@lem8240141 P a)). Qed.
Lemma lem8240144 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240145 {A P : Type'} (f : P -> A) (y : P) : (term94 A P f y) = (f y).
Proof. exact (@lem8240144 P A f y). Qed.
Lemma lem8240146 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (@lem8240145 A P (term154 A B P p t f s) a). Qed.
Lemma lem8240147 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240148 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term162 A B P p t f s) = (term154 A B P p t f s).
Proof. exact (fun_ext (fun a : P => @lem8240147 A B P p t f s a)). Qed.
Lemma lem8240149 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240150 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240148 A B P p t f s) (@lem8240149 P a)). Qed.
Lemma lem8240151 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240152 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term163 A B P p t f s a) = (term164 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240151 A) (@lem8240150 A B P p t f s a)). Qed.
Lemma lem8240153 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240154 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term160 A B P p t f s a) = (term159 A B P p t f s a)) = ((term159 A B P p t f s a) = (term161 A B P p t f s a)).
Proof. exact (MK_COMB (@lem8240152 A B P p t f s a) (@lem8240153 A B P p t f s a)). Qed.
Lemma lem8240155 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (EQ_MP (@lem8240154 A B P p t f s a) (@lem8240146 A B P p t f s a)). Qed.
Lemma lem8240156 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term161 A B P p t f s a).
Proof. exact (TRANS (@lem8240142 A B P p t f s a) (@lem8240155 A B P p t f s a)). Qed.
Lemma lem8240157 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8240158 {A B P : Type'} (lt2 : type1402 A) (y : A) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term165 A B P lt2 y p t s f a) = (term166 A B P lt2 y p t f s a).
Proof. exact (MK_COMB (@lem8240157 A lt2 y) (@lem8240156 A B P p t f s a)). Qed.
Lemma lem8240159 {A B P : Type'} (lt2 : type1402 A) (y : A) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term167 A B P lt2 y p t s f a) = (term168 A B P lt2 y p t f s a).
Proof. exact (MK_COMB (@lem8240127 A B P f a) (@lem8240158 A B P lt2 y p t f s a)). Qed.
Lemma lem8240161 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8240162 {A B P : Type'} (lt2 : type1402 A) (y : A) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term168 A B P lt2 y p t f s a) = (term166 A B P lt2 y p t f s a).
Proof. exact (@lem8240161 (term166 A B P lt2 y p t f s a)). Qed.
Lemma lem8240163 {A B P : Type'} (lt2 : type1402 A) (y : A) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term167 A B P lt2 y p t s f a) = (term166 A B P lt2 y p t f s a).
Proof. exact (TRANS (@lem8240159 A B P lt2 y p t f s a) (@lem8240162 A B P lt2 y p t f s a)). Qed.
Lemma lem8240164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8240165 {A B P : Type'} (lt2 : type1402 A) (y : A) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term169 A B P lt2 y p t s f a) = (term170 A B P lt2 y p t f s a).
Proof. exact (MK_COMB (@lem8240164) (@lem8240163 A B P lt2 y p t f s a)). Qed.
Lemma lem8240166 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term171 A P lt2 y s a).
Proof. exact (eq_refl (term171 A P lt2 y s a)). Qed.
Lemma lem8240167 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term172 A B P p t f lt2 y s a) = (term173 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8240165 A B P lt2 y p t f s a) (@lem8240166 A P lt2 y s a)). Qed.
Lemma lem8240170 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term174 A B P p t f lt2 s a) = (term175 A B P p t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8240167 A B P p t f lt2 y s a)). Qed.
Lemma lem8240171 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8240172 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term176 A B P p t f lt2 s a) = (term177 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8240171 A) (@lem8240170 A B P p t f lt2 s a)). Qed.
Lemma lem8240177 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term178 A B P p t f lt2 s) = (term179 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8240172 A B P p t f lt2 s a)). Qed.
Lemma lem8240178 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8240179 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term180 A B P p t f lt2 s) = (term181 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8240178 P) (@lem8240177 A B P p t f lt2 s)). Qed.
Lemma lem8240184 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term182 A B P p t lt2 s) = (term183 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240179 A B P p t f lt2 s)). Qed.
Lemma lem8240185 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8240186 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term184 A B P p t lt2 s) = (term185 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8240185 A B) (@lem8240184 A B P p t lt2 s)). Qed.
Lemma lem8240191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240192 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term186 A B P p t lt2 s) = (term187 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8240191) (@lem8240186 A B P p t lt2 s)). Qed.
Lemma lem8240222 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240223 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8240222 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8240224 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (@lem8240223 A B P (term45 A B P) f). Qed.
Lemma lem8240225 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240226 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8240225 A B P f)). Qed.
Lemma lem8240227 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240228 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (MK_COMB (@lem8240226 A B P) (@lem8240227 A B f)). Qed.
Lemma lem8240229 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8240230 {A B P : Type'} (f : A -> B) : (term52 A B P f) = (term53 A B P f).
Proof. exact (MK_COMB (@lem8240229 P) (@lem8240228 A B P f)). Qed.
Lemma lem8240231 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240232 {A B P : Type'} (f : A -> B) : ((term48 A B P f) = (term49 A B P f)) = ((term49 A B P f) = (term50 P)).
Proof. exact (MK_COMB (@lem8240230 A B P f) (@lem8240231 A B P f)). Qed.
Lemma lem8240233 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (EQ_MP (@lem8240232 A B P f) (@lem8240224 A B P f)). Qed.
Lemma lem8240234 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240235 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240233 A B P f) (@lem8240234 P a)). Qed.
Lemma lem8240237 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240238 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8240237 P Prop f y). Qed.
Lemma lem8240239 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8240238 P (term50 P) a). Qed.
Lemma lem8240240 {P : Type'} (x : P) : (term55 P x) = True.
Proof. exact (eq_refl (term55 P x)). Qed.
Lemma lem8240241 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun x : P => @lem8240240 P x)). Qed.
Lemma lem8240242 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240243 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240241 P) (@lem8240242 P a)). Qed.
Lemma lem8240244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8240245 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8240244) (@lem8240243 P a)). Qed.
Lemma lem8240246 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8240247 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8240245 P a) (@lem8240246 P a)). Qed.
Lemma lem8240248 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8240247 P a) (@lem8240239 P a)). Qed.
Lemma lem8240249 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = True.
Proof. exact (TRANS (@lem8240235 A B P f a) (@lem8240248 P a)). Qed.
Lemma lem8240250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8240251 {A B P : Type'} (f : A -> B) (a : P) : (term188 A B P f a) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8240250) (@lem8240249 A B P f a)). Qed.
Lemma lem8240253 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240254 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8240253 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8240255 {A B P : Type'} (g : A -> B) : (term48 A B P g) = (term49 A B P g).
Proof. exact (@lem8240254 A B P (term45 A B P) g). Qed.
Lemma lem8240256 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240257 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8240256 A B P f)). Qed.
Lemma lem8240258 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8240259 {A B P : Type'} (g : A -> B) : (term48 A B P g) = (term49 A B P g).
Proof. exact (MK_COMB (@lem8240257 A B P) (@lem8240258 A B g)). Qed.
Lemma lem8240260 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8240261 {A B P : Type'} (g : A -> B) : (term52 A B P g) = (term53 A B P g).
Proof. exact (MK_COMB (@lem8240260 P) (@lem8240259 A B P g)). Qed.
Lemma lem8240262 {A B P : Type'} (g : A -> B) : (term49 A B P g) = (term50 P).
Proof. exact (eq_refl (term49 A B P g)). Qed.
Lemma lem8240263 {A B P : Type'} (g : A -> B) : ((term48 A B P g) = (term49 A B P g)) = ((term49 A B P g) = (term50 P)).
Proof. exact (MK_COMB (@lem8240261 A B P g) (@lem8240262 A B P g)). Qed.
Lemma lem8240264 {A B P : Type'} (g : A -> B) : (term49 A B P g) = (term50 P).
Proof. exact (EQ_MP (@lem8240263 A B P g) (@lem8240255 A B P g)). Qed.
Lemma lem8240265 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240266 {A B P : Type'} (g : A -> B) (a : P) : (term54 A B P g a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240264 A B P g) (@lem8240265 P a)). Qed.
Lemma lem8240268 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240269 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8240268 P Prop f y). Qed.
Lemma lem8240270 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8240269 P (term50 P) a). Qed.
Lemma lem8240271 {P : Type'} (x : P) : (term55 P x) = True.
Proof. exact (eq_refl (term55 P x)). Qed.
Lemma lem8240272 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun x : P => @lem8240271 P x)). Qed.
Lemma lem8240273 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240274 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240272 P) (@lem8240273 P a)). Qed.
Lemma lem8240275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8240276 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8240275) (@lem8240274 P a)). Qed.
Lemma lem8240277 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8240278 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8240276 P a) (@lem8240277 P a)). Qed.
Lemma lem8240279 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8240278 P a) (@lem8240270 P a)). Qed.
Lemma lem8240280 {A B P : Type'} (g : A -> B) (a : P) : (term54 A B P g a) = True.
Proof. exact (TRANS (@lem8240266 A B P g a) (@lem8240279 P a)). Qed.
Lemma lem8240281 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : ((term54 A B P f a) = (term54 A B P g a)) = (True = True).
Proof. exact (MK_COMB (@lem8240251 A B P f a) (@lem8240280 A B P g a)). Qed.
Lemma lem8240283 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8240284 : (True = True) = True.
Proof. exact (@lem8240283 True). Qed.
Lemma lem8240285 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : ((term54 A B P f a) = (term54 A B P g a)) = True.
Proof. exact (TRANS (@lem8240281 A B P f g a) (@lem8240284)). Qed.
Lemma lem8240286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240287 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) : (term189 A B P f g a) = (and True).
Proof. exact (MK_COMB (@lem8240286) (@lem8240285 A B P f g a)). Qed.
Lemma lem8240293 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240294 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term150 A B P f y) = (f y).
Proof. exact (@lem8240293 (A -> B) (P -> A) f y). Qed.
Lemma lem8240295 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (@lem8240294 A B P (term153 A B P p t s) f). Qed.
Lemma lem8240296 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240297 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term155 A B P p t s) = (term153 A B P p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240296 A B P p t f s)). Qed.
Lemma lem8240298 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240299 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (MK_COMB (@lem8240297 A B P p t s) (@lem8240298 A B f)). Qed.
Lemma lem8240300 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8240301 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term156 A B P p t s f) = (term157 A B P p t s f).
Proof. exact (MK_COMB (@lem8240300 A P) (@lem8240299 A B P p t s f)). Qed.
Lemma lem8240302 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240303 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term151 A B P p t s f) = (term152 A B P p t s f)) = ((term152 A B P p t s f) = (term154 A B P p t f s)).
Proof. exact (MK_COMB (@lem8240301 A B P p t s f) (@lem8240302 A B P p t f s)). Qed.
Lemma lem8240304 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (EQ_MP (@lem8240303 A B P p t f s) (@lem8240295 A B P p t s f)). Qed.
Lemma lem8240305 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240306 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240304 A B P p t f s) (@lem8240305 P a)). Qed.
Lemma lem8240308 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240309 {A P : Type'} (f : P -> A) (y : P) : (term94 A P f y) = (f y).
Proof. exact (@lem8240308 P A f y). Qed.
Lemma lem8240310 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (@lem8240309 A P (term154 A B P p t f s) a). Qed.
Lemma lem8240311 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240312 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term162 A B P p t f s) = (term154 A B P p t f s).
Proof. exact (fun_ext (fun a : P => @lem8240311 A B P p t f s a)). Qed.
Lemma lem8240313 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240314 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240312 A B P p t f s) (@lem8240313 P a)). Qed.
Lemma lem8240315 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240316 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term163 A B P p t f s a) = (term164 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240315 A) (@lem8240314 A B P p t f s a)). Qed.
Lemma lem8240317 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240318 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term160 A B P p t f s a) = (term159 A B P p t f s a)) = ((term159 A B P p t f s a) = (term161 A B P p t f s a)).
Proof. exact (MK_COMB (@lem8240316 A B P p t f s a) (@lem8240317 A B P p t f s a)). Qed.
Lemma lem8240319 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (EQ_MP (@lem8240318 A B P p t f s a) (@lem8240310 A B P p t f s a)). Qed.
Lemma lem8240320 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term161 A B P p t f s a).
Proof. exact (TRANS (@lem8240306 A B P p t f s a) (@lem8240319 A B P p t f s a)). Qed.
Lemma lem8240321 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240322 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term190 A B P p t s f a) = (term191 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240321 A) (@lem8240320 A B P p t f s a)). Qed.
Lemma lem8240324 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240325 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term150 A B P f y) = (f y).
Proof. exact (@lem8240324 (A -> B) (P -> A) f y). Qed.
Lemma lem8240326 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (g : A -> B) : (term151 A B P p t s g) = (term152 A B P p t s g).
Proof. exact (@lem8240325 A B P (term153 A B P p t s) g). Qed.
Lemma lem8240327 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240328 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term155 A B P p t s) = (term153 A B P p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240327 A B P p t f s)). Qed.
Lemma lem8240329 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8240330 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (g : A -> B) : (term151 A B P p t s g) = (term152 A B P p t s g).
Proof. exact (MK_COMB (@lem8240328 A B P p t s) (@lem8240329 A B g)). Qed.
Lemma lem8240331 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8240332 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (g : A -> B) : (term156 A B P p t s g) = (term157 A B P p t s g).
Proof. exact (MK_COMB (@lem8240331 A P) (@lem8240330 A B P p t s g)). Qed.
Lemma lem8240333 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : (term152 A B P p t s g) = (term154 A B P p t g s).
Proof. exact (eq_refl (term152 A B P p t s g)). Qed.
Lemma lem8240334 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : ((term151 A B P p t s g) = (term152 A B P p t s g)) = ((term152 A B P p t s g) = (term154 A B P p t g s)).
Proof. exact (MK_COMB (@lem8240332 A B P p t s g) (@lem8240333 A B P p t g s)). Qed.
Lemma lem8240335 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : (term152 A B P p t s g) = (term154 A B P p t g s).
Proof. exact (EQ_MP (@lem8240334 A B P p t g s) (@lem8240326 A B P p t s g)). Qed.
Lemma lem8240336 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240337 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s g a) = (term159 A B P p t g s a).
Proof. exact (MK_COMB (@lem8240335 A B P p t g s) (@lem8240336 P a)). Qed.
Lemma lem8240339 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240340 {A P : Type'} (f : P -> A) (y : P) : (term94 A P f y) = (f y).
Proof. exact (@lem8240339 P A f y). Qed.
Lemma lem8240341 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term160 A B P p t g s a) = (term159 A B P p t g s a).
Proof. exact (@lem8240340 A P (term154 A B P p t g s) a). Qed.
Lemma lem8240342 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term159 A B P p t g s a) = (term161 A B P p t g s a).
Proof. exact (eq_refl (term159 A B P p t g s a)). Qed.
Lemma lem8240343 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : (term162 A B P p t g s) = (term154 A B P p t g s).
Proof. exact (fun_ext (fun a : P => @lem8240342 A B P p t g s a)). Qed.
Lemma lem8240344 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240345 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term160 A B P p t g s a) = (term159 A B P p t g s a).
Proof. exact (MK_COMB (@lem8240343 A B P p t g s) (@lem8240344 P a)). Qed.
Lemma lem8240346 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240347 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term163 A B P p t g s a) = (term164 A B P p t g s a).
Proof. exact (MK_COMB (@lem8240346 A) (@lem8240345 A B P p t g s a)). Qed.
Lemma lem8240348 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term159 A B P p t g s a) = (term161 A B P p t g s a).
Proof. exact (eq_refl (term159 A B P p t g s a)). Qed.
Lemma lem8240349 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : ((term160 A B P p t g s a) = (term159 A B P p t g s a)) = ((term159 A B P p t g s a) = (term161 A B P p t g s a)).
Proof. exact (MK_COMB (@lem8240347 A B P p t g s a) (@lem8240348 A B P p t g s a)). Qed.
Lemma lem8240350 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term159 A B P p t g s a) = (term161 A B P p t g s a).
Proof. exact (EQ_MP (@lem8240349 A B P p t g s a) (@lem8240341 A B P p t g s a)). Qed.
Lemma lem8240351 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s g a) = (term161 A B P p t g s a).
Proof. exact (TRANS (@lem8240337 A B P p t g s a) (@lem8240350 A B P p t g s a)). Qed.
Lemma lem8240352 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : ((term158 A B P p t s f a) = (term158 A B P p t s g a)) = ((term161 A B P p t f s a) = (term161 A B P p t g s a)).
Proof. exact (MK_COMB (@lem8240322 A B P p t f s a) (@lem8240351 A B P p t g s a)). Qed.
Lemma lem8240355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240356 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term192 A B P f p t s g a) = (term193 A B P f p t g s a).
Proof. exact (MK_COMB (@lem8240355) (@lem8240352 A B P f p t g s a)). Qed.
Lemma lem8240360 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240361 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term85 A B P f y) = (f y).
Proof. exact (@lem8240360 (A -> B) (P -> B) f y). Qed.
Lemma lem8240362 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term194 A B P anything f) = (term195 A B P anything f).
Proof. exact (@lem8240361 A B P (term196 A B P anything) f). Qed.
Lemma lem8240363 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (eq_refl (term195 A B P anything f)). Qed.
Lemma lem8240364 {A B P : Type'} (anything : P -> B) : (term197 A B P anything) = (term196 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8240363 A B P f anything)). Qed.
Lemma lem8240365 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240366 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term194 A B P anything f) = (term195 A B P anything f).
Proof. exact (MK_COMB (@lem8240364 A B P anything) (@lem8240365 A B f)). Qed.
Lemma lem8240367 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8240368 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term198 A B P anything f) = (term199 A B P anything f).
Proof. exact (MK_COMB (@lem8240367 B P) (@lem8240366 A B P anything f)). Qed.
Lemma lem8240369 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (eq_refl (term195 A B P anything f)). Qed.
Lemma lem8240370 {A B P : Type'} (f : A -> B) (anything : P -> B) : ((term194 A B P anything f) = (term195 A B P anything f)) = ((term195 A B P anything f) = anything).
Proof. exact (MK_COMB (@lem8240368 A B P anything f) (@lem8240369 A B P f anything)). Qed.
Lemma lem8240371 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (EQ_MP (@lem8240370 A B P f anything) (@lem8240362 A B P anything f)). Qed.
Lemma lem8240372 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240373 {A B P : Type'} (f : A -> B) (anything : P -> B) (a : P) : (term200 A B P anything f a) = (anything a).
Proof. exact (MK_COMB (@lem8240371 A B P f anything) (@lem8240372 P a)). Qed.
Lemma lem8240374 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8240375 {A B P : Type'} (f : A -> B) (anything : P -> B) (a : P) : (term201 A B P anything f a) = (term202 B P anything a).
Proof. exact (MK_COMB (@lem8240374 B) (@lem8240373 A B P f anything a)). Qed.
Lemma lem8240377 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240378 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term85 A B P f y) = (f y).
Proof. exact (@lem8240377 (A -> B) (P -> B) f y). Qed.
Lemma lem8240379 {A B P : Type'} (anything : P -> B) (g : A -> B) : (term194 A B P anything g) = (term195 A B P anything g).
Proof. exact (@lem8240378 A B P (term196 A B P anything) g). Qed.
Lemma lem8240380 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (eq_refl (term195 A B P anything f)). Qed.
Lemma lem8240381 {A B P : Type'} (anything : P -> B) : (term197 A B P anything) = (term196 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8240380 A B P f anything)). Qed.
Lemma lem8240382 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8240383 {A B P : Type'} (anything : P -> B) (g : A -> B) : (term194 A B P anything g) = (term195 A B P anything g).
Proof. exact (MK_COMB (@lem8240381 A B P anything) (@lem8240382 A B g)). Qed.
Lemma lem8240384 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8240385 {A B P : Type'} (anything : P -> B) (g : A -> B) : (term198 A B P anything g) = (term199 A B P anything g).
Proof. exact (MK_COMB (@lem8240384 B P) (@lem8240383 A B P anything g)). Qed.
Lemma lem8240386 {A B P : Type'} (g : A -> B) (anything : P -> B) : (term195 A B P anything g) = anything.
Proof. exact (eq_refl (term195 A B P anything g)). Qed.
Lemma lem8240387 {A B P : Type'} (g : A -> B) (anything : P -> B) : ((term194 A B P anything g) = (term195 A B P anything g)) = ((term195 A B P anything g) = anything).
Proof. exact (MK_COMB (@lem8240385 A B P anything g) (@lem8240386 A B P g anything)). Qed.
Lemma lem8240388 {A B P : Type'} (g : A -> B) (anything : P -> B) : (term195 A B P anything g) = anything.
Proof. exact (EQ_MP (@lem8240387 A B P g anything) (@lem8240379 A B P anything g)). Qed.
Lemma lem8240389 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240390 {A B P : Type'} (g : A -> B) (anything : P -> B) (a : P) : (term200 A B P anything g a) = (anything a).
Proof. exact (MK_COMB (@lem8240388 A B P g anything) (@lem8240389 P a)). Qed.
Lemma lem8240391 {A B P : Type'} (f : A -> B) (g : A -> B) (anything : P -> B) (a : P) : ((term200 A B P anything f a) = (term200 A B P anything g a)) = ((anything a) = (anything a)).
Proof. exact (MK_COMB (@lem8240375 A B P f anything a) (@lem8240390 A B P g anything a)). Qed.
Lemma lem8240393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8240394 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem8240393 B x). Qed.
Lemma lem8240395 {B P : Type'} (anything : P -> B) (a : P) : ((anything a) = (anything a)) = True.
Proof. exact (@lem8240394 B (anything a)). Qed.
Lemma lem8240396 {A B P : Type'} (f : A -> B) (anything : P -> B) (g : A -> B) (a : P) : ((term200 A B P anything f a) = (term200 A B P anything g a)) = True.
Proof. exact (TRANS (@lem8240391 A B P f g anything a) (@lem8240395 B P anything a)). Qed.
Lemma lem8240397 {A B P : Type'} (anything : P -> B) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term203 A B P p t s f anything g a) = (term204 A B P f p t g s a).
Proof. exact (MK_COMB (@lem8240356 A B P f p t g s a) (@lem8240396 A B P f anything g a)). Qed.
Lemma lem8240399 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8240400 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term204 A B P f p t g s a) = ((term161 A B P p t f s a) = (term161 A B P p t g s a)).
Proof. exact (@lem8240399 ((term161 A B P p t f s a) = (term161 A B P p t g s a))). Qed.
Lemma lem8240403 {A B P : Type'} (anything : P -> B) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term203 A B P p t s f anything g a) = ((term161 A B P p t f s a) = (term161 A B P p t g s a)).
Proof. exact (TRANS (@lem8240397 A B P anything f p t g s a) (@lem8240400 A B P f p t g s a)). Qed.
Lemma lem8240404 {A B P : Type'} (anything : P -> B) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term205 A B P p t s f anything g a) = (term206 A B P f p t g s a).
Proof. exact (MK_COMB (@lem8240287 A B P f g a) (@lem8240403 A B P anything f p t g s a)). Qed.
Lemma lem8240406 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8240407 {A B P : Type'} (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term206 A B P f p t g s a) = ((term161 A B P p t f s a) = (term161 A B P p t g s a)).
Proof. exact (@lem8240406 ((term161 A B P p t f s a) = (term161 A B P p t g s a))). Qed.
Lemma lem8240410 {A B P : Type'} (anything : P -> B) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term205 A B P p t s f anything g a) = ((term161 A B P p t f s a) = (term161 A B P p t g s a)).
Proof. exact (TRANS (@lem8240404 A B P anything f p t g s a) (@lem8240407 A B P f p t g s a)). Qed.
Lemma lem8240411 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8240412 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term207 A B P lt2 p t s f anything g a) = (term208 A B P lt2 f p t g s a).
Proof. exact (MK_COMB (@lem8240411 A B P lt2 s a f g) (@lem8240410 A B P anything f p t g s a)). Qed.
Lemma lem8240415 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : (term209 A B P lt2 p t s f anything g) = (term210 A B P lt2 f p t g s).
Proof. exact (fun_ext (fun a : P => @lem8240412 A B P anything lt2 f p t g s a)). Qed.
Lemma lem8240416 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8240417 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) : (term211 A B P lt2 p t s f anything g) = (term212 A B P lt2 f p t g s).
Proof. exact (MK_COMB (@lem8240416 P) (@lem8240415 A B P anything lt2 f p t g s)). Qed.
Lemma lem8240422 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term213 A B P lt2 p t s f anything) = (term214 A B P lt2 f p t s).
Proof. exact (fun_ext (fun g : A -> B => @lem8240417 A B P anything lt2 f p t g s)). Qed.
Lemma lem8240423 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8240424 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term215 A B P lt2 p t s f anything) = (term216 A B P lt2 f p t s).
Proof. exact (MK_COMB (@lem8240423 A B) (@lem8240422 A B P anything lt2 f p t s)). Qed.
Lemma lem8240429 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term217 A B P lt2 p t s anything) = (term218 A B P lt2 p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240424 A B P anything lt2 f p t s)). Qed.
Lemma lem8240430 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8240431 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term219 A B P lt2 p t s anything) = (term220 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240430 A B) (@lem8240429 A B P anything lt2 p t s)). Qed.
Lemma lem8240436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240437 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term221 A B P lt2 p t s anything) = (term222 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240436) (@lem8240431 A B P anything lt2 p t s)). Qed.
Lemma lem8240451 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240452 {A B P : Type'} (f : type560 A B P) (y : A -> B) : (term47 A B P f y) = (f y).
Proof. exact (@lem8240451 (A -> B) (P -> Prop) f y). Qed.
Lemma lem8240453 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (@lem8240452 A B P (term45 A B P) f). Qed.
Lemma lem8240454 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240455 {A B P : Type'} : (term51 A B P) = (term45 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8240454 A B P f)). Qed.
Lemma lem8240456 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240457 {A B P : Type'} (f : A -> B) : (term48 A B P f) = (term49 A B P f).
Proof. exact (MK_COMB (@lem8240455 A B P) (@lem8240456 A B f)). Qed.
Lemma lem8240458 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8240459 {A B P : Type'} (f : A -> B) : (term52 A B P f) = (term53 A B P f).
Proof. exact (MK_COMB (@lem8240458 P) (@lem8240457 A B P f)). Qed.
Lemma lem8240460 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (eq_refl (term49 A B P f)). Qed.
Lemma lem8240461 {A B P : Type'} (f : A -> B) : ((term48 A B P f) = (term49 A B P f)) = ((term49 A B P f) = (term50 P)).
Proof. exact (MK_COMB (@lem8240459 A B P f) (@lem8240460 A B P f)). Qed.
Lemma lem8240462 {A B P : Type'} (f : A -> B) : (term49 A B P f) = (term50 P).
Proof. exact (EQ_MP (@lem8240461 A B P f) (@lem8240453 A B P f)). Qed.
Lemma lem8240463 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240464 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240462 A B P f) (@lem8240463 P a)). Qed.
Lemma lem8240466 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240467 {P : Type'} (f : P -> Prop) (y : P) : (term56 P f y) = (f y).
Proof. exact (@lem8240466 P Prop f y). Qed.
Lemma lem8240468 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (@lem8240467 P (term50 P) a). Qed.
Lemma lem8240469 {P : Type'} (x : P) : (term55 P x) = True.
Proof. exact (eq_refl (term55 P x)). Qed.
Lemma lem8240470 {P : Type'} : (term58 P) = (term50 P).
Proof. exact (fun_ext (fun x : P => @lem8240469 P x)). Qed.
Lemma lem8240471 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240472 {P : Type'} (a : P) : (term57 P a) = (term55 P a).
Proof. exact (MK_COMB (@lem8240470 P) (@lem8240471 P a)). Qed.
Lemma lem8240473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8240474 {P : Type'} (a : P) : (term59 P a) = (term60 P a).
Proof. exact (MK_COMB (@lem8240473) (@lem8240472 P a)). Qed.
Lemma lem8240475 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (eq_refl (term55 P a)). Qed.
Lemma lem8240476 {P : Type'} (a : P) : ((term57 P a) = (term55 P a)) = ((term55 P a) = True).
Proof. exact (MK_COMB (@lem8240474 P a) (@lem8240475 P a)). Qed.
Lemma lem8240477 {P : Type'} (a : P) : (term55 P a) = True.
Proof. exact (EQ_MP (@lem8240476 P a) (@lem8240468 P a)). Qed.
Lemma lem8240478 {A B P : Type'} (f : A -> B) (a : P) : (term54 A B P f a) = True.
Proof. exact (TRANS (@lem8240464 A B P f a) (@lem8240477 P a)). Qed.
Lemma lem8240479 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem8240480 {A B P : Type'} (f : A -> B) (a : P) : (term223 A B P f a) = (@COND B True).
Proof. exact (MK_COMB (@lem8240479 B) (@lem8240478 A B P f a)). Qed.
Lemma lem8240482 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240483 {A B P : Type'} (f : type557 A B P) (y : A -> B) : (term150 A B P f y) = (f y).
Proof. exact (@lem8240482 (A -> B) (P -> A) f y). Qed.
Lemma lem8240484 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (@lem8240483 A B P (term153 A B P p t s) f). Qed.
Lemma lem8240485 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240486 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term155 A B P p t s) = (term153 A B P p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240485 A B P p t f s)). Qed.
Lemma lem8240487 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240488 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term151 A B P p t s f) = (term152 A B P p t s f).
Proof. exact (MK_COMB (@lem8240486 A B P p t s) (@lem8240487 A B f)). Qed.
Lemma lem8240489 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8240490 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (f : A -> B) : (term156 A B P p t s f) = (term157 A B P p t s f).
Proof. exact (MK_COMB (@lem8240489 A P) (@lem8240488 A B P p t s f)). Qed.
Lemma lem8240491 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (eq_refl (term152 A B P p t s f)). Qed.
Lemma lem8240492 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term151 A B P p t s f) = (term152 A B P p t s f)) = ((term152 A B P p t s f) = (term154 A B P p t f s)).
Proof. exact (MK_COMB (@lem8240490 A B P p t s f) (@lem8240491 A B P p t f s)). Qed.
Lemma lem8240493 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term152 A B P p t s f) = (term154 A B P p t f s).
Proof. exact (EQ_MP (@lem8240492 A B P p t f s) (@lem8240484 A B P p t s f)). Qed.
Lemma lem8240494 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240495 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240493 A B P p t f s) (@lem8240494 P a)). Qed.
Lemma lem8240497 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240498 {A P : Type'} (f : P -> A) (y : P) : (term94 A P f y) = (f y).
Proof. exact (@lem8240497 P A f y). Qed.
Lemma lem8240499 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (@lem8240498 A P (term154 A B P p t f s) a). Qed.
Lemma lem8240500 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240501 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term162 A B P p t f s) = (term154 A B P p t f s).
Proof. exact (fun_ext (fun a : P => @lem8240500 A B P p t f s a)). Qed.
Lemma lem8240502 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240503 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term160 A B P p t f s a) = (term159 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240501 A B P p t f s) (@lem8240502 P a)). Qed.
Lemma lem8240504 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240505 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term163 A B P p t f s a) = (term164 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240504 A) (@lem8240503 A B P p t f s a)). Qed.
Lemma lem8240506 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (eq_refl (term159 A B P p t f s a)). Qed.
Lemma lem8240507 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term160 A B P p t f s a) = (term159 A B P p t f s a)) = ((term159 A B P p t f s a) = (term161 A B P p t f s a)).
Proof. exact (MK_COMB (@lem8240505 A B P p t f s a) (@lem8240506 A B P p t f s a)). Qed.
Lemma lem8240508 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term159 A B P p t f s a) = (term161 A B P p t f s a).
Proof. exact (EQ_MP (@lem8240507 A B P p t f s a) (@lem8240499 A B P p t f s a)). Qed.
Lemma lem8240509 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term158 A B P p t s f a) = (term161 A B P p t f s a).
Proof. exact (TRANS (@lem8240495 A B P p t f s a) (@lem8240508 A B P p t f s a)). Qed.
Lemma lem8240510 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240511 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term224 A B P p t s f a) = (term225 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240510 A B f) (@lem8240509 A B P p t f s a)). Qed.
Lemma lem8240512 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term226 A B P p t s f a) = (term227 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240480 A B P f a) (@lem8240511 A B P p t f s a)). Qed.
Lemma lem8240514 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8240515 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term85 A B P f y) = (f y).
Proof. exact (@lem8240514 (A -> B) (P -> B) f y). Qed.
Lemma lem8240516 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term194 A B P anything f) = (term195 A B P anything f).
Proof. exact (@lem8240515 A B P (term196 A B P anything) f). Qed.
Lemma lem8240517 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (eq_refl (term195 A B P anything f)). Qed.
Lemma lem8240518 {A B P : Type'} (anything : P -> B) : (term197 A B P anything) = (term196 A B P anything).
Proof. exact (fun_ext (fun f : A -> B => @lem8240517 A B P f anything)). Qed.
Lemma lem8240519 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240520 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term194 A B P anything f) = (term195 A B P anything f).
Proof. exact (MK_COMB (@lem8240518 A B P anything) (@lem8240519 A B f)). Qed.
Lemma lem8240521 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8240522 {A B P : Type'} (anything : P -> B) (f : A -> B) : (term198 A B P anything f) = (term199 A B P anything f).
Proof. exact (MK_COMB (@lem8240521 B P) (@lem8240520 A B P anything f)). Qed.
Lemma lem8240523 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (eq_refl (term195 A B P anything f)). Qed.
Lemma lem8240524 {A B P : Type'} (f : A -> B) (anything : P -> B) : ((term194 A B P anything f) = (term195 A B P anything f)) = ((term195 A B P anything f) = anything).
Proof. exact (MK_COMB (@lem8240522 A B P anything f) (@lem8240523 A B P f anything)). Qed.
Lemma lem8240525 {A B P : Type'} (f : A -> B) (anything : P -> B) : (term195 A B P anything f) = anything.
Proof. exact (EQ_MP (@lem8240524 A B P f anything) (@lem8240516 A B P anything f)). Qed.
Lemma lem8240526 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8240527 {A B P : Type'} (f : A -> B) (anything : P -> B) (a : P) : (term200 A B P anything f a) = (anything a).
Proof. exact (MK_COMB (@lem8240525 A B P f anything) (@lem8240526 P a)). Qed.
Lemma lem8240528 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (anything : P -> B) (a : P) : (term228 A B P p t s anything f a) = (term229 A B P p t f s anything a).
Proof. exact (MK_COMB (@lem8240512 A B P p t f s a) (@lem8240527 A B P f anything a)). Qed.
Lemma lem8240530 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8240531 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem8240530 B t2 t1). Qed.
Lemma lem8240532 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term229 A B P p t f s anything a) = (term225 A B P p t f s a).
Proof. exact (@lem8240531 B (anything a) (term225 A B P p t f s a)). Qed.
Lemma lem8240533 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term228 A B P p t s anything f a) = (term225 A B P p t f s a).
Proof. exact (TRANS (@lem8240528 A B P p t f s anything a) (@lem8240532 A B P anything p t f s a)). Qed.
Lemma lem8240534 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term101 A B P t f a) = (term101 A B P t f a).
Proof. exact (eq_refl (term101 A B P t f a)). Qed.
Lemma lem8240535 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term96 A B P t f a) = (term228 A B P p t s anything f a)) = ((term96 A B P t f a) = (term225 A B P p t f s a)).
Proof. exact (MK_COMB (@lem8240534 A B P t f a) (@lem8240533 A B P anything p t f s a)). Qed.
Lemma lem8240538 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term103 A B P p f a) = (term103 A B P p f a).
Proof. exact (eq_refl (term103 A B P p f a)). Qed.
Lemma lem8240539 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term230 A B P p t s anything f a) = (term231 A B P p t f s a).
Proof. exact (MK_COMB (@lem8240538 A B P p f a) (@lem8240535 A B P anything p t f s a)). Qed.
Lemma lem8240542 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term232 A B P p t s anything f) = (term233 A B P p t f s).
Proof. exact (fun_ext (fun a : P => @lem8240539 A B P anything p t f s a)). Qed.
Lemma lem8240543 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8240544 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term234 A B P p t s anything f) = (term235 A B P p t f s).
Proof. exact (MK_COMB (@lem8240543 P) (@lem8240542 A B P anything p t f s)). Qed.
Lemma lem8240549 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term236 A B P p t s anything) = (term237 A B P p t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8240544 A B P anything p t f s)). Qed.
Lemma lem8240550 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8240551 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term238 A B P p t s anything) = (term239 A B P p t s).
Proof. exact (MK_COMB (@lem8240550 A B) (@lem8240549 A B P anything p t s)). Qed.
Lemma lem8240556 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term240 A B P lt2 p t s anything) = (term241 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240437 A B P anything lt2 p t s) (@lem8240551 A B P anything p t s)). Qed.
Lemma lem8240559 {A B P : Type'} (anything : P -> B) (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term242 A B P lt2 p t s anything) = (term243 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240192 A B P p t lt2 s) (@lem8240556 A B P anything lt2 p t s)). Qed.
Lemma lem8240562 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (anything : P -> B) : (term243 A B P lt2 p t s) = (term242 A B P lt2 p t s anything).
Proof. exact (SYM (@lem8240559 A B P anything lt2 p t s)). Qed.
Lemma lem8240564 (p : Prop) : p = (term244 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8240565 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term243 A B P lt2 p t s) = (term245 A B P lt2 p t s).
Proof. exact (@lem8240564 (term243 A B P lt2 p t s)). Qed.
Lemma lem8240566 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term245 A B P lt2 p t s) = (term243 A B P lt2 p t s).
Proof. exact (SYM (@lem8240565 A B P lt2 p t s)). Qed.
Lemma lem8240567 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term246 A B P lt2 p t s) : term246 A B P lt2 p t s.
Proof. exact (h1). Qed.
Lemma lem8240570 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term247 A B P lt2 p t s) : term247 A B P lt2 p t s.
Proof. exact (h1). Qed.
Lemma lem8240571 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term248 A B P lt2 p t s.
Proof. exact (fun h0 : term247 A B P lt2 p t s => @lem8240570 A B P lt2 p t s h0). Qed.
Lemma lem8240572 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term248 A B P lt2 p t s) : term248 A B P lt2 p t s.
Proof. exact (h1). Qed.
Lemma lem8240573 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term247 A B P lt2 p t s) : term247 A B P lt2 p t s.
Proof. exact (h1). Qed.
Lemma lem8240574 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term247 A B P lt2 p t s) (h2 : term248 A B P lt2 p t s) : term247 A B P lt2 p t s.
Proof. exact (@lem8240572 A B P lt2 p t s h2 (@lem8240573 A B P lt2 p t s h1)). Qed.
Lemma lem8240575 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term247 A B P lt2 p t s) : term249 A B P lt2 p t s.
Proof. exact (fun h0 : term248 A B P lt2 p t s => @lem8240574 A B P lt2 p t s h1 h0). Qed.
Lemma lem8240576 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term248 A B P lt2 p t s) : term248 A B P lt2 p t s.
Proof. exact (h1). Qed.
Lemma lem8240577 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term247 A B P lt2 p t s) (h2 : term248 A B P lt2 p t s) : term247 A B P lt2 p t s.
Proof. exact (@lem8240575 A B P lt2 p t s h1 (@lem8240576 A B P lt2 p t s h2)). Qed.
Lemma lem8240578 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term248 A B P lt2 p t s) : term248 A B P lt2 p t s.
Proof. exact (fun h0 : term247 A B P lt2 p t s => @lem8240577 A B P lt2 p t s h0 h1). Qed.
Lemma lem8240579 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term250 A B P lt2 p t s.
Proof. exact (fun h0 : term248 A B P lt2 p t s => @lem8240578 A B P lt2 p t s h0). Qed.
Lemma lem8240582 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term248 A B P lt2 p t s.
Proof. exact (@lem8240579 A B P lt2 p t s (@lem8240571 A B P lt2 p t s)). Qed.
Lemma lem8240583 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term248 A B P lt2 p t s.
Proof. exact (@lem8240582 A B P lt2 p t s). Qed.
Lemma lem8240667 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8240668 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term245 A B P lt2 p t s) = (term251 A B P lt2 p t s).
Proof. exact (@lem8240667 (term246 A B P lt2 p t s)). Qed.
Lemma lem8240670 (t : Prop) : (term252 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8240671 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term251 A B P lt2 p t s) = (term243 A B P lt2 p t s).
Proof. exact (@lem8240670 (term243 A B P lt2 p t s)). Qed.
Lemma lem8240674 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term245 A B P lt2 p t s) = (term243 A B P lt2 p t s).
Proof. exact (TRANS (@lem8240668 A B P lt2 p t s) (@lem8240671 A B P lt2 p t s)). Qed.
Lemma lem8240721 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term82 A B P lt2 s p) = (term82 A B P lt2 s p).
Proof. exact (eq_refl (term82 A B P lt2 s p)). Qed.
Lemma lem8240722 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term253 A B P lt2 p t s) = (term254 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240721 A B P lt2 s p) (@lem8240674 A B P lt2 p t s)). Qed.
Lemma lem8240725 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term255 A B P p t lt2 s) = (term255 A B P p t lt2 s).
Proof. exact (eq_refl (term255 A B P p t lt2 s)). Qed.
Lemma lem8240726 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term256 A B P lt2 p t s) = (term257 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240725 A B P p t lt2 s) (@lem8240722 A B P lt2 p t s)). Qed.
Lemma lem8240729 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term258 A B P p lt2 s t) = (term258 A B P p lt2 s t).
Proof. exact (eq_refl (term258 A B P p lt2 s t)). Qed.
Lemma lem8240730 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term247 A B P lt2 p t s) = (term259 A B P lt2 p t s).
Proof. exact (MK_COMB (@lem8240729 A B P p lt2 s t) (@lem8240726 A B P lt2 p t s)). Qed.
Lemma lem8240733 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term260 A B P p t s) = (term261 A B P p t s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8240730 A B P lt2 p t s)). Qed.
Lemma lem8240734 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8240735 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term262 A B P p t s) = (term263 A B P p t s).
Proof. exact (MK_COMB (@lem8240734 A) (@lem8240733 A B P p t s)). Qed.
Lemma lem8240740 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term264 A B P t s) = (term265 A B P t s).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8240735 A B P p t s)). Qed.
Lemma lem8240741 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8240742 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term266 A B P t s) = (term267 A B P t s).
Proof. exact (MK_COMB (@lem8240741 A B P) (@lem8240740 A B P t s)). Qed.
Lemma lem8240747 {A B P : Type'} (s : P -> A) : (term268 A B P s) = (term269 A B P s).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8240742 A B P t s)). Qed.
Lemma lem8240748 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8240749 {A B P : Type'} (s : P -> A) : (term270 A B P s) = (term271 A B P s).
Proof. exact (MK_COMB (@lem8240748 A B P) (@lem8240747 A B P s)). Qed.
Lemma lem8240754 {A B P : Type'} : (term272 A B P) = (term273 A B P).
Proof. exact (fun_ext (fun s : P -> A => @lem8240749 A B P s)). Qed.
Lemma lem8240755 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8240764 {A B P : Type'} : (term274 A B P) = (term275 A B P).
Proof. exact (MK_COMB (@lem8240755 A P) (@lem8240754 A B P)). Qed.
Lemma lem8240768 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8240769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8240770 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term103 A B P p f a) = (imp False).
Proof. exact (MK_COMB (@lem8240769) (@lem8240768 A B P p f a h1)). Qed.
Lemma lem8240772 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8240773 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240774 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term276 A B P p f a) = (@COND A False).
Proof. exact (MK_COMB (@lem8240773 A) (@lem8240772 A B P p f a h1)). Qed.
Lemma lem8240775 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8240776 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term277 A B P p t f a) = (term278 A B P t f a).
Proof. exact (MK_COMB (@lem8240774 A B P p f a h1) (@lem8240775 A B P t f a)). Qed.
Lemma lem8240777 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240778 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (term279 A B P t f s a).
Proof. exact (MK_COMB (@lem8240776 A B P t p f a h1) (@lem8240777 A P s a)). Qed.
Lemma lem8240780 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8240781 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem8240780 A t1 t2). Qed.
Lemma lem8240782 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term279 A B P t f s a) = (s a).
Proof. exact (@lem8240781 A (t f a) (s a)). Qed.
Lemma lem8240783 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (s a).
Proof. exact (TRANS (@lem8240778 A B P t s p f a h1) (@lem8240782 A B P t f s a)). Qed.
Lemma lem8240784 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240785 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term225 A B P p t f s a) = (term280 A B P f s a).
Proof. exact (MK_COMB (@lem8240784 A B f) (@lem8240783 A B P t s p f a h1)). Qed.
Lemma lem8240786 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term101 A B P t f a) = (term101 A B P t f a).
Proof. exact (eq_refl (term101 A B P t f a)). Qed.
Lemma lem8240787 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : ((term96 A B P t f a) = (term225 A B P p t f s a)) = ((term96 A B P t f a) = (term280 A B P f s a)).
Proof. exact (MK_COMB (@lem8240786 A B P t f a) (@lem8240785 A B P t s p f a h1)). Qed.
Lemma lem8240790 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term231 A B P p t f s a) = (term281 A B P t f s a).
Proof. exact (MK_COMB (@lem8240770 A B P p f a h1) (@lem8240787 A B P t s p f a h1)). Qed.
Lemma lem8240792 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8240793 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term281 A B P t f s a) = True.
Proof. exact (@lem8240792 ((term96 A B P t f a) = (term280 A B P f s a))). Qed.
Lemma lem8240794 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term231 A B P p t f s a) = True.
Proof. exact (TRANS (@lem8240790 A B P t s p f a h1) (@lem8240793 A B P t f s a)). Qed.
Lemma lem8240795 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : term282 A B P p t f s a.
Proof. exact (fun h0 : (p f a) = False => @lem8240794 A B P t s p f a h0). Qed.
Lemma lem8240797 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8240798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8240799 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term103 A B P p f a) = (imp True).
Proof. exact (MK_COMB (@lem8240798) (@lem8240797 A B P p f a h1)). Qed.
Lemma lem8240801 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8240802 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240803 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term276 A B P p f a) = (@COND A True).
Proof. exact (MK_COMB (@lem8240802 A) (@lem8240801 A B P p f a h1)). Qed.
Lemma lem8240804 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8240805 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term277 A B P p t f a) = (term283 A B P t f a).
Proof. exact (MK_COMB (@lem8240803 A B P p f a h1) (@lem8240804 A B P t f a)). Qed.
Lemma lem8240806 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240807 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (term284 A B P t f s a).
Proof. exact (MK_COMB (@lem8240805 A B P t p f a h1) (@lem8240806 A P s a)). Qed.
Lemma lem8240809 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8240810 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem8240809 A t2 t1). Qed.
Lemma lem8240811 {A B P : Type'} (s : P -> A) (t : type557 A B P) (f : A -> B) (a : P) : (term284 A B P t f s a) = (t f a).
Proof. exact (@lem8240810 A (s a) (t f a)). Qed.
Lemma lem8240812 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (t f a).
Proof. exact (TRANS (@lem8240807 A B P t s p f a h1) (@lem8240811 A B P s t f a)). Qed.
Lemma lem8240813 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8240814 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term225 A B P p t f s a) = (term96 A B P t f a).
Proof. exact (MK_COMB (@lem8240813 A B f) (@lem8240812 A B P s t p f a h1)). Qed.
Lemma lem8240815 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term101 A B P t f a) = (term101 A B P t f a).
Proof. exact (eq_refl (term101 A B P t f a)). Qed.
Lemma lem8240816 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((term96 A B P t f a) = (term225 A B P p t f s a)) = ((term96 A B P t f a) = (term96 A B P t f a)).
Proof. exact (MK_COMB (@lem8240815 A B P t f a) (@lem8240814 A B P s t p f a h1)). Qed.
Lemma lem8240818 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8240819 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem8240818 B x). Qed.
Lemma lem8240820 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : ((term96 A B P t f a) = (term96 A B P t f a)) = True.
Proof. exact (@lem8240819 B (term96 A B P t f a)). Qed.
Lemma lem8240821 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((term96 A B P t f a) = (term225 A B P p t f s a)) = True.
Proof. exact (TRANS (@lem8240816 A B P s t p f a h1) (@lem8240820 A B P t f a)). Qed.
Lemma lem8240822 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term231 A B P p t f s a) = (True -> True).
Proof. exact (MK_COMB (@lem8240799 A B P p f a h1) (@lem8240821 A B P t s p f a h1)). Qed.
Lemma lem8240824 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8240825 : (True -> True) = True.
Proof. exact (@lem8240824 True). Qed.
Lemma lem8240826 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term231 A B P p t f s a) = True.
Proof. exact (TRANS (@lem8240822 A B P t s p f a h1) (@lem8240825)). Qed.
Lemma lem8240827 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : term285 A B P p t f s a.
Proof. exact (fun h0 : (p f a) = True => @lem8240826 A B P t s p f a h0). Qed.
Lemma lem8240828 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : term286 A B P p t f s a.
Proof. exact (conj (@lem8240795 A B P p t f s a) (@lem8240827 A B P p t f s a)). Qed.
Lemma lem8240830 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term287 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8240831 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) : term288 A B P t s p f a.
Proof. exact (@lem8240830 (term231 A B P p t f s a) True (p f a) True). Qed.
Lemma lem8240832 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) : (term231 A B P p t f s a) = (term289 A B P p f a).
Proof. exact (@lem8240831 A B P t s p f a (@lem8240828 A B P p t f s a)). Qed.
Lemma lem8240834 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8240835 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term290 A B P p f a) = True.
Proof. exact (@lem8240834 (p f a)). Qed.
Lemma lem8240837 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8240838 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term291 A B P p f a) = True.
Proof. exact (@lem8240837 (term292 A B P p f a)). Qed.
Lemma lem8240839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240840 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term293 A B P p f a) = (and True).
Proof. exact (MK_COMB (@lem8240839) (@lem8240838 A B P p f a)). Qed.
Lemma lem8240841 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term289 A B P p f a) = (True /\ True).
Proof. exact (MK_COMB (@lem8240840 A B P p f a) (@lem8240835 A B P p f a)). Qed.
Lemma lem8240843 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8240844 : (True /\ True) = True.
Proof. exact (@lem8240843 True). Qed.
Lemma lem8240845 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term289 A B P p f a) = True.
Proof. exact (TRANS (@lem8240841 A B P p f a) (@lem8240844)). Qed.
Lemma lem8240850 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term231 A B P p t f s a) = True.
Proof. exact (TRANS (@lem8240832 A B P t s p f a) (@lem8240845 A B P p f a)). Qed.
Lemma lem8240851 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term233 A B P p t f s) = (term50 P).
Proof. exact (fun_ext (fun a : P => @lem8240850 A B P p t f s a)). Qed.
Lemma lem8240852 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8240853 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term235 A B P p t f s) = (term294 P).
Proof. exact (MK_COMB (@lem8240852 P) (@lem8240851 A B P p t f s)). Qed.
Lemma lem8240854 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term237 A B P p t s) = (term295 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem8240853 A B P p t f s)). Qed.
Lemma lem8240855 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8240856 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term239 A B P p t s) = (term296 A B P).
Proof. exact (MK_COMB (@lem8240855 A B) (@lem8240854 A B P p t s)). Qed.
Lemma lem8240868 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8240869 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240870 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term276 A B P p f a) = (@COND A False).
Proof. exact (MK_COMB (@lem8240869 A) (@lem8240868 A B P p f a h1)). Qed.
Lemma lem8240871 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8240872 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term277 A B P p t f a) = (term278 A B P t f a).
Proof. exact (MK_COMB (@lem8240870 A B P p f a h1) (@lem8240871 A B P t f a)). Qed.
Lemma lem8240873 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240874 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (term279 A B P t f s a).
Proof. exact (MK_COMB (@lem8240872 A B P t p f a h1) (@lem8240873 A P s a)). Qed.
Lemma lem8240876 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8240877 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem8240876 A t1 t2). Qed.
Lemma lem8240878 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term279 A B P t f s a) = (s a).
Proof. exact (@lem8240877 A (t f a) (s a)). Qed.
Lemma lem8240879 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (s a).
Proof. exact (TRANS (@lem8240874 A B P t s p f a h1) (@lem8240878 A B P t f s a)). Qed.
Lemma lem8240880 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240881 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term191 A B P p t f s a) = (term202 A P s a).
Proof. exact (MK_COMB (@lem8240880 A) (@lem8240879 A B P t s p f a h1)). Qed.
Lemma lem8240882 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term161 A B P p t g s a) = (term161 A B P p t g s a).
Proof. exact (eq_refl (term161 A B P p t g s a)). Qed.
Lemma lem8240883 {A B P : Type'} (t : type557 A B P) (g : A -> B) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : ((term161 A B P p t f s a) = (term161 A B P p t g s a)) = ((s a) = (term161 A B P p t g s a)).
Proof. exact (MK_COMB (@lem8240881 A B P t s p f a h1) (@lem8240882 A B P p t g s a)). Qed.
Lemma lem8240886 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8240887 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (g : A -> B) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term208 A B P lt2 f p t g s a) = (term297 A B P lt2 f p t g s a).
Proof. exact (MK_COMB (@lem8240886 A B P lt2 s a f g) (@lem8240883 A B P t g s p f a h1)). Qed.
Lemma lem8240890 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : term298 A B P lt2 f p t g s a.
Proof. exact (fun h0 : (p f a) = False => @lem8240887 A B P lt2 t g s p f a h0). Qed.
Lemma lem8240900 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8240901 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240902 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term276 A B P p f a) = (@COND A True).
Proof. exact (MK_COMB (@lem8240901 A) (@lem8240900 A B P p f a h1)). Qed.
Lemma lem8240903 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8240904 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term277 A B P p t f a) = (term283 A B P t f a).
Proof. exact (MK_COMB (@lem8240902 A B P p f a h1) (@lem8240903 A B P t f a)). Qed.
Lemma lem8240905 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240906 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (term284 A B P t f s a).
Proof. exact (MK_COMB (@lem8240904 A B P t p f a h1) (@lem8240905 A P s a)). Qed.
Lemma lem8240908 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8240909 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem8240908 A t2 t1). Qed.
Lemma lem8240910 {A B P : Type'} (s : P -> A) (t : type557 A B P) (f : A -> B) (a : P) : (term284 A B P t f s a) = (t f a).
Proof. exact (@lem8240909 A (s a) (t f a)). Qed.
Lemma lem8240911 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (t f a).
Proof. exact (TRANS (@lem8240906 A B P t s p f a h1) (@lem8240910 A B P s t f a)). Qed.
Lemma lem8240912 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8240913 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term191 A B P p t f s a) = (term299 A B P t f a).
Proof. exact (MK_COMB (@lem8240912 A) (@lem8240911 A B P s t p f a h1)). Qed.
Lemma lem8240914 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term161 A B P p t g s a) = (term161 A B P p t g s a).
Proof. exact (eq_refl (term161 A B P p t g s a)). Qed.
Lemma lem8240915 {A B P : Type'} (t : type557 A B P) (g : A -> B) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : ((term161 A B P p t f s a) = (term161 A B P p t g s a)) = ((t f a) = (term161 A B P p t g s a)).
Proof. exact (MK_COMB (@lem8240913 A B P s t p f a h1) (@lem8240914 A B P p t g s a)). Qed.
Lemma lem8240918 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8240919 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (g : A -> B) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term208 A B P lt2 f p t g s a) = (term300 A B P lt2 f p t g s a).
Proof. exact (MK_COMB (@lem8240918 A B P lt2 s a f g) (@lem8240915 A B P t g s p f a h1)). Qed.
Lemma lem8240922 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : term301 A B P lt2 f p t g s a.
Proof. exact (fun h0 : (p f a) = True => @lem8240919 A B P lt2 t g s p f a h0). Qed.
Lemma lem8240923 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : term302 A B P lt2 f p t g s a.
Proof. exact (conj (@lem8240890 A B P lt2 f p t g s a) (@lem8240922 A B P lt2 f p t g s a)). Qed.
Lemma lem8240925 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term287 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8240926 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : term303 A B P lt2 f p t g s a.
Proof. exact (@lem8240925 (term208 A B P lt2 f p t g s a) (term300 A B P lt2 f p t g s a) (p f a) (term297 A B P lt2 f p t g s a)). Qed.
Lemma lem8240941 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term208 A B P lt2 f p t g s a) = (term304 A B P lt2 f p t g s a).
Proof. exact (@lem8240926 A B P lt2 f p t g s a (@lem8240923 A B P lt2 f p t g s a)). Qed.
Lemma lem8240953 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (p g a) = False.
Proof. exact (h1). Qed.
Lemma lem8240954 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240955 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term276 A B P p g a) = (@COND A False).
Proof. exact (MK_COMB (@lem8240954 A) (@lem8240953 A B P p g a h1)). Qed.
Lemma lem8240956 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8240957 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term277 A B P p t g a) = (term278 A B P t g a).
Proof. exact (MK_COMB (@lem8240955 A B P p g a h1) (@lem8240956 A B P t g a)). Qed.
Lemma lem8240958 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240959 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term161 A B P p t g s a) = (term279 A B P t g s a).
Proof. exact (MK_COMB (@lem8240957 A B P t p g a h1) (@lem8240958 A P s a)). Qed.
Lemma lem8240961 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8240962 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem8240961 A t1 t2). Qed.
Lemma lem8240963 {A B P : Type'} (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term279 A B P t g s a) = (s a).
Proof. exact (@lem8240962 A (t g a) (s a)). Qed.
Lemma lem8240964 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term161 A B P p t g s a) = (s a).
Proof. exact (TRANS (@lem8240959 A B P t s p g a h1) (@lem8240963 A B P t g s a)). Qed.
Lemma lem8240965 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term299 A B P t f a) = (term299 A B P t f a).
Proof. exact (eq_refl (term299 A B P t f a)). Qed.
Lemma lem8240966 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : ((t f a) = (term161 A B P p t g s a)) = ((t f a) = (s a)).
Proof. exact (MK_COMB (@lem8240965 A B P t f a) (@lem8240964 A B P t s p g a h1)). Qed.
Lemma lem8240969 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8240970 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term300 A B P lt2 f p t g s a) = (term305 A B P lt2 g t f s a).
Proof. exact (MK_COMB (@lem8240969 A B P lt2 s a f g) (@lem8240966 A B P t f s p g a h1)). Qed.
Lemma lem8240973 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8240974 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term307 A B P lt2 f p t g s a) = (term308 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8240973 A B P p f a) (@lem8240970 A B P lt2 t f s p g a h1)). Qed.
Lemma lem8240977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8240978 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term309 A B P lt2 f p t g s a) = (term310 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8240977) (@lem8240974 A B P lt2 t f s p g a h1)). Qed.
Lemma lem8240988 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (p g a) = False.
Proof. exact (h1). Qed.
Lemma lem8240989 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8240990 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term276 A B P p g a) = (@COND A False).
Proof. exact (MK_COMB (@lem8240989 A) (@lem8240988 A B P p g a h1)). Qed.
Lemma lem8240991 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8240992 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term277 A B P p t g a) = (term278 A B P t g a).
Proof. exact (MK_COMB (@lem8240990 A B P p g a h1) (@lem8240991 A B P t g a)). Qed.
Lemma lem8240993 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8240994 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term161 A B P p t g s a) = (term279 A B P t g s a).
Proof. exact (MK_COMB (@lem8240992 A B P t p g a h1) (@lem8240993 A P s a)). Qed.
Lemma lem8240996 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8240997 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem8240996 A t1 t2). Qed.
Lemma lem8240998 {A B P : Type'} (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term279 A B P t g s a) = (s a).
Proof. exact (@lem8240997 A (t g a) (s a)). Qed.
Lemma lem8240999 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term161 A B P p t g s a) = (s a).
Proof. exact (TRANS (@lem8240994 A B P t s p g a h1) (@lem8240998 A B P t g s a)). Qed.
Lemma lem8241000 {A P : Type'} (s : P -> A) (a : P) : (term202 A P s a) = (term202 A P s a).
Proof. exact (eq_refl (term202 A P s a)). Qed.
Lemma lem8241001 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : ((s a) = (term161 A B P p t g s a)) = ((s a) = (s a)).
Proof. exact (MK_COMB (@lem8241000 A P s a) (@lem8240999 A B P t s p g a h1)). Qed.
Lemma lem8241003 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8241004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem8241003 A x). Qed.
Lemma lem8241005 {A P : Type'} (s : P -> A) (a : P) : ((s a) = (s a)) = True.
Proof. exact (@lem8241004 A (s a)). Qed.
Lemma lem8241006 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : ((s a) = (term161 A B P p t g s a)) = True.
Proof. exact (TRANS (@lem8241001 A B P t s p g a h1) (@lem8241005 A P s a)). Qed.
Lemma lem8241007 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8241008 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term297 A B P lt2 f p t g s a) = (term311 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241007 A B P lt2 s a f g) (@lem8241006 A B P t s p g a h1)). Qed.
Lemma lem8241010 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8241011 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term311 A B P lt2 s a f g) = True.
Proof. exact (@lem8241010 (term62 A B P lt2 s a f g)). Qed.
Lemma lem8241012 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term297 A B P lt2 f p t g s a) = True.
Proof. exact (TRANS (@lem8241008 A B P t lt2 s f p g a h1) (@lem8241011 A B P lt2 s a f g)). Qed.
Lemma lem8241013 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term312 A B P p f a) = (term312 A B P p f a).
Proof. exact (eq_refl (term312 A B P p f a)). Qed.
Lemma lem8241014 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term313 A B P lt2 f p t g s a) = (term290 A B P p f a).
Proof. exact (MK_COMB (@lem8241013 A B P p f a) (@lem8241012 A B P lt2 f t s p g a h1)). Qed.
Lemma lem8241016 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8241017 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term290 A B P p f a) = True.
Proof. exact (@lem8241016 (p f a)). Qed.
Lemma lem8241018 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term313 A B P lt2 f p t g s a) = True.
Proof. exact (TRANS (@lem8241014 A B P lt2 t s f p g a h1) (@lem8241017 A B P p f a)). Qed.
Lemma lem8241019 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term304 A B P lt2 f p t g s a) = (term314 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8240978 A B P lt2 t f s p g a h1) (@lem8241018 A B P lt2 f t s p g a h1)). Qed.
Lemma lem8241021 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8241022 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term314 A B P p lt2 g t f s a) = (term308 A B P p lt2 g t f s a).
Proof. exact (@lem8241021 (term308 A B P p lt2 g t f s a)). Qed.
Lemma lem8241025 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = False) : (term304 A B P lt2 f p t g s a) = (term308 A B P p lt2 g t f s a).
Proof. exact (TRANS (@lem8241019 A B P lt2 t f s p g a h1) (@lem8241022 A B P p lt2 g t f s a)). Qed.
Lemma lem8241026 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : term315 A B P p lt2 g t f s a.
Proof. exact (fun h0 : (p g a) = False => @lem8241025 A B P lt2 t f s p g a h0). Qed.
Lemma lem8241036 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (p g a) = True.
Proof. exact (h1). Qed.
Lemma lem8241037 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8241038 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term276 A B P p g a) = (@COND A True).
Proof. exact (MK_COMB (@lem8241037 A) (@lem8241036 A B P p g a h1)). Qed.
Lemma lem8241039 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8241040 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term277 A B P p t g a) = (term283 A B P t g a).
Proof. exact (MK_COMB (@lem8241038 A B P p g a h1) (@lem8241039 A B P t g a)). Qed.
Lemma lem8241041 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8241042 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term161 A B P p t g s a) = (term284 A B P t g s a).
Proof. exact (MK_COMB (@lem8241040 A B P t p g a h1) (@lem8241041 A P s a)). Qed.
Lemma lem8241044 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8241045 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem8241044 A t2 t1). Qed.
Lemma lem8241046 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term284 A B P t g s a) = (t g a).
Proof. exact (@lem8241045 A (s a) (t g a)). Qed.
Lemma lem8241047 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term161 A B P p t g s a) = (t g a).
Proof. exact (TRANS (@lem8241042 A B P t s p g a h1) (@lem8241046 A B P s t g a)). Qed.
Lemma lem8241048 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term299 A B P t f a) = (term299 A B P t f a).
Proof. exact (eq_refl (term299 A B P t f a)). Qed.
Lemma lem8241049 {A B P : Type'} (s : P -> A) (f : A -> B) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : ((t f a) = (term161 A B P p t g s a)) = ((t f a) = (t g a)).
Proof. exact (MK_COMB (@lem8241048 A B P t f a) (@lem8241047 A B P s t p g a h1)). Qed.
Lemma lem8241052 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8241053 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term300 A B P lt2 f p t g s a) = (term316 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241052 A B P lt2 s a f g) (@lem8241049 A B P s f t p g a h1)). Qed.
Lemma lem8241056 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241057 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term307 A B P lt2 f p t g s a) = (term317 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241056 A B P p f a) (@lem8241053 A B P lt2 s f t p g a h1)). Qed.
Lemma lem8241060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8241061 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term309 A B P lt2 f p t g s a) = (term318 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241060) (@lem8241057 A B P lt2 s f t p g a h1)). Qed.
Lemma lem8241071 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (p g a) = True.
Proof. exact (h1). Qed.
Lemma lem8241072 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8241073 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term276 A B P p g a) = (@COND A True).
Proof. exact (MK_COMB (@lem8241072 A) (@lem8241071 A B P p g a h1)). Qed.
Lemma lem8241074 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (t g a).
Proof. exact (eq_refl (t g a)). Qed.
Lemma lem8241075 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term277 A B P p t g a) = (term283 A B P t g a).
Proof. exact (MK_COMB (@lem8241073 A B P p g a h1) (@lem8241074 A B P t g a)). Qed.
Lemma lem8241076 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8241077 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term161 A B P p t g s a) = (term284 A B P t g s a).
Proof. exact (MK_COMB (@lem8241075 A B P t p g a h1) (@lem8241076 A P s a)). Qed.
Lemma lem8241079 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8241080 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem8241079 A t2 t1). Qed.
Lemma lem8241081 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term284 A B P t g s a) = (t g a).
Proof. exact (@lem8241080 A (s a) (t g a)). Qed.
Lemma lem8241082 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term161 A B P p t g s a) = (t g a).
Proof. exact (TRANS (@lem8241077 A B P t s p g a h1) (@lem8241081 A B P s t g a)). Qed.
Lemma lem8241083 {A P : Type'} (s : P -> A) (a : P) : (term202 A P s a) = (term202 A P s a).
Proof. exact (eq_refl (term202 A P s a)). Qed.
Lemma lem8241084 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : ((s a) = (term161 A B P p t g s a)) = ((s a) = (t g a)).
Proof. exact (MK_COMB (@lem8241083 A P s a) (@lem8241082 A B P s t p g a h1)). Qed.
Lemma lem8241087 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (eq_refl (term67 A B P lt2 s a f g)). Qed.
Lemma lem8241088 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term297 A B P lt2 f p t g s a) = (term319 A B P lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241087 A B P lt2 s a f g) (@lem8241084 A B P s t p g a h1)). Qed.
Lemma lem8241091 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term312 A B P p f a) = (term312 A B P p f a).
Proof. exact (eq_refl (term312 A B P p f a)). Qed.
Lemma lem8241092 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term313 A B P lt2 f p t g s a) = (term320 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241091 A B P p f a) (@lem8241088 A B P lt2 f s t p g a h1)). Qed.
Lemma lem8241095 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : (p g a) = True) : (term304 A B P lt2 f p t g s a) = (term321 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241061 A B P lt2 s f t p g a h1) (@lem8241092 A B P lt2 f s t p g a h1)). Qed.
Lemma lem8241098 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : term322 A B P p lt2 f s t g a.
Proof. exact (fun h0 : (p g a) = True => @lem8241095 A B P lt2 f s t p g a h0). Qed.
Lemma lem8241099 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : term323 A B P p lt2 f s t g a.
Proof. exact (conj (@lem8241026 A B P p lt2 g t f s a) (@lem8241098 A B P p lt2 f s t g a)). Qed.
Lemma lem8241101 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term287 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8241102 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : term324 A B P p lt2 g t f s a.
Proof. exact (@lem8241101 (term304 A B P lt2 f p t g s a) (term321 A B P p lt2 f s t g a) (p g a) (term308 A B P p lt2 g t f s a)). Qed.
Lemma lem8241117 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term304 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a).
Proof. exact (@lem8241102 A B P p lt2 g t f s a (@lem8241099 A B P p lt2 f s t g a)). Qed.
Lemma lem8241118 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((t f a) = (s a)) = ((t f a) = (s a)).
Proof. exact (eq_refl ((t f a) = (s a))). Qed.
Lemma lem8241123 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term326 A B P lt2 s a f g z)). Qed.
Lemma lem8241124 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term327 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241123 A B P lt2 s a f g z)). Qed.
Lemma lem8241125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241126 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241125 A) (@lem8241124 A B P lt2 s a f g)). Qed.
Lemma lem8241127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241128 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241127) (@lem8241126 A B P lt2 s a f g)). Qed.
Lemma lem8241129 {A B P : Type'} (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term305 A B P lt2 g t f s a) = (term305 A B P lt2 g t f s a).
Proof. exact (MK_COMB (@lem8241128 A B P lt2 s a f g) (@lem8241118 A B P t f s a)). Qed.
Lemma lem8241134 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241135 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term308 A B P p lt2 g t f s a) = (term308 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8241134 A B P p f a) (@lem8241129 A B P lt2 g t f s a)). Qed.
Lemma lem8241138 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term312 A B P p g a) = (term312 A B P p g a).
Proof. exact (eq_refl (term312 A B P p g a)). Qed.
Lemma lem8241139 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term328 A B P p lt2 g t f s a) = (term328 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8241138 A B P p g a) (@lem8241135 A B P p lt2 g t f s a)). Qed.
Lemma lem8241140 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : ((s a) = (t g a)) = ((s a) = (t g a)).
Proof. exact (eq_refl ((s a) = (t g a))). Qed.
Lemma lem8241145 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term326 A B P lt2 s a f g z)). Qed.
Lemma lem8241146 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term327 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241145 A B P lt2 s a f g z)). Qed.
Lemma lem8241147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241148 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241147 A) (@lem8241146 A B P lt2 s a f g)). Qed.
Lemma lem8241149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241150 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241149) (@lem8241148 A B P lt2 s a f g)). Qed.
Lemma lem8241151 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term319 A B P lt2 f s t g a) = (term319 A B P lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241150 A B P lt2 s a f g) (@lem8241140 A B P s t g a)). Qed.
Lemma lem8241154 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term312 A B P p f a) = (term312 A B P p f a).
Proof. exact (eq_refl (term312 A B P p f a)). Qed.
Lemma lem8241155 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term320 A B P p lt2 f s t g a) = (term320 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241154 A B P p f a) (@lem8241151 A B P lt2 f s t g a)). Qed.
Lemma lem8241156 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241161 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term326 A B P lt2 s a f g z)). Qed.
Lemma lem8241162 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term327 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241161 A B P lt2 s a f g z)). Qed.
Lemma lem8241163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241164 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241163 A) (@lem8241162 A B P lt2 s a f g)). Qed.
Lemma lem8241165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241166 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241165) (@lem8241164 A B P lt2 s a f g)). Qed.
Lemma lem8241167 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term316 A B P lt2 s f t g a) = (term316 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241166 A B P lt2 s a f g) (@lem8241156 A B P f t g a)). Qed.
Lemma lem8241172 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241173 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term317 A B P p lt2 s f t g a) = (term317 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241172 A B P p f a) (@lem8241167 A B P lt2 s f t g a)). Qed.
Lemma lem8241174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8241175 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term318 A B P p lt2 s f t g a) = (term318 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241174) (@lem8241173 A B P p lt2 s f t g a)). Qed.
Lemma lem8241176 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term321 A B P p lt2 f s t g a) = (term321 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241175 A B P p lt2 s f t g a) (@lem8241155 A B P p lt2 f s t g a)). Qed.
Lemma lem8241181 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term306 A B P p g a) = (term306 A B P p g a).
Proof. exact (eq_refl (term306 A B P p g a)). Qed.
Lemma lem8241182 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term329 A B P p lt2 f s t g a) = (term329 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241181 A B P p g a) (@lem8241176 A B P p lt2 f s t g a)). Qed.
Lemma lem8241183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8241184 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term330 A B P p lt2 f s t g a) = (term330 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8241183) (@lem8241182 A B P p lt2 f s t g a)). Qed.
Lemma lem8241185 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term325 A B P p lt2 g t f s a) = (term325 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8241184 A B P p lt2 f s t g a) (@lem8241139 A B P p lt2 g t f s a)). Qed.
Lemma lem8241186 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term331 A B P lt2 f p t g s a) = (term331 A B P lt2 f p t g s a).
Proof. exact (eq_refl (term331 A B P lt2 f p t g s a)). Qed.
Lemma lem8241187 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term304 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a)) = ((term304 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a)).
Proof. exact (MK_COMB (@lem8241186 A B P lt2 f p t g s a) (@lem8241185 A B P p lt2 g t f s a)). Qed.
Lemma lem8241188 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term304 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a).
Proof. exact (EQ_MP (@lem8241187 A B P p lt2 g t f s a) (@lem8241117 A B P p lt2 g t f s a)). Qed.
Lemma lem8241189 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (p : type560 A B P) (t : type557 A B P) (g : A -> B) (s : P -> A) (a : P) : (term332 A B P lt2 f p t g s a) = (term332 A B P lt2 f p t g s a).
Proof. exact (eq_refl (term332 A B P lt2 f p t g s a)). Qed.
Lemma lem8241190 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : ((term208 A B P lt2 f p t g s a) = (term304 A B P lt2 f p t g s a)) = ((term208 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a)).
Proof. exact (MK_COMB (@lem8241189 A B P lt2 f p t g s a) (@lem8241188 A B P p lt2 g t f s a)). Qed.
Lemma lem8241191 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term208 A B P lt2 f p t g s a) = (term325 A B P p lt2 g t f s a).
Proof. exact (EQ_MP (@lem8241190 A B P p lt2 g t f s a) (@lem8240941 A B P lt2 f p t g s a)). Qed.
Lemma lem8241192 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term210 A B P lt2 f p t g s) = (term333 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8241191 A B P p lt2 g t f s a)). Qed.
Lemma lem8241193 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241194 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term212 A B P lt2 f p t g s) = (term334 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8241193 P) (@lem8241192 A B P p lt2 g t f s)). Qed.
Lemma lem8241195 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term214 A B P lt2 f p t s) = (term335 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8241194 A B P p lt2 g t f s)). Qed.
Lemma lem8241196 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241197 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term216 A B P lt2 f p t s) = (term336 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8241196 A B) (@lem8241195 A B P p lt2 t f s)). Qed.
Lemma lem8241198 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term218 A B P lt2 p t s) = (term337 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8241197 A B P p lt2 t f s)). Qed.
Lemma lem8241199 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241200 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term220 A B P lt2 p t s) = (term338 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241199 A B) (@lem8241198 A B P p lt2 t s)). Qed.
Lemma lem8241201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8241202 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term222 A B P lt2 p t s) = (term339 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241201) (@lem8241200 A B P p lt2 t s)). Qed.
Lemma lem8241203 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term241 A B P lt2 p t s) = (term340 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241202 A B P p lt2 t s) (@lem8240856 A B P p t s)). Qed.
Lemma lem8241207 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (p f a) = False.
Proof. exact (h1). Qed.
Lemma lem8241208 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8241209 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term276 A B P p f a) = (@COND A False).
Proof. exact (MK_COMB (@lem8241208 A) (@lem8241207 A B P p f a h1)). Qed.
Lemma lem8241210 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8241211 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term277 A B P p t f a) = (term278 A B P t f a).
Proof. exact (MK_COMB (@lem8241209 A B P p f a h1) (@lem8241210 A B P t f a)). Qed.
Lemma lem8241212 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8241213 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (term279 A B P t f s a).
Proof. exact (MK_COMB (@lem8241211 A B P t p f a h1) (@lem8241212 A P s a)). Qed.
Lemma lem8241215 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8241216 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem8241215 A t1 t2). Qed.
Lemma lem8241217 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term279 A B P t f s a) = (s a).
Proof. exact (@lem8241216 A (t f a) (s a)). Qed.
Lemma lem8241218 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term161 A B P p t f s a) = (s a).
Proof. exact (TRANS (@lem8241213 A B P t s p f a h1) (@lem8241217 A B P t f s a)). Qed.
Lemma lem8241219 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8241220 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (y : A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term166 A B P lt2 y p t f s a) = (term171 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8241219 A lt2 y) (@lem8241218 A B P t s p f a h1)). Qed.
Lemma lem8241221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241222 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (y : A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term170 A B P lt2 y p t f s a) = (term341 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8241221) (@lem8241220 A B P t lt2 y s p f a h1)). Qed.
Lemma lem8241223 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term171 A P lt2 y s a).
Proof. exact (eq_refl (term171 A P lt2 y s a)). Qed.
Lemma lem8241224 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (y : A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term173 A B P p t f lt2 y s a) = (term342 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8241222 A B P t lt2 y s p f a h1) (@lem8241223 A P lt2 y s a)). Qed.
Lemma lem8241226 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem8241227 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term342 A P lt2 y s a) = True.
Proof. exact (@lem8241226 (term171 A P lt2 y s a)). Qed.
Lemma lem8241228 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (y : A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term173 A B P p t f lt2 y s a) = True.
Proof. exact (TRANS (@lem8241224 A B P t lt2 y s p f a h1) (@lem8241227 A P lt2 y s a)). Qed.
Lemma lem8241229 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term175 A B P p t f lt2 s a) = (term50 A).
Proof. exact (fun_ext (fun y : A => @lem8241228 A B P t lt2 y s p f a h1)). Qed.
Lemma lem8241230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241231 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term177 A B P p t f lt2 s a) = (term294 A).
Proof. exact (MK_COMB (@lem8241230 A) (@lem8241229 A B P t lt2 s p f a h1)). Qed.
Lemma lem8241233 {A : Type'} (t : Prop) : (term343 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8241234 {A : Type'} (t : Prop) : (term343 A t) = t.
Proof. exact (@lem8241233 A t). Qed.
Lemma lem8241235 {A : Type'} : (term294 A) = True.
Proof. exact (@lem8241234 A True). Qed.
Lemma lem8241236 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = False) : (term177 A B P p t f lt2 s a) = True.
Proof. exact (TRANS (@lem8241231 A B P t lt2 s p f a h1) (@lem8241235 A)). Qed.
Lemma lem8241237 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : term344 A B P p t f lt2 s a.
Proof. exact (fun h0 : (p f a) = False => @lem8241236 A B P t lt2 s p f a h0). Qed.
Lemma lem8241239 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (p f a) = True.
Proof. exact (h1). Qed.
Lemma lem8241240 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem8241241 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term276 A B P p f a) = (@COND A True).
Proof. exact (MK_COMB (@lem8241240 A) (@lem8241239 A B P p f a h1)). Qed.
Lemma lem8241242 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (t f a).
Proof. exact (eq_refl (t f a)). Qed.
Lemma lem8241243 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term277 A B P p t f a) = (term283 A B P t f a).
Proof. exact (MK_COMB (@lem8241241 A B P p f a h1) (@lem8241242 A B P t f a)). Qed.
Lemma lem8241244 {A P : Type'} (s : P -> A) (a : P) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem8241245 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (term284 A B P t f s a).
Proof. exact (MK_COMB (@lem8241243 A B P t p f a h1) (@lem8241244 A P s a)). Qed.
Lemma lem8241247 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8241248 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem8241247 A t2 t1). Qed.
Lemma lem8241249 {A B P : Type'} (s : P -> A) (t : type557 A B P) (f : A -> B) (a : P) : (term284 A B P t f s a) = (t f a).
Proof. exact (@lem8241248 A (s a) (t f a)). Qed.
Lemma lem8241250 {A B P : Type'} (s : P -> A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term161 A B P p t f s a) = (t f a).
Proof. exact (TRANS (@lem8241245 A B P t s p f a h1) (@lem8241249 A B P s t f a)). Qed.
Lemma lem8241251 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8241252 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (y : A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term166 A B P lt2 y p t f s a) = (term345 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8241251 A lt2 y) (@lem8241250 A B P s t p f a h1)). Qed.
Lemma lem8241253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241254 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (y : A) (t : type557 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term170 A B P lt2 y p t f s a) = (term346 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8241253) (@lem8241252 A B P s lt2 y t p f a h1)). Qed.
Lemma lem8241255 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term171 A P lt2 y s a).
Proof. exact (eq_refl (term171 A P lt2 y s a)). Qed.
Lemma lem8241256 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (y : A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term173 A B P p t f lt2 y s a) = (term347 A B P t f lt2 y s a).
Proof. exact (MK_COMB (@lem8241254 A B P s lt2 y t p f a h1) (@lem8241255 A P lt2 y s a)). Qed.
Lemma lem8241259 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term175 A B P p t f lt2 s a) = (term348 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8241256 A B P t lt2 y s p f a h1)). Qed.
Lemma lem8241260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241261 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) (h1 : (p f a) = True) : (term177 A B P p t f lt2 s a) = (term349 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8241260 A) (@lem8241259 A B P t lt2 s p f a h1)). Qed.
Lemma lem8241266 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : term350 A B P p t f lt2 s a.
Proof. exact (fun h0 : (p f a) = True => @lem8241261 A B P t lt2 s p f a h0). Qed.
Lemma lem8241267 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : term351 A B P p t f lt2 s a.
Proof. exact (conj (@lem8241237 A B P p t f lt2 s a) (@lem8241266 A B P p t f lt2 s a)). Qed.
Lemma lem8241269 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term287 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8241270 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) : term352 A B P t lt2 s p f a.
Proof. exact (@lem8241269 (term177 A B P p t f lt2 s a) (term349 A B P t f lt2 s a) (p f a) True). Qed.
Lemma lem8241271 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (f : A -> B) (a : P) : (term177 A B P p t f lt2 s a) = (term353 A B P t lt2 s p f a).
Proof. exact (@lem8241270 A B P t lt2 s p f a (@lem8241267 A B P p t f lt2 s a)). Qed.
Lemma lem8241273 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8241274 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term290 A B P p f a) = True.
Proof. exact (@lem8241273 (p f a)). Qed.
Lemma lem8241279 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term354 A B P p t f lt2 s a) = (term354 A B P p t f lt2 s a).
Proof. exact (eq_refl (term354 A B P p t f lt2 s a)). Qed.
Lemma lem8241280 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term353 A B P t lt2 s p f a) = (term355 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8241279 A B P p t f lt2 s a) (@lem8241274 A B P p f a)). Qed.
Lemma lem8241282 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8241283 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term355 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (@lem8241282 (term356 A B P p t f lt2 s a)). Qed.
Lemma lem8241284 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term353 A B P t lt2 s p f a) = (term356 A B P p t f lt2 s a).
Proof. exact (TRANS (@lem8241280 A B P p t f lt2 s a) (@lem8241283 A B P p t f lt2 s a)). Qed.
Lemma lem8241285 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term177 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (TRANS (@lem8241271 A B P t lt2 s p f a) (@lem8241284 A B P p t f lt2 s a)). Qed.
Lemma lem8241290 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term347 A B P t f lt2 y s a) = (term347 A B P t f lt2 y s a).
Proof. exact (eq_refl (term347 A B P t f lt2 y s a)). Qed.
Lemma lem8241291 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term348 A B P t f lt2 s a) = (term348 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8241290 A B P t f lt2 y s a)). Qed.
Lemma lem8241292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241293 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term349 A B P t f lt2 s a) = (term349 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8241292 A) (@lem8241291 A B P t f lt2 s a)). Qed.
Lemma lem8241298 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241299 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term356 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8241298 A B P p f a) (@lem8241293 A B P t f lt2 s a)). Qed.
Lemma lem8241300 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term357 A B P p t f lt2 s a) = (term357 A B P p t f lt2 s a).
Proof. exact (eq_refl (term357 A B P p t f lt2 s a)). Qed.
Lemma lem8241301 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : ((term177 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a)) = ((term177 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a)).
Proof. exact (MK_COMB (@lem8241300 A B P p t f lt2 s a) (@lem8241299 A B P p t f lt2 s a)). Qed.
Lemma lem8241302 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term177 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (EQ_MP (@lem8241301 A B P p t f lt2 s a) (@lem8241285 A B P p t f lt2 s a)). Qed.
Lemma lem8241303 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term179 A B P p t f lt2 s) = (term358 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8241302 A B P p t f lt2 s a)). Qed.
Lemma lem8241304 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241305 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term181 A B P p t f lt2 s) = (term359 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8241304 P) (@lem8241303 A B P p t f lt2 s)). Qed.
Lemma lem8241306 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term183 A B P p t lt2 s) = (term360 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8241305 A B P p t f lt2 s)). Qed.
Lemma lem8241307 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241308 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term185 A B P p t lt2 s) = (term361 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8241307 A B) (@lem8241306 A B P p t lt2 s)). Qed.
Lemma lem8241309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8241310 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term187 A B P p t lt2 s) = (term362 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8241309) (@lem8241308 A B P p t lt2 s)). Qed.
Lemma lem8241311 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term243 A B P lt2 p t s) = (term363 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241310 A B P p t lt2 s) (@lem8241203 A B P p lt2 t s)). Qed.
Lemma lem8241316 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = ((p f a) = (p g a)).
Proof. exact (eq_refl ((p f a) = (p g a))). Qed.
Lemma lem8241321 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term326 A B P lt2 s a f g z)). Qed.
Lemma lem8241322 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term327 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241321 A B P lt2 s a f g z)). Qed.
Lemma lem8241323 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241324 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241323 A) (@lem8241322 A B P lt2 s a f g)). Qed.
Lemma lem8241325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241326 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term67 A B P lt2 s a f g) = (term67 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241325) (@lem8241324 A B P lt2 s a f g)). Qed.
Lemma lem8241327 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term69 A B P lt2 s f p g a) = (term69 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8241326 A B P lt2 s a f g) (@lem8241316 A B P f p g a)). Qed.
Lemma lem8241328 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term71 A B P lt2 s f p g) = (term71 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8241327 A B P lt2 s f p g a)). Qed.
Lemma lem8241329 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241330 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term73 A B P lt2 s f p g) = (term73 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8241329 P) (@lem8241328 A B P lt2 s f p g)). Qed.
Lemma lem8241331 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term75 A B P lt2 s f p) = (term75 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8241330 A B P lt2 s f p g)). Qed.
Lemma lem8241332 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241333 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term77 A B P lt2 s f p) = (term77 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8241332 A B) (@lem8241331 A B P lt2 s f p)). Qed.
Lemma lem8241334 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term79 A B P lt2 s p) = (term79 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8241333 A B P lt2 s f p)). Qed.
Lemma lem8241335 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241336 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term80 A B P lt2 s p) = (term80 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8241335 A B) (@lem8241334 A B P lt2 s p)). Qed.
Lemma lem8241337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241338 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term82 A B P lt2 s p) = (term82 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8241337) (@lem8241336 A B P lt2 s p)). Qed.
Lemma lem8241339 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term254 A B P lt2 p t s) = (term364 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241338 A B P lt2 s p) (@lem8241311 A B P p lt2 t s)). Qed.
Lemma lem8241344 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term347 A B P t f lt2 y s a) = (term347 A B P t f lt2 y s a).
Proof. exact (eq_refl (term347 A B P t f lt2 y s a)). Qed.
Lemma lem8241345 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term348 A B P t f lt2 s a) = (term348 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8241344 A B P t f lt2 y s a)). Qed.
Lemma lem8241346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241347 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term349 A B P t f lt2 s a) = (term349 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8241346 A) (@lem8241345 A B P t f lt2 s a)). Qed.
Lemma lem8241350 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term103 A B P p f a) = (term103 A B P p f a).
Proof. exact (eq_refl (term103 A B P p f a)). Qed.
Lemma lem8241351 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term365 A B P p t f lt2 s a) = (term365 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8241350 A B P p f a) (@lem8241347 A B P t f lt2 s a)). Qed.
Lemma lem8241352 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term366 A B P p t f lt2 s) = (term366 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8241351 A B P p t f lt2 s a)). Qed.
Lemma lem8241353 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241354 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term367 A B P p t f lt2 s) = (term367 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8241353 P) (@lem8241352 A B P p t f lt2 s)). Qed.
Lemma lem8241355 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term368 A B P p t lt2 s) = (term368 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8241354 A B P p t f lt2 s)). Qed.
Lemma lem8241356 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241357 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term34 A B P p t lt2 s) = (term34 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8241356 A B) (@lem8241355 A B P p t lt2 s)). Qed.
Lemma lem8241358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241359 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term255 A B P p t lt2 s) = (term255 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8241358) (@lem8241357 A B P p t lt2 s)). Qed.
Lemma lem8241360 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term257 A B P lt2 p t s) = (term369 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241359 A B P p t lt2 s) (@lem8241339 A B P p lt2 t s)). Qed.
Lemma lem8241361 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241366 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term326 A B P lt2 s a f g z)). Qed.
Lemma lem8241367 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term327 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241366 A B P lt2 s a f g z)). Qed.
Lemma lem8241368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8241369 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term62 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241368 A) (@lem8241367 A B P lt2 s a f g)). Qed.
Lemma lem8241372 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term370 A B P p g a) = (term370 A B P p g a).
Proof. exact (eq_refl (term370 A B P p g a)). Qed.
Lemma lem8241373 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term371 A B P p lt2 s a f g) = (term371 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241372 A B P p g a) (@lem8241369 A B P lt2 s a f g)). Qed.
Lemma lem8241376 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term370 A B P p f a) = (term370 A B P p f a).
Proof. exact (eq_refl (term370 A B P p f a)). Qed.
Lemma lem8241377 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term372 A B P p lt2 s a f g) = (term372 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241376 A B P p f a) (@lem8241373 A B P p lt2 s a f g)). Qed.
Lemma lem8241378 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241379 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term373 A B P p lt2 s a f g) = (term373 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241378) (@lem8241377 A B P p lt2 s a f g)). Qed.
Lemma lem8241380 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term374 A B P p lt2 s f t g a) = (term374 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241379 A B P p lt2 s a f g) (@lem8241361 A B P f t g a)). Qed.
Lemma lem8241381 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term375 A B P p lt2 s f t g) = (term375 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8241380 A B P p lt2 s f t g a)). Qed.
Lemma lem8241382 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241383 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term376 A B P p lt2 s f t g) = (term376 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241382 P) (@lem8241381 A B P p lt2 s f t g)). Qed.
Lemma lem8241384 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term377 A B P p lt2 s f t) = (term377 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8241383 A B P p lt2 s f t g)). Qed.
Lemma lem8241385 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241386 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term378 A B P p lt2 s f t) = (term378 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8241385 A B) (@lem8241384 A B P p lt2 s f t)). Qed.
Lemma lem8241387 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term379 A B P p lt2 s t) = (term379 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8241386 A B P p lt2 s f t)). Qed.
Lemma lem8241388 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241389 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term31 A B P p lt2 s t) = (term31 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8241388 A B) (@lem8241387 A B P p lt2 s t)). Qed.
Lemma lem8241390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8241391 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term258 A B P p lt2 s t) = (term258 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8241390) (@lem8241389 A B P p lt2 s t)). Qed.
Lemma lem8241392 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term259 A B P lt2 p t s) = (term380 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241391 A B P p lt2 s t) (@lem8241360 A B P p lt2 t s)). Qed.
Lemma lem8241393 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term261 A B P p t s) = (term381 A B P p t s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8241392 A B P p lt2 t s)). Qed.
Lemma lem8241394 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8241395 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term263 A B P p t s) = (term382 A B P p t s).
Proof. exact (MK_COMB (@lem8241394 A) (@lem8241393 A B P p t s)). Qed.
Lemma lem8241396 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term265 A B P t s) = (term383 A B P t s).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8241395 A B P p t s)). Qed.
Lemma lem8241397 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8241398 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term267 A B P t s) = (term384 A B P t s).
Proof. exact (MK_COMB (@lem8241397 A B P) (@lem8241396 A B P t s)). Qed.
Lemma lem8241399 {A B P : Type'} (s : P -> A) : (term269 A B P s) = (term385 A B P s).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8241398 A B P t s)). Qed.
Lemma lem8241400 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8241401 {A B P : Type'} (s : P -> A) : (term271 A B P s) = (term386 A B P s).
Proof. exact (MK_COMB (@lem8241400 A B P) (@lem8241399 A B P s)). Qed.
Lemma lem8241402 {A B P : Type'} : (term273 A B P) = (term387 A B P).
Proof. exact (fun_ext (fun s : P -> A => @lem8241401 A B P s)). Qed.
Lemma lem8241403 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8241404 {A B P : Type'} : (term275 A B P) = (term388 A B P).
Proof. exact (MK_COMB (@lem8241403 A P) (@lem8241402 A B P)). Qed.
Lemma lem8241405 {A B P : Type'} : (term274 A B P) = (term388 A B P).
Proof. exact (TRANS (@lem8240764 A B P) (@lem8241404 A B P)). Qed.
Lemma lem8241607 {A : Type'} (t : Prop) : (term343 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8241608 {A B : Type'} (t : Prop) : (term389 A B t) = t.
Proof. exact (@lem8241607 (A -> B) t). Qed.
Lemma lem8241609 {A B P : Type'} : (term296 A B P) = (term294 P).
Proof. exact (@lem8241608 A B (term294 P)). Qed.
Lemma lem8241611 {A : Type'} (t : Prop) : (term343 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem8241612 {P : Type'} (t : Prop) : (term343 P t) = t.
Proof. exact (@lem8241611 P t). Qed.
Lemma lem8241613 {P : Type'} : (term294 P) = True.
Proof. exact (@lem8241612 P True). Qed.
Lemma lem8241614 {A B P : Type'} : (term296 A B P) = True.
Proof. exact (TRANS (@lem8241609 A B P) (@lem8241613 P)). Qed.
Lemma lem8241615 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term339 A B P p lt2 t s) = (term339 A B P p lt2 t s).
Proof. exact (eq_refl (term339 A B P p lt2 t s)). Qed.
Lemma lem8241616 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term340 A B P p lt2 t s) = (term390 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241615 A B P p lt2 t s) (@lem8241614 A B P)). Qed.
Lemma lem8241618 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem8241619 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term390 A B P p lt2 t s) = (term338 A B P p lt2 t s).
Proof. exact (@lem8241618 (term338 A B P p lt2 t s)). Qed.
Lemma lem8241682 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term340 A B P p lt2 t s) = (term338 A B P p lt2 t s).
Proof. exact (TRANS (@lem8241616 A B P p lt2 t s) (@lem8241619 A B P p lt2 t s)). Qed.
Lemma lem8241683 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term362 A B P p t lt2 s) = (term362 A B P p t lt2 s).
Proof. exact (eq_refl (term362 A B P p t lt2 s)). Qed.
Lemma lem8241684 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term363 A B P p lt2 t s) = (term391 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241683 A B P p t lt2 s) (@lem8241682 A B P p lt2 t s)). Qed.
Lemma lem8241687 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term82 A B P lt2 s p) = (term82 A B P lt2 s p).
Proof. exact (eq_refl (term82 A B P lt2 s p)). Qed.
Lemma lem8241688 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term364 A B P p lt2 t s) = (term392 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241687 A B P lt2 s p) (@lem8241684 A B P p lt2 t s)). Qed.
Lemma lem8241691 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term255 A B P p t lt2 s) = (term255 A B P p t lt2 s).
Proof. exact (eq_refl (term255 A B P p t lt2 s)). Qed.
Lemma lem8241692 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term369 A B P p lt2 t s) = (term393 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241691 A B P p t lt2 s) (@lem8241688 A B P p lt2 t s)). Qed.
Lemma lem8241695 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term258 A B P p lt2 s t) = (term258 A B P p lt2 s t).
Proof. exact (eq_refl (term258 A B P p lt2 s t)). Qed.
Lemma lem8241696 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term380 A B P p lt2 t s) = (term394 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8241695 A B P p lt2 s t) (@lem8241692 A B P p lt2 t s)). Qed.
Lemma lem8241699 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term381 A B P p t s) = (term395 A B P p t s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8241696 A B P p lt2 t s)). Qed.
Lemma lem8241700 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8241701 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term382 A B P p t s) = (term396 A B P p t s).
Proof. exact (MK_COMB (@lem8241700 A) (@lem8241699 A B P p t s)). Qed.
Lemma lem8241708 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term383 A B P t s) = (term397 A B P t s).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8241701 A B P p t s)). Qed.
Lemma lem8241709 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8241710 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term384 A B P t s) = (term398 A B P t s).
Proof. exact (MK_COMB (@lem8241709 A B P) (@lem8241708 A B P t s)). Qed.
Lemma lem8241717 {A B P : Type'} (s : P -> A) : (term385 A B P s) = (term399 A B P s).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8241710 A B P t s)). Qed.
Lemma lem8241718 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8241719 {A B P : Type'} (s : P -> A) : (term386 A B P s) = (term400 A B P s).
Proof. exact (MK_COMB (@lem8241718 A B P) (@lem8241717 A B P s)). Qed.
Lemma lem8241726 {A B P : Type'} : (term387 A B P) = (term401 A B P).
Proof. exact (fun_ext (fun s : P -> A => @lem8241719 A B P s)). Qed.
Lemma lem8241727 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8241728 {A B P : Type'} : (term388 A B P) = (term402 A B P).
Proof. exact (MK_COMB (@lem8241727 A P) (@lem8241726 A B P)). Qed.
Lemma lem8241735 {A B P : Type'} : (term274 A B P) = (term402 A B P).
Proof. exact (TRANS (@lem8241405 A B P) (@lem8241728 A B P)). Qed.
Lemma lem8241736 {A B P : Type'} : (term402 A B P) = (term274 A B P).
Proof. exact (SYM (@lem8241735 A B P)). Qed.
Lemma lem8241737 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term31 A B P p lt2 s t) : term31 A B P p lt2 s t.
Proof. exact (h1). Qed.
Lemma lem8241738 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term34 A B P p t lt2 s.
Proof. exact (h1). Qed.
Lemma lem8241739 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term80 A B P lt2 s p) : term80 A B P lt2 s p.
Proof. exact (h1). Qed.
Lemma lem8241741 (p : Prop) : p = (term244 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8241742 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term391 A B P p lt2 t s) = (term403 A B P p lt2 t s).
Proof. exact (@lem8241741 (term391 A B P p lt2 t s)). Qed.
Lemma lem8241743 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term403 A B P p lt2 t s) = (term391 A B P p lt2 t s).
Proof. exact (SYM (@lem8241742 A B P p lt2 t s)). Qed.
Lemma lem8241744 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term404 A B P p lt2 t s) : term404 A B P p lt2 t s.
Proof. exact (h1). Qed.
Lemma lem8241753 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term405 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term171 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8241754 {A : Type'} (P : A -> Prop) : (term407 A P) = (term408 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8241755 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term409 A B P lt2 s a f g) = (term410 A B P lt2 s a f g).
Proof. exact (@lem8241754 A (term327 A B P lt2 s a f g)). Qed.
Lemma lem8241756 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term411 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term411 A B P lt2 s a f g z)). Qed.
Lemma lem8241757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8241758 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term412 A B P lt2 s a f g z) = (term405 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8241757) (@lem8241756 A B P lt2 s a f g z)). Qed.
Lemma lem8241759 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term412 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8241758 A B P lt2 s a f g z) (@lem8241753 A B P lt2 s a f g z)). Qed.
Lemma lem8241760 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term413 A B P lt2 s a f g) = (term414 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241759 A B P lt2 s a f g z)). Qed.
Lemma lem8241761 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241762 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term410 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241761 A) (@lem8241760 A B P lt2 s a f g)). Qed.
Lemma lem8241763 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term409 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8241755 A B P lt2 s a f g) (@lem8241762 A B P lt2 s a f g)). Qed.
Lemma lem8241765 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term306 A B P p g a) = (term306 A B P p g a).
Proof. exact (eq_refl (term306 A B P p g a)). Qed.
Lemma lem8241766 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term416 A B P p lt2 s a f g) = (term417 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241765 A B P p g a) (@lem8241763 A B P lt2 s a f g)). Qed.
Lemma lem8241767 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term418 A B P p lt2 s a f g) = (term416 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term62 A B P lt2 s a f g)). Qed.
Lemma lem8241768 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term418 A B P p lt2 s a f g) = (term417 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8241767 A B P p lt2 s a f g) (@lem8241766 A B P p lt2 s a f g)). Qed.
Lemma lem8241770 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241771 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term419 A B P p lt2 s a f g) = (term420 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241770 A B P p f a) (@lem8241768 A B P p lt2 s a f g)). Qed.
Lemma lem8241772 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term421 A B P p lt2 s a f g) = (term419 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term371 A B P p lt2 s a f g)). Qed.
Lemma lem8241773 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term421 A B P p lt2 s a f g) = (term420 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8241772 A B P p lt2 s a f g) (@lem8241771 A B P p lt2 s a f g)). Qed.
Lemma lem8241774 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8241776 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term422 A B P p lt2 s a f g) = (term423 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241775) (@lem8241773 A B P p lt2 s a f g)). Qed.
Lemma lem8241777 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term424 A B P p lt2 s f t g a) = (term425 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241776 A B P p lt2 s a f g) (@lem8241774 A B P f t g a)). Qed.
Lemma lem8241778 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term374 A B P p lt2 s f t g a) = (term424 A B P p lt2 s f t g a).
Proof. exact (@lem17265 (term372 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8241779 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term374 A B P p lt2 s f t g a) = (term425 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8241778 A B P p lt2 s f t g a) (@lem8241777 A B P p lt2 s f t g a)). Qed.
Lemma lem8241780 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term375 A B P p lt2 s f t g) = (term426 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8241779 A B P p lt2 s f t g a)). Qed.
Lemma lem8241781 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241782 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term376 A B P p lt2 s f t g) = (term427 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241781 P) (@lem8241780 A B P p lt2 s f t g)). Qed.
Lemma lem8241783 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term377 A B P p lt2 s f t) = (term428 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8241782 A B P p lt2 s f t g)). Qed.
Lemma lem8241784 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241785 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term378 A B P p lt2 s f t) = (term429 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8241784 A B) (@lem8241783 A B P p lt2 s f t)). Qed.
Lemma lem8241786 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term379 A B P p lt2 s t) = (term430 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8241785 A B P p lt2 s f t)). Qed.
Lemma lem8241787 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8241788 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term31 A B P p lt2 s t) = (term431 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8241787 A B) (@lem8241786 A B P p lt2 s t)). Qed.
Lemma lem8241895 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8241896 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (@lem8241895 A P Q). Qed.
Lemma lem8241897 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term434 A B P p lt2 s a f g) = (term435 A B P p lt2 s a f g).
Proof. exact (@lem8241896 A (term292 A B P p g a) (term414 A B P lt2 s a f g)). Qed.
Lemma lem8241898 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term436 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (eq_refl (term436 A B P lt2 s a f g z)). Qed.
Lemma lem8241899 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term437 A B P lt2 s a f g) = (term414 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241898 A B P lt2 s a f g z)). Qed.
Lemma lem8241900 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241901 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term438 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8241900 A) (@lem8241899 A B P lt2 s a f g)). Qed.
Lemma lem8241902 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term306 A B P p g a) = (term306 A B P p g a).
Proof. exact (eq_refl (term306 A B P p g a)). Qed.
Lemma lem8241903 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term434 A B P p lt2 s a f g) = (term417 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241902 A B P p g a) (@lem8241901 A B P lt2 s a f g)). Qed.
Lemma lem8241904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8241905 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term439 A B P p lt2 s a f g) = (term440 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241904) (@lem8241903 A B P p lt2 s a f g)). Qed.
Lemma lem8241906 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term436 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (eq_refl (term436 A B P lt2 s a f g z)). Qed.
Lemma lem8241907 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term306 A B P p g a) = (term306 A B P p g a).
Proof. exact (eq_refl (term306 A B P p g a)). Qed.
Lemma lem8241908 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term441 A B P p lt2 s a f g z) = (term442 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8241907 A B P p g a) (@lem8241906 A B P lt2 s a f g z)). Qed.
Lemma lem8241909 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term443 A B P p lt2 s a f g) = (term444 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241908 A B P p lt2 s a f g z)). Qed.
Lemma lem8241910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241911 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term435 A B P p lt2 s a f g) = (term445 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241910 A) (@lem8241909 A B P p lt2 s a f g)). Qed.
Lemma lem8241912 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term434 A B P p lt2 s a f g) = (term435 A B P p lt2 s a f g)) = ((term417 A B P p lt2 s a f g) = (term445 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8241905 A B P p lt2 s a f g) (@lem8241911 A B P p lt2 s a f g)). Qed.
Lemma lem8241913 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term417 A B P p lt2 s a f g) = (term445 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8241912 A B P p lt2 s a f g) (@lem8241897 A B P p lt2 s a f g)). Qed.
Lemma lem8241914 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241915 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term420 A B P p lt2 s a f g) = (term446 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241914 A B P p f a) (@lem8241913 A B P p lt2 s a f g)). Qed.
Lemma lem8241917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8241918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (@lem8241917 A P Q). Qed.
Lemma lem8241919 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term447 A B P p lt2 s a f g) = (term448 A B P p lt2 s a f g).
Proof. exact (@lem8241918 A (term292 A B P p f a) (term444 A B P p lt2 s a f g)). Qed.
Lemma lem8241920 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term449 A B P p lt2 s a f g z) = (term442 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term449 A B P p lt2 s a f g z)). Qed.
Lemma lem8241921 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term450 A B P p lt2 s a f g) = (term444 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241920 A B P p lt2 s a f g z)). Qed.
Lemma lem8241922 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241923 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term451 A B P p lt2 s a f g) = (term445 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241922 A) (@lem8241921 A B P p lt2 s a f g)). Qed.
Lemma lem8241924 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241925 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term447 A B P p lt2 s a f g) = (term446 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241924 A B P p f a) (@lem8241923 A B P p lt2 s a f g)). Qed.
Lemma lem8241926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8241927 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term452 A B P p lt2 s a f g) = (term453 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241926) (@lem8241925 A B P p lt2 s a f g)). Qed.
Lemma lem8241928 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term449 A B P p lt2 s a f g z) = (term442 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term449 A B P p lt2 s a f g z)). Qed.
Lemma lem8241929 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8241930 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term454 A B P p lt2 s a f g z) = (term455 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8241929 A B P p f a) (@lem8241928 A B P p lt2 s a f g z)). Qed.
Lemma lem8241931 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term456 A B P p lt2 s a f g) = (term457 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241930 A B P p lt2 s a f g z)). Qed.
Lemma lem8241932 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241933 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term448 A B P p lt2 s a f g) = (term458 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241932 A) (@lem8241931 A B P p lt2 s a f g)). Qed.
Lemma lem8241934 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term447 A B P p lt2 s a f g) = (term448 A B P p lt2 s a f g)) = ((term446 A B P p lt2 s a f g) = (term458 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8241927 A B P p lt2 s a f g) (@lem8241933 A B P p lt2 s a f g)). Qed.
Lemma lem8241935 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term446 A B P p lt2 s a f g) = (term458 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8241934 A B P p lt2 s a f g) (@lem8241919 A B P p lt2 s a f g)). Qed.
Lemma lem8241936 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term420 A B P p lt2 s a f g) = (term458 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8241915 A B P p lt2 s a f g) (@lem8241935 A B P p lt2 s a f g)). Qed.
Lemma lem8241937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8241938 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term423 A B P p lt2 s a f g) = (term459 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241937) (@lem8241936 A B P p lt2 s a f g)). Qed.
Lemma lem8241939 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241940 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term425 A B P p lt2 s f t g a) = (term460 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241938 A B P p lt2 s a f g) (@lem8241939 A B P f t g a)). Qed.
Lemma lem8241942 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8241943 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (@lem8241942 A P Q). Qed.
Lemma lem8241944 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term463 A B P p lt2 s f t g a) = (term464 A B P p lt2 s f t g a).
Proof. exact (@lem8241943 A (term457 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8241945 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term465 A B P p lt2 s a f g z) = (term455 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term465 A B P p lt2 s a f g z)). Qed.
Lemma lem8241946 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term466 A B P p lt2 s a f g) = (term457 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8241945 A B P p lt2 s a f g z)). Qed.
Lemma lem8241947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241948 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term467 A B P p lt2 s a f g) = (term458 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241947 A) (@lem8241946 A B P p lt2 s a f g)). Qed.
Lemma lem8241949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8241950 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term468 A B P p lt2 s a f g) = (term459 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8241949) (@lem8241948 A B P p lt2 s a f g)). Qed.
Lemma lem8241951 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241952 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term463 A B P p lt2 s f t g a) = (term460 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241950 A B P p lt2 s a f g) (@lem8241951 A B P f t g a)). Qed.
Lemma lem8241953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8241954 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term469 A B P p lt2 s f t g a) = (term470 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241953) (@lem8241952 A B P p lt2 s f t g a)). Qed.
Lemma lem8241955 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term465 A B P p lt2 s a f g z) = (term455 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term465 A B P p lt2 s a f g z)). Qed.
Lemma lem8241956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8241957 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term471 A B P p lt2 s a f g z) = (term472 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8241956) (@lem8241955 A B P p lt2 s a f g z)). Qed.
Lemma lem8241958 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8241959 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term473 A B P p lt2 s z f t g a) = (term474 A B P p lt2 s z f t g a).
Proof. exact (MK_COMB (@lem8241957 A B P p lt2 s a f g z) (@lem8241958 A B P f t g a)). Qed.
Lemma lem8241960 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term475 A B P p lt2 s f t g a) = (term476 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8241959 A B P p lt2 s z f t g a)). Qed.
Lemma lem8241961 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241962 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term464 A B P p lt2 s f t g a) = (term477 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241961 A) (@lem8241960 A B P p lt2 s f t g a)). Qed.
Lemma lem8241963 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term463 A B P p lt2 s f t g a) = (term464 A B P p lt2 s f t g a)) = ((term460 A B P p lt2 s f t g a) = (term477 A B P p lt2 s f t g a)).
Proof. exact (MK_COMB (@lem8241954 A B P p lt2 s f t g a) (@lem8241962 A B P p lt2 s f t g a)). Qed.
Lemma lem8241964 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term460 A B P p lt2 s f t g a) = (term477 A B P p lt2 s f t g a).
Proof. exact (EQ_MP (@lem8241963 A B P p lt2 s f t g a) (@lem8241944 A B P p lt2 s f t g a)). Qed.
Lemma lem8241965 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term425 A B P p lt2 s f t g a) = (term477 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8241940 A B P p lt2 s f t g a) (@lem8241964 A B P p lt2 s f t g a)). Qed.
Lemma lem8241966 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term426 A B P p lt2 s f t g) = (term478 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8241965 A B P p lt2 s f t g a)). Qed.
Lemma lem8241967 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241968 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term427 A B P p lt2 s f t g) = (term479 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241967 P) (@lem8241966 A B P p lt2 s f t g)). Qed.
Lemma lem8241970 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8241971 {A P : Type'} (P' : type1470 A P) : (term482 A P P') = (term483 A P P').
Proof. exact (@lem8241970 P A P'). Qed.
Lemma lem8241972 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term484 A B P p lt2 s f t g) = (term485 A B P p lt2 s f t g).
Proof. exact (@lem8241971 A P (term486 A B P p lt2 s f t g)). Qed.
Lemma lem8241973 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term487 A B P p lt2 s f t g a) = (term476 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term487 A B P p lt2 s f t g a)). Qed.
Lemma lem8241974 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8241975 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (z : A) : (term488 A B P p lt2 s f t g a z) = (term489 A B P p lt2 s f t g a z).
Proof. exact (MK_COMB (@lem8241973 A B P p lt2 s f t g a) (@lem8241974 A z)). Qed.
Lemma lem8241976 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term489 A B P p lt2 s f t g a z) = (term474 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term489 A B P p lt2 s f t g a z)). Qed.
Lemma lem8241977 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term488 A B P p lt2 s f t g a z) = (term474 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8241975 A B P p lt2 s f t g a z) (@lem8241976 A B P p lt2 s z f t g a)). Qed.
Lemma lem8241978 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term490 A B P p lt2 s f t g a) = (term476 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8241977 A B P p lt2 s z f t g a)). Qed.
Lemma lem8241979 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8241980 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term491 A B P p lt2 s f t g a) = (term477 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8241979 A) (@lem8241978 A B P p lt2 s f t g a)). Qed.
Lemma lem8241981 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term492 A B P p lt2 s f t g) = (term478 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8241980 A B P p lt2 s f t g a)). Qed.
Lemma lem8241982 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241983 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term484 A B P p lt2 s f t g) = (term479 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241982 P) (@lem8241981 A B P p lt2 s f t g)). Qed.
Lemma lem8241984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8241985 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term493 A B P p lt2 s f t g) = (term494 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241984) (@lem8241983 A B P p lt2 s f t g)). Qed.
Lemma lem8241986 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term487 A B P p lt2 s f t g a) = (term476 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term487 A B P p lt2 s f t g a)). Qed.
Lemma lem8241987 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8241988 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (z : P -> A) (a : P) : (term495 A B P p lt2 s f t g z a) = (term496 A B P p lt2 s f t g z a).
Proof. exact (MK_COMB (@lem8241986 A B P p lt2 s f t g a) (@lem8241987 A P z a)). Qed.
Lemma lem8241989 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term496 A B P p lt2 s f t g z a) = (term497 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term496 A B P p lt2 s f t g z a)). Qed.
Lemma lem8241990 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term495 A B P p lt2 s f t g z a) = (term497 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8241988 A B P p lt2 s f t g z a) (@lem8241989 A B P p lt2 s z f t g a)). Qed.
Lemma lem8241991 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term498 A B P p lt2 s f t g z) = (term499 A B P p lt2 s z f t g).
Proof. exact (fun_ext (fun a : P => @lem8241990 A B P p lt2 s z f t g a)). Qed.
Lemma lem8241992 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8241993 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term500 A B P p lt2 s f t g z) = (term501 A B P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8241992 P) (@lem8241991 A B P p lt2 s z f t g)). Qed.
Lemma lem8241994 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term502 A B P p lt2 s f t g) = (term503 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8241993 A B P p lt2 s z f t g)). Qed.
Lemma lem8241995 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8241996 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term485 A B P p lt2 s f t g) = (term504 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8241995 A P) (@lem8241994 A B P p lt2 s f t g)). Qed.
Lemma lem8241997 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : ((term484 A B P p lt2 s f t g) = (term485 A B P p lt2 s f t g)) = ((term479 A B P p lt2 s f t g) = (term504 A B P p lt2 s f t g)).
Proof. exact (MK_COMB (@lem8241985 A B P p lt2 s f t g) (@lem8241996 A B P p lt2 s f t g)). Qed.
Lemma lem8241998 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term479 A B P p lt2 s f t g) = (term504 A B P p lt2 s f t g).
Proof. exact (EQ_MP (@lem8241997 A B P p lt2 s f t g) (@lem8241972 A B P p lt2 s f t g)). Qed.
Lemma lem8241999 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term427 A B P p lt2 s f t g) = (term504 A B P p lt2 s f t g).
Proof. exact (TRANS (@lem8241968 A B P p lt2 s f t g) (@lem8241998 A B P p lt2 s f t g)). Qed.
Lemma lem8242000 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term428 A B P p lt2 s f t) = (term505 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8241999 A B P p lt2 s f t g)). Qed.
Lemma lem8242001 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242002 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term429 A B P p lt2 s f t) = (term506 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8242001 A B) (@lem8242000 A B P p lt2 s f t)). Qed.
Lemma lem8242004 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8242005 {A B P : Type'} (P' : type537 A B P) : (term507 A B P P') = (term508 A B P P').
Proof. exact (@lem8242004 (A -> B) (P -> A) P'). Qed.
Lemma lem8242006 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term509 A B P p lt2 s f t) = (term510 A B P p lt2 s f t).
Proof. exact (@lem8242005 A B P (term511 A B P p lt2 s f t)). Qed.
Lemma lem8242007 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term512 A B P p lt2 s f t g) = (term503 A B P p lt2 s f t g).
Proof. exact (eq_refl (term512 A B P p lt2 s f t g)). Qed.
Lemma lem8242008 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8242009 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (z : P -> A) : (term513 A B P p lt2 s f t g z) = (term514 A B P p lt2 s f t g z).
Proof. exact (MK_COMB (@lem8242007 A B P p lt2 s f t g) (@lem8242008 A P z)). Qed.
Lemma lem8242010 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term514 A B P p lt2 s f t g z) = (term501 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term514 A B P p lt2 s f t g z)). Qed.
Lemma lem8242011 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term513 A B P p lt2 s f t g z) = (term501 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8242009 A B P p lt2 s f t g z) (@lem8242010 A B P p lt2 s z f t g)). Qed.
Lemma lem8242012 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term515 A B P p lt2 s f t g) = (term503 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8242011 A B P p lt2 s z f t g)). Qed.
Lemma lem8242013 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8242014 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term516 A B P p lt2 s f t g) = (term504 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8242013 A P) (@lem8242012 A B P p lt2 s f t g)). Qed.
Lemma lem8242015 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term517 A B P p lt2 s f t) = (term505 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8242014 A B P p lt2 s f t g)). Qed.
Lemma lem8242016 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242017 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term509 A B P p lt2 s f t) = (term506 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8242016 A B) (@lem8242015 A B P p lt2 s f t)). Qed.
Lemma lem8242018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242019 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term518 A B P p lt2 s f t) = (term519 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8242018) (@lem8242017 A B P p lt2 s f t)). Qed.
Lemma lem8242020 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term512 A B P p lt2 s f t g) = (term503 A B P p lt2 s f t g).
Proof. exact (eq_refl (term512 A B P p lt2 s f t g)). Qed.
Lemma lem8242021 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8242022 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (z : type557 A B P) (g : A -> B) : (term520 A B P p lt2 s f t z g) = (term521 A B P p lt2 s f t z g).
Proof. exact (MK_COMB (@lem8242020 A B P p lt2 s f t g) (@lem8242021 A B P z g)). Qed.
Lemma lem8242023 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term521 A B P p lt2 s f t z g) = (term522 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term521 A B P p lt2 s f t z g)). Qed.
Lemma lem8242024 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term520 A B P p lt2 s f t z g) = (term522 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8242022 A B P p lt2 s f t z g) (@lem8242023 A B P p lt2 s z f t g)). Qed.
Lemma lem8242025 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term523 A B P p lt2 s f t z) = (term524 A B P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8242024 A B P p lt2 s z f t g)). Qed.
Lemma lem8242026 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242027 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term525 A B P p lt2 s f t z) = (term526 A B P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8242026 A B) (@lem8242025 A B P p lt2 s z f t)). Qed.
Lemma lem8242028 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term527 A B P p lt2 s f t) = (term528 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8242027 A B P p lt2 s z f t)). Qed.
Lemma lem8242029 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8242030 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term510 A B P p lt2 s f t) = (term529 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8242029 A B P) (@lem8242028 A B P p lt2 s f t)). Qed.
Lemma lem8242031 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : ((term509 A B P p lt2 s f t) = (term510 A B P p lt2 s f t)) = ((term506 A B P p lt2 s f t) = (term529 A B P p lt2 s f t)).
Proof. exact (MK_COMB (@lem8242019 A B P p lt2 s f t) (@lem8242030 A B P p lt2 s f t)). Qed.
Lemma lem8242032 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term506 A B P p lt2 s f t) = (term529 A B P p lt2 s f t).
Proof. exact (EQ_MP (@lem8242031 A B P p lt2 s f t) (@lem8242006 A B P p lt2 s f t)). Qed.
Lemma lem8242033 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term429 A B P p lt2 s f t) = (term529 A B P p lt2 s f t).
Proof. exact (TRANS (@lem8242002 A B P p lt2 s f t) (@lem8242032 A B P p lt2 s f t)). Qed.
Lemma lem8242034 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term430 A B P p lt2 s t) = (term530 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8242033 A B P p lt2 s f t)). Qed.
Lemma lem8242035 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242036 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term431 A B P p lt2 s t) = (term531 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8242035 A B) (@lem8242034 A B P p lt2 s t)). Qed.
Lemma lem8242038 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8242039 {A B P : Type'} (P' : type495 A B P) : (term532 A B P P') = (term533 A B P P').
Proof. exact (@lem8242038 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8242040 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term534 A B P p lt2 s t) = (term535 A B P p lt2 s t).
Proof. exact (@lem8242039 A B P (term536 A B P p lt2 s t)). Qed.
Lemma lem8242041 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term537 A B P p lt2 s t f) = (term528 A B P p lt2 s f t).
Proof. exact (eq_refl (term537 A B P p lt2 s t f)). Qed.
Lemma lem8242042 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8242043 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (z : type557 A B P) : (term538 A B P p lt2 s t f z) = (term539 A B P p lt2 s f t z).
Proof. exact (MK_COMB (@lem8242041 A B P p lt2 s f t) (@lem8242042 A B P z)). Qed.
Lemma lem8242044 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term539 A B P p lt2 s f t z) = (term526 A B P p lt2 s z f t).
Proof. exact (eq_refl (term539 A B P p lt2 s f t z)). Qed.
Lemma lem8242045 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term538 A B P p lt2 s t f z) = (term526 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8242043 A B P p lt2 s f t z) (@lem8242044 A B P p lt2 s z f t)). Qed.
Lemma lem8242046 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term540 A B P p lt2 s t f) = (term528 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8242045 A B P p lt2 s z f t)). Qed.
Lemma lem8242047 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8242048 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term541 A B P p lt2 s t f) = (term529 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8242047 A B P) (@lem8242046 A B P p lt2 s f t)). Qed.
Lemma lem8242049 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term542 A B P p lt2 s t) = (term530 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8242048 A B P p lt2 s f t)). Qed.
Lemma lem8242050 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242051 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term534 A B P p lt2 s t) = (term531 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8242050 A B) (@lem8242049 A B P p lt2 s t)). Qed.
Lemma lem8242052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242053 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term543 A B P p lt2 s t) = (term544 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8242052) (@lem8242051 A B P p lt2 s t)). Qed.
Lemma lem8242054 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term537 A B P p lt2 s t f) = (term528 A B P p lt2 s f t).
Proof. exact (eq_refl (term537 A B P p lt2 s t f)). Qed.
Lemma lem8242055 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8242056 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (z : type518 A B P) (f : A -> B) : (term545 A B P p lt2 s t z f) = (term546 A B P p lt2 s t z f).
Proof. exact (MK_COMB (@lem8242054 A B P p lt2 s f t) (@lem8242055 A B P z f)). Qed.
Lemma lem8242057 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term546 A B P p lt2 s t z f) = (term547 A B P p lt2 s z f t).
Proof. exact (eq_refl (term546 A B P p lt2 s t z f)). Qed.
Lemma lem8242058 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term545 A B P p lt2 s t z f) = (term547 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8242056 A B P p lt2 s t z f) (@lem8242057 A B P p lt2 s z f t)). Qed.
Lemma lem8242059 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term548 A B P p lt2 s t z) = (term549 A B P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8242058 A B P p lt2 s z f t)). Qed.
Lemma lem8242060 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242061 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term550 A B P p lt2 s t z) = (term551 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8242060 A B) (@lem8242059 A B P p lt2 s z t)). Qed.
Lemma lem8242062 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term552 A B P p lt2 s t) = (term553 A B P p lt2 s t).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8242061 A B P p lt2 s z t)). Qed.
Lemma lem8242063 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8242064 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term535 A B P p lt2 s t) = (term554 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8242063 A B P) (@lem8242062 A B P p lt2 s t)). Qed.
Lemma lem8242065 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : ((term534 A B P p lt2 s t) = (term535 A B P p lt2 s t)) = ((term531 A B P p lt2 s t) = (term554 A B P p lt2 s t)).
Proof. exact (MK_COMB (@lem8242053 A B P p lt2 s t) (@lem8242064 A B P p lt2 s t)). Qed.
Lemma lem8242066 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term531 A B P p lt2 s t) = (term554 A B P p lt2 s t).
Proof. exact (EQ_MP (@lem8242065 A B P p lt2 s t) (@lem8242040 A B P p lt2 s t)). Qed.
Lemma lem8242068 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term431 A B P p lt2 s t) = (term554 A B P p lt2 s t).
Proof. exact (TRANS (@lem8242036 A B P p lt2 s t) (@lem8242066 A B P p lt2 s t)). Qed.
Lemma lem8242069 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term31 A B P p lt2 s t) = (term554 A B P p lt2 s t).
Proof. exact (TRANS (@lem8241788 A B P p lt2 s t) (@lem8242068 A B P p lt2 s t)). Qed.
Lemma lem8242070 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term31 A B P p lt2 s t) : term554 A B P p lt2 s t.
Proof. exact (EQ_MP (@lem8242069 A B P p lt2 s t) (@lem8241737 A B P p lt2 s t h1)). Qed.
Lemma lem8242078 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term347 A B P t f lt2 y s a) = (term555 A B P t f lt2 y s a).
Proof. exact (@lem17265 (term345 A B P lt2 y t f a) (term171 A P lt2 y s a)). Qed.
Lemma lem8242079 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term348 A B P t f lt2 s a) = (term556 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8242078 A B P t f lt2 y s a)). Qed.
Lemma lem8242080 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8242081 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term349 A B P t f lt2 s a) = (term557 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8242080 A) (@lem8242079 A B P t f lt2 s a)). Qed.
Lemma lem8242083 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term306 A B P p f a).
Proof. exact (eq_refl (term306 A B P p f a)). Qed.
Lemma lem8242084 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term356 A B P p t f lt2 s a) = (term558 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8242083 A B P p f a) (@lem8242081 A B P t f lt2 s a)). Qed.
Lemma lem8242085 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term365 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (@lem17265 (p f a) (term349 A B P t f lt2 s a)). Qed.
Lemma lem8242086 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term365 A B P p t f lt2 s a) = (term558 A B P p t f lt2 s a).
Proof. exact (TRANS (@lem8242085 A B P p t f lt2 s a) (@lem8242084 A B P p t f lt2 s a)). Qed.
Lemma lem8242087 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term366 A B P p t f lt2 s) = (term559 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8242086 A B P p t f lt2 s a)). Qed.
Lemma lem8242088 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8242089 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term367 A B P p t f lt2 s) = (term560 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8242088 P) (@lem8242087 A B P p t f lt2 s)). Qed.
Lemma lem8242090 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term368 A B P p t lt2 s) = (term561 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8242089 A B P p t f lt2 s)). Qed.
Lemma lem8242091 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242196 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term34 A B P p t lt2 s) = (term562 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8242091 A B) (@lem8242090 A B P p t lt2 s)). Qed.
Lemma lem8242197 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term562 A B P p t lt2 s.
Proof. exact (EQ_MP (@lem8242196 A B P p t lt2 s) (@lem8241738 A B P p t lt2 s h1)). Qed.
Lemma lem8242204 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term405 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term171 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8242205 {A : Type'} (P : A -> Prop) : (term407 A P) = (term408 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8242206 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term409 A B P lt2 s a f g) = (term410 A B P lt2 s a f g).
Proof. exact (@lem8242205 A (term327 A B P lt2 s a f g)). Qed.
Lemma lem8242207 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term411 A B P lt2 s a f g z) = (term326 A B P lt2 s a f g z).
Proof. exact (eq_refl (term411 A B P lt2 s a f g z)). Qed.
Lemma lem8242208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242209 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term412 A B P lt2 s a f g z) = (term405 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8242208) (@lem8242207 A B P lt2 s a f g z)). Qed.
Lemma lem8242210 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term412 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8242209 A B P lt2 s a f g z) (@lem8242204 A B P lt2 s a f g z)). Qed.
Lemma lem8242211 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term413 A B P lt2 s a f g) = (term414 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8242210 A B P lt2 s a f g z)). Qed.
Lemma lem8242212 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8242213 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term410 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242212 A) (@lem8242211 A B P lt2 s a f g)). Qed.
Lemma lem8242214 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term409 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8242206 A B P lt2 s a f g) (@lem8242213 A B P lt2 s a f g)). Qed.
Lemma lem8242229 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((p f a) = (p g a)) = (term563 A B P f p g a).
Proof. exact (@lem17784 (p f a) (p g a)). Qed.
Lemma lem8242230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242231 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term564 A B P lt2 s a f g) = (term565 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242230) (@lem8242214 A B P lt2 s a f g)). Qed.
Lemma lem8242232 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term566 A B P lt2 s f p g a) = (term567 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8242231 A B P lt2 s a f g) (@lem8242229 A B P f p g a)). Qed.
Lemma lem8242233 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term69 A B P lt2 s f p g a) = (term566 A B P lt2 s f p g a).
Proof. exact (@lem17265 (term62 A B P lt2 s a f g) ((p f a) = (p g a))). Qed.
Lemma lem8242234 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term69 A B P lt2 s f p g a) = (term567 A B P lt2 s f p g a).
Proof. exact (TRANS (@lem8242233 A B P lt2 s f p g a) (@lem8242232 A B P lt2 s f p g a)). Qed.
Lemma lem8242235 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term71 A B P lt2 s f p g) = (term568 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8242234 A B P lt2 s f p g a)). Qed.
Lemma lem8242236 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8242237 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term73 A B P lt2 s f p g) = (term569 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242236 P) (@lem8242235 A B P lt2 s f p g)). Qed.
Lemma lem8242238 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term75 A B P lt2 s f p) = (term570 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8242237 A B P lt2 s f p g)). Qed.
Lemma lem8242239 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242240 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term77 A B P lt2 s f p) = (term571 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242239 A B) (@lem8242238 A B P lt2 s f p)). Qed.
Lemma lem8242241 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term79 A B P lt2 s p) = (term572 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8242240 A B P lt2 s f p)). Qed.
Lemma lem8242242 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242243 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term80 A B P lt2 s p) = (term573 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8242242 A B) (@lem8242241 A B P lt2 s p)). Qed.
Lemma lem8242350 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8242351 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (@lem8242350 A P Q). Qed.
Lemma lem8242352 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term574 A B P lt2 s f p g a) = (term575 A B P lt2 s f p g a).
Proof. exact (@lem8242351 A (term414 A B P lt2 s a f g) (term563 A B P f p g a)). Qed.
Lemma lem8242353 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term436 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (eq_refl (term436 A B P lt2 s a f g z)). Qed.
Lemma lem8242354 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term437 A B P lt2 s a f g) = (term414 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8242353 A B P lt2 s a f g z)). Qed.
Lemma lem8242355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8242356 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term438 A B P lt2 s a f g) = (term415 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242355 A) (@lem8242354 A B P lt2 s a f g)). Qed.
Lemma lem8242357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242358 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term576 A B P lt2 s a f g) = (term565 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242357) (@lem8242356 A B P lt2 s a f g)). Qed.
Lemma lem8242359 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term563 A B P f p g a) = (term563 A B P f p g a).
Proof. exact (eq_refl (term563 A B P f p g a)). Qed.
Lemma lem8242360 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term574 A B P lt2 s f p g a) = (term567 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8242358 A B P lt2 s a f g) (@lem8242359 A B P f p g a)). Qed.
Lemma lem8242361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242362 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term577 A B P lt2 s f p g a) = (term578 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8242361) (@lem8242360 A B P lt2 s f p g a)). Qed.
Lemma lem8242363 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term436 A B P lt2 s a f g z) = (term406 A B P lt2 s a f g z).
Proof. exact (eq_refl (term436 A B P lt2 s a f g z)). Qed.
Lemma lem8242364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242365 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term579 A B P lt2 s a f g z) = (term580 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8242364) (@lem8242363 A B P lt2 s a f g z)). Qed.
Lemma lem8242366 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term563 A B P f p g a) = (term563 A B P f p g a).
Proof. exact (eq_refl (term563 A B P f p g a)). Qed.
Lemma lem8242367 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term581 A B P lt2 s z f p g a) = (term582 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8242365 A B P lt2 s a f g z) (@lem8242366 A B P f p g a)). Qed.
Lemma lem8242368 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term583 A B P lt2 s f p g a) = (term584 A B P lt2 s f p g a).
Proof. exact (fun_ext (fun z : A => @lem8242367 A B P lt2 s z f p g a)). Qed.
Lemma lem8242369 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8242370 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term575 A B P lt2 s f p g a) = (term585 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8242369 A) (@lem8242368 A B P lt2 s f p g a)). Qed.
Lemma lem8242371 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : ((term574 A B P lt2 s f p g a) = (term575 A B P lt2 s f p g a)) = ((term567 A B P lt2 s f p g a) = (term585 A B P lt2 s f p g a)).
Proof. exact (MK_COMB (@lem8242362 A B P lt2 s f p g a) (@lem8242370 A B P lt2 s f p g a)). Qed.
Lemma lem8242372 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term567 A B P lt2 s f p g a) = (term585 A B P lt2 s f p g a).
Proof. exact (EQ_MP (@lem8242371 A B P lt2 s f p g a) (@lem8242352 A B P lt2 s f p g a)). Qed.
Lemma lem8242373 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term568 A B P lt2 s f p g) = (term586 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8242372 A B P lt2 s f p g a)). Qed.
Lemma lem8242374 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8242375 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term569 A B P lt2 s f p g) = (term587 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242374 P) (@lem8242373 A B P lt2 s f p g)). Qed.
Lemma lem8242377 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8242378 {A P : Type'} (P' : type1470 A P) : (term482 A P P') = (term483 A P P').
Proof. exact (@lem8242377 P A P'). Qed.
Lemma lem8242379 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term588 A B P lt2 s f p g) = (term589 A B P lt2 s f p g).
Proof. exact (@lem8242378 A P (term590 A B P lt2 s f p g)). Qed.
Lemma lem8242380 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term591 A B P lt2 s f p g a) = (term584 A B P lt2 s f p g a).
Proof. exact (eq_refl (term591 A B P lt2 s f p g a)). Qed.
Lemma lem8242381 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8242382 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (z : A) : (term592 A B P lt2 s f p g a z) = (term593 A B P lt2 s f p g a z).
Proof. exact (MK_COMB (@lem8242380 A B P lt2 s f p g a) (@lem8242381 A z)). Qed.
Lemma lem8242383 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term593 A B P lt2 s f p g a z) = (term582 A B P lt2 s z f p g a).
Proof. exact (eq_refl (term593 A B P lt2 s f p g a z)). Qed.
Lemma lem8242384 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term592 A B P lt2 s f p g a z) = (term582 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8242382 A B P lt2 s f p g a z) (@lem8242383 A B P lt2 s z f p g a)). Qed.
Lemma lem8242385 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term594 A B P lt2 s f p g a) = (term584 A B P lt2 s f p g a).
Proof. exact (fun_ext (fun z : A => @lem8242384 A B P lt2 s z f p g a)). Qed.
Lemma lem8242386 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8242387 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term595 A B P lt2 s f p g a) = (term585 A B P lt2 s f p g a).
Proof. exact (MK_COMB (@lem8242386 A) (@lem8242385 A B P lt2 s f p g a)). Qed.
Lemma lem8242388 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term596 A B P lt2 s f p g) = (term586 A B P lt2 s f p g).
Proof. exact (fun_ext (fun a : P => @lem8242387 A B P lt2 s f p g a)). Qed.
Lemma lem8242389 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8242390 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term588 A B P lt2 s f p g) = (term587 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242389 P) (@lem8242388 A B P lt2 s f p g)). Qed.
Lemma lem8242391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242392 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term597 A B P lt2 s f p g) = (term598 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242391) (@lem8242390 A B P lt2 s f p g)). Qed.
Lemma lem8242393 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term591 A B P lt2 s f p g a) = (term584 A B P lt2 s f p g a).
Proof. exact (eq_refl (term591 A B P lt2 s f p g a)). Qed.
Lemma lem8242394 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8242395 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (z : P -> A) (a : P) : (term599 A B P lt2 s f p g z a) = (term600 A B P lt2 s f p g z a).
Proof. exact (MK_COMB (@lem8242393 A B P lt2 s f p g a) (@lem8242394 A P z a)). Qed.
Lemma lem8242396 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term600 A B P lt2 s f p g z a) = (term601 A B P lt2 s z f p g a).
Proof. exact (eq_refl (term600 A B P lt2 s f p g z a)). Qed.
Lemma lem8242397 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term599 A B P lt2 s f p g z a) = (term601 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8242395 A B P lt2 s f p g z a) (@lem8242396 A B P lt2 s z f p g a)). Qed.
Lemma lem8242398 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term602 A B P lt2 s f p g z) = (term603 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8242397 A B P lt2 s z f p g a)). Qed.
Lemma lem8242399 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8242400 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term604 A B P lt2 s f p g z) = (term605 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8242399 P) (@lem8242398 A B P lt2 s z f p g)). Qed.
Lemma lem8242401 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term606 A B P lt2 s f p g) = (term607 A B P lt2 s f p g).
Proof. exact (fun_ext (fun z : P -> A => @lem8242400 A B P lt2 s z f p g)). Qed.
Lemma lem8242402 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8242403 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term589 A B P lt2 s f p g) = (term608 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242402 A P) (@lem8242401 A B P lt2 s f p g)). Qed.
Lemma lem8242404 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : ((term588 A B P lt2 s f p g) = (term589 A B P lt2 s f p g)) = ((term587 A B P lt2 s f p g) = (term608 A B P lt2 s f p g)).
Proof. exact (MK_COMB (@lem8242392 A B P lt2 s f p g) (@lem8242403 A B P lt2 s f p g)). Qed.
Lemma lem8242405 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term587 A B P lt2 s f p g) = (term608 A B P lt2 s f p g).
Proof. exact (EQ_MP (@lem8242404 A B P lt2 s f p g) (@lem8242379 A B P lt2 s f p g)). Qed.
Lemma lem8242406 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term569 A B P lt2 s f p g) = (term608 A B P lt2 s f p g).
Proof. exact (TRANS (@lem8242375 A B P lt2 s f p g) (@lem8242405 A B P lt2 s f p g)). Qed.
Lemma lem8242407 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term570 A B P lt2 s f p) = (term609 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8242406 A B P lt2 s f p g)). Qed.
Lemma lem8242408 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242409 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term571 A B P lt2 s f p) = (term610 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242408 A B) (@lem8242407 A B P lt2 s f p)). Qed.
Lemma lem8242411 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8242412 {A B P : Type'} (P' : type537 A B P) : (term507 A B P P') = (term508 A B P P').
Proof. exact (@lem8242411 (A -> B) (P -> A) P'). Qed.
Lemma lem8242413 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term611 A B P lt2 s f p) = (term612 A B P lt2 s f p).
Proof. exact (@lem8242412 A B P (term613 A B P lt2 s f p)). Qed.
Lemma lem8242414 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term614 A B P lt2 s f p g) = (term607 A B P lt2 s f p g).
Proof. exact (eq_refl (term614 A B P lt2 s f p g)). Qed.
Lemma lem8242415 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8242416 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) (z : P -> A) : (term615 A B P lt2 s f p g z) = (term616 A B P lt2 s f p g z).
Proof. exact (MK_COMB (@lem8242414 A B P lt2 s f p g) (@lem8242415 A P z)). Qed.
Lemma lem8242417 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term616 A B P lt2 s f p g z) = (term605 A B P lt2 s z f p g).
Proof. exact (eq_refl (term616 A B P lt2 s f p g z)). Qed.
Lemma lem8242418 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term615 A B P lt2 s f p g z) = (term605 A B P lt2 s z f p g).
Proof. exact (TRANS (@lem8242416 A B P lt2 s f p g z) (@lem8242417 A B P lt2 s z f p g)). Qed.
Lemma lem8242419 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term617 A B P lt2 s f p g) = (term607 A B P lt2 s f p g).
Proof. exact (fun_ext (fun z : P -> A => @lem8242418 A B P lt2 s z f p g)). Qed.
Lemma lem8242420 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8242421 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term618 A B P lt2 s f p g) = (term608 A B P lt2 s f p g).
Proof. exact (MK_COMB (@lem8242420 A P) (@lem8242419 A B P lt2 s f p g)). Qed.
Lemma lem8242422 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term619 A B P lt2 s f p) = (term609 A B P lt2 s f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8242421 A B P lt2 s f p g)). Qed.
Lemma lem8242423 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242424 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term611 A B P lt2 s f p) = (term610 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242423 A B) (@lem8242422 A B P lt2 s f p)). Qed.
Lemma lem8242425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242426 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term620 A B P lt2 s f p) = (term621 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242425) (@lem8242424 A B P lt2 s f p)). Qed.
Lemma lem8242427 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term614 A B P lt2 s f p g) = (term607 A B P lt2 s f p g).
Proof. exact (eq_refl (term614 A B P lt2 s f p g)). Qed.
Lemma lem8242428 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8242429 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (z : type557 A B P) (g : A -> B) : (term622 A B P lt2 s f p z g) = (term623 A B P lt2 s f p z g).
Proof. exact (MK_COMB (@lem8242427 A B P lt2 s f p g) (@lem8242428 A B P z g)). Qed.
Lemma lem8242430 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term623 A B P lt2 s f p z g) = (term624 A B P lt2 s z f p g).
Proof. exact (eq_refl (term623 A B P lt2 s f p z g)). Qed.
Lemma lem8242431 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term622 A B P lt2 s f p z g) = (term624 A B P lt2 s z f p g).
Proof. exact (TRANS (@lem8242429 A B P lt2 s f p z g) (@lem8242430 A B P lt2 s z f p g)). Qed.
Lemma lem8242432 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term625 A B P lt2 s f p z) = (term626 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8242431 A B P lt2 s z f p g)). Qed.
Lemma lem8242433 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242434 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term627 A B P lt2 s f p z) = (term628 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8242433 A B) (@lem8242432 A B P lt2 s z f p)). Qed.
Lemma lem8242435 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term629 A B P lt2 s f p) = (term630 A B P lt2 s f p).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8242434 A B P lt2 s z f p)). Qed.
Lemma lem8242436 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8242437 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term612 A B P lt2 s f p) = (term631 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242436 A B P) (@lem8242435 A B P lt2 s f p)). Qed.
Lemma lem8242438 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : ((term611 A B P lt2 s f p) = (term612 A B P lt2 s f p)) = ((term610 A B P lt2 s f p) = (term631 A B P lt2 s f p)).
Proof. exact (MK_COMB (@lem8242426 A B P lt2 s f p) (@lem8242437 A B P lt2 s f p)). Qed.
Lemma lem8242439 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term610 A B P lt2 s f p) = (term631 A B P lt2 s f p).
Proof. exact (EQ_MP (@lem8242438 A B P lt2 s f p) (@lem8242413 A B P lt2 s f p)). Qed.
Lemma lem8242440 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term571 A B P lt2 s f p) = (term631 A B P lt2 s f p).
Proof. exact (TRANS (@lem8242409 A B P lt2 s f p) (@lem8242439 A B P lt2 s f p)). Qed.
Lemma lem8242441 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term572 A B P lt2 s p) = (term632 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8242440 A B P lt2 s f p)). Qed.
Lemma lem8242442 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242443 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term573 A B P lt2 s p) = (term633 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8242442 A B) (@lem8242441 A B P lt2 s p)). Qed.
Lemma lem8242445 {A B : Type'} (P : type1413 A B) : (term480 A B P) = (term481 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8242446 {A B P : Type'} (P' : type495 A B P) : (term532 A B P P') = (term533 A B P P').
Proof. exact (@lem8242445 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8242447 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term634 A B P lt2 s p) = (term635 A B P lt2 s p).
Proof. exact (@lem8242446 A B P (term636 A B P lt2 s p)). Qed.
Lemma lem8242448 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term637 A B P lt2 s p f) = (term630 A B P lt2 s f p).
Proof. exact (eq_refl (term637 A B P lt2 s p f)). Qed.
Lemma lem8242449 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8242450 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) (z : type557 A B P) : (term638 A B P lt2 s p f z) = (term639 A B P lt2 s f p z).
Proof. exact (MK_COMB (@lem8242448 A B P lt2 s f p) (@lem8242449 A B P z)). Qed.
Lemma lem8242451 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term639 A B P lt2 s f p z) = (term628 A B P lt2 s z f p).
Proof. exact (eq_refl (term639 A B P lt2 s f p z)). Qed.
Lemma lem8242452 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (p : type560 A B P) : (term638 A B P lt2 s p f z) = (term628 A B P lt2 s z f p).
Proof. exact (TRANS (@lem8242450 A B P lt2 s f p z) (@lem8242451 A B P lt2 s z f p)). Qed.
Lemma lem8242453 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term640 A B P lt2 s p f) = (term630 A B P lt2 s f p).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8242452 A B P lt2 s z f p)). Qed.
Lemma lem8242454 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8242455 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term641 A B P lt2 s p f) = (term631 A B P lt2 s f p).
Proof. exact (MK_COMB (@lem8242454 A B P) (@lem8242453 A B P lt2 s f p)). Qed.
Lemma lem8242456 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term642 A B P lt2 s p) = (term632 A B P lt2 s p).
Proof. exact (fun_ext (fun f : A -> B => @lem8242455 A B P lt2 s f p)). Qed.
Lemma lem8242457 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242458 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term634 A B P lt2 s p) = (term633 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8242457 A B) (@lem8242456 A B P lt2 s p)). Qed.
Lemma lem8242459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242460 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term643 A B P lt2 s p) = (term644 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8242459) (@lem8242458 A B P lt2 s p)). Qed.
Lemma lem8242461 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (p : type560 A B P) : (term637 A B P lt2 s p f) = (term630 A B P lt2 s f p).
Proof. exact (eq_refl (term637 A B P lt2 s p f)). Qed.
Lemma lem8242462 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8242463 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) : (term645 A B P lt2 s p z f) = (term646 A B P lt2 s p z f).
Proof. exact (MK_COMB (@lem8242461 A B P lt2 s f p) (@lem8242462 A B P z f)). Qed.
Lemma lem8242464 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term646 A B P lt2 s p z f) = (term647 A B P lt2 s z f p).
Proof. exact (eq_refl (term646 A B P lt2 s p z f)). Qed.
Lemma lem8242465 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term645 A B P lt2 s p z f) = (term647 A B P lt2 s z f p).
Proof. exact (TRANS (@lem8242463 A B P lt2 s p z f) (@lem8242464 A B P lt2 s z f p)). Qed.
Lemma lem8242466 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term648 A B P lt2 s p z) = (term649 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8242465 A B P lt2 s z f p)). Qed.
Lemma lem8242467 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8242468 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term650 A B P lt2 s p z) = (term651 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8242467 A B) (@lem8242466 A B P lt2 s z p)). Qed.
Lemma lem8242469 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term652 A B P lt2 s p) = (term653 A B P lt2 s p).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8242468 A B P lt2 s z p)). Qed.
Lemma lem8242470 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8242471 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term635 A B P lt2 s p) = (term654 A B P lt2 s p).
Proof. exact (MK_COMB (@lem8242470 A B P) (@lem8242469 A B P lt2 s p)). Qed.
Lemma lem8242472 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : ((term634 A B P lt2 s p) = (term635 A B P lt2 s p)) = ((term633 A B P lt2 s p) = (term654 A B P lt2 s p)).
Proof. exact (MK_COMB (@lem8242460 A B P lt2 s p) (@lem8242471 A B P lt2 s p)). Qed.
Lemma lem8242473 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term633 A B P lt2 s p) = (term654 A B P lt2 s p).
Proof. exact (EQ_MP (@lem8242472 A B P lt2 s p) (@lem8242447 A B P lt2 s p)). Qed.
Lemma lem8242475 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term573 A B P lt2 s p) = (term654 A B P lt2 s p).
Proof. exact (TRANS (@lem8242443 A B P lt2 s p) (@lem8242473 A B P lt2 s p)). Qed.
Lemma lem8242476 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : (term80 A B P lt2 s p) = (term654 A B P lt2 s p).
Proof. exact (TRANS (@lem8242243 A B P lt2 s p) (@lem8242475 A B P lt2 s p)). Qed.
Lemma lem8242477 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (h1 : term80 A B P lt2 s p) : term654 A B P lt2 s p.
Proof. exact (EQ_MP (@lem8242476 A B P lt2 s p) (@lem8241739 A B P lt2 s p h1)). Qed.
Lemma lem8242480 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term655 A B P p f a) = (p f a).
Proof. exact (@lem16933 (p f a)). Qed.
Lemma lem8242487 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term656 A B P t f lt2 y s a) = (term657 A B P t f lt2 y s a).
Proof. exact (@lem17362 (term345 A B P lt2 y t f a) (term171 A P lt2 y s a)). Qed.
Lemma lem8242488 {A : Type'} (P : A -> Prop) : (term407 A P) = (term408 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8242489 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term658 A B P t f lt2 s a) = (term659 A B P t f lt2 s a).
Proof. exact (@lem8242488 A (term348 A B P t f lt2 s a)). Qed.
Lemma lem8242490 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term660 A B P t f lt2 s a y) = (term347 A B P t f lt2 y s a).
Proof. exact (eq_refl (term660 A B P t f lt2 s a y)). Qed.
Lemma lem8242491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242492 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term661 A B P t f lt2 s a y) = (term656 A B P t f lt2 y s a).
Proof. exact (MK_COMB (@lem8242491) (@lem8242490 A B P t f lt2 y s a)). Qed.
Lemma lem8242493 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term661 A B P t f lt2 s a y) = (term657 A B P t f lt2 y s a).
Proof. exact (TRANS (@lem8242492 A B P t f lt2 y s a) (@lem8242487 A B P t f lt2 y s a)). Qed.
Lemma lem8242494 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term662 A B P t f lt2 s a) = (term663 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8242493 A B P t f lt2 y s a)). Qed.
Lemma lem8242495 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8242496 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term659 A B P t f lt2 s a) = (term664 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8242495 A) (@lem8242494 A B P t f lt2 s a)). Qed.
Lemma lem8242497 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term658 A B P t f lt2 s a) = (term664 A B P t f lt2 s a).
Proof. exact (TRANS (@lem8242489 A B P t f lt2 s a) (@lem8242496 A B P t f lt2 s a)). Qed.
Lemma lem8242498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242499 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term665 A B P p f a) = (term370 A B P p f a).
Proof. exact (MK_COMB (@lem8242498) (@lem8242480 A B P p f a)). Qed.
Lemma lem8242500 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term666 A B P p t f lt2 s a) = (term667 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8242499 A B P p f a) (@lem8242497 A B P t f lt2 s a)). Qed.
Lemma lem8242501 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term668 A B P p t f lt2 s a) = (term666 A B P p t f lt2 s a).
Proof. exact (@lem17160 (term292 A B P p f a) (term349 A B P t f lt2 s a)). Qed.
Lemma lem8242502 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term668 A B P p t f lt2 s a) = (term667 A B P p t f lt2 s a).
Proof. exact (TRANS (@lem8242501 A B P p t f lt2 s a) (@lem8242500 A B P p t f lt2 s a)). Qed.
Lemma lem8242503 {P : Type'} (P' : P -> Prop) : (term407 P P') = (term408 P P').
Proof. exact (@lem18392 P P'). Qed.
Lemma lem8242504 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term669 A B P p t f lt2 s) = (term670 A B P p t f lt2 s).
Proof. exact (@lem8242503 P (term358 A B P p t f lt2 s)). Qed.
Lemma lem8242505 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term671 A B P p t f lt2 s a) = (term356 A B P p t f lt2 s a).
Proof. exact (eq_refl (term671 A B P p t f lt2 s a)). Qed.
Lemma lem8242506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242507 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term672 A B P p t f lt2 s a) = (term668 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8242506) (@lem8242505 A B P p t f lt2 s a)). Qed.
Lemma lem8242508 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term672 A B P p t f lt2 s a) = (term667 A B P p t f lt2 s a).
Proof. exact (TRANS (@lem8242507 A B P p t f lt2 s a) (@lem8242502 A B P p t f lt2 s a)). Qed.
Lemma lem8242509 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term673 A B P p t f lt2 s) = (term674 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8242508 A B P p t f lt2 s a)). Qed.
Lemma lem8242510 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8242511 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term670 A B P p t f lt2 s) = (term675 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8242510 P) (@lem8242509 A B P p t f lt2 s)). Qed.
Lemma lem8242512 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term669 A B P p t f lt2 s) = (term675 A B P p t f lt2 s).
Proof. exact (TRANS (@lem8242504 A B P p t f lt2 s) (@lem8242511 A B P p t f lt2 s)). Qed.
Lemma lem8242513 {A B : Type'} (P : type572 A B) : (term676 A B P) = (term677 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem8242514 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term678 A B P p t lt2 s) = (term679 A B P p t lt2 s).
Proof. exact (@lem8242513 A B (term360 A B P p t lt2 s)). Qed.
Lemma lem8242515 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term680 A B P p t lt2 s f) = (term359 A B P p t f lt2 s).
Proof. exact (eq_refl (term680 A B P p t lt2 s f)). Qed.
Lemma lem8242516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242517 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term681 A B P p t lt2 s f) = (term669 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8242516) (@lem8242515 A B P p t f lt2 s)). Qed.
Lemma lem8242518 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term681 A B P p t lt2 s f) = (term675 A B P p t f lt2 s).
Proof. exact (TRANS (@lem8242517 A B P p t f lt2 s) (@lem8242512 A B P p t f lt2 s)). Qed.
Lemma lem8242519 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term682 A B P p t lt2 s) = (term683 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8242518 A B P p t f lt2 s)). Qed.
Lemma lem8242520 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8242521 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term679 A B P p t lt2 s) = (term684 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8242520 A B) (@lem8242519 A B P p t lt2 s)). Qed.
Lemma lem8242522 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term678 A B P p t lt2 s) = (term684 A B P p t lt2 s).
Proof. exact (TRANS (@lem8242514 A B P p t lt2 s) (@lem8242521 A B P p t lt2 s)). Qed.
Lemma lem8242525 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term655 A B P p g a) = (p g a).
Proof. exact (@lem16933 (p g a)). Qed.
Lemma lem8242528 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term655 A B P p f a) = (p f a).
Proof. exact (@lem16933 (p f a)). Qed.
Lemma lem8242535 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term685 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term171 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8242536 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term686 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8242535 A B P lt2 s a f g z)). Qed.
Lemma lem8242537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8242538 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term687 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242537 A) (@lem8242536 A B P lt2 s a f g)). Qed.
Lemma lem8242539 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term688 A B P f t g a) = (term688 A B P f t g a).
Proof. exact (eq_refl (term688 A B P f t g a)). Qed.
Lemma lem8242540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242541 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term689 A B P lt2 s a f g) = (term690 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242540) (@lem8242538 A B P lt2 s a f g)). Qed.
Lemma lem8242542 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term691 A B P lt2 s f t g a) = (term692 A B P lt2 s f t g a).
Proof. exact (MK_COMB (@lem8242541 A B P lt2 s a f g) (@lem8242539 A B P f t g a)). Qed.
Lemma lem8242543 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term693 A B P lt2 s f t g a) = (term691 A B P lt2 s f t g a).
Proof. exact (@lem17362 (term62 A B P lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8242544 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term693 A B P lt2 s f t g a) = (term692 A B P lt2 s f t g a).
Proof. exact (TRANS (@lem8242543 A B P lt2 s f t g a) (@lem8242542 A B P lt2 s f t g a)). Qed.
Lemma lem8242545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242546 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term665 A B P p f a) = (term370 A B P p f a).
Proof. exact (MK_COMB (@lem8242545) (@lem8242528 A B P p f a)). Qed.
Lemma lem8242547 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term694 A B P p lt2 s f t g a) = (term695 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8242546 A B P p f a) (@lem8242544 A B P lt2 s f t g a)). Qed.
Lemma lem8242548 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term696 A B P p lt2 s f t g a) = (term694 A B P p lt2 s f t g a).
Proof. exact (@lem17160 (term292 A B P p f a) (term316 A B P lt2 s f t g a)). Qed.
Lemma lem8242549 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term696 A B P p lt2 s f t g a) = (term695 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8242548 A B P p lt2 s f t g a) (@lem8242547 A B P p lt2 s f t g a)). Qed.
Lemma lem8242557 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term685 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term171 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8242558 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term686 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8242557 A B P lt2 s a f g z)). Qed.
Lemma lem8242559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8242560 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term687 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242559 A) (@lem8242558 A B P lt2 s a f g)). Qed.
Lemma lem8242561 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term697 A B P s t g a) = (term697 A B P s t g a).
Proof. exact (eq_refl (term697 A B P s t g a)). Qed.
Lemma lem8242562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242563 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term689 A B P lt2 s a f g) = (term690 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242562) (@lem8242560 A B P lt2 s a f g)). Qed.
Lemma lem8242564 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term698 A B P lt2 f s t g a) = (term699 A B P lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242563 A B P lt2 s a f g) (@lem8242561 A B P s t g a)). Qed.
Lemma lem8242565 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term700 A B P lt2 f s t g a) = (term698 A B P lt2 f s t g a).
Proof. exact (@lem17362 (term62 A B P lt2 s a f g) ((s a) = (t g a))). Qed.
Lemma lem8242566 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term700 A B P lt2 f s t g a) = (term699 A B P lt2 f s t g a).
Proof. exact (TRANS (@lem8242565 A B P lt2 f s t g a) (@lem8242564 A B P lt2 f s t g a)). Qed.
Lemma lem8242568 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term701 A B P p f a) = (term701 A B P p f a).
Proof. exact (eq_refl (term701 A B P p f a)). Qed.
Lemma lem8242569 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term702 A B P p lt2 f s t g a) = (term703 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242568 A B P p f a) (@lem8242566 A B P lt2 f s t g a)). Qed.
Lemma lem8242570 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term704 A B P p lt2 f s t g a) = (term702 A B P p lt2 f s t g a).
Proof. exact (@lem17160 (p f a) (term319 A B P lt2 f s t g a)). Qed.
Lemma lem8242571 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term704 A B P p lt2 f s t g a) = (term703 A B P p lt2 f s t g a).
Proof. exact (TRANS (@lem8242570 A B P p lt2 f s t g a) (@lem8242569 A B P p lt2 f s t g a)). Qed.
Lemma lem8242572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242573 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term705 A B P p lt2 s f t g a) = (term706 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8242572) (@lem8242549 A B P p lt2 s f t g a)). Qed.
Lemma lem8242574 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term707 A B P p lt2 f s t g a) = (term708 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242573 A B P p lt2 s f t g a) (@lem8242571 A B P p lt2 f s t g a)). Qed.
Lemma lem8242575 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term709 A B P p lt2 f s t g a) = (term707 A B P p lt2 f s t g a).
Proof. exact (@lem17045 (term317 A B P p lt2 s f t g a) (term320 A B P p lt2 f s t g a)). Qed.
Lemma lem8242576 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term709 A B P p lt2 f s t g a) = (term708 A B P p lt2 f s t g a).
Proof. exact (TRANS (@lem8242575 A B P p lt2 f s t g a) (@lem8242574 A B P p lt2 f s t g a)). Qed.
Lemma lem8242577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242578 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term665 A B P p g a) = (term370 A B P p g a).
Proof. exact (MK_COMB (@lem8242577) (@lem8242525 A B P p g a)). Qed.
Lemma lem8242579 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term710 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242578 A B P p g a) (@lem8242576 A B P p lt2 f s t g a)). Qed.
Lemma lem8242580 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term712 A B P p lt2 f s t g a) = (term710 A B P p lt2 f s t g a).
Proof. exact (@lem17160 (term292 A B P p g a) (term321 A B P p lt2 f s t g a)). Qed.
Lemma lem8242581 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term712 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (TRANS (@lem8242580 A B P p lt2 f s t g a) (@lem8242579 A B P p lt2 f s t g a)). Qed.
Lemma lem8242585 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term655 A B P p f a) = (p f a).
Proof. exact (@lem16933 (p f a)). Qed.
Lemma lem8242592 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term326 A B P lt2 s a f g z) = (term685 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term171 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8242593 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term327 A B P lt2 s a f g) = (term686 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8242592 A B P lt2 s a f g z)). Qed.
Lemma lem8242594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8242595 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term62 A B P lt2 s a f g) = (term687 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242594 A) (@lem8242593 A B P lt2 s a f g)). Qed.
Lemma lem8242596 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term713 A B P t f s a) = (term713 A B P t f s a).
Proof. exact (eq_refl (term713 A B P t f s a)). Qed.
Lemma lem8242597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242598 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term689 A B P lt2 s a f g) = (term690 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8242597) (@lem8242595 A B P lt2 s a f g)). Qed.
Lemma lem8242599 {A B P : Type'} (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term714 A B P lt2 g t f s a) = (term715 A B P lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242598 A B P lt2 s a f g) (@lem8242596 A B P t f s a)). Qed.
Lemma lem8242600 {A B P : Type'} (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term716 A B P lt2 g t f s a) = (term714 A B P lt2 g t f s a).
Proof. exact (@lem17362 (term62 A B P lt2 s a f g) ((t f a) = (s a))). Qed.
Lemma lem8242601 {A B P : Type'} (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term716 A B P lt2 g t f s a) = (term715 A B P lt2 g t f s a).
Proof. exact (TRANS (@lem8242600 A B P lt2 g t f s a) (@lem8242599 A B P lt2 g t f s a)). Qed.
Lemma lem8242602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8242603 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term665 A B P p f a) = (term370 A B P p f a).
Proof. exact (MK_COMB (@lem8242602) (@lem8242585 A B P p f a)). Qed.
Lemma lem8242604 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term717 A B P p lt2 g t f s a) = (term718 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242603 A B P p f a) (@lem8242601 A B P lt2 g t f s a)). Qed.
Lemma lem8242605 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term719 A B P p lt2 g t f s a) = (term717 A B P p lt2 g t f s a).
Proof. exact (@lem17160 (term292 A B P p f a) (term305 A B P lt2 g t f s a)). Qed.
Lemma lem8242606 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term719 A B P p lt2 g t f s a) = (term718 A B P p lt2 g t f s a).
Proof. exact (TRANS (@lem8242605 A B P p lt2 g t f s a) (@lem8242604 A B P p lt2 g t f s a)). Qed.
Lemma lem8242608 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term701 A B P p g a) = (term701 A B P p g a).
Proof. exact (eq_refl (term701 A B P p g a)). Qed.
Lemma lem8242609 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term720 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242608 A B P p g a) (@lem8242606 A B P p lt2 g t f s a)). Qed.
Lemma lem8242610 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term722 A B P p lt2 g t f s a) = (term720 A B P p lt2 g t f s a).
Proof. exact (@lem17160 (p g a) (term308 A B P p lt2 g t f s a)). Qed.
Lemma lem8242611 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term722 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (TRANS (@lem8242610 A B P p lt2 g t f s a) (@lem8242609 A B P p lt2 g t f s a)). Qed.
Lemma lem8242612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242613 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term723 A B P p lt2 f s t g a) = (term724 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242612) (@lem8242581 A B P p lt2 f s t g a)). Qed.
Lemma lem8242614 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term725 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242613 A B P p lt2 f s t g a) (@lem8242611 A B P p lt2 g t f s a)). Qed.
Lemma lem8242615 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term727 A B P p lt2 g t f s a) = (term725 A B P p lt2 g t f s a).
Proof. exact (@lem17045 (term329 A B P p lt2 f s t g a) (term328 A B P p lt2 g t f s a)). Qed.
Lemma lem8242616 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term727 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (TRANS (@lem8242615 A B P p lt2 g t f s a) (@lem8242614 A B P p lt2 g t f s a)). Qed.
Lemma lem8242617 {P : Type'} (P' : P -> Prop) : (term407 P P') = (term408 P P').
Proof. exact (@lem18392 P P'). Qed.
Lemma lem8242618 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term728 A B P p lt2 g t f s) = (term729 A B P p lt2 g t f s).
Proof. exact (@lem8242617 P (term333 A B P p lt2 g t f s)). Qed.
Lemma lem8242619 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term730 A B P p lt2 g t f s a) = (term325 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term730 A B P p lt2 g t f s a)). Qed.
Lemma lem8242620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242621 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term731 A B P p lt2 g t f s a) = (term727 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242620) (@lem8242619 A B P p lt2 g t f s a)). Qed.
Lemma lem8242622 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term731 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (TRANS (@lem8242621 A B P p lt2 g t f s a) (@lem8242616 A B P p lt2 g t f s a)). Qed.
Lemma lem8242623 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term732 A B P p lt2 g t f s) = (term733 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8242622 A B P p lt2 g t f s a)). Qed.
Lemma lem8242624 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8242625 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term729 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242624 P) (@lem8242623 A B P p lt2 g t f s)). Qed.
Lemma lem8242626 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term728 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (TRANS (@lem8242618 A B P p lt2 g t f s) (@lem8242625 A B P p lt2 g t f s)). Qed.
Lemma lem8242627 {A B : Type'} (P : type572 A B) : (term676 A B P) = (term677 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem8242628 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term735 A B P p lt2 t f s) = (term736 A B P p lt2 t f s).
Proof. exact (@lem8242627 A B (term335 A B P p lt2 t f s)). Qed.
Lemma lem8242629 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term737 A B P p lt2 t f s g) = (term334 A B P p lt2 g t f s).
Proof. exact (eq_refl (term737 A B P p lt2 t f s g)). Qed.
Lemma lem8242630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242631 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term738 A B P p lt2 t f s g) = (term728 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242630) (@lem8242629 A B P p lt2 g t f s)). Qed.
Lemma lem8242632 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term738 A B P p lt2 t f s g) = (term734 A B P p lt2 g t f s).
Proof. exact (TRANS (@lem8242631 A B P p lt2 g t f s) (@lem8242626 A B P p lt2 g t f s)). Qed.
Lemma lem8242633 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term739 A B P p lt2 t f s) = (term740 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8242632 A B P p lt2 g t f s)). Qed.
Lemma lem8242634 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8242635 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term736 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8242634 A B) (@lem8242633 A B P p lt2 t f s)). Qed.
Lemma lem8242636 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term735 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (TRANS (@lem8242628 A B P p lt2 t f s) (@lem8242635 A B P p lt2 t f s)). Qed.
Lemma lem8242637 {A B : Type'} (P : type572 A B) : (term676 A B P) = (term677 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem8242638 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term742 A B P p lt2 t s) = (term743 A B P p lt2 t s).
Proof. exact (@lem8242637 A B (term337 A B P p lt2 t s)). Qed.
Lemma lem8242639 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term744 A B P p lt2 t s f) = (term336 A B P p lt2 t f s).
Proof. exact (eq_refl (term744 A B P p lt2 t s f)). Qed.
Lemma lem8242640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8242641 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term745 A B P p lt2 t s f) = (term735 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8242640) (@lem8242639 A B P p lt2 t f s)). Qed.
Lemma lem8242642 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term745 A B P p lt2 t s f) = (term741 A B P p lt2 t f s).
Proof. exact (TRANS (@lem8242641 A B P p lt2 t f s) (@lem8242636 A B P p lt2 t f s)). Qed.
Lemma lem8242643 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term746 A B P p lt2 t s) = (term747 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8242642 A B P p lt2 t f s)). Qed.
Lemma lem8242644 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8242645 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term743 A B P p lt2 t s) = (term748 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8242644 A B) (@lem8242643 A B P p lt2 t s)). Qed.
Lemma lem8242646 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term742 A B P p lt2 t s) = (term748 A B P p lt2 t s).
Proof. exact (TRANS (@lem8242638 A B P p lt2 t s) (@lem8242645 A B P p lt2 t s)). Qed.
Lemma lem8242647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242648 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term749 A B P p t lt2 s) = (term750 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8242647) (@lem8242522 A B P p t lt2 s)). Qed.
Lemma lem8242649 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term751 A B P p lt2 t s) = (term752 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8242648 A B P p t lt2 s) (@lem8242646 A B P p lt2 t s)). Qed.
Lemma lem8242650 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term404 A B P p lt2 t s) = (term751 A B P p lt2 t s).
Proof. exact (@lem17045 (term361 A B P p t lt2 s) (term338 A B P p lt2 t s)). Qed.
Lemma lem8242651 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term404 A B P p lt2 t s) = (term752 A B P p lt2 t s).
Proof. exact (TRANS (@lem8242650 A B P p lt2 t s) (@lem8242649 A B P p lt2 t s)). Qed.
Lemma lem8242761 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term753 A P Q) = (term754 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem8242762 {P : Type'} (P' : P -> Prop) (Q : P -> Prop) : (term753 P P' Q) = (term754 P P' Q).
Proof. exact (@lem8242761 P P' Q). Qed.
Lemma lem8242763 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term755 A B P p lt2 g t f s) = (term756 A B P p lt2 g t f s).
Proof. exact (@lem8242762 P (term757 A B P p lt2 f s t g) (term758 A B P p lt2 g t f s)). Qed.
Lemma lem8242764 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term759 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (eq_refl (term759 A B P p lt2 f s t g a)). Qed.
Lemma lem8242765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242766 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term760 A B P p lt2 f s t g a) = (term724 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8242765) (@lem8242764 A B P p lt2 f s t g a)). Qed.
Lemma lem8242767 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term761 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term761 A B P p lt2 g t f s a)). Qed.
Lemma lem8242768 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term762 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8242766 A B P p lt2 f s t g a) (@lem8242767 A B P p lt2 g t f s a)). Qed.
Lemma lem8242769 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term763 A B P p lt2 g t f s) = (term733 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8242768 A B P p lt2 g t f s a)). Qed.
Lemma lem8242770 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8242771 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term755 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242770 P) (@lem8242769 A B P p lt2 g t f s)). Qed.
Lemma lem8242772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8242773 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term764 A B P p lt2 g t f s) = (term765 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242772) (@lem8242771 A B P p lt2 g t f s)). Qed.
Lemma lem8242774 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term759 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (eq_refl (term759 A B P p lt2 f s t g a)). Qed.
Lemma lem8242775 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term766 A B P p lt2 f s t g) = (term757 A B P p lt2 f s t g).
Proof. exact (fun_ext (fun a : P => @lem8242774 A B P p lt2 f s t g a)). Qed.
Lemma lem8242776 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8242777 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term767 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8242776 P) (@lem8242775 A B P p lt2 f s t g)). Qed.
Lemma lem8242778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8242779 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term769 A B P p lt2 f s t g) = (term770 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8242778) (@lem8242777 A B P p lt2 f s t g)). Qed.
Lemma lem8242780 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term761 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term761 A B P p lt2 g t f s a)). Qed.
Lemma lem8242781 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term771 A B P p lt2 g t f s) = (term758 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8242780 A B P p lt2 g t f s a)). Qed.
Lemma lem8242782 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8242783 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term772 A B P p lt2 g t f s) = (term773 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242782 P) (@lem8242781 A B P p lt2 g t f s)). Qed.
Lemma lem8242784 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term756 A B P p lt2 g t f s) = (term774 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8242779 A B P p lt2 f s t g) (@lem8242783 A B P p lt2 g t f s)). Qed.
Lemma lem8242785 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term755 A B P p lt2 g t f s) = (term756 A B P p lt2 g t f s)) = ((term734 A B P p lt2 g t f s) = (term774 A B P p lt2 g t f s)).
Proof. exact (MK_COMB (@lem8242773 A B P p lt2 g t f s) (@lem8242784 A B P p lt2 g t f s)). Qed.
Lemma lem8242786 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term734 A B P p lt2 g t f s) = (term774 A B P p lt2 g t f s).
Proof. exact (EQ_MP (@lem8242785 A B P p lt2 g t f s) (@lem8242763 A B P p lt2 g t f s)). Qed.
Lemma lem8243027 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term740 A B P p lt2 t f s) = (term775 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8242786 A B P p lt2 g t f s)). Qed.
Lemma lem8243028 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243029 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term776 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243028 A B) (@lem8243027 A B P p lt2 t f s)). Qed.
Lemma lem8243031 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term753 A P Q) = (term754 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem8243032 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term777 A B P Q) = (term778 A B P Q).
Proof. exact (@lem8243031 (A -> B) P Q). Qed.
Lemma lem8243033 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term779 A B P p lt2 t f s) = (term780 A B P p lt2 t f s).
Proof. exact (@lem8243032 A B (term781 A B P p lt2 f s t) (term782 A B P p lt2 t f s)). Qed.
Lemma lem8243034 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term783 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (eq_refl (term783 A B P p lt2 f s t g)). Qed.
Lemma lem8243035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243036 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term784 A B P p lt2 f s t g) = (term770 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8243035) (@lem8243034 A B P p lt2 f s t g)). Qed.
Lemma lem8243037 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term785 A B P p lt2 t f s g) = (term773 A B P p lt2 g t f s).
Proof. exact (eq_refl (term785 A B P p lt2 t f s g)). Qed.
Lemma lem8243038 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term786 A B P p lt2 t f s g) = (term774 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243036 A B P p lt2 f s t g) (@lem8243037 A B P p lt2 g t f s)). Qed.
Lemma lem8243039 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term787 A B P p lt2 t f s) = (term775 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243038 A B P p lt2 g t f s)). Qed.
Lemma lem8243040 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243041 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term779 A B P p lt2 t f s) = (term776 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243040 A B) (@lem8243039 A B P p lt2 t f s)). Qed.
Lemma lem8243042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243043 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term788 A B P p lt2 t f s) = (term789 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243042) (@lem8243041 A B P p lt2 t f s)). Qed.
Lemma lem8243044 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term783 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (eq_refl (term783 A B P p lt2 f s t g)). Qed.
Lemma lem8243045 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term790 A B P p lt2 f s t) = (term781 A B P p lt2 f s t).
Proof. exact (fun_ext (fun g : A -> B => @lem8243044 A B P p lt2 f s t g)). Qed.
Lemma lem8243046 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243047 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term791 A B P p lt2 f s t) = (term792 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243046 A B) (@lem8243045 A B P p lt2 f s t)). Qed.
Lemma lem8243048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243049 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term793 A B P p lt2 f s t) = (term794 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243048) (@lem8243047 A B P p lt2 f s t)). Qed.
Lemma lem8243050 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term785 A B P p lt2 t f s g) = (term773 A B P p lt2 g t f s).
Proof. exact (eq_refl (term785 A B P p lt2 t f s g)). Qed.
Lemma lem8243051 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term795 A B P p lt2 t f s) = (term782 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243050 A B P p lt2 g t f s)). Qed.
Lemma lem8243052 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243053 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term796 A B P p lt2 t f s) = (term797 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243052 A B) (@lem8243051 A B P p lt2 t f s)). Qed.
Lemma lem8243054 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term780 A B P p lt2 t f s) = (term798 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243049 A B P p lt2 f s t) (@lem8243053 A B P p lt2 t f s)). Qed.
Lemma lem8243055 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term779 A B P p lt2 t f s) = (term780 A B P p lt2 t f s)) = ((term776 A B P p lt2 t f s) = (term798 A B P p lt2 t f s)).
Proof. exact (MK_COMB (@lem8243043 A B P p lt2 t f s) (@lem8243054 A B P p lt2 t f s)). Qed.
Lemma lem8243056 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term776 A B P p lt2 t f s) = (term798 A B P p lt2 t f s).
Proof. exact (EQ_MP (@lem8243055 A B P p lt2 t f s) (@lem8243033 A B P p lt2 t f s)). Qed.
Lemma lem8243305 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term798 A B P p lt2 t f s).
Proof. exact (TRANS (@lem8243029 A B P p lt2 t f s) (@lem8243056 A B P p lt2 t f s)). Qed.
Lemma lem8243306 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term747 A B P p lt2 t s) = (term799 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243305 A B P p lt2 t f s)). Qed.
Lemma lem8243307 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243308 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term748 A B P p lt2 t s) = (term800 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243307 A B) (@lem8243306 A B P p lt2 t s)). Qed.
Lemma lem8243310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term753 A P Q) = (term754 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem8243311 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term777 A B P Q) = (term778 A B P Q).
Proof. exact (@lem8243310 (A -> B) P Q). Qed.
Lemma lem8243312 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term801 A B P p lt2 t s) = (term802 A B P p lt2 t s).
Proof. exact (@lem8243311 A B (term803 A B P p lt2 s t) (term804 A B P p lt2 t s)). Qed.
Lemma lem8243313 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term805 A B P p lt2 s t f) = (term792 A B P p lt2 f s t).
Proof. exact (eq_refl (term805 A B P p lt2 s t f)). Qed.
Lemma lem8243314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243315 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term806 A B P p lt2 s t f) = (term794 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243314) (@lem8243313 A B P p lt2 f s t)). Qed.
Lemma lem8243316 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term807 A B P p lt2 t s f) = (term797 A B P p lt2 t f s).
Proof. exact (eq_refl (term807 A B P p lt2 t s f)). Qed.
Lemma lem8243317 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term808 A B P p lt2 t s f) = (term798 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243315 A B P p lt2 f s t) (@lem8243316 A B P p lt2 t f s)). Qed.
Lemma lem8243318 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term809 A B P p lt2 t s) = (term799 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243317 A B P p lt2 t f s)). Qed.
Lemma lem8243319 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243320 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term801 A B P p lt2 t s) = (term800 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243319 A B) (@lem8243318 A B P p lt2 t s)). Qed.
Lemma lem8243321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243322 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term810 A B P p lt2 t s) = (term811 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243321) (@lem8243320 A B P p lt2 t s)). Qed.
Lemma lem8243323 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term805 A B P p lt2 s t f) = (term792 A B P p lt2 f s t).
Proof. exact (eq_refl (term805 A B P p lt2 s t f)). Qed.
Lemma lem8243324 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term812 A B P p lt2 s t) = (term803 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8243323 A B P p lt2 f s t)). Qed.
Lemma lem8243325 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243326 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term813 A B P p lt2 s t) = (term814 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8243325 A B) (@lem8243324 A B P p lt2 s t)). Qed.
Lemma lem8243327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243328 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term815 A B P p lt2 s t) = (term816 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8243327) (@lem8243326 A B P p lt2 s t)). Qed.
Lemma lem8243329 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term807 A B P p lt2 t s f) = (term797 A B P p lt2 t f s).
Proof. exact (eq_refl (term807 A B P p lt2 t s f)). Qed.
Lemma lem8243330 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term817 A B P p lt2 t s) = (term804 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243329 A B P p lt2 t f s)). Qed.
Lemma lem8243331 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243332 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term818 A B P p lt2 t s) = (term819 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243331 A B) (@lem8243330 A B P p lt2 t s)). Qed.
Lemma lem8243333 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term802 A B P p lt2 t s) = (term820 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243328 A B P p lt2 s t) (@lem8243332 A B P p lt2 t s)). Qed.
Lemma lem8243334 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : ((term801 A B P p lt2 t s) = (term802 A B P p lt2 t s)) = ((term800 A B P p lt2 t s) = (term820 A B P p lt2 t s)).
Proof. exact (MK_COMB (@lem8243322 A B P p lt2 t s) (@lem8243333 A B P p lt2 t s)). Qed.
Lemma lem8243335 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term800 A B P p lt2 t s) = (term820 A B P p lt2 t s).
Proof. exact (EQ_MP (@lem8243334 A B P p lt2 t s) (@lem8243312 A B P p lt2 t s)). Qed.
Lemma lem8243592 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term748 A B P p lt2 t s) = (term820 A B P p lt2 t s).
Proof. exact (TRANS (@lem8243308 A B P p lt2 t s) (@lem8243335 A B P p lt2 t s)). Qed.
Lemma lem8243593 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term750 A B P p t lt2 s) = (term750 A B P p t lt2 s).
Proof. exact (eq_refl (term750 A B P p t lt2 s)). Qed.
Lemma lem8243594 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term752 A B P p lt2 t s) = (term821 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243593 A B P p t lt2 s) (@lem8243592 A B P p lt2 t s)). Qed.
Lemma lem8243596 {A : Type'} (P : Prop) (Q : A -> Prop) : (term822 A P Q) = (term823 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8243597 {A : Type'} (P : Prop) (Q : A -> Prop) : (term822 A P Q) = (term823 A P Q).
Proof. exact (@lem8243596 A P Q). Qed.
Lemma lem8243598 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term824 A B P p t f lt2 s a) = (term825 A B P p t f lt2 s a).
Proof. exact (@lem8243597 A (p f a) (term663 A B P t f lt2 s a)). Qed.
Lemma lem8243599 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term826 A B P t f lt2 s a y) = (term657 A B P t f lt2 y s a).
Proof. exact (eq_refl (term826 A B P t f lt2 s a y)). Qed.
Lemma lem8243600 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term827 A B P t f lt2 s a) = (term663 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8243599 A B P t f lt2 y s a)). Qed.
Lemma lem8243601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8243602 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term828 A B P t f lt2 s a) = (term664 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8243601 A) (@lem8243600 A B P t f lt2 s a)). Qed.
Lemma lem8243603 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term370 A B P p f a) = (term370 A B P p f a).
Proof. exact (eq_refl (term370 A B P p f a)). Qed.
Lemma lem8243604 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term824 A B P p t f lt2 s a) = (term667 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243603 A B P p f a) (@lem8243602 A B P t f lt2 s a)). Qed.
Lemma lem8243605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243606 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term829 A B P p t f lt2 s a) = (term830 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243605) (@lem8243604 A B P p t f lt2 s a)). Qed.
Lemma lem8243607 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term826 A B P t f lt2 s a y) = (term657 A B P t f lt2 y s a).
Proof. exact (eq_refl (term826 A B P t f lt2 s a y)). Qed.
Lemma lem8243608 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term370 A B P p f a) = (term370 A B P p f a).
Proof. exact (eq_refl (term370 A B P p f a)). Qed.
Lemma lem8243609 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term831 A B P p t f lt2 s a y) = (term832 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8243608 A B P p f a) (@lem8243607 A B P t f lt2 y s a)). Qed.
Lemma lem8243610 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term833 A B P p t f lt2 s a) = (term834 A B P p t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8243609 A B P p t f lt2 y s a)). Qed.
Lemma lem8243611 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8243612 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term825 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243611 A) (@lem8243610 A B P p t f lt2 s a)). Qed.
Lemma lem8243613 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : ((term824 A B P p t f lt2 s a) = (term825 A B P p t f lt2 s a)) = ((term667 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a)).
Proof. exact (MK_COMB (@lem8243606 A B P p t f lt2 s a) (@lem8243612 A B P p t f lt2 s a)). Qed.
Lemma lem8243614 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term667 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a).
Proof. exact (EQ_MP (@lem8243613 A B P p t f lt2 s a) (@lem8243598 A B P p t f lt2 s a)). Qed.
Lemma lem8243615 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term674 A B P p t f lt2 s) = (term836 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8243614 A B P p t f lt2 s a)). Qed.
Lemma lem8243616 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243617 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term675 A B P p t f lt2 s) = (term837 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8243616 P) (@lem8243615 A B P p t f lt2 s)). Qed.
Lemma lem8243618 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term683 A B P p t lt2 s) = (term838 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243617 A B P p t f lt2 s)). Qed.
Lemma lem8243619 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243620 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term684 A B P p t lt2 s) = (term839 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8243619 A B) (@lem8243618 A B P p t lt2 s)). Qed.
Lemma lem8243621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243622 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term750 A B P p t lt2 s) = (term840 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8243621) (@lem8243620 A B P p t lt2 s)). Qed.
Lemma lem8243624 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term754 A P Q) = (term753 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8243625 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term778 A B P Q) = (term777 A B P Q).
Proof. exact (@lem8243624 (A -> B) P Q). Qed.
Lemma lem8243626 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term802 A B P p lt2 t s) = (term801 A B P p lt2 t s).
Proof. exact (@lem8243625 A B (term803 A B P p lt2 s t) (term804 A B P p lt2 t s)). Qed.
Lemma lem8243627 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term805 A B P p lt2 s t f) = (term792 A B P p lt2 f s t).
Proof. exact (eq_refl (term805 A B P p lt2 s t f)). Qed.
Lemma lem8243628 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term812 A B P p lt2 s t) = (term803 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8243627 A B P p lt2 f s t)). Qed.
Lemma lem8243629 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243630 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term813 A B P p lt2 s t) = (term814 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8243629 A B) (@lem8243628 A B P p lt2 s t)). Qed.
Lemma lem8243631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243632 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term815 A B P p lt2 s t) = (term816 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8243631) (@lem8243630 A B P p lt2 s t)). Qed.
Lemma lem8243633 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term807 A B P p lt2 t s f) = (term797 A B P p lt2 t f s).
Proof. exact (eq_refl (term807 A B P p lt2 t s f)). Qed.
Lemma lem8243634 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term817 A B P p lt2 t s) = (term804 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243633 A B P p lt2 t f s)). Qed.
Lemma lem8243635 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243636 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term818 A B P p lt2 t s) = (term819 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243635 A B) (@lem8243634 A B P p lt2 t s)). Qed.
Lemma lem8243637 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term802 A B P p lt2 t s) = (term820 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243632 A B P p lt2 s t) (@lem8243636 A B P p lt2 t s)). Qed.
Lemma lem8243638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243639 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term841 A B P p lt2 t s) = (term842 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243638) (@lem8243637 A B P p lt2 t s)). Qed.
Lemma lem8243640 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term805 A B P p lt2 s t f) = (term792 A B P p lt2 f s t).
Proof. exact (eq_refl (term805 A B P p lt2 s t f)). Qed.
Lemma lem8243641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243642 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term806 A B P p lt2 s t f) = (term794 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243641) (@lem8243640 A B P p lt2 f s t)). Qed.
Lemma lem8243643 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term807 A B P p lt2 t s f) = (term797 A B P p lt2 t f s).
Proof. exact (eq_refl (term807 A B P p lt2 t s f)). Qed.
Lemma lem8243644 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term808 A B P p lt2 t s f) = (term798 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243642 A B P p lt2 f s t) (@lem8243643 A B P p lt2 t f s)). Qed.
Lemma lem8243645 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term809 A B P p lt2 t s) = (term799 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243644 A B P p lt2 t f s)). Qed.
Lemma lem8243646 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243647 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term801 A B P p lt2 t s) = (term800 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243646 A B) (@lem8243645 A B P p lt2 t s)). Qed.
Lemma lem8243648 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : ((term802 A B P p lt2 t s) = (term801 A B P p lt2 t s)) = ((term820 A B P p lt2 t s) = (term800 A B P p lt2 t s)).
Proof. exact (MK_COMB (@lem8243639 A B P p lt2 t s) (@lem8243647 A B P p lt2 t s)). Qed.
Lemma lem8243649 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term820 A B P p lt2 t s) = (term800 A B P p lt2 t s).
Proof. exact (EQ_MP (@lem8243648 A B P p lt2 t s) (@lem8243626 A B P p lt2 t s)). Qed.
Lemma lem8243651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term754 A P Q) = (term753 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8243652 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term778 A B P Q) = (term777 A B P Q).
Proof. exact (@lem8243651 (A -> B) P Q). Qed.
Lemma lem8243653 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term780 A B P p lt2 t f s) = (term779 A B P p lt2 t f s).
Proof. exact (@lem8243652 A B (term781 A B P p lt2 f s t) (term782 A B P p lt2 t f s)). Qed.
Lemma lem8243654 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term783 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (eq_refl (term783 A B P p lt2 f s t g)). Qed.
Lemma lem8243655 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term790 A B P p lt2 f s t) = (term781 A B P p lt2 f s t).
Proof. exact (fun_ext (fun g : A -> B => @lem8243654 A B P p lt2 f s t g)). Qed.
Lemma lem8243656 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243657 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term791 A B P p lt2 f s t) = (term792 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243656 A B) (@lem8243655 A B P p lt2 f s t)). Qed.
Lemma lem8243658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243659 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) : (term793 A B P p lt2 f s t) = (term794 A B P p lt2 f s t).
Proof. exact (MK_COMB (@lem8243658) (@lem8243657 A B P p lt2 f s t)). Qed.
Lemma lem8243660 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term785 A B P p lt2 t f s g) = (term773 A B P p lt2 g t f s).
Proof. exact (eq_refl (term785 A B P p lt2 t f s g)). Qed.
Lemma lem8243661 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term795 A B P p lt2 t f s) = (term782 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243660 A B P p lt2 g t f s)). Qed.
Lemma lem8243662 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243663 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term796 A B P p lt2 t f s) = (term797 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243662 A B) (@lem8243661 A B P p lt2 t f s)). Qed.
Lemma lem8243664 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term780 A B P p lt2 t f s) = (term798 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243659 A B P p lt2 f s t) (@lem8243663 A B P p lt2 t f s)). Qed.
Lemma lem8243665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243666 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term843 A B P p lt2 t f s) = (term844 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243665) (@lem8243664 A B P p lt2 t f s)). Qed.
Lemma lem8243667 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term783 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (eq_refl (term783 A B P p lt2 f s t g)). Qed.
Lemma lem8243668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243669 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term784 A B P p lt2 f s t g) = (term770 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8243668) (@lem8243667 A B P p lt2 f s t g)). Qed.
Lemma lem8243670 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term785 A B P p lt2 t f s g) = (term773 A B P p lt2 g t f s).
Proof. exact (eq_refl (term785 A B P p lt2 t f s g)). Qed.
Lemma lem8243671 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term786 A B P p lt2 t f s g) = (term774 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243669 A B P p lt2 f s t g) (@lem8243670 A B P p lt2 g t f s)). Qed.
Lemma lem8243672 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term787 A B P p lt2 t f s) = (term775 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243671 A B P p lt2 g t f s)). Qed.
Lemma lem8243673 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243674 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term779 A B P p lt2 t f s) = (term776 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243673 A B) (@lem8243672 A B P p lt2 t f s)). Qed.
Lemma lem8243675 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term780 A B P p lt2 t f s) = (term779 A B P p lt2 t f s)) = ((term798 A B P p lt2 t f s) = (term776 A B P p lt2 t f s)).
Proof. exact (MK_COMB (@lem8243666 A B P p lt2 t f s) (@lem8243674 A B P p lt2 t f s)). Qed.
Lemma lem8243676 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term798 A B P p lt2 t f s) = (term776 A B P p lt2 t f s).
Proof. exact (EQ_MP (@lem8243675 A B P p lt2 t f s) (@lem8243653 A B P p lt2 t f s)). Qed.
Lemma lem8243678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term754 A P Q) = (term753 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8243679 {P : Type'} (P' : P -> Prop) (Q : P -> Prop) : (term754 P P' Q) = (term753 P P' Q).
Proof. exact (@lem8243678 P P' Q). Qed.
Lemma lem8243680 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term756 A B P p lt2 g t f s) = (term755 A B P p lt2 g t f s).
Proof. exact (@lem8243679 P (term757 A B P p lt2 f s t g) (term758 A B P p lt2 g t f s)). Qed.
Lemma lem8243681 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term759 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (eq_refl (term759 A B P p lt2 f s t g a)). Qed.
Lemma lem8243682 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term766 A B P p lt2 f s t g) = (term757 A B P p lt2 f s t g).
Proof. exact (fun_ext (fun a : P => @lem8243681 A B P p lt2 f s t g a)). Qed.
Lemma lem8243683 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243684 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term767 A B P p lt2 f s t g) = (term768 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8243683 P) (@lem8243682 A B P p lt2 f s t g)). Qed.
Lemma lem8243685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243686 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) : (term769 A B P p lt2 f s t g) = (term770 A B P p lt2 f s t g).
Proof. exact (MK_COMB (@lem8243685) (@lem8243684 A B P p lt2 f s t g)). Qed.
Lemma lem8243687 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term761 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term761 A B P p lt2 g t f s a)). Qed.
Lemma lem8243688 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term771 A B P p lt2 g t f s) = (term758 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8243687 A B P p lt2 g t f s a)). Qed.
Lemma lem8243689 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243690 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term772 A B P p lt2 g t f s) = (term773 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243689 P) (@lem8243688 A B P p lt2 g t f s)). Qed.
Lemma lem8243691 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term756 A B P p lt2 g t f s) = (term774 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243686 A B P p lt2 f s t g) (@lem8243690 A B P p lt2 g t f s)). Qed.
Lemma lem8243692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243693 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term845 A B P p lt2 g t f s) = (term846 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243692) (@lem8243691 A B P p lt2 g t f s)). Qed.
Lemma lem8243694 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term759 A B P p lt2 f s t g a) = (term711 A B P p lt2 f s t g a).
Proof. exact (eq_refl (term759 A B P p lt2 f s t g a)). Qed.
Lemma lem8243695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243696 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a : P) : (term760 A B P p lt2 f s t g a) = (term724 A B P p lt2 f s t g a).
Proof. exact (MK_COMB (@lem8243695) (@lem8243694 A B P p lt2 f s t g a)). Qed.
Lemma lem8243697 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term761 A B P p lt2 g t f s a) = (term721 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term761 A B P p lt2 g t f s a)). Qed.
Lemma lem8243698 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term762 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (MK_COMB (@lem8243696 A B P p lt2 f s t g a) (@lem8243697 A B P p lt2 g t f s a)). Qed.
Lemma lem8243699 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term763 A B P p lt2 g t f s) = (term733 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8243698 A B P p lt2 g t f s a)). Qed.
Lemma lem8243700 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243701 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term755 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243700 P) (@lem8243699 A B P p lt2 g t f s)). Qed.
Lemma lem8243702 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term756 A B P p lt2 g t f s) = (term755 A B P p lt2 g t f s)) = ((term774 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s)).
Proof. exact (MK_COMB (@lem8243693 A B P p lt2 g t f s) (@lem8243701 A B P p lt2 g t f s)). Qed.
Lemma lem8243703 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term774 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (EQ_MP (@lem8243702 A B P p lt2 g t f s) (@lem8243680 A B P p lt2 g t f s)). Qed.
Lemma lem8243704 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term775 A B P p lt2 t f s) = (term740 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243703 A B P p lt2 g t f s)). Qed.
Lemma lem8243705 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243706 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term776 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243705 A B) (@lem8243704 A B P p lt2 t f s)). Qed.
Lemma lem8243707 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term798 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (TRANS (@lem8243676 A B P p lt2 t f s) (@lem8243706 A B P p lt2 t f s)). Qed.
Lemma lem8243708 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term799 A B P p lt2 t s) = (term747 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243707 A B P p lt2 t f s)). Qed.
Lemma lem8243709 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243710 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term800 A B P p lt2 t s) = (term748 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243709 A B) (@lem8243708 A B P p lt2 t s)). Qed.
Lemma lem8243711 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term820 A B P p lt2 t s) = (term748 A B P p lt2 t s).
Proof. exact (TRANS (@lem8243649 A B P p lt2 t s) (@lem8243710 A B P p lt2 t s)). Qed.
Lemma lem8243712 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term821 A B P p lt2 t s) = (term847 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243622 A B P p t lt2 s) (@lem8243711 A B P p lt2 t s)). Qed.
Lemma lem8243714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term754 A P Q) = (term753 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8243715 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term778 A B P Q) = (term777 A B P Q).
Proof. exact (@lem8243714 (A -> B) P Q). Qed.
Lemma lem8243716 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term848 A B P p lt2 t s) = (term849 A B P p lt2 t s).
Proof. exact (@lem8243715 A B (term838 A B P p t lt2 s) (term747 A B P p lt2 t s)). Qed.
Lemma lem8243717 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term850 A B P p t lt2 s f) = (term837 A B P p t f lt2 s).
Proof. exact (eq_refl (term850 A B P p t lt2 s f)). Qed.
Lemma lem8243718 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term851 A B P p t lt2 s) = (term838 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243717 A B P p t f lt2 s)). Qed.
Lemma lem8243719 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243720 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term852 A B P p t lt2 s) = (term839 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8243719 A B) (@lem8243718 A B P p t lt2 s)). Qed.
Lemma lem8243721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243722 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term853 A B P p t lt2 s) = (term840 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8243721) (@lem8243720 A B P p t lt2 s)). Qed.
Lemma lem8243723 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term854 A B P p lt2 t s f) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term854 A B P p lt2 t s f)). Qed.
Lemma lem8243724 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term855 A B P p lt2 t s) = (term747 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243723 A B P p lt2 t f s)). Qed.
Lemma lem8243725 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243726 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term856 A B P p lt2 t s) = (term748 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243725 A B) (@lem8243724 A B P p lt2 t s)). Qed.
Lemma lem8243727 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term848 A B P p lt2 t s) = (term847 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243722 A B P p t lt2 s) (@lem8243726 A B P p lt2 t s)). Qed.
Lemma lem8243728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243729 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term857 A B P p lt2 t s) = (term858 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243728) (@lem8243727 A B P p lt2 t s)). Qed.
Lemma lem8243730 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term850 A B P p t lt2 s f) = (term837 A B P p t f lt2 s).
Proof. exact (eq_refl (term850 A B P p t lt2 s f)). Qed.
Lemma lem8243731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243732 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term859 A B P p t lt2 s f) = (term860 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8243731) (@lem8243730 A B P p t f lt2 s)). Qed.
Lemma lem8243733 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term854 A B P p lt2 t s f) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term854 A B P p lt2 t s f)). Qed.
Lemma lem8243734 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term861 A B P p lt2 t s f) = (term862 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243732 A B P p t f lt2 s) (@lem8243733 A B P p lt2 t f s)). Qed.
Lemma lem8243735 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term863 A B P p lt2 t s) = (term864 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243734 A B P p lt2 t f s)). Qed.
Lemma lem8243736 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243737 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term849 A B P p lt2 t s) = (term865 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243736 A B) (@lem8243735 A B P p lt2 t s)). Qed.
Lemma lem8243738 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : ((term848 A B P p lt2 t s) = (term849 A B P p lt2 t s)) = ((term847 A B P p lt2 t s) = (term865 A B P p lt2 t s)).
Proof. exact (MK_COMB (@lem8243729 A B P p lt2 t s) (@lem8243737 A B P p lt2 t s)). Qed.
Lemma lem8243739 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term847 A B P p lt2 t s) = (term865 A B P p lt2 t s).
Proof. exact (EQ_MP (@lem8243738 A B P p lt2 t s) (@lem8243716 A B P p lt2 t s)). Qed.
Lemma lem8243743 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8243744 {P : Type'} (P' : P -> Prop) (Q : Prop) : (term461 P P' Q) = (term462 P P' Q).
Proof. exact (@lem8243743 P P' Q). Qed.
Lemma lem8243745 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term866 A B P p lt2 t f s) = (term867 A B P p lt2 t f s).
Proof. exact (@lem8243744 P (term836 A B P p t f lt2 s) (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243746 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term868 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a).
Proof. exact (eq_refl (term868 A B P p t f lt2 s a)). Qed.
Lemma lem8243747 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term869 A B P p t f lt2 s) = (term836 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8243746 A B P p t f lt2 s a)). Qed.
Lemma lem8243748 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243749 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term870 A B P p t f lt2 s) = (term837 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8243748 P) (@lem8243747 A B P p t f lt2 s)). Qed.
Lemma lem8243750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243751 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term871 A B P p t f lt2 s) = (term860 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8243750) (@lem8243749 A B P p t f lt2 s)). Qed.
Lemma lem8243752 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243753 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term866 A B P p lt2 t f s) = (term862 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243751 A B P p t f lt2 s) (@lem8243752 A B P p lt2 t f s)). Qed.
Lemma lem8243754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243755 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term872 A B P p lt2 t f s) = (term873 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243754) (@lem8243753 A B P p lt2 t f s)). Qed.
Lemma lem8243756 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term868 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a).
Proof. exact (eq_refl (term868 A B P p t f lt2 s a)). Qed.
Lemma lem8243757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243758 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term874 A B P p t f lt2 s a) = (term875 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243757) (@lem8243756 A B P p t f lt2 s a)). Qed.
Lemma lem8243759 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243760 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term876 A B P a p lt2 t f s) = (term877 A B P a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243758 A B P p t f lt2 s a) (@lem8243759 A B P p lt2 t f s)). Qed.
Lemma lem8243761 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term878 A B P p lt2 t f s) = (term879 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8243760 A B P a p lt2 t f s)). Qed.
Lemma lem8243762 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243763 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term867 A B P p lt2 t f s) = (term880 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243762 P) (@lem8243761 A B P p lt2 t f s)). Qed.
Lemma lem8243764 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term866 A B P p lt2 t f s) = (term867 A B P p lt2 t f s)) = ((term862 A B P p lt2 t f s) = (term880 A B P p lt2 t f s)).
Proof. exact (MK_COMB (@lem8243755 A B P p lt2 t f s) (@lem8243763 A B P p lt2 t f s)). Qed.
Lemma lem8243765 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term862 A B P p lt2 t f s) = (term880 A B P p lt2 t f s).
Proof. exact (EQ_MP (@lem8243764 A B P p lt2 t f s) (@lem8243745 A B P p lt2 t f s)). Qed.
Lemma lem8243769 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8243770 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (@lem8243769 A P Q). Qed.
Lemma lem8243771 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term881 A B P a p lt2 t f s) = (term882 A B P a p lt2 t f s).
Proof. exact (@lem8243770 A (term834 A B P p t f lt2 s a) (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243772 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term883 A B P p t f lt2 s a y) = (term832 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term883 A B P p t f lt2 s a y)). Qed.
Lemma lem8243773 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term884 A B P p t f lt2 s a) = (term834 A B P p t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8243772 A B P p t f lt2 y s a)). Qed.
Lemma lem8243774 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8243775 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term885 A B P p t f lt2 s a) = (term835 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243774 A) (@lem8243773 A B P p t f lt2 s a)). Qed.
Lemma lem8243776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243777 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term886 A B P p t f lt2 s a) = (term875 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243776) (@lem8243775 A B P p t f lt2 s a)). Qed.
Lemma lem8243778 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243779 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term881 A B P a p lt2 t f s) = (term877 A B P a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243777 A B P p t f lt2 s a) (@lem8243778 A B P p lt2 t f s)). Qed.
Lemma lem8243780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243781 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term887 A B P a p lt2 t f s) = (term888 A B P a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243780) (@lem8243779 A B P a p lt2 t f s)). Qed.
Lemma lem8243782 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term883 A B P p t f lt2 s a y) = (term832 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term883 A B P p t f lt2 s a y)). Qed.
Lemma lem8243783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243784 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term889 A B P p t f lt2 s a y) = (term890 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8243783) (@lem8243782 A B P p t f lt2 y s a)). Qed.
Lemma lem8243785 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term741 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (eq_refl (term741 A B P p lt2 t f s)). Qed.
Lemma lem8243786 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term891 A B P a y p lt2 t f s) = (term892 A B P y a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243784 A B P p t f lt2 y s a) (@lem8243785 A B P p lt2 t f s)). Qed.
Lemma lem8243787 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term893 A B P a p lt2 t f s) = (term894 A B P a p lt2 t f s).
Proof. exact (fun_ext (fun y : A => @lem8243786 A B P y a p lt2 t f s)). Qed.
Lemma lem8243788 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8243789 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term882 A B P a p lt2 t f s) = (term895 A B P a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243788 A) (@lem8243787 A B P a p lt2 t f s)). Qed.
Lemma lem8243790 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term881 A B P a p lt2 t f s) = (term882 A B P a p lt2 t f s)) = ((term877 A B P a p lt2 t f s) = (term895 A B P a p lt2 t f s)).
Proof. exact (MK_COMB (@lem8243781 A B P a p lt2 t f s) (@lem8243789 A B P a p lt2 t f s)). Qed.
Lemma lem8243791 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term877 A B P a p lt2 t f s) = (term895 A B P a p lt2 t f s).
Proof. exact (EQ_MP (@lem8243790 A B P a p lt2 t f s) (@lem8243771 A B P a p lt2 t f s)). Qed.
Lemma lem8243793 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8243794 {A B : Type'} (P : Prop) (Q : type572 A B) : (term896 A B P Q) = (term897 A B P Q).
Proof. exact (@lem8243793 (A -> B) P Q). Qed.
Lemma lem8243795 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term898 A B P y a p lt2 t f s) = (term899 A B P y a p lt2 t f s).
Proof. exact (@lem8243794 A B (term832 A B P p t f lt2 y s a) (term740 A B P p lt2 t f s)). Qed.
Lemma lem8243796 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term900 A B P p lt2 t f s g) = (term734 A B P p lt2 g t f s).
Proof. exact (eq_refl (term900 A B P p lt2 t f s g)). Qed.
Lemma lem8243797 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term901 A B P p lt2 t f s) = (term740 A B P p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243796 A B P p lt2 g t f s)). Qed.
Lemma lem8243798 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243799 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term902 A B P p lt2 t f s) = (term741 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243798 A B) (@lem8243797 A B P p lt2 t f s)). Qed.
Lemma lem8243800 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term890 A B P p t f lt2 y s a) = (term890 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term890 A B P p t f lt2 y s a)). Qed.
Lemma lem8243801 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term898 A B P y a p lt2 t f s) = (term892 A B P y a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243800 A B P p t f lt2 y s a) (@lem8243799 A B P p lt2 t f s)). Qed.
Lemma lem8243802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243803 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term903 A B P y a p lt2 t f s) = (term904 A B P y a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243802) (@lem8243801 A B P y a p lt2 t f s)). Qed.
Lemma lem8243804 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term900 A B P p lt2 t f s g) = (term734 A B P p lt2 g t f s).
Proof. exact (eq_refl (term900 A B P p lt2 t f s g)). Qed.
Lemma lem8243805 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term890 A B P p t f lt2 y s a) = (term890 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term890 A B P p t f lt2 y s a)). Qed.
Lemma lem8243806 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term905 A B P y a p lt2 t f s g) = (term906 A B P y a p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243805 A B P p t f lt2 y s a) (@lem8243804 A B P p lt2 g t f s)). Qed.
Lemma lem8243807 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term907 A B P y a p lt2 t f s) = (term908 A B P y a p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243806 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243808 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243809 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term899 A B P y a p lt2 t f s) = (term909 A B P y a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243808 A B) (@lem8243807 A B P y a p lt2 t f s)). Qed.
Lemma lem8243810 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term898 A B P y a p lt2 t f s) = (term899 A B P y a p lt2 t f s)) = ((term892 A B P y a p lt2 t f s) = (term909 A B P y a p lt2 t f s)).
Proof. exact (MK_COMB (@lem8243803 A B P y a p lt2 t f s) (@lem8243809 A B P y a p lt2 t f s)). Qed.
Lemma lem8243811 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term892 A B P y a p lt2 t f s) = (term909 A B P y a p lt2 t f s).
Proof. exact (EQ_MP (@lem8243810 A B P y a p lt2 t f s) (@lem8243795 A B P y a p lt2 t f s)). Qed.
Lemma lem8243813 {A : Type'} (P : Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8243814 {P : Type'} (P' : Prop) (Q : P -> Prop) : (term432 P P' Q) = (term433 P P' Q).
Proof. exact (@lem8243813 P P' Q). Qed.
Lemma lem8243815 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term910 A B P y a p lt2 g t f s) = (term911 A B P y a p lt2 g t f s).
Proof. exact (@lem8243814 P (term832 A B P p t f lt2 y s a) (term733 A B P p lt2 g t f s)). Qed.
Lemma lem8243816 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term912 A B P p lt2 g t f s a) = (term726 A B P p lt2 g t f s a).
Proof. exact (eq_refl (term912 A B P p lt2 g t f s a)). Qed.
Lemma lem8243817 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term913 A B P p lt2 g t f s) = (term733 A B P p lt2 g t f s).
Proof. exact (fun_ext (fun a : P => @lem8243816 A B P p lt2 g t f s a)). Qed.
Lemma lem8243818 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243819 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term914 A B P p lt2 g t f s) = (term734 A B P p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243818 P) (@lem8243817 A B P p lt2 g t f s)). Qed.
Lemma lem8243820 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term890 A B P p t f lt2 y s a) = (term890 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term890 A B P p t f lt2 y s a)). Qed.
Lemma lem8243821 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term910 A B P y a p lt2 g t f s) = (term906 A B P y a p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243820 A B P p t f lt2 y s a) (@lem8243819 A B P p lt2 g t f s)). Qed.
Lemma lem8243822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8243823 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term915 A B P y a p lt2 g t f s) = (term916 A B P y a p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243822) (@lem8243821 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243824 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term912 A B P p lt2 g t f s a') = (term726 A B P p lt2 g t f s a').
Proof. exact (eq_refl (term912 A B P p lt2 g t f s a')). Qed.
Lemma lem8243825 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term890 A B P p t f lt2 y s a) = (term890 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term890 A B P p t f lt2 y s a)). Qed.
Lemma lem8243826 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term917 A B P y a p lt2 g t f s a') = (term918 A B P y a p lt2 g t f s a').
Proof. exact (MK_COMB (@lem8243825 A B P p t f lt2 y s a) (@lem8243824 A B P p lt2 g t f s a')). Qed.
Lemma lem8243827 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term919 A B P y a p lt2 g t f s) = (term920 A B P y a p lt2 g t f s).
Proof. exact (fun_ext (fun a' : P => @lem8243826 A B P y a p lt2 g t f s a')). Qed.
Lemma lem8243828 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243829 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term911 A B P y a p lt2 g t f s) = (term921 A B P y a p lt2 g t f s).
Proof. exact (MK_COMB (@lem8243828 P) (@lem8243827 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243830 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : ((term910 A B P y a p lt2 g t f s) = (term911 A B P y a p lt2 g t f s)) = ((term906 A B P y a p lt2 g t f s) = (term921 A B P y a p lt2 g t f s)).
Proof. exact (MK_COMB (@lem8243823 A B P y a p lt2 g t f s) (@lem8243829 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243831 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term906 A B P y a p lt2 g t f s) = (term921 A B P y a p lt2 g t f s).
Proof. exact (EQ_MP (@lem8243830 A B P y a p lt2 g t f s) (@lem8243815 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243832 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term908 A B P y a p lt2 t f s) = (term922 A B P y a p lt2 t f s).
Proof. exact (fun_ext (fun g : A -> B => @lem8243831 A B P y a p lt2 g t f s)). Qed.
Lemma lem8243833 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243834 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term909 A B P y a p lt2 t f s) = (term923 A B P y a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243833 A B) (@lem8243832 A B P y a p lt2 t f s)). Qed.
Lemma lem8243835 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term892 A B P y a p lt2 t f s) = (term923 A B P y a p lt2 t f s).
Proof. exact (TRANS (@lem8243811 A B P y a p lt2 t f s) (@lem8243834 A B P y a p lt2 t f s)). Qed.
Lemma lem8243836 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term894 A B P a p lt2 t f s) = (term924 A B P a p lt2 t f s).
Proof. exact (fun_ext (fun y : A => @lem8243835 A B P y a p lt2 t f s)). Qed.
Lemma lem8243837 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8243838 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term895 A B P a p lt2 t f s) = (term925 A B P a p lt2 t f s).
Proof. exact (MK_COMB (@lem8243837 A) (@lem8243836 A B P a p lt2 t f s)). Qed.
Lemma lem8243839 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term877 A B P a p lt2 t f s) = (term925 A B P a p lt2 t f s).
Proof. exact (TRANS (@lem8243791 A B P a p lt2 t f s) (@lem8243838 A B P a p lt2 t f s)). Qed.
Lemma lem8243840 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term879 A B P p lt2 t f s) = (term926 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8243839 A B P a p lt2 t f s)). Qed.
Lemma lem8243841 {P : Type'} : (@ex P) = (@ex P).
Proof. exact (eq_refl (@ex P)). Qed.
Lemma lem8243842 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term880 A B P p lt2 t f s) = (term927 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8243841 P) (@lem8243840 A B P p lt2 t f s)). Qed.
Lemma lem8243843 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term862 A B P p lt2 t f s) = (term927 A B P p lt2 t f s).
Proof. exact (TRANS (@lem8243765 A B P p lt2 t f s) (@lem8243842 A B P p lt2 t f s)). Qed.
Lemma lem8243844 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term864 A B P p lt2 t s) = (term928 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243843 A B P p lt2 t f s)). Qed.
Lemma lem8243845 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem8243846 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term865 A B P p lt2 t s) = (term929 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8243845 A B) (@lem8243844 A B P p lt2 t s)). Qed.
Lemma lem8243847 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term847 A B P p lt2 t s) = (term929 A B P p lt2 t s).
Proof. exact (TRANS (@lem8243739 A B P p lt2 t s) (@lem8243846 A B P p lt2 t s)). Qed.
Lemma lem8243848 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term821 A B P p lt2 t s) = (term929 A B P p lt2 t s).
Proof. exact (TRANS (@lem8243712 A B P p lt2 t s) (@lem8243847 A B P p lt2 t s)). Qed.
Lemma lem8243849 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term752 A B P p lt2 t s) = (term929 A B P p lt2 t s).
Proof. exact (TRANS (@lem8243594 A B P p lt2 t s) (@lem8243848 A B P p lt2 t s)). Qed.
Lemma lem8243850 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term404 A B P p lt2 t s) = (term929 A B P p lt2 t s).
Proof. exact (TRANS (@lem8242651 A B P p lt2 t s) (@lem8243849 A B P p lt2 t s)). Qed.
Lemma lem8243851 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term404 A B P p lt2 t s) : term929 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8243850 A B P p lt2 t s) (@lem8241744 A B P p lt2 t s h1)). Qed.
Lemma lem8243852 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term927 A B P p lt2 t f s) : term927 A B P p lt2 t f s.
Proof. exact (h1). Qed.
Lemma lem8243853 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term925 A B P a p lt2 t f s) : term925 A B P a p lt2 t f s.
Proof. exact (h1). Qed.
Lemma lem8243854 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term923 A B P y a p lt2 t f s) : term923 A B P y a p lt2 t f s.
Proof. exact (h1). Qed.
Lemma lem8243855 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term921 A B P y a p lt2 g t f s) : term921 A B P y a p lt2 g t f s.
Proof. exact (h1). Qed.
Lemma lem8243856 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term918 A B P y a p lt2 g t f s a') : term918 A B P y a p lt2 g t f s a'.
Proof. exact (h1). Qed.
Lemma lem8243857 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term651 A B P lt2 s z p.
Proof. exact (h1). Qed.
Lemma lem8243858 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term551 A B P p lt2 s z' t.
Proof. exact (h1). Qed.
Lemma lem8243865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243866 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8243865 P A f x). Qed.
Lemma lem8243868 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8243866 A P s a). Qed.
Lemma lem8243869 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8243870 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term930 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8243869 A lt2 y) (@lem8243868 A P s a)). Qed.
Lemma lem8243872 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243873 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8243872 A (A -> Prop) f x). Qed.
Lemma lem8243874 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem8243873 A lt2 y). Qed.
Lemma lem8243875 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8243876 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term930 A P lt2 y s a) = (term931 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8243874 A lt2 y) (@lem8243875 A P s a)). Qed.
Lemma lem8243878 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243879 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8243878 A Prop f x). Qed.
Lemma lem8243880 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term931 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (@lem8243879 A (@I (A -> A -> Prop) lt2 y) (@I (P -> A) s a)). Qed.
Lemma lem8243881 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term930 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (TRANS (@lem8243876 A P lt2 y s a) (@lem8243880 A P lt2 y s a)). Qed.
Lemma lem8243882 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (TRANS (@lem8243870 A P lt2 y s a) (@lem8243881 A P lt2 y s a)). Qed.
Lemma lem8243883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8243892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243893 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8243892 (A -> B) (P -> A) f x). Qed.
Lemma lem8243894 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8243893 A B P t f). Qed.
Lemma lem8243895 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8243896 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8243894 A B P t f) (@lem8243895 P a)). Qed.
Lemma lem8243898 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243899 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8243898 P A f x). Qed.
Lemma lem8243900 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term933 A B P t f a).
Proof. exact (@lem8243899 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8243902 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term933 A B P t f a).
Proof. exact (TRANS (@lem8243896 A B P t f a) (@lem8243900 A B P t f a)). Qed.
Lemma lem8243903 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8243904 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term345 A B P lt2 y t f a) = (term934 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8243903 A lt2 y) (@lem8243902 A B P t f a)). Qed.
Lemma lem8243906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243907 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8243906 A (A -> Prop) f x). Qed.
Lemma lem8243908 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem8243907 A lt2 y). Qed.
Lemma lem8243909 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term933 A B P t f a) = (term933 A B P t f a).
Proof. exact (eq_refl (term933 A B P t f a)). Qed.
Lemma lem8243910 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term934 A B P lt2 y t f a) = (term935 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8243908 A lt2 y) (@lem8243909 A B P t f a)). Qed.
Lemma lem8243912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243913 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8243912 A Prop f x). Qed.
Lemma lem8243914 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term935 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (@lem8243913 A (@I (A -> A -> Prop) lt2 y) (term933 A B P t f a)). Qed.
Lemma lem8243915 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term934 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (TRANS (@lem8243910 A B P lt2 y t f a) (@lem8243914 A B P lt2 y t f a)). Qed.
Lemma lem8243916 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term345 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (TRANS (@lem8243904 A B P lt2 y t f a) (@lem8243915 A B P lt2 y t f a)). Qed.
Lemma lem8243917 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term937 A B P lt2 y t f a) = (term938 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8243883) (@lem8243916 A B P lt2 y t f a)). Qed.
Lemma lem8243918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243919 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term939 A B P lt2 y t f a) = (term940 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8243918) (@lem8243917 A B P lt2 y t f a)). Qed.
Lemma lem8243920 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term555 A B P t f lt2 y s a) = (term941 A B P t f lt2 y s a).
Proof. exact (MK_COMB (@lem8243919 A B P lt2 y t f a) (@lem8243882 A P lt2 y s a)). Qed.
Lemma lem8243921 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term556 A B P t f lt2 s a) = (term942 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8243920 A B P t f lt2 y s a)). Qed.
Lemma lem8243922 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8243923 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term557 A B P t f lt2 s a) = (term943 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8243922 A) (@lem8243921 A B P t f lt2 s a)). Qed.
Lemma lem8243924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8243931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243932 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8243931 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8243933 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8243932 A B P p f). Qed.
Lemma lem8243934 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8243935 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8243933 A B P p f) (@lem8243934 P a)). Qed.
Lemma lem8243937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243938 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8243937 P Prop f x). Qed.
Lemma lem8243939 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term944 A B P p f a).
Proof. exact (@lem8243938 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8243941 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term944 A B P p f a).
Proof. exact (TRANS (@lem8243935 A B P p f a) (@lem8243939 A B P p f a)). Qed.
Lemma lem8243942 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term292 A B P p f a) = (term945 A B P p f a).
Proof. exact (MK_COMB (@lem8243924) (@lem8243941 A B P p f a)). Qed.
Lemma lem8243943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8243944 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term946 A B P p f a).
Proof. exact (MK_COMB (@lem8243943) (@lem8243942 A B P p f a)). Qed.
Lemma lem8243945 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term558 A B P p t f lt2 s a) = (term947 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8243944 A B P p f a) (@lem8243923 A B P t f lt2 s a)). Qed.
Lemma lem8243946 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term559 A B P p t f lt2 s) = (term948 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8243945 A B P p t f lt2 s a)). Qed.
Lemma lem8243947 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8243948 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term560 A B P p t f lt2 s) = (term949 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8243947 P) (@lem8243946 A B P p t f lt2 s)). Qed.
Lemma lem8243949 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term561 A B P p t lt2 s) = (term950 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8243948 A B P p t f lt2 s)). Qed.
Lemma lem8243950 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8243951 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term562 A B P p t lt2 s) = (term951 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8243950 A B) (@lem8243949 A B P p t lt2 s)). Qed.
Lemma lem8243952 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term951 A B P p t lt2 s.
Proof. exact (EQ_MP (@lem8243951 A B P p t lt2 s) (@lem8242197 A B P p t lt2 s h1)). Qed.
Lemma lem8243953 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8243954 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8243961 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243962 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8243961 (A -> B) (P -> A) f x). Qed.
Lemma lem8243963 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8243962 A B P t f). Qed.
Lemma lem8243964 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8243965 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (t f a') = (@I ((A -> B) -> P -> A) t f a').
Proof. exact (MK_COMB (@lem8243963 A B P t f) (@lem8243964 P a')). Qed.
Lemma lem8243967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243968 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8243967 P A f x). Qed.
Lemma lem8243969 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (@I ((A -> B) -> P -> A) t f a') = (term933 A B P t f a').
Proof. exact (@lem8243968 A P (@I ((A -> B) -> P -> A) t f) a'). Qed.
Lemma lem8243971 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (t f a') = (term933 A B P t f a').
Proof. exact (TRANS (@lem8243965 A B P t f a') (@lem8243969 A B P t f a')). Qed.
Lemma lem8243976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243977 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8243976 P A f x). Qed.
Lemma lem8243979 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8243977 A P s a'). Qed.
Lemma lem8243980 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (term299 A B P t f a') = (term952 A B P t f a').
Proof. exact (MK_COMB (@lem8243954 A) (@lem8243971 A B P t f a')). Qed.
Lemma lem8243981 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : ((t f a') = (s a')) = ((term933 A B P t f a') = (@I (P -> A) s a')).
Proof. exact (MK_COMB (@lem8243980 A B P t f a') (@lem8243979 A P s a')). Qed.
Lemma lem8243982 {A B P : Type'} (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term713 A B P t f s a') = (term953 A B P t f s a').
Proof. exact (MK_COMB (@lem8243953) (@lem8243981 A B P t f s a')). Qed.
Lemma lem8243983 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8243988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243989 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8243988 A B f x). Qed.
Lemma lem8243991 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8243989 A B f z). Qed.
Lemma lem8243996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8243997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8243996 A B f x). Qed.
Lemma lem8243999 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8243997 A B g z). Qed.
Lemma lem8244000 {A B : Type'} (f : A -> B) (z : A) : (term954 A B f z) = (term955 A B f z).
Proof. exact (MK_COMB (@lem8243983 B) (@lem8243991 A B f z)). Qed.
Lemma lem8244001 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8244000 A B f z) (@lem8243999 A B g z)). Qed.
Lemma lem8244002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244010 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244009 P A f x). Qed.
Lemma lem8244012 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8244010 A P s a'). Qed.
Lemma lem8244013 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8244014 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term930 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244013 A lt2 z) (@lem8244012 A P s a')). Qed.
Lemma lem8244016 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244017 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244016 A (A -> Prop) f x). Qed.
Lemma lem8244018 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8244017 A lt2 z). Qed.
Lemma lem8244019 {A P : Type'} (s : P -> A) (a' : P) : (@I (P -> A) s a') = (@I (P -> A) s a').
Proof. exact (eq_refl (@I (P -> A) s a')). Qed.
Lemma lem8244020 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term931 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244018 A lt2 z) (@lem8244019 A P s a')). Qed.
Lemma lem8244022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244023 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244022 A Prop f x). Qed.
Lemma lem8244024 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term931 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (@lem8244023 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a')). Qed.
Lemma lem8244025 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244020 A P lt2 z s a') (@lem8244024 A P lt2 z s a')). Qed.
Lemma lem8244026 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244014 A P lt2 z s a') (@lem8244025 A P lt2 z s a')). Qed.
Lemma lem8244027 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term956 A P lt2 z s a') = (term957 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244002) (@lem8244026 A P lt2 z s a')). Qed.
Lemma lem8244028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244029 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term958 A P lt2 z s a') = (term959 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244028) (@lem8244027 A P lt2 z s a')). Qed.
Lemma lem8244030 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term685 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (MK_COMB (@lem8244029 A P lt2 z s a') (@lem8244001 A B f g z)). Qed.
Lemma lem8244031 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term686 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8244030 A B P lt2 s a' f g z)). Qed.
Lemma lem8244032 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244033 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term687 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244032 A) (@lem8244031 A B P lt2 s a' f g)). Qed.
Lemma lem8244034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244035 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term690 A B P lt2 s a' f g) = (term963 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244034) (@lem8244033 A B P lt2 s a' f g)). Qed.
Lemma lem8244036 {A B P : Type'} (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term715 A B P lt2 g t f s a') = (term964 A B P lt2 g t f s a').
Proof. exact (MK_COMB (@lem8244035 A B P lt2 s a' f g) (@lem8243982 A B P t f s a')). Qed.
Lemma lem8244043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244044 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244043 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244045 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244044 A B P p f). Qed.
Lemma lem8244046 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244047 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (@I ((A -> B) -> P -> Prop) p f a').
Proof. exact (MK_COMB (@lem8244045 A B P p f) (@lem8244046 P a')). Qed.
Lemma lem8244049 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244050 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244049 P Prop f x). Qed.
Lemma lem8244051 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (@I ((A -> B) -> P -> Prop) p f a') = (term944 A B P p f a').
Proof. exact (@lem8244050 P (@I ((A -> B) -> P -> Prop) p f) a'). Qed.
Lemma lem8244053 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (term944 A B P p f a').
Proof. exact (TRANS (@lem8244047 A B P p f a') (@lem8244051 A B P p f a')). Qed.
Lemma lem8244054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244055 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term370 A B P p f a') = (term965 A B P p f a').
Proof. exact (MK_COMB (@lem8244054) (@lem8244053 A B P p f a')). Qed.
Lemma lem8244056 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term718 A B P p lt2 g t f s a') = (term966 A B P p lt2 g t f s a').
Proof. exact (MK_COMB (@lem8244055 A B P p f a') (@lem8244036 A B P lt2 g t f s a')). Qed.
Lemma lem8244057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244065 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244064 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244066 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8244065 A B P p g). Qed.
Lemma lem8244067 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244068 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (p g a') = (@I ((A -> B) -> P -> Prop) p g a').
Proof. exact (MK_COMB (@lem8244066 A B P p g) (@lem8244067 P a')). Qed.
Lemma lem8244070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244071 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244070 P Prop f x). Qed.
Lemma lem8244072 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (@I ((A -> B) -> P -> Prop) p g a') = (term944 A B P p g a').
Proof. exact (@lem8244071 P (@I ((A -> B) -> P -> Prop) p g) a'). Qed.
Lemma lem8244074 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (p g a') = (term944 A B P p g a').
Proof. exact (TRANS (@lem8244068 A B P p g a') (@lem8244072 A B P p g a')). Qed.
Lemma lem8244075 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term292 A B P p g a') = (term945 A B P p g a').
Proof. exact (MK_COMB (@lem8244057) (@lem8244074 A B P p g a')). Qed.
Lemma lem8244076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244077 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term701 A B P p g a') = (term967 A B P p g a').
Proof. exact (MK_COMB (@lem8244076) (@lem8244075 A B P p g a')). Qed.
Lemma lem8244078 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term721 A B P p lt2 g t f s a') = (term968 A B P p lt2 g t f s a').
Proof. exact (MK_COMB (@lem8244077 A B P p g a') (@lem8244056 A B P p lt2 g t f s a')). Qed.
Lemma lem8244079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244080 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8244085 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244086 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244085 P A f x). Qed.
Lemma lem8244088 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8244086 A P s a'). Qed.
Lemma lem8244095 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244096 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244095 (A -> B) (P -> A) f x). Qed.
Lemma lem8244097 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> A) t g).
Proof. exact (@lem8244096 A B P t g). Qed.
Lemma lem8244098 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244099 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (t g a') = (@I ((A -> B) -> P -> A) t g a').
Proof. exact (MK_COMB (@lem8244097 A B P t g) (@lem8244098 P a')). Qed.
Lemma lem8244101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244102 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244101 P A f x). Qed.
Lemma lem8244103 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (@I ((A -> B) -> P -> A) t g a') = (term933 A B P t g a').
Proof. exact (@lem8244102 A P (@I ((A -> B) -> P -> A) t g) a'). Qed.
Lemma lem8244105 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (t g a') = (term933 A B P t g a').
Proof. exact (TRANS (@lem8244099 A B P t g a') (@lem8244103 A B P t g a')). Qed.
Lemma lem8244106 {A P : Type'} (s : P -> A) (a' : P) : (term202 A P s a') = (term969 A P s a').
Proof. exact (MK_COMB (@lem8244080 A) (@lem8244088 A P s a')). Qed.
Lemma lem8244107 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : ((s a') = (t g a')) = ((@I (P -> A) s a') = (term933 A B P t g a')).
Proof. exact (MK_COMB (@lem8244106 A P s a') (@lem8244105 A B P t g a')). Qed.
Lemma lem8244108 {A B P : Type'} (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term697 A B P s t g a') = (term970 A B P s t g a').
Proof. exact (MK_COMB (@lem8244079) (@lem8244107 A B P s t g a')). Qed.
Lemma lem8244109 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8244114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244114 A B f x). Qed.
Lemma lem8244117 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8244115 A B f z). Qed.
Lemma lem8244122 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244122 A B f x). Qed.
Lemma lem8244125 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8244123 A B g z). Qed.
Lemma lem8244126 {A B : Type'} (f : A -> B) (z : A) : (term954 A B f z) = (term955 A B f z).
Proof. exact (MK_COMB (@lem8244109 B) (@lem8244117 A B f z)). Qed.
Lemma lem8244127 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8244126 A B f z) (@lem8244125 A B g z)). Qed.
Lemma lem8244128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244136 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244135 P A f x). Qed.
Lemma lem8244138 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8244136 A P s a'). Qed.
Lemma lem8244139 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8244140 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term930 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244139 A lt2 z) (@lem8244138 A P s a')). Qed.
Lemma lem8244142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244143 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244142 A (A -> Prop) f x). Qed.
Lemma lem8244144 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8244143 A lt2 z). Qed.
Lemma lem8244145 {A P : Type'} (s : P -> A) (a' : P) : (@I (P -> A) s a') = (@I (P -> A) s a').
Proof. exact (eq_refl (@I (P -> A) s a')). Qed.
Lemma lem8244146 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term931 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244144 A lt2 z) (@lem8244145 A P s a')). Qed.
Lemma lem8244148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244149 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244148 A Prop f x). Qed.
Lemma lem8244150 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term931 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (@lem8244149 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a')). Qed.
Lemma lem8244151 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244146 A P lt2 z s a') (@lem8244150 A P lt2 z s a')). Qed.
Lemma lem8244152 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244140 A P lt2 z s a') (@lem8244151 A P lt2 z s a')). Qed.
Lemma lem8244153 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term956 A P lt2 z s a') = (term957 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244128) (@lem8244152 A P lt2 z s a')). Qed.
Lemma lem8244154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244155 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term958 A P lt2 z s a') = (term959 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244154) (@lem8244153 A P lt2 z s a')). Qed.
Lemma lem8244156 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term685 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (MK_COMB (@lem8244155 A P lt2 z s a') (@lem8244127 A B f g z)). Qed.
Lemma lem8244157 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term686 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8244156 A B P lt2 s a' f g z)). Qed.
Lemma lem8244158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244159 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term687 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244158 A) (@lem8244157 A B P lt2 s a' f g)). Qed.
Lemma lem8244160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244161 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term690 A B P lt2 s a' f g) = (term963 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244160) (@lem8244159 A B P lt2 s a' f g)). Qed.
Lemma lem8244162 {A B P : Type'} (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term699 A B P lt2 f s t g a') = (term971 A B P lt2 f s t g a').
Proof. exact (MK_COMB (@lem8244161 A B P lt2 s a' f g) (@lem8244108 A B P s t g a')). Qed.
Lemma lem8244163 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244171 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244170 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244172 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244171 A B P p f). Qed.
Lemma lem8244173 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244174 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (@I ((A -> B) -> P -> Prop) p f a').
Proof. exact (MK_COMB (@lem8244172 A B P p f) (@lem8244173 P a')). Qed.
Lemma lem8244176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244177 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244176 P Prop f x). Qed.
Lemma lem8244178 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (@I ((A -> B) -> P -> Prop) p f a') = (term944 A B P p f a').
Proof. exact (@lem8244177 P (@I ((A -> B) -> P -> Prop) p f) a'). Qed.
Lemma lem8244180 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (term944 A B P p f a').
Proof. exact (TRANS (@lem8244174 A B P p f a') (@lem8244178 A B P p f a')). Qed.
Lemma lem8244181 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term292 A B P p f a') = (term945 A B P p f a').
Proof. exact (MK_COMB (@lem8244163) (@lem8244180 A B P p f a')). Qed.
Lemma lem8244182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244183 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term701 A B P p f a') = (term967 A B P p f a').
Proof. exact (MK_COMB (@lem8244182) (@lem8244181 A B P p f a')). Qed.
Lemma lem8244184 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term703 A B P p lt2 f s t g a') = (term972 A B P p lt2 f s t g a').
Proof. exact (MK_COMB (@lem8244183 A B P p f a') (@lem8244162 A B P lt2 f s t g a')). Qed.
Lemma lem8244185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244186 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8244193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244194 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244193 (A -> B) (P -> A) f x). Qed.
Lemma lem8244195 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8244194 A B P t f). Qed.
Lemma lem8244196 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244197 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (t f a') = (@I ((A -> B) -> P -> A) t f a').
Proof. exact (MK_COMB (@lem8244195 A B P t f) (@lem8244196 P a')). Qed.
Lemma lem8244199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244200 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244199 P A f x). Qed.
Lemma lem8244201 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (@I ((A -> B) -> P -> A) t f a') = (term933 A B P t f a').
Proof. exact (@lem8244200 A P (@I ((A -> B) -> P -> A) t f) a'). Qed.
Lemma lem8244203 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (t f a') = (term933 A B P t f a').
Proof. exact (TRANS (@lem8244197 A B P t f a') (@lem8244201 A B P t f a')). Qed.
Lemma lem8244210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244211 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244210 (A -> B) (P -> A) f x). Qed.
Lemma lem8244212 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> A) t g).
Proof. exact (@lem8244211 A B P t g). Qed.
Lemma lem8244213 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244214 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (t g a') = (@I ((A -> B) -> P -> A) t g a').
Proof. exact (MK_COMB (@lem8244212 A B P t g) (@lem8244213 P a')). Qed.
Lemma lem8244216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244217 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244216 P A f x). Qed.
Lemma lem8244218 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (@I ((A -> B) -> P -> A) t g a') = (term933 A B P t g a').
Proof. exact (@lem8244217 A P (@I ((A -> B) -> P -> A) t g) a'). Qed.
Lemma lem8244220 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a' : P) : (t g a') = (term933 A B P t g a').
Proof. exact (TRANS (@lem8244214 A B P t g a') (@lem8244218 A B P t g a')). Qed.
Lemma lem8244221 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a' : P) : (term299 A B P t f a') = (term952 A B P t f a').
Proof. exact (MK_COMB (@lem8244186 A) (@lem8244203 A B P t f a')). Qed.
Lemma lem8244222 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : ((t f a') = (t g a')) = ((term933 A B P t f a') = (term933 A B P t g a')).
Proof. exact (MK_COMB (@lem8244221 A B P t f a') (@lem8244220 A B P t g a')). Qed.
Lemma lem8244223 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term688 A B P f t g a') = (term973 A B P f t g a').
Proof. exact (MK_COMB (@lem8244185) (@lem8244222 A B P f t g a')). Qed.
Lemma lem8244224 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8244229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244230 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244229 A B f x). Qed.
Lemma lem8244232 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8244230 A B f z). Qed.
Lemma lem8244237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244237 A B f x). Qed.
Lemma lem8244240 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8244238 A B g z). Qed.
Lemma lem8244241 {A B : Type'} (f : A -> B) (z : A) : (term954 A B f z) = (term955 A B f z).
Proof. exact (MK_COMB (@lem8244224 B) (@lem8244232 A B f z)). Qed.
Lemma lem8244242 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8244241 A B f z) (@lem8244240 A B g z)). Qed.
Lemma lem8244243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244251 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244250 P A f x). Qed.
Lemma lem8244253 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8244251 A P s a'). Qed.
Lemma lem8244254 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8244255 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term930 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244254 A lt2 z) (@lem8244253 A P s a')). Qed.
Lemma lem8244257 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244258 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244257 A (A -> Prop) f x). Qed.
Lemma lem8244259 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8244258 A lt2 z). Qed.
Lemma lem8244260 {A P : Type'} (s : P -> A) (a' : P) : (@I (P -> A) s a') = (@I (P -> A) s a').
Proof. exact (eq_refl (@I (P -> A) s a')). Qed.
Lemma lem8244261 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term931 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244259 A lt2 z) (@lem8244260 A P s a')). Qed.
Lemma lem8244263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244264 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244263 A Prop f x). Qed.
Lemma lem8244265 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term931 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (@lem8244264 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a')). Qed.
Lemma lem8244266 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term930 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244261 A P lt2 z s a') (@lem8244265 A P lt2 z s a')). Qed.
Lemma lem8244267 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term171 A P lt2 z s a') = (term932 A P lt2 z s a').
Proof. exact (TRANS (@lem8244255 A P lt2 z s a') (@lem8244266 A P lt2 z s a')). Qed.
Lemma lem8244268 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term956 A P lt2 z s a') = (term957 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244243) (@lem8244267 A P lt2 z s a')). Qed.
Lemma lem8244269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244270 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a' : P) : (term958 A P lt2 z s a') = (term959 A P lt2 z s a').
Proof. exact (MK_COMB (@lem8244269) (@lem8244268 A P lt2 z s a')). Qed.
Lemma lem8244271 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term685 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (MK_COMB (@lem8244270 A P lt2 z s a') (@lem8244242 A B f g z)). Qed.
Lemma lem8244272 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term686 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8244271 A B P lt2 s a' f g z)). Qed.
Lemma lem8244273 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244274 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term687 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244273 A) (@lem8244272 A B P lt2 s a' f g)). Qed.
Lemma lem8244275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244276 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term690 A B P lt2 s a' f g) = (term963 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8244275) (@lem8244274 A B P lt2 s a' f g)). Qed.
Lemma lem8244277 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term692 A B P lt2 s f t g a') = (term974 A B P lt2 s f t g a').
Proof. exact (MK_COMB (@lem8244276 A B P lt2 s a' f g) (@lem8244223 A B P f t g a')). Qed.
Lemma lem8244284 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244285 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244284 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244286 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244285 A B P p f). Qed.
Lemma lem8244287 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244288 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (@I ((A -> B) -> P -> Prop) p f a').
Proof. exact (MK_COMB (@lem8244286 A B P p f) (@lem8244287 P a')). Qed.
Lemma lem8244290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244291 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244290 P Prop f x). Qed.
Lemma lem8244292 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (@I ((A -> B) -> P -> Prop) p f a') = (term944 A B P p f a').
Proof. exact (@lem8244291 P (@I ((A -> B) -> P -> Prop) p f) a'). Qed.
Lemma lem8244294 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (p f a') = (term944 A B P p f a').
Proof. exact (TRANS (@lem8244288 A B P p f a') (@lem8244292 A B P p f a')). Qed.
Lemma lem8244295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244296 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term370 A B P p f a') = (term965 A B P p f a').
Proof. exact (MK_COMB (@lem8244295) (@lem8244294 A B P p f a')). Qed.
Lemma lem8244297 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term695 A B P p lt2 s f t g a') = (term975 A B P p lt2 s f t g a').
Proof. exact (MK_COMB (@lem8244296 A B P p f a') (@lem8244277 A B P lt2 s f t g a')). Qed.
Lemma lem8244298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244299 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term706 A B P p lt2 s f t g a') = (term976 A B P p lt2 s f t g a').
Proof. exact (MK_COMB (@lem8244298) (@lem8244297 A B P p lt2 s f t g a')). Qed.
Lemma lem8244300 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term708 A B P p lt2 f s t g a') = (term977 A B P p lt2 f s t g a').
Proof. exact (MK_COMB (@lem8244299 A B P p lt2 s f t g a') (@lem8244184 A B P p lt2 f s t g a')). Qed.
Lemma lem8244307 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244308 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244307 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244309 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8244308 A B P p g). Qed.
Lemma lem8244310 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8244311 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (p g a') = (@I ((A -> B) -> P -> Prop) p g a').
Proof. exact (MK_COMB (@lem8244309 A B P p g) (@lem8244310 P a')). Qed.
Lemma lem8244313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244314 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244313 P Prop f x). Qed.
Lemma lem8244315 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (@I ((A -> B) -> P -> Prop) p g a') = (term944 A B P p g a').
Proof. exact (@lem8244314 P (@I ((A -> B) -> P -> Prop) p g) a'). Qed.
Lemma lem8244317 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (p g a') = (term944 A B P p g a').
Proof. exact (TRANS (@lem8244311 A B P p g a') (@lem8244315 A B P p g a')). Qed.
Lemma lem8244318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244319 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term370 A B P p g a') = (term965 A B P p g a').
Proof. exact (MK_COMB (@lem8244318) (@lem8244317 A B P p g a')). Qed.
Lemma lem8244320 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term711 A B P p lt2 f s t g a') = (term978 A B P p lt2 f s t g a').
Proof. exact (MK_COMB (@lem8244319 A B P p g a') (@lem8244300 A B P p lt2 f s t g a')). Qed.
Lemma lem8244321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244322 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) : (term724 A B P p lt2 f s t g a') = (term979 A B P p lt2 f s t g a').
Proof. exact (MK_COMB (@lem8244321) (@lem8244320 A B P p lt2 f s t g a')). Qed.
Lemma lem8244323 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term726 A B P p lt2 g t f s a') = (term980 A B P p lt2 g t f s a').
Proof. exact (MK_COMB (@lem8244322 A B P p lt2 f s t g a') (@lem8244078 A B P p lt2 g t f s a')). Qed.
Lemma lem8244324 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244332 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244331 P A f x). Qed.
Lemma lem8244334 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8244332 A P s a). Qed.
Lemma lem8244335 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8244336 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term930 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8244335 A lt2 y) (@lem8244334 A P s a)). Qed.
Lemma lem8244338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244339 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244338 A (A -> Prop) f x). Qed.
Lemma lem8244340 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem8244339 A lt2 y). Qed.
Lemma lem8244341 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8244342 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term930 A P lt2 y s a) = (term931 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8244340 A lt2 y) (@lem8244341 A P s a)). Qed.
Lemma lem8244344 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244345 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244344 A Prop f x). Qed.
Lemma lem8244346 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term931 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (@lem8244345 A (@I (A -> A -> Prop) lt2 y) (@I (P -> A) s a)). Qed.
Lemma lem8244347 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term930 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (TRANS (@lem8244342 A P lt2 y s a) (@lem8244346 A P lt2 y s a)). Qed.
Lemma lem8244348 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term171 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (TRANS (@lem8244336 A P lt2 y s a) (@lem8244347 A P lt2 y s a)). Qed.
Lemma lem8244349 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term956 A P lt2 y s a) = (term957 A P lt2 y s a).
Proof. exact (MK_COMB (@lem8244324) (@lem8244348 A P lt2 y s a)). Qed.
Lemma lem8244358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244359 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244358 (A -> B) (P -> A) f x). Qed.
Lemma lem8244360 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8244359 A B P t f). Qed.
Lemma lem8244361 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244362 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8244360 A B P t f) (@lem8244361 P a)). Qed.
Lemma lem8244364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244365 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244364 P A f x). Qed.
Lemma lem8244366 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term933 A B P t f a).
Proof. exact (@lem8244365 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8244368 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term933 A B P t f a).
Proof. exact (TRANS (@lem8244362 A B P t f a) (@lem8244366 A B P t f a)). Qed.
Lemma lem8244369 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (lt2 y).
Proof. exact (eq_refl (lt2 y)). Qed.
Lemma lem8244370 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term345 A B P lt2 y t f a) = (term934 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8244369 A lt2 y) (@lem8244368 A B P t f a)). Qed.
Lemma lem8244372 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244373 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244372 A (A -> Prop) f x). Qed.
Lemma lem8244374 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem8244373 A lt2 y). Qed.
Lemma lem8244375 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term933 A B P t f a) = (term933 A B P t f a).
Proof. exact (eq_refl (term933 A B P t f a)). Qed.
Lemma lem8244376 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term934 A B P lt2 y t f a) = (term935 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8244374 A lt2 y) (@lem8244375 A B P t f a)). Qed.
Lemma lem8244378 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244379 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244378 A Prop f x). Qed.
Lemma lem8244380 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term935 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (@lem8244379 A (@I (A -> A -> Prop) lt2 y) (term933 A B P t f a)). Qed.
Lemma lem8244381 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term934 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (TRANS (@lem8244376 A B P lt2 y t f a) (@lem8244380 A B P lt2 y t f a)). Qed.
Lemma lem8244382 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term345 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (TRANS (@lem8244370 A B P lt2 y t f a) (@lem8244381 A B P lt2 y t f a)). Qed.
Lemma lem8244383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244384 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term981 A B P lt2 y t f a) = (term982 A B P lt2 y t f a).
Proof. exact (MK_COMB (@lem8244383) (@lem8244382 A B P lt2 y t f a)). Qed.
Lemma lem8244385 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term657 A B P t f lt2 y s a) = (term983 A B P t f lt2 y s a).
Proof. exact (MK_COMB (@lem8244384 A B P lt2 y t f a) (@lem8244349 A P lt2 y s a)). Qed.
Lemma lem8244392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244393 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244392 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244394 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244393 A B P p f). Qed.
Lemma lem8244395 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244396 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8244394 A B P p f) (@lem8244395 P a)). Qed.
Lemma lem8244398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244399 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244398 P Prop f x). Qed.
Lemma lem8244400 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term944 A B P p f a).
Proof. exact (@lem8244399 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8244402 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term944 A B P p f a).
Proof. exact (TRANS (@lem8244396 A B P p f a) (@lem8244400 A B P p f a)). Qed.
Lemma lem8244403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244404 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term370 A B P p f a) = (term965 A B P p f a).
Proof. exact (MK_COMB (@lem8244403) (@lem8244402 A B P p f a)). Qed.
Lemma lem8244405 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term832 A B P p t f lt2 y s a) = (term984 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8244404 A B P p f a) (@lem8244385 A B P t f lt2 y s a)). Qed.
Lemma lem8244406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244407 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term890 A B P p t f lt2 y s a) = (term985 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8244406) (@lem8244405 A B P p t f lt2 y s a)). Qed.
Lemma lem8244408 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) : (term918 A B P y a p lt2 g t f s a') = (term986 A B P y a p lt2 g t f s a').
Proof. exact (MK_COMB (@lem8244407 A B P p t f lt2 y s a) (@lem8244323 A B P p lt2 g t f s a')). Qed.
Lemma lem8244409 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term918 A B P y a p lt2 g t f s a') : term986 A B P y a p lt2 g t f s a'.
Proof. exact (EQ_MP (@lem8244408 A B P y a p lt2 g t f s a') (@lem8243856 A B P y a p lt2 g t f s a' h1)). Qed.
Lemma lem8244416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244417 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244416 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244418 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8244417 A B P p g). Qed.
Lemma lem8244419 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244420 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8244418 A B P p g) (@lem8244419 P a)). Qed.
Lemma lem8244422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244423 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244422 P Prop f x). Qed.
Lemma lem8244424 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term944 A B P p g a).
Proof. exact (@lem8244423 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8244426 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term944 A B P p g a).
Proof. exact (TRANS (@lem8244420 A B P p g a) (@lem8244424 A B P p g a)). Qed.
Lemma lem8244427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244435 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244434 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244436 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244435 A B P p f). Qed.
Lemma lem8244437 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244438 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8244436 A B P p f) (@lem8244437 P a)). Qed.
Lemma lem8244440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244441 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244440 P Prop f x). Qed.
Lemma lem8244442 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term944 A B P p f a).
Proof. exact (@lem8244441 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8244444 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term944 A B P p f a).
Proof. exact (TRANS (@lem8244438 A B P p f a) (@lem8244442 A B P p f a)). Qed.
Lemma lem8244445 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term292 A B P p f a) = (term945 A B P p f a).
Proof. exact (MK_COMB (@lem8244427) (@lem8244444 A B P p f a)). Qed.
Lemma lem8244446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244447 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term946 A B P p f a).
Proof. exact (MK_COMB (@lem8244446) (@lem8244445 A B P p f a)). Qed.
Lemma lem8244448 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term987 A B P f p g a) = (term988 A B P f p g a).
Proof. exact (MK_COMB (@lem8244447 A B P p f a) (@lem8244426 A B P p g a)). Qed.
Lemma lem8244449 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244456 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244457 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244456 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244458 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8244457 A B P p g). Qed.
Lemma lem8244459 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244460 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8244458 A B P p g) (@lem8244459 P a)). Qed.
Lemma lem8244462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244463 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244462 P Prop f x). Qed.
Lemma lem8244464 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term944 A B P p g a).
Proof. exact (@lem8244463 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8244466 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term944 A B P p g a).
Proof. exact (TRANS (@lem8244460 A B P p g a) (@lem8244464 A B P p g a)). Qed.
Lemma lem8244467 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term292 A B P p g a) = (term945 A B P p g a).
Proof. exact (MK_COMB (@lem8244449) (@lem8244466 A B P p g a)). Qed.
Lemma lem8244474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244475 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244474 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244476 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244475 A B P p f). Qed.
Lemma lem8244477 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244478 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8244476 A B P p f) (@lem8244477 P a)). Qed.
Lemma lem8244480 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244481 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244480 P Prop f x). Qed.
Lemma lem8244482 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term944 A B P p f a).
Proof. exact (@lem8244481 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8244484 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term944 A B P p f a).
Proof. exact (TRANS (@lem8244478 A B P p f a) (@lem8244482 A B P p f a)). Qed.
Lemma lem8244485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244486 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term312 A B P p f a) = (term989 A B P p f a).
Proof. exact (MK_COMB (@lem8244485) (@lem8244484 A B P p f a)). Qed.
Lemma lem8244487 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term990 A B P f p g a) = (term991 A B P f p g a).
Proof. exact (MK_COMB (@lem8244486 A B P p f a) (@lem8244467 A B P p g a)). Qed.
Lemma lem8244488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244489 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term992 A B P f p g a) = (term993 A B P f p g a).
Proof. exact (MK_COMB (@lem8244488) (@lem8244487 A B P f p g a)). Qed.
Lemma lem8244490 {A B P : Type'} (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term563 A B P f p g a) = (term994 A B P f p g a).
Proof. exact (MK_COMB (@lem8244489 A B P f p g a) (@lem8244448 A B P f p g a)). Qed.
Lemma lem8244491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244492 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8244493 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8244502 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244503 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244502 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244504 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8244503 A B P z f). Qed.
Lemma lem8244505 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244506 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8244504 A B P z f) (@lem8244505 A B g)). Qed.
Lemma lem8244508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244509 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244508 (A -> B) (P -> A) f x). Qed.
Lemma lem8244510 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term995 A B P z f g).
Proof. exact (@lem8244509 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8244511 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term995 A B P z f g).
Proof. exact (TRANS (@lem8244506 A B P z f g) (@lem8244510 A B P z f g)). Qed.
Lemma lem8244512 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244513 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term996 A B P z f g a).
Proof. exact (MK_COMB (@lem8244511 A B P z f g) (@lem8244512 P a)). Qed.
Lemma lem8244515 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244516 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244515 P A f x). Qed.
Lemma lem8244517 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z f g a) = (term997 A B P z f g a).
Proof. exact (@lem8244516 A P (term995 A B P z f g) a). Qed.
Lemma lem8244519 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term997 A B P z f g a).
Proof. exact (TRANS (@lem8244513 A B P z f g a) (@lem8244517 A B P z f g a)). Qed.
Lemma lem8244520 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term998 A B P z f g a) = (term999 A B P z f g a).
Proof. exact (MK_COMB (@lem8244493 A B f) (@lem8244519 A B P z f g a)). Qed.
Lemma lem8244522 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244522 A B f x). Qed.
Lemma lem8244524 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term999 A B P z f g a) = (term1000 A B P z f g a).
Proof. exact (@lem8244523 A B f (term997 A B P z f g a)). Qed.
Lemma lem8244525 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term998 A B P z f g a) = (term1000 A B P z f g a).
Proof. exact (TRANS (@lem8244520 A B P z f g a) (@lem8244524 A B P z f g a)). Qed.
Lemma lem8244526 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244535 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244536 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244535 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244537 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8244536 A B P z f). Qed.
Lemma lem8244538 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244539 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8244537 A B P z f) (@lem8244538 A B g)). Qed.
Lemma lem8244541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244542 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244541 (A -> B) (P -> A) f x). Qed.
Lemma lem8244543 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term995 A B P z f g).
Proof. exact (@lem8244542 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8244544 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term995 A B P z f g).
Proof. exact (TRANS (@lem8244539 A B P z f g) (@lem8244543 A B P z f g)). Qed.
Lemma lem8244545 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244546 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term996 A B P z f g a).
Proof. exact (MK_COMB (@lem8244544 A B P z f g) (@lem8244545 P a)). Qed.
Lemma lem8244548 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244549 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244548 P A f x). Qed.
Lemma lem8244550 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z f g a) = (term997 A B P z f g a).
Proof. exact (@lem8244549 A P (term995 A B P z f g) a). Qed.
Lemma lem8244552 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term997 A B P z f g a).
Proof. exact (TRANS (@lem8244546 A B P z f g a) (@lem8244550 A B P z f g a)). Qed.
Lemma lem8244553 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1001 A B P z f g a) = (term1002 A B P z f g a).
Proof. exact (MK_COMB (@lem8244526 A B g) (@lem8244552 A B P z f g a)). Qed.
Lemma lem8244555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244556 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244555 A B f x). Qed.
Lemma lem8244557 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1002 A B P z f g a) = (term1003 A B P z f g a).
Proof. exact (@lem8244556 A B g (term997 A B P z f g a)). Qed.
Lemma lem8244558 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1001 A B P z f g a) = (term1003 A B P z f g a).
Proof. exact (TRANS (@lem8244553 A B P z f g a) (@lem8244557 A B P z f g a)). Qed.
Lemma lem8244559 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1004 A B P z f g a) = (term1005 A B P z f g a).
Proof. exact (MK_COMB (@lem8244492 B) (@lem8244525 A B P z f g a)). Qed.
Lemma lem8244560 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term998 A B P z f g a) = (term1001 A B P z f g a)) = ((term1000 A B P z f g a) = (term1003 A B P z f g a)).
Proof. exact (MK_COMB (@lem8244559 A B P z f g a) (@lem8244558 A B P z f g a)). Qed.
Lemma lem8244561 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1006 A B P z f g a) = (term1007 A B P z f g a).
Proof. exact (MK_COMB (@lem8244491) (@lem8244560 A B P z f g a)). Qed.
Lemma lem8244562 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8244571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244572 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244571 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244573 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8244572 A B P z f). Qed.
Lemma lem8244574 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244575 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8244573 A B P z f) (@lem8244574 A B g)). Qed.
Lemma lem8244577 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244578 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244577 (A -> B) (P -> A) f x). Qed.
Lemma lem8244579 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term995 A B P z f g).
Proof. exact (@lem8244578 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8244580 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term995 A B P z f g).
Proof. exact (TRANS (@lem8244575 A B P z f g) (@lem8244579 A B P z f g)). Qed.
Lemma lem8244581 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244582 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term996 A B P z f g a).
Proof. exact (MK_COMB (@lem8244580 A B P z f g) (@lem8244581 P a)). Qed.
Lemma lem8244584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244585 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244584 P A f x). Qed.
Lemma lem8244586 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z f g a) = (term997 A B P z f g a).
Proof. exact (@lem8244585 A P (term995 A B P z f g) a). Qed.
Lemma lem8244588 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term997 A B P z f g a).
Proof. exact (TRANS (@lem8244582 A B P z f g a) (@lem8244586 A B P z f g a)). Qed.
Lemma lem8244593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244594 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244593 P A f x). Qed.
Lemma lem8244596 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8244594 A P s a). Qed.
Lemma lem8244597 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1008 A B P lt2 z f g a) = (term1009 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8244562 A lt2) (@lem8244588 A B P z f g a)). Qed.
Lemma lem8244598 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1010 A B P lt2 z f g s a) = (term1011 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8244597 A B P lt2 z f g a) (@lem8244596 A P s a)). Qed.
Lemma lem8244600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244601 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244600 A (A -> Prop) f x). Qed.
Lemma lem8244602 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1009 A B P lt2 z f g a) = (term1012 A B P lt2 z f g a).
Proof. exact (@lem8244601 A lt2 (term997 A B P z f g a)). Qed.
Lemma lem8244603 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8244604 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1011 A B P lt2 z f g s a) = (term1013 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8244602 A B P lt2 z f g a) (@lem8244603 A P s a)). Qed.
Lemma lem8244606 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244607 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244606 A Prop f x). Qed.
Lemma lem8244608 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1013 A B P lt2 z f g s a) = (term1014 A B P lt2 z f g s a).
Proof. exact (@lem8244607 A (term1012 A B P lt2 z f g a) (@I (P -> A) s a)). Qed.
Lemma lem8244609 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1011 A B P lt2 z f g s a) = (term1014 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8244604 A B P lt2 z f g s a) (@lem8244608 A B P lt2 z f g s a)). Qed.
Lemma lem8244610 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1010 A B P lt2 z f g s a) = (term1014 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8244598 A B P lt2 z f g s a) (@lem8244609 A B P lt2 z f g s a)). Qed.
Lemma lem8244611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244612 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1015 A B P lt2 z f g s a) = (term1016 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8244611) (@lem8244610 A B P lt2 z f g s a)). Qed.
Lemma lem8244613 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1017 A B P lt2 s z f g a) = (term1018 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8244612 A B P lt2 z f g s a) (@lem8244561 A B P z f g a)). Qed.
Lemma lem8244614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244615 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1019 A B P lt2 s z f g a) = (term1020 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8244614) (@lem8244613 A B P lt2 s z f g a)). Qed.
Lemma lem8244616 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1021 A B P lt2 s z f p g a) = (term1022 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8244615 A B P lt2 s z f g a) (@lem8244490 A B P f p g a)). Qed.
Lemma lem8244617 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1023 A B P lt2 s z f p g) = (term1024 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8244616 A B P lt2 s z f p g a)). Qed.
Lemma lem8244618 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8244619 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1025 A B P lt2 s z f p g) = (term1026 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8244618 P) (@lem8244617 A B P lt2 s z f p g)). Qed.
Lemma lem8244620 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term1027 A B P lt2 s z f p) = (term1028 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8244619 A B P lt2 s z f p g)). Qed.
Lemma lem8244621 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244622 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term647 A B P lt2 s z f p) = (term1029 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8244621 A B) (@lem8244620 A B P lt2 s z f p)). Qed.
Lemma lem8244623 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term649 A B P lt2 s z p) = (term1030 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8244622 A B P lt2 s z f p)). Qed.
Lemma lem8244624 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244625 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term651 A B P lt2 s z p) = (term1031 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8244624 A B) (@lem8244623 A B P lt2 s z p)). Qed.
Lemma lem8244626 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1031 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8244625 A B P lt2 s z p) (@lem8243857 A B P lt2 s z p h1)). Qed.
Lemma lem8244627 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8244634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244635 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244634 (A -> B) (P -> A) f x). Qed.
Lemma lem8244636 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8244635 A B P t f). Qed.
Lemma lem8244637 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244638 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8244636 A B P t f) (@lem8244637 P a)). Qed.
Lemma lem8244640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244641 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244640 P A f x). Qed.
Lemma lem8244642 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term933 A B P t f a).
Proof. exact (@lem8244641 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8244644 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term933 A B P t f a).
Proof. exact (TRANS (@lem8244638 A B P t f a) (@lem8244642 A B P t f a)). Qed.
Lemma lem8244651 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244652 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244651 (A -> B) (P -> A) f x). Qed.
Lemma lem8244653 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> A) t g).
Proof. exact (@lem8244652 A B P t g). Qed.
Lemma lem8244654 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244655 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> A) t g a).
Proof. exact (MK_COMB (@lem8244653 A B P t g) (@lem8244654 P a)). Qed.
Lemma lem8244657 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244658 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244657 P A f x). Qed.
Lemma lem8244659 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t g a) = (term933 A B P t g a).
Proof. exact (@lem8244658 A P (@I ((A -> B) -> P -> A) t g) a). Qed.
Lemma lem8244661 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (term933 A B P t g a).
Proof. exact (TRANS (@lem8244655 A B P t g a) (@lem8244659 A B P t g a)). Qed.
Lemma lem8244662 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term299 A B P t f a) = (term952 A B P t f a).
Proof. exact (MK_COMB (@lem8244627 A) (@lem8244644 A B P t f a)). Qed.
Lemma lem8244663 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((term933 A B P t f a) = (term933 A B P t g a)).
Proof. exact (MK_COMB (@lem8244662 A B P t f a) (@lem8244661 A B P t g a)). Qed.
Lemma lem8244664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244665 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8244666 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8244675 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244676 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244675 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244677 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8244676 A B P z' f). Qed.
Lemma lem8244678 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244679 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8244677 A B P z' f) (@lem8244678 A B g)). Qed.
Lemma lem8244681 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244682 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244681 (A -> B) (P -> A) f x). Qed.
Lemma lem8244683 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term995 A B P z' f g).
Proof. exact (@lem8244682 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8244684 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term995 A B P z' f g).
Proof. exact (TRANS (@lem8244679 A B P z' f g) (@lem8244683 A B P z' f g)). Qed.
Lemma lem8244685 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244686 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term996 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244684 A B P z' f g) (@lem8244685 P a)). Qed.
Lemma lem8244688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244689 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244688 P A f x). Qed.
Lemma lem8244690 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z' f g a) = (term997 A B P z' f g a).
Proof. exact (@lem8244689 A P (term995 A B P z' f g) a). Qed.
Lemma lem8244692 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term997 A B P z' f g a).
Proof. exact (TRANS (@lem8244686 A B P z' f g a) (@lem8244690 A B P z' f g a)). Qed.
Lemma lem8244693 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term998 A B P z' f g a) = (term999 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244666 A B f) (@lem8244692 A B P z' f g a)). Qed.
Lemma lem8244695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244695 A B f x). Qed.
Lemma lem8244697 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term999 A B P z' f g a) = (term1000 A B P z' f g a).
Proof. exact (@lem8244696 A B f (term997 A B P z' f g a)). Qed.
Lemma lem8244698 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term998 A B P z' f g a) = (term1000 A B P z' f g a).
Proof. exact (TRANS (@lem8244693 A B P z' f g a) (@lem8244697 A B P z' f g a)). Qed.
Lemma lem8244699 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244709 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244708 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244710 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8244709 A B P z' f). Qed.
Lemma lem8244711 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244712 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8244710 A B P z' f) (@lem8244711 A B g)). Qed.
Lemma lem8244714 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244715 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244714 (A -> B) (P -> A) f x). Qed.
Lemma lem8244716 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term995 A B P z' f g).
Proof. exact (@lem8244715 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8244717 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term995 A B P z' f g).
Proof. exact (TRANS (@lem8244712 A B P z' f g) (@lem8244716 A B P z' f g)). Qed.
Lemma lem8244718 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244719 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term996 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244717 A B P z' f g) (@lem8244718 P a)). Qed.
Lemma lem8244721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244722 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244721 P A f x). Qed.
Lemma lem8244723 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z' f g a) = (term997 A B P z' f g a).
Proof. exact (@lem8244722 A P (term995 A B P z' f g) a). Qed.
Lemma lem8244725 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term997 A B P z' f g a).
Proof. exact (TRANS (@lem8244719 A B P z' f g a) (@lem8244723 A B P z' f g a)). Qed.
Lemma lem8244726 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1001 A B P z' f g a) = (term1002 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244699 A B g) (@lem8244725 A B P z' f g a)). Qed.
Lemma lem8244728 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8244728 A B f x). Qed.
Lemma lem8244730 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1002 A B P z' f g a) = (term1003 A B P z' f g a).
Proof. exact (@lem8244729 A B g (term997 A B P z' f g a)). Qed.
Lemma lem8244731 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1001 A B P z' f g a) = (term1003 A B P z' f g a).
Proof. exact (TRANS (@lem8244726 A B P z' f g a) (@lem8244730 A B P z' f g a)). Qed.
Lemma lem8244732 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1004 A B P z' f g a) = (term1005 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244665 B) (@lem8244698 A B P z' f g a)). Qed.
Lemma lem8244733 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term998 A B P z' f g a) = (term1001 A B P z' f g a)) = ((term1000 A B P z' f g a) = (term1003 A B P z' f g a)).
Proof. exact (MK_COMB (@lem8244732 A B P z' f g a) (@lem8244731 A B P z' f g a)). Qed.
Lemma lem8244734 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1006 A B P z' f g a) = (term1007 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244664) (@lem8244733 A B P z' f g a)). Qed.
Lemma lem8244735 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8244744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244745 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8244744 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8244746 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8244745 A B P z' f). Qed.
Lemma lem8244747 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8244748 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8244746 A B P z' f) (@lem8244747 A B g)). Qed.
Lemma lem8244750 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244751 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8244750 (A -> B) (P -> A) f x). Qed.
Lemma lem8244752 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term995 A B P z' f g).
Proof. exact (@lem8244751 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8244753 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term995 A B P z' f g).
Proof. exact (TRANS (@lem8244748 A B P z' f g) (@lem8244752 A B P z' f g)). Qed.
Lemma lem8244754 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244755 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term996 A B P z' f g a).
Proof. exact (MK_COMB (@lem8244753 A B P z' f g) (@lem8244754 P a)). Qed.
Lemma lem8244757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244758 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244757 P A f x). Qed.
Lemma lem8244759 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term996 A B P z' f g a) = (term997 A B P z' f g a).
Proof. exact (@lem8244758 A P (term995 A B P z' f g) a). Qed.
Lemma lem8244761 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term997 A B P z' f g a).
Proof. exact (TRANS (@lem8244755 A B P z' f g a) (@lem8244759 A B P z' f g a)). Qed.
Lemma lem8244766 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244767 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8244766 P A f x). Qed.
Lemma lem8244769 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8244767 A P s a). Qed.
Lemma lem8244770 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1008 A B P lt2 z' f g a) = (term1009 A B P lt2 z' f g a).
Proof. exact (MK_COMB (@lem8244735 A lt2) (@lem8244761 A B P z' f g a)). Qed.
Lemma lem8244771 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1010 A B P lt2 z' f g s a) = (term1011 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8244770 A B P lt2 z' f g a) (@lem8244769 A P s a)). Qed.
Lemma lem8244773 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244774 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8244773 A (A -> Prop) f x). Qed.
Lemma lem8244775 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1009 A B P lt2 z' f g a) = (term1012 A B P lt2 z' f g a).
Proof. exact (@lem8244774 A lt2 (term997 A B P z' f g a)). Qed.
Lemma lem8244776 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8244777 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1011 A B P lt2 z' f g s a) = (term1013 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8244775 A B P lt2 z' f g a) (@lem8244776 A P s a)). Qed.
Lemma lem8244779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244780 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8244779 A Prop f x). Qed.
Lemma lem8244781 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1013 A B P lt2 z' f g s a) = (term1014 A B P lt2 z' f g s a).
Proof. exact (@lem8244780 A (term1012 A B P lt2 z' f g a) (@I (P -> A) s a)). Qed.
Lemma lem8244782 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1011 A B P lt2 z' f g s a) = (term1014 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8244777 A B P lt2 z' f g s a) (@lem8244781 A B P lt2 z' f g s a)). Qed.
Lemma lem8244783 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1010 A B P lt2 z' f g s a) = (term1014 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8244771 A B P lt2 z' f g s a) (@lem8244782 A B P lt2 z' f g s a)). Qed.
Lemma lem8244784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8244785 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term1015 A B P lt2 z' f g s a) = (term1016 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8244784) (@lem8244783 A B P lt2 z' f g s a)). Qed.
Lemma lem8244786 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1017 A B P lt2 s z' f g a) = (term1018 A B P lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8244785 A B P lt2 z' f g s a) (@lem8244734 A B P z' f g a)). Qed.
Lemma lem8244787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244795 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244794 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244796 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8244795 A B P p g). Qed.
Lemma lem8244797 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244798 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8244796 A B P p g) (@lem8244797 P a)). Qed.
Lemma lem8244800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244801 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244800 P Prop f x). Qed.
Lemma lem8244802 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term944 A B P p g a).
Proof. exact (@lem8244801 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8244804 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term944 A B P p g a).
Proof. exact (TRANS (@lem8244798 A B P p g a) (@lem8244802 A B P p g a)). Qed.
Lemma lem8244805 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term292 A B P p g a) = (term945 A B P p g a).
Proof. exact (MK_COMB (@lem8244787) (@lem8244804 A B P p g a)). Qed.
Lemma lem8244806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244807 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term306 A B P p g a) = (term946 A B P p g a).
Proof. exact (MK_COMB (@lem8244806) (@lem8244805 A B P p g a)). Qed.
Lemma lem8244808 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1032 A B P p lt2 s z' f g a) = (term1033 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8244807 A B P p g a) (@lem8244786 A B P lt2 s z' f g a)). Qed.
Lemma lem8244809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8244816 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244817 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8244816 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8244818 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8244817 A B P p f). Qed.
Lemma lem8244819 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8244820 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8244818 A B P p f) (@lem8244819 P a)). Qed.
Lemma lem8244822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8244823 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8244822 P Prop f x). Qed.
Lemma lem8244824 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term944 A B P p f a).
Proof. exact (@lem8244823 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8244826 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term944 A B P p f a).
Proof. exact (TRANS (@lem8244820 A B P p f a) (@lem8244824 A B P p f a)). Qed.
Lemma lem8244827 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term292 A B P p f a) = (term945 A B P p f a).
Proof. exact (MK_COMB (@lem8244809) (@lem8244826 A B P p f a)). Qed.
Lemma lem8244828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244829 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term306 A B P p f a) = (term946 A B P p f a).
Proof. exact (MK_COMB (@lem8244828) (@lem8244827 A B P p f a)). Qed.
Lemma lem8244830 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1034 A B P p lt2 s z' f g a) = (term1035 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8244829 A B P p f a) (@lem8244808 A B P p lt2 s z' f g a)). Qed.
Lemma lem8244831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8244832 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1036 A B P p lt2 s z' f g a) = (term1037 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8244831) (@lem8244830 A B P p lt2 s z' f g a)). Qed.
Lemma lem8244833 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term1038 A B P p lt2 s z' f t g a) = (term1039 A B P p lt2 s z' f t g a).
Proof. exact (MK_COMB (@lem8244832 A B P p lt2 s z' f g a) (@lem8244663 A B P f t g a)). Qed.
Lemma lem8244834 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term1040 A B P p lt2 s z' f t g) = (term1041 A B P p lt2 s z' f t g).
Proof. exact (fun_ext (fun a : P => @lem8244833 A B P p lt2 s z' f t g a)). Qed.
Lemma lem8244835 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8244836 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term1042 A B P p lt2 s z' f t g) = (term1043 A B P p lt2 s z' f t g).
Proof. exact (MK_COMB (@lem8244835 P) (@lem8244834 A B P p lt2 s z' f t g)). Qed.
Lemma lem8244837 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) : (term1044 A B P p lt2 s z' f t) = (term1045 A B P p lt2 s z' f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8244836 A B P p lt2 s z' f t g)). Qed.
Lemma lem8244838 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244839 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) : (term547 A B P p lt2 s z' f t) = (term1046 A B P p lt2 s z' f t).
Proof. exact (MK_COMB (@lem8244838 A B) (@lem8244837 A B P p lt2 s z' f t)). Qed.
Lemma lem8244840 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) : (term549 A B P p lt2 s z' t) = (term1047 A B P p lt2 s z' t).
Proof. exact (fun_ext (fun f : A -> B => @lem8244839 A B P p lt2 s z' f t)). Qed.
Lemma lem8244841 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244842 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) : (term551 A B P p lt2 s z' t) = (term1048 A B P p lt2 s z' t).
Proof. exact (MK_COMB (@lem8244841 A B) (@lem8244840 A B P p lt2 s z' t)). Qed.
Lemma lem8244843 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1048 A B P p lt2 s z' t.
Proof. exact (EQ_MP (@lem8244842 A B P p lt2 s z' t) (@lem8243858 A B P p lt2 s z' t h1)). Qed.
Lemma lem8244844 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term984 A B P p t f lt2 y s a.
Proof. exact (h1). Qed.
Lemma lem8244845 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term980 A B P p lt2 g t f s a') : term980 A B P p lt2 g t f s a'.
Proof. exact (h1). Qed.
Lemma lem8244846 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term983 A B P t f lt2 y s a.
Proof. exact (proj2 (@lem8244844 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8244850 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term978 A B P p lt2 f s t g a'.
Proof. exact (h1). Qed.
Lemma lem8244851 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term968 A B P p lt2 g t f s a'.
Proof. exact (h1). Qed.
Lemma lem8244852 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term977 A B P p lt2 f s t g a'.
Proof. exact (proj2 (@lem8244850 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8244854 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term975 A B P p lt2 s f t g a'.
Proof. exact (h1). Qed.
Lemma lem8244855 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term972 A B P p lt2 f s t g a'.
Proof. exact (h1). Qed.
Lemma lem8244856 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term974 A B P lt2 s f t g a'.
Proof. exact (proj2 (@lem8244854 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8244859 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term962 A B P lt2 s a' f g.
Proof. exact (proj1 (@lem8244856 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8244860 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term971 A B P lt2 f s t g a'.
Proof. exact (proj2 (@lem8244855 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8244863 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term962 A B P lt2 s a' f g.
Proof. exact (proj1 (@lem8244860 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8244864 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term966 A B P p lt2 g t f s a'.
Proof. exact (proj2 (@lem8244851 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8244866 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term964 A B P lt2 g t f s a'.
Proof. exact (proj2 (@lem8244864 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8244869 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term962 A B P lt2 s a' f g.
Proof. exact (proj1 (@lem8244866 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8244871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1049 A P Q) = (term1050 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem8244872 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1049 A P Q) = (term1050 A P Q).
Proof. exact (@lem8244871 A P Q). Qed.
Lemma lem8244873 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1051 A B P p t f lt2 s a) = (term1052 A B P p t f lt2 s a).
Proof. exact (@lem8244872 A (term945 A B P p f a) (term942 A B P t f lt2 s a)). Qed.
Lemma lem8244874 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term1053 A B P t f lt2 s a y) = (term941 A B P t f lt2 y s a).
Proof. exact (eq_refl (term1053 A B P t f lt2 s a y)). Qed.
Lemma lem8244875 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1054 A B P t f lt2 s a) = (term942 A B P t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8244874 A B P t f lt2 y s a)). Qed.
Lemma lem8244876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244877 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1055 A B P t f lt2 s a) = (term943 A B P t f lt2 s a).
Proof. exact (MK_COMB (@lem8244876 A) (@lem8244875 A B P t f lt2 s a)). Qed.
Lemma lem8244878 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term946 A B P p f a) = (term946 A B P p f a).
Proof. exact (eq_refl (term946 A B P p f a)). Qed.
Lemma lem8244879 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1051 A B P p t f lt2 s a) = (term947 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8244878 A B P p f a) (@lem8244877 A B P t f lt2 s a)). Qed.
Lemma lem8244880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8244881 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1056 A B P p t f lt2 s a) = (term1057 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8244880) (@lem8244879 A B P p t f lt2 s a)). Qed.
Lemma lem8244882 {A B P : Type'} (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term1053 A B P t f lt2 s a y) = (term941 A B P t f lt2 y s a).
Proof. exact (eq_refl (term1053 A B P t f lt2 s a y)). Qed.
Lemma lem8244883 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term946 A B P p f a) = (term946 A B P p f a).
Proof. exact (eq_refl (term946 A B P p f a)). Qed.
Lemma lem8244884 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term1058 A B P p t f lt2 s a y) = (term1059 A B P p t f lt2 y s a).
Proof. exact (MK_COMB (@lem8244883 A B P p f a) (@lem8244882 A B P t f lt2 y s a)). Qed.
Lemma lem8244885 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1060 A B P p t f lt2 s a) = (term1061 A B P p t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8244884 A B P p t f lt2 y s a)). Qed.
Lemma lem8244886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244887 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1052 A B P p t f lt2 s a) = (term1062 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8244886 A) (@lem8244885 A B P p t f lt2 s a)). Qed.
Lemma lem8244888 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : ((term1051 A B P p t f lt2 s a) = (term1052 A B P p t f lt2 s a)) = ((term947 A B P p t f lt2 s a) = (term1062 A B P p t f lt2 s a)).
Proof. exact (MK_COMB (@lem8244881 A B P p t f lt2 s a) (@lem8244887 A B P p t f lt2 s a)). Qed.
Lemma lem8244889 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term947 A B P p t f lt2 s a) = (term1062 A B P p t f lt2 s a).
Proof. exact (EQ_MP (@lem8244888 A B P p t f lt2 s a) (@lem8244873 A B P p t f lt2 s a)). Qed.
Lemma lem8244890 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term948 A B P p t f lt2 s) = (term1063 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8244889 A B P p t f lt2 s a)). Qed.
Lemma lem8244891 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8244892 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term949 A B P p t f lt2 s) = (term1064 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8244891 P) (@lem8244890 A B P p t f lt2 s)). Qed.
Lemma lem8244893 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term950 A B P p t lt2 s) = (term1065 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8244892 A B P p t f lt2 s)). Qed.
Lemma lem8244894 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244895 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term951 A B P p t lt2 s) = (term1066 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8244894 A B) (@lem8244893 A B P p t lt2 s)). Qed.
Lemma lem8244908 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term1059 A B P p t f lt2 y s a) = (term1059 A B P p t f lt2 y s a).
Proof. exact (eq_refl (term1059 A B P p t f lt2 y s a)). Qed.
Lemma lem8244909 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1061 A B P p t f lt2 s a) = (term1061 A B P p t f lt2 s a).
Proof. exact (fun_ext (fun y : A => @lem8244908 A B P p t f lt2 y s a)). Qed.
Lemma lem8244910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8244911 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) (a : P) : (term1062 A B P p t f lt2 s a) = (term1062 A B P p t f lt2 s a).
Proof. exact (MK_COMB (@lem8244910 A) (@lem8244909 A B P p t f lt2 s a)). Qed.
Lemma lem8244912 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term1063 A B P p t f lt2 s) = (term1063 A B P p t f lt2 s).
Proof. exact (fun_ext (fun a : P => @lem8244911 A B P p t f lt2 s a)). Qed.
Lemma lem8244913 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8244914 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (s : P -> A) : (term1064 A B P p t f lt2 s) = (term1064 A B P p t f lt2 s).
Proof. exact (MK_COMB (@lem8244913 P) (@lem8244912 A B P p t f lt2 s)). Qed.
Lemma lem8244915 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term1065 A B P p t lt2 s) = (term1065 A B P p t lt2 s).
Proof. exact (fun_ext (fun f : A -> B => @lem8244914 A B P p t f lt2 s)). Qed.
Lemma lem8244916 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8244917 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term1066 A B P p t lt2 s) = (term1066 A B P p t lt2 s).
Proof. exact (MK_COMB (@lem8244916 A B) (@lem8244915 A B P p t lt2 s)). Qed.
Lemma lem8244918 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) : (term951 A B P p t lt2 s) = (term1066 A B P p t lt2 s).
Proof. exact (TRANS (@lem8244895 A B P p t lt2 s) (@lem8244917 A B P p t lt2 s)). Qed.
Lemma lem8244919 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1066 A B P p t lt2 s.
Proof. exact (EQ_MP (@lem8244918 A B P p t lt2 s) (@lem8243952 A B P p t lt2 s h1)). Qed.
Lemma lem8245150 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term933 A B P t f a) = (term933 A B P t g a)) = ((term933 A B P t f a) = (term933 A B P t g a)).
Proof. exact (eq_refl ((term933 A B P t f a) = (term933 A B P t g a))). Qed.
Lemma lem8245167 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1033 A B P p lt2 s z' f g a) = (term1067 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term1014 A B P lt2 z' f g s a) (term945 A B P p g a) (term1007 A B P z' f g a)). Qed.
Lemma lem8245170 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term946 A B P p f a) = (term946 A B P p f a).
Proof. exact (eq_refl (term946 A B P p f a)). Qed.
Lemma lem8245171 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1035 A B P p lt2 s z' f g a) = (term1068 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8245170 A B P p f a) (@lem8245167 A B P lt2 s p z' f g a)). Qed.
Lemma lem8245178 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1068 A B P lt2 s p z' f g a) = (term1069 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term1070 A B P p lt2 z' f g s a) (term945 A B P p f a) (term1071 A B P p z' f g a)). Qed.
Lemma lem8245179 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1035 A B P p lt2 s z' f g a) = (term1069 A B P lt2 s p z' f g a).
Proof. exact (TRANS (@lem8245171 A B P lt2 s p z' f g a) (@lem8245178 A B P lt2 s p z' f g a)). Qed.
Lemma lem8245180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8245181 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term1037 A B P p lt2 s z' f g a) = (term1072 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8245180) (@lem8245179 A B P lt2 s p z' f g a)). Qed.
Lemma lem8245182 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term1039 A B P p lt2 s z' f t g a) = (term1073 A B P lt2 s p z' f t g a).
Proof. exact (MK_COMB (@lem8245181 A B P lt2 s p z' f g a) (@lem8245150 A B P f t g a)). Qed.
Lemma lem8245189 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term1073 A B P lt2 s p z' f t g a) = (term1074 A B P lt2 s p z' f t g a).
Proof. exact (@lem19699 (term1075 A B P p lt2 z' f g s a) (term1076 A B P p z' f g a) ((term933 A B P t f a) = (term933 A B P t g a))). Qed.
Lemma lem8245190 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term1039 A B P p lt2 s z' f t g a) = (term1074 A B P lt2 s p z' f t g a).
Proof. exact (TRANS (@lem8245182 A B P lt2 s p z' f t g a) (@lem8245189 A B P lt2 s p z' f t g a)). Qed.
Lemma lem8245191 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term1041 A B P p lt2 s z' f t g) = (term1077 A B P lt2 s p z' f t g).
Proof. exact (fun_ext (fun a : P => @lem8245190 A B P lt2 s p z' f t g a)). Qed.
Lemma lem8245192 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8245193 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term1043 A B P p lt2 s z' f t g) = (term1078 A B P lt2 s p z' f t g).
Proof. exact (MK_COMB (@lem8245192 P) (@lem8245191 A B P lt2 s p z' f t g)). Qed.
Lemma lem8245194 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) : (term1045 A B P p lt2 s z' f t) = (term1079 A B P lt2 s p z' f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8245193 A B P lt2 s p z' f t g)). Qed.
Lemma lem8245195 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245196 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (t : type557 A B P) : (term1046 A B P p lt2 s z' f t) = (term1080 A B P lt2 s p z' f t).
Proof. exact (MK_COMB (@lem8245195 A B) (@lem8245194 A B P lt2 s p z' f t)). Qed.
Lemma lem8245197 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (t : type557 A B P) : (term1047 A B P p lt2 s z' t) = (term1081 A B P lt2 s p z' t).
Proof. exact (fun_ext (fun f : A -> B => @lem8245196 A B P lt2 s p z' f t)). Qed.
Lemma lem8245198 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245200 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (t : type557 A B P) : (term1048 A B P p lt2 s z' t) = (term1082 A B P lt2 s p z' t).
Proof. exact (MK_COMB (@lem8245198 A B) (@lem8245197 A B P lt2 s p z' t)). Qed.
Lemma lem8245201 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1082 A B P lt2 s p z' t.
Proof. exact (EQ_MP (@lem8245200 A B P lt2 s p z' t) (@lem8244843 A B P p lt2 s z' t h1)). Qed.
Lemma lem8245217 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term960 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (eq_refl (term960 A B P lt2 s a' f g z)). Qed.
Lemma lem8245218 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term961 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8245217 A B P lt2 s a' f g z)). Qed.
Lemma lem8245219 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8245221 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term962 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8245219 A) (@lem8245218 A B P lt2 s a' f g)). Qed.
Lemma lem8245222 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term962 A B P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8245221 A B P lt2 s a' f g) (@lem8244859 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8245303 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1022 A B P lt2 s z f p g a) = (term1083 A B P lt2 s z f p g a).
Proof. exact (@lem19490 (term991 A B P f p g a) (term1018 A B P lt2 s z f g a) (term988 A B P f p g a)). Qed.
Lemma lem8245310 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1084 A B P lt2 s z f p g a) = (term1085 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term1014 A B P lt2 z f g s a) (term1007 A B P z f g a) (term988 A B P f p g a)). Qed.
Lemma lem8245317 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1086 A B P lt2 s z f p g a) = (term1087 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term1014 A B P lt2 z f g s a) (term1007 A B P z f g a) (term991 A B P f p g a)). Qed.
Lemma lem8245318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8245319 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1088 A B P lt2 s z f p g a) = (term1089 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8245318) (@lem8245317 A B P lt2 s z f p g a)). Qed.
Lemma lem8245320 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1083 A B P lt2 s z f p g a) = (term1090 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8245319 A B P lt2 s z f p g a) (@lem8245310 A B P lt2 s z f p g a)). Qed.
Lemma lem8245322 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1022 A B P lt2 s z f p g a) = (term1090 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8245303 A B P lt2 s z f p g a) (@lem8245320 A B P lt2 s z f p g a)). Qed.
Lemma lem8245323 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1024 A B P lt2 s z f p g) = (term1091 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8245322 A B P lt2 s z f p g a)). Qed.
Lemma lem8245324 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8245325 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1026 A B P lt2 s z f p g) = (term1092 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8245324 P) (@lem8245323 A B P lt2 s z f p g)). Qed.
Lemma lem8245326 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term1028 A B P lt2 s z f p) = (term1093 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8245325 A B P lt2 s z f p g)). Qed.
Lemma lem8245327 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245328 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term1029 A B P lt2 s z f p) = (term1094 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8245327 A B) (@lem8245326 A B P lt2 s z f p)). Qed.
Lemma lem8245329 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term1030 A B P lt2 s z p) = (term1095 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8245328 A B P lt2 s z f p)). Qed.
Lemma lem8245330 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245332 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term1031 A B P lt2 s z p) = (term1096 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8245330 A B) (@lem8245329 A B P lt2 s z p)). Qed.
Lemma lem8245333 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1096 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8245332 A B P lt2 s z p) (@lem8244626 A B P lt2 s z p h1)). Qed.
Lemma lem8245402 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term960 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (eq_refl (term960 A B P lt2 s a' f g z)). Qed.
Lemma lem8245403 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term961 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8245402 A B P lt2 s a' f g z)). Qed.
Lemma lem8245404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8245406 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term962 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8245404 A) (@lem8245403 A B P lt2 s a' f g)). Qed.
Lemma lem8245407 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term962 A B P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8245406 A B P lt2 s a' f g) (@lem8244863 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8245488 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1022 A B P lt2 s z f p g a) = (term1083 A B P lt2 s z f p g a).
Proof. exact (@lem19490 (term991 A B P f p g a) (term1018 A B P lt2 s z f g a) (term988 A B P f p g a)). Qed.
Lemma lem8245495 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1084 A B P lt2 s z f p g a) = (term1085 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term1014 A B P lt2 z f g s a) (term1007 A B P z f g a) (term988 A B P f p g a)). Qed.
Lemma lem8245502 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1086 A B P lt2 s z f p g a) = (term1087 A B P lt2 s z f p g a).
Proof. exact (@lem19699 (term1014 A B P lt2 z f g s a) (term1007 A B P z f g a) (term991 A B P f p g a)). Qed.
Lemma lem8245503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8245504 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1088 A B P lt2 s z f p g a) = (term1089 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8245503) (@lem8245502 A B P lt2 s z f p g a)). Qed.
Lemma lem8245505 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1083 A B P lt2 s z f p g a) = (term1090 A B P lt2 s z f p g a).
Proof. exact (MK_COMB (@lem8245504 A B P lt2 s z f p g a) (@lem8245495 A B P lt2 s z f p g a)). Qed.
Lemma lem8245507 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) : (term1022 A B P lt2 s z f p g a) = (term1090 A B P lt2 s z f p g a).
Proof. exact (TRANS (@lem8245488 A B P lt2 s z f p g a) (@lem8245505 A B P lt2 s z f p g a)). Qed.
Lemma lem8245508 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1024 A B P lt2 s z f p g) = (term1091 A B P lt2 s z f p g).
Proof. exact (fun_ext (fun a : P => @lem8245507 A B P lt2 s z f p g a)). Qed.
Lemma lem8245509 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8245510 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) : (term1026 A B P lt2 s z f p g) = (term1092 A B P lt2 s z f p g).
Proof. exact (MK_COMB (@lem8245509 P) (@lem8245508 A B P lt2 s z f p g)). Qed.
Lemma lem8245511 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term1028 A B P lt2 s z f p) = (term1093 A B P lt2 s z f p).
Proof. exact (fun_ext (fun g : A -> B => @lem8245510 A B P lt2 s z f p g)). Qed.
Lemma lem8245512 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245513 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (p : type560 A B P) : (term1029 A B P lt2 s z f p) = (term1094 A B P lt2 s z f p).
Proof. exact (MK_COMB (@lem8245512 A B) (@lem8245511 A B P lt2 s z f p)). Qed.
Lemma lem8245514 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term1030 A B P lt2 s z p) = (term1095 A B P lt2 s z p).
Proof. exact (fun_ext (fun f : A -> B => @lem8245513 A B P lt2 s z f p)). Qed.
Lemma lem8245515 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8245517 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) : (term1031 A B P lt2 s z p) = (term1096 A B P lt2 s z p).
Proof. exact (MK_COMB (@lem8245515 A B) (@lem8245514 A B P lt2 s z p)). Qed.
Lemma lem8245518 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1096 A B P lt2 s z p.
Proof. exact (EQ_MP (@lem8245517 A B P lt2 s z p) (@lem8244626 A B P lt2 s z p h1)). Qed.
Lemma lem8245587 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (z : A) : (term960 A B P lt2 s a' f g z) = (term960 A B P lt2 s a' f g z).
Proof. exact (eq_refl (term960 A B P lt2 s a' f g z)). Qed.
Lemma lem8245588 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term961 A B P lt2 s a' f g) = (term961 A B P lt2 s a' f g).
Proof. exact (fun_ext (fun z : A => @lem8245587 A B P lt2 s a' f g z)). Qed.
Lemma lem8245589 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8245591 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) : (term962 A B P lt2 s a' f g) = (term962 A B P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8245589 A) (@lem8245588 A B P lt2 s a' f g)). Qed.
Lemma lem8245592 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term962 A B P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8245591 A B P lt2 s a' f g) (@lem8244869 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8245597 {A B P : Type'} (_109746 : A -> B) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1097 A B P p t lt2 s _109746.
Proof. exact (@lem8244919 A B P p t lt2 s h1 _109746). Qed.
Lemma lem8245598 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (s : P -> A) : (term1097 A B P p t lt2 s _109746) = (term1064 A B P p t _109746 lt2 s).
Proof. exact (eq_refl (term1097 A B P p t lt2 s _109746)). Qed.
Lemma lem8245599 {A B P : Type'} (_109746 : A -> B) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1064 A B P p t _109746 lt2 s.
Proof. exact (EQ_MP (@lem8245598 A B P p t _109746 lt2 s) (@lem8245597 A B P _109746 p t lt2 s h1)). Qed.
Lemma lem8245600 {A B P : Type'} (_109746 : A -> B) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1098 A B P p t _109746 lt2 s _109747.
Proof. exact (@lem8245599 A B P _109746 p t lt2 s h1 _109747). Qed.
Lemma lem8245601 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (s : P -> A) (_109747 : P) : (term1098 A B P p t _109746 lt2 s _109747) = (term1062 A B P p t _109746 lt2 s _109747).
Proof. exact (eq_refl (term1098 A B P p t _109746 lt2 s _109747)). Qed.
Lemma lem8245602 {A B P : Type'} (_109746 : A -> B) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1062 A B P p t _109746 lt2 s _109747.
Proof. exact (EQ_MP (@lem8245601 A B P p t _109746 lt2 s _109747) (@lem8245600 A B P _109746 _109747 p t lt2 s h1)). Qed.
Lemma lem8245603 {A B P : Type'} (_109746 : A -> B) (_109747 : P) (_109748 : A) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1099 A B P p t _109746 lt2 s _109747 _109748.
Proof. exact (@lem8245602 A B P _109746 _109747 p t lt2 s h1 _109748). Qed.
Lemma lem8245604 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1099 A B P p t _109746 lt2 s _109747 _109748) = (term1059 A B P p t _109746 lt2 _109748 s _109747).
Proof. exact (eq_refl (term1099 A B P p t _109746 lt2 s _109747 _109748)). Qed.
Lemma lem8245642 {A B P : Type'} (_109761 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1100 A B P lt2 s p z' t _109761.
Proof. exact (@lem8245201 A B P p lt2 s z' t h1 _109761). Qed.
Lemma lem8245643 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) : (term1100 A B P lt2 s p z' t _109761) = (term1080 A B P lt2 s p z' _109761 t).
Proof. exact (eq_refl (term1100 A B P lt2 s p z' t _109761)). Qed.
Lemma lem8245644 {A B P : Type'} (_109761 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1080 A B P lt2 s p z' _109761 t.
Proof. exact (EQ_MP (@lem8245643 A B P lt2 s p z' _109761 t) (@lem8245642 A B P _109761 p lt2 s z' t h1)). Qed.
Lemma lem8245645 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1101 A B P lt2 s p z' _109761 t _109762.
Proof. exact (@lem8245644 A B P _109761 p lt2 s z' t h1 _109762). Qed.
Lemma lem8245646 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) : (term1101 A B P lt2 s p z' _109761 t _109762) = (term1078 A B P lt2 s p z' _109761 t _109762).
Proof. exact (eq_refl (term1101 A B P lt2 s p z' _109761 t _109762)). Qed.
Lemma lem8245647 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1078 A B P lt2 s p z' _109761 t _109762.
Proof. exact (EQ_MP (@lem8245646 A B P lt2 s p z' _109761 t _109762) (@lem8245645 A B P _109761 _109762 p lt2 s z' t h1)). Qed.
Lemma lem8245648 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1102 A B P lt2 s p z' _109761 t _109762 _109763.
Proof. exact (@lem8245647 A B P _109761 _109762 p lt2 s z' t h1 _109763). Qed.
Lemma lem8245649 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1102 A B P lt2 s p z' _109761 t _109762 _109763) = (term1074 A B P lt2 s p z' _109761 t _109762 _109763).
Proof. exact (eq_refl (term1102 A B P lt2 s p z' _109761 t _109762 _109763)). Qed.
Lemma lem8245650 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1074 A B P lt2 s p z' _109761 t _109762 _109763.
Proof. exact (EQ_MP (@lem8245649 A B P lt2 s p z' _109761 t _109762 _109763) (@lem8245648 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8245651 {A B P : Type'} (_109764 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1103 A B P lt2 s a' f g _109764.
Proof. exact (@lem8245222 A B P p lt2 s f t g a' h1 _109764). Qed.
Lemma lem8245652 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109764 : A) : (term1103 A B P lt2 s a' f g _109764) = (term960 A B P lt2 s a' f g _109764).
Proof. exact (eq_refl (term1103 A B P lt2 s a' f g _109764)). Qed.
Lemma lem8245663 {A B P : Type'} (_109768 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1104 A B P lt2 s z p _109768.
Proof. exact (@lem8245333 A B P lt2 s z p h1 _109768). Qed.
Lemma lem8245664 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) : (term1104 A B P lt2 s z p _109768) = (term1094 A B P lt2 s z _109768 p).
Proof. exact (eq_refl (term1104 A B P lt2 s z p _109768)). Qed.
Lemma lem8245665 {A B P : Type'} (_109768 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1094 A B P lt2 s z _109768 p.
Proof. exact (EQ_MP (@lem8245664 A B P lt2 s z _109768 p) (@lem8245663 A B P _109768 lt2 s z p h1)). Qed.
Lemma lem8245666 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1105 A B P lt2 s z _109768 p _109769.
Proof. exact (@lem8245665 A B P _109768 lt2 s z p h1 _109769). Qed.
Lemma lem8245667 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) : (term1105 A B P lt2 s z _109768 p _109769) = (term1092 A B P lt2 s z _109768 p _109769).
Proof. exact (eq_refl (term1105 A B P lt2 s z _109768 p _109769)). Qed.
Lemma lem8245668 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1092 A B P lt2 s z _109768 p _109769.
Proof. exact (EQ_MP (@lem8245667 A B P lt2 s z _109768 p _109769) (@lem8245666 A B P _109768 _109769 lt2 s z p h1)). Qed.
Lemma lem8245669 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1106 A B P lt2 s z _109768 p _109769 _109770.
Proof. exact (@lem8245668 A B P _109768 _109769 lt2 s z p h1 _109770). Qed.
Lemma lem8245670 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1106 A B P lt2 s z _109768 p _109769 _109770) = (term1090 A B P lt2 s z _109768 p _109769 _109770).
Proof. exact (eq_refl (term1106 A B P lt2 s z _109768 p _109769 _109770)). Qed.
Lemma lem8245671 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1090 A B P lt2 s z _109768 p _109769 _109770.
Proof. exact (EQ_MP (@lem8245670 A B P lt2 s z _109768 p _109769 _109770) (@lem8245669 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8245681 {A B P : Type'} (_109774 : A) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1103 A B P lt2 s a' f g _109774.
Proof. exact (@lem8245407 A B P p lt2 f s t g a' h1 _109774). Qed.
Lemma lem8245682 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109774 : A) : (term1103 A B P lt2 s a' f g _109774) = (term960 A B P lt2 s a' f g _109774).
Proof. exact (eq_refl (term1103 A B P lt2 s a' f g _109774)). Qed.
Lemma lem8245693 {A B P : Type'} (_109778 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1104 A B P lt2 s z p _109778.
Proof. exact (@lem8245518 A B P lt2 s z p h1 _109778). Qed.
Lemma lem8245694 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) : (term1104 A B P lt2 s z p _109778) = (term1094 A B P lt2 s z _109778 p).
Proof. exact (eq_refl (term1104 A B P lt2 s z p _109778)). Qed.
Lemma lem8245695 {A B P : Type'} (_109778 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1094 A B P lt2 s z _109778 p.
Proof. exact (EQ_MP (@lem8245694 A B P lt2 s z _109778 p) (@lem8245693 A B P _109778 lt2 s z p h1)). Qed.
Lemma lem8245696 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1105 A B P lt2 s z _109778 p _109779.
Proof. exact (@lem8245695 A B P _109778 lt2 s z p h1 _109779). Qed.
Lemma lem8245697 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) : (term1105 A B P lt2 s z _109778 p _109779) = (term1092 A B P lt2 s z _109778 p _109779).
Proof. exact (eq_refl (term1105 A B P lt2 s z _109778 p _109779)). Qed.
Lemma lem8245698 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1092 A B P lt2 s z _109778 p _109779.
Proof. exact (EQ_MP (@lem8245697 A B P lt2 s z _109778 p _109779) (@lem8245696 A B P _109778 _109779 lt2 s z p h1)). Qed.
Lemma lem8245699 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1106 A B P lt2 s z _109778 p _109779 _109780.
Proof. exact (@lem8245698 A B P _109778 _109779 lt2 s z p h1 _109780). Qed.
Lemma lem8245700 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1106 A B P lt2 s z _109778 p _109779 _109780) = (term1090 A B P lt2 s z _109778 p _109779 _109780).
Proof. exact (eq_refl (term1106 A B P lt2 s z _109778 p _109779 _109780)). Qed.
Lemma lem8245701 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1090 A B P lt2 s z _109778 p _109779 _109780.
Proof. exact (EQ_MP (@lem8245700 A B P lt2 s z _109778 p _109779 _109780) (@lem8245699 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8245711 {A B P : Type'} (_109784 : A) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1103 A B P lt2 s a' f g _109784.
Proof. exact (@lem8245592 A B P p lt2 g t f s a' h1 _109784). Qed.
Lemma lem8245712 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109784 : A) : (term1103 A B P lt2 s a' f g _109784) = (term960 A B P lt2 s a' f g _109784).
Proof. exact (eq_refl (term1103 A B P lt2 s a' f g _109784)). Qed.
Lemma lem8245722 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1107 A B P p z' _109761 t _109762 _109763.
Proof. exact (proj2 (@lem8245650 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8245723 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1108 A B P p lt2 z' s _109761 t _109762 _109763.
Proof. exact (proj1 (@lem8245650 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8245733 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1087 A B P lt2 s z _109768 p _109769 _109770.
Proof. exact (proj1 (@lem8245671 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8245740 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1085 A B P lt2 s z _109778 p _109779 _109780.
Proof. exact (proj2 (@lem8245701 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8245755 {A B P : Type'} (_109746 : A -> B) (_109748 : A) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1059 A B P p t _109746 lt2 _109748 s _109747.
Proof. exact (EQ_MP (@lem8245604 A B P p t _109746 lt2 _109748 s _109747) (@lem8245603 A B P _109746 _109747 _109748 p t lt2 s h1)). Qed.
Lemma lem8245761 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term957 A P lt2 y s a.
Proof. exact (proj2 (@lem8244846 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8245857 {A B P : Type'} (_109764 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term960 A B P lt2 s a' f g _109764.
Proof. exact (EQ_MP (@lem8245652 A B P lt2 s a' f g _109764) (@lem8245651 A B P _109764 p lt2 s f t g a' h1)). Qed.
Lemma lem8245859 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term973 A B P f t g a'.
Proof. exact (proj2 (@lem8244856 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8245863 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1108 A B P p lt2 z' s _109761 t _109762 _109763) = (term1109 A B P p lt2 z' s _109761 t _109762 _109763).
Proof. exact (@lem8239577 (term945 A B P p _109761 _109763) (term1070 A B P p lt2 z' _109761 _109762 s _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8245870 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1110 A B P p lt2 z' s _109761 t _109762 _109763) = (term1111 A B P p lt2 z' s _109761 t _109762 _109763).
Proof. exact (@lem8239577 (term945 A B P p _109762 _109763) (term1014 A B P lt2 z' _109761 _109762 s _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8245871 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8245874 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1109 A B P p lt2 z' s _109761 t _109762 _109763) = (term1112 A B P p lt2 z' s _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8245871 A B P p _109761 _109763) (@lem8245870 A B P p lt2 z' s _109761 t _109762 _109763)). Qed.
Lemma lem8245876 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1108 A B P p lt2 z' s _109761 t _109762 _109763) = (term1112 A B P p lt2 z' s _109761 t _109762 _109763).
Proof. exact (TRANS (@lem8245863 A B P p lt2 z' s _109761 t _109762 _109763) (@lem8245874 A B P p lt2 z' s _109761 t _109762 _109763)). Qed.
Lemma lem8245877 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1112 A B P p lt2 z' s _109761 t _109762 _109763.
Proof. exact (EQ_MP (@lem8245876 A B P p lt2 z' s _109761 t _109762 _109763) (@lem8245723 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8245881 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1107 A B P p z' _109761 t _109762 _109763) = (term1113 A B P p z' _109761 t _109762 _109763).
Proof. exact (@lem8239577 (term945 A B P p _109761 _109763) (term1071 A B P p z' _109761 _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8245888 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1114 A B P p z' _109761 t _109762 _109763) = (term1115 A B P p z' _109761 t _109762 _109763).
Proof. exact (@lem8239577 (term945 A B P p _109762 _109763) (term1007 A B P z' _109761 _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8245889 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8245892 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1113 A B P p z' _109761 t _109762 _109763) = (term1116 A B P p z' _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8245889 A B P p _109761 _109763) (@lem8245888 A B P p z' _109761 t _109762 _109763)). Qed.
Lemma lem8245894 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1107 A B P p z' _109761 t _109762 _109763) = (term1116 A B P p z' _109761 t _109762 _109763).
Proof. exact (TRANS (@lem8245881 A B P p z' _109761 t _109762 _109763) (@lem8245892 A B P p z' _109761 t _109762 _109763)). Qed.
Lemma lem8245895 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1116 A B P p z' _109761 t _109762 _109763.
Proof. exact (EQ_MP (@lem8245894 A B P p z' _109761 t _109762 _109763) (@lem8245722 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8245949 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term945 A B P p f a'.
Proof. exact (proj1 (@lem8244855 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8245955 {A B P : Type'} (_109774 : A) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term960 A B P lt2 s a' f g _109774.
Proof. exact (EQ_MP (@lem8245682 A B P lt2 s a' f g _109774) (@lem8245681 A B P _109774 p lt2 f s t g a' h1)). Qed.
Lemma lem8246023 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1117 A B P lt2 z s _109768 p _109769 _109770.
Proof. exact (proj1 (@lem8245733 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8246033 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1118 A B P z _109768 p _109769 _109770.
Proof. exact (proj2 (@lem8245733 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8246045 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term945 A B P p g a'.
Proof. exact (proj1 (@lem8244851 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8246053 {A B P : Type'} (_109784 : A) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term960 A B P lt2 s a' f g _109784.
Proof. exact (EQ_MP (@lem8245712 A B P lt2 s a' f g _109784) (@lem8245711 A B P _109784 p lt2 g t f s a' h1)). Qed.
Lemma lem8246101 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1119 A B P lt2 z s _109778 p _109779 _109780.
Proof. exact (proj1 (@lem8245740 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8246111 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1120 A B P z _109778 p _109779 _109780.
Proof. exact (proj2 (@lem8245740 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8246283 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term944 A B P p f a.
Proof. exact (proj1 (@lem8244844 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246284 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term1121 A B P p f a.
Proof. exact (fun h0 : term945 A B P p f a => @lem8246283 A B P p t f lt2 y s a h1). Qed.
Lemma lem8246286 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246287 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term1121 A B P p f a) = (term944 A B P p f a).
Proof. exact (@lem8246286 (term944 A B P p f a)). Qed.
Lemma lem8246288 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term944 A B P p f a.
Proof. exact (EQ_MP (@lem8246287 A B P p f a) (@lem8246284 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246290 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term936 A B P lt2 y t f a.
Proof. exact (proj1 (@lem8244846 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246291 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term1123 A B P lt2 y t f a.
Proof. exact (fun h0 : term938 A B P lt2 y t f a => @lem8246290 A B P p t f lt2 y s a h1). Qed.
Lemma lem8246293 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246294 {A B P : Type'} (lt2 : type1402 A) (y : A) (t : type557 A B P) (f : A -> B) (a : P) : (term1123 A B P lt2 y t f a) = (term936 A B P lt2 y t f a).
Proof. exact (@lem8246293 (term936 A B P lt2 y t f a)). Qed.
Lemma lem8246295 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term936 A B P lt2 y t f a.
Proof. exact (EQ_MP (@lem8246294 A B P lt2 y t f a) (@lem8246291 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246301 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246302 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1124 A B P t p _109746 lt2 _109748 s _109747).
Proof. exact (@lem8246301 (term938 A B P lt2 _109748 t _109746 _109747) (term945 A B P p _109746 _109747) (term932 A P lt2 _109748 s _109747)). Qed.
Lemma lem8246316 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246317 {A B P : Type'} (lt2 : type1402 A) (_109748 : A) (s : P -> A) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1125 A B P p _109746 lt2 _109748 s _109747) = (term1126 A B P lt2 _109748 s p _109746 _109747).
Proof. exact (@lem8246316 (term932 A P lt2 _109748 s _109747) (term945 A B P p _109746 _109747)). Qed.
Lemma lem8246323 {A B P : Type'} (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term940 A B P lt2 _109748 t _109746 _109747) = (term940 A B P lt2 _109748 t _109746 _109747).
Proof. exact (eq_refl (term940 A B P lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246324 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1124 A B P t p _109746 lt2 _109748 s _109747) = (term1127 A B P t lt2 _109748 s p _109746 _109747).
Proof. exact (MK_COMB (@lem8246323 A B P lt2 _109748 t _109746 _109747) (@lem8246317 A B P lt2 _109748 s p _109746 _109747)). Qed.
Lemma lem8246328 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246329 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1127 A B P t lt2 _109748 s p _109746 _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747).
Proof. exact (@lem8246328 (term932 A P lt2 _109748 s _109747) (term938 A B P lt2 _109748 t _109746 _109747) (term945 A B P p _109746 _109747)). Qed.
Lemma lem8246345 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1124 A B P t p _109746 lt2 _109748 s _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747).
Proof. exact (TRANS (@lem8246324 A B P t lt2 _109748 s p _109746 _109747) (@lem8246329 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246346 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747).
Proof. exact (TRANS (@lem8246302 A B P t p _109746 lt2 _109748 s _109747) (@lem8246345 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8246348 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1129 A B P p t _109746 lt2 _109748 s _109747) = (term1130 A B P s lt2 _109748 t p _109746 _109747).
Proof. exact (MK_COMB (@lem8246347) (@lem8246346 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246363 {A B P : Type'} (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1131 A B P p lt2 _109748 t _109746 _109747) = (term1132 A B P lt2 _109748 t p _109746 _109747).
Proof. exact (@lem8246362 (term938 A B P lt2 _109748 t _109746 _109747) (term945 A B P p _109746 _109747)). Qed.
Lemma lem8246369 {A P : Type'} (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1133 A P lt2 _109748 s _109747) = (term1133 A P lt2 _109748 s _109747).
Proof. exact (eq_refl (term1133 A P lt2 _109748 s _109747)). Qed.
Lemma lem8246370 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1134 A B P s p lt2 _109748 t _109746 _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747).
Proof. exact (MK_COMB (@lem8246369 A P lt2 _109748 s _109747) (@lem8246363 A B P lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246381 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : ((term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1134 A B P s p lt2 _109748 t _109746 _109747)) = ((term1128 A B P s lt2 _109748 t p _109746 _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747)).
Proof. exact (MK_COMB (@lem8246348 A B P s lt2 _109748 t p _109746 _109747) (@lem8246370 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8246384 (x : Prop) : (x = x) = True.
Proof. exact (@lem8246383 Prop x). Qed.
Lemma lem8246385 {A B P : Type'} (s : P -> A) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : ((term1128 A B P s lt2 _109748 t p _109746 _109747) = (term1128 A B P s lt2 _109748 t p _109746 _109747)) = True.
Proof. exact (@lem8246384 (term1128 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246386 {A B P : Type'} (s : P -> A) (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : ((term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1134 A B P s p lt2 _109748 t _109746 _109747)) = True.
Proof. exact (TRANS (@lem8246381 A B P s lt2 _109748 t p _109746 _109747) (@lem8246385 A B P s lt2 _109748 t p _109746 _109747)). Qed.
Lemma lem8246387 {A B P : Type'} (s : P -> A) (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : True = ((term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1134 A B P s p lt2 _109748 t _109746 _109747)).
Proof. exact (SYM (@lem8246386 A B P s p lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246388 {A B P : Type'} (s : P -> A) (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1059 A B P p t _109746 lt2 _109748 s _109747) = (term1134 A B P s p lt2 _109748 t _109746 _109747).
Proof. exact (EQ_MP (@lem8246387 A B P s p lt2 _109748 t _109746 _109747) (@lem0)). Qed.
Lemma lem8246389 {A B P : Type'} (_109748 : A) (_109746 : A -> B) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1134 A B P s p lt2 _109748 t _109746 _109747.
Proof. exact (EQ_MP (@lem8246388 A B P s p lt2 _109748 t _109746 _109747) (@lem8245755 A B P _109746 _109748 _109747 p t lt2 s h1)). Qed.
Lemma lem8246391 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8246392 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1134 A B P s p lt2 _109748 t _109746 _109747) = (term1136 A B P p t _109746 lt2 _109748 s _109747).
Proof. exact (@lem8246391 (term1131 A B P p lt2 _109748 t _109746 _109747) (term932 A P lt2 _109748 s _109747)). Qed.
Lemma lem8246394 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8246395 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1139 A B P p lt2 _109748 t _109746 _109747) = (term1140 A B P p lt2 _109748 t _109746 _109747).
Proof. exact (@lem8246394 (term945 A B P p _109746 _109747) (term938 A B P lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246397 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8246398 {A B P : Type'} (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1141 A B P p _109746 _109747) = (term944 A B P p _109746 _109747).
Proof. exact (@lem8246397 (term944 A B P p _109746 _109747)). Qed.
Lemma lem8246399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8246400 {A B P : Type'} (p : type560 A B P) (_109746 : A -> B) (_109747 : P) : (term1142 A B P p _109746 _109747) = (term965 A B P p _109746 _109747).
Proof. exact (MK_COMB (@lem8246399) (@lem8246398 A B P p _109746 _109747)). Qed.
Lemma lem8246402 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8246403 {A B P : Type'} (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1143 A B P lt2 _109748 t _109746 _109747) = (term936 A B P lt2 _109748 t _109746 _109747).
Proof. exact (@lem8246402 (term936 A B P lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246404 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1140 A B P p lt2 _109748 t _109746 _109747) = (term1144 A B P p lt2 _109748 t _109746 _109747).
Proof. exact (MK_COMB (@lem8246400 A B P p _109746 _109747) (@lem8246403 A B P lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246405 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1139 A B P p lt2 _109748 t _109746 _109747) = (term1144 A B P p lt2 _109748 t _109746 _109747).
Proof. exact (TRANS (@lem8246395 A B P p lt2 _109748 t _109746 _109747) (@lem8246404 A B P p lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8246407 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (_109748 : A) (t : type557 A B P) (_109746 : A -> B) (_109747 : P) : (term1145 A B P p lt2 _109748 t _109746 _109747) = (term1146 A B P p lt2 _109748 t _109746 _109747).
Proof. exact (MK_COMB (@lem8246406) (@lem8246405 A B P p lt2 _109748 t _109746 _109747)). Qed.
Lemma lem8246408 {A P : Type'} (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term932 A P lt2 _109748 s _109747) = (term932 A P lt2 _109748 s _109747).
Proof. exact (eq_refl (term932 A P lt2 _109748 s _109747)). Qed.
Lemma lem8246409 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1136 A B P p t _109746 lt2 _109748 s _109747) = (term1147 A B P p t _109746 lt2 _109748 s _109747).
Proof. exact (MK_COMB (@lem8246407 A B P p lt2 _109748 t _109746 _109747) (@lem8246408 A P lt2 _109748 s _109747)). Qed.
Lemma lem8246410 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (_109746 : A -> B) (lt2 : type1402 A) (_109748 : A) (s : P -> A) (_109747 : P) : (term1134 A B P s p lt2 _109748 t _109746 _109747) = (term1147 A B P p t _109746 lt2 _109748 s _109747).
Proof. exact (TRANS (@lem8246392 A B P p t _109746 lt2 _109748 s _109747) (@lem8246409 A B P p t _109746 lt2 _109748 s _109747)). Qed.
Lemma lem8246412 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term1144 A B P p lt2 y t f a.
Proof. exact (conj (@lem8246288 A B P p t f lt2 y s a h1) (@lem8246295 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246414 {A B P : Type'} (_109746 : A -> B) (_109748 : A) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1147 A B P p t _109746 lt2 _109748 s _109747.
Proof. exact (EQ_MP (@lem8246410 A B P p t _109746 lt2 _109748 s _109747) (@lem8246389 A B P _109748 _109746 _109747 p t lt2 s h1)). Qed.
Lemma lem8246415 {A B P : Type'} (_109746 : A -> B) (_109748 : A) (_109747 : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1147 A B P p t _109746 lt2 _109748 s _109747.
Proof. exact (@lem8246414 A B P _109746 _109748 _109747 p t lt2 s h1). Qed.
Lemma lem8246416 {A B P : Type'} (f : A -> B) (y : A) (a : P) (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term34 A B P p t lt2 s) : term1147 A B P p t f lt2 y s a.
Proof. exact (@lem8246415 A B P f y a p t lt2 s h1). Qed.
Lemma lem8246419 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : term932 A P lt2 y s a.
Proof. exact (@lem8246416 A B P f y a p t lt2 s h1 (@lem8246412 A B P p t f lt2 y s a h2)). Qed.
Lemma lem8246420 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : term1148 A P lt2 y s a.
Proof. exact (fun h0 : term957 A P lt2 y s a => @lem8246419 A B P p t f lt2 y s a h1 h2). Qed.
Lemma lem8246422 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246423 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term1148 A P lt2 y s a) = (term932 A P lt2 y s a).
Proof. exact (@lem8246422 (term932 A P lt2 y s a)). Qed.
Lemma lem8246424 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : term932 A P lt2 y s a.
Proof. exact (EQ_MP (@lem8246423 A P lt2 y s a) (@lem8246420 A B P p t f lt2 y s a h1 h2)). Qed.
Lemma lem8246427 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8246429 {A P : Type'} (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) : (term957 A P lt2 y s a) = (term1149 A P lt2 y s a).
Proof. exact (@lem8246427 (term932 A P lt2 y s a)). Qed.
Lemma lem8246432 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term984 A B P p t f lt2 y s a) : term1149 A P lt2 y s a.
Proof. exact (EQ_MP (@lem8246429 A P lt2 y s a) (@lem8245761 A B P p t f lt2 y s a h1)). Qed.
Lemma lem8246435 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : False.
Proof. exact (@lem8246432 A B P p t f lt2 y s a h2 (@lem8246424 A B P p t f lt2 y s a h1 h2)). Qed.
Lemma lem8246436 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : term1150.
Proof. exact (fun h0 : ~ False => @lem8246435 A B P p t f lt2 y s a h1 h2). Qed.
Lemma lem8246438 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246439 : term1150 = False.
Proof. exact (@lem8246438 False). Qed.
Lemma lem8246440 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (f : A -> B) (lt2 : type1402 A) (y : A) (s : P -> A) (a : P) (h1 : term34 A B P p t lt2 s) (h2 : term984 A B P p t f lt2 y s a) : False.
Proof. exact (EQ_MP (@lem8246439) (@lem8246436 A B P p t f lt2 y s a h1 h2)). Qed.
Lemma lem8246592 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term944 A B P p f a'.
Proof. exact (proj1 (@lem8244854 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8246593 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1121 A B P p f a'.
Proof. exact (fun h0 : term945 A B P p f a' => @lem8246592 A B P p lt2 s f t g a' h1). Qed.
Lemma lem8246595 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246596 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1121 A B P p f a') = (term944 A B P p f a').
Proof. exact (@lem8246595 (term944 A B P p f a')). Qed.
Lemma lem8246597 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term944 A B P p f a'.
Proof. exact (EQ_MP (@lem8246596 A B P p f a') (@lem8246593 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8246599 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (proj1 (@lem8244850 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8246600 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term1121 A B P p g a'.
Proof. exact (fun h0 : term945 A B P p g a' => @lem8246599 A B P p lt2 f s t g a' h1). Qed.
Lemma lem8246602 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246603 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1121 A B P p g a') = (term944 A B P p g a').
Proof. exact (@lem8246602 (term944 A B P p g a')). Qed.
Lemma lem8246604 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (EQ_MP (@lem8246603 A B P p g a') (@lem8246600 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8246606 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term944 A B P p f a'.
Proof. exact (proj1 (@lem8244854 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8246607 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1121 A B P p f a'.
Proof. exact (fun h0 : term945 A B P p f a' => @lem8246606 A B P p lt2 s f t g a' h1). Qed.
Lemma lem8246609 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246610 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1121 A B P p f a') = (term944 A B P p f a').
Proof. exact (@lem8246609 (term944 A B P p f a')). Qed.
Lemma lem8246611 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term944 A B P p f a'.
Proof. exact (EQ_MP (@lem8246610 A B P p f a') (@lem8246607 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8246613 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (proj1 (@lem8244850 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8246614 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term1121 A B P p g a'.
Proof. exact (fun h0 : term945 A B P p g a' => @lem8246613 A B P p lt2 f s t g a' h1). Qed.
Lemma lem8246616 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246617 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1121 A B P p g a') = (term944 A B P p g a').
Proof. exact (@lem8246616 (term944 A B P p g a')). Qed.
Lemma lem8246618 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (EQ_MP (@lem8246617 A B P p g a') (@lem8246614 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8246621 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term973 A B P f t g a') : term973 A B P f t g a'.
Proof. exact (h1). Qed.
Lemma lem8246622 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term973 A B P f t g a') : term1151 A B P f t g a'.
Proof. exact (fun h0 : (term933 A B P t f a') = (term933 A B P t g a') => @lem8246621 A B P f t g a' h1). Qed.
Lemma lem8246624 (p : Prop) : (term1152 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8246625 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term1151 A B P f t g a') = (term973 A B P f t g a').
Proof. exact (@lem8246624 ((term933 A B P t f a') = (term933 A B P t g a'))). Qed.
Lemma lem8246626 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term973 A B P f t g a') : term973 A B P f t g a'.
Proof. exact (EQ_MP (@lem8246625 A B P f t g a') (@lem8246622 A B P f t g a' h1)). Qed.
Lemma lem8246642 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246643 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1111 A B P p lt2 z' s _109761 t _109762 _109763) = (term1153 A B P lt2 z' s p _109761 t _109762 _109763).
Proof. exact (@lem8246642 (term1014 A B P lt2 z' _109761 _109762 s _109763) (term945 A B P p _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8246657 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246658 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1154 A B P p _109761 t _109762 _109763) = (term1155 A B P _109761 t p _109762 _109763).
Proof. exact (@lem8246657 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246666 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1156 A B P lt2 z' _109761 _109762 s _109763) = (term1156 A B P lt2 z' _109761 _109762 s _109763).
Proof. exact (eq_refl (term1156 A B P lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246667 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1153 A B P lt2 z' s p _109761 t _109762 _109763) = (term1157 A B P lt2 z' s _109761 t p _109762 _109763).
Proof. exact (MK_COMB (@lem8246666 A B P lt2 z' _109761 _109762 s _109763) (@lem8246658 A B P _109761 t p _109762 _109763)). Qed.
Lemma lem8246671 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246672 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (s : P -> A) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1157 A B P lt2 z' s _109761 t p _109762 _109763) = (term1158 A B P t lt2 z' _109761 s p _109762 _109763).
Proof. exact (@lem8246671 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term1014 A B P lt2 z' _109761 _109762 s _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246690 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (s : P -> A) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1153 A B P lt2 z' s p _109761 t _109762 _109763) = (term1158 A B P t lt2 z' _109761 s p _109762 _109763).
Proof. exact (TRANS (@lem8246667 A B P lt2 z' s _109761 t p _109762 _109763) (@lem8246672 A B P t lt2 z' _109761 s p _109762 _109763)). Qed.
Lemma lem8246691 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (s : P -> A) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1111 A B P p lt2 z' s _109761 t _109762 _109763) = (term1158 A B P t lt2 z' _109761 s p _109762 _109763).
Proof. exact (TRANS (@lem8246643 A B P lt2 z' s p _109761 t _109762 _109763) (@lem8246690 A B P t lt2 z' _109761 s p _109762 _109763)). Qed.
Lemma lem8246692 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8246693 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (s : P -> A) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1159 A B P t lt2 z' _109761 s p _109762 _109763).
Proof. exact (MK_COMB (@lem8246692 A B P p _109761 _109763) (@lem8246691 A B P t lt2 z' _109761 s p _109762 _109763)). Qed.
Lemma lem8246697 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246698 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (s : P -> A) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1159 A B P t lt2 z' _109761 s p _109762 _109763) = (term1160 A B P t lt2 z' _109761 s p _109762 _109763).
Proof. exact (@lem8246697 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109761 _109763) (term1161 A B P lt2 z' _109761 s p _109762 _109763)). Qed.
Lemma lem8246714 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246715 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1162 A B P lt2 z' _109761 s p _109762 _109763) = (term1163 A B P lt2 z' s _109761 p _109762 _109763).
Proof. exact (@lem8246714 (term1014 A B P lt2 z' _109761 _109762 s _109763) (term945 A B P p _109761 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246731 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1164 A B P _109761 t _109762 _109763) = (term1164 A B P _109761 t _109762 _109763).
Proof. exact (eq_refl (term1164 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8246732 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1160 A B P t lt2 z' _109761 s p _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8246731 A B P _109761 t _109762 _109763) (@lem8246715 A B P lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246743 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1159 A B P t lt2 z' _109761 s p _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246698 A B P t lt2 z' _109761 s p _109762 _109763) (@lem8246732 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246744 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246693 A B P t lt2 z' _109761 s p _109762 _109763) (@lem8246743 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8246746 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1166 A B P p lt2 z' s _109761 t _109762 _109763) = (term1167 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8246745) (@lem8246744 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246770 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246771 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1154 A B P p _109761 t _109762 _109763) = (term1155 A B P _109761 t p _109762 _109763).
Proof. exact (@lem8246770 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246779 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8246780 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1168 A B P p _109761 t _109762 _109763) = (term1169 A B P _109761 t p _109762 _109763).
Proof. exact (MK_COMB (@lem8246779 A B P p _109761 _109763) (@lem8246771 A B P _109761 t p _109762 _109763)). Qed.
Lemma lem8246784 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246785 {A B P : Type'} (t : type557 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1169 A B P _109761 t p _109762 _109763) = (term1170 A B P t _109761 p _109762 _109763).
Proof. exact (@lem8246784 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109761 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246803 {A B P : Type'} (t : type557 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1168 A B P p _109761 t _109762 _109763) = (term1170 A B P t _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246780 A B P _109761 t p _109762 _109763) (@lem8246785 A B P t _109761 p _109762 _109763)). Qed.
Lemma lem8246804 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1156 A B P lt2 z' _109761 _109762 s _109763) = (term1156 A B P lt2 z' _109761 _109762 s _109763).
Proof. exact (eq_refl (term1156 A B P lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246805 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (t : type557 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1171 A B P lt2 z' s p _109761 t _109762 _109763) = (term1172 A B P lt2 z' s t _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8246804 A B P lt2 z' _109761 _109762 s _109763) (@lem8246803 A B P t _109761 p _109762 _109763)). Qed.
Lemma lem8246809 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246810 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1172 A B P lt2 z' s t _109761 p _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (@lem8246809 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term1014 A B P lt2 z' _109761 _109762 s _109763) (term1173 A B P _109761 p _109762 _109763)). Qed.
Lemma lem8246838 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1171 A B P lt2 z' s p _109761 t _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246805 A B P lt2 z' s t _109761 p _109762 _109763) (@lem8246810 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246839 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : ((term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1171 A B P lt2 z' s p _109761 t _109762 _109763)) = ((term1165 A B P t lt2 z' s _109761 p _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763)).
Proof. exact (MK_COMB (@lem8246746 A B P t lt2 z' s _109761 p _109762 _109763) (@lem8246838 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246841 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8246842 (x : Prop) : (x = x) = True.
Proof. exact (@lem8246841 Prop x). Qed.
Lemma lem8246843 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : ((term1165 A B P t lt2 z' s _109761 p _109762 _109763) = (term1165 A B P t lt2 z' s _109761 p _109762 _109763)) = True.
Proof. exact (@lem8246842 (term1165 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246844 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : ((term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1171 A B P lt2 z' s p _109761 t _109762 _109763)) = True.
Proof. exact (TRANS (@lem8246839 A B P t lt2 z' s _109761 p _109762 _109763) (@lem8246843 A B P t lt2 z' s _109761 p _109762 _109763)). Qed.
Lemma lem8246845 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : True = ((term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1171 A B P lt2 z' s p _109761 t _109762 _109763)).
Proof. exact (SYM (@lem8246844 A B P lt2 z' s p _109761 t _109762 _109763)). Qed.
Lemma lem8246846 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (s : P -> A) (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1112 A B P p lt2 z' s _109761 t _109762 _109763) = (term1171 A B P lt2 z' s p _109761 t _109762 _109763).
Proof. exact (EQ_MP (@lem8246845 A B P lt2 z' s p _109761 t _109762 _109763) (@lem0)). Qed.
Lemma lem8246847 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1171 A B P lt2 z' s p _109761 t _109762 _109763.
Proof. exact (EQ_MP (@lem8246846 A B P lt2 z' s p _109761 t _109762 _109763) (@lem8245877 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8246849 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8246850 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1171 A B P lt2 z' s p _109761 t _109762 _109763) = (term1174 A B P p t lt2 z' _109761 _109762 s _109763).
Proof. exact (@lem8246849 (term1168 A B P p _109761 t _109762 _109763) (term1014 A B P lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246852 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8246853 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1175 A B P p _109761 t _109762 _109763) = (term1176 A B P p _109761 t _109762 _109763).
Proof. exact (@lem8246852 (term945 A B P p _109761 _109763) (term1154 A B P p _109761 t _109762 _109763)). Qed.
Lemma lem8246855 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8246856 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term1141 A B P p _109761 _109763) = (term944 A B P p _109761 _109763).
Proof. exact (@lem8246855 (term944 A B P p _109761 _109763)). Qed.
Lemma lem8246857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8246858 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term1142 A B P p _109761 _109763) = (term965 A B P p _109761 _109763).
Proof. exact (MK_COMB (@lem8246857) (@lem8246856 A B P p _109761 _109763)). Qed.
Lemma lem8246860 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8246861 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1177 A B P p _109761 t _109762 _109763) = (term1178 A B P p _109761 t _109762 _109763).
Proof. exact (@lem8246860 (term945 A B P p _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8246863 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8246864 {A B P : Type'} (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1141 A B P p _109762 _109763) = (term944 A B P p _109762 _109763).
Proof. exact (@lem8246863 (term944 A B P p _109762 _109763)). Qed.
Lemma lem8246865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8246866 {A B P : Type'} (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1142 A B P p _109762 _109763) = (term965 A B P p _109762 _109763).
Proof. exact (MK_COMB (@lem8246865) (@lem8246864 A B P p _109762 _109763)). Qed.
Lemma lem8246867 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term973 A B P _109761 t _109762 _109763) = (term973 A B P _109761 t _109762 _109763).
Proof. exact (eq_refl (term973 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8246868 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1178 A B P p _109761 t _109762 _109763) = (term1179 A B P p _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8246866 A B P p _109762 _109763) (@lem8246867 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8246869 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1177 A B P p _109761 t _109762 _109763) = (term1179 A B P p _109761 t _109762 _109763).
Proof. exact (TRANS (@lem8246861 A B P p _109761 t _109762 _109763) (@lem8246868 A B P p _109761 t _109762 _109763)). Qed.
Lemma lem8246870 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1176 A B P p _109761 t _109762 _109763) = (term1180 A B P p _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8246858 A B P p _109761 _109763) (@lem8246869 A B P p _109761 t _109762 _109763)). Qed.
Lemma lem8246871 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1175 A B P p _109761 t _109762 _109763) = (term1180 A B P p _109761 t _109762 _109763).
Proof. exact (TRANS (@lem8246853 A B P p _109761 t _109762 _109763) (@lem8246870 A B P p _109761 t _109762 _109763)). Qed.
Lemma lem8246872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8246873 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1181 A B P p _109761 t _109762 _109763) = (term1182 A B P p _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8246872) (@lem8246871 A B P p _109761 t _109762 _109763)). Qed.
Lemma lem8246874 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1014 A B P lt2 z' _109761 _109762 s _109763) = (term1014 A B P lt2 z' _109761 _109762 s _109763).
Proof. exact (eq_refl (term1014 A B P lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246875 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1174 A B P p t lt2 z' _109761 _109762 s _109763) = (term1183 A B P p t lt2 z' _109761 _109762 s _109763).
Proof. exact (MK_COMB (@lem8246873 A B P p _109761 t _109762 _109763) (@lem8246874 A B P lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246876 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (s : P -> A) (_109763 : P) : (term1171 A B P lt2 z' s p _109761 t _109762 _109763) = (term1183 A B P p t lt2 z' _109761 _109762 s _109763).
Proof. exact (TRANS (@lem8246850 A B P p t lt2 z' _109761 _109762 s _109763) (@lem8246875 A B P p t lt2 z' _109761 _109762 s _109763)). Qed.
Lemma lem8246878 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term973 A B P f t g a') (h2 : term978 A B P p lt2 f s t g a') : term1179 A B P p f t g a'.
Proof. exact (conj (@lem8246618 A B P p lt2 f s t g a' h2) (@lem8246626 A B P f t g a' h1)). Qed.
Lemma lem8246879 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term973 A B P f t g a') (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : term1180 A B P p f t g a'.
Proof. exact (conj (@lem8246611 A B P p lt2 s f t g a' h2) (@lem8246878 A B P p lt2 f s t g a' h1 h3)). Qed.
Lemma lem8246881 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1183 A B P p t lt2 z' _109761 _109762 s _109763.
Proof. exact (EQ_MP (@lem8246876 A B P p t lt2 z' _109761 _109762 s _109763) (@lem8246847 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8246882 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1183 A B P p t lt2 z' _109761 _109762 s _109763.
Proof. exact (@lem8246881 A B P _109761 _109762 _109763 p lt2 s z' t h1). Qed.
Lemma lem8246883 {A B P : Type'} (f : A -> B) (g : A -> B) (a' : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1183 A B P p t lt2 z' f g s a'.
Proof. exact (@lem8246882 A B P f g a' p lt2 s z' t h1). Qed.
Lemma lem8246886 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1014 A B P lt2 z' f g s a'.
Proof. exact (@lem8246883 A B P f g a' p lt2 s z' t h1 (@lem8246879 A B P p lt2 f s t g a' h2 h3 h4)). Qed.
Lemma lem8246887 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1184 A B P lt2 z' f g s a'.
Proof. exact (fun h0 : term1185 A B P lt2 z' f g s a' => @lem8246886 A B P z' p lt2 f s t g a' h1 h2 h3 h4). Qed.
Lemma lem8246889 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246890 {A B P : Type'} (lt2 : type1402 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a' : P) : (term1184 A B P lt2 z' f g s a') = (term1014 A B P lt2 z' f g s a').
Proof. exact (@lem8246889 (term1014 A B P lt2 z' f g s a')). Qed.
Lemma lem8246891 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1014 A B P lt2 z' f g s a'.
Proof. exact (EQ_MP (@lem8246890 A B P lt2 z' f g s a') (@lem8246887 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8246897 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246898 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109764) = (term1186 A B P f g lt2 _109764 s a').
Proof. exact (@lem8246897 ((@I (A -> B) f _109764) = (@I (A -> B) g _109764)) (term957 A P lt2 _109764 s a')). Qed.
Lemma lem8246906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8246907 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term1187 A B P lt2 s a' f g _109764) = (term1188 A B P f g lt2 _109764 s a').
Proof. exact (MK_COMB (@lem8246906) (@lem8246898 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246915 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term1186 A B P f g lt2 _109764 s a') = (term1186 A B P f g lt2 _109764 s a').
Proof. exact (eq_refl (term1186 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246916 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109764) = (term1186 A B P f g lt2 _109764 s a')) = ((term1186 A B P f g lt2 _109764 s a') = (term1186 A B P f g lt2 _109764 s a')).
Proof. exact (MK_COMB (@lem8246907 A B P f g lt2 _109764 s a') (@lem8246915 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246918 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8246919 (x : Prop) : (x = x) = True.
Proof. exact (@lem8246918 Prop x). Qed.
Lemma lem8246920 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : ((term1186 A B P f g lt2 _109764 s a') = (term1186 A B P f g lt2 _109764 s a')) = True.
Proof. exact (@lem8246919 (term1186 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246921 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109764) = (term1186 A B P f g lt2 _109764 s a')) = True.
Proof. exact (TRANS (@lem8246916 A B P f g lt2 _109764 s a') (@lem8246920 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246922 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : True = ((term960 A B P lt2 s a' f g _109764) = (term1186 A B P f g lt2 _109764 s a')).
Proof. exact (SYM (@lem8246921 A B P f g lt2 _109764 s a')). Qed.
Lemma lem8246923 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109764) = (term1186 A B P f g lt2 _109764 s a').
Proof. exact (EQ_MP (@lem8246922 A B P f g lt2 _109764 s a') (@lem0)). Qed.
Lemma lem8246924 {A B P : Type'} (_109764 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1186 A B P f g lt2 _109764 s a'.
Proof. exact (EQ_MP (@lem8246923 A B P f g lt2 _109764 s a') (@lem8245857 A B P _109764 p lt2 s f t g a' h1)). Qed.
Lemma lem8246926 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8246927 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109764 : A) : (term1186 A B P f g lt2 _109764 s a') = (term1189 A B P lt2 s a' f g _109764).
Proof. exact (@lem8246926 (term957 A P lt2 _109764 s a') ((@I (A -> B) f _109764) = (@I (A -> B) g _109764))). Qed.
Lemma lem8246929 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8246930 {A P : Type'} (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term1190 A P lt2 _109764 s a') = (term932 A P lt2 _109764 s a').
Proof. exact (@lem8246929 (term932 A P lt2 _109764 s a')). Qed.
Lemma lem8246931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8246932 {A P : Type'} (lt2 : type1402 A) (_109764 : A) (s : P -> A) (a' : P) : (term1191 A P lt2 _109764 s a') = (term1192 A P lt2 _109764 s a').
Proof. exact (MK_COMB (@lem8246931) (@lem8246930 A P lt2 _109764 s a')). Qed.
Lemma lem8246933 {A B : Type'} (f : A -> B) (g : A -> B) (_109764 : A) : ((@I (A -> B) f _109764) = (@I (A -> B) g _109764)) = ((@I (A -> B) f _109764) = (@I (A -> B) g _109764)).
Proof. exact (eq_refl ((@I (A -> B) f _109764) = (@I (A -> B) g _109764))). Qed.
Lemma lem8246934 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109764 : A) : (term1189 A B P lt2 s a' f g _109764) = (term1193 A B P lt2 s a' f g _109764).
Proof. exact (MK_COMB (@lem8246932 A P lt2 _109764 s a') (@lem8246933 A B f g _109764)). Qed.
Lemma lem8246935 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109764 : A) : (term1186 A B P f g lt2 _109764 s a') = (term1193 A B P lt2 s a' f g _109764).
Proof. exact (TRANS (@lem8246927 A B P lt2 s a' f g _109764) (@lem8246934 A B P lt2 s a' f g _109764)). Qed.
Lemma lem8246938 {A B P : Type'} (_109764 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1193 A B P lt2 s a' f g _109764.
Proof. exact (EQ_MP (@lem8246935 A B P lt2 s a' f g _109764) (@lem8246924 A B P _109764 p lt2 s f t g a' h1)). Qed.
Lemma lem8246939 {A B P : Type'} (_109764 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1193 A B P lt2 s a' f g _109764.
Proof. exact (@lem8246938 A B P _109764 p lt2 s f t g a' h1). Qed.
Lemma lem8246940 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1194 A B P lt2 s z' f g a'.
Proof. exact (@lem8246939 A B P (term997 A B P z' f g a') p lt2 s f t g a' h1). Qed.
Lemma lem8246943 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : (term1000 A B P z' f g a') = (term1003 A B P z' f g a').
Proof. exact (@lem8246940 A B P z' p lt2 s f t g a' h3 (@lem8246891 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8246944 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1195 A B P z' f g a'.
Proof. exact (fun h0 : term1007 A B P z' f g a' => @lem8246943 A B P z' p lt2 f s t g a' h1 h2 h3 h4). Qed.
Lemma lem8246946 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8246947 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a' : P) : (term1195 A B P z' f g a') = ((term1000 A B P z' f g a') = (term1003 A B P z' f g a')).
Proof. exact (@lem8246946 ((term1000 A B P z' f g a') = (term1003 A B P z' f g a'))). Qed.
Lemma lem8246948 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : (term1000 A B P z' f g a') = (term1003 A B P z' f g a').
Proof. exact (EQ_MP (@lem8246947 A B P z' f g a') (@lem8246944 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8246964 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246965 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1115 A B P p z' _109761 t _109762 _109763) = (term1196 A B P z' p _109761 t _109762 _109763).
Proof. exact (@lem8246964 (term1007 A B P z' _109761 _109762 _109763) (term945 A B P p _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8246981 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8246982 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1154 A B P p _109761 t _109762 _109763) = (term1155 A B P _109761 t p _109762 _109763).
Proof. exact (@lem8246981 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8246990 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1197 A B P z' _109761 _109762 _109763) = (term1197 A B P z' _109761 _109762 _109763).
Proof. exact (eq_refl (term1197 A B P z' _109761 _109762 _109763)). Qed.
Lemma lem8246991 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1196 A B P z' p _109761 t _109762 _109763) = (term1198 A B P z' _109761 t p _109762 _109763).
Proof. exact (MK_COMB (@lem8246990 A B P z' _109761 _109762 _109763) (@lem8246982 A B P _109761 t p _109762 _109763)). Qed.
Lemma lem8246995 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8246996 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1198 A B P z' _109761 t p _109762 _109763) = (term1199 A B P t z' _109761 p _109762 _109763).
Proof. exact (@lem8246995 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term1007 A B P z' _109761 _109762 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8247016 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1196 A B P z' p _109761 t _109762 _109763) = (term1199 A B P t z' _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246991 A B P z' _109761 t p _109762 _109763) (@lem8246996 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247017 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1115 A B P p z' _109761 t _109762 _109763) = (term1199 A B P t z' _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8246965 A B P z' p _109761 t _109762 _109763) (@lem8247016 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247018 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8247019 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1116 A B P p z' _109761 t _109762 _109763) = (term1200 A B P t z' _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8247018 A B P p _109761 _109763) (@lem8247017 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247023 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8247024 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1200 A B P t z' _109761 p _109762 _109763) = (term1201 A B P t z' _109761 p _109762 _109763).
Proof. exact (@lem8247023 ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) (term945 A B P p _109761 _109763) (term1202 A B P z' _109761 p _109762 _109763)). Qed.
Lemma lem8247040 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8247041 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1203 A B P z' _109761 p _109762 _109763) = (term1204 A B P z' _109761 p _109762 _109763).
Proof. exact (@lem8247040 (term1007 A B P z' _109761 _109762 _109763) (term945 A B P p _109761 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8247059 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1164 A B P _109761 t _109762 _109763) = (term1164 A B P _109761 t _109762 _109763).
Proof. exact (eq_refl (term1164 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8247060 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1201 A B P t z' _109761 p _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8247059 A B P _109761 t _109762 _109763) (@lem8247041 A B P z' _109761 p _109762 _109763)). Qed.
Lemma lem8247071 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1200 A B P t z' _109761 p _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8247024 A B P t z' _109761 p _109762 _109763) (@lem8247060 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247072 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1116 A B P p z' _109761 t _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8247019 A B P t z' _109761 p _109762 _109763) (@lem8247071 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8247074 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1206 A B P p z' _109761 t _109762 _109763) = (term1207 A B P t z' _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8247073) (@lem8247072 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8247101 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1071 A B P p z' _109761 _109762 _109763) = (term1202 A B P z' _109761 p _109762 _109763).
Proof. exact (@lem8247100 (term1007 A B P z' _109761 _109762 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8247109 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term946 A B P p _109761 _109763) = (term946 A B P p _109761 _109763).
Proof. exact (eq_refl (term946 A B P p _109761 _109763)). Qed.
Lemma lem8247110 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1076 A B P p z' _109761 _109762 _109763) = (term1203 A B P z' _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8247109 A B P p _109761 _109763) (@lem8247101 A B P z' _109761 p _109762 _109763)). Qed.
Lemma lem8247114 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8247115 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1203 A B P z' _109761 p _109762 _109763) = (term1204 A B P z' _109761 p _109762 _109763).
Proof. exact (@lem8247114 (term1007 A B P z' _109761 _109762 _109763) (term945 A B P p _109761 _109763) (term945 A B P p _109762 _109763)). Qed.
Lemma lem8247133 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1076 A B P p z' _109761 _109762 _109763) = (term1204 A B P z' _109761 p _109762 _109763).
Proof. exact (TRANS (@lem8247110 A B P z' _109761 p _109762 _109763) (@lem8247115 A B P z' _109761 p _109762 _109763)). Qed.
Lemma lem8247134 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1164 A B P _109761 t _109762 _109763) = (term1164 A B P _109761 t _109762 _109763).
Proof. exact (eq_refl (term1164 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8247135 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1208 A B P t p z' _109761 _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763).
Proof. exact (MK_COMB (@lem8247134 A B P _109761 t _109762 _109763) (@lem8247133 A B P z' _109761 p _109762 _109763)). Qed.
Lemma lem8247146 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : ((term1116 A B P p z' _109761 t _109762 _109763) = (term1208 A B P t p z' _109761 _109762 _109763)) = ((term1205 A B P t z' _109761 p _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763)).
Proof. exact (MK_COMB (@lem8247074 A B P t z' _109761 p _109762 _109763) (@lem8247135 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247148 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8247149 (x : Prop) : (x = x) = True.
Proof. exact (@lem8247148 Prop x). Qed.
Lemma lem8247150 {A B P : Type'} (t : type557 A B P) (z' : type518 A B P) (_109761 : A -> B) (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : ((term1205 A B P t z' _109761 p _109762 _109763) = (term1205 A B P t z' _109761 p _109762 _109763)) = True.
Proof. exact (@lem8247149 (term1205 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247151 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : ((term1116 A B P p z' _109761 t _109762 _109763) = (term1208 A B P t p z' _109761 _109762 _109763)) = True.
Proof. exact (TRANS (@lem8247146 A B P t z' _109761 p _109762 _109763) (@lem8247150 A B P t z' _109761 p _109762 _109763)). Qed.
Lemma lem8247152 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : True = ((term1116 A B P p z' _109761 t _109762 _109763) = (term1208 A B P t p z' _109761 _109762 _109763)).
Proof. exact (SYM (@lem8247151 A B P t p z' _109761 _109762 _109763)). Qed.
Lemma lem8247153 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1116 A B P p z' _109761 t _109762 _109763) = (term1208 A B P t p z' _109761 _109762 _109763).
Proof. exact (EQ_MP (@lem8247152 A B P t p z' _109761 _109762 _109763) (@lem0)). Qed.
Lemma lem8247154 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1208 A B P t p z' _109761 _109762 _109763.
Proof. exact (EQ_MP (@lem8247153 A B P t p z' _109761 _109762 _109763) (@lem8245895 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8247156 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247157 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1208 A B P t p z' _109761 _109762 _109763) = (term1209 A B P p z' _109761 t _109762 _109763).
Proof. exact (@lem8247156 (term1076 A B P p z' _109761 _109762 _109763) ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8247159 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247160 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1210 A B P p z' _109761 _109762 _109763) = (term1211 A B P p z' _109761 _109762 _109763).
Proof. exact (@lem8247159 (term945 A B P p _109761 _109763) (term1071 A B P p z' _109761 _109762 _109763)). Qed.
Lemma lem8247162 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247163 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term1141 A B P p _109761 _109763) = (term944 A B P p _109761 _109763).
Proof. exact (@lem8247162 (term944 A B P p _109761 _109763)). Qed.
Lemma lem8247164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8247165 {A B P : Type'} (p : type560 A B P) (_109761 : A -> B) (_109763 : P) : (term1142 A B P p _109761 _109763) = (term965 A B P p _109761 _109763).
Proof. exact (MK_COMB (@lem8247164) (@lem8247163 A B P p _109761 _109763)). Qed.
Lemma lem8247167 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247168 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1212 A B P p z' _109761 _109762 _109763) = (term1213 A B P p z' _109761 _109762 _109763).
Proof. exact (@lem8247167 (term945 A B P p _109762 _109763) (term1007 A B P z' _109761 _109762 _109763)). Qed.
Lemma lem8247170 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247171 {A B P : Type'} (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1141 A B P p _109762 _109763) = (term944 A B P p _109762 _109763).
Proof. exact (@lem8247170 (term944 A B P p _109762 _109763)). Qed.
Lemma lem8247172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8247173 {A B P : Type'} (p : type560 A B P) (_109762 : A -> B) (_109763 : P) : (term1142 A B P p _109762 _109763) = (term965 A B P p _109762 _109763).
Proof. exact (MK_COMB (@lem8247172) (@lem8247171 A B P p _109762 _109763)). Qed.
Lemma lem8247175 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247176 {A B P : Type'} (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1214 A B P z' _109761 _109762 _109763) = ((term1000 A B P z' _109761 _109762 _109763) = (term1003 A B P z' _109761 _109762 _109763)).
Proof. exact (@lem8247175 ((term1000 A B P z' _109761 _109762 _109763) = (term1003 A B P z' _109761 _109762 _109763))). Qed.
Lemma lem8247177 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1213 A B P p z' _109761 _109762 _109763) = (term1215 A B P p z' _109761 _109762 _109763).
Proof. exact (MK_COMB (@lem8247173 A B P p _109762 _109763) (@lem8247176 A B P z' _109761 _109762 _109763)). Qed.
Lemma lem8247178 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1212 A B P p z' _109761 _109762 _109763) = (term1215 A B P p z' _109761 _109762 _109763).
Proof. exact (TRANS (@lem8247168 A B P p z' _109761 _109762 _109763) (@lem8247177 A B P p z' _109761 _109762 _109763)). Qed.
Lemma lem8247179 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1211 A B P p z' _109761 _109762 _109763) = (term1216 A B P p z' _109761 _109762 _109763).
Proof. exact (MK_COMB (@lem8247165 A B P p _109761 _109763) (@lem8247178 A B P p z' _109761 _109762 _109763)). Qed.
Lemma lem8247180 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1210 A B P p z' _109761 _109762 _109763) = (term1216 A B P p z' _109761 _109762 _109763).
Proof. exact (TRANS (@lem8247160 A B P p z' _109761 _109762 _109763) (@lem8247179 A B P p z' _109761 _109762 _109763)). Qed.
Lemma lem8247181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247182 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) : (term1217 A B P p z' _109761 _109762 _109763) = (term1218 A B P p z' _109761 _109762 _109763).
Proof. exact (MK_COMB (@lem8247181) (@lem8247180 A B P p z' _109761 _109762 _109763)). Qed.
Lemma lem8247183 {A B P : Type'} (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)) = ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763)).
Proof. exact (eq_refl ((term933 A B P t _109761 _109763) = (term933 A B P t _109762 _109763))). Qed.
Lemma lem8247184 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1209 A B P p z' _109761 t _109762 _109763) = (term1219 A B P p z' _109761 t _109762 _109763).
Proof. exact (MK_COMB (@lem8247182 A B P p z' _109761 _109762 _109763) (@lem8247183 A B P _109761 t _109762 _109763)). Qed.
Lemma lem8247185 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109761 : A -> B) (t : type557 A B P) (_109762 : A -> B) (_109763 : P) : (term1208 A B P t p z' _109761 _109762 _109763) = (term1219 A B P p z' _109761 t _109762 _109763).
Proof. exact (TRANS (@lem8247157 A B P p z' _109761 t _109762 _109763) (@lem8247184 A B P p z' _109761 t _109762 _109763)). Qed.
Lemma lem8247187 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1215 A B P p z' f g a'.
Proof. exact (conj (@lem8246604 A B P p lt2 f s t g a' h4) (@lem8246948 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8247188 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : term1216 A B P p z' f g a'.
Proof. exact (conj (@lem8246597 A B P p lt2 s f t g a' h3) (@lem8247187 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8247190 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1219 A B P p z' _109761 t _109762 _109763.
Proof. exact (EQ_MP (@lem8247185 A B P p z' _109761 t _109762 _109763) (@lem8247154 A B P _109761 _109762 _109763 p lt2 s z' t h1)). Qed.
Lemma lem8247191 {A B P : Type'} (_109761 : A -> B) (_109762 : A -> B) (_109763 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1219 A B P p z' _109761 t _109762 _109763.
Proof. exact (@lem8247190 A B P _109761 _109762 _109763 p lt2 s z' t h1). Qed.
Lemma lem8247192 {A B P : Type'} (f : A -> B) (g : A -> B) (a' : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z' : type518 A B P) (t : type557 A B P) (h1 : term551 A B P p lt2 s z' t) : term1219 A B P p z' f t g a'.
Proof. exact (@lem8247191 A B P f g a' p lt2 s z' t h1). Qed.
Lemma lem8247195 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term973 A B P f t g a') (h3 : term975 A B P p lt2 s f t g a') (h4 : term978 A B P p lt2 f s t g a') : (term933 A B P t f a') = (term933 A B P t g a').
Proof. exact (@lem8247192 A B P f g a' p lt2 s z' t h1 (@lem8247188 A B P z' p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8247196 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : term1220 A B P f t g a'.
Proof. exact (fun h0 : term973 A B P f t g a' => @lem8247195 A B P z' p lt2 f s t g a' h1 h0 h2 h3). Qed.
Lemma lem8247198 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247199 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term1220 A B P f t g a') = ((term933 A B P t f a') = (term933 A B P t g a')).
Proof. exact (@lem8247198 ((term933 A B P t f a') = (term933 A B P t g a'))). Qed.
Lemma lem8247200 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : (term933 A B P t f a') = (term933 A B P t g a').
Proof. exact (EQ_MP (@lem8247199 A B P f t g a') (@lem8247196 A B P z' p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247203 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8247205 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) : (term973 A B P f t g a') = (term1221 A B P f t g a').
Proof. exact (@lem8247203 ((term933 A B P t f a') = (term933 A B P t g a'))). Qed.
Lemma lem8247208 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term975 A B P p lt2 s f t g a') : term1221 A B P f t g a'.
Proof. exact (EQ_MP (@lem8247205 A B P f t g a') (@lem8245859 A B P p lt2 s f t g a' h1)). Qed.
Lemma lem8247211 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : False.
Proof. exact (@lem8247208 A B P p lt2 s f t g a' h2 (@lem8247200 A B P z' p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247212 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : term1150.
Proof. exact (fun h0 : ~ False => @lem8247211 A B P z' p lt2 f s t g a' h1 h2 h3). Qed.
Lemma lem8247214 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247215 : term1150 = False.
Proof. exact (@lem8247214 False). Qed.
Lemma lem8247216 {A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term551 A B P p lt2 s z' t) (h2 : term975 A B P p lt2 s f t g a') (h3 : term978 A B P p lt2 f s t g a') : False.
Proof. exact (EQ_MP (@lem8247215) (@lem8247212 A B P z' p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247369 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) (h1 : term945 A B P p f a') : term945 A B P p f a'.
Proof. exact (h1). Qed.
Lemma lem8247370 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) (h1 : term945 A B P p f a') : term1222 A B P p f a'.
Proof. exact (fun h0 : term944 A B P p f a' => @lem8247369 A B P p f a' h1). Qed.
Lemma lem8247372 (p : Prop) : (term1152 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8247373 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1222 A B P p f a') = (term945 A B P p f a').
Proof. exact (@lem8247372 (term944 A B P p f a')). Qed.
Lemma lem8247374 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) (h1 : term945 A B P p f a') : term945 A B P p f a'.
Proof. exact (EQ_MP (@lem8247373 A B P p f a') (@lem8247370 A B P p f a' h1)). Qed.
Lemma lem8247376 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (proj1 (@lem8244850 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8247377 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term1121 A B P p g a'.
Proof. exact (fun h0 : term945 A B P p g a' => @lem8247376 A B P p lt2 f s t g a' h1). Qed.
Lemma lem8247379 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247380 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1121 A B P p g a') = (term944 A B P p g a').
Proof. exact (@lem8247379 (term944 A B P p g a')). Qed.
Lemma lem8247381 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (EQ_MP (@lem8247380 A B P p g a') (@lem8247377 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8247383 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247384 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (s : P -> A) (_109770 : P) : (term1117 A B P lt2 z s _109768 p _109769 _109770) = (term1223 A B P p lt2 z _109768 _109769 s _109770).
Proof. exact (@lem8247383 (term991 A B P _109768 p _109769 _109770) (term1014 A B P lt2 z _109768 _109769 s _109770)). Qed.
Lemma lem8247386 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247387 {A B P : Type'} (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1224 A B P _109768 p _109769 _109770) = (term1225 A B P _109768 p _109769 _109770).
Proof. exact (@lem8247386 (term944 A B P p _109768 _109770) (term945 A B P p _109769 _109770)). Qed.
Lemma lem8247389 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247390 {A B P : Type'} (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1141 A B P p _109769 _109770) = (term944 A B P p _109769 _109770).
Proof. exact (@lem8247389 (term944 A B P p _109769 _109770)). Qed.
Lemma lem8247391 {A B P : Type'} (p : type560 A B P) (_109768 : A -> B) (_109770 : P) : (term967 A B P p _109768 _109770) = (term967 A B P p _109768 _109770).
Proof. exact (eq_refl (term967 A B P p _109768 _109770)). Qed.
Lemma lem8247392 {A B P : Type'} (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1225 A B P _109768 p _109769 _109770) = (term1226 A B P _109768 p _109769 _109770).
Proof. exact (MK_COMB (@lem8247391 A B P p _109768 _109770) (@lem8247390 A B P p _109769 _109770)). Qed.
Lemma lem8247393 {A B P : Type'} (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1224 A B P _109768 p _109769 _109770) = (term1226 A B P _109768 p _109769 _109770).
Proof. exact (TRANS (@lem8247387 A B P _109768 p _109769 _109770) (@lem8247392 A B P _109768 p _109769 _109770)). Qed.
Lemma lem8247394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247395 {A B P : Type'} (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1227 A B P _109768 p _109769 _109770) = (term1228 A B P _109768 p _109769 _109770).
Proof. exact (MK_COMB (@lem8247394) (@lem8247393 A B P _109768 p _109769 _109770)). Qed.
Lemma lem8247396 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (s : P -> A) (_109770 : P) : (term1014 A B P lt2 z _109768 _109769 s _109770) = (term1014 A B P lt2 z _109768 _109769 s _109770).
Proof. exact (eq_refl (term1014 A B P lt2 z _109768 _109769 s _109770)). Qed.
Lemma lem8247397 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (s : P -> A) (_109770 : P) : (term1223 A B P p lt2 z _109768 _109769 s _109770) = (term1229 A B P p lt2 z _109768 _109769 s _109770).
Proof. exact (MK_COMB (@lem8247395 A B P _109768 p _109769 _109770) (@lem8247396 A B P lt2 z _109768 _109769 s _109770)). Qed.
Lemma lem8247398 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (s : P -> A) (_109770 : P) : (term1117 A B P lt2 z s _109768 p _109769 _109770) = (term1229 A B P p lt2 z _109768 _109769 s _109770).
Proof. exact (TRANS (@lem8247384 A B P p lt2 z _109768 _109769 s _109770) (@lem8247397 A B P p lt2 z _109768 _109769 s _109770)). Qed.
Lemma lem8247400 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term945 A B P p f a') (h2 : term978 A B P p lt2 f s t g a') : term1226 A B P f p g a'.
Proof. exact (conj (@lem8247374 A B P p f a' h1) (@lem8247381 A B P p lt2 f s t g a' h2)). Qed.
Lemma lem8247402 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1229 A B P p lt2 z _109768 _109769 s _109770.
Proof. exact (EQ_MP (@lem8247398 A B P p lt2 z _109768 _109769 s _109770) (@lem8246023 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8247403 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1229 A B P p lt2 z _109768 _109769 s _109770.
Proof. exact (@lem8247402 A B P _109768 _109769 _109770 lt2 s z p h1). Qed.
Lemma lem8247404 {A B P : Type'} (f : A -> B) (g : A -> B) (a' : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1229 A B P p lt2 z f g s a'.
Proof. exact (@lem8247403 A B P f g a' lt2 s z p h1). Qed.
Lemma lem8247407 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term978 A B P p lt2 f s t g a') : term1014 A B P lt2 z f g s a'.
Proof. exact (@lem8247404 A B P f g a' lt2 s z p h1 (@lem8247400 A B P p lt2 f s t g a' h2 h3)). Qed.
Lemma lem8247408 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term978 A B P p lt2 f s t g a') : term1184 A B P lt2 z f g s a'.
Proof. exact (fun h0 : term1185 A B P lt2 z f g s a' => @lem8247407 A B P z p lt2 f s t g a' h1 h2 h3). Qed.
Lemma lem8247410 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247411 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a' : P) : (term1184 A B P lt2 z f g s a') = (term1014 A B P lt2 z f g s a').
Proof. exact (@lem8247410 (term1014 A B P lt2 z f g s a')). Qed.
Lemma lem8247412 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term978 A B P p lt2 f s t g a') : term1014 A B P lt2 z f g s a'.
Proof. exact (EQ_MP (@lem8247411 A B P lt2 z f g s a') (@lem8247408 A B P z p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247418 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8247419 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109774) = (term1186 A B P f g lt2 _109774 s a').
Proof. exact (@lem8247418 ((@I (A -> B) f _109774) = (@I (A -> B) g _109774)) (term957 A P lt2 _109774 s a')). Qed.
Lemma lem8247427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8247428 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term1187 A B P lt2 s a' f g _109774) = (term1188 A B P f g lt2 _109774 s a').
Proof. exact (MK_COMB (@lem8247427) (@lem8247419 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247436 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term1186 A B P f g lt2 _109774 s a') = (term1186 A B P f g lt2 _109774 s a').
Proof. exact (eq_refl (term1186 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247437 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109774) = (term1186 A B P f g lt2 _109774 s a')) = ((term1186 A B P f g lt2 _109774 s a') = (term1186 A B P f g lt2 _109774 s a')).
Proof. exact (MK_COMB (@lem8247428 A B P f g lt2 _109774 s a') (@lem8247436 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247439 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8247440 (x : Prop) : (x = x) = True.
Proof. exact (@lem8247439 Prop x). Qed.
Lemma lem8247441 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : ((term1186 A B P f g lt2 _109774 s a') = (term1186 A B P f g lt2 _109774 s a')) = True.
Proof. exact (@lem8247440 (term1186 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247442 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109774) = (term1186 A B P f g lt2 _109774 s a')) = True.
Proof. exact (TRANS (@lem8247437 A B P f g lt2 _109774 s a') (@lem8247441 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247443 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : True = ((term960 A B P lt2 s a' f g _109774) = (term1186 A B P f g lt2 _109774 s a')).
Proof. exact (SYM (@lem8247442 A B P f g lt2 _109774 s a')). Qed.
Lemma lem8247444 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109774) = (term1186 A B P f g lt2 _109774 s a').
Proof. exact (EQ_MP (@lem8247443 A B P f g lt2 _109774 s a') (@lem0)). Qed.
Lemma lem8247445 {A B P : Type'} (_109774 : A) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1186 A B P f g lt2 _109774 s a'.
Proof. exact (EQ_MP (@lem8247444 A B P f g lt2 _109774 s a') (@lem8245955 A B P _109774 p lt2 f s t g a' h1)). Qed.
Lemma lem8247447 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247448 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109774 : A) : (term1186 A B P f g lt2 _109774 s a') = (term1189 A B P lt2 s a' f g _109774).
Proof. exact (@lem8247447 (term957 A P lt2 _109774 s a') ((@I (A -> B) f _109774) = (@I (A -> B) g _109774))). Qed.
Lemma lem8247450 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247451 {A P : Type'} (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term1190 A P lt2 _109774 s a') = (term932 A P lt2 _109774 s a').
Proof. exact (@lem8247450 (term932 A P lt2 _109774 s a')). Qed.
Lemma lem8247452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247453 {A P : Type'} (lt2 : type1402 A) (_109774 : A) (s : P -> A) (a' : P) : (term1191 A P lt2 _109774 s a') = (term1192 A P lt2 _109774 s a').
Proof. exact (MK_COMB (@lem8247452) (@lem8247451 A P lt2 _109774 s a')). Qed.
Lemma lem8247454 {A B : Type'} (f : A -> B) (g : A -> B) (_109774 : A) : ((@I (A -> B) f _109774) = (@I (A -> B) g _109774)) = ((@I (A -> B) f _109774) = (@I (A -> B) g _109774)).
Proof. exact (eq_refl ((@I (A -> B) f _109774) = (@I (A -> B) g _109774))). Qed.
Lemma lem8247455 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109774 : A) : (term1189 A B P lt2 s a' f g _109774) = (term1193 A B P lt2 s a' f g _109774).
Proof. exact (MK_COMB (@lem8247453 A P lt2 _109774 s a') (@lem8247454 A B f g _109774)). Qed.
Lemma lem8247456 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109774 : A) : (term1186 A B P f g lt2 _109774 s a') = (term1193 A B P lt2 s a' f g _109774).
Proof. exact (TRANS (@lem8247448 A B P lt2 s a' f g _109774) (@lem8247455 A B P lt2 s a' f g _109774)). Qed.
Lemma lem8247459 {A B P : Type'} (_109774 : A) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1193 A B P lt2 s a' f g _109774.
Proof. exact (EQ_MP (@lem8247456 A B P lt2 s a' f g _109774) (@lem8247445 A B P _109774 p lt2 f s t g a' h1)). Qed.
Lemma lem8247460 {A B P : Type'} (_109774 : A) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1193 A B P lt2 s a' f g _109774.
Proof. exact (@lem8247459 A B P _109774 p lt2 f s t g a' h1). Qed.
Lemma lem8247461 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1194 A B P lt2 s z f g a'.
Proof. exact (@lem8247460 A B P (term997 A B P z f g a') p lt2 f s t g a' h1). Qed.
Lemma lem8247464 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term972 A B P p lt2 f s t g a') (h4 : term978 A B P p lt2 f s t g a') : (term1000 A B P z f g a') = (term1003 A B P z f g a').
Proof. exact (@lem8247461 A B P z p lt2 f s t g a' h3 (@lem8247412 A B P z p lt2 f s t g a' h1 h2 h4)). Qed.
Lemma lem8247465 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term972 A B P p lt2 f s t g a') (h4 : term978 A B P p lt2 f s t g a') : term1195 A B P z f g a'.
Proof. exact (fun h0 : term1007 A B P z f g a' => @lem8247464 A B P z p lt2 f s t g a' h1 h2 h3 h4). Qed.
Lemma lem8247467 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247468 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a' : P) : (term1195 A B P z f g a') = ((term1000 A B P z f g a') = (term1003 A B P z f g a')).
Proof. exact (@lem8247467 ((term1000 A B P z f g a') = (term1003 A B P z f g a'))). Qed.
Lemma lem8247469 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term972 A B P p lt2 f s t g a') (h4 : term978 A B P p lt2 f s t g a') : (term1000 A B P z f g a') = (term1003 A B P z f g a').
Proof. exact (EQ_MP (@lem8247468 A B P z f g a') (@lem8247465 A B P z p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8247471 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (proj1 (@lem8244850 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8247472 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term1121 A B P p g a'.
Proof. exact (fun h0 : term945 A B P p g a' => @lem8247471 A B P p lt2 f s t g a' h1). Qed.
Lemma lem8247474 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247475 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1121 A B P p g a') = (term944 A B P p g a').
Proof. exact (@lem8247474 (term944 A B P p g a')). Qed.
Lemma lem8247476 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term978 A B P p lt2 f s t g a') : term944 A B P p g a'.
Proof. exact (EQ_MP (@lem8247475 A B P p g a') (@lem8247472 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8247482 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8247483 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1118 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770).
Proof. exact (@lem8247482 (term944 A B P p _109768 _109770) (term1007 A B P z _109768 _109769 _109770) (term945 A B P p _109769 _109770)). Qed.
Lemma lem8247501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8247502 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1231 A B P z _109768 p _109769 _109770) = (term1232 A B P z _109768 p _109769 _109770).
Proof. exact (MK_COMB (@lem8247501) (@lem8247483 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247520 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1230 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770).
Proof. exact (eq_refl (term1230 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247521 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : ((term1118 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770)) = ((term1230 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770)).
Proof. exact (MK_COMB (@lem8247502 A B P z _109768 p _109769 _109770) (@lem8247520 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8247524 (x : Prop) : (x = x) = True.
Proof. exact (@lem8247523 Prop x). Qed.
Lemma lem8247525 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : ((term1230 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770)) = True.
Proof. exact (@lem8247524 (term1230 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247526 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : ((term1118 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770)) = True.
Proof. exact (TRANS (@lem8247521 A B P z _109768 p _109769 _109770) (@lem8247525 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247527 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : True = ((term1118 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770)).
Proof. exact (SYM (@lem8247526 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247528 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1118 A B P z _109768 p _109769 _109770) = (term1230 A B P z _109768 p _109769 _109770).
Proof. exact (EQ_MP (@lem8247527 A B P z _109768 p _109769 _109770) (@lem0)). Qed.
Lemma lem8247529 {A B P : Type'} (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1230 A B P z _109768 p _109769 _109770.
Proof. exact (EQ_MP (@lem8247528 A B P z _109768 p _109769 _109770) (@lem8246033 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8247531 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247532 {A B P : Type'} (z : type518 A B P) (_109769 : A -> B) (p : type560 A B P) (_109768 : A -> B) (_109770 : P) : (term1230 A B P z _109768 p _109769 _109770) = (term1233 A B P z _109769 p _109768 _109770).
Proof. exact (@lem8247531 (term1202 A B P z _109768 p _109769 _109770) (term944 A B P p _109768 _109770)). Qed.
Lemma lem8247534 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247535 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1234 A B P z _109768 p _109769 _109770) = (term1235 A B P z _109768 p _109769 _109770).
Proof. exact (@lem8247534 (term1007 A B P z _109768 _109769 _109770) (term945 A B P p _109769 _109770)). Qed.
Lemma lem8247537 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247538 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) : (term1214 A B P z _109768 _109769 _109770) = ((term1000 A B P z _109768 _109769 _109770) = (term1003 A B P z _109768 _109769 _109770)).
Proof. exact (@lem8247537 ((term1000 A B P z _109768 _109769 _109770) = (term1003 A B P z _109768 _109769 _109770))). Qed.
Lemma lem8247539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8247540 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (_109769 : A -> B) (_109770 : P) : (term1236 A B P z _109768 _109769 _109770) = (term1237 A B P z _109768 _109769 _109770).
Proof. exact (MK_COMB (@lem8247539) (@lem8247538 A B P z _109768 _109769 _109770)). Qed.
Lemma lem8247542 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247543 {A B P : Type'} (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1141 A B P p _109769 _109770) = (term944 A B P p _109769 _109770).
Proof. exact (@lem8247542 (term944 A B P p _109769 _109770)). Qed.
Lemma lem8247544 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1235 A B P z _109768 p _109769 _109770) = (term1238 A B P z _109768 p _109769 _109770).
Proof. exact (MK_COMB (@lem8247540 A B P z _109768 _109769 _109770) (@lem8247543 A B P p _109769 _109770)). Qed.
Lemma lem8247545 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1234 A B P z _109768 p _109769 _109770) = (term1238 A B P z _109768 p _109769 _109770).
Proof. exact (TRANS (@lem8247535 A B P z _109768 p _109769 _109770) (@lem8247544 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247547 {A B P : Type'} (z : type518 A B P) (_109768 : A -> B) (p : type560 A B P) (_109769 : A -> B) (_109770 : P) : (term1239 A B P z _109768 p _109769 _109770) = (term1240 A B P z _109768 p _109769 _109770).
Proof. exact (MK_COMB (@lem8247546) (@lem8247545 A B P z _109768 p _109769 _109770)). Qed.
Lemma lem8247548 {A B P : Type'} (p : type560 A B P) (_109768 : A -> B) (_109770 : P) : (term944 A B P p _109768 _109770) = (term944 A B P p _109768 _109770).
Proof. exact (eq_refl (term944 A B P p _109768 _109770)). Qed.
Lemma lem8247549 {A B P : Type'} (z : type518 A B P) (_109769 : A -> B) (p : type560 A B P) (_109768 : A -> B) (_109770 : P) : (term1233 A B P z _109769 p _109768 _109770) = (term1241 A B P z _109769 p _109768 _109770).
Proof. exact (MK_COMB (@lem8247547 A B P z _109768 p _109769 _109770) (@lem8247548 A B P p _109768 _109770)). Qed.
Lemma lem8247550 {A B P : Type'} (z : type518 A B P) (_109769 : A -> B) (p : type560 A B P) (_109768 : A -> B) (_109770 : P) : (term1230 A B P z _109768 p _109769 _109770) = (term1241 A B P z _109769 p _109768 _109770).
Proof. exact (TRANS (@lem8247532 A B P z _109769 p _109768 _109770) (@lem8247549 A B P z _109769 p _109768 _109770)). Qed.
Lemma lem8247552 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term972 A B P p lt2 f s t g a') (h4 : term978 A B P p lt2 f s t g a') : term1238 A B P z f p g a'.
Proof. exact (conj (@lem8247469 A B P z p lt2 f s t g a' h1 h2 h3 h4) (@lem8247476 A B P p lt2 f s t g a' h4)). Qed.
Lemma lem8247554 {A B P : Type'} (_109769 : A -> B) (_109768 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1241 A B P z _109769 p _109768 _109770.
Proof. exact (EQ_MP (@lem8247550 A B P z _109769 p _109768 _109770) (@lem8247529 A B P _109768 _109769 _109770 lt2 s z p h1)). Qed.
Lemma lem8247555 {A B P : Type'} (_109769 : A -> B) (_109768 : A -> B) (_109770 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1241 A B P z _109769 p _109768 _109770.
Proof. exact (@lem8247554 A B P _109769 _109768 _109770 lt2 s z p h1). Qed.
Lemma lem8247556 {A B P : Type'} (g : A -> B) (f : A -> B) (a' : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1241 A B P z g p f a'.
Proof. exact (@lem8247555 A B P g f a' lt2 s z p h1). Qed.
Lemma lem8247559 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p f a') (h3 : term972 A B P p lt2 f s t g a') (h4 : term978 A B P p lt2 f s t g a') : term944 A B P p f a'.
Proof. exact (@lem8247556 A B P g f a' lt2 s z p h1 (@lem8247552 A B P z p lt2 f s t g a' h1 h2 h3 h4)). Qed.
Lemma lem8247560 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term972 A B P p lt2 f s t g a') (h3 : term978 A B P p lt2 f s t g a') : term1121 A B P p f a'.
Proof. exact (fun h0 : term945 A B P p f a' => @lem8247559 A B P z p lt2 f s t g a' h1 h0 h2 h3). Qed.
Lemma lem8247562 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247563 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1121 A B P p f a') = (term944 A B P p f a').
Proof. exact (@lem8247562 (term944 A B P p f a')). Qed.
Lemma lem8247564 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term972 A B P p lt2 f s t g a') (h3 : term978 A B P p lt2 f s t g a') : term944 A B P p f a'.
Proof. exact (EQ_MP (@lem8247563 A B P p f a') (@lem8247560 A B P z p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8247569 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term945 A B P p f a') = (term1242 A B P p f a').
Proof. exact (@lem8247567 (term944 A B P p f a')). Qed.
Lemma lem8247572 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term972 A B P p lt2 f s t g a') : term1242 A B P p f a'.
Proof. exact (EQ_MP (@lem8247569 A B P p f a') (@lem8245949 A B P p lt2 f s t g a' h1)). Qed.
Lemma lem8247575 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term972 A B P p lt2 f s t g a') (h3 : term978 A B P p lt2 f s t g a') : False.
Proof. exact (@lem8247572 A B P p lt2 f s t g a' h2 (@lem8247564 A B P z p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247576 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term972 A B P p lt2 f s t g a') (h3 : term978 A B P p lt2 f s t g a') : term1150.
Proof. exact (fun h0 : ~ False => @lem8247575 A B P z p lt2 f s t g a' h1 h2 h3). Qed.
Lemma lem8247578 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247579 : term1150 = False.
Proof. exact (@lem8247578 False). Qed.
Lemma lem8247580 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term972 A B P p lt2 f s t g a') (h3 : term978 A B P p lt2 f s t g a') : False.
Proof. exact (EQ_MP (@lem8247579) (@lem8247576 A B P z p lt2 f s t g a' h1 h2 h3)). Qed.
Lemma lem8247732 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term944 A B P p f a'.
Proof. exact (proj1 (@lem8244864 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8247733 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1121 A B P p f a'.
Proof. exact (fun h0 : term945 A B P p f a' => @lem8247732 A B P p lt2 g t f s a' h1). Qed.
Lemma lem8247735 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247736 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1121 A B P p f a') = (term944 A B P p f a').
Proof. exact (@lem8247735 (term944 A B P p f a')). Qed.
Lemma lem8247737 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term944 A B P p f a'.
Proof. exact (EQ_MP (@lem8247736 A B P p f a') (@lem8247733 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8247740 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) (h1 : term945 A B P p g a') : term945 A B P p g a'.
Proof. exact (h1). Qed.
Lemma lem8247741 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) (h1 : term945 A B P p g a') : term1222 A B P p g a'.
Proof. exact (fun h0 : term944 A B P p g a' => @lem8247740 A B P p g a' h1). Qed.
Lemma lem8247743 (p : Prop) : (term1152 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8247744 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1222 A B P p g a') = (term945 A B P p g a').
Proof. exact (@lem8247743 (term944 A B P p g a')). Qed.
Lemma lem8247745 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) (h1 : term945 A B P p g a') : term945 A B P p g a'.
Proof. exact (EQ_MP (@lem8247744 A B P p g a') (@lem8247741 A B P p g a' h1)). Qed.
Lemma lem8247747 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247748 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (s : P -> A) (_109780 : P) : (term1119 A B P lt2 z s _109778 p _109779 _109780) = (term1243 A B P p lt2 z _109778 _109779 s _109780).
Proof. exact (@lem8247747 (term988 A B P _109778 p _109779 _109780) (term1014 A B P lt2 z _109778 _109779 s _109780)). Qed.
Lemma lem8247750 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247751 {A B P : Type'} (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1244 A B P _109778 p _109779 _109780) = (term1245 A B P _109778 p _109779 _109780).
Proof. exact (@lem8247750 (term945 A B P p _109778 _109780) (term944 A B P p _109779 _109780)). Qed.
Lemma lem8247753 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247754 {A B P : Type'} (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1141 A B P p _109778 _109780) = (term944 A B P p _109778 _109780).
Proof. exact (@lem8247753 (term944 A B P p _109778 _109780)). Qed.
Lemma lem8247755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8247756 {A B P : Type'} (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1142 A B P p _109778 _109780) = (term965 A B P p _109778 _109780).
Proof. exact (MK_COMB (@lem8247755) (@lem8247754 A B P p _109778 _109780)). Qed.
Lemma lem8247757 {A B P : Type'} (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term945 A B P p _109779 _109780) = (term945 A B P p _109779 _109780).
Proof. exact (eq_refl (term945 A B P p _109779 _109780)). Qed.
Lemma lem8247758 {A B P : Type'} (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1245 A B P _109778 p _109779 _109780) = (term1246 A B P _109778 p _109779 _109780).
Proof. exact (MK_COMB (@lem8247756 A B P p _109778 _109780) (@lem8247757 A B P p _109779 _109780)). Qed.
Lemma lem8247759 {A B P : Type'} (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1244 A B P _109778 p _109779 _109780) = (term1246 A B P _109778 p _109779 _109780).
Proof. exact (TRANS (@lem8247751 A B P _109778 p _109779 _109780) (@lem8247758 A B P _109778 p _109779 _109780)). Qed.
Lemma lem8247760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247761 {A B P : Type'} (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1247 A B P _109778 p _109779 _109780) = (term1248 A B P _109778 p _109779 _109780).
Proof. exact (MK_COMB (@lem8247760) (@lem8247759 A B P _109778 p _109779 _109780)). Qed.
Lemma lem8247762 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (s : P -> A) (_109780 : P) : (term1014 A B P lt2 z _109778 _109779 s _109780) = (term1014 A B P lt2 z _109778 _109779 s _109780).
Proof. exact (eq_refl (term1014 A B P lt2 z _109778 _109779 s _109780)). Qed.
Lemma lem8247763 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (s : P -> A) (_109780 : P) : (term1243 A B P p lt2 z _109778 _109779 s _109780) = (term1249 A B P p lt2 z _109778 _109779 s _109780).
Proof. exact (MK_COMB (@lem8247761 A B P _109778 p _109779 _109780) (@lem8247762 A B P lt2 z _109778 _109779 s _109780)). Qed.
Lemma lem8247764 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (s : P -> A) (_109780 : P) : (term1119 A B P lt2 z s _109778 p _109779 _109780) = (term1249 A B P p lt2 z _109778 _109779 s _109780).
Proof. exact (TRANS (@lem8247748 A B P p lt2 z _109778 _109779 s _109780) (@lem8247763 A B P p lt2 z _109778 _109779 s _109780)). Qed.
Lemma lem8247766 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term945 A B P p g a') (h2 : term968 A B P p lt2 g t f s a') : term1246 A B P f p g a'.
Proof. exact (conj (@lem8247737 A B P p lt2 g t f s a' h2) (@lem8247745 A B P p g a' h1)). Qed.
Lemma lem8247768 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1249 A B P p lt2 z _109778 _109779 s _109780.
Proof. exact (EQ_MP (@lem8247764 A B P p lt2 z _109778 _109779 s _109780) (@lem8246101 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8247769 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1249 A B P p lt2 z _109778 _109779 s _109780.
Proof. exact (@lem8247768 A B P _109778 _109779 _109780 lt2 s z p h1). Qed.
Lemma lem8247770 {A B P : Type'} (f : A -> B) (g : A -> B) (a' : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1249 A B P p lt2 z f g s a'.
Proof. exact (@lem8247769 A B P f g a' lt2 s z p h1). Qed.
Lemma lem8247773 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term1014 A B P lt2 z f g s a'.
Proof. exact (@lem8247770 A B P f g a' lt2 s z p h1 (@lem8247766 A B P p lt2 g t f s a' h2 h3)). Qed.
Lemma lem8247774 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term1184 A B P lt2 z f g s a'.
Proof. exact (fun h0 : term1185 A B P lt2 z f g s a' => @lem8247773 A B P z p lt2 g t f s a' h1 h2 h3). Qed.
Lemma lem8247776 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247777 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a' : P) : (term1184 A B P lt2 z f g s a') = (term1014 A B P lt2 z f g s a').
Proof. exact (@lem8247776 (term1014 A B P lt2 z f g s a')). Qed.
Lemma lem8247778 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term1014 A B P lt2 z f g s a'.
Proof. exact (EQ_MP (@lem8247777 A B P lt2 z f g s a') (@lem8247774 A B P z p lt2 g t f s a' h1 h2 h3)). Qed.
Lemma lem8247784 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8247785 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109784) = (term1186 A B P f g lt2 _109784 s a').
Proof. exact (@lem8247784 ((@I (A -> B) f _109784) = (@I (A -> B) g _109784)) (term957 A P lt2 _109784 s a')). Qed.
Lemma lem8247793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8247794 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term1187 A B P lt2 s a' f g _109784) = (term1188 A B P f g lt2 _109784 s a').
Proof. exact (MK_COMB (@lem8247793) (@lem8247785 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247802 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term1186 A B P f g lt2 _109784 s a') = (term1186 A B P f g lt2 _109784 s a').
Proof. exact (eq_refl (term1186 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247803 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109784) = (term1186 A B P f g lt2 _109784 s a')) = ((term1186 A B P f g lt2 _109784 s a') = (term1186 A B P f g lt2 _109784 s a')).
Proof. exact (MK_COMB (@lem8247794 A B P f g lt2 _109784 s a') (@lem8247802 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8247806 (x : Prop) : (x = x) = True.
Proof. exact (@lem8247805 Prop x). Qed.
Lemma lem8247807 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : ((term1186 A B P f g lt2 _109784 s a') = (term1186 A B P f g lt2 _109784 s a')) = True.
Proof. exact (@lem8247806 (term1186 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247808 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : ((term960 A B P lt2 s a' f g _109784) = (term1186 A B P f g lt2 _109784 s a')) = True.
Proof. exact (TRANS (@lem8247803 A B P f g lt2 _109784 s a') (@lem8247807 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247809 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : True = ((term960 A B P lt2 s a' f g _109784) = (term1186 A B P f g lt2 _109784 s a')).
Proof. exact (SYM (@lem8247808 A B P f g lt2 _109784 s a')). Qed.
Lemma lem8247810 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term960 A B P lt2 s a' f g _109784) = (term1186 A B P f g lt2 _109784 s a').
Proof. exact (EQ_MP (@lem8247809 A B P f g lt2 _109784 s a') (@lem0)). Qed.
Lemma lem8247811 {A B P : Type'} (_109784 : A) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1186 A B P f g lt2 _109784 s a'.
Proof. exact (EQ_MP (@lem8247810 A B P f g lt2 _109784 s a') (@lem8246053 A B P _109784 p lt2 g t f s a' h1)). Qed.
Lemma lem8247813 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247814 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109784 : A) : (term1186 A B P f g lt2 _109784 s a') = (term1189 A B P lt2 s a' f g _109784).
Proof. exact (@lem8247813 (term957 A P lt2 _109784 s a') ((@I (A -> B) f _109784) = (@I (A -> B) g _109784))). Qed.
Lemma lem8247816 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247817 {A P : Type'} (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term1190 A P lt2 _109784 s a') = (term932 A P lt2 _109784 s a').
Proof. exact (@lem8247816 (term932 A P lt2 _109784 s a')). Qed.
Lemma lem8247818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247819 {A P : Type'} (lt2 : type1402 A) (_109784 : A) (s : P -> A) (a' : P) : (term1191 A P lt2 _109784 s a') = (term1192 A P lt2 _109784 s a').
Proof. exact (MK_COMB (@lem8247818) (@lem8247817 A P lt2 _109784 s a')). Qed.
Lemma lem8247820 {A B : Type'} (f : A -> B) (g : A -> B) (_109784 : A) : ((@I (A -> B) f _109784) = (@I (A -> B) g _109784)) = ((@I (A -> B) f _109784) = (@I (A -> B) g _109784)).
Proof. exact (eq_refl ((@I (A -> B) f _109784) = (@I (A -> B) g _109784))). Qed.
Lemma lem8247821 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109784 : A) : (term1189 A B P lt2 s a' f g _109784) = (term1193 A B P lt2 s a' f g _109784).
Proof. exact (MK_COMB (@lem8247819 A P lt2 _109784 s a') (@lem8247820 A B f g _109784)). Qed.
Lemma lem8247822 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a' : P) (f : A -> B) (g : A -> B) (_109784 : A) : (term1186 A B P f g lt2 _109784 s a') = (term1193 A B P lt2 s a' f g _109784).
Proof. exact (TRANS (@lem8247814 A B P lt2 s a' f g _109784) (@lem8247821 A B P lt2 s a' f g _109784)). Qed.
Lemma lem8247825 {A B P : Type'} (_109784 : A) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1193 A B P lt2 s a' f g _109784.
Proof. exact (EQ_MP (@lem8247822 A B P lt2 s a' f g _109784) (@lem8247811 A B P _109784 p lt2 g t f s a' h1)). Qed.
Lemma lem8247826 {A B P : Type'} (_109784 : A) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1193 A B P lt2 s a' f g _109784.
Proof. exact (@lem8247825 A B P _109784 p lt2 g t f s a' h1). Qed.
Lemma lem8247827 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1194 A B P lt2 s z f g a'.
Proof. exact (@lem8247826 A B P (term997 A B P z f g a') p lt2 g t f s a' h1). Qed.
Lemma lem8247830 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : (term1000 A B P z f g a') = (term1003 A B P z f g a').
Proof. exact (@lem8247827 A B P z p lt2 g t f s a' h3 (@lem8247778 A B P z p lt2 g t f s a' h1 h2 h3)). Qed.
Lemma lem8247831 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term1195 A B P z f g a'.
Proof. exact (fun h0 : term1007 A B P z f g a' => @lem8247830 A B P z p lt2 g t f s a' h1 h2 h3). Qed.
Lemma lem8247833 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247834 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a' : P) : (term1195 A B P z f g a') = ((term1000 A B P z f g a') = (term1003 A B P z f g a')).
Proof. exact (@lem8247833 ((term1000 A B P z f g a') = (term1003 A B P z f g a'))). Qed.
Lemma lem8247835 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : (term1000 A B P z f g a') = (term1003 A B P z f g a').
Proof. exact (EQ_MP (@lem8247834 A B P z f g a') (@lem8247831 A B P z p lt2 g t f s a' h1 h2 h3)). Qed.
Lemma lem8247837 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term944 A B P p f a'.
Proof. exact (proj1 (@lem8244864 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8247838 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1121 A B P p f a'.
Proof. exact (fun h0 : term945 A B P p f a' => @lem8247837 A B P p lt2 g t f s a' h1). Qed.
Lemma lem8247840 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247841 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a' : P) : (term1121 A B P p f a') = (term944 A B P p f a').
Proof. exact (@lem8247840 (term944 A B P p f a')). Qed.
Lemma lem8247842 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term944 A B P p f a'.
Proof. exact (EQ_MP (@lem8247841 A B P p f a') (@lem8247838 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8247860 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8247861 {A B P : Type'} (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term988 A B P _109778 p _109779 _109780) = (term991 A B P _109779 p _109778 _109780).
Proof. exact (@lem8247860 (term944 A B P p _109779 _109780) (term945 A B P p _109778 _109780)). Qed.
Lemma lem8247867 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) : (term1197 A B P z _109778 _109779 _109780) = (term1197 A B P z _109778 _109779 _109780).
Proof. exact (eq_refl (term1197 A B P z _109778 _109779 _109780)). Qed.
Lemma lem8247868 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1120 A B P z _109778 p _109779 _109780) = (term1250 A B P z _109779 p _109778 _109780).
Proof. exact (MK_COMB (@lem8247867 A B P z _109778 _109779 _109780) (@lem8247861 A B P _109779 p _109778 _109780)). Qed.
Lemma lem8247872 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8247873 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1250 A B P z _109779 p _109778 _109780) = (term1251 A B P z _109779 p _109778 _109780).
Proof. exact (@lem8247872 (term944 A B P p _109779 _109780) (term1007 A B P z _109778 _109779 _109780) (term945 A B P p _109778 _109780)). Qed.
Lemma lem8247891 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1120 A B P z _109778 p _109779 _109780) = (term1251 A B P z _109779 p _109778 _109780).
Proof. exact (TRANS (@lem8247868 A B P z _109779 p _109778 _109780) (@lem8247873 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8247893 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1252 A B P z _109778 p _109779 _109780) = (term1253 A B P z _109779 p _109778 _109780).
Proof. exact (MK_COMB (@lem8247892) (@lem8247891 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247911 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1251 A B P z _109779 p _109778 _109780) = (term1251 A B P z _109779 p _109778 _109780).
Proof. exact (eq_refl (term1251 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247912 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : ((term1120 A B P z _109778 p _109779 _109780) = (term1251 A B P z _109779 p _109778 _109780)) = ((term1251 A B P z _109779 p _109778 _109780) = (term1251 A B P z _109779 p _109778 _109780)).
Proof. exact (MK_COMB (@lem8247893 A B P z _109779 p _109778 _109780) (@lem8247911 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8247915 (x : Prop) : (x = x) = True.
Proof. exact (@lem8247914 Prop x). Qed.
Lemma lem8247916 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : ((term1251 A B P z _109779 p _109778 _109780) = (term1251 A B P z _109779 p _109778 _109780)) = True.
Proof. exact (@lem8247915 (term1251 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247917 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : ((term1120 A B P z _109778 p _109779 _109780) = (term1251 A B P z _109779 p _109778 _109780)) = True.
Proof. exact (TRANS (@lem8247912 A B P z _109779 p _109778 _109780) (@lem8247916 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247918 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : True = ((term1120 A B P z _109778 p _109779 _109780) = (term1251 A B P z _109779 p _109778 _109780)).
Proof. exact (SYM (@lem8247917 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247919 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1120 A B P z _109778 p _109779 _109780) = (term1251 A B P z _109779 p _109778 _109780).
Proof. exact (EQ_MP (@lem8247918 A B P z _109779 p _109778 _109780) (@lem0)). Qed.
Lemma lem8247920 {A B P : Type'} (_109779 : A -> B) (_109778 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1251 A B P z _109779 p _109778 _109780.
Proof. exact (EQ_MP (@lem8247919 A B P z _109779 p _109778 _109780) (@lem8246111 A B P _109778 _109779 _109780 lt2 s z p h1)). Qed.
Lemma lem8247922 (b : Prop) (a : Prop) : (a \/ b) = (term1135 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8247923 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1251 A B P z _109779 p _109778 _109780) = (term1254 A B P z _109778 p _109779 _109780).
Proof. exact (@lem8247922 (term1255 A B P z _109779 p _109778 _109780) (term944 A B P p _109779 _109780)). Qed.
Lemma lem8247925 (a : Prop) (b : Prop) : (term1137 a b) = (term1138 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8247926 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1256 A B P z _109779 p _109778 _109780) = (term1257 A B P z _109779 p _109778 _109780).
Proof. exact (@lem8247925 (term1007 A B P z _109778 _109779 _109780) (term945 A B P p _109778 _109780)). Qed.
Lemma lem8247928 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247929 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) : (term1214 A B P z _109778 _109779 _109780) = ((term1000 A B P z _109778 _109779 _109780) = (term1003 A B P z _109778 _109779 _109780)).
Proof. exact (@lem8247928 ((term1000 A B P z _109778 _109779 _109780) = (term1003 A B P z _109778 _109779 _109780))). Qed.
Lemma lem8247930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8247931 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) : (term1236 A B P z _109778 _109779 _109780) = (term1237 A B P z _109778 _109779 _109780).
Proof. exact (MK_COMB (@lem8247930) (@lem8247929 A B P z _109778 _109779 _109780)). Qed.
Lemma lem8247933 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8247934 {A B P : Type'} (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1141 A B P p _109778 _109780) = (term944 A B P p _109778 _109780).
Proof. exact (@lem8247933 (term944 A B P p _109778 _109780)). Qed.
Lemma lem8247935 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1257 A B P z _109779 p _109778 _109780) = (term1258 A B P z _109779 p _109778 _109780).
Proof. exact (MK_COMB (@lem8247931 A B P z _109778 _109779 _109780) (@lem8247934 A B P p _109778 _109780)). Qed.
Lemma lem8247936 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1256 A B P z _109779 p _109778 _109780) = (term1258 A B P z _109779 p _109778 _109780).
Proof. exact (TRANS (@lem8247926 A B P z _109779 p _109778 _109780) (@lem8247935 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8247938 {A B P : Type'} (z : type518 A B P) (_109779 : A -> B) (p : type560 A B P) (_109778 : A -> B) (_109780 : P) : (term1259 A B P z _109779 p _109778 _109780) = (term1260 A B P z _109779 p _109778 _109780).
Proof. exact (MK_COMB (@lem8247937) (@lem8247936 A B P z _109779 p _109778 _109780)). Qed.
Lemma lem8247939 {A B P : Type'} (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term944 A B P p _109779 _109780) = (term944 A B P p _109779 _109780).
Proof. exact (eq_refl (term944 A B P p _109779 _109780)). Qed.
Lemma lem8247940 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1254 A B P z _109778 p _109779 _109780) = (term1261 A B P z _109778 p _109779 _109780).
Proof. exact (MK_COMB (@lem8247938 A B P z _109779 p _109778 _109780) (@lem8247939 A B P p _109779 _109780)). Qed.
Lemma lem8247941 {A B P : Type'} (z : type518 A B P) (_109778 : A -> B) (p : type560 A B P) (_109779 : A -> B) (_109780 : P) : (term1251 A B P z _109779 p _109778 _109780) = (term1261 A B P z _109778 p _109779 _109780).
Proof. exact (TRANS (@lem8247923 A B P z _109778 p _109779 _109780) (@lem8247940 A B P z _109778 p _109779 _109780)). Qed.
Lemma lem8247943 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term1258 A B P z g p f a'.
Proof. exact (conj (@lem8247835 A B P z p lt2 g t f s a' h1 h2 h3) (@lem8247842 A B P p lt2 g t f s a' h3)). Qed.
Lemma lem8247945 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1261 A B P z _109778 p _109779 _109780.
Proof. exact (EQ_MP (@lem8247941 A B P z _109778 p _109779 _109780) (@lem8247920 A B P _109779 _109778 _109780 lt2 s z p h1)). Qed.
Lemma lem8247946 {A B P : Type'} (_109778 : A -> B) (_109779 : A -> B) (_109780 : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1261 A B P z _109778 p _109779 _109780.
Proof. exact (@lem8247945 A B P _109778 _109779 _109780 lt2 s z p h1). Qed.
Lemma lem8247947 {A B P : Type'} (f : A -> B) (g : A -> B) (a' : P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (p : type560 A B P) (h1 : term651 A B P lt2 s z p) : term1261 A B P z f p g a'.
Proof. exact (@lem8247946 A B P f g a' lt2 s z p h1). Qed.
Lemma lem8247950 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term945 A B P p g a') (h3 : term968 A B P p lt2 g t f s a') : term944 A B P p g a'.
Proof. exact (@lem8247947 A B P f g a' lt2 s z p h1 (@lem8247943 A B P z p lt2 g t f s a' h1 h2 h3)). Qed.
Lemma lem8247951 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term968 A B P p lt2 g t f s a') : term1121 A B P p g a'.
Proof. exact (fun h0 : term945 A B P p g a' => @lem8247950 A B P z p lt2 g t f s a' h1 h0 h2). Qed.
Lemma lem8247953 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247954 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term1121 A B P p g a') = (term944 A B P p g a').
Proof. exact (@lem8247953 (term944 A B P p g a')). Qed.
Lemma lem8247955 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term968 A B P p lt2 g t f s a') : term944 A B P p g a'.
Proof. exact (EQ_MP (@lem8247954 A B P p g a') (@lem8247951 A B P z p lt2 g t f s a' h1 h2)). Qed.
Lemma lem8247958 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8247960 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a' : P) : (term945 A B P p g a') = (term1242 A B P p g a').
Proof. exact (@lem8247958 (term944 A B P p g a')). Qed.
Lemma lem8247963 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term968 A B P p lt2 g t f s a') : term1242 A B P p g a'.
Proof. exact (EQ_MP (@lem8247960 A B P p g a') (@lem8246045 A B P p lt2 g t f s a' h1)). Qed.
Lemma lem8247966 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term968 A B P p lt2 g t f s a') : False.
Proof. exact (@lem8247963 A B P p lt2 g t f s a' h2 (@lem8247955 A B P z p lt2 g t f s a' h1 h2)). Qed.
Lemma lem8247967 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term968 A B P p lt2 g t f s a') : term1150.
Proof. exact (fun h0 : ~ False => @lem8247966 A B P z p lt2 g t f s a' h1 h2). Qed.
Lemma lem8247969 (p : Prop) : (term1122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8247970 : term1150 = False.
Proof. exact (@lem8247969 False). Qed.
Lemma lem8247971 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term968 A B P p lt2 g t f s a') : False.
Proof. exact (EQ_MP (@lem8247970) (@lem8247967 A B P z p lt2 g t f s a' h1 h2)). Qed.
Lemma lem8247972 {A B P : Type'} (z : type518 A B P) (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (f : A -> B) (s : P -> A) (t : type557 A B P) (g : A -> B) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term551 A B P p lt2 s z' t) (h3 : term978 A B P p lt2 f s t g a') : False.
Proof. exact (or_elim (@lem8244852 A B P p lt2 f s t g a' h3) (fun h0 : term975 A B P p lt2 s f t g a' => @lem8247216 A B P z' p lt2 f s t g a' h2 h0 h3) (fun h0 : term972 A B P p lt2 f s t g a' => @lem8247580 A B P z p lt2 f s t g a' h1 h0 h3)). Qed.
Lemma lem8247973 {A B P : Type'} (z : type518 A B P) (z' : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term651 A B P lt2 s z p) (h2 : term551 A B P p lt2 s z' t) (h3 : term980 A B P p lt2 g t f s a') : False.
Proof. exact (or_elim (@lem8244845 A B P p lt2 g t f s a' h3) (fun h0 : term978 A B P p lt2 f s t g a' => @lem8247972 A B P z z' p lt2 f s t g a' h1 h2 h0) (fun h0 : term968 A B P p lt2 g t f s a' => @lem8247971 A B P z p lt2 g t f s a' h1 h0)). Qed.
Lemma lem8247974 {A B P : Type'} (z : type518 A B P) (z' : type518 A B P) (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term34 A B P p t lt2 s) (h2 : term651 A B P lt2 s z p) (h3 : term551 A B P p lt2 s z' t) (h4 : term918 A B P y a p lt2 g t f s a') : False.
Proof. exact (or_elim (@lem8244409 A B P y a p lt2 g t f s a' h4) (fun h0 : term984 A B P p t f lt2 y s a => @lem8246440 A B P p t f lt2 y s a h1 h0) (fun h0 : term980 A B P p lt2 g t f s a' => @lem8247973 A B P z z' p lt2 g t f s a' h2 h3 h0)). Qed.
Lemma lem8247975 {A B P : Type'} (z : type518 A B P) (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) (h3 : term651 A B P lt2 s z p) (h4 : term918 A B P y a p lt2 g t f s a') : False.
Proof. exact (ex_elim (@lem8242070 A B P p lt2 s t h2) (fun z' : type518 A B P => fun h0 : term553 A B P p lt2 s t z' => @lem8247974 A B P z z' y a p lt2 g t f s a' h1 h3 h0 h4)). Qed.
Lemma lem8247976 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (a' : P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term918 A B P y a p lt2 g t f s a') : False.
Proof. exact (ex_elim (@lem8242477 A B P lt2 s p h2) (fun z : type518 A B P => fun h0 : term653 A B P lt2 s p z => @lem8247975 A B P z y a p lt2 g t f s a' h1 h3 h0 h4)). Qed.
Lemma lem8247977 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (g : A -> B) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term921 A B P y a p lt2 g t f s) : False.
Proof. exact (ex_elim (@lem8243855 A B P y a p lt2 g t f s h4) (fun a' : P => fun h0 : term920 A B P y a p lt2 g t f s a' => @lem8247976 A B P y a p lt2 g t f s a' h1 h2 h3 h0)). Qed.
Lemma lem8247978 {A B P : Type'} (y : A) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term923 A B P y a p lt2 t f s) : False.
Proof. exact (ex_elim (@lem8243854 A B P y a p lt2 t f s h4) (fun g : A -> B => fun h0 : term922 A B P y a p lt2 t f s g => @lem8247977 A B P y a p lt2 g t f s h1 h2 h3 h0)). Qed.
Lemma lem8247979 {A B P : Type'} (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term925 A B P a p lt2 t f s) : False.
Proof. exact (ex_elim (@lem8243853 A B P a p lt2 t f s h4) (fun y : A => fun h0 : term924 A B P a p lt2 t f s y => @lem8247978 A B P y a p lt2 t f s h1 h2 h3 h0)). Qed.
Lemma lem8247980 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term927 A B P p lt2 t f s) : False.
Proof. exact (ex_elim (@lem8243852 A B P p lt2 t f s h4) (fun a : P => fun h0 : term926 A B P p lt2 t f s a => @lem8247979 A B P a p lt2 t f s h1 h2 h3 h0)). Qed.
Lemma lem8247981 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term404 A B P p lt2 t s) : False.
Proof. exact (ex_elim (@lem8243851 A B P p lt2 t s h4) (fun f : A -> B => fun h0 : term928 A B P p lt2 t s f => @lem8247980 A B P p lt2 t f s h1 h2 h3 h0)). Qed.
Lemma lem8247982 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term404 A B P p lt2 t s) : (term404 A B P p lt2 t s) = False.
Proof. exact (prop_ext (fun h5 : term404 A B P p lt2 t s => @lem8247981 A B P p lt2 t s h1 h2 h3 h4) (fun h5 : False => @lem8241744 A B P p lt2 t s h4)). Qed.
Lemma lem8247983 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term404 A B P p lt2 t s) : False.
Proof. exact (EQ_MP (@lem8247982 A B P p lt2 t s h1 h2 h3 h4) (@lem8241744 A B P p lt2 t s h4)). Qed.
Lemma lem8247984 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term403 A B P p lt2 t s.
Proof. exact (fun h0 : term404 A B P p lt2 t s => @lem8247983 A B P p lt2 t s h1 h2 h3 h0). Qed.
Lemma lem8247985 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term391 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8241743 A B P p lt2 t s) (@lem8247984 A B P p lt2 s t h1 h2 h3)). Qed.
Lemma lem8247986 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : term392 A B P p lt2 t s.
Proof. exact (fun h0 : term80 A B P lt2 s p => @lem8247985 A B P p lt2 s t h1 h0 h2). Qed.
Lemma lem8247987 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term31 A B P p lt2 s t) : term393 A B P p lt2 t s.
Proof. exact (fun h0 : term34 A B P p t lt2 s => @lem8247986 A B P p lt2 s t h0 h1). Qed.
Lemma lem8247988 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : term394 A B P p lt2 t s.
Proof. exact (fun h0 : term31 A B P p lt2 s t => @lem8247987 A B P p lt2 s t h0). Qed.
Lemma lem8247993 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term396 A B P p t s.
Proof. exact (fun lt2 : type1402 A => @lem8247988 A B P p lt2 t s). Qed.
Lemma lem8247998 {A B P : Type'} (t : type557 A B P) (s : P -> A) : term398 A B P t s.
Proof. exact (fun p : type560 A B P => @lem8247993 A B P p t s). Qed.
Lemma lem8248003 {A B P : Type'} (s : P -> A) : term400 A B P s.
Proof. exact (fun t : type557 A B P => @lem8247998 A B P t s). Qed.
Lemma lem8248008 {A B P : Type'} : term402 A B P.
Proof. exact (fun s : P -> A => @lem8248003 A B P s). Qed.
Lemma lem8248009 {A B P : Type'} : term274 A B P.
Proof. exact (EQ_MP (@lem8241736 A B P) (@lem8248008 A B P)). Qed.
Lemma lem8248010 {A B P : Type'} (s : P -> A) : term1262 A B P s.
Proof. exact (@lem8248009 A B P s). Qed.
Lemma lem8248011 {A B P : Type'} (s : P -> A) : (term1262 A B P s) = (term270 A B P s).
Proof. exact (eq_refl (term1262 A B P s)). Qed.
Lemma lem8248012 {A B P : Type'} (s : P -> A) : term270 A B P s.
Proof. exact (EQ_MP (@lem8248011 A B P s) (@lem8248010 A B P s)). Qed.
Lemma lem8248013 {A B P : Type'} (s : P -> A) (t : type557 A B P) : term1263 A B P s t.
Proof. exact (@lem8248012 A B P s t). Qed.
Lemma lem8248014 {A B P : Type'} (t : type557 A B P) (s : P -> A) : (term1263 A B P s t) = (term266 A B P t s).
Proof. exact (eq_refl (term1263 A B P s t)). Qed.
Lemma lem8248015 {A B P : Type'} (t : type557 A B P) (s : P -> A) : term266 A B P t s.
Proof. exact (EQ_MP (@lem8248014 A B P t s) (@lem8248013 A B P s t)). Qed.
Lemma lem8248016 {A B P : Type'} (t : type557 A B P) (s : P -> A) (p : type560 A B P) : term1264 A B P t s p.
Proof. exact (@lem8248015 A B P t s p). Qed.
Lemma lem8248017 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term1264 A B P t s p) = (term262 A B P p t s).
Proof. exact (eq_refl (term1264 A B P t s p)). Qed.
Lemma lem8248018 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term262 A B P p t s.
Proof. exact (EQ_MP (@lem8248017 A B P p t s) (@lem8248016 A B P t s p)). Qed.
Lemma lem8248019 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (s : P -> A) (lt2 : type1402 A) : term1265 A B P p t s lt2.
Proof. exact (@lem8248018 A B P p t s lt2). Qed.
Lemma lem8248020 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : (term1265 A B P p t s lt2) = (term247 A B P lt2 p t s).
Proof. exact (eq_refl (term1265 A B P p t s lt2)). Qed.
Lemma lem8248021 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term247 A B P lt2 p t s.
Proof. exact (EQ_MP (@lem8248020 A B P lt2 p t s) (@lem8248019 A B P p t s lt2)). Qed.
Lemma lem8248023 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) : term247 A B P lt2 p t s.
Proof. exact (@lem8240583 A B P lt2 p t s (@lem8248021 A B P lt2 p t s)). Qed.
Lemma lem8248024 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term31 A B P p lt2 s t) : term256 A B P lt2 p t s.
Proof. exact (@lem8248023 A B P lt2 p t s (@lem8240047 A B P p lt2 s t h1)). Qed.
Lemma lem8248025 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : term253 A B P lt2 p t s.
Proof. exact (@lem8248024 A B P p lt2 s t h2 (@lem8240046 A B P p t lt2 s h1)). Qed.
Lemma lem8248026 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term245 A B P lt2 p t s.
Proof. exact (@lem8248025 A B P p lt2 s t h1 h3 (@lem8240048 A B P lt2 s p h2)). Qed.
Lemma lem8248027 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term246 A B P lt2 p t s) : False.
Proof. exact (@lem8248026 A B P p lt2 s t h1 h2 h3 (@lem8240567 A B P lt2 p t s h4)). Qed.
Lemma lem8248028 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term246 A B P lt2 p t s) : (term246 A B P lt2 p t s) = False.
Proof. exact (prop_ext (fun h5 : term246 A B P lt2 p t s => @lem8248027 A B P lt2 p t s h1 h2 h3 h4) (fun h5 : False => @lem8240567 A B P lt2 p t s h4)). Qed.
Lemma lem8248029 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) (t : type557 A B P) (s : P -> A) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) (h4 : term246 A B P lt2 p t s) : False.
Proof. exact (EQ_MP (@lem8248028 A B P lt2 p t s h1 h2 h3 h4) (@lem8240567 A B P lt2 p t s h4)). Qed.
Lemma lem8248030 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term245 A B P lt2 p t s.
Proof. exact (fun h0 : term246 A B P lt2 p t s => @lem8248029 A B P lt2 p t s h1 h2 h3 h0). Qed.
Lemma lem8248031 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term243 A B P lt2 p t s.
Proof. exact (EQ_MP (@lem8240566 A B P lt2 p t s) (@lem8248030 A B P p lt2 s t h1 h2 h3)). Qed.
Lemma lem8248032 {A B P : Type'} (anything : P -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term242 A B P lt2 p t s anything.
Proof. exact (EQ_MP (@lem8240562 A B P lt2 p t s anything) (@lem8248031 A B P p lt2 s t h1 h2 h3)). Qed.
Lemma lem8248033 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term1266 A B P lt2 p t s.
Proof. exact (ex_intro (term1267 A B P lt2 p t s) (term1268 A B P) (@lem8248032 A B P (@el (P -> B)) p lt2 s t h1 h2 h3)). Qed.
Lemma lem8248034 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term1269 A B P lt2 s p t.
Proof. exact (ex_intro (term1270 A B P lt2 s p t) (term153 A B P p t s) (@lem8248033 A B P p lt2 s t h1 h2 h3)). Qed.
Lemma lem8248035 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term130 A B P lt2 s p t.
Proof. exact (ex_intro (term129 A B P lt2 s p t) (term45 A B P) (@lem8248034 A B P p lt2 s t h1 h2 h3)). Qed.
Lemma lem8248036 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : (term80 A B P lt2 s p) = (term130 A B P lt2 s p t).
Proof. exact (prop_ext (fun h4 : term80 A B P lt2 s p => @lem8248035 A B P p lt2 s t h1 h2 h3) (fun h4 : term130 A B P lt2 s p t => @lem8240048 A B P lt2 s p h2)). Qed.
Lemma lem8248037 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term80 A B P lt2 s p) (h3 : term31 A B P p lt2 s t) : term130 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8248036 A B P p lt2 s t h1 h2 h3) (@lem8240048 A B P lt2 s p h2)). Qed.
Lemma lem8248038 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : term131 A B P lt2 s p t.
Proof. exact (fun h0 : term80 A B P lt2 s p => @lem8248037 A B P p lt2 s t h1 h0 h2). Qed.
Lemma lem8248039 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term36 A B P p t lt2 s) : term34 A B P p t lt2 s.
Proof. exact (proj2 (@lem8240045 A B P p t lt2 s h1)). Qed.
Lemma lem8248040 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term36 A B P p t lt2 s) : term31 A B P p lt2 s t.
Proof. exact (proj1 (@lem8240045 A B P p t lt2 s h1)). Qed.
Lemma lem8248041 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : (term34 A B P p t lt2 s) = (term131 A B P lt2 s p t).
Proof. exact (prop_ext (fun h3 : term34 A B P p t lt2 s => @lem8248038 A B P p lt2 s t h1 h2) (fun h3 : term131 A B P lt2 s p t => @lem8240046 A B P p t lt2 s h1)). Qed.
Lemma lem8248042 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : term131 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8248041 A B P p lt2 s t h1 h2) (@lem8240046 A B P p t lt2 s h1)). Qed.
Lemma lem8248043 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : (term31 A B P p lt2 s t) = (term131 A B P lt2 s p t).
Proof. exact (prop_ext (fun h3 : term31 A B P p lt2 s t => @lem8248042 A B P p lt2 s t h1 h2) (fun h3 : term131 A B P lt2 s p t => @lem8240047 A B P p lt2 s t h2)). Qed.
Lemma lem8248044 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (h1 : term34 A B P p t lt2 s) (h2 : term31 A B P p lt2 s t) : term131 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8248043 A B P p lt2 s t h1 h2) (@lem8240047 A B P p lt2 s t h2)). Qed.
Lemma lem8248045 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term31 A B P p lt2 s t) (h2 : term36 A B P p t lt2 s) : (term34 A B P p t lt2 s) = (term131 A B P lt2 s p t).
Proof. exact (prop_ext (fun h3 : term34 A B P p t lt2 s => @lem8248044 A B P p lt2 s t h3 h1) (fun h3 : term131 A B P lt2 s p t => @lem8248039 A B P p t lt2 s h2)). Qed.
Lemma lem8248046 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term31 A B P p lt2 s t) (h2 : term36 A B P p t lt2 s) : term131 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8248045 A B P p t lt2 s h1 h2) (@lem8248039 A B P p t lt2 s h2)). Qed.
Lemma lem8248047 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term36 A B P p t lt2 s) : (term31 A B P p lt2 s t) = (term131 A B P lt2 s p t).
Proof. exact (prop_ext (fun h2 : term31 A B P p lt2 s t => @lem8248046 A B P p t lt2 s h2 h1) (fun h2 : term131 A B P lt2 s p t => @lem8248040 A B P p t lt2 s h1)). Qed.
Lemma lem8248048 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (s : P -> A) (h1 : term36 A B P p t lt2 s) : term131 A B P lt2 s p t.
Proof. exact (EQ_MP (@lem8248047 A B P p t lt2 s h1) (@lem8248040 A B P p t lt2 s h1)). Qed.
Lemma lem8248049 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (t : type557 A B P) : term133 A B P lt2 s p t.
Proof. exact (fun h0 : term36 A B P p t lt2 s => @lem8248048 A B P p t lt2 s h0). Qed.
Lemma lem8248054 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) : term137 A B P lt2 s p.
Proof. exact (fun t : type557 A B P => @lem8248049 A B P lt2 s p t). Qed.
Lemma lem8248059 {A B P : Type'} (lt2 : type1402 A) (p : type560 A B P) : term141 A B P lt2 p.
Proof. exact (fun s : P -> A => @lem8248054 A B P lt2 s p). Qed.
Lemma lem8248064 {A B P : Type'} (lt2 : type1402 A) : term145 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8248059 A B P lt2 p). Qed.
Lemma lem8248069 {A B P : Type'} : term149 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8248064 A B P lt2). Qed.
Lemma lem8248070 {A B P : Type'} : term148 A B P.
Proof. exact (EQ_MP (@lem8240044 A B P) (@lem8248069 A B P)). Qed.
