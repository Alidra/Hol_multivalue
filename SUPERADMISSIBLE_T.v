Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPERADMISSIBLE_T_term_abbrevs.
Require Import admissible_spec.
Require Import superadmissible_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8440649 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term0 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8440650 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term0 _143449 _143452 _143456 _143457 _143462 p) = (term1 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term0 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8440651 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term1 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8440650 _143449 _143452 _143456 _143457 _143462 p) (@lem8440649 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8440652 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term2 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8440651 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8440653 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term2 _143449 _143452 _143456 _143457 _143462 p lt2) = (term3 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term2 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8440654 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term3 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8440653 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8440652 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8440655 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term4 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8440654 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8440656 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term4 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term5 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term4 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8440657 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term5 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8440656 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8440655 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8440658 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8440657 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8440659 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term7 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8440661 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term8 _143606 _143608 _143614 lt2.
Proof. exact (@lem8096071 _143606 _143608 _143614 lt2). Qed.
Lemma lem8440662 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : (term8 _143606 _143608 _143614 lt2) = (term9 _143606 _143608 _143614 lt2).
Proof. exact (eq_refl (term8 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8440663 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) : term9 _143606 _143608 _143614 lt2.
Proof. exact (EQ_MP (@lem8440662 _143606 _143608 _143614 lt2) (@lem8440661 _143606 _143608 _143614 lt2)). Qed.
Lemma lem8440664 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term10 _143606 _143608 _143614 lt2 p.
Proof. exact (@lem8440663 _143606 _143608 _143614 lt2 p). Qed.
Lemma lem8440665 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : (term10 _143606 _143608 _143614 lt2 p) = (term11 _143606 _143608 _143614 lt2 p).
Proof. exact (eq_refl (term10 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8440666 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) : term11 _143606 _143608 _143614 lt2 p.
Proof. exact (EQ_MP (@lem8440665 _143606 _143608 _143614 lt2 p) (@lem8440664 _143606 _143608 _143614 lt2 p)). Qed.
Lemma lem8440667 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term12 _143606 _143608 _143614 lt2 p s.
Proof. exact (@lem8440666 _143606 _143608 _143614 lt2 p s). Qed.
Lemma lem8440668 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : (term12 _143606 _143608 _143614 lt2 p s) = (term13 _143606 _143608 _143614 lt2 p s).
Proof. exact (eq_refl (term12 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8440669 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) : term13 _143606 _143608 _143614 lt2 p s.
Proof. exact (EQ_MP (@lem8440668 _143606 _143608 _143614 lt2 p s) (@lem8440667 _143606 _143608 _143614 lt2 p s)). Qed.
Lemma lem8440670 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : term14 _143606 _143608 _143614 lt2 p s t.
Proof. exact (@lem8440669 _143606 _143608 _143614 lt2 p s t). Qed.
Lemma lem8440671 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (term14 _143606 _143608 _143614 lt2 p s t) = ((@superadmissible _143606 _143608 _143614 lt2 p s t) = (term15 _143606 _143608 _143614 lt2 p s t)).
Proof. exact (eq_refl (term14 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8440676 {_143606 _143608 _143614 : Type'} (lt2 : type1402 _143606) (p : type560 _143606 _143608 _143614) (s : _143614 -> _143606) (t : type558 _143606 _143608 _143614) : (@superadmissible _143606 _143608 _143614 lt2 p s t) = (term15 _143606 _143608 _143614 lt2 p s t).
Proof. exact (EQ_MP (@lem8440671 _143606 _143608 _143614 lt2 p s t) (@lem8440670 _143606 _143608 _143614 lt2 p s t)). Qed.
Lemma lem8440677 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (p : type560 _147009 _147011 _147015) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (@superadmissible _147009 _147011 _147015 lt2 p s t) = (term15 _147009 _147011 _147015 lt2 p s t).
Proof. exact (@lem8440676 _147009 _147011 _147015 lt2 p s t). Qed.
Lemma lem8440678 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term16 _147009 _147011 _147015 lt2 s t) = (term17 _147009 _147011 _147015 lt2 s t).
Proof. exact (@lem8440677 _147009 _147011 _147015 lt2 (term18 _147009 _147011 _147015) s t). Qed.
Lemma lem8440682 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term7 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8440659 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8440658 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8440683 {_147009 _147011 _147015 : Type'} (p : type560 _147009 _147011 _147015) (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type560 _147009 _147011 _147015) : (@admissible _147009 _147011 _147009 Prop _147015 lt2 p s t) = (term19 _147009 _147011 _147015 p lt2 s t).
Proof. exact (@lem8440682 _147009 _147011 _147009 Prop _147015 p lt2 s t). Qed.
Lemma lem8440684 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term20 _147009 _147011 _147015 lt2 s) = (term21 _147009 _147011 _147015 lt2 s).
Proof. exact (@lem8440683 _147009 _147011 _147015 (term18 _147009 _147011 _147015) lt2 s (term18 _147009 _147011 _147015)). Qed.
Lemma lem8440702 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440703 {_147009 _147011 _147015 : Type'} (f : type560 _147009 _147011 _147015) (y : _147009 -> _147011) : (term23 _147009 _147011 _147015 f y) = (f y).
Proof. exact (@lem8440702 (_147009 -> _147011) (_147015 -> Prop) f y). Qed.
Lemma lem8440704 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f).
Proof. exact (@lem8440703 _147009 _147011 _147015 (term18 _147009 _147011 _147015) f). Qed.
Lemma lem8440705 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440706 {_147009 _147011 _147015 : Type'} : (term27 _147009 _147011 _147015) = (term18 _147009 _147011 _147015).
Proof. exact (fun_ext (fun f : _147009 -> _147011 => @lem8440705 _147009 _147011 _147015 f)). Qed.
Lemma lem8440707 {_147009 _147011 : Type'} (f : _147009 -> _147011) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8440708 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f).
Proof. exact (MK_COMB (@lem8440706 _147009 _147011 _147015) (@lem8440707 _147009 _147011 f)). Qed.
Lemma lem8440709 {_147015 : Type'} : (@eq (_147015 -> Prop)) = (@eq (_147015 -> Prop)).
Proof. exact (eq_refl (@eq (_147015 -> Prop))). Qed.
Lemma lem8440710 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term28 _147009 _147011 _147015 f) = (term29 _147009 _147011 _147015 f).
Proof. exact (MK_COMB (@lem8440709 _147015) (@lem8440708 _147009 _147011 _147015 f)). Qed.
Lemma lem8440711 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440712 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : ((term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f)) = ((term25 _147009 _147011 _147015 f) = (term26 _147015)).
Proof. exact (MK_COMB (@lem8440710 _147009 _147011 _147015 f) (@lem8440711 _147009 _147011 _147015 f)). Qed.
Lemma lem8440713 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (EQ_MP (@lem8440712 _147009 _147011 _147015 f) (@lem8440704 _147009 _147011 _147015 f)). Qed.
Lemma lem8440714 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440715 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 f a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440713 _147009 _147011 _147015 f) (@lem8440714 _147015 a)). Qed.
Lemma lem8440717 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440718 {_147015 : Type'} (f : _147015 -> Prop) (y : _147015) : (term32 _147015 f y) = (f y).
Proof. exact (@lem8440717 _147015 Prop f y). Qed.
Lemma lem8440719 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (@lem8440718 _147015 (term26 _147015) a). Qed.
Lemma lem8440720 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440721 {_147015 : Type'} : (term34 _147015) = (term26 _147015).
Proof. exact (fun_ext (fun a : _147015 => @lem8440720 _147015 a)). Qed.
Lemma lem8440722 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440723 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440721 _147015) (@lem8440722 _147015 a)). Qed.
Lemma lem8440724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440725 {_147015 : Type'} (a : _147015) : (term35 _147015 a) = (term36 _147015 a).
Proof. exact (MK_COMB (@lem8440724) (@lem8440723 _147015 a)). Qed.
Lemma lem8440726 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440727 {_147015 : Type'} (a : _147015) : ((term33 _147015 a) = (term31 _147015 a)) = ((term31 _147015 a) = True).
Proof. exact (MK_COMB (@lem8440725 _147015 a) (@lem8440726 _147015 a)). Qed.
Lemma lem8440728 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (EQ_MP (@lem8440727 _147015 a) (@lem8440719 _147015 a)). Qed.
Lemma lem8440729 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 f a) = True.
Proof. exact (TRANS (@lem8440715 _147009 _147011 _147015 f a) (@lem8440728 _147015 a)). Qed.
Lemma lem8440730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8440731 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term37 _147009 _147011 _147015 f a) = (and True).
Proof. exact (MK_COMB (@lem8440730) (@lem8440729 _147009 _147011 _147015 f a)). Qed.
Lemma lem8440735 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440736 {_147009 _147011 _147015 : Type'} (f : type560 _147009 _147011 _147015) (y : _147009 -> _147011) : (term23 _147009 _147011 _147015 f y) = (f y).
Proof. exact (@lem8440735 (_147009 -> _147011) (_147015 -> Prop) f y). Qed.
Lemma lem8440737 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g).
Proof. exact (@lem8440736 _147009 _147011 _147015 (term18 _147009 _147011 _147015) g). Qed.
Lemma lem8440738 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440739 {_147009 _147011 _147015 : Type'} : (term27 _147009 _147011 _147015) = (term18 _147009 _147011 _147015).
Proof. exact (fun_ext (fun f : _147009 -> _147011 => @lem8440738 _147009 _147011 _147015 f)). Qed.
Lemma lem8440740 {_147009 _147011 : Type'} (g : _147009 -> _147011) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8440741 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g).
Proof. exact (MK_COMB (@lem8440739 _147009 _147011 _147015) (@lem8440740 _147009 _147011 g)). Qed.
Lemma lem8440742 {_147015 : Type'} : (@eq (_147015 -> Prop)) = (@eq (_147015 -> Prop)).
Proof. exact (eq_refl (@eq (_147015 -> Prop))). Qed.
Lemma lem8440743 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term28 _147009 _147011 _147015 g) = (term29 _147009 _147011 _147015 g).
Proof. exact (MK_COMB (@lem8440742 _147015) (@lem8440741 _147009 _147011 _147015 g)). Qed.
Lemma lem8440744 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term25 _147009 _147011 _147015 g) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 g)). Qed.
Lemma lem8440745 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : ((term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g)) = ((term25 _147009 _147011 _147015 g) = (term26 _147015)).
Proof. exact (MK_COMB (@lem8440743 _147009 _147011 _147015 g) (@lem8440744 _147009 _147011 _147015 g)). Qed.
Lemma lem8440746 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term25 _147009 _147011 _147015 g) = (term26 _147015).
Proof. exact (EQ_MP (@lem8440745 _147009 _147011 _147015 g) (@lem8440737 _147009 _147011 _147015 g)). Qed.
Lemma lem8440747 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440748 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 g a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440746 _147009 _147011 _147015 g) (@lem8440747 _147015 a)). Qed.
Lemma lem8440750 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440751 {_147015 : Type'} (f : _147015 -> Prop) (y : _147015) : (term32 _147015 f y) = (f y).
Proof. exact (@lem8440750 _147015 Prop f y). Qed.
Lemma lem8440752 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (@lem8440751 _147015 (term26 _147015) a). Qed.
Lemma lem8440753 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440754 {_147015 : Type'} : (term34 _147015) = (term26 _147015).
Proof. exact (fun_ext (fun a : _147015 => @lem8440753 _147015 a)). Qed.
Lemma lem8440755 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440756 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440754 _147015) (@lem8440755 _147015 a)). Qed.
Lemma lem8440757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440758 {_147015 : Type'} (a : _147015) : (term35 _147015 a) = (term36 _147015 a).
Proof. exact (MK_COMB (@lem8440757) (@lem8440756 _147015 a)). Qed.
Lemma lem8440759 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440760 {_147015 : Type'} (a : _147015) : ((term33 _147015 a) = (term31 _147015 a)) = ((term31 _147015 a) = True).
Proof. exact (MK_COMB (@lem8440758 _147015 a) (@lem8440759 _147015 a)). Qed.
Lemma lem8440761 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (EQ_MP (@lem8440760 _147015 a) (@lem8440752 _147015 a)). Qed.
Lemma lem8440762 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 g a) = True.
Proof. exact (TRANS (@lem8440748 _147009 _147011 _147015 g a) (@lem8440761 _147015 a)). Qed.
Lemma lem8440763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8440764 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) (a : _147015) : (term37 _147009 _147011 _147015 g a) = (and True).
Proof. exact (MK_COMB (@lem8440763) (@lem8440762 _147009 _147011 _147015 g a)). Qed.
Lemma lem8440773 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term38 _147009 _147011 _147015 lt2 s a f g) = (term38 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (eq_refl (term38 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440774 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term39 _147009 _147011 _147015 lt2 s a f g) = (term40 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (MK_COMB (@lem8440764 _147009 _147011 _147015 g a) (@lem8440773 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440776 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8440777 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term40 _147009 _147011 _147015 lt2 s a f g) = (term38 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (@lem8440776 (term38 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440786 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term39 _147009 _147011 _147015 lt2 s a f g) = (term38 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (TRANS (@lem8440774 _147009 _147011 _147015 lt2 s a f g) (@lem8440777 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440787 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term41 _147009 _147011 _147015 lt2 s a f g) = (term40 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (MK_COMB (@lem8440731 _147009 _147011 _147015 f a) (@lem8440786 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440789 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8440790 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term40 _147009 _147011 _147015 lt2 s a f g) = (term38 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (@lem8440789 (term38 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440799 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term41 _147009 _147011 _147015 lt2 s a f g) = (term38 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (TRANS (@lem8440787 _147009 _147011 _147015 lt2 s a f g) (@lem8440790 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8440801 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term42 _147009 _147011 _147015 lt2 s a f g) = (term43 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (MK_COMB (@lem8440800) (@lem8440799 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440805 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440806 {_147009 _147011 _147015 : Type'} (f : type560 _147009 _147011 _147015) (y : _147009 -> _147011) : (term23 _147009 _147011 _147015 f y) = (f y).
Proof. exact (@lem8440805 (_147009 -> _147011) (_147015 -> Prop) f y). Qed.
Lemma lem8440807 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f).
Proof. exact (@lem8440806 _147009 _147011 _147015 (term18 _147009 _147011 _147015) f). Qed.
Lemma lem8440808 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440809 {_147009 _147011 _147015 : Type'} : (term27 _147009 _147011 _147015) = (term18 _147009 _147011 _147015).
Proof. exact (fun_ext (fun f : _147009 -> _147011 => @lem8440808 _147009 _147011 _147015 f)). Qed.
Lemma lem8440810 {_147009 _147011 : Type'} (f : _147009 -> _147011) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8440811 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f).
Proof. exact (MK_COMB (@lem8440809 _147009 _147011 _147015) (@lem8440810 _147009 _147011 f)). Qed.
Lemma lem8440812 {_147015 : Type'} : (@eq (_147015 -> Prop)) = (@eq (_147015 -> Prop)).
Proof. exact (eq_refl (@eq (_147015 -> Prop))). Qed.
Lemma lem8440813 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term28 _147009 _147011 _147015 f) = (term29 _147009 _147011 _147015 f).
Proof. exact (MK_COMB (@lem8440812 _147015) (@lem8440811 _147009 _147011 _147015 f)). Qed.
Lemma lem8440814 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440815 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : ((term24 _147009 _147011 _147015 f) = (term25 _147009 _147011 _147015 f)) = ((term25 _147009 _147011 _147015 f) = (term26 _147015)).
Proof. exact (MK_COMB (@lem8440813 _147009 _147011 _147015 f) (@lem8440814 _147009 _147011 _147015 f)). Qed.
Lemma lem8440816 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (EQ_MP (@lem8440815 _147009 _147011 _147015 f) (@lem8440807 _147009 _147011 _147015 f)). Qed.
Lemma lem8440817 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440818 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 f a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440816 _147009 _147011 _147015 f) (@lem8440817 _147015 a)). Qed.
Lemma lem8440820 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440821 {_147015 : Type'} (f : _147015 -> Prop) (y : _147015) : (term32 _147015 f y) = (f y).
Proof. exact (@lem8440820 _147015 Prop f y). Qed.
Lemma lem8440822 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (@lem8440821 _147015 (term26 _147015) a). Qed.
Lemma lem8440823 {_147015 : Type'} (x : _147015) : (term31 _147015 x) = True.
Proof. exact (eq_refl (term31 _147015 x)). Qed.
Lemma lem8440824 {_147015 : Type'} : (term34 _147015) = (term26 _147015).
Proof. exact (fun_ext (fun x : _147015 => @lem8440823 _147015 x)). Qed.
Lemma lem8440825 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440826 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440824 _147015) (@lem8440825 _147015 a)). Qed.
Lemma lem8440827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440828 {_147015 : Type'} (a : _147015) : (term35 _147015 a) = (term36 _147015 a).
Proof. exact (MK_COMB (@lem8440827) (@lem8440826 _147015 a)). Qed.
Lemma lem8440829 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440830 {_147015 : Type'} (a : _147015) : ((term33 _147015 a) = (term31 _147015 a)) = ((term31 _147015 a) = True).
Proof. exact (MK_COMB (@lem8440828 _147015 a) (@lem8440829 _147015 a)). Qed.
Lemma lem8440831 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (EQ_MP (@lem8440830 _147015 a) (@lem8440822 _147015 a)). Qed.
Lemma lem8440832 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 f a) = True.
Proof. exact (TRANS (@lem8440818 _147009 _147011 _147015 f a) (@lem8440831 _147015 a)). Qed.
Lemma lem8440833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440834 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (a : _147015) : (term44 _147009 _147011 _147015 f a) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8440833) (@lem8440832 _147009 _147011 _147015 f a)). Qed.
Lemma lem8440836 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440837 {_147009 _147011 _147015 : Type'} (f : type560 _147009 _147011 _147015) (y : _147009 -> _147011) : (term23 _147009 _147011 _147015 f y) = (f y).
Proof. exact (@lem8440836 (_147009 -> _147011) (_147015 -> Prop) f y). Qed.
Lemma lem8440838 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g).
Proof. exact (@lem8440837 _147009 _147011 _147015 (term18 _147009 _147011 _147015) g). Qed.
Lemma lem8440839 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) : (term25 _147009 _147011 _147015 f) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 f)). Qed.
Lemma lem8440840 {_147009 _147011 _147015 : Type'} : (term27 _147009 _147011 _147015) = (term18 _147009 _147011 _147015).
Proof. exact (fun_ext (fun f : _147009 -> _147011 => @lem8440839 _147009 _147011 _147015 f)). Qed.
Lemma lem8440841 {_147009 _147011 : Type'} (g : _147009 -> _147011) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8440842 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g).
Proof. exact (MK_COMB (@lem8440840 _147009 _147011 _147015) (@lem8440841 _147009 _147011 g)). Qed.
Lemma lem8440843 {_147015 : Type'} : (@eq (_147015 -> Prop)) = (@eq (_147015 -> Prop)).
Proof. exact (eq_refl (@eq (_147015 -> Prop))). Qed.
Lemma lem8440844 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term28 _147009 _147011 _147015 g) = (term29 _147009 _147011 _147015 g).
Proof. exact (MK_COMB (@lem8440843 _147015) (@lem8440842 _147009 _147011 _147015 g)). Qed.
Lemma lem8440845 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term25 _147009 _147011 _147015 g) = (term26 _147015).
Proof. exact (eq_refl (term25 _147009 _147011 _147015 g)). Qed.
Lemma lem8440846 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : ((term24 _147009 _147011 _147015 g) = (term25 _147009 _147011 _147015 g)) = ((term25 _147009 _147011 _147015 g) = (term26 _147015)).
Proof. exact (MK_COMB (@lem8440844 _147009 _147011 _147015 g) (@lem8440845 _147009 _147011 _147015 g)). Qed.
Lemma lem8440847 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) : (term25 _147009 _147011 _147015 g) = (term26 _147015).
Proof. exact (EQ_MP (@lem8440846 _147009 _147011 _147015 g) (@lem8440838 _147009 _147011 _147015 g)). Qed.
Lemma lem8440848 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440849 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 g a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440847 _147009 _147011 _147015 g) (@lem8440848 _147015 a)). Qed.
Lemma lem8440851 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8440852 {_147015 : Type'} (f : _147015 -> Prop) (y : _147015) : (term32 _147015 f y) = (f y).
Proof. exact (@lem8440851 _147015 Prop f y). Qed.
Lemma lem8440853 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (@lem8440852 _147015 (term26 _147015) a). Qed.
Lemma lem8440854 {_147015 : Type'} (x : _147015) : (term31 _147015 x) = True.
Proof. exact (eq_refl (term31 _147015 x)). Qed.
Lemma lem8440855 {_147015 : Type'} : (term34 _147015) = (term26 _147015).
Proof. exact (fun_ext (fun x : _147015 => @lem8440854 _147015 x)). Qed.
Lemma lem8440856 {_147015 : Type'} (a : _147015) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8440857 {_147015 : Type'} (a : _147015) : (term33 _147015 a) = (term31 _147015 a).
Proof. exact (MK_COMB (@lem8440855 _147015) (@lem8440856 _147015 a)). Qed.
Lemma lem8440858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440859 {_147015 : Type'} (a : _147015) : (term35 _147015 a) = (term36 _147015 a).
Proof. exact (MK_COMB (@lem8440858) (@lem8440857 _147015 a)). Qed.
Lemma lem8440860 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (eq_refl (term31 _147015 a)). Qed.
Lemma lem8440861 {_147015 : Type'} (a : _147015) : ((term33 _147015 a) = (term31 _147015 a)) = ((term31 _147015 a) = True).
Proof. exact (MK_COMB (@lem8440859 _147015 a) (@lem8440860 _147015 a)). Qed.
Lemma lem8440862 {_147015 : Type'} (a : _147015) : (term31 _147015 a) = True.
Proof. exact (EQ_MP (@lem8440861 _147015 a) (@lem8440853 _147015 a)). Qed.
Lemma lem8440863 {_147009 _147011 _147015 : Type'} (g : _147009 -> _147011) (a : _147015) : (term30 _147009 _147011 _147015 g a) = True.
Proof. exact (TRANS (@lem8440849 _147009 _147011 _147015 g a) (@lem8440862 _147015 a)). Qed.
Lemma lem8440864 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (g : _147009 -> _147011) (a : _147015) : ((term30 _147009 _147011 _147015 f a) = (term30 _147009 _147011 _147015 g a)) = (True = True).
Proof. exact (MK_COMB (@lem8440834 _147009 _147011 _147015 f a) (@lem8440863 _147009 _147011 _147015 g a)). Qed.
Lemma lem8440866 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8440867 : (True = True) = True.
Proof. exact (@lem8440866 True). Qed.
Lemma lem8440868 {_147009 _147011 _147015 : Type'} (f : _147009 -> _147011) (g : _147009 -> _147011) (a : _147015) : ((term30 _147009 _147011 _147015 f a) = (term30 _147009 _147011 _147015 g a)) = True.
Proof. exact (TRANS (@lem8440864 _147009 _147011 _147015 f g a) (@lem8440867)). Qed.
Lemma lem8440869 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term45 _147009 _147011 _147015 lt2 s f g a) = (term46 _147009 _147011 _147015 lt2 s a f g).
Proof. exact (MK_COMB (@lem8440801 _147009 _147011 _147015 lt2 s a f g) (@lem8440868 _147009 _147011 _147015 f g a)). Qed.
Lemma lem8440871 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8440872 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (a : _147015) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term46 _147009 _147011 _147015 lt2 s a f g) = True.
Proof. exact (@lem8440871 (term38 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440873 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) (g : _147009 -> _147011) (a : _147015) : (term45 _147009 _147011 _147015 lt2 s f g a) = True.
Proof. exact (TRANS (@lem8440869 _147009 _147011 _147015 lt2 s a f g) (@lem8440872 _147009 _147011 _147015 lt2 s a f g)). Qed.
Lemma lem8440874 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term47 _147009 _147011 _147015 lt2 s f g) = (term26 _147015).
Proof. exact (fun_ext (fun a : _147015 => @lem8440873 _147009 _147011 _147015 lt2 s f g a)). Qed.
Lemma lem8440875 {_147015 : Type'} : (@all _147015) = (@all _147015).
Proof. exact (eq_refl (@all _147015)). Qed.
Lemma lem8440876 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term48 _147009 _147011 _147015 lt2 s f g) = (term49 _147015).
Proof. exact (MK_COMB (@lem8440875 _147015) (@lem8440874 _147009 _147011 _147015 lt2 s f g)). Qed.
Lemma lem8440878 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8440879 {_147015 : Type'} (t : Prop) : (term50 _147015 t) = t.
Proof. exact (@lem8440878 _147015 t). Qed.
Lemma lem8440880 {_147015 : Type'} : (term49 _147015) = True.
Proof. exact (@lem8440879 _147015 True). Qed.
Lemma lem8440881 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) (g : _147009 -> _147011) : (term48 _147009 _147011 _147015 lt2 s f g) = True.
Proof. exact (TRANS (@lem8440876 _147009 _147011 _147015 lt2 s f g) (@lem8440880 _147015)). Qed.
Lemma lem8440882 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) : (term51 _147009 _147011 _147015 lt2 s f) = (term52 _147009 _147011).
Proof. exact (fun_ext (fun g : _147009 -> _147011 => @lem8440881 _147009 _147011 _147015 lt2 s f g)). Qed.
Lemma lem8440883 {_147009 _147011 : Type'} : (@all (_147009 -> _147011)) = (@all (_147009 -> _147011)).
Proof. exact (eq_refl (@all (_147009 -> _147011))). Qed.
Lemma lem8440884 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) : (term53 _147009 _147011 _147015 lt2 s f) = (term54 _147009 _147011).
Proof. exact (MK_COMB (@lem8440883 _147009 _147011) (@lem8440882 _147009 _147011 _147015 lt2 s f)). Qed.
Lemma lem8440886 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8440887 {_147009 _147011 : Type'} (t : Prop) : (term55 _147009 _147011 t) = t.
Proof. exact (@lem8440886 (_147009 -> _147011) t). Qed.
Lemma lem8440888 {_147009 _147011 : Type'} : (term54 _147009 _147011) = True.
Proof. exact (@lem8440887 _147009 _147011 True). Qed.
Lemma lem8440889 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (f : _147009 -> _147011) : (term53 _147009 _147011 _147015 lt2 s f) = True.
Proof. exact (TRANS (@lem8440884 _147009 _147011 _147015 lt2 s f) (@lem8440888 _147009 _147011)). Qed.
Lemma lem8440890 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term56 _147009 _147011 _147015 lt2 s) = (term52 _147009 _147011).
Proof. exact (fun_ext (fun f : _147009 -> _147011 => @lem8440889 _147009 _147011 _147015 lt2 s f)). Qed.
Lemma lem8440891 {_147009 _147011 : Type'} : (@all (_147009 -> _147011)) = (@all (_147009 -> _147011)).
Proof. exact (eq_refl (@all (_147009 -> _147011))). Qed.
Lemma lem8440892 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term21 _147009 _147011 _147015 lt2 s) = (term54 _147009 _147011).
Proof. exact (MK_COMB (@lem8440891 _147009 _147011) (@lem8440890 _147009 _147011 _147015 lt2 s)). Qed.
Lemma lem8440894 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8440895 {_147009 _147011 : Type'} (t : Prop) : (term55 _147009 _147011 t) = t.
Proof. exact (@lem8440894 (_147009 -> _147011) t). Qed.
Lemma lem8440896 {_147009 _147011 : Type'} : (term54 _147009 _147011) = True.
Proof. exact (@lem8440895 _147009 _147011 True). Qed.
Lemma lem8440897 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term21 _147009 _147011 _147015 lt2 s) = True.
Proof. exact (TRANS (@lem8440892 _147009 _147011 _147015 lt2 s) (@lem8440896 _147009 _147011)). Qed.
Lemma lem8440898 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term20 _147009 _147011 _147015 lt2 s) = True.
Proof. exact (TRANS (@lem8440684 _147009 _147011 _147015 lt2 s) (@lem8440897 _147009 _147011 _147015 lt2 s)). Qed.
Lemma lem8440899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8440900 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) : (term57 _147009 _147011 _147015 lt2 s) = (imp True).
Proof. exact (MK_COMB (@lem8440899) (@lem8440898 _147009 _147011 _147015 lt2 s)). Qed.
Lemma lem8440901 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term58 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (eq_refl (term58 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440902 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term17 _147009 _147011 _147015 lt2 s t) = (term59 _147009 _147011 _147015 lt2 s t).
Proof. exact (MK_COMB (@lem8440900 _147009 _147011 _147015 lt2 s) (@lem8440901 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440904 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8440905 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term59 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (@lem8440904 (term58 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440906 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term17 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (TRANS (@lem8440902 _147009 _147011 _147015 lt2 s t) (@lem8440905 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440907 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term16 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (TRANS (@lem8440678 _147009 _147011 _147015 lt2 s t) (@lem8440906 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8440909 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term60 _147009 _147011 _147015 lt2 s t) = (term61 _147009 _147011 _147015 lt2 s t).
Proof. exact (MK_COMB (@lem8440908) (@lem8440907 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440910 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term58 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (eq_refl (term58 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440911 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : ((term16 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t)) = ((term58 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t)).
Proof. exact (MK_COMB (@lem8440909 _147009 _147011 _147015 lt2 s t) (@lem8440910 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8440914 (x : Prop) : (x = x) = True.
Proof. exact (@lem8440913 Prop x). Qed.
Lemma lem8440915 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : ((term58 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t)) = True.
Proof. exact (@lem8440914 (term58 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440916 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : ((term16 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t)) = True.
Proof. exact (TRANS (@lem8440911 _147009 _147011 _147015 lt2 s t) (@lem8440915 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440917 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : True = ((term16 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t)).
Proof. exact (SYM (@lem8440916 _147009 _147011 _147015 lt2 s t)). Qed.
Lemma lem8440918 {_147009 _147011 _147015 : Type'} (lt2 : type1402 _147009) (s : _147015 -> _147009) (t : type558 _147009 _147011 _147015) : (term16 _147009 _147011 _147015 lt2 s t) = (term58 _147009 _147011 _147015 lt2 s t).
Proof. exact (EQ_MP (@lem8440917 _147009 _147011 _147015 lt2 s t) (@lem0)). Qed.
