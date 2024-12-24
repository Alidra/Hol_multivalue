Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IPRODUCT_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_INT_MUL_spec.
Require Import NEUTRAL_INT_MUL_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm6904563_spec.
Require Import thm6904577_spec.
Require Import thm7_spec.
Lemma lem6908638 : (@monoidal int int_mul) = ((@monoidal int int_mul) = True).
Proof. exact (@lem7 (@monoidal int int_mul)). Qed.
Lemma lem6908640 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6908641 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6908640 _120477 _120519 _120521 h1 op). Qed.
Lemma lem6908642 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6908643 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6908642 _120477 _120519 _120521 op) (@lem6908641 _120477 _120519 _120521 op h1)). Qed.
Lemma lem6908644 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6908645 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6908643 _120477 _120519 _120521 op h1 (@lem6908644 _120519 op h2)). Qed.
Lemma lem6908646 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6908645 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem6908647 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6908648 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6908646 _120477 _120519 _120521 op h2 (@lem6908647 _120477 _120519 _120521 h1)). Qed.
Lemma lem6908649 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6908648 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem6908650 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem6908649 _120477 _120519 _120521 op h1). Qed.
Lemma lem6908651 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6908650 _120477 _120519 _120521 h0). Qed.
Lemma lem6908652 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem6908651 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem6908653 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6908652 _120477 _120519 _120521 op). Qed.
Lemma lem6908654 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6908656 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem6908657 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem6908659 (h1 : (@neutral int int_mul) = term9) : (@neutral int int_mul) = term9.
Proof. exact (h1). Qed.
Lemma lem6908660 (h1 : (@neutral int int_mul) = term9) : term9 = (@neutral int int_mul).
Proof. exact (SYM (@lem6908659 h1)). Qed.
Lemma lem6908661 (h1 : term9 = (@neutral int int_mul)) : term9 = (@neutral int int_mul).
Proof. exact (h1). Qed.
Lemma lem6908662 (h1 : term9 = (@neutral int int_mul)) : (@neutral int int_mul) = term9.
Proof. exact (SYM (@lem6908661 h1)). Qed.
Lemma lem6908663 : ((@neutral int int_mul) = term9) = (term9 = (@neutral int int_mul)).
Proof. exact (prop_ext (fun h1 : (@neutral int int_mul) = term9 => @lem6908660 h1) (fun h1 : term9 = (@neutral int int_mul) => @lem6908662 h1)). Qed.
Lemma lem6908674 {_126180 : Type'} : (@iproduct _126180) = (@iterate int _126180 int_mul).
Proof. exact (TRANS (@lem6904563 _126180) (@lem6904577 _126180)). Qed.
Lemma lem6908675 {_126209 : Type'} : (@iproduct _126209) = (@iterate int _126209 int_mul).
Proof. exact (@lem6908674 _126209). Qed.
Lemma lem6908676 {_126209 : Type'} : (@EMPTY _126209) = (@EMPTY _126209).
Proof. exact (eq_refl (@EMPTY _126209)). Qed.
Lemma lem6908677 {_126209 : Type'} : (@iproduct _126209 (@EMPTY _126209)) = (@iterate int _126209 int_mul (@EMPTY _126209)).
Proof. exact (MK_COMB (@lem6908675 _126209) (@lem6908676 _126209)). Qed.
Lemma lem6908678 {_126209 : Type'} (f : _126209 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908679 {_126209 : Type'} (f : _126209 -> int) : (@iproduct _126209 (@EMPTY _126209) f) = (@iterate int _126209 int_mul (@EMPTY _126209) f).
Proof. exact (MK_COMB (@lem6908677 _126209) (@lem6908678 _126209 f)). Qed.
Lemma lem6908680 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6908681 {_126209 : Type'} (f : _126209 -> int) : (term10 _126209 f) = (term11 _126209 f).
Proof. exact (MK_COMB (@lem6908680) (@lem6908679 _126209 f)). Qed.
Lemma lem6908683 : term9 = (@neutral int int_mul).
Proof. exact (EQ_MP (@lem6908663) (@lem6905936)). Qed.
Lemma lem6908684 {_126209 : Type'} (f : _126209 -> int) : ((@iproduct _126209 (@EMPTY _126209) f) = term9) = ((@iterate int _126209 int_mul (@EMPTY _126209) f) = (@neutral int int_mul)).
Proof. exact (MK_COMB (@lem6908681 _126209 f) (@lem6908683)). Qed.
Lemma lem6908687 {_126209 : Type'} : (term12 _126209) = (term13 _126209).
Proof. exact (fun_ext (fun f : _126209 -> int => @lem6908684 _126209 f)). Qed.
Lemma lem6908688 {_126209 : Type'} : (@all (_126209 -> int)) = (@all (_126209 -> int)).
Proof. exact (eq_refl (@all (_126209 -> int))). Qed.
Lemma lem6908689 {_126209 : Type'} : (term14 _126209) = (term15 _126209).
Proof. exact (MK_COMB (@lem6908688 _126209) (@lem6908687 _126209)). Qed.
Lemma lem6908694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908695 {_126209 : Type'} : (term16 _126209) = (term17 _126209).
Proof. exact (MK_COMB (@lem6908694) (@lem6908689 _126209)). Qed.
Lemma lem6908713 {_126180 : Type'} : (@iproduct _126180) = (@iterate int _126180 int_mul).
Proof. exact (TRANS (@lem6904563 _126180) (@lem6904577 _126180)). Qed.
Lemma lem6908714 {_126250 : Type'} : (@iproduct _126250) = (@iterate int _126250 int_mul).
Proof. exact (@lem6908713 _126250). Qed.
Lemma lem6908715 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) : (@INSERT _126250 x s) = (@INSERT _126250 x s).
Proof. exact (eq_refl (@INSERT _126250 x s)). Qed.
Lemma lem6908716 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) : (term18 _126250 x s) = (term19 _126250 x s).
Proof. exact (MK_COMB (@lem6908714 _126250) (@lem6908715 _126250 x s)). Qed.
Lemma lem6908717 {_126250 : Type'} (f : _126250 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908718 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term20 _126250 x s f) = (term21 _126250 x s f).
Proof. exact (MK_COMB (@lem6908716 _126250 x s) (@lem6908717 _126250 f)). Qed.
Lemma lem6908719 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6908720 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term22 _126250 x s f) = (term23 _126250 x s f).
Proof. exact (MK_COMB (@lem6908719) (@lem6908718 _126250 x s f)). Qed.
Lemma lem6908722 {_126180 : Type'} : (@iproduct _126180) = (@iterate int _126180 int_mul).
Proof. exact (TRANS (@lem6904563 _126180) (@lem6904577 _126180)). Qed.
Lemma lem6908723 {_126250 : Type'} : (@iproduct _126250) = (@iterate int _126250 int_mul).
Proof. exact (@lem6908722 _126250). Qed.
Lemma lem6908724 {_126250 : Type'} (s : _126250 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6908725 {_126250 : Type'} (s : _126250 -> Prop) : (@iproduct _126250 s) = (@iterate int _126250 int_mul s).
Proof. exact (MK_COMB (@lem6908723 _126250) (@lem6908724 _126250 s)). Qed.
Lemma lem6908726 {_126250 : Type'} (f : _126250 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908727 {_126250 : Type'} (s : _126250 -> Prop) (f : _126250 -> int) : (@iproduct _126250 s f) = (@iterate int _126250 int_mul s f).
Proof. exact (MK_COMB (@lem6908725 _126250 s) (@lem6908726 _126250 f)). Qed.
Lemma lem6908728 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) : (term24 _126250 x s) = (term24 _126250 x s).
Proof. exact (eq_refl (term24 _126250 x s)). Qed.
Lemma lem6908729 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term25 _126250 x s f) = (term26 _126250 x s f).
Proof. exact (MK_COMB (@lem6908728 _126250 x s) (@lem6908727 _126250 s f)). Qed.
Lemma lem6908731 {_126180 : Type'} : (@iproduct _126180) = (@iterate int _126180 int_mul).
Proof. exact (TRANS (@lem6904563 _126180) (@lem6904577 _126180)). Qed.
Lemma lem6908732 {_126250 : Type'} : (@iproduct _126250) = (@iterate int _126250 int_mul).
Proof. exact (@lem6908731 _126250). Qed.
Lemma lem6908733 {_126250 : Type'} (s : _126250 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6908734 {_126250 : Type'} (s : _126250 -> Prop) : (@iproduct _126250 s) = (@iterate int _126250 int_mul s).
Proof. exact (MK_COMB (@lem6908732 _126250) (@lem6908733 _126250 s)). Qed.
Lemma lem6908735 {_126250 : Type'} (f : _126250 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908736 {_126250 : Type'} (s : _126250 -> Prop) (f : _126250 -> int) : (@iproduct _126250 s f) = (@iterate int _126250 int_mul s f).
Proof. exact (MK_COMB (@lem6908734 _126250 s) (@lem6908735 _126250 f)). Qed.
Lemma lem6908737 {_126250 : Type'} (f : _126250 -> int) (x : _126250) : (term27 _126250 f x) = (term27 _126250 f x).
Proof. exact (eq_refl (term27 _126250 f x)). Qed.
Lemma lem6908738 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term28 _126250 x s f) = (term29 _126250 x s f).
Proof. exact (MK_COMB (@lem6908737 _126250 f x) (@lem6908736 _126250 s f)). Qed.
Lemma lem6908739 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term30 _126250 x s f) = (term31 _126250 x s f).
Proof. exact (MK_COMB (@lem6908729 _126250 x s f) (@lem6908738 _126250 x s f)). Qed.
Lemma lem6908740 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : ((term20 _126250 x s f) = (term30 _126250 x s f)) = ((term21 _126250 x s f) = (term31 _126250 x s f)).
Proof. exact (MK_COMB (@lem6908720 _126250 x s f) (@lem6908739 _126250 x s f)). Qed.
Lemma lem6908743 {_126250 : Type'} (s : _126250 -> Prop) : (term32 _126250 s) = (term32 _126250 s).
Proof. exact (eq_refl (term32 _126250 s)). Qed.
Lemma lem6908744 {_126250 : Type'} (x : _126250) (s : _126250 -> Prop) (f : _126250 -> int) : (term33 _126250 x s f) = (term34 _126250 x s f).
Proof. exact (MK_COMB (@lem6908743 _126250 s) (@lem6908740 _126250 x s f)). Qed.
Lemma lem6908747 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term35 _126250 x f) = (term36 _126250 x f).
Proof. exact (fun_ext (fun s : _126250 -> Prop => @lem6908744 _126250 x s f)). Qed.
Lemma lem6908748 {_126250 : Type'} : (@all (_126250 -> Prop)) = (@all (_126250 -> Prop)).
Proof. exact (eq_refl (@all (_126250 -> Prop))). Qed.
Lemma lem6908749 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term37 _126250 x f) = (term38 _126250 x f).
Proof. exact (MK_COMB (@lem6908748 _126250) (@lem6908747 _126250 x f)). Qed.
Lemma lem6908754 {_126250 : Type'} (x : _126250) : (term39 _126250 x) = (term40 _126250 x).
Proof. exact (fun_ext (fun f : _126250 -> int => @lem6908749 _126250 x f)). Qed.
Lemma lem6908755 {_126250 : Type'} : (@all (_126250 -> int)) = (@all (_126250 -> int)).
Proof. exact (eq_refl (@all (_126250 -> int))). Qed.
Lemma lem6908756 {_126250 : Type'} (x : _126250) : (term41 _126250 x) = (term42 _126250 x).
Proof. exact (MK_COMB (@lem6908755 _126250) (@lem6908754 _126250 x)). Qed.
Lemma lem6908761 {_126250 : Type'} : (term43 _126250) = (term44 _126250).
Proof. exact (fun_ext (fun x : _126250 => @lem6908756 _126250 x)). Qed.
Lemma lem6908762 {_126250 : Type'} : (@all _126250) = (@all _126250).
Proof. exact (eq_refl (@all _126250)). Qed.
Lemma lem6908763 {_126250 : Type'} : (term45 _126250) = (term46 _126250).
Proof. exact (MK_COMB (@lem6908762 _126250) (@lem6908761 _126250)). Qed.
Lemma lem6908768 {_126209 _126250 : Type'} : (term47 _126209 _126250) = (term48 _126209 _126250).
Proof. exact (MK_COMB (@lem6908695 _126209) (@lem6908763 _126250)). Qed.
Lemma lem6908771 {_126209 _126250 : Type'} : (term48 _126209 _126250) = (term47 _126209 _126250).
Proof. exact (SYM (@lem6908768 _126209 _126250)). Qed.
Lemma lem6908781 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem6908657 A B P) (@lem6908656 A B P)). Qed.
Lemma lem6908782 {_126250 : Type'} (P : type1365 _126250) : (term49 _126250 P) = (term50 _126250 P).
Proof. exact (@lem6908781 _126250 (_126250 -> int) P). Qed.
Lemma lem6908783 {_126250 : Type'} : (term51 _126250) = (term52 _126250).
Proof. exact (@lem6908782 _126250 (term53 _126250)). Qed.
Lemma lem6908784 {_126250 : Type'} (x : _126250) : (term54 _126250 x) = (term40 _126250 x).
Proof. exact (eq_refl (term54 _126250 x)). Qed.
Lemma lem6908785 {_126250 : Type'} (f : _126250 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908786 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term55 _126250 x f) = (term56 _126250 x f).
Proof. exact (MK_COMB (@lem6908784 _126250 x) (@lem6908785 _126250 f)). Qed.
Lemma lem6908787 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term56 _126250 x f) = (term38 _126250 x f).
Proof. exact (eq_refl (term56 _126250 x f)). Qed.
Lemma lem6908788 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term55 _126250 x f) = (term38 _126250 x f).
Proof. exact (TRANS (@lem6908786 _126250 x f) (@lem6908787 _126250 x f)). Qed.
Lemma lem6908789 {_126250 : Type'} (x : _126250) : (term57 _126250 x) = (term40 _126250 x).
Proof. exact (fun_ext (fun f : _126250 -> int => @lem6908788 _126250 x f)). Qed.
Lemma lem6908790 {_126250 : Type'} : (@all (_126250 -> int)) = (@all (_126250 -> int)).
Proof. exact (eq_refl (@all (_126250 -> int))). Qed.
Lemma lem6908791 {_126250 : Type'} (x : _126250) : (term58 _126250 x) = (term42 _126250 x).
Proof. exact (MK_COMB (@lem6908790 _126250) (@lem6908789 _126250 x)). Qed.
Lemma lem6908792 {_126250 : Type'} : (term59 _126250) = (term44 _126250).
Proof. exact (fun_ext (fun x : _126250 => @lem6908791 _126250 x)). Qed.
Lemma lem6908793 {_126250 : Type'} : (@all _126250) = (@all _126250).
Proof. exact (eq_refl (@all _126250)). Qed.
Lemma lem6908794 {_126250 : Type'} : (term51 _126250) = (term46 _126250).
Proof. exact (MK_COMB (@lem6908793 _126250) (@lem6908792 _126250)). Qed.
Lemma lem6908795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6908796 {_126250 : Type'} : (term60 _126250) = (term61 _126250).
Proof. exact (MK_COMB (@lem6908795) (@lem6908794 _126250)). Qed.
Lemma lem6908797 {_126250 : Type'} (x : _126250) : (term54 _126250 x) = (term40 _126250 x).
Proof. exact (eq_refl (term54 _126250 x)). Qed.
Lemma lem6908798 {_126250 : Type'} (f : _126250 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6908799 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term55 _126250 x f) = (term56 _126250 x f).
Proof. exact (MK_COMB (@lem6908797 _126250 x) (@lem6908798 _126250 f)). Qed.
Lemma lem6908800 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term56 _126250 x f) = (term38 _126250 x f).
Proof. exact (eq_refl (term56 _126250 x f)). Qed.
Lemma lem6908801 {_126250 : Type'} (x : _126250) (f : _126250 -> int) : (term55 _126250 x f) = (term38 _126250 x f).
Proof. exact (TRANS (@lem6908799 _126250 x f) (@lem6908800 _126250 x f)). Qed.
Lemma lem6908802 {_126250 : Type'} (f : _126250 -> int) : (term62 _126250 f) = (term63 _126250 f).
Proof. exact (fun_ext (fun x : _126250 => @lem6908801 _126250 x f)). Qed.
Lemma lem6908803 {_126250 : Type'} : (@all _126250) = (@all _126250).
Proof. exact (eq_refl (@all _126250)). Qed.
Lemma lem6908804 {_126250 : Type'} (f : _126250 -> int) : (term64 _126250 f) = (term65 _126250 f).
Proof. exact (MK_COMB (@lem6908803 _126250) (@lem6908802 _126250 f)). Qed.
Lemma lem6908805 {_126250 : Type'} : (term66 _126250) = (term67 _126250).
Proof. exact (fun_ext (fun f : _126250 -> int => @lem6908804 _126250 f)). Qed.
Lemma lem6908806 {_126250 : Type'} : (@all (_126250 -> int)) = (@all (_126250 -> int)).
Proof. exact (eq_refl (@all (_126250 -> int))). Qed.
Lemma lem6908807 {_126250 : Type'} : (term52 _126250) = (term68 _126250).
Proof. exact (MK_COMB (@lem6908806 _126250) (@lem6908805 _126250)). Qed.
Lemma lem6908808 {_126250 : Type'} : ((term51 _126250) = (term52 _126250)) = ((term46 _126250) = (term68 _126250)).
Proof. exact (MK_COMB (@lem6908796 _126250) (@lem6908807 _126250)). Qed.
Lemma lem6908809 {_126250 : Type'} : (term46 _126250) = (term68 _126250).
Proof. exact (EQ_MP (@lem6908808 _126250) (@lem6908783 _126250)). Qed.
Lemma lem6908810 {_126209 : Type'} : (term17 _126209) = (term17 _126209).
Proof. exact (eq_refl (term17 _126209)). Qed.
Lemma lem6908811 {_126209 _126250 : Type'} : (term48 _126209 _126250) = (term69 _126209 _126250).
Proof. exact (MK_COMB (@lem6908810 _126209) (@lem6908809 _126250)). Qed.
Lemma lem6908812 {_126209 _126250 : Type'} : (term69 _126209 _126250) = (term48 _126209 _126250).
Proof. exact (SYM (@lem6908811 _126209 _126250)). Qed.
Lemma lem6908814 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6908654 _120477 _120519 _120521 op) (@lem6908653 _120477 _120519 _120521 op)). Qed.
Lemma lem6908815 {_126209 _126250 : Type'} (op : type1551) : term70 _126209 _126250 op.
Proof. exact (@lem6908814 _126209 int _126250 op). Qed.
Lemma lem6908816 {_126209 _126250 : Type'} : term71 _126209 _126250.
Proof. exact (@lem6908815 _126209 _126250 int_mul). Qed.
Lemma lem6908818 : (@monoidal int int_mul) = True.
Proof. exact (EQ_MP (@lem6908638) (@lem6908637)). Qed.
Lemma lem6908819 : True = (@monoidal int int_mul).
Proof. exact (SYM (@lem6908818)). Qed.
Lemma lem6908820 : @monoidal int int_mul.
Proof. exact (EQ_MP (@lem6908819) (@lem0)). Qed.
Lemma lem6908821 {_126209 _126250 : Type'} : term69 _126209 _126250.
Proof. exact (@lem6908816 _126209 _126250 (@lem6908820)). Qed.
Lemma lem6908822 {_126209 _126250 : Type'} : term48 _126209 _126250.
Proof. exact (EQ_MP (@lem6908812 _126209 _126250) (@lem6908821 _126209 _126250)). Qed.
Lemma lem6908823 {_126209 _126250 : Type'} : term47 _126209 _126250.
Proof. exact (EQ_MP (@lem6908771 _126209 _126250) (@lem6908822 _126209 _126250)). Qed.
