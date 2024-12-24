Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6924731 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6924733 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6924734 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6924733 _120477 _120519 _120521 h1 op). Qed.
Lemma lem6924735 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6924736 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6924735 _120477 _120519 _120521 op) (@lem6924734 _120477 _120519 _120521 op h1)). Qed.
Lemma lem6924737 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6924738 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6924736 _120477 _120519 _120521 op h1 (@lem6924737 _120519 op h2)). Qed.
Lemma lem6924739 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6924738 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem6924740 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6924741 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6924739 _120477 _120519 _120521 op h2 (@lem6924740 _120477 _120519 _120521 h1)). Qed.
Lemma lem6924742 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6924741 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem6924743 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem6924742 _120477 _120519 _120521 op h1). Qed.
Lemma lem6924744 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6924743 _120477 _120519 _120521 h0). Qed.
Lemma lem6924745 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem6924744 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem6924746 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6924745 _120477 _120519 _120521 op). Qed.
Lemma lem6924747 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6924749 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem6924750 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem6924752 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6924753 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6924752 h1)). Qed.
Lemma lem6924754 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6924755 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6924754 h1)). Qed.
Lemma lem6924756 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6924753 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6924755 h1)). Qed.
Lemma lem6924767 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924768 {_126486 : Type'} : (@nsum _126486) = (@iterate nat _126486 Nat.add).
Proof. exact (@lem6924767 _126486). Qed.
Lemma lem6924769 {_126486 : Type'} : (@EMPTY _126486) = (@EMPTY _126486).
Proof. exact (eq_refl (@EMPTY _126486)). Qed.
Lemma lem6924770 {_126486 : Type'} : (@nsum _126486 (@EMPTY _126486)) = (@iterate nat _126486 Nat.add (@EMPTY _126486)).
Proof. exact (MK_COMB (@lem6924768 _126486) (@lem6924769 _126486)). Qed.
Lemma lem6924771 {_126486 : Type'} (f : _126486 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924772 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (@iterate nat _126486 Nat.add (@EMPTY _126486) f).
Proof. exact (MK_COMB (@lem6924770 _126486) (@lem6924771 _126486 f)). Qed.
Lemma lem6924773 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6924774 {_126486 : Type'} (f : _126486 -> nat) : (term9 _126486 f) = (term10 _126486 f).
Proof. exact (MK_COMB (@lem6924773) (@lem6924772 _126486 f)). Qed.
Lemma lem6924776 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6924756) (@lem6921993)). Qed.
Lemma lem6924777 {_126486 : Type'} (f : _126486 -> nat) : ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)) = ((@iterate nat _126486 Nat.add (@EMPTY _126486) f) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem6924774 _126486 f) (@lem6924776)). Qed.
Lemma lem6924780 {_126486 : Type'} : (term11 _126486) = (term12 _126486).
Proof. exact (fun_ext (fun f : _126486 -> nat => @lem6924777 _126486 f)). Qed.
Lemma lem6924781 {_126486 : Type'} : (@all (_126486 -> nat)) = (@all (_126486 -> nat)).
Proof. exact (eq_refl (@all (_126486 -> nat))). Qed.
Lemma lem6924782 {_126486 : Type'} : (term13 _126486) = (term14 _126486).
Proof. exact (MK_COMB (@lem6924781 _126486) (@lem6924780 _126486)). Qed.
Lemma lem6924787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6924788 {_126486 : Type'} : (term15 _126486) = (term16 _126486).
Proof. exact (MK_COMB (@lem6924787) (@lem6924782 _126486)). Qed.
Lemma lem6924806 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924807 {_126525 : Type'} : (@nsum _126525) = (@iterate nat _126525 Nat.add).
Proof. exact (@lem6924806 _126525). Qed.
Lemma lem6924808 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) : (@INSERT _126525 x s) = (@INSERT _126525 x s).
Proof. exact (eq_refl (@INSERT _126525 x s)). Qed.
Lemma lem6924809 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) : (term17 _126525 x s) = (term18 _126525 x s).
Proof. exact (MK_COMB (@lem6924807 _126525) (@lem6924808 _126525 x s)). Qed.
Lemma lem6924810 {_126525 : Type'} (f : _126525 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924811 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term19 _126525 x s f) = (term20 _126525 x s f).
Proof. exact (MK_COMB (@lem6924809 _126525 x s) (@lem6924810 _126525 f)). Qed.
Lemma lem6924812 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6924813 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term21 _126525 x s f) = (term22 _126525 x s f).
Proof. exact (MK_COMB (@lem6924812) (@lem6924811 _126525 x s f)). Qed.
Lemma lem6924815 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924816 {_126525 : Type'} : (@nsum _126525) = (@iterate nat _126525 Nat.add).
Proof. exact (@lem6924815 _126525). Qed.
Lemma lem6924817 {_126525 : Type'} (s : _126525 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6924818 {_126525 : Type'} (s : _126525 -> Prop) : (@nsum _126525 s) = (@iterate nat _126525 Nat.add s).
Proof. exact (MK_COMB (@lem6924816 _126525) (@lem6924817 _126525 s)). Qed.
Lemma lem6924819 {_126525 : Type'} (f : _126525 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924820 {_126525 : Type'} (s : _126525 -> Prop) (f : _126525 -> nat) : (@nsum _126525 s f) = (@iterate nat _126525 Nat.add s f).
Proof. exact (MK_COMB (@lem6924818 _126525 s) (@lem6924819 _126525 f)). Qed.
Lemma lem6924821 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) : (term23 _126525 x s) = (term23 _126525 x s).
Proof. exact (eq_refl (term23 _126525 x s)). Qed.
Lemma lem6924822 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term24 _126525 x s f) = (term25 _126525 x s f).
Proof. exact (MK_COMB (@lem6924821 _126525 x s) (@lem6924820 _126525 s f)). Qed.
Lemma lem6924824 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6924825 {_126525 : Type'} : (@nsum _126525) = (@iterate nat _126525 Nat.add).
Proof. exact (@lem6924824 _126525). Qed.
Lemma lem6924826 {_126525 : Type'} (s : _126525 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6924827 {_126525 : Type'} (s : _126525 -> Prop) : (@nsum _126525 s) = (@iterate nat _126525 Nat.add s).
Proof. exact (MK_COMB (@lem6924825 _126525) (@lem6924826 _126525 s)). Qed.
Lemma lem6924828 {_126525 : Type'} (f : _126525 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924829 {_126525 : Type'} (s : _126525 -> Prop) (f : _126525 -> nat) : (@nsum _126525 s f) = (@iterate nat _126525 Nat.add s f).
Proof. exact (MK_COMB (@lem6924827 _126525 s) (@lem6924828 _126525 f)). Qed.
Lemma lem6924830 {_126525 : Type'} (f : _126525 -> nat) (x : _126525) : (term26 _126525 f x) = (term26 _126525 f x).
Proof. exact (eq_refl (term26 _126525 f x)). Qed.
Lemma lem6924831 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term27 _126525 x s f) = (term28 _126525 x s f).
Proof. exact (MK_COMB (@lem6924830 _126525 f x) (@lem6924829 _126525 s f)). Qed.
Lemma lem6924832 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term29 _126525 x s f) = (term30 _126525 x s f).
Proof. exact (MK_COMB (@lem6924822 _126525 x s f) (@lem6924831 _126525 x s f)). Qed.
Lemma lem6924833 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : ((term19 _126525 x s f) = (term29 _126525 x s f)) = ((term20 _126525 x s f) = (term30 _126525 x s f)).
Proof. exact (MK_COMB (@lem6924813 _126525 x s f) (@lem6924832 _126525 x s f)). Qed.
Lemma lem6924836 {_126525 : Type'} (s : _126525 -> Prop) : (term31 _126525 s) = (term31 _126525 s).
Proof. exact (eq_refl (term31 _126525 s)). Qed.
Lemma lem6924837 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term32 _126525 x s f) = (term33 _126525 x s f).
Proof. exact (MK_COMB (@lem6924836 _126525 s) (@lem6924833 _126525 x s f)). Qed.
Lemma lem6924840 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term34 _126525 x f) = (term35 _126525 x f).
Proof. exact (fun_ext (fun s : _126525 -> Prop => @lem6924837 _126525 x s f)). Qed.
Lemma lem6924841 {_126525 : Type'} : (@all (_126525 -> Prop)) = (@all (_126525 -> Prop)).
Proof. exact (eq_refl (@all (_126525 -> Prop))). Qed.
Lemma lem6924842 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term36 _126525 x f) = (term37 _126525 x f).
Proof. exact (MK_COMB (@lem6924841 _126525) (@lem6924840 _126525 x f)). Qed.
Lemma lem6924847 {_126525 : Type'} (x : _126525) : (term38 _126525 x) = (term39 _126525 x).
Proof. exact (fun_ext (fun f : _126525 -> nat => @lem6924842 _126525 x f)). Qed.
Lemma lem6924848 {_126525 : Type'} : (@all (_126525 -> nat)) = (@all (_126525 -> nat)).
Proof. exact (eq_refl (@all (_126525 -> nat))). Qed.
Lemma lem6924849 {_126525 : Type'} (x : _126525) : (term40 _126525 x) = (term41 _126525 x).
Proof. exact (MK_COMB (@lem6924848 _126525) (@lem6924847 _126525 x)). Qed.
Lemma lem6924854 {_126525 : Type'} : (term42 _126525) = (term43 _126525).
Proof. exact (fun_ext (fun x : _126525 => @lem6924849 _126525 x)). Qed.
Lemma lem6924855 {_126525 : Type'} : (@all _126525) = (@all _126525).
Proof. exact (eq_refl (@all _126525)). Qed.
Lemma lem6924856 {_126525 : Type'} : (term44 _126525) = (term45 _126525).
Proof. exact (MK_COMB (@lem6924855 _126525) (@lem6924854 _126525)). Qed.
Lemma lem6924861 {_126486 _126525 : Type'} : (term46 _126486 _126525) = (term47 _126486 _126525).
Proof. exact (MK_COMB (@lem6924788 _126486) (@lem6924856 _126525)). Qed.
Lemma lem6924864 {_126486 _126525 : Type'} : (term47 _126486 _126525) = (term46 _126486 _126525).
Proof. exact (SYM (@lem6924861 _126486 _126525)). Qed.
Lemma lem6924874 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem6924750 A B P) (@lem6924749 A B P)). Qed.
Lemma lem6924875 {_126525 : Type'} (P : type1366 _126525) : (term48 _126525 P) = (term49 _126525 P).
Proof. exact (@lem6924874 _126525 (_126525 -> nat) P). Qed.
Lemma lem6924876 {_126525 : Type'} : (term50 _126525) = (term51 _126525).
Proof. exact (@lem6924875 _126525 (term52 _126525)). Qed.
Lemma lem6924877 {_126525 : Type'} (x : _126525) : (term53 _126525 x) = (term39 _126525 x).
Proof. exact (eq_refl (term53 _126525 x)). Qed.
Lemma lem6924878 {_126525 : Type'} (f : _126525 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924879 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term54 _126525 x f) = (term55 _126525 x f).
Proof. exact (MK_COMB (@lem6924877 _126525 x) (@lem6924878 _126525 f)). Qed.
Lemma lem6924880 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term55 _126525 x f) = (term37 _126525 x f).
Proof. exact (eq_refl (term55 _126525 x f)). Qed.
Lemma lem6924881 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term54 _126525 x f) = (term37 _126525 x f).
Proof. exact (TRANS (@lem6924879 _126525 x f) (@lem6924880 _126525 x f)). Qed.
Lemma lem6924882 {_126525 : Type'} (x : _126525) : (term56 _126525 x) = (term39 _126525 x).
Proof. exact (fun_ext (fun f : _126525 -> nat => @lem6924881 _126525 x f)). Qed.
Lemma lem6924883 {_126525 : Type'} : (@all (_126525 -> nat)) = (@all (_126525 -> nat)).
Proof. exact (eq_refl (@all (_126525 -> nat))). Qed.
Lemma lem6924884 {_126525 : Type'} (x : _126525) : (term57 _126525 x) = (term41 _126525 x).
Proof. exact (MK_COMB (@lem6924883 _126525) (@lem6924882 _126525 x)). Qed.
Lemma lem6924885 {_126525 : Type'} : (term58 _126525) = (term43 _126525).
Proof. exact (fun_ext (fun x : _126525 => @lem6924884 _126525 x)). Qed.
Lemma lem6924886 {_126525 : Type'} : (@all _126525) = (@all _126525).
Proof. exact (eq_refl (@all _126525)). Qed.
Lemma lem6924887 {_126525 : Type'} : (term50 _126525) = (term45 _126525).
Proof. exact (MK_COMB (@lem6924886 _126525) (@lem6924885 _126525)). Qed.
Lemma lem6924888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6924889 {_126525 : Type'} : (term59 _126525) = (term60 _126525).
Proof. exact (MK_COMB (@lem6924888) (@lem6924887 _126525)). Qed.
Lemma lem6924890 {_126525 : Type'} (x : _126525) : (term53 _126525 x) = (term39 _126525 x).
Proof. exact (eq_refl (term53 _126525 x)). Qed.
Lemma lem6924891 {_126525 : Type'} (f : _126525 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6924892 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term54 _126525 x f) = (term55 _126525 x f).
Proof. exact (MK_COMB (@lem6924890 _126525 x) (@lem6924891 _126525 f)). Qed.
Lemma lem6924893 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term55 _126525 x f) = (term37 _126525 x f).
Proof. exact (eq_refl (term55 _126525 x f)). Qed.
Lemma lem6924894 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term54 _126525 x f) = (term37 _126525 x f).
Proof. exact (TRANS (@lem6924892 _126525 x f) (@lem6924893 _126525 x f)). Qed.
Lemma lem6924895 {_126525 : Type'} (f : _126525 -> nat) : (term61 _126525 f) = (term62 _126525 f).
Proof. exact (fun_ext (fun x : _126525 => @lem6924894 _126525 x f)). Qed.
Lemma lem6924896 {_126525 : Type'} : (@all _126525) = (@all _126525).
Proof. exact (eq_refl (@all _126525)). Qed.
Lemma lem6924897 {_126525 : Type'} (f : _126525 -> nat) : (term63 _126525 f) = (term64 _126525 f).
Proof. exact (MK_COMB (@lem6924896 _126525) (@lem6924895 _126525 f)). Qed.
Lemma lem6924898 {_126525 : Type'} : (term65 _126525) = (term66 _126525).
Proof. exact (fun_ext (fun f : _126525 -> nat => @lem6924897 _126525 f)). Qed.
Lemma lem6924899 {_126525 : Type'} : (@all (_126525 -> nat)) = (@all (_126525 -> nat)).
Proof. exact (eq_refl (@all (_126525 -> nat))). Qed.
Lemma lem6924900 {_126525 : Type'} : (term51 _126525) = (term67 _126525).
Proof. exact (MK_COMB (@lem6924899 _126525) (@lem6924898 _126525)). Qed.
Lemma lem6924901 {_126525 : Type'} : ((term50 _126525) = (term51 _126525)) = ((term45 _126525) = (term67 _126525)).
Proof. exact (MK_COMB (@lem6924889 _126525) (@lem6924900 _126525)). Qed.
Lemma lem6924902 {_126525 : Type'} : (term45 _126525) = (term67 _126525).
Proof. exact (EQ_MP (@lem6924901 _126525) (@lem6924876 _126525)). Qed.
Lemma lem6924903 {_126486 : Type'} : (term16 _126486) = (term16 _126486).
Proof. exact (eq_refl (term16 _126486)). Qed.
Lemma lem6924904 {_126486 _126525 : Type'} : (term47 _126486 _126525) = (term68 _126486 _126525).
Proof. exact (MK_COMB (@lem6924903 _126486) (@lem6924902 _126525)). Qed.
Lemma lem6924905 {_126486 _126525 : Type'} : (term68 _126486 _126525) = (term47 _126486 _126525).
Proof. exact (SYM (@lem6924904 _126486 _126525)). Qed.
Lemma lem6924907 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6924747 _120477 _120519 _120521 op) (@lem6924746 _120477 _120519 _120521 op)). Qed.
Lemma lem6924908 {_126486 _126525 : Type'} (op : type1606) : term69 _126486 _126525 op.
Proof. exact (@lem6924907 _126486 nat _126525 op). Qed.
Lemma lem6924909 {_126486 _126525 : Type'} : term70 _126486 _126525.
Proof. exact (@lem6924908 _126486 _126525 Nat.add). Qed.
Lemma lem6924911 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6924731) (@lem6924403)). Qed.
Lemma lem6924912 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6924911)). Qed.
Lemma lem6924913 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6924912) (@lem0)). Qed.
Lemma lem6924914 {_126486 _126525 : Type'} : term68 _126486 _126525.
Proof. exact (@lem6924909 _126486 _126525 (@lem6924913)). Qed.
Lemma lem6924915 {_126486 _126525 : Type'} : term47 _126486 _126525.
Proof. exact (EQ_MP (@lem6924905 _126486 _126525) (@lem6924914 _126486 _126525)). Qed.
Lemma lem6924916 {_126486 _126525 : Type'} : term46 _126486 _126525.
Proof. exact (EQ_MP (@lem6924864 _126486 _126525) (@lem6924915 _126486 _126525)). Qed.
