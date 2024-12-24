Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PRODUCT_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_REAL_MUL_spec.
Require Import NEUTRAL_REAL_MUL_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm6910045_spec.
Require Import thm6910059_spec.
Require Import thm7_spec.
Lemma lem6912756 : (@monoidal real real_mul) = ((@monoidal real real_mul) = True).
Proof. exact (@lem7 (@monoidal real real_mul)). Qed.
Lemma lem6912758 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6912759 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6912758 _120477 _120519 _120521 h1 op). Qed.
Lemma lem6912760 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6912761 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6912760 _120477 _120519 _120521 op) (@lem6912759 _120477 _120519 _120521 op h1)). Qed.
Lemma lem6912762 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6912763 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6912761 _120477 _120519 _120521 op h1 (@lem6912762 _120519 op h2)). Qed.
Lemma lem6912764 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6912763 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem6912765 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6912766 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6912764 _120477 _120519 _120521 op h2 (@lem6912765 _120477 _120519 _120521 h1)). Qed.
Lemma lem6912767 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6912766 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem6912768 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem6912767 _120477 _120519 _120521 op h1). Qed.
Lemma lem6912769 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6912768 _120477 _120519 _120521 h0). Qed.
Lemma lem6912770 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem6912769 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem6912771 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6912770 _120477 _120519 _120521 op). Qed.
Lemma lem6912772 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6912774 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem6912775 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem6912777 (h1 : (@neutral real real_mul) = term9) : (@neutral real real_mul) = term9.
Proof. exact (h1). Qed.
Lemma lem6912778 (h1 : (@neutral real real_mul) = term9) : term9 = (@neutral real real_mul).
Proof. exact (SYM (@lem6912777 h1)). Qed.
Lemma lem6912779 (h1 : term9 = (@neutral real real_mul)) : term9 = (@neutral real real_mul).
Proof. exact (h1). Qed.
Lemma lem6912780 (h1 : term9 = (@neutral real real_mul)) : (@neutral real real_mul) = term9.
Proof. exact (SYM (@lem6912779 h1)). Qed.
Lemma lem6912781 : ((@neutral real real_mul) = term9) = (term9 = (@neutral real real_mul)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_mul) = term9 => @lem6912778 h1) (fun h1 : term9 = (@neutral real real_mul) => @lem6912780 h1)). Qed.
Lemma lem6912792 {_126259 : Type'} : (@product _126259) = (@iterate real _126259 real_mul).
Proof. exact (TRANS (@lem6910045 _126259) (@lem6910059 _126259)). Qed.
Lemma lem6912793 {_126288 : Type'} : (@product _126288) = (@iterate real _126288 real_mul).
Proof. exact (@lem6912792 _126288). Qed.
Lemma lem6912794 {_126288 : Type'} : (@EMPTY _126288) = (@EMPTY _126288).
Proof. exact (eq_refl (@EMPTY _126288)). Qed.
Lemma lem6912795 {_126288 : Type'} : (@product _126288 (@EMPTY _126288)) = (@iterate real _126288 real_mul (@EMPTY _126288)).
Proof. exact (MK_COMB (@lem6912793 _126288) (@lem6912794 _126288)). Qed.
Lemma lem6912796 {_126288 : Type'} (f : _126288 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912797 {_126288 : Type'} (f : _126288 -> real) : (@product _126288 (@EMPTY _126288) f) = (@iterate real _126288 real_mul (@EMPTY _126288) f).
Proof. exact (MK_COMB (@lem6912795 _126288) (@lem6912796 _126288 f)). Qed.
Lemma lem6912798 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6912799 {_126288 : Type'} (f : _126288 -> real) : (term10 _126288 f) = (term11 _126288 f).
Proof. exact (MK_COMB (@lem6912798) (@lem6912797 _126288 f)). Qed.
Lemma lem6912801 : term9 = (@neutral real real_mul).
Proof. exact (EQ_MP (@lem6912781) (@lem6911418)). Qed.
Lemma lem6912802 {_126288 : Type'} (f : _126288 -> real) : ((@product _126288 (@EMPTY _126288) f) = term9) = ((@iterate real _126288 real_mul (@EMPTY _126288) f) = (@neutral real real_mul)).
Proof. exact (MK_COMB (@lem6912799 _126288 f) (@lem6912801)). Qed.
Lemma lem6912805 {_126288 : Type'} : (term12 _126288) = (term13 _126288).
Proof. exact (fun_ext (fun f : _126288 -> real => @lem6912802 _126288 f)). Qed.
Lemma lem6912806 {_126288 : Type'} : (@all (_126288 -> real)) = (@all (_126288 -> real)).
Proof. exact (eq_refl (@all (_126288 -> real))). Qed.
Lemma lem6912807 {_126288 : Type'} : (term14 _126288) = (term15 _126288).
Proof. exact (MK_COMB (@lem6912806 _126288) (@lem6912805 _126288)). Qed.
Lemma lem6912812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6912813 {_126288 : Type'} : (term16 _126288) = (term17 _126288).
Proof. exact (MK_COMB (@lem6912812) (@lem6912807 _126288)). Qed.
Lemma lem6912831 {_126259 : Type'} : (@product _126259) = (@iterate real _126259 real_mul).
Proof. exact (TRANS (@lem6910045 _126259) (@lem6910059 _126259)). Qed.
Lemma lem6912832 {_126329 : Type'} : (@product _126329) = (@iterate real _126329 real_mul).
Proof. exact (@lem6912831 _126329). Qed.
Lemma lem6912833 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) : (@INSERT _126329 x s) = (@INSERT _126329 x s).
Proof. exact (eq_refl (@INSERT _126329 x s)). Qed.
Lemma lem6912834 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) : (term18 _126329 x s) = (term19 _126329 x s).
Proof. exact (MK_COMB (@lem6912832 _126329) (@lem6912833 _126329 x s)). Qed.
Lemma lem6912835 {_126329 : Type'} (f : _126329 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912836 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term20 _126329 x s f) = (term21 _126329 x s f).
Proof. exact (MK_COMB (@lem6912834 _126329 x s) (@lem6912835 _126329 f)). Qed.
Lemma lem6912837 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6912838 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term22 _126329 x s f) = (term23 _126329 x s f).
Proof. exact (MK_COMB (@lem6912837) (@lem6912836 _126329 x s f)). Qed.
Lemma lem6912840 {_126259 : Type'} : (@product _126259) = (@iterate real _126259 real_mul).
Proof. exact (TRANS (@lem6910045 _126259) (@lem6910059 _126259)). Qed.
Lemma lem6912841 {_126329 : Type'} : (@product _126329) = (@iterate real _126329 real_mul).
Proof. exact (@lem6912840 _126329). Qed.
Lemma lem6912842 {_126329 : Type'} (s : _126329 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6912843 {_126329 : Type'} (s : _126329 -> Prop) : (@product _126329 s) = (@iterate real _126329 real_mul s).
Proof. exact (MK_COMB (@lem6912841 _126329) (@lem6912842 _126329 s)). Qed.
Lemma lem6912844 {_126329 : Type'} (f : _126329 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912845 {_126329 : Type'} (s : _126329 -> Prop) (f : _126329 -> real) : (@product _126329 s f) = (@iterate real _126329 real_mul s f).
Proof. exact (MK_COMB (@lem6912843 _126329 s) (@lem6912844 _126329 f)). Qed.
Lemma lem6912846 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) : (term24 _126329 x s) = (term24 _126329 x s).
Proof. exact (eq_refl (term24 _126329 x s)). Qed.
Lemma lem6912847 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term25 _126329 x s f) = (term26 _126329 x s f).
Proof. exact (MK_COMB (@lem6912846 _126329 x s) (@lem6912845 _126329 s f)). Qed.
Lemma lem6912849 {_126259 : Type'} : (@product _126259) = (@iterate real _126259 real_mul).
Proof. exact (TRANS (@lem6910045 _126259) (@lem6910059 _126259)). Qed.
Lemma lem6912850 {_126329 : Type'} : (@product _126329) = (@iterate real _126329 real_mul).
Proof. exact (@lem6912849 _126329). Qed.
Lemma lem6912851 {_126329 : Type'} (s : _126329 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6912852 {_126329 : Type'} (s : _126329 -> Prop) : (@product _126329 s) = (@iterate real _126329 real_mul s).
Proof. exact (MK_COMB (@lem6912850 _126329) (@lem6912851 _126329 s)). Qed.
Lemma lem6912853 {_126329 : Type'} (f : _126329 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912854 {_126329 : Type'} (s : _126329 -> Prop) (f : _126329 -> real) : (@product _126329 s f) = (@iterate real _126329 real_mul s f).
Proof. exact (MK_COMB (@lem6912852 _126329 s) (@lem6912853 _126329 f)). Qed.
Lemma lem6912855 {_126329 : Type'} (f : _126329 -> real) (x : _126329) : (term27 _126329 f x) = (term27 _126329 f x).
Proof. exact (eq_refl (term27 _126329 f x)). Qed.
Lemma lem6912856 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term28 _126329 x s f) = (term29 _126329 x s f).
Proof. exact (MK_COMB (@lem6912855 _126329 f x) (@lem6912854 _126329 s f)). Qed.
Lemma lem6912857 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term30 _126329 x s f) = (term31 _126329 x s f).
Proof. exact (MK_COMB (@lem6912847 _126329 x s f) (@lem6912856 _126329 x s f)). Qed.
Lemma lem6912858 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : ((term20 _126329 x s f) = (term30 _126329 x s f)) = ((term21 _126329 x s f) = (term31 _126329 x s f)).
Proof. exact (MK_COMB (@lem6912838 _126329 x s f) (@lem6912857 _126329 x s f)). Qed.
Lemma lem6912861 {_126329 : Type'} (s : _126329 -> Prop) : (term32 _126329 s) = (term32 _126329 s).
Proof. exact (eq_refl (term32 _126329 s)). Qed.
Lemma lem6912862 {_126329 : Type'} (x : _126329) (s : _126329 -> Prop) (f : _126329 -> real) : (term33 _126329 x s f) = (term34 _126329 x s f).
Proof. exact (MK_COMB (@lem6912861 _126329 s) (@lem6912858 _126329 x s f)). Qed.
Lemma lem6912865 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term35 _126329 x f) = (term36 _126329 x f).
Proof. exact (fun_ext (fun s : _126329 -> Prop => @lem6912862 _126329 x s f)). Qed.
Lemma lem6912866 {_126329 : Type'} : (@all (_126329 -> Prop)) = (@all (_126329 -> Prop)).
Proof. exact (eq_refl (@all (_126329 -> Prop))). Qed.
Lemma lem6912867 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term37 _126329 x f) = (term38 _126329 x f).
Proof. exact (MK_COMB (@lem6912866 _126329) (@lem6912865 _126329 x f)). Qed.
Lemma lem6912872 {_126329 : Type'} (x : _126329) : (term39 _126329 x) = (term40 _126329 x).
Proof. exact (fun_ext (fun f : _126329 -> real => @lem6912867 _126329 x f)). Qed.
Lemma lem6912873 {_126329 : Type'} : (@all (_126329 -> real)) = (@all (_126329 -> real)).
Proof. exact (eq_refl (@all (_126329 -> real))). Qed.
Lemma lem6912874 {_126329 : Type'} (x : _126329) : (term41 _126329 x) = (term42 _126329 x).
Proof. exact (MK_COMB (@lem6912873 _126329) (@lem6912872 _126329 x)). Qed.
Lemma lem6912879 {_126329 : Type'} : (term43 _126329) = (term44 _126329).
Proof. exact (fun_ext (fun x : _126329 => @lem6912874 _126329 x)). Qed.
Lemma lem6912880 {_126329 : Type'} : (@all _126329) = (@all _126329).
Proof. exact (eq_refl (@all _126329)). Qed.
Lemma lem6912881 {_126329 : Type'} : (term45 _126329) = (term46 _126329).
Proof. exact (MK_COMB (@lem6912880 _126329) (@lem6912879 _126329)). Qed.
Lemma lem6912886 {_126288 _126329 : Type'} : (term47 _126288 _126329) = (term48 _126288 _126329).
Proof. exact (MK_COMB (@lem6912813 _126288) (@lem6912881 _126329)). Qed.
Lemma lem6912889 {_126288 _126329 : Type'} : (term48 _126288 _126329) = (term47 _126288 _126329).
Proof. exact (SYM (@lem6912886 _126288 _126329)). Qed.
Lemma lem6912899 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem6912775 A B P) (@lem6912774 A B P)). Qed.
Lemma lem6912900 {_126329 : Type'} (P : type1367 _126329) : (term49 _126329 P) = (term50 _126329 P).
Proof. exact (@lem6912899 _126329 (_126329 -> real) P). Qed.
Lemma lem6912901 {_126329 : Type'} : (term51 _126329) = (term52 _126329).
Proof. exact (@lem6912900 _126329 (term53 _126329)). Qed.
Lemma lem6912902 {_126329 : Type'} (x : _126329) : (term54 _126329 x) = (term40 _126329 x).
Proof. exact (eq_refl (term54 _126329 x)). Qed.
Lemma lem6912903 {_126329 : Type'} (f : _126329 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912904 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term55 _126329 x f) = (term56 _126329 x f).
Proof. exact (MK_COMB (@lem6912902 _126329 x) (@lem6912903 _126329 f)). Qed.
Lemma lem6912905 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term56 _126329 x f) = (term38 _126329 x f).
Proof. exact (eq_refl (term56 _126329 x f)). Qed.
Lemma lem6912906 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term55 _126329 x f) = (term38 _126329 x f).
Proof. exact (TRANS (@lem6912904 _126329 x f) (@lem6912905 _126329 x f)). Qed.
Lemma lem6912907 {_126329 : Type'} (x : _126329) : (term57 _126329 x) = (term40 _126329 x).
Proof. exact (fun_ext (fun f : _126329 -> real => @lem6912906 _126329 x f)). Qed.
Lemma lem6912908 {_126329 : Type'} : (@all (_126329 -> real)) = (@all (_126329 -> real)).
Proof. exact (eq_refl (@all (_126329 -> real))). Qed.
Lemma lem6912909 {_126329 : Type'} (x : _126329) : (term58 _126329 x) = (term42 _126329 x).
Proof. exact (MK_COMB (@lem6912908 _126329) (@lem6912907 _126329 x)). Qed.
Lemma lem6912910 {_126329 : Type'} : (term59 _126329) = (term44 _126329).
Proof. exact (fun_ext (fun x : _126329 => @lem6912909 _126329 x)). Qed.
Lemma lem6912911 {_126329 : Type'} : (@all _126329) = (@all _126329).
Proof. exact (eq_refl (@all _126329)). Qed.
Lemma lem6912912 {_126329 : Type'} : (term51 _126329) = (term46 _126329).
Proof. exact (MK_COMB (@lem6912911 _126329) (@lem6912910 _126329)). Qed.
Lemma lem6912913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6912914 {_126329 : Type'} : (term60 _126329) = (term61 _126329).
Proof. exact (MK_COMB (@lem6912913) (@lem6912912 _126329)). Qed.
Lemma lem6912915 {_126329 : Type'} (x : _126329) : (term54 _126329 x) = (term40 _126329 x).
Proof. exact (eq_refl (term54 _126329 x)). Qed.
Lemma lem6912916 {_126329 : Type'} (f : _126329 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6912917 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term55 _126329 x f) = (term56 _126329 x f).
Proof. exact (MK_COMB (@lem6912915 _126329 x) (@lem6912916 _126329 f)). Qed.
Lemma lem6912918 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term56 _126329 x f) = (term38 _126329 x f).
Proof. exact (eq_refl (term56 _126329 x f)). Qed.
Lemma lem6912919 {_126329 : Type'} (x : _126329) (f : _126329 -> real) : (term55 _126329 x f) = (term38 _126329 x f).
Proof. exact (TRANS (@lem6912917 _126329 x f) (@lem6912918 _126329 x f)). Qed.
Lemma lem6912920 {_126329 : Type'} (f : _126329 -> real) : (term62 _126329 f) = (term63 _126329 f).
Proof. exact (fun_ext (fun x : _126329 => @lem6912919 _126329 x f)). Qed.
Lemma lem6912921 {_126329 : Type'} : (@all _126329) = (@all _126329).
Proof. exact (eq_refl (@all _126329)). Qed.
Lemma lem6912922 {_126329 : Type'} (f : _126329 -> real) : (term64 _126329 f) = (term65 _126329 f).
Proof. exact (MK_COMB (@lem6912921 _126329) (@lem6912920 _126329 f)). Qed.
Lemma lem6912923 {_126329 : Type'} : (term66 _126329) = (term67 _126329).
Proof. exact (fun_ext (fun f : _126329 -> real => @lem6912922 _126329 f)). Qed.
Lemma lem6912924 {_126329 : Type'} : (@all (_126329 -> real)) = (@all (_126329 -> real)).
Proof. exact (eq_refl (@all (_126329 -> real))). Qed.
Lemma lem6912925 {_126329 : Type'} : (term52 _126329) = (term68 _126329).
Proof. exact (MK_COMB (@lem6912924 _126329) (@lem6912923 _126329)). Qed.
Lemma lem6912926 {_126329 : Type'} : ((term51 _126329) = (term52 _126329)) = ((term46 _126329) = (term68 _126329)).
Proof. exact (MK_COMB (@lem6912914 _126329) (@lem6912925 _126329)). Qed.
Lemma lem6912927 {_126329 : Type'} : (term46 _126329) = (term68 _126329).
Proof. exact (EQ_MP (@lem6912926 _126329) (@lem6912901 _126329)). Qed.
Lemma lem6912928 {_126288 : Type'} : (term17 _126288) = (term17 _126288).
Proof. exact (eq_refl (term17 _126288)). Qed.
Lemma lem6912929 {_126288 _126329 : Type'} : (term48 _126288 _126329) = (term69 _126288 _126329).
Proof. exact (MK_COMB (@lem6912928 _126288) (@lem6912927 _126329)). Qed.
Lemma lem6912930 {_126288 _126329 : Type'} : (term69 _126288 _126329) = (term48 _126288 _126329).
Proof. exact (SYM (@lem6912929 _126288 _126329)). Qed.
Lemma lem6912932 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6912772 _120477 _120519 _120521 op) (@lem6912771 _120477 _120519 _120521 op)). Qed.
Lemma lem6912933 {_126288 _126329 : Type'} (op : type1627) : term70 _126288 _126329 op.
Proof. exact (@lem6912932 _126288 real _126329 op). Qed.
Lemma lem6912934 {_126288 _126329 : Type'} : term71 _126288 _126329.
Proof. exact (@lem6912933 _126288 _126329 real_mul). Qed.
Lemma lem6912936 : (@monoidal real real_mul) = True.
Proof. exact (EQ_MP (@lem6912756) (@lem6912755)). Qed.
Lemma lem6912937 : True = (@monoidal real real_mul).
Proof. exact (SYM (@lem6912936)). Qed.
Lemma lem6912938 : @monoidal real real_mul.
Proof. exact (EQ_MP (@lem6912937) (@lem0)). Qed.
Lemma lem6912939 {_126288 _126329 : Type'} : term69 _126288 _126329.
Proof. exact (@lem6912934 _126288 _126329 (@lem6912938)). Qed.
Lemma lem6912940 {_126288 _126329 : Type'} : term48 _126288 _126329.
Proof. exact (EQ_MP (@lem6912930 _126288 _126329) (@lem6912939 _126288 _126329)). Qed.
Lemma lem6912941 {_126288 _126329 : Type'} : term47 _126288 _126329.
Proof. exact (EQ_MP (@lem6912889 _126288 _126329) (@lem6912940 _126288 _126329)). Qed.
