Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUM_GEN_term_abbrevs.
Require Import NSUM_SUPPORT_spec.
Require Import REAL_OF_NUM_SUM_spec.
Require Import SUM_SUPPORT_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7209760 (m : nat) : term0 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem7209761 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7209762 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7209761 m) (@lem7209760 m)). Qed.
Lemma lem7209763 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7209762 m n). Qed.
Lemma lem7209764 (m : nat) (n : nat) : (term2 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7209766 {A B : Type'} (s : A -> Prop) : term3 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem7209767 {A B : Type'} (s : A -> Prop) : (term3 A B s) = (term4 A B s).
Proof. exact (eq_refl (term3 A B s)). Qed.
Lemma lem7209768 {A B : Type'} (s : A -> Prop) : term4 A B s.
Proof. exact (EQ_MP (@lem7209767 A B s) (@lem7209766 A B s)). Qed.
Lemma lem7209769 {A B : Type'} (s : A -> Prop) (f : A -> B) : term5 A B s f.
Proof. exact (@lem7209768 A B s f). Qed.
Lemma lem7209770 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term5 A B s f) = (term6 A B s f).
Proof. exact (eq_refl (term5 A B s f)). Qed.
Lemma lem7209771 {A B : Type'} (s : A -> Prop) (f : A -> B) : term6 A B s f.
Proof. exact (EQ_MP (@lem7209770 A B s f) (@lem7209769 A B s f)). Qed.
Lemma lem7209772 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term7 A B s f op.
Proof. exact (@lem7209771 A B s f op). Qed.
Lemma lem7209773 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term7 A B s f op) = ((@support A B op f s) = (term8 A B s f op)).
Proof. exact (eq_refl (term7 A B s f op)). Qed.
Lemma lem7209777 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (term9 _126695 s f) = (@nsum _126695 s f)) : (term9 _126695 s f) = (@nsum _126695 s f).
Proof. exact (h1). Qed.
Lemma lem7209778 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (term9 _126695 s f) = (@nsum _126695 s f)) : (@nsum _126695 s f) = (term9 _126695 s f).
Proof. exact (SYM (@lem7209777 _126695 s f h1)). Qed.
Lemma lem7209779 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (@nsum _126695 s f) = (term9 _126695 s f)) : (@nsum _126695 s f) = (term9 _126695 s f).
Proof. exact (h1). Qed.
Lemma lem7209780 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (@nsum _126695 s f) = (term9 _126695 s f)) : (term9 _126695 s f) = (@nsum _126695 s f).
Proof. exact (SYM (@lem7209779 _126695 s f h1)). Qed.
Lemma lem7209781 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : ((term9 _126695 s f) = (@nsum _126695 s f)) = ((@nsum _126695 s f) = (term9 _126695 s f)).
Proof. exact (prop_ext (fun h1 : (term9 _126695 s f) = (@nsum _126695 s f) => @lem7209778 _126695 s f h1) (fun h1 : (@nsum _126695 s f) = (term9 _126695 s f) => @lem7209780 _126695 s f h1)). Qed.
Lemma lem7209782 {_126695 : Type'} (f : _126695 -> nat) : (term10 _126695 f) = (term11 _126695 f).
Proof. exact (fun_ext (fun s : _126695 -> Prop => @lem7209781 _126695 s f)). Qed.
Lemma lem7209783 {_126695 : Type'} : (@all (_126695 -> Prop)) = (@all (_126695 -> Prop)).
Proof. exact (eq_refl (@all (_126695 -> Prop))). Qed.
Lemma lem7209784 {_126695 : Type'} (f : _126695 -> nat) : (term12 _126695 f) = (term13 _126695 f).
Proof. exact (MK_COMB (@lem7209783 _126695) (@lem7209782 _126695 f)). Qed.
Lemma lem7209785 {_126695 : Type'} : (term14 _126695) = (term15 _126695).
Proof. exact (fun_ext (fun f : _126695 -> nat => @lem7209784 _126695 f)). Qed.
Lemma lem7209786 {_126695 : Type'} : (@all (_126695 -> nat)) = (@all (_126695 -> nat)).
Proof. exact (eq_refl (@all (_126695 -> nat))). Qed.
Lemma lem7209787 {_126695 : Type'} : (term16 _126695) = (term17 _126695).
Proof. exact (MK_COMB (@lem7209786 _126695) (@lem7209785 _126695)). Qed.
Lemma lem7209788 {_126695 : Type'} : term17 _126695.
Proof. exact (EQ_MP (@lem7209787 _126695) (@lem6930330 _126695)). Qed.
Lemma lem7209791 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (term18 _131679 s f) = (@sum _131679 s f)) : (term18 _131679 s f) = (@sum _131679 s f).
Proof. exact (h1). Qed.
Lemma lem7209792 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (term18 _131679 s f) = (@sum _131679 s f)) : (@sum _131679 s f) = (term18 _131679 s f).
Proof. exact (SYM (@lem7209791 _131679 s f h1)). Qed.
Lemma lem7209793 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (@sum _131679 s f) = (term18 _131679 s f)) : (@sum _131679 s f) = (term18 _131679 s f).
Proof. exact (h1). Qed.
Lemma lem7209794 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (@sum _131679 s f) = (term18 _131679 s f)) : (term18 _131679 s f) = (@sum _131679 s f).
Proof. exact (SYM (@lem7209793 _131679 s f h1)). Qed.
Lemma lem7209795 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : ((term18 _131679 s f) = (@sum _131679 s f)) = ((@sum _131679 s f) = (term18 _131679 s f)).
Proof. exact (prop_ext (fun h1 : (term18 _131679 s f) = (@sum _131679 s f) => @lem7209792 _131679 s f h1) (fun h1 : (@sum _131679 s f) = (term18 _131679 s f) => @lem7209794 _131679 s f h1)). Qed.
Lemma lem7209796 {_131679 : Type'} (f : _131679 -> real) : (term19 _131679 f) = (term20 _131679 f).
Proof. exact (fun_ext (fun s : _131679 -> Prop => @lem7209795 _131679 s f)). Qed.
Lemma lem7209797 {_131679 : Type'} : (@all (_131679 -> Prop)) = (@all (_131679 -> Prop)).
Proof. exact (eq_refl (@all (_131679 -> Prop))). Qed.
Lemma lem7209798 {_131679 : Type'} (f : _131679 -> real) : (term21 _131679 f) = (term22 _131679 f).
Proof. exact (MK_COMB (@lem7209797 _131679) (@lem7209796 _131679 f)). Qed.
Lemma lem7209799 {_131679 : Type'} : (term23 _131679) = (term24 _131679).
Proof. exact (fun_ext (fun f : _131679 -> real => @lem7209798 _131679 f)). Qed.
Lemma lem7209800 {_131679 : Type'} : (@all (_131679 -> real)) = (@all (_131679 -> real)).
Proof. exact (eq_refl (@all (_131679 -> real))). Qed.
Lemma lem7209801 {_131679 : Type'} : (term25 _131679) = (term26 _131679).
Proof. exact (MK_COMB (@lem7209800 _131679) (@lem7209799 _131679)). Qed.
Lemma lem7209802 {_131679 : Type'} : term26 _131679.
Proof. exact (EQ_MP (@lem7209801 _131679) (@lem7068649 _131679)). Qed.
Lemma lem7209803 {_126695 : Type'} (f : _126695 -> nat) : term27 _126695 f.
Proof. exact (@lem7209788 _126695 f). Qed.
Lemma lem7209804 {_126695 : Type'} (f : _126695 -> nat) : (term27 _126695 f) = (term13 _126695 f).
Proof. exact (eq_refl (term27 _126695 f)). Qed.
Lemma lem7209805 {_126695 : Type'} (f : _126695 -> nat) : term13 _126695 f.
Proof. exact (EQ_MP (@lem7209804 _126695 f) (@lem7209803 _126695 f)). Qed.
Lemma lem7209806 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term28 _126695 f s.
Proof. exact (@lem7209805 _126695 f s). Qed.
Lemma lem7209807 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (term28 _126695 f s) = ((@nsum _126695 s f) = (term9 _126695 s f)).
Proof. exact (eq_refl (term28 _126695 f s)). Qed.
Lemma lem7209809 {_131679 : Type'} (f : _131679 -> real) : term29 _131679 f.
Proof. exact (@lem7209802 _131679 f). Qed.
Lemma lem7209810 {_131679 : Type'} (f : _131679 -> real) : (term29 _131679 f) = (term22 _131679 f).
Proof. exact (eq_refl (term29 _131679 f)). Qed.
Lemma lem7209811 {_131679 : Type'} (f : _131679 -> real) : term22 _131679 f.
Proof. exact (EQ_MP (@lem7209810 _131679 f) (@lem7209809 _131679 f)). Qed.
Lemma lem7209812 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term30 _131679 f s.
Proof. exact (@lem7209811 _131679 f s). Qed.
Lemma lem7209813 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (term30 _131679 f s) = ((@sum _131679 s f) = (term18 _131679 s f)).
Proof. exact (eq_refl (term30 _131679 f s)). Qed.
Lemma lem7209815 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : term31 A s f.
Proof. exact (h1). Qed.
Lemma lem7209819 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (@nsum _126695 s f) = (term9 _126695 s f).
Proof. exact (EQ_MP (@lem7209807 _126695 s f) (@lem7209806 _126695 f s)). Qed.
Lemma lem7209820 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term9 A s f).
Proof. exact (@lem7209819 A s f). Qed.
Lemma lem7209821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7209822 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term32 A s f) = (term33 A s f).
Proof. exact (MK_COMB (@lem7209821) (@lem7209820 A s f)). Qed.
Lemma lem7209823 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7209824 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term34 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem7209823) (@lem7209822 A s f)). Qed.
Lemma lem7209826 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (@sum _131679 s f) = (term18 _131679 s f).
Proof. exact (EQ_MP (@lem7209813 _131679 s f) (@lem7209812 _131679 f s)). Qed.
Lemma lem7209827 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term18 A s f).
Proof. exact (@lem7209826 A s f). Qed.
Lemma lem7209828 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term36 A s f) = (term37 A s f).
Proof. exact (@lem7209827 A s (term38 A f)). Qed.
Lemma lem7209829 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term32 A s f) = (term36 A s f)) = ((term33 A s f) = (term37 A s f)).
Proof. exact (MK_COMB (@lem7209824 A s f) (@lem7209828 A s f)). Qed.
Lemma lem7209830 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term33 A s f) = (term37 A s f)) = ((term32 A s f) = (term36 A s f)).
Proof. exact (SYM (@lem7209829 A s f)). Qed.
Lemma lem7209834 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term8 A B s f op).
Proof. exact (EQ_MP (@lem7209773 A B s f op) (@lem7209772 A B s f op)). Qed.
Lemma lem7209835 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@support A nat op f s) = (term39 A s f op).
Proof. exact (@lem7209834 A nat s f op). Qed.
Lemma lem7209836 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term40 A s f).
Proof. exact (@lem7209835 A s f Nat.add). Qed.
Lemma lem7209846 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7209847 {A : Type'} (f : A -> nat) (x : A) : (term41 A f x) = (term41 A f x).
Proof. exact (eq_refl (term41 A f x)). Qed.
Lemma lem7209848 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7209847 A f x) (@lem7209846)). Qed.
Lemma lem7209851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7209852 {A : Type'} (f : A -> nat) (x : A) : (term42 A f x) = (term43 A f x).
Proof. exact (MK_COMB (@lem7209851) (@lem7209848 A f x)). Qed.
Lemma lem7209853 {A : Type'} (x : A) (s : A -> Prop) : (term44 A x s) = (term44 A x s).
Proof. exact (eq_refl (term44 A x s)). Qed.
Lemma lem7209854 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term45 A s f x) = (term46 A s f x).
Proof. exact (MK_COMB (@lem7209853 A x s) (@lem7209852 A f x)). Qed.
Lemma lem7209857 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7209858 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term47 A GEN_PVAR_237 s f x) = (term48 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7209857 A GEN_PVAR_237) (@lem7209854 A s f x)). Qed.
Lemma lem7209859 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7209860 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term49 A GEN_PVAR_237 s f x) = (term50 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7209858 A GEN_PVAR_237 s f x) (@lem7209859 A x)). Qed.
Lemma lem7209861 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term51 A GEN_PVAR_237 s f) = (term52 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7209860 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7209862 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7209863 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term53 A GEN_PVAR_237 s f) = (term54 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7209862 A) (@lem7209861 A GEN_PVAR_237 s f)). Qed.
Lemma lem7209868 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term55 A s f) = (term56 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7209863 A GEN_PVAR_237 s f)). Qed.
Lemma lem7209869 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7209870 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term40 A s f) = (term57 A s f).
Proof. exact (MK_COMB (@lem7209869 A) (@lem7209868 A s f)). Qed.
Lemma lem7209871 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term57 A s f).
Proof. exact (TRANS (@lem7209836 A s f) (@lem7209870 A s f)). Qed.
Lemma lem7209872 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7209873 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term58 A f s) = (term59 A s f).
Proof. exact (MK_COMB (@lem7209872 A) (@lem7209871 A s f)). Qed.
Lemma lem7209874 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7209875 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term9 A s f) = (term60 A s f).
Proof. exact (MK_COMB (@lem7209873 A s f) (@lem7209874 A f)). Qed.
Lemma lem7209876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7209877 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term33 A s f) = (term61 A s f).
Proof. exact (MK_COMB (@lem7209876) (@lem7209875 A s f)). Qed.
Lemma lem7209878 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7209879 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term35 A s f) = (term62 A s f).
Proof. exact (MK_COMB (@lem7209878) (@lem7209877 A s f)). Qed.
Lemma lem7209881 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term8 A B s f op).
Proof. exact (EQ_MP (@lem7209773 A B s f op) (@lem7209772 A B s f op)). Qed.
Lemma lem7209882 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@support A real op f s) = (term63 A s f op).
Proof. exact (@lem7209881 A real s f op). Qed.
Lemma lem7209883 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term64 A f s) = (term65 A s f).
Proof. exact (@lem7209882 A s (term38 A f) real_add). Qed.
Lemma lem7209893 {A B : Type'} (f : A -> B) (y : A) : (term66 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7209894 {A : Type'} (f : A -> real) (y : A) : (term67 A f y) = (f y).
Proof. exact (@lem7209893 A real f y). Qed.
Lemma lem7209895 {A : Type'} (f : A -> nat) (x : A) : (term68 A f x) = (term69 A f x).
Proof. exact (@lem7209894 A (term38 A f) x). Qed.
Lemma lem7209896 {A : Type'} (f : A -> nat) (x : A) : (term69 A f x) = (term70 A f x).
Proof. exact (eq_refl (term69 A f x)). Qed.
Lemma lem7209897 {A : Type'} (f : A -> nat) : (term71 A f) = (term38 A f).
Proof. exact (fun_ext (fun x : A => @lem7209896 A f x)). Qed.
Lemma lem7209898 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7209899 {A : Type'} (f : A -> nat) (x : A) : (term68 A f x) = (term69 A f x).
Proof. exact (MK_COMB (@lem7209897 A f) (@lem7209898 A x)). Qed.
Lemma lem7209900 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7209901 {A : Type'} (f : A -> nat) (x : A) : (term72 A f x) = (term73 A f x).
Proof. exact (MK_COMB (@lem7209900) (@lem7209899 A f x)). Qed.
Lemma lem7209902 {A : Type'} (f : A -> nat) (x : A) : (term69 A f x) = (term70 A f x).
Proof. exact (eq_refl (term69 A f x)). Qed.
Lemma lem7209903 {A : Type'} (f : A -> nat) (x : A) : ((term68 A f x) = (term69 A f x)) = ((term69 A f x) = (term70 A f x)).
Proof. exact (MK_COMB (@lem7209901 A f x) (@lem7209902 A f x)). Qed.
Lemma lem7209904 {A : Type'} (f : A -> nat) (x : A) : (term69 A f x) = (term70 A f x).
Proof. exact (EQ_MP (@lem7209903 A f x) (@lem7209895 A f x)). Qed.
Lemma lem7209905 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7209906 {A : Type'} (f : A -> nat) (x : A) : (term73 A f x) = (term74 A f x).
Proof. exact (MK_COMB (@lem7209905) (@lem7209904 A f x)). Qed.
Lemma lem7209908 : (@neutral real real_add) = term75.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7209909 {A : Type'} (f : A -> nat) (x : A) : ((term69 A f x) = (@neutral real real_add)) = ((term70 A f x) = term75).
Proof. exact (MK_COMB (@lem7209906 A f x) (@lem7209908)). Qed.
Lemma lem7209911 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem7209764 m n) (@lem7209763 m n)). Qed.
Lemma lem7209912 {A : Type'} (f : A -> nat) (x : A) : ((term70 A f x) = term75) = ((f x) = (NUMERAL 0)).
Proof. exact (@lem7209911 (f x) (NUMERAL 0)). Qed.
Lemma lem7209915 {A : Type'} (f : A -> nat) (x : A) : ((term69 A f x) = (@neutral real real_add)) = ((f x) = (NUMERAL 0)).
Proof. exact (TRANS (@lem7209909 A f x) (@lem7209912 A f x)). Qed.
Lemma lem7209916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7209917 {A : Type'} (f : A -> nat) (x : A) : (term76 A f x) = (term43 A f x).
Proof. exact (MK_COMB (@lem7209916) (@lem7209915 A f x)). Qed.
Lemma lem7209918 {A : Type'} (x : A) (s : A -> Prop) : (term44 A x s) = (term44 A x s).
Proof. exact (eq_refl (term44 A x s)). Qed.
Lemma lem7209919 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term77 A s f x) = (term46 A s f x).
Proof. exact (MK_COMB (@lem7209918 A x s) (@lem7209917 A f x)). Qed.
Lemma lem7209922 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7209923 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term78 A GEN_PVAR_237 s f x) = (term48 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7209922 A GEN_PVAR_237) (@lem7209919 A s f x)). Qed.
Lemma lem7209924 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7209925 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term79 A GEN_PVAR_237 s f x) = (term50 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7209923 A GEN_PVAR_237 s f x) (@lem7209924 A x)). Qed.
Lemma lem7209926 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term80 A GEN_PVAR_237 s f) = (term52 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7209925 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7209927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7209928 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term81 A GEN_PVAR_237 s f) = (term54 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7209927 A) (@lem7209926 A GEN_PVAR_237 s f)). Qed.
Lemma lem7209933 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term82 A s f) = (term56 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7209928 A GEN_PVAR_237 s f)). Qed.
Lemma lem7209934 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7209935 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term65 A s f) = (term57 A s f).
Proof. exact (MK_COMB (@lem7209934 A) (@lem7209933 A s f)). Qed.
Lemma lem7209936 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term64 A f s) = (term57 A s f).
Proof. exact (TRANS (@lem7209883 A s f) (@lem7209935 A s f)). Qed.
Lemma lem7209937 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7209938 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term83 A f s) = (term84 A s f).
Proof. exact (MK_COMB (@lem7209937 A) (@lem7209936 A s f)). Qed.
Lemma lem7209939 {A : Type'} (f : A -> nat) : (term38 A f) = (term38 A f).
Proof. exact (eq_refl (term38 A f)). Qed.
Lemma lem7209940 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term37 A s f) = (term85 A s f).
Proof. exact (MK_COMB (@lem7209938 A s f) (@lem7209939 A f)). Qed.
Lemma lem7209941 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term33 A s f) = (term37 A s f)) = ((term61 A s f) = (term85 A s f)).
Proof. exact (MK_COMB (@lem7209879 A s f) (@lem7209940 A s f)). Qed.
Lemma lem7209944 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term61 A s f) = (term85 A s f)) = ((term33 A s f) = (term37 A s f)).
Proof. exact (SYM (@lem7209941 A s f)). Qed.
Lemma lem7209945 {_134498 : Type'} (f : _134498 -> nat) : term86 _134498 f.
Proof. exact (@lem7169057 _134498 f). Qed.
Lemma lem7209946 {_134498 : Type'} (f : _134498 -> nat) : (term86 _134498 f) = (term87 _134498 f).
Proof. exact (eq_refl (term86 _134498 f)). Qed.
Lemma lem7209947 {_134498 : Type'} (f : _134498 -> nat) : term87 _134498 f.
Proof. exact (EQ_MP (@lem7209946 _134498 f) (@lem7209945 _134498 f)). Qed.
Lemma lem7209948 {_134498 : Type'} (f : _134498 -> nat) (s : _134498 -> Prop) : term88 _134498 f s.
Proof. exact (@lem7209947 _134498 f s). Qed.
Lemma lem7209949 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term88 _134498 f s) = (term89 _134498 s f).
Proof. exact (eq_refl (term88 _134498 f s)). Qed.
Lemma lem7209950 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term89 _134498 s f.
Proof. exact (EQ_MP (@lem7209949 _134498 s f) (@lem7209948 _134498 f s)). Qed.
Lemma lem7209951 {_134498 : Type'} (s : _134498 -> Prop) (h1 : @FINITE _134498 s) : @FINITE _134498 s.
Proof. exact (h1). Qed.
Lemma lem7209952 {_134498 : Type'} (f : _134498 -> nat) (s : _134498 -> Prop) (h1 : @FINITE _134498 s) : (term32 _134498 s f) = (term36 _134498 s f).
Proof. exact (@lem7209950 _134498 s f (@lem7209951 _134498 s h1)). Qed.
Lemma lem7209958 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term31 A s f) = ((term31 A s f) = True).
Proof. exact (@lem7 (term31 A s f)). Qed.
Lemma lem7209963 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term89 _134498 s f.
Proof. exact (fun h0 : @FINITE _134498 s => @lem7209952 _134498 f s h0). Qed.
Lemma lem7209964 {A : Type'} (s : A -> Prop) (f : A -> nat) : term89 A s f.
Proof. exact (@lem7209963 A s f). Qed.
Lemma lem7209965 {A : Type'} (s : A -> Prop) (f : A -> nat) : term90 A s f.
Proof. exact (@lem7209964 A (term57 A s f) f). Qed.
Lemma lem7209967 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term31 A s f) = True.
Proof. exact (EQ_MP (@lem7209958 A s f) (@lem7209815 A s f h1)). Qed.
Lemma lem7209968 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term31 A s f) = True.
Proof. exact (@lem7209967 A s f h1). Qed.
Lemma lem7209969 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : True = (term31 A s f).
Proof. exact (SYM (@lem7209968 A s f h1)). Qed.
Lemma lem7209970 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : term31 A s f.
Proof. exact (EQ_MP (@lem7209969 A s f h1) (@lem0)). Qed.
Lemma lem7209971 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term61 A s f) = (term85 A s f).
Proof. exact (@lem7209965 A s f (@lem7209970 A s f h1)). Qed.
Lemma lem7209980 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7209981 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term62 A s f) = (term91 A s f).
Proof. exact (MK_COMB (@lem7209980) (@lem7209971 A s f h1)). Qed.
Lemma lem7209998 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term85 A s f) = (term85 A s f).
Proof. exact (eq_refl (term85 A s f)). Qed.
Lemma lem7209999 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : ((term61 A s f) = (term85 A s f)) = ((term85 A s f) = (term85 A s f)).
Proof. exact (MK_COMB (@lem7209981 A s f h1) (@lem7209998 A s f)). Qed.
Lemma lem7210001 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7210002 (x : real) : (x = x) = True.
Proof. exact (@lem7210001 real x). Qed.
Lemma lem7210003 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term85 A s f) = (term85 A s f)) = True.
Proof. exact (@lem7210002 (term85 A s f)). Qed.
Lemma lem7210004 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : ((term61 A s f) = (term85 A s f)) = True.
Proof. exact (TRANS (@lem7209999 A s f h1) (@lem7210003 A s f)). Qed.
Lemma lem7210005 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : True = ((term61 A s f) = (term85 A s f)).
Proof. exact (SYM (@lem7210004 A s f h1)). Qed.
Lemma lem7210006 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term61 A s f) = (term85 A s f).
Proof. exact (EQ_MP (@lem7210005 A s f h1) (@lem0)). Qed.
Lemma lem7210007 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term33 A s f) = (term37 A s f).
Proof. exact (EQ_MP (@lem7209944 A s f) (@lem7210006 A s f h1)). Qed.
Lemma lem7210008 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term32 A s f) = (term36 A s f).
Proof. exact (EQ_MP (@lem7209830 A s f) (@lem7210007 A s f h1)). Qed.
Lemma lem7210009 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term31 A s f) = ((term32 A s f) = (term36 A s f)).
Proof. exact (prop_ext (fun h2 : term31 A s f => @lem7210008 A s f h1) (fun h2 : (term32 A s f) = (term36 A s f) => @lem7209815 A s f h1)). Qed.
Lemma lem7210010 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term31 A s f) : (term32 A s f) = (term36 A s f).
Proof. exact (EQ_MP (@lem7210009 A s f h1) (@lem7209815 A s f h1)). Qed.
Lemma lem7210011 {A : Type'} (s : A -> Prop) (f : A -> nat) : term92 A s f.
Proof. exact (fun h0 : term31 A s f => @lem7210010 A s f h0). Qed.
Lemma lem7210016 {A : Type'} (f : A -> nat) : term93 A f.
Proof. exact (fun s : A -> Prop => @lem7210011 A s f). Qed.
Lemma lem7210021 {A : Type'} : term94 A.
Proof. exact (fun f : A -> nat => @lem7210016 A f). Qed.
